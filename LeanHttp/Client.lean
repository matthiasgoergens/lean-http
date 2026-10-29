module

public import Std.Async.TCP
public import Std.Http.Data
public import Std.Sync.Mutex
public import Std.Time.DateTime.Timestamp
public import LeanHttp.Body
public import LeanHttp.Call
public import LeanHttp.Call.Trace
public import LeanHttp.Config
public import LeanHttp.Connect
public import LeanHttp.Error
public import LeanHttp.Exchange
public import LeanHttp.Pool
public import LeanHttp.Wait
public import LeanHttp.Wire

public section

/-!
# The client

`Client.withResponse` makes one HTTP/1.1 call and hands the final response to a callback, whose body
the callback pulls (`BodyStream`); `Client.request` reads the whole body into memory on top of it.
The calling task does all the work.  Three pure cores make every decision, and the client only
carries them out:

- the **per-call planner** (`LeanHttp.Call`) decides, after each exchange, whether to deliver the
  response, follow a redirect with the next request, send the same request again after a delay, or
  fail.  The client starts it with the call's request, sends its current request, reports how the
  exchange ended (the final response head, before its body is read, or a `Failure`) with the time,
  and does what the step says.  A response that is followed or retried has its body drained within
  the drain limit, or its connection closed, before the next request.  With `Config.observe` the
  client reports each of these steps, and `Call.validate` checks such a record against the planner.
- the **pool core** (`LeanHttp.Pool`) decides which connection each exchange uses.  The client keeps
  it under one mutex: each pool operation is a quick pure step, and nothing waits while holding it.
- the **exchange core** (`LeanHttp.Exchange`) runs one request and response on one connection; the
  client performs its writes and reads (at most one of each in flight) and races them against its
  deadlines (`LeanHttp.Body`).

An idle connection in the pool is a socket with no task and no pending operation.  A call that takes
one first watches it for `Config.idleCheckMs` (a bounded `waitReadable`, then `cancelRecv`): bytes,
the end of input or an error mean the server closed it or sent something unasked, such as a 408, so
the connection is closed and the call takes another.  Even a window of zero sees what arrived while
the connection was idle: the timer that ends the wait fires only after the event loop has polled the
socket once (`NOTES.md`).  When the exchange ends, the connection goes back to the pool with the
core's reuse verdict.  An exchange whose pooled connection turns out to be closed anyway is sent
once more, on a fresh connection, when that is safe (`redispatch?`): nothing of it was written, or
the server answered 408 before anything else, or the method is idempotent and the connection closed
before any byte of a response.  For the planner that is all one exchange, and it spends none of the
planner's retries.

No receive is left pending when a call returns, nor when the callback of `withResponse` ends: a
pending receive on v4.34.1 can keep the process from exiting (`NOTES.md`).

With `Config.pool` off, every exchange opens a connection of its own, sends `Connection: close` and
drops the connection at the end, as milestone 1 did.

v4.34.1 can cancel a pending receive but not a pending connect, write or name lookup, so three
things can outlive a call that gave up on them: a connect attempt that was abandoned (its socket is
released when the kernel gives up on the SYN), a write the peer never accepts (its socket stays open
while the peer keeps the connection), and a name lookup that timed out (it runs on in libuv's thread
pool until the resolver gives up).  `NOTES.md` records what each costs.

Only `http` targets are reached: an `https` request, or a redirect to one, fails with
`invalidRequest` until the client has TLS.
-/

namespace LeanHttp

set_option linter.all true

open Std.Http Std.Async Std.Net

/--
What a successful call records about itself, in the response's extensions:
`response.extensions.get CallInfo`.
-/
structure CallInfo where
  /--
  The seed of the backoff jitter, for replaying the call's schedule.
  -/
  seed : UInt64

  /--
  How many rounds of connect attempts the call made, over all its exchanges; 0 if every exchange
  used a connection from the pool.
  -/
  connectRounds : Nat

  /--
  The address the call's connection is connected to.
  -/
  address : SocketAddress

  /--
  The connect attempts of the call that did not win, over all its exchanges.
  -/
  failedAttempts : Array ConnectAttempt

  /--
  Milliseconds from the start of the call to the final response head (`withResponse`), or to the
  end of its body (`request`).
  -/
  elapsedMs : Nat

  /--
  The pool's id of the connection, or `none` with pooling off.  Two calls with the same id used the
  same connection.
  -/
  connection : Option ConnId := none

  /--
  Whether the connection was taken from the pool.
  -/
  reused : Bool := false

  /--
  Idle connections the call took from the pool and closed because they failed the idle check.
  -/
  discarded : Nat := 0

  /--
  Microseconds the call spent in idle checks.
  -/
  idleCheckUs : Nat := 0

  /--
  Whether the final request was sent a second time, on a fresh connection, after its pooled
  connection turned out to be closed.
  -/
  redispatched : Bool := false

  /--
  Redirects the call followed.
  -/
  hops : Nat := 0

  /--
  Retries the call made, over all its hops.
  -/
  retries : Nat := 0

  /--
  The target of the final request, as an absolute URI: the request's own, or where its redirects
  led.
  -/
  uri : String := ""
deriving TypeName

/--
An idle connection's socket, kept next to the pool.
-/
structure IdleSocket where
  /--
  The socket, with no operation pending.
  -/
  socket : TCP.Socket.Client

  /--
  The address it is connected to.
  -/
  address : SocketAddress

/--
What the client's mutex guards: the pool core, the sockets of its idle connections, and a promise
that is resolved, and replaced, whenever a connection leaves the checked-out set, for calls waiting
at `Config.maxActivePerOrigin`.

These tables are carried across waits, so the runtime never updates them in place (`NOTES.md`):
every operation copies them.  They are small (a few connections per origin).
-/
structure PoolState where
  /--
  The pool core, with origins as `host:port`.
  -/
  pool : Pool String

  /--
  The socket of every idle connection, by id: exactly the ids idle in `pool`.
  -/
  idle : Std.HashMap ConnId IdleSocket := {}

  /--
  Resolved when a connection is given back or dropped, or the client is closed, and then replaced.
  It is shared by every origin: each waiting call asks the pool again when it is resolved.
  -/
  freed : IO.Promise Unit

/--
An HTTP/1.1 client: its configuration and its connection pool.  Calls through one client from any
number of tasks share the pool.
-/
structure Client where
  /--
  The limits and timeouts of every call.
  -/
  config : Config

  /--
  The pool, under one mutex.
  -/
  state : Std.Mutex PoolState

  /--
  The number of the next call, for `Config.observe`.
  -/
  calls : IO.Ref Nat

namespace Client

/--
The pool core's limits for `config`.
-/
def poolConfig (config : Config) : PoolConfig :=
  { maxIdle := config.maxIdlePerOrigin, idleTimeoutMs := config.idleTimeoutMs,
    maxActive := config.maxActivePerOrigin }

/--
A client with the given configuration and an empty pool.
-/
def new (config : Config := {}) : BaseIO Client := do
  let freed ← IO.Promise.new
  let state ← Std.Mutex.new { pool := Pool.empty (poolConfig config), freed }
  return { config, state, calls := ← IO.mkRef 0 }

/--
Runs `f` on the pool state under the mutex.
-/
private def withState {β : Type} (client : Client) (f : PoolState → BaseIO (PoolState × β)) :
    BaseIO β :=
  client.state.atomically (m := BaseIO) do
    let (s, b) ← f (← get)
    set s
    return b

/--
Wakes the calls waiting for a connection to come back, and arms a new promise for the next ones.
-/
private def wake (s : PoolState) : BaseIO PoolState := do
  s.freed.resolve ()
  return { s with freed := ← IO.Promise.new }

/--
Forgets the sockets of idle connections the pool let go, which closes them.
-/
private def forget (s : PoolState) (ids : List ConnId) : PoolState :=
  { s with idle := ids.foldl (·.erase ·) s.idle }

/--
Counts of the pool's connections, for tests and monitoring.
-/
structure Stats where
  /--
  Idle connections, over all origins.
  -/
  idle : Nat

  /--
  Connections checked out by calls, over all origins.
  -/
  checkedOut : Nat

  /--
  Ids allocated so far: the number of connections the pool has decided to open.
  -/
  allocated : Nat
deriving Repr

/--
The pool's counts now.
-/
def stats (client : Client) : BaseIO Stats :=
  client.withState fun s =>
    return (s, { idle := s.pool.idle.length, checkedOut := s.pool.out.length, allocated := s.pool.next })

/--
Closes every idle connection and the pool: calls already holding a connection finish, and their
connections are closed at the end; later calls fail with `Cause.localClose`, not sent (with pooling
off too).
-/
def close (client : Client) : BaseIO Unit :=
  client.withState fun s => do
    let (pool, _) := s.pool.closeAll
    let s ← wake { s with pool, idle := {} }
    return (s, ())

/--
A seed for the backoff jitter, from the operating system.
-/
def osSeed : IO UInt64 := do
  let bytes ← IO.getRandomBytes 8
  return bytes.foldl (init := 0) fun acc b => (acc <<< 8) ||| b.toUInt64

/--
Whether idle connection `socket` is still clean: nothing arrived on it within `ms` milliseconds of
starting to wait for input (no bytes, no end of input, no error).  The wait is cancelled before this
returns, so no receive stays pending.  It does not read: a connection that is not clean is closed.
-/
def idleClean (socket : TCP.Socket.Client) (ms : Nat) : Async Bool := do
  let waiter ← try socket.native.waitReadable catch _ => return false
  let result ← try awaitFirst #[waiter.result?] ms catch _ => pure (some none)
  socket.native.cancelRecv
  return result.isNone

/--
The exchange core's settings for one call of `config`, with a body limit of `maxBody` (by default
`Config.maxBodyBytes`): keep-alive when pooling is on.  Fails with
`invalidRequest` if `readGapMs` is zero, which would make every write and read due the moment it is
issued, or if `readChunkBytes` is zero, which would ask for reads that can return nothing.
-/
def exchangeConfig (config : Config) (maxBody : Nat := config.maxBodyBytes) :
    Except Cause ExchangeConfig :=
  if hg : 0 < config.readGapMs then
    if hr : 0 < config.readChunkBytes then
      .ok {
        limits := config.limits, keepAlive := config.pool, maxInterim := config.maxInterimResponses,
        maxBody, readChunk := config.readChunkBytes, readChunk_pos := hr,
        writeChunk := config.writeChunkBytes, gapMs := config.readGapMs, gapMs_pos := hg,
        drainBytes := config.drainBytes, drainMs := config.drainMs }
    else
      .error (.invalidRequest "readChunkBytes must be positive")
  else
    .error (.invalidRequest "readGapMs must be positive")

/--
Checks the settings that bound a call before its exchange starts.  Fails with `invalidRequest` if
`deadlineMs` is zero, which no call can meet (and which would still start a name lookup, only to
abandon it), or if `connectTimeoutMs` is zero, which lets an attempt connect only if the connection
completes before a timer of zero milliseconds fires: on loopback it does, over any real network it
would not.  A zero `connectStaggerMs` is accepted: it starts every attempt of a round at once.  A
`maxActivePerOrigin` of zero is refused: every call would wait out its deadline.
-/
def checkConfig (config : Config) : Except Cause Unit := do
  if config.deadlineMs == 0 then
    throw (.invalidRequest "deadlineMs must be positive")
  if config.connectTimeoutMs == 0 then
    throw (.invalidRequest "connectTimeoutMs must be positive")
  if config.maxActivePerOrigin == some 0 then
    throw (.invalidRequest "maxActivePerOrigin must be positive: no call could take a connection")

/--
What the client knows about a call so far, over all its exchanges.
-/
private structure Progress where
  /--
  Rounds of connect attempts.
  -/
  rounds : Nat := 0

  /--
  The connect attempts that did not win.
  -/
  attempts : Array ConnectAttempt := #[]

  /--
  Idle connections closed by the idle check.
  -/
  discarded : Nat := 0

  /--
  Microseconds spent in idle checks.
  -/
  idleCheckUs : Nat := 0

  /--
  Whether the current exchange was sent a second time.
  -/
  redispatched : Bool := false

  /--
  Whether the current exchange ran on a connection from the pool.
  -/
  reused : Bool := false

  /--
  The furthest any request of the call got.
  -/
  furthest : Delivery := .notSent

/--
A connection the call holds, from the pool or fresh.
-/
private structure Held where
  /--
  The socket.
  -/
  socket : TCP.Socket.Client

  /--
  The address it is connected to.
  -/
  address : SocketAddress

  /--
  The pool's id, if pooling is on.
  -/
  id : Option ConnId

  /--
  Whether it came from the pool.
  -/
  reused : Bool

/--
Gives connection `id` back to the pool with the exchange's reuse verdict, keeping its socket if the
pool keeps it idle.
-/
private def giveBack (client : Client) (id : ConnId) (socket : TCP.Socket.Client)
    (address : SocketAddress) (reusable : Bool) : BaseIO Unit := do
  client.withState fun s => do
    -- The time is read under the mutex, so that the pool sees times in the order of its operations.
    let now ← IO.monoMsNow
    let (pool, returned, closing) := s.pool.giveBack id reusable now
    let s := forget { s with pool } closing
    let s := match returned with
      | .idle => { s with idle := s.idle.insert id { socket, address } }
      | .dropped | .notOut => s
    return (← wake s, ())

/--
Lets connection `id` go: its exchange failed, its connect failed, or it failed the idle check.
-/
private def dropConn (client : Client) (id : ConnId) : BaseIO Unit :=
  client.withState fun s => do
    let (pool, _) := s.pool.drop id
    return (← wake { s with pool }, ())

/--
Ends the call's hold on a connection with the exchange's verdict: back to the pool if pooling is on
(where a connection that is not reusable is dropped), and otherwise nothing, the socket closing
when its last reference goes.
-/
private def settleHeld (client : Client) (held : Held) (reusable : Bool) : BaseIO Unit := do
  if let some id := held.id then
    giveBack client id held.socket held.address reusable

/--
What taking a connection from the pool came to, with the socket of a reused one.
-/
private inductive Got where
  /-- An idle connection, now checked out. -/
  | reuse (id : ConnId) (idle : IdleSocket)
  /-- A new id to connect under, now checked out. -/
  | fresh (id : ConnId)
  /-- The origin is at its active cap: wait for `freed`, then ask again. -/
  | atCap (freed : IO.Promise Unit)
  /-- The client was closed. -/
  | closed

/--
Takes a connection of `origin` from the pool, reusing an idle one if `reuse` holds.
-/
private def takeConn (client : Client) (origin : String) (reuse : Bool) : BaseIO Got := do
  client.withState fun s => do
    let now ← IO.monoMsNow
    let (pool, taken, closing) := s.pool.take origin now reuse
    let s := forget { s with pool } closing
    match taken with
    | .reuse id =>
      match s.idle[id]? with
      | some idle => return ({ s with idle := s.idle.erase id }, .reuse id idle)
      | none =>
        -- The socket table holds a socket for every idle id, so this does not happen; if it did,
        -- the connection is dropped and the call opens a new one.
        let (pool, _) := s.pool.drop id
        let (pool, taken, _) := pool.take origin now false
        let s := { s with pool }
        match taken with
        | .fresh id => return (s, .fresh id)
        | .atCap => return (s, .atCap s.freed)
        | _ => return (s, .closed)
    | .fresh id => return (s, .fresh id)
    | .atCap => return (s, .atCap s.freed)
    | .closed => return (s, .closed)

/--
One exchange of a call: its client, where it goes, what it sends, and the call's deadline.
-/
private structure Attempt where
  /-- The client. -/
  client : Client
  /-- Where the request goes. -/
  plan : Plan
  /-- The origin, as `host:port`. -/
  target : String
  /-- The request, encoded. -/
  prepared : PreparedRequest
  /-- The deadline of the whole call. -/
  deadline : Nat
  /-- Reports a step of the call (`Config.observe`). -/
  observe : Call.Event → BaseIO Unit

/--
A failure before any request byte was written.
-/
private def notSent (cause : Cause) (detail : String := "") : Failure :=
  { cause, delivery := .notSent, written := 0, detail }

/--
Opens a connection, under pool id `id` if pooling is on, with one round of connect attempts;
drops the id if the connect fails.
-/
private def Attempt.connect (a : Attempt) (id : Option ConnId) (progress : Progress) :
    Async (Except Failure Held × Progress) := do
  let config := a.client.config
  -- An exchange sent again may get here with the deadline gone: no lookup is started then, since a
  -- lookup cannot be cancelled and an abandoned one can delay exit (`NOTES.md`).
  if a.deadline ≤ (← IO.monoMsNow) then
    if let some id := id then dropConn a.client id
    return (.error (notSent (.timeout .deadline)), progress)
  -- `Connect.run` reports its failures as values; should it throw anyway, the id must not stay
  -- checked out, so the exception counts as a failed connect.
  let connected : Except String (Except ConnectError Connected) ←
    try pure (.ok (← Connect.run config (.ofHost a.plan.host) a.plan.port progress.rounds a.deadline))
    catch e => pure (.error (toString e))
  match connected with
  | .ok (.ok c) =>
    let held : Held := { socket := c.socket, address := c.address, id, reused := false }
    return (.ok held, { progress with
      rounds := progress.rounds + 1, attempts := progress.attempts ++ c.attempts })
  | .ok (.error e) =>
    if let some id := id then dropConn a.client id
    return match e with
      | .resolve host detail => (.error (notSent (.resolve host detail)), progress)
      | .exhausted attempts =>
        (.error (notSent (.connect attempts)),
          { progress with rounds := progress.rounds + 1, attempts := progress.attempts ++ attempts })
      | .deadline attempts =>
        if attempts.isEmpty then
          (.error (notSent (.timeout .deadline)
            "the deadline passed before any connect attempt started (resolving the name, or before)"),
            progress)
        else
          (.error (notSent (.timeout .deadline) (Cause.connect attempts).describe),
            { progress with rounds := progress.rounds + 1, attempts := progress.attempts ++ attempts })
  | .error detail =>
    if let some id := id then dropConn a.client id
    return (.error (notSent (.connect #[]) detail), progress)

/--
Takes a connection from the pool for the exchange: an idle one that passes the idle check (closing
those that fail it), or a new one, waiting while the origin is at its active cap, within the
deadline.
-/
private partial def Attempt.acquire (a : Attempt) (reuse : Bool) (progress : Progress) :
    Async (Except Failure Held × Progress) := do
  let config := a.client.config
  let left := a.deadline - (← IO.monoMsNow)
  if left == 0 then
    return (.error (notSent (.timeout .deadline)
      "the deadline passed while taking a connection from the pool"), progress)
  match ← takeConn a.client a.target reuse with
  | .closed => return (.error (notSent .localClose "the client was closed"), progress)
  | .atCap freed =>
    let left := a.deadline - (← IO.monoMsNow)
    if left == 0 then
      return (.error (notSent (.timeout .deadline)
        "waiting for a connection: the origin is at maxActivePerOrigin"), progress)
    match ← (try (some <$> awaitFirst #[freed.result?] left) catch _ => pure none) with
    | some _ => a.acquire reuse progress
    | none =>
      return (.error (notSent (.timeout .deadline) "waiting for a connection failed"), progress)
  | .fresh id => a.connect (some id) progress
  | .reuse id idle =>
    let held : Held := { socket := idle.socket, address := idle.address, id, reused := true }
    if !config.idleCheck then
      return (.ok held, progress)
    let t0 ← IO.monoNanosNow
    let window := min config.idleCheckMs (a.deadline - (← IO.monoMsNow))
    let clean ← try idleClean idle.socket window catch _ => pure false
    let t1 ← IO.monoNanosNow
    let progress := { progress with idleCheckUs := progress.idleCheckUs + (t1 - t0) / 1000 }
    if clean then
      return (.ok held, progress)
    dropConn a.client id
    a.acquire reuse { progress with discarded := progress.discarded + 1 }

/--
How one exchange of a call began, for the planner: the final response head, with the exchange still
going on its connection, or a failure.
-/
private inductive Began where
  /--
  The final response head arrived; the exchange holds the body.
  -/
  | head (live : Live) (head : Response.Head) (held : Held)

  /--
  The exchange failed before the final response head, or no connection was made.
  -/
  | failure (failure : Failure)

/--
Runs one exchange until its final response head: takes or opens a connection, starts the exchange on
it and drives it until the head arrives or the exchange fails, and sends it once more on a fresh
connection if the pooled one turned out to be closed and `redispatch?` says that is safe.
-/
private partial def Attempt.run (a : Attempt) (reuse : Bool) (progress : Progress) :
    Async (Began × Progress) := do
  let config := a.client.config
  let (got, progress) ← if config.pool then a.acquire reuse progress else do
      -- Without pooling the pool only records whether the client was closed.
      let closed ← a.client.withState (β := Bool) fun s => pure (s, s.pool.closed)
      if closed then
        pure (.error (notSent .localClose "the client was closed"), progress)
      else
        a.connect none progress
  let held ← match got with
    | .ok held => pure held
    | .error f => return (.failure f, { progress with reused := false })
  let progress := { progress with reused := held.reused }
  -- The shell reports socket errors to the core as events; should anything throw anyway, the
  -- connection is dropped like after any failure, with no receive left pending, and the exchange
  -- is not sent again.
  let begun : Except Failure (Live × Option Response.Head) ←
    try pure (.ok (← Live.begin held.socket a.prepared a.deadline))
    catch e =>
      try held.socket.native.cancelRecv catch _ => pure ()
      pure (.error {
        cause := .peerClosed, delivery := .maybeDelivered, written := 0,
        detail := s!"the client failed: {e}" })
  let (ended, live?) := match begun with
    | .ok (live, some head) => (Ended.response head live.ex.interim, some live)
    | .ok (live, none) =>
      -- The core ends before a head only by failing; a finish without one is a closed connection.
      let f := live.failure?.getD
        { cause := .peerClosed, delivery := live.ex.delivery, written := live.ex.written }
      (.failure f live.received, some live)
    | .error f => (.failure f true, none)
  let why := if held.reused && !progress.redispatched then redispatch? a.prepared.method ended
    else none
  -- The second attempt describes the exchange, but the first one was written: unless the server
  -- said with a 408 that it did not process it, it may have been delivered even if the second was
  -- not, and the planner is told so.  Either way the call's error must not say not sent.
  let again : Async (Began × Progress) := do
    if let some reason := why then a.observe (.redispatch held.reused ended reason)
    let first := match ended with
      | .response .. => Delivery.maybeDelivered
      | .failure f _ => f.delivery
    let (began, progress) ← a.run false { progress with
      redispatched := true, furthest := progress.furthest.max first }
    return match began with
      | .failure f =>
        if why == some .closedBeforeResponse && f.delivery == .notSent then
          (.failure { f with delivery := .maybeDelivered }, progress)
        else (began, progress)
      | _ => (began, progress)
  match ended, live? with
  | .response head _, some live =>
    if why.isSome then
      -- The connection is dropped, so the rest of the 408 is not worth draining.
      discard <| live.cancelRead
      settleHeld a.client held false
      again
    else
      return (.head live head held, progress)
  | .failure f _, _ =>
    if let some id := held.id then
      -- An exchange that timed out before writing anything (its deadline had passed when it began)
      -- left the connection as it was.
      if f.delivery == .notSent && (f.cause matches .timeout _) then
        giveBack a.client id held.socket held.address true
      else dropConn a.client id
    if why.isSome then again else return (.failure f, progress)
  | .response _ _, none =>
    -- `begun` gives a head only with its exchange, so this does not happen; if it did, the
    -- connection is dropped.
    settleHeld a.client held false
    return (.failure (notSent .peerClosed), progress)

/--
The wall clock, in whole seconds since 1970-01-01T00:00:00Z.
-/
def wallSec : IO Nat := do
  return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat

/--
Sleeps until `IO.monoMsNow` reaches `target`.  A timer may fire up to a millisecond before its time by
`IO.monoMsNow`, since libuv measures timers from the time it cached at the start of the loop's
iteration, so the remainder is slept again.
-/
partial def sleepUntil (target : Nat) : Async Unit := do
  let now ← IO.monoMsNow
  if now < target then
    Std.Async.sleep (.ofNat (target - now))
    sleepUntil target

/--
What a call is made of, fixed when it starts.
-/
private structure CallSpec where
  /-- The client. -/
  client : Client
  /-- The caller's request. -/
  req : Request ByteArray
  /-- The exchange core's settings. -/
  xcfg : ExchangeConfig
  /-- The seed of the backoff jitter. -/
  seed : UInt64
  /-- When the call started. -/
  started : Nat
  /-- The deadline of the whole call. -/
  deadline : Nat
  /-- The call's number, for `Config.observe`. -/
  number : Nat

/--
Reports a step of the call to `Config.observe`, if it is set.
-/
private def CallSpec.observe (spec : CallSpec) (event : Call.Event) : BaseIO Unit := do
  if let some f := spec.client.config.observe then f spec.number event

/--
The call's error for a failure `f` of its current exchange, in the planner's state `st`.  The
delivery is the furthest any request of the call got; a connect failure lists every failed connect
attempt of the call.
-/
private def callError (seed : UInt64) (st : Call.State) (progress : Progress) (target : String)
    (f : Failure) (notRetried : Option Call.NoRetry) : Error :=
  let cause := match f.cause with
    | .connect _ => .connect progress.attempts
    | c => c
  { cause, delivery := progress.furthest.max f.delivery, written := f.written, target, seed,
    connectRounds := progress.rounds, status := f.status, detail := f.detail,
    reused := progress.reused, redispatched := progress.redispatched, hops := st.hops,
    retries := st.retries, notRetried }

/--
`callError` with the call's seed.
-/
private def CallSpec.error (spec : CallSpec) (st : Call.State) (progress : Progress) (target : String)
    (f : Failure) (notRetried : Option Call.NoRetry) : Error :=
  callError spec.seed st progress target f notRetried

/--
Runs the call from the planner's state `st`: sends the current request, asks the planner what
follows, and does what it says, until it delivers (by entering `k`) or fails.
-/
private partial def CallSpec.loop {α : Type} (spec : CallSpec) (st : Call.State)
    (progress : Progress) (k : Response BodyStream → Async α) : Async (Except Error α) := do
  let hop := st.current
  let body := match hop.body with
    | .original => spec.req.body
    | .empty => .empty
  let fail (e : Error) : Async (Except Error α) := do
    spec.observe (.fail e)
    return .error e
  -- The planner follows redirects to `https` too, which the client cannot reach yet.
  let plan ← match Client.plan hop.head with
    | .ok plan => pure plan
    | .error msg =>
      let f := notSent (.invalidRequest s!"cannot follow the redirect to {hop.head.uri}: {msg}")
      let target := s!"{hop.origin.host}:{hop.origin.port}"
      return ← fail (spec.error st { progress with reused := false, redispatched := false } target f none)
  let target := plan.target
  let prepared := Exchange.prepare spec.xcfg plan.head body
  if spec.client.config.observe.isSome then
    let wire := prepared.bytes.extract 0 prepared.headBytes
    spec.observe (.send hop.head target wire body.size (← IO.monoMsNow))
  let attempt : Attempt := {
    client := spec.client, plan, target, prepared, deadline := spec.deadline,
    observe := spec.observe }
  let (began, progress) ← attempt.run true { progress with redispatched := false }
  let outcome := match began with
    | .head _ head _ => Call.Outcome.response head
    | .failure f => .failure f
  let progress := { progress with
    furthest := progress.furthest.max (match began with
      | .head .. => .responseReceived
      | .failure f => f.delivery) }
  -- Should the wall clock fail, a `Retry-After` date measured from it looks decades away, and the
  -- response is delivered rather than retried; nothing here may throw while a connection is held.
  let wall ← try wallSec catch _ => pure 0
  let clock : Call.Clock := { now := ← IO.monoMsNow, wallSec := wall }
  let (st', step) := Call.plan st clock outcome
  spec.observe (.decide clock outcome step)
  -- A response that is not delivered has its body drained or its connection dropped first.
  let discardBody : Async Unit := do
    if let .head live _ held := began then
      settleHeld spec.client held (← live.abandon)
  match step, began with
  | .deliver, .head live head held =>
    spec.observe .deliver
    let info : CallInfo := {
      seed := spec.seed, connectRounds := progress.rounds, address := held.address,
      failedAttempts := progress.attempts, elapsedMs := (← IO.monoMsNow) - spec.started,
      connection := held.id, reused := held.reused, discarded := progress.discarded,
      idleCheckUs := progress.idleCheckUs, redispatched := progress.redispatched, hops := st.hops,
      retries := st.retries, uri := toString hop.head.uri }
    -- The stream keeps this for the body's errors; it holds neither the request nor its body.
    let seed := spec.seed
    let errorOf (f : Failure) : Error := callError seed st progress target f none
    let stream ← BodyStream.new live (settleHeld spec.client held) errorOf
    let result ← try
        pure (Except.ok (← k { line := head, body := stream, extensions := Extensions.empty.insert info }))
      catch e => pure (.error e)
    stream.release
    match result with
    | .ok a => return .ok a
    | .error e =>
      -- An error the stream raised that leaves the callback is the call's error; any other
      -- exception is the caller's, and goes on.
      match ← stream.raised.get with
      | some (err, message) => if toString e == message then return .error err else throw e
      | none => throw e
  | .follow _, _ =>
    discardBody
    spec.loop st' progress k
  | .retry delay _, _ =>
    discardBody
    -- The delay runs from the time the planner decided, and is never slept past the deadline (the
    -- planner made it end before the deadline when it decided).
    let endsAt := min (clock.now + delay) spec.deadline
    spec.observe (.wait endsAt)
    sleepUntil endsAt
    spec.loop st' progress k
  | .fail reason, _ =>
    discardBody
    let (status, written) := match began with
      | .head live head _ => (some head.status, live.ex.written)
      | .failure f => (none, f.written)
    let e := match reason with
      | .failure f why => spec.error st progress target f (some why)
      | .tooManyRedirects limit =>
        spec.error st progress target
          { cause := .tooManyRedirects limit, delivery := .responseReceived, written, status } none
      | .deadline =>
        spec.error st progress target
          { cause := .timeout .deadline, delivery := .responseReceived, written, status,
            detail := "the deadline passed before the redirect could be followed" } none
    fail e
  | .deliver, .failure f =>
    -- The planner delivers only responses; should it not, the failure is the call's error.
    fail (spec.error st progress target f none)

/--
Makes a call whose response body may be read up to `maxBody` bytes, and hands the response to `k`.
-/
private def run {α : Type} (client : Client) (req : Request ByteArray) (maxBody : Nat)
    (k : Response BodyStream → Async α) : Async (Except Error α) := do
  let config := client.config
  let started ← IO.monoMsNow
  let deadline := started + config.deadlineMs
  let seed ← match config.backoffSeed with
    | some seed => pure seed
    | none => osSeed
  let refuse (cause : Cause) (target : String) : Except Error α :=
    .error { cause, delivery := .notSent, target, seed }
  let plan ← match plan req.line with
    | .ok plan => pure plan
    | .error msg => return refuse (.invalidRequest msg) ""
  let target := plan.target
  let xcfg ← match checkConfig config *> exchangeConfig config maxBody with
    | .ok xcfg => pure xcfg
    | .error cause => return refuse cause target
  let kind : Call.BodyKind := if req.body.isEmpty then .none else .bytes
  let st ← match Call.start config.policy req.line kind seed deadline with
    | .ok st => pure st
    | .error e => return refuse (.invalidRequest s!"the planner refuses the request: {reprStr e}") target
  let number ← client.calls.modifyGet fun n => (n, n + 1)
  let spec : CallSpec := { client, req, xcfg, seed, started, deadline, number }
  spec.observe (.start config.policy req.line kind req.body.size seed deadline xcfg.keepAlive)
  spec.loop st {} k

/--
Sends `req` and hands the final response to `k`, whose body `k` pulls with `BodyStream.read`.
Redirects and retries happen before `k` is entered: `k` sees only the final response.  The request's
target must be an absolute `http` URI; its body is sent with a `Content-Length`, and
`Connection: keep-alive` is added (`Connection: close` with pooling off).

```
let client ← LeanHttp.Client.new
let req := Std.Http.Request.get (.parse! "http://127.0.0.1:8080/big") |>.body .empty
let result ← client.withResponse req fun response => do
  let mut total := 0
  while let some bytes ← response.body.read do
    total := total + bytes.size
  return total
```

Each `read` asks the exchange core for more of the body, so the core reads from the socket only as
fast as `k` reads, and holds at most one read; a streamed body has no size limit.  When `k` ends,
normally or by an exception, the rest of the body is abandoned: read and discarded if it is at most
`Config.drainBytes` and arrives within `Config.drainMs`, keeping the connection for reuse, and
otherwise the connection is closed.  The stream must not be used after `k` ends; if it is, it raises
an error.  An error the stream raised (the connection closed early, a timeout) that leaves `k` makes
the call's result that `Error`; any other exception from `k` is raised again once the connection is
released.  The call's deadline (`Config.deadlineMs`) covers reading the body too.
-/
def withResponse {α : Type} (client : Client) (req : Request ByteArray)
    (k : Response BodyStream → Async α) : Async (Except Error α) :=
  client.run req (2 ^ 62) k

/--
Sends `req` and reads the whole response, up to `Config.maxBodyBytes`.  The request's target must be
an absolute `http` URI; its body is sent with a `Content-Length`, and `Connection: keep-alive` is
added (`Connection: close` with pooling off).  Redirects are followed and failures retried as the
configuration says (`Config.followRedirects`, `Config.maxRetriesPerHop` and the rest).

```
let client ← LeanHttp.Client.new { deadlineMs := 15 * 60 * 1000, readGapMs := 15 * 60 * 1000 }
let req := Std.Http.Request.post (.parse! "http://127.0.0.1:8080/v1/chat")
  |>.header! "Content-Type" "application/json"
  |>.body body
match ← client.request req with
| .ok response => ...
| .error err => if err.notSent then ... else ...
```

Never throws: every failure is an `Error`, which says how far the call got.
-/
def request (client : Client) (req : Request ByteArray) :
    Async (Except Error (Response ByteArray)) := do
  let started ← IO.monoMsNow
  let read (response : Response BodyStream) : Async (Response ByteArray) := do
    let body ← response.body.readAll
    let elapsedMs := (← IO.monoMsNow) - started
    let extensions := match response.extensions.get CallInfo with
      | some info => response.extensions.insert { info with elapsedMs }
      | none => response.extensions
    return { response with body, extensions }
  -- `readAll` raises only the stream's own errors, which `run` returns as the call's error; should
  -- anything else escape, it is reported as an error too.
  try client.run req client.config.maxBodyBytes read
  catch e =>
    return .error {
      cause := .peerClosed, delivery := .maybeDelivered, detail := s!"the client failed: {e}" }

/--
Like `request`, but throws the error as an `IO.Error` (its message says how far the call got).
-/
def send (client : Client) (req : Request ByteArray) : Async (Response ByteArray) := do
  match ← client.request req with
  | .ok response => return response
  | .error err => throw err.toIOError

end Client

end LeanHttp
