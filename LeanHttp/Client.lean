module

public import Std.Async.TCP
public import Std.Http.Data
public import Std.Sync.Mutex
public import LeanHttp.Config
public import LeanHttp.Connect
public import LeanHttp.Error
public import LeanHttp.Exchange
public import LeanHttp.Pool
public import LeanHttp.Wait

public section

/-!
# The client

`Client.request` makes one HTTP/1.1 call and reads the whole response into memory.  The calling task
does all the work: it takes a connection from the pool or opens one (name resolution, connecting),
and then drives the exchange core (`Exchange`), whose writes and reads it performs (at most one of
each in flight, so the response is read while a large request is still being written) and whose
deadlines it races against them.  Every decision about the exchange is the core's, and every
decision about which connection to use is the pool core's (`Pool`), which the client keeps under one
mutex: each pool operation is a quick pure step, and nothing waits while holding it.

An idle connection in the pool is a socket with no task and no pending operation.  A call that takes
one first watches it for `Config.idleCheckMs` (a bounded `waitReadable`, then `cancelRecv`): bytes,
the end of input or an error mean the server closed it or sent something unasked, such as a 408, so
the connection is closed and the call takes another.  Even a window of zero sees what arrived while
the connection was idle: the timer that ends the wait fires only after the event loop has polled the
socket once (`NOTES.md`).  When the exchange ends, the connection goes
back to the pool with the core's reuse verdict.  A call whose pooled connection turns out to be
closed anyway is sent once more, on a fresh connection, when that is safe (`redispatch?`): nothing
of it was written, or the server answered 408 before anything else, or the method is idempotent and
the connection closed before any byte of a response.  No receive is left pending when a call
returns: a pending receive on v4.34.1 can keep the process from exiting (`NOTES.md`).

With `Config.pool` off, every call opens a connection of its own, sends `Connection: close` and
drops the connection at the end, as milestone 1 did.

v4.34.1 can cancel a pending receive but not a pending connect, write or name lookup, so three
things can outlive a call that gave up on them: a connect attempt that was abandoned (its socket is
released when the kernel gives up on the SYN), a write the peer never accepts (its socket stays open
while the peer keeps the connection), and a name lookup that timed out (it runs on in libuv's thread
pool until the resolver gives up).  `NOTES.md` records what each costs.

Only connect failures are retried, since nothing has been sent when a connect fails; everything else
is reported with how far the request got (`Delivery`), so that the caller can decide.
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
  How many rounds of connect attempts were made, counting the successful one; 0 on a reused
  connection.
  -/
  connectRounds : Nat

  /--
  The address the call's connection is connected to.
  -/
  address : SocketAddress

  /--
  The connect attempts that did not win.
  -/
  failedAttempts : Array ConnectAttempt

  /--
  Milliseconds from the start of the call to the end of the response.
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
  Whether the call was sent a second time, on a fresh connection, after its pooled connection
  turned out to be closed.
  -/
  redispatched : Bool := false
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
  return { config, state }

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
Where a request goes and what goes on the wire, worked out from its absolute-form target.
-/
structure Plan where
  /--
  The host to connect to.
  -/
  host : URI.Host

  /--
  The port to connect to.
  -/
  port : UInt16

  /--
  The request head as sent: origin-form target, `Host` field filled in.
  -/
  head : Request.Head

/--
Works out where `head` goes.  Its target must be an absolute `http` URI; the head sent carries the
origin-form target (`/` for an empty path) and a `Host` field, unless it has one already.
-/
def plan (head : Request.Head) : Except String Plan := do
  let .absoluteForm uri := head.uri
    | throw "the request target must be an absolute URI, such as http://host:port/path"
  if uri.scheme.val != "http" then
    throw s!"unsupported scheme {uri.scheme.val}: this client speaks plain HTTP only"
  let some host := uri.host?
    | throw "the URI has no host"
  let port := uri.port
  let path := if uri.path.segments.isEmpty then { uri.path with absolute := true } else uri.path
  let headers ←
    if head.headers.contains Header.Name.host then
      pure head.headers
    else
      let value := URI.Origin.hostHeader { scheme := uri.scheme, host, port }
      match Header.Value.ofString? value with
      | some value => pure (head.headers.insert Header.Name.host value)
      | none => throw s!"cannot write a Host field for {value}"
  return { host, port, head := { head with uri := .originForm path uri.query, headers } }

/--
A seed for the backoff jitter, from the operating system.
-/
def osSeed : IO UInt64 := do
  let bytes ← IO.getRandomBytes 8
  return bytes.foldl (init := 0) fun acc b => (acc <<< 8) ||| b.toUInt64

/--
Stops a pending receive on `socket`, releasing the reference it holds.
-/
private def cancelReceive (socket : TCP.Socket.Client) : Async Unit :=
  (socket.recvSelector 0).unregisterFn

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
The exchange core's settings for one call of `config`: keep-alive when pooling is on.  Fails with
`invalidRequest` if `readGapMs` is zero, which would make every write and read due the moment it is
issued, or if `readChunkBytes` is zero, which would ask for reads that can return nothing.
-/
def exchangeConfig (config : Config) : Except Cause ExchangeConfig :=
  if hg : 0 < config.readGapMs then
    if hr : 0 < config.readChunkBytes then
      .ok {
        limits := config.limits, keepAlive := config.pool, maxInterim := config.maxInterimResponses,
        maxBody := config.maxBodyBytes, readChunk := config.readChunkBytes, readChunk_pos := hr,
        writeChunk := config.writeChunkBytes, gapMs := config.readGapMs, gapMs_pos := hg }
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
A socket operation the shell started for the exchange core, once it has completed.
-/
private inductive Completion where
  /--
  A read ended: bytes, end of input, or an error.
  -/
  | read (result : Except IO.Error (Option ByteArray))

  /--
  A write of `length` bytes ended.
  -/
  | wrote (length : Nat) (result : Except IO.Error Unit)

/--
What the shell holds while it drives an exchange: the operations in flight and what was delivered.
-/
private structure Driver where
  /--
  The read in flight.
  -/
  reading : Option (Task Completion) := none

  /--
  The write in flight.
  -/
  writing : Option (Task Completion) := none

  /--
  The final response head, once delivered.
  -/
  head : Option Response.Head := none

  /--
  The body chunks delivered so far, last first.
  -/
  chunks : List ByteArray := []

  /--
  Their total size.
  -/
  bodySize : Nat := 0

  /--
  Whether any read returned bytes.
  -/
  received : Bool := false

/--
Joins body chunks given last first.  The result is allocated here, so appending to it is done in
place.
-/
private def joinChunks (chunks : List ByteArray) (size : Nat) : ByteArray :=
  chunks.reverse.foldl (init := ByteArray.emptyWithCapacity size) (· ++ ·)

/--
How an exchange ended, as the shell saw it.
-/
inductive Ended where
  /--
  The response arrived in full, after `interim` interim responses, with the core's verdict on
  reusing the connection.
  -/
  | response (head : Response.Head) (body : ByteArray) (reusable : Bool) (interim : Nat)

  /--
  The exchange failed; `received` says whether any byte of a response had arrived.
  -/
  | failure (failure : Failure) (received : Bool)

/--
Drives `ex` on `socket`: performs `actions`, waits for the first operation to complete or the next
deadline, reports what happened, and repeats until the core finishes or fails.  It decides nothing
itself.  A receive still pending at the end is cancelled, so that none outlives the call.

The body is kept as a list of chunks and joined at the end.  Everything carried across a wait is
captured by a continuation that another thread may run, which marks it as shared between threads,
and the runtime never updates such an object in place: appending each chunk to one byte array
copied the whole body every time, quadratic in its length (both here and in milestone 1).
-/
private partial def drive (socket : TCP.Socket.Client) (ex : Exchange)
    (actions : Array ExchangeAction) (driver : Driver) : Async Ended := do
  let mut driver := driver
  for action in actions do
    match action with
    | .write bytes =>
      let task ← start (socket.send bytes)
      driver := { driver with writing := some (Task.map (sync := true) (Completion.wrote bytes.size) task) }
    | .read max =>
      let task ← start (socket.recv? max.toUInt64)
      driver := { driver with reading := some (Task.map (sync := true) Completion.read task) }
    | .deliverHead head => driver := { driver with head := some head }
    | .deliverBody bytes =>
      driver := { driver with
        chunks := bytes :: driver.chunks, bodySize := driver.bodySize + bytes.size }
    | .finish reusable =>
      if driver.reading.isSome then cancelReceive socket
      return match driver.head with
        | some head => .response head (joinChunks driver.chunks driver.bodySize) reusable ex.interim
        | none =>
          .failure { cause := .peerClosed, delivery := ex.delivery, written := ex.written }
            driver.received
    | .fail failure =>
      if driver.reading.isSome then cancelReceive socket
      return .failure failure driver.received
  let now ← IO.monoMsNow
  let wait := (ex.nextDeadline.getD now) - now
  let pending := driver.reading.toArray ++ driver.writing.toArray
  let (event, next) ← match ← awaitFirst pending wait with
    | none => pure (ExchangeEvent.tick, driver)
    | some (.read result) =>
      -- An empty read, which a receive of a positive size should not return, changes nothing in
      -- the core; no receive is pending after it, so the core's read gap ends the call.
      let event := match result with
        | .ok (some bytes) => ExchangeEvent.received bytes
        | .ok none => .endOfInput
        | .error err => .readFailed (toString err)
      let got := match result with
        | .ok (some bytes) => !bytes.isEmpty
        | _ => false
      pure (event, { driver with reading := none, received := driver.received || got })
    | some (.wrote length result) =>
      let event := match result with
        | .ok () => ExchangeEvent.written length
        | .error err => .writeFailed (toString err)
      pure (event, { driver with writing := none })
  let (ex, actions) := ex.step (← IO.monoMsNow) event
  drive socket ex actions next

/--
Runs the exchange of `prepared` on `socket` until it ends, with `deadline` for the whole call.  The
whole body is wanted, up to the limit, which the core enforces.
-/
private def exchangeOn (config : Config) (socket : TCP.Socket.Client) (prepared : PreparedRequest)
    (deadline : Nat) : Async Ended := do
  let now ← IO.monoMsNow
  let (ex, actions) := Exchange.begin prepared now deadline
  let (ex, more) := ex.step now (.wantBody (config.maxBodyBytes + 1))
  drive socket ex (actions ++ more) {}

/--
Why a call on a reused connection may be sent again on a fresh one.
-/
inductive Redispatch where
  /--
  No byte of the request was written: the server cannot have seen it.  Safe for any method.  The
  exchange core counts a request as possibly delivered from its first write on, so on a reused
  connection this arises only if the exchange fails before writing; the idle check is what catches a
  connection the server closed before the request.
  -/
  | notSent

  /--
  The server answered 408 (Request Timeout) before any other response: it did not process the
  request, and RFC 9110 section 15.5.9 lets a client repeat it.  Bytes a server sent on an idle
  connection before it saw the request are read as the response, and a 408 is what servers send
  before they close an idle connection.  Safe for any method.
  -/
  | requestTimeout

  /--
  The connection closed, or failed, before any byte of a response arrived: most likely the server
  closed the idle connection as the request went out.  The server may have acted on the request, so
  only an idempotent method is sent again, as Go's transport does (RFC 9110 section 9.2.2).
  -/
  | closedBeforeResponse
deriving Repr, DecidableEq

/--
Whether a call whose exchange on a reused connection ended as `ended` is sent again on a fresh
connection, and why.  It never is when the server may have acted on a request whose method is not
idempotent, except after a 408, which says it did not.
-/
def redispatch? (method : Method) : Ended → Option Redispatch
  | .response head _ _ interim =>
    if head.status == .requestTimeout && interim == 0 then some .requestTimeout else none
  | .failure f received =>
    if f.delivery == .notSent && (f.cause matches .peerClosed) then some .notSent
    else if !received && f.delivery == .maybeDelivered && (f.cause matches .peerClosed) &&
        method.isIdempotent then
      some .closedBeforeResponse
    else none

/--
What the client knows about a call so far, for its result or error.
-/
private structure Progress where
  /--
  Rounds of connect attempts.
  -/
  rounds : Nat := 0

  /--
  Idle connections closed by the idle check.
  -/
  discarded : Nat := 0

  /--
  Microseconds spent in idle checks.
  -/
  idleCheckUs : Nat := 0

  /--
  Whether the call was sent a second time.
  -/
  redispatched : Bool := false

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
  The connect attempts that did not win, for a fresh connection.
  -/
  attempts : Array ConnectAttempt := #[]

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
What one call works with: its client, where it goes, what it sends, and its seed and deadline.
-/
private structure Call where
  /-- The client. -/
  client : Client
  /-- Where the request goes. -/
  plan : Plan
  /-- The origin, as `host:port`. -/
  target : String
  /-- The request, encoded. -/
  prepared : PreparedRequest
  /-- The seed of the backoff jitter. -/
  seed : UInt64
  /-- When the call started. -/
  started : Nat
  /-- The deadline of the whole call. -/
  deadline : Nat

/--
A failed call's result.
-/
private def Call.fail (call : Call) (cause : Cause) (delivery : Delivery) (rounds : Nat := 0)
    (status : Option Status := none) (detail : String := "") (written : Nat := 0)
    (reused redispatched : Bool := false) : Except Error (Response ByteArray) :=
  .error {
    cause, delivery, written, target := call.target, seed := call.seed, connectRounds := rounds,
    status, detail, reused, redispatched }

/--
Opens a connection, under pool id `id` if pooling is on; drops the id if the connect fails.
-/
private def Call.connect (call : Call) (id : Option ConnId) (progress : Progress) :
    Async (Except (Except Error (Response ByteArray)) (Held × Progress)) := do
  let config := call.client.config
  let r := progress.redispatched
  -- A call sent again may get here with its deadline gone: no lookup is started then, since a lookup
  -- cannot be cancelled and an abandoned one can delay exit (`NOTES.md`).
  if call.deadline ≤ (← IO.monoMsNow) then
    if let some id := id then dropConn call.client id
    return .error (call.fail (.timeout .deadline) .notSent progress.rounds (redispatched := r))
  -- `Connect.run` reports its failures as values; should it throw anyway, the id must not stay
  -- checked out, so the exception counts as a failed connect.
  let connected : Except String (Except ConnectError Connected) ←
    try pure (.ok (← Connect.run config (.ofHost call.plan.host) call.plan.port call.seed call.deadline))
    catch e => pure (.error (toString e))
  match connected with
  | .ok (.ok c) =>
    let held : Held :=
      { socket := c.socket, address := c.address, id, reused := false, attempts := c.attempts }
    return .ok (held, { progress with rounds := progress.rounds + c.rounds })
  | .ok (.error e) =>
    if let some id := id then dropConn call.client id
    let rounds := progress.rounds
    return .error <| match e with
      | .resolve host detail => call.fail (.resolve host detail) .notSent (redispatched := r)
      | .exhausted attempts n => call.fail (.connect attempts) .notSent (rounds + n) (redispatched := r)
      | .deadline attempts n =>
        call.fail (.timeout .deadline) .notSent (rounds + n)
          (detail := (Cause.connect attempts).describe) (redispatched := r)
  | .error detail =>
    if let some id := id then dropConn call.client id
    return .error (call.fail (.connect #[]) .notSent progress.rounds (detail := detail) (redispatched := r))

/--
Takes a connection from the pool for the call: an idle one that passes the idle check (closing those
that fail it), or a new one, waiting while the origin is at its active cap, within the deadline.
-/
private partial def Call.acquire (call : Call) (reuse : Bool) (progress : Progress) :
    Async (Except (Except Error (Response ByteArray)) (Held × Progress)) := do
  let config := call.client.config
  let left := call.deadline - (← IO.monoMsNow)
  if left == 0 then
    return .error (call.fail (.timeout .deadline) .notSent
      (detail := "the deadline passed while taking a connection from the pool")
      (redispatched := progress.redispatched))
  match ← takeConn call.client call.target reuse with
  | .closed =>
    return .error (call.fail .localClose .notSent (detail := "the client was closed")
      (redispatched := progress.redispatched))
  | .atCap freed =>
    let left := call.deadline - (← IO.monoMsNow)
    if left == 0 then
      return .error (call.fail (.timeout .deadline) .notSent
        (detail := "waiting for a connection: the origin is at maxActivePerOrigin")
        (redispatched := progress.redispatched))
    match ← (try (some <$> awaitFirst #[freed.result?] left) catch _ => pure none) with
    | some _ => call.acquire reuse progress
    | none =>
      return .error (call.fail (.timeout .deadline) .notSent
        (detail := "waiting for a connection failed") (redispatched := progress.redispatched))
  | .fresh id => call.connect (some id) progress
  | .reuse id idle =>
    let held : Held := { socket := idle.socket, address := idle.address, id, reused := true }
    if !config.idleCheck then
      return .ok (held, progress)
    let t0 ← IO.monoNanosNow
    let window := min config.idleCheckMs (call.deadline - (← IO.monoMsNow))
    let clean ← try idleClean idle.socket window catch _ => pure false
    let t1 ← IO.monoNanosNow
    let progress := { progress with idleCheckUs := progress.idleCheckUs + (t1 - t0) / 1000 }
    if clean then
      return .ok (held, progress)
    dropConn call.client id
    call.acquire reuse { progress with discarded := progress.discarded + 1 }

/--
Makes the call: takes or opens a connection, runs the exchange on it, gives the connection back
with the core's verdict, and sends the call once more on a fresh connection if the pooled one
turned out to be closed and `redispatch?` says that is safe.
-/
private partial def Call.attempt (call : Call) (reuse : Bool) (progress : Progress) :
    Async (Except Error (Response ByteArray)) := do
  let config := call.client.config
  let got ← if config.pool then call.acquire reuse progress else do
      -- Without pooling the pool only records whether the client was closed.
      let closed ← call.client.withState (β := Bool) fun s => pure (s, s.pool.closed)
      if closed then
        pure (.error (call.fail .localClose .notSent (detail := "the client was closed")))
      else
        call.connect none progress
  let (held, progress) ← match got with
    | .ok hp => pure hp
    | .error e => return e
  -- The shell reports socket errors to the core as events; should anything throw anyway, the
  -- connection is dropped like after any failure, with no receive left pending, and the call is
  -- not sent again.
  let ended ← try exchangeOn config held.socket call.prepared call.deadline
    catch e =>
      try held.socket.native.cancelRecv catch _ => pure ()
      let failure : Failure := {
        cause := .peerClosed, delivery := .maybeDelivered, written := 0,
        detail := s!"the client failed: {e}" }
      pure (.failure failure true)
  let why := if held.reused && !progress.redispatched then redispatch? call.prepared.method ended
    else none
  -- The second attempt describes the call, but the first one was written: unless the server said
  -- with a 408 that it did not process it, it may have been delivered even if the second was not.
  let again : Async (Except Error (Response ByteArray)) := do
    let result ← call.attempt false { progress with redispatched := true }
    return result.mapError fun e =>
      if why == some .closedBeforeResponse && e.delivery == .notSent then
        { e with delivery := .maybeDelivered }
      else e
  match ended with
  | .response head body reusable _ =>
    if let some id := held.id then
      giveBack call.client id held.socket held.address (reusable && why.isNone)
    if why.isSome then
      again
    else
      let finished ← IO.monoMsNow
      let info : CallInfo := {
        seed := call.seed, connectRounds := progress.rounds, address := held.address,
        failedAttempts := held.attempts, elapsedMs := finished - call.started, connection := held.id,
        reused := held.reused, discarded := progress.discarded, idleCheckUs := progress.idleCheckUs,
        redispatched := progress.redispatched }
      return .ok { line := head, body, extensions := Extensions.empty.insert info }
  | .failure f _ =>
    if let some id := held.id then
      -- An exchange that timed out before writing anything (its deadline had passed when it began)
      -- left the connection as it was.
      if f.delivery == .notSent && (f.cause matches .timeout _) then
        giveBack call.client id held.socket held.address true
      else dropConn call.client id
    if why.isSome then
      again
    else
      return call.fail f.cause f.delivery progress.rounds f.status f.detail f.written held.reused
        progress.redispatched

/--
Sends `req` and reads the whole response.  The request's target must be an absolute `http` URI;
its body is sent with a `Content-Length`, and `Connection: keep-alive` is added (`Connection: close`
with pooling off).

```
let client ← LeanHttp.Client.new { deadlineMs := 15 * 60 * 1000, readGapMs := 15 * 60 * 1000 }
let req := Std.Http.Request.post (.parse! "http://127.0.0.1:8080/v1/chat")
  |>.header! "Content-Type" "application/json"
  |>.body body
match ← client.request req with
| .ok response => ...
| .error err => if err.notSent then ... else ...
```

Never throws: every failure is an `Error`, which says how far the request got.
-/
def request (client : Client) (req : Request ByteArray) :
    Async (Except Error (Response ByteArray)) := do
  let config := client.config
  let started ← IO.monoMsNow
  let deadline := started + config.deadlineMs
  let seed ← match config.backoffSeed with
    | some seed => pure seed
    | none => osSeed
  let refuse (cause : Cause) (target : String) : Except Error (Response ByteArray) :=
    .error { cause, delivery := .notSent, target, seed }
  let plan ← match plan req.line with
    | .ok plan => pure plan
    | .error msg => return refuse (.invalidRequest msg) ""
  let target := s!"{plan.host}:{plan.port}"
  let checked := do
    checkConfig config
    return Exchange.prepare (← exchangeConfig config) plan.head req.body
  let prepared ← match checked with
    | .ok prepared => pure prepared
    | .error cause => return refuse cause target
  let call : Call := { client, plan, target, prepared, seed, started, deadline }
  call.attempt true {}

/--
Like `request`, but throws the error as an `IO.Error` (its message says how far the request got).
-/
def send (client : Client) (req : Request ByteArray) : Async (Response ByteArray) := do
  match ← client.request req with
  | .ok response => return response
  | .error err => throw err.toIOError

end Client

end LeanHttp
