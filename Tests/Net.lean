import LeanHttp

/-!
# Real-socket test driver

Run by `tests/net/run.sh` against local servers.  Prints one line per call and, for repeated calls,
a summary of the per-call times; the last line says when `main` returned, so that the harness can
tell how long the process took to exit after that.

```
net-client call <METHOD> <URL> [key=value ...]
  body=N         send N bytes of body (default 0)
  repeat=N       make N calls one after another (default 1)
  pause=MS       wait between calls (default 0)
  concurrent=N   make N calls at once through the one client, repeat times (default 1)
  close=1        close the client after the calls
  deadline=MS gap=MS connect=MS stagger=MS retries=N budget=N base=MS cap=MS maxbody=N interim=N
  ca=PATH        trust the certificates of this PEM file for https (Config.tls.caFile)
  tlshs=MS       the TLS handshake's time limit (Config.tlsHandshakeTimeoutMs)
  seed=N nodelay=0|1 pool=0|1 idlecheck=MS|off maxidle=N idletimeout=MS maxactive=N
  follow=0|1 maxredirects=N retry429=0|1 retry503=0|1 maxretryafter=MS drainbytes=N drainms=MS
  auth=VALUE cookie=VALUE   send an Authorization or Cookie field
  trace=0        do not check each call's steps against the planner (default: check, `Call.validate`)
  showtrace=1    print each call's steps
  linger=MS      after the calls, wait and count open descriptors again
  cancel=MS      give the calls a cancellation token, cancelled MS ms after the first call starts
                 (0: before it starts), or after the mark of after=
  cancelcalls=N  give the token to the first N calls only (default: all)
  cancelfrom=N   and not to the calls before call N (default 0)
  shutdown=MS    shut the client down MS ms after the first call starts, or after the mark of
                 after=, then make one more call
  after=MARK[:N] measure cancel=MS or shutdown=MS from the Nth time (default 1) any call reaches
                 MARK instead: send (a request goes out), follow (the planner follows a redirect),
                 wait (the wait before a retry begins), deliver (the response goes to the
                 callback), read (a read of the body returns bytes, stream); or idle, hold (stream)
                 or pull (upload), whose sleep, or the producer's delay, the action falls MS ms into
  log=PATH logtext=TEXT logcount=N
                 and not before N (default 1) more occurrences of TEXT are in the file PATH (a
                 server's log) than when the first call started
                 Prints when the action was taken, from the start of the first call.
net-client stream <METHOD> <URL> [key=value ...]
  Calls `Client.withResponse` and reads the body in pulls; the options of `call`, and
  pull=N          bytes asked for in each read (default 65536)
  stop=N          leave the callback once N bytes were read (default: read to the end)
  throw=1         raise an exception inside the callback, after reading
  escape=1        keep the stream, and read from it after the callback ended
  race=MS         start a task that reads the stream, and leave the callback MS ms later while
                  that read is in progress
  whole=1         a control: `Client.request`, which reads the whole body into memory
  idle=MS         sleep MS inside the callback before reading the body
  hold=MS         once the pulls stop (stop=N), sleep MS and read once more
  Prints when the first call's callback was entered, and the peak resident memory of the process
  at the end.
net-client upload <METHOD> <URL> [key=value ...]
  Calls `Client.upload` with a streamed body that a producer makes as it is pulled: byte k of the
  body is k % 251.  The options of `call` (repeat, deadline, gap, retries, ...), and
  size=N          bytes the producer gives in all (default 0)
  chunk=N         bytes per chunk (default 16384)
  declare=N|none  the size declared (default: size); none sends the body chunked
  fail=K          the producer raises an error at pull K, counting from 0
  delay=MS        the producer waits MS before each chunk
  stall=MS        with after=pull, the producer waits MS after the action rather than the rest of
                  its delay
  bytes=1         a control: the same body as one byte array, through `Client.request`
  Prints, per call, the outcome as `call` does with the producer's pulls and the bytes it gave,
  and at the end the peak resident memory of the process.
net-client idlecheck <PORT> [key=value ...]
  Measures `Client.idleClean` on fresh connections to tests/net/idle.py, after it sent bytes, closed
  or reset the connection, or did nothing (scenario=data|fin|rst|none).
  n=N ms=MS scenario=S wait=MS
net-client rawpost <PORT> [key=value ...]
  A control that bypasses the client: POSTs with the head and the body in two writes.
  n=N size=N keepalive=0|1 nodelay=0|1
net-client backoff <SEED> [n=N base=MS cap=MS]
  Prints the backoff schedule for SEED.
```
-/

open Std.Http Std.Async Std.Net LeanHttp

/-- `key=value` arguments. -/
def parseKV (args : List String) : List (String × String) :=
  args.filterMap fun a =>
    match a.splitOn "=" with
    | [k, v] => some (k, v)
    | _ => none

def getNat (kv : List (String × String)) (key : String) (default : Nat) : Nat :=
  (kv.lookup key >>= String.toNat?).getD default

def parseMethod : String → Option Method
  | "GET" => some .get
  | "POST" => some .post
  | "HEAD" => some .head
  | "PUT" => some .put
  | "DELETE" => some .delete
  | _ => none

/-- Milliseconds with three decimals, from nanoseconds. -/
def fmtMs (ns : Nat) : String :=
  let us := ns / 1000
  let frac := toString (us % 1000)
  s!"{us / 1000}.{String.ofList (List.replicate (3 - frac.length) '0')}{frac}"

def configOf (kv : List (String × String)) : Config :=
  let d : Config := {}
  { deadlineMs := getNat kv "deadline" d.deadlineMs
    readGapMs := getNat kv "gap" d.readGapMs
    connectTimeoutMs := getNat kv "connect" d.connectTimeoutMs
    connectStaggerMs := getNat kv "stagger" d.connectStaggerMs
    maxRetriesPerHop := getNat kv "retries" d.maxRetriesPerHop
    maxBodyBytes := getNat kv "maxbody" d.maxBodyBytes
    maxInterimResponses := getNat kv "interim" d.maxInterimResponses
    backoffSeed := (kv.lookup "seed" >>= String.toNat?).map (·.toUInt64)
    noDelay := getNat kv "nodelay" 1 == 1
    pool := getNat kv "pool" 1 == 1
    idleCheck := kv.lookup "idlecheck" != some "off"
    idleCheckMs := getNat kv "idlecheck" d.idleCheckMs
    maxIdlePerOrigin := getNat kv "maxidle" d.maxIdlePerOrigin
    idleTimeoutMs := getNat kv "idletimeout" d.idleTimeoutMs
    maxActivePerOrigin := kv.lookup "maxactive" >>= String.toNat?
    retryBudget := getNat kv "budget" d.retryBudget
    backoffBaseMs := getNat kv "base" d.backoffBaseMs
    backoffCapMs := getNat kv "cap" d.backoffCapMs
    followRedirects := getNat kv "follow" 1 == 1
    maxRedirects := getNat kv "maxredirects" d.maxRedirects
    retry429 := getNat kv "retry429" 0 == 1
    retry503 := getNat kv "retry503" 0 == 1
    maxRetryAfterMs := getNat kv "maxretryafter" d.maxRetryAfterMs
    drainBytes := getNat kv "drainbytes" d.drainBytes
    drainMs := getNat kv "drainms" d.drainMs
    tlsHandshakeTimeoutMs := getNat kv "tlshs" d.tlsHandshakeTimeoutMs
    tls := { caFile := (kv.lookup "ca").map System.FilePath.mk } }

/-- The steps of every call, by call number, as `Config.observe` reports them. -/
abbrev Traces := IO.Ref (Std.HashMap Nat (Array Call.Event))

/-- `config` with an observer that records every call's steps in `traces`, unless `trace=0`. -/
def withTraces (config : Config) (kv : List (String × String)) (traces : Traces)
    (hook : Call.Event → BaseIO Unit := fun _ => pure ()) : Config :=
  let record := getNat kv "trace" 1 != 0
  { config with observe := some fun n e => do
    if record then traces.modify fun m => m.insert n ((m.getD n #[]).push e)
    hook e }

/--
Checks every recorded call against the planner (`Call.validate`) and prints the result, the
delays of its retries as the planner gave them and the gaps the client left before sending again.
-/
def reportTraces (kv : List (String × String)) (traces : Traces) : IO Unit := do
  let m ← traces.get
  for n in (m.toList.map (·.1)).mergeSort do
    let events := m.getD n #[]
    if getNat kv "showtrace" 0 == 1 then
      for e in events do IO.println s!"trace call {n}: {e.describe}"
    match Call.validate events with
    | .ok steps => IO.println s!"trace call {n} ok steps={steps}"
    | .error msg => IO.println s!"trace call {n} FAIL {msg}"
    -- Each retry decision with the time the next request went out.
    let mut delays := #[]
    let mut gaps := #[]
    for h : i in [0:events.size] do
      if let .decide clock _ (.retry delay _) := events[i] then
        -- The retry's request is the next send, after the wait.
        let next := (events.extract (i + 1) events.size).findSome? fun
          | .send _ _ _ _ time => some time
          | _ => none
        if let some time := next then
          delays := delays.push delay
          gaps := gaps.push (time - clock.now)
    if !delays.isEmpty then
      IO.println s!"trace call {n} retry delays={delays.toList} gaps={gaps.toList}"

def attemptsText (attempts : Array ConnectAttempt) : String :=
  let parts := attempts.toList.map fun a =>
    let o := match a.outcome with
      | .timedOut => "timedOut"
      | .failed m => s!"failed({m})"
      | .abandoned => "abandoned"
    s!"{a.address}#{a.round}:{o}"
  "[" ++ String.intercalate ", " parts ++ "]"

def percentile (sorted : Array Nat) (p : Nat) : Nat :=
  if sorted.isEmpty then 0 else sorted[min (sorted.size - 1) (sorted.size * p / 100)]!

def summary (label : String) (times : Array Nat) : String :=
  let s := times.qsort (· < ·)
  s!"summary {label} n={s.size} min={fmtMs (percentile s 0)} p50={fmtMs (percentile s 50)} " ++
    s!"p90={fmtMs (percentile s 90)} max={fmtMs (s.back?.getD 0)} ms"

/-- The number of open file descriptors of this process. -/
def openFds : IO Nat := do
  return (← System.FilePath.readDir "/proc/self/fd").size

/-- Runs `action` `ms` milliseconds from now, from a task of its own; at once for 0. -/
def after (ms : Nat) (action : BaseIO Unit) : IO Unit := do
  if ms == 0 then action
  else discard <| start (do Std.Async.sleep (.ofNat ms); action : Async Unit)

/--
Where the action of `cancel=MS` or `shutdown=MS` is measured from (`after=MARK[:N]`): the first call's
start, or the `N`th time (default the first) any call of the client reaches one of these steps.
-/
inductive Mark where
  /-- The first call starts (the default). -/
  | start
  /-- A call's request goes out (`Call.Event.send`): the call begins taking a connection for it. -/
  | send
  /-- The planner decides to follow a redirect, before the redirect's body is drained. -/
  | follow
  /-- The wait before a retry begins. -/
  | wait
  /-- The response is about to be handed to the callback. -/
  | deliver
  /-- A read of the body by the callback (`stream`) returned bytes. -/
  | read
  /-- The callback's `idle` sleep; the callback itself acts `MS` ms into it, then sleeps the rest. -/
  | idle
  /-- The callback's `hold` sleep, in the same way. -/
  | hold
  /-- A call of the upload's producer; the producer acts `MS` ms into its `delay`, then waits the rest. -/
  | pull
  deriving BEq

def Mark.parse? : String → Option Mark
  | "start" => some .start
  | "send" => some .send
  | "follow" => some .follow
  | "wait" => some .wait
  | "deliver" => some .deliver
  | "read" => some .read
  | "idle" => some .idle
  | "hold" => some .hold
  | "pull" => some .pull
  | _ => none

/--
The cancellation (`cancel=MS`, of a token the calls get) or shutdown (`shutdown=MS`) of a run, and
when it is taken: `MS` ms after its mark (`after=`), and, with `log=PATH logtext=TEXT`, not before
`logcount` (default 1) more occurrences of `TEXT` are in the file `PATH` than when the first call
started: a server's log saying that it has the request, so that the action is placed at a stage of
the call a server sees and the client does not report.
-/
structure Trigger where
  /-- `cancel` or `shutdown`; `none` without either option. -/
  label : Option String
  mark : Mark
  count : Nat
  ms : Nat
  log? : Option (System.FilePath × String × Nat)
  /-- The token of `cancel=MS`. -/
  token : Option Std.CancellationToken
  /-- What is done: cancel the token, or shut the client down (set once there is a client). -/
  action : IO.Ref (BaseIO Unit)
  /-- How often the mark was reached. -/
  seen : IO.Ref Nat
  /-- Whether the mark was reached, for a trigger that also waits for a log. -/
  reached : IO.Ref Bool
  /-- Whether the action was taken, or is being taken. -/
  claimed : IO.Ref Bool
  /-- When the first call started (`IO.monoNanosNow`). -/
  armedAt : IO.Ref Nat
  /-- When the action was taken, in nanoseconds from the start of the first call. -/
  firedAt : IO.Ref (Option Nat)
  /-- The occurrences of the log's text when the first call started. -/
  logBase : IO.Ref Nat
  /-- Set when the calls are over, so that a trigger still waiting for its log stops. -/
  done : IO.Ref Bool

def triggerOf (kv : List (String × String)) : IO Trigger := do
  let (label, ms) ← match kv.lookup "cancel" >>= String.toNat?, kv.lookup "shutdown" >>= String.toNat? with
    | some _, some _ => throw (.userError "give cancel=MS or shutdown=MS, not both")
    | some ms, none => pure (some "cancel", ms)
    | none, some ms => pure (some "shutdown", ms)
    | none, none => pure (none, 0)
  let (mark, count) ← match (kv.lookup "after").map (·.splitOn ":") with
    | none => pure (Mark.start, 1)
    | some [m] => match Mark.parse? m with
      | some mark => pure (mark, 1)
      | none => throw (.userError s!"after={m}: no such mark")
    | some [m, n] => match Mark.parse? m, n.toNat? with
      | some mark, some n => pure (mark, n)
      | _, _ => throw (.userError s!"after={m}:{n}: no such mark, or not a count")
    | some _ => throw (.userError "after=MARK or after=MARK:N")
  let log? ← match kv.lookup "log", kv.lookup "logtext" with
    | some path, some text => pure (some (System.FilePath.mk path, text, getNat kv "logcount" 1))
    | none, none => pure none
    | _, _ => throw (.userError "log=PATH and logtext=TEXT go together")
  if log?.isSome && (mark == .idle || mark == .hold || mark == .pull) then
    throw (.userError "a log cannot be waited for inside the callback or the producer")
  let token ← if label == some "cancel" then some <$> Std.CancellationToken.new else pure none
  let cancel : BaseIO Unit := match token with
    | some t => t.cancel .cancel
    | none => pure ()
  return {
    label, mark, count, ms, log?, token, action := ← IO.mkRef cancel, seen := ← IO.mkRef 0,
    reached := ← IO.mkRef false, claimed := ← IO.mkRef false, armedAt := ← IO.mkRef 0,
    firedAt := ← IO.mkRef none, logBase := ← IO.mkRef 0, done := ← IO.mkRef false }

/-- With `shutdown=MS`, the client to shut down. -/
def Trigger.setClient (t : Trigger) (client : Client) : BaseIO Unit := do
  if t.label == some "shutdown" then t.action.set client.shutdownNow

/-- Takes the action, once, and records when. -/
def Trigger.fire (t : Trigger) : BaseIO Unit := do
  if ← t.claimed.modifyGet fun c => (c, true) then return
  t.firedAt.set (some ((← IO.monoNanosNow) - (← t.armedAt.get)))
  (← t.action.get)

/-- The occurrences of `text` in the file `path` (0 if it cannot be read). -/
def occurrences (path : System.FilePath) (text : String) : BaseIO Nat := do
  match ← (IO.FS.readFile path).toBaseIO with
  | .ok s => return (s.splitOn text).length - 1
  | .error _ => return 0

/-- Waits, for at most 60 s, until the mark was reached and the log has the text, then acts. -/
def Trigger.poll (t : Trigger) (path : System.FilePath) (text : String) (n : Nat) : Async Unit := do
  for _ in [0:30000] do
    if ← t.done.get then return
    if (← t.reached.get) && (← occurrences path text) ≥ (← t.logBase.get) + n then
      if t.ms > 0 then Std.Async.sleep (.ofNat t.ms)
      t.fire
      return
    Std.Async.sleep (.ofNat 2)

/-- The mark `m` was reached: the action follows `ms` ms after its `count`th time (or the log). -/
def Trigger.reach (t : Trigger) (m : Mark) : BaseIO Unit := do
  if t.label.isNone || t.mark != m then return
  let n ← t.seen.modifyGet fun n => (n + 1, n + 1)
  if n != t.count then return
  if t.log?.isSome then t.reached.set true
  else (after t.ms t.fire).catchExceptions fun _ => pure ()

/-- An observer of the calls' steps (`Config.observe`) that reaches the marks they are. -/
def Trigger.observe (t : Trigger) : Call.Event → BaseIO Unit
  | .send .. => t.reach .send
  | .decide _ _ (.follow _) => t.reach .follow
  | .wait _ => t.reach .wait
  | .deliver => t.reach .deliver
  | _ => pure ()

/--
Sleeps `total` ms, for the mark `m` (`idle`, `hold`, `pull`): if this is its `count`th time, takes
the action `ms` ms into the sleep, from this task, so that it falls inside the sleep whatever the
load, and then sleeps the rest, or `rest` ms if given.
-/
def Trigger.sleepAt (t : Trigger) (m : Mark) (total : Nat) (rest : Option Nat := none) :
    Async Unit := do
  let mine ← if t.label.isSome && t.mark == m then
      (· == t.count) <$> t.seen.modifyGet fun n => (n + 1, n + 1)
    else pure false
  if mine then
    let first := min t.ms total
    if first > 0 then Std.Async.sleep (.ofNat first)
    t.fire
    let rest := rest.getD (total - first)
    if rest > 0 then Std.Async.sleep (.ofNat rest)
  else if total > 0 then Std.Async.sleep (.ofNat total)

/-- Arms the trigger as the first call starts, and returns that time (`IO.monoNanosNow`). -/
def Trigger.arm (t : Trigger) : IO Nat := do
  let now ← IO.monoNanosNow
  t.armedAt.set now
  if t.label.isNone then return now
  match t.log? with
  | some (path, text, n) =>
    t.logBase.set (← occurrences path text)
    if t.mark == .start then t.reached.set true
    discard <| start (t.poll path text n)
  | none => if t.mark == .start then after t.ms t.fire
  return now

/-- Prints when the action was taken, from the start of the first call, and stops a waiting trigger. -/
def Trigger.report (t : Trigger) : IO Unit := do
  t.done.set true
  let some label := t.label | return
  match ← t.firedAt.get with
  | some ns => IO.println s!"{label} fired at ms={fmtMs ns}"
  | none => IO.println s!"{label} never fired"

/-- The token call `k` gets: the calls from `cancelfrom` (default 0) up to `cancelcalls` get it. -/
def tokenFor (kv : List (String × String)) (t : Trigger) (k : Nat) : Option Std.CancellationToken :=
  if getNat kv "cancelfrom" 0 ≤ k && k < getNat kv "cancelcalls" (2 ^ 62) then t.token else none

/-- One line describing call `i`'s result. -/
def describeCall (i : Nat) (ns : Nat) (result : Except Error (Response ByteArray)) : String :=
  match result with
  | .ok resp =>
    let infoText := match resp.extensions.get CallInfo with
      | some i =>
        s!"rounds={i.connectRounds} address={i.address} seed={i.seed} " ++
          s!"failed_attempts={attemptsText i.failedAttempts} conn={i.connection} reused={i.reused} " ++
          s!"discarded={i.discarded} check_us={i.idleCheckUs} redispatched={i.redispatched} " ++
          s!"hops={i.hops} retries={i.retries} uri={i.uri} tls={i.tls.getD "none"}"
      | none => "no CallInfo"
    let preview := (String.fromUTF8? (resp.body.extract 0 40)).getD "<binary>"
    s!"call {i} ok status={resp.line.status.toCode} bytes={resp.body.size} ms={fmtMs ns} " ++
      s!"{infoText} body_start={repr preview}"
  | .error err =>
    let attempts := match err.cause with
      | .connect a => s!" attempts={attemptsText a}"
      | _ => ""
    s!"call {i} error delivery={err.delivery.name} ms={fmtMs ns} rounds={err.connectRounds} " ++
      s!"seed={err.seed} reused={err.reused} redispatched={err.redispatched} " ++
      s!"hops={err.hops} retries={err.retries} not_retried={(err.notRetried.map reprStr).getD "none"} " ++
      s!"status={err.status.map Status.toCode} cause={repr err.cause.describe} " ++
      s!"detail={repr err.detail}{attempts}"

/-- The request a `call` or `stream` command describes: method, URL, body and fields. -/
def requestOf (methodName url : String) (kv : List (String × String)) : IO (Request ByteArray) := do
  let some method := parseMethod methodName
    | throw (.userError s!"unknown method {methodName}")
  let some uri := URI.parse? url
    | throw (.userError s!"cannot parse {url}")
  let body := ByteArray.mk (Array.replicate (getNat kv "body" 0) 'x'.toUInt8)
  let field (name : Header.Name) (key : String) (headers : Headers) : IO Headers :=
    match kv.lookup key with
    | none => pure headers
    | some v => match Header.Value.ofString? v with
      | some value => pure (headers.insert name value)
      | none => throw (.userError s!"not a field value: {v}")
  let headers ← field Header.Name.authorization "auth" .empty >>= field Header.Name.cookie "cookie"
  return { line := { method, version := .v11, uri := .absoluteForm uri, headers }, body }

def runCalls (args : List String) : IO Unit := do
  let (methodName, url, rest) ← match args with
    | m :: u :: rest => pure (m, u, rest)
    | _ => throw (.userError "usage: net-client call <METHOD> <URL> [key=value ...]")
  let kv := parseKV rest
  let req ← requestOf methodName url kv
  let traces : Traces ← IO.mkRef {}
  let trigger ← triggerOf kv
  let config := withTraces (configOf kv) kv traces trigger.observe
  let client ← Client.new config
  trigger.setClient client
  let n := getNat kv "repeat" 1
  let pause := getNat kv "pause" 0
  let concurrent := getNat kv "concurrent" 1
  let mut times := #[]
  let mut checks := #[]
  let mut oks := 0
  let mut k := 0
  for round in [0:n] do
    if round > 0 && pause > 0 then IO.sleep pause.toUInt32
    let t0 ← if round == 0 then trigger.arm else IO.monoNanosNow
    if concurrent ≤ 1 then
      let result ← (client.request req (tokenFor kv trigger k)).block
      let t1 ← IO.monoNanosNow
      times := times.push (t1 - t0)
      if let .ok resp := result then
        if let some info := resp.extensions.get CallInfo then
          if info.reused then checks := checks.push (info.idleCheckUs * 1000)
      if result matches .ok _ then oks := oks + 1
      if n ≤ 20 || round < 3 then
        IO.println (describeCall k (t1 - t0) result)
      k := k + 1
    else
      -- All the calls of a round start at once; each records its own time.
      let mut tasks := #[]
      for j in [0:concurrent] do
        let cancel := tokenFor kv trigger (k + j)
        let task ← start do
          let r ← client.request req cancel
          return (r, ← IO.monoNanosNow)
        tasks := tasks.push task
      for task in tasks do
        match ← IO.wait task with
        | .ok (result, t1) =>
          times := times.push (t1 - t0)
          if result matches .ok _ then oks := oks + 1
          IO.println (describeCall k (t1 - t0) result)
        | .error e => IO.println s!"call {k} threw {e}"
        k := k + 1
      let t1 ← IO.monoNanosNow
      IO.println s!"round {round} of {concurrent} calls took ms={fmtMs (t1 - t0)}"
  if k > 1 then
    IO.println s!"{summary "calls" times} ok={oks}"
    if concurrent ≤ 1 then
      IO.println (summary "later calls" (times.extract 1 times.size))
  if !checks.isEmpty then
    IO.println (summary "idle checks of reused connections" checks)
  trigger.report
  let stats ← client.stats
  IO.println s!"pool idle={stats.idle} checked_out={stats.checkedOut} allocated={stats.allocated}"
  if (kv.lookup "shutdown").isSome then
    let result ← (client.request req).block
    IO.println s!"after shutdown: {describeCall k 0 result}"
    let stats ← client.stats
    IO.println s!"after shutdown: pool idle={stats.idle} checked_out={stats.checkedOut}"
  if getNat kv "close" 0 == 1 then
    client.close
    let stats ← client.stats
    IO.println s!"after close: pool idle={stats.idle} checked_out={stats.checkedOut}"
    let result ← (client.request req).block
    IO.println s!"after close: {describeCall k 0 result}"
  -- After the calls after a shutdown or a close, so that their steps are checked too.
  reportTraces kv traces
  -- Open descriptors right after the calls and, with `linger=MS`, again after waiting: sockets of
  -- abandoned connect attempts are released only when the kernel gives up on them.
  IO.println s!"fds_after_calls={← openFds}"
  let linger := getNat kv "linger" 0
  if linger > 0 then
    IO.sleep linger.toUInt32
    IO.println s!"fds_after_linger_{linger}ms={← openFds}"

/-- A field of `/proc/self/status`, in kB, or 0. -/
def procStatusKb (field : String) : IO Nat := do
  let text ← IO.FS.readFile "/proc/self/status"
  let line := (text.splitOn "\n").find? (·.startsWith s!"{field}:")
  return (line.bind fun l => ((l.drop (field.length + 1)).trimAscii.toString.splitOn " ").head?.bind
    String.toNat?).getD 0

/-- What the callback of one streamed call saw. -/
structure Streamed where
  status : Status
  read : Nat
  pulls : Nat
  maxPull : Nat
  info : Option CallInfo

/--
Reads `body` in pulls of `pull` bytes until its end or until `stop` bytes were read, counting the
bytes read in `count` too, so that they are known if a read raises.
-/
partial def pullLoop (body : BodyStream) (pull : Nat) (stop : Option Nat) (count : IO.Ref Nat)
    (read pulls maxPull : Nat) (onRead : BaseIO Unit := pure ()) : Async (Nat × Nat × Nat) := do
  if stop.any (read ≥ ·) then return (read, pulls, maxPull)
  match ← body.read pull with
  | none => return (read, pulls, maxPull)
  | some bytes =>
    count.set (read + bytes.size)
    onRead
    pullLoop body pull stop count (read + bytes.size) (pulls + 1) (max maxPull bytes.size) onRead

def runStream (args : List String) : IO Unit := do
  let (methodName, url, rest) ← match args with
    | m :: u :: rest => pure (m, u, rest)
    | _ => throw (.userError "usage: net-client stream <METHOD> <URL> [key=value ...]")
  let kv := parseKV rest
  let req ← requestOf methodName url kv
  let traces : Traces ← IO.mkRef {}
  let trigger ← triggerOf kv
  let client ← Client.new (withTraces (configOf kv) kv traces trigger.observe)
  trigger.setClient client
  let idle := getNat kv "idle" 0
  let hold := getNat kv "hold" 0
  let pull := getNat kv "pull" 65536
  let stop := kv.lookup "stop" >>= String.toNat?
  let throwIt := getNat kv "throw" 0 == 1
  let escape := getNat kv "escape" 0 == 1
  for i in [0:getNat kv "repeat" 1] do
    if i > 0 then IO.sleep (getNat kv "pause" 0).toUInt32
    let t0 ← if i == 0 then trigger.arm else IO.monoNanosNow
    if getNat kv "whole" 0 == 1 then
      let result ← (client.request req (tokenFor kv trigger i)).block
      IO.println (describeCall i ((← IO.monoNanosNow) - t0) result)
      continue
    let kept : IO.Ref (Option BodyStream) ← IO.mkRef none
    let count : IO.Ref Nat ← IO.mkRef 0
    let racer : IO.Ref (Option (AsyncTask (Nat × Nat × Nat))) ← IO.mkRef none
    let entered : IO.Ref (Option Nat) ← IO.mkRef none
    let result ← try
        pure (some (← (client.withResponse req (cancel := tokenFor kv trigger i) fun resp => do
          entered.set (some ((← IO.monoNanosNow) - t0))
          trigger.sleepAt .idle idle
          if let some ms := kv.lookup "race" >>= String.toNat? then
            racer.set (some (← start (pullLoop resp.body pull none (← IO.mkRef 0) 0 0 0)))
            Std.Async.sleep (.ofNat ms)
            return ({
              status := resp.line.status, read := 0, pulls := 0, maxPull := 0,
              info := resp.extensions.get CallInfo } : Streamed)
          let (read, pulls, maxPull) ← pullLoop resp.body pull stop count 0 0 0 (trigger.reach .read)
          let read ← if hold == 0 then pure read else do
            trigger.sleepAt .hold hold
            let more := ((← resp.body.read pull).map (·.size)).getD 0
            count.set (read + more)
            pure (read + more)
          if escape then kept.set (some resp.body)
          if throwIt then throw (IO.userError "thrown inside the callback")
          return ({
            status := resp.line.status, read, pulls, maxPull,
            info := resp.extensions.get CallInfo } : Streamed)).block))
      catch e =>
        IO.println s!"stream {i} threw {repr (toString e)} ms={fmtMs ((← IO.monoNanosNow) - t0)}"
        pure none
    let ns := (← IO.monoNanosNow) - t0
    match result with
    | some (.ok r) =>
      let infoText := match r.info with
        | some info => s!"conn={info.connection} reused={info.reused} hops={info.hops} " ++
            s!"retries={info.retries} uri={info.uri}"
        | none => "no CallInfo"
      IO.println s!"stream {i} ok status={r.status.toCode} read={r.read} pulls={r.pulls} max_pull={r.maxPull} ms={fmtMs ns} {infoText}"
    | some (.error err) =>
      IO.println s!"stream {describeCall i ns (.error err)} read_before={← count.get}"
    | none => pure ()
    if i == 0 then
      if let some ns ← entered.get then IO.println s!"callback entered at ms={fmtMs ns}"
    if let some task ← racer.get then
      let stats ← client.stats
      IO.println s!"when withResponse returned: pool checked_out={stats.checkedOut}"
      match ← IO.wait task with
      | .ok (read, _, _) => IO.println s!"the racing reader ended after {read} bytes"
      | .error e => IO.println s!"the racing reader raised {repr (toString e)}"
    if let some body ← kept.get then
      try
        let r ← (body.read pull).block
        IO.println s!"after the callback: read returned {(r.map (·.size))}"
      catch e => IO.println s!"after the callback: read raised {repr (toString e)}"
    let stats ← client.stats
    IO.println s!"after stream {i}: pool idle={stats.idle} checked_out={stats.checkedOut} allocated={stats.allocated}"
  trigger.report
  reportTraces kv traces
  IO.println s!"rss_peak_kb={← procStatusKb "VmHWM"} rss_kb={← procStatusKb "VmRSS"}"

/-- `n` bytes of the upload pattern from offset `o`: byte k of the body is k % 251. -/
def patternBytes (o n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for j in [0:n] do
    out := out.push ((o + j) % 251).toUInt8
  return out

/--
A producer of `size` bytes of the pattern in chunks of `chunk`, counting its pulls and the bytes it
gave in `pulls` and `produced`; it raises an error at pull `fail` and waits `delay` ms before each chunk.
-/
def producer (size chunk : Nat) (fail : Option Nat) (delay : Nat) (pulls produced : IO.Ref Nat)
    (trigger : Trigger) (stall : Option Nat) : Async (Option ByteArray) := do
  let k ← pulls.modifyGet fun k => (k, k + 1)
  if fail == some k then throw (IO.userError "the producer failed on purpose")
  trigger.sleepAt .pull delay stall
  let o ← produced.get
  if o ≥ size then return none
  let n := min (max 1 chunk) (size - o)
  produced.set (o + n)
  return some (patternBytes o n)

def runUpload (args : List String) : IO Unit := do
  let (methodName, url, rest) ← match args with
    | m :: u :: rest => pure (m, u, rest)
    | _ => throw (.userError "usage: net-client upload <METHOD> <URL> [key=value ...]")
  let kv := parseKV rest
  let req ← requestOf methodName url kv
  let traces : Traces ← IO.mkRef {}
  let trigger ← triggerOf kv
  let client ← Client.new (withTraces (configOf kv) kv traces trigger.observe)
  trigger.setClient client
  let size := getNat kv "size" 0
  let chunk := getNat kv "chunk" 16384
  let declared : Option Nat := match kv.lookup "declare" with
    | some "none" => none
    | some v => v.toNat?
    | none => some size
  let fail := kv.lookup "fail" >>= String.toNat?
  let delay := getNat kv "delay" 0
  let stall := kv.lookup "stall" >>= String.toNat?
  for i in [0:getNat kv "repeat" 1] do
    if i > 0 then IO.sleep (getNat kv "pause" 0).toUInt32
    let pulls ← IO.mkRef 0
    let produced ← IO.mkRef 0
    let t0 ← if i == 0 then trigger.arm else IO.monoNanosNow
    let result ← if getNat kv "bytes" 0 == 1 then
        (client.request { req with body := patternBytes 0 size } (tokenFor kv trigger i)).block
      else
        let body := RequestBody.stream declared (producer size chunk fail delay pulls produced trigger stall)
        (client.upload { req with body } (tokenFor kv trigger i)).block
    let ns := (← IO.monoNanosNow) - t0
    let response := match result with
      | .ok resp => s!" response={repr ((String.fromUTF8? resp.body).getD "<binary>")}"
      | .error _ => ""
    IO.println s!"upload {describeCall i ns result} pulls={← pulls.get} produced={← produced.get}{response}"
    let stats ← client.stats
    IO.println s!"after upload {i}: pool idle={stats.idle} checked_out={stats.checkedOut} allocated={stats.allocated}"
  trigger.report
  reportTraces kv traces
  IO.println s!"rss_peak_kb={← procStatusKb "VmHWM"} rss_kb={← procStatusKb "VmRSS"}"

/--
Measures the idle check on `n` fresh connections to `tests/net/idle.py`: each sends `ping`, reads
`pong`, waits `wait` ms (the server acts 50 ms after `pong`: sends bytes, closes, resets, or does
nothing), then runs `Client.idleClean` with a window of `ms`.  Prints how many connections the check
found clean and the distribution of the check's duration.
-/
def idleCheck (port : UInt16) (kv : List (String × String)) : IO Unit := do
  let n := getNat kv "n" 200
  let ms := getNat kv "ms" 5
  let wait := getNat kv "wait" 100
  let scenario := (kv.lookup "scenario").getD "fin"
  let addr : SocketAddress := .v4 { addr := .ofParts 127 0 0 1, port }
  let mut clean := 0
  let mut times := #[]
  for _ in [0:n] do
    let s ← TCP.Socket.Client.mk
    (do s.connect addr; s.send s!"{scenario}\n".toUTF8; discard <| s.recv? 16 : Async Unit).block
    IO.sleep wait.toUInt32
    let t0 ← IO.monoNanosNow
    let ok ← (Client.idleClean s ms).block
    let t1 ← IO.monoNanosNow
    times := times.push (t1 - t0)
    if ok then clean := clean + 1
  IO.println s!"idlecheck scenario={scenario} ms={ms} n={n} clean={clean} detected={n - clean}"
  IO.println (summary s!"idlecheck scenario={scenario} ms={ms}" times)

/-- The value of a `Content-Length` field in a response head, or 0. -/
def contentLength (head : String) : Nat :=
  let len := (head.splitOn "\r\n").findSome? fun line =>
    match line.splitOn ":" with
    | [k, v] =>
      if k.trimAscii.toString.toLower == "content-length" then v.trimAscii.toString.toNat? else none
    | _ => none
  len.getD 0

/-- Reads one response with a `Content-Length` from `socket`, given what is already buffered. -/
partial def readOne (socket : TCP.Socket.Client) (buf : ByteArray) : Async Unit := do
  let text := String.fromUTF8? buf |>.getD ""
  match text.splitOn "\r\n\r\n" with
  | head :: rest :: _ =>
    if rest.utf8ByteSize ≥ contentLength head then
      return
  | _ => pure ()
  match ← socket.recv? 65536 with
  | some more => readOne socket (buf ++ more)
  | none => throw (.userError "eof in the response")

def rawPost (port : UInt16) (kv : List (String × String)) : IO Unit := do
  let n := getNat kv "n" 200
  let size := getNat kv "size" 100
  let keepAlive := getNat kv "keepalive" 1 == 1
  let noDelay := getNat kv "nodelay" 0 == 1
  let body := ByteArray.mk (Array.replicate size 'x'.toUInt8)
  let head := s!"POST / HTTP/1.1\r\nHost: 127.0.0.1\r\nContent-Length: {size}\r\n\r\n".toUTF8
  let addr : SocketAddress := .v4 { addr := .ofParts 127 0 0 1, port }
  let connect : Async TCP.Socket.Client := do
    let s ← TCP.Socket.Client.mk
    s.connect addr
    if noDelay then s.noDelay
    return s
  let mut times := #[]
  let mut shared : Option TCP.Socket.Client := none
  for _ in [0:n] do
    let t0 ← IO.monoNanosNow
    let s ← match shared with
      | some s => pure s
      | none => connect.block
    if keepAlive then shared := some s
    (do s.send head; s.send body; readOne s .empty : Async Unit).block
    let t1 ← IO.monoNanosNow
    times := times.push (t1 - t0)
  IO.println (summary s!"rawpost keepalive={keepAlive} nodelay={noDelay} split=1 size={size}" times)

def main (args : List String) : IO UInt32 := do
  let start ← IO.monoNanosNow
  match args with
  | "call" :: rest => runCalls rest
  | "stream" :: rest => runStream rest
  | "upload" :: rest => runUpload rest
  | "rawpost" :: port :: rest => rawPost port.toNat!.toUInt16 (parseKV rest)
  | "idlecheck" :: port :: rest => idleCheck port.toNat!.toUInt16 (parseKV rest)
  | "backoff" :: seed :: rest =>
    let kv := parseKV rest
    let d : Config := {}
    let s := Backoff.schedule (getNat kv "base" d.backoffBaseMs) (getNat kv "cap" d.backoffCapMs)
      seed.toNat!.toUInt64 (getNat kv "n" d.maxRetriesPerHop)
    IO.println s!"backoff seed={seed} schedule={s}"
  | _ =>
    IO.eprintln "usage: net-client call|stream|upload|rawpost|idlecheck|backoff ..."
    return 2
  let now ← IO.monoNanosNow
  IO.println s!"main returning at ms={fmtMs (now - start)}"
  return 0
