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
  deadline=MS gap=MS connect=MS stagger=MS retries=N maxbody=N interim=N seed=N nodelay=0|1
  pool=0|1 idlecheck=MS|off maxidle=N idletimeout=MS maxactive=N
  linger=MS      after the calls, wait and count open descriptors again
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
    maxConnectRetries := getNat kv "retries" d.maxConnectRetries
    maxBodyBytes := getNat kv "maxbody" d.maxBodyBytes
    maxInterimResponses := getNat kv "interim" d.maxInterimResponses
    backoffSeed := (kv.lookup "seed" >>= String.toNat?).map (·.toUInt64)
    noDelay := getNat kv "nodelay" 1 == 1
    pool := getNat kv "pool" 1 == 1
    idleCheck := kv.lookup "idlecheck" != some "off"
    idleCheckMs := getNat kv "idlecheck" d.idleCheckMs
    maxIdlePerOrigin := getNat kv "maxidle" d.maxIdlePerOrigin
    idleTimeoutMs := getNat kv "idletimeout" d.idleTimeoutMs
    maxActivePerOrigin := kv.lookup "maxactive" >>= String.toNat? }

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

/-- One line describing call `i`'s result. -/
def describeCall (i : Nat) (ns : Nat) (result : Except Error (Response ByteArray)) : String :=
  match result with
  | .ok resp =>
    let infoText := match resp.extensions.get CallInfo with
      | some i =>
        s!"rounds={i.connectRounds} address={i.address} seed={i.seed} " ++
          s!"failed_attempts={attemptsText i.failedAttempts} conn={i.connection} reused={i.reused} " ++
          s!"discarded={i.discarded} check_us={i.idleCheckUs} redispatched={i.redispatched}"
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
      s!"status={err.status.map Status.toCode} cause={repr err.cause.describe} " ++
      s!"detail={repr err.detail}{attempts}"

def runCalls (args : List String) : IO Unit := do
  let (methodName, url, rest) ← match args with
    | m :: u :: rest => pure (m, u, rest)
    | _ => throw (.userError "usage: net-client call <METHOD> <URL> [key=value ...]")
  let some method := parseMethod methodName
    | throw (.userError s!"unknown method {methodName}")
  let some uri := URI.parse? url
    | throw (.userError s!"cannot parse {url}")
  let kv := parseKV rest
  let config := configOf kv
  let body := ByteArray.mk (Array.replicate (getNat kv "body" 0) 'x'.toUInt8)
  let client ← Client.new config
  let n := getNat kv "repeat" 1
  let pause := getNat kv "pause" 0
  let concurrent := getNat kv "concurrent" 1
  let req : Request ByteArray :=
    { line := { method, version := .v11, uri := .absoluteForm uri }, body }
  let mut times := #[]
  let mut checks := #[]
  let mut oks := 0
  let mut k := 0
  for round in [0:n] do
    if round > 0 && pause > 0 then IO.sleep pause.toUInt32
    if concurrent ≤ 1 then
      let t0 ← IO.monoNanosNow
      let result ← (client.request req).block
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
      let t0 ← IO.monoNanosNow
      let mut tasks := #[]
      for _ in [0:concurrent] do
        let task ← start do
          let r ← client.request req
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
  let stats ← client.stats
  IO.println s!"pool idle={stats.idle} checked_out={stats.checkedOut} allocated={stats.allocated}"
  if getNat kv "close" 0 == 1 then
    client.close
    let stats ← client.stats
    IO.println s!"after close: pool idle={stats.idle} checked_out={stats.checkedOut}"
    let result ← (client.request req).block
    IO.println s!"after close: {describeCall k 0 result}"
  -- Open descriptors right after the calls and, with `linger=MS`, again after waiting: sockets of
  -- abandoned connect attempts are released only when the kernel gives up on them.
  IO.println s!"fds_after_calls={← openFds}"
  let linger := getNat kv "linger" 0
  if linger > 0 then
    IO.sleep linger.toUInt32
    IO.println s!"fds_after_linger_{linger}ms={← openFds}"

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
  | "rawpost" :: port :: rest => rawPost port.toNat!.toUInt16 (parseKV rest)
  | "idlecheck" :: port :: rest => idleCheck port.toNat!.toUInt16 (parseKV rest)
  | "backoff" :: seed :: rest =>
    let kv := parseKV rest
    let d : Config := {}
    let s := Backoff.schedule (getNat kv "base" d.backoffBaseMs) (getNat kv "cap" d.backoffCapMs)
      seed.toNat!.toUInt64 (getNat kv "n" d.maxConnectRetries)
    IO.println s!"backoff seed={seed} schedule={s}"
  | _ =>
    IO.eprintln "usage: net-client call|rawpost|idlecheck|backoff ..."
    return 2
  let now ← IO.monoNanosNow
  IO.println s!"main returning at ms={fmtMs (now - start)}"
  return 0
