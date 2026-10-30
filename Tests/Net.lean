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
net-client stream <METHOD> <URL> [key=value ...]
  Calls `Client.withResponse` and reads the body in pulls; the options of `call`, and
  pull=N          bytes asked for in each read (default 65536)
  stop=N          leave the callback once N bytes were read (default: read to the end)
  throw=1         raise an exception inside the callback, after reading
  escape=1        keep the stream, and read from it after the callback ended
  race=MS         start a task that reads the stream, and leave the callback MS ms later while
                  that read is in progress
  whole=1         a control: `Client.request`, which reads the whole body into memory
  Prints the peak resident memory of the process at the end.
net-client upload <METHOD> <URL> [key=value ...]
  Calls `Client.upload` with a streamed body that a producer makes as it is pulled: byte k of the
  body is k % 251.  The options of `call` (repeat, deadline, gap, retries, ...), and
  size=N          bytes the producer gives in all (default 0)
  chunk=N         bytes per chunk (default 16384)
  declare=N|none  the size declared (default: size); none sends the body chunked
  fail=K          the producer raises an error at pull K, counting from 0
  delay=MS        the producer waits MS before each chunk
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
def withTraces (config : Config) (kv : List (String × String)) (traces : Traces) : Config :=
  if getNat kv "trace" 1 == 0 then config
  else { config with observe := some fun n e => traces.modify fun m => m.insert n ((m.getD n #[]).push e) }

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
  let config := withTraces (configOf kv) kv traces
  let client ← Client.new config
  let n := getNat kv "repeat" 1
  let pause := getNat kv "pause" 0
  let concurrent := getNat kv "concurrent" 1
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
  reportTraces kv traces
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
    (read pulls maxPull : Nat) : Async (Nat × Nat × Nat) := do
  if stop.any (read ≥ ·) then return (read, pulls, maxPull)
  match ← body.read pull with
  | none => return (read, pulls, maxPull)
  | some bytes =>
    count.set (read + bytes.size)
    pullLoop body pull stop count (read + bytes.size) (pulls + 1) (max maxPull bytes.size)

def runStream (args : List String) : IO Unit := do
  let (methodName, url, rest) ← match args with
    | m :: u :: rest => pure (m, u, rest)
    | _ => throw (.userError "usage: net-client stream <METHOD> <URL> [key=value ...]")
  let kv := parseKV rest
  let req ← requestOf methodName url kv
  let traces : Traces ← IO.mkRef {}
  let client ← Client.new (withTraces (configOf kv) kv traces)
  let pull := getNat kv "pull" 65536
  let stop := kv.lookup "stop" >>= String.toNat?
  let throwIt := getNat kv "throw" 0 == 1
  let escape := getNat kv "escape" 0 == 1
  for i in [0:getNat kv "repeat" 1] do
    if i > 0 then IO.sleep (getNat kv "pause" 0).toUInt32
    let t0 ← IO.monoNanosNow
    if getNat kv "whole" 0 == 1 then
      let result ← (client.request req).block
      IO.println (describeCall i ((← IO.monoNanosNow) - t0) result)
      continue
    let kept : IO.Ref (Option BodyStream) ← IO.mkRef none
    let count : IO.Ref Nat ← IO.mkRef 0
    let racer : IO.Ref (Option (AsyncTask (Nat × Nat × Nat))) ← IO.mkRef none
    let result ← try
        pure (some (← (client.withResponse req fun resp => do
          if let some ms := kv.lookup "race" >>= String.toNat? then
            racer.set (some (← start (pullLoop resp.body pull none (← IO.mkRef 0) 0 0 0)))
            Std.Async.sleep (.ofNat ms)
            return ({
              status := resp.line.status, read := 0, pulls := 0, maxPull := 0,
              info := resp.extensions.get CallInfo } : Streamed)
          let (read, pulls, maxPull) ← pullLoop resp.body pull stop count 0 0 0
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
gave in `pulls` and `given`; it raises an error at pull `fail` and waits `delay` ms before each chunk.
-/
def producer (size chunk : Nat) (fail : Option Nat) (delay : Nat) (pulls given : IO.Ref Nat) :
    Async (Option ByteArray) := do
  let k ← pulls.modifyGet fun k => (k, k + 1)
  if fail == some k then throw (IO.userError "the producer failed on purpose")
  if delay > 0 then Std.Async.sleep (.ofNat delay)
  let o ← given.get
  if o ≥ size then return none
  let n := min (max 1 chunk) (size - o)
  given.set (o + n)
  return some (patternBytes o n)

def runUpload (args : List String) : IO Unit := do
  let (methodName, url, rest) ← match args with
    | m :: u :: rest => pure (m, u, rest)
    | _ => throw (.userError "usage: net-client upload <METHOD> <URL> [key=value ...]")
  let kv := parseKV rest
  let req ← requestOf methodName url kv
  let traces : Traces ← IO.mkRef {}
  let client ← Client.new (withTraces (configOf kv) kv traces)
  let size := getNat kv "size" 0
  let chunk := getNat kv "chunk" 16384
  let declared : Option Nat := match kv.lookup "declare" with
    | some "none" => none
    | some v => v.toNat?
    | none => some size
  let fail := kv.lookup "fail" >>= String.toNat?
  let delay := getNat kv "delay" 0
  for i in [0:getNat kv "repeat" 1] do
    if i > 0 then IO.sleep (getNat kv "pause" 0).toUInt32
    let pulls ← IO.mkRef 0
    let given ← IO.mkRef 0
    let t0 ← IO.monoNanosNow
    let result ← if getNat kv "bytes" 0 == 1 then
        (client.request { req with body := patternBytes 0 size }).block
      else
        let body := RequestBody.stream declared (producer size chunk fail delay pulls given)
        (client.upload { req with body }).block
    let ns := (← IO.monoNanosNow) - t0
    let response := match result with
      | .ok resp => s!" response={repr ((String.fromUTF8? resp.body).getD "<binary>")}"
      | .error _ => ""
    IO.println s!"upload {describeCall i ns result} pulls={← pulls.get} produced={← given.get}{response}"
    let stats ← client.stats
    IO.println s!"after upload {i}: pool idle={stats.idle} checked_out={stats.checkedOut} allocated={stats.allocated}"
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
