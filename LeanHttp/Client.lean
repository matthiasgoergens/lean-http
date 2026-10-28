module

public import Std.Async.TCP
public import Std.Http.Data
public import LeanHttp.Config
public import LeanHttp.Connect
public import LeanHttp.Error
public import LeanHttp.Exchange
public import LeanHttp.Wait

public section

/-!
# The client

`Client.request` makes one HTTP/1.1 call on a connection of its own (`Connection: close`) and reads
the whole response into memory.  The calling task does all the work: name resolution, connecting,
and then driving the exchange core (`Exchange`), whose writes and reads it performs (at most one of
each in flight, so the response is read while a large request is still being written) and whose
deadlines it races against them.  Every decision about the exchange is the core's.

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
  How many rounds of connect attempts were made, counting the successful one.
  -/
  connectRounds : Nat

  /--
  The address the call connected to.
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
deriving TypeName

/--
An HTTP/1.1 client.  In this version it holds only its configuration: every call opens a connection
of its own and closes it at the end.
-/
structure Client where
  /--
  The limits and timeouts of every call.
  -/
  config : Config := {}

namespace Client

/--
A client with the given configuration.
-/
def new (config : Config := {}) : Client :=
  { config }

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
The exchange core's settings for one call of `config`: no reuse in this version.  Fails with
`invalidRequest` if `readGapMs` is zero, which would make every write and read due the moment it is
issued.
-/
def exchangeConfig (config : Config) : Except Cause ExchangeConfig :=
  if h : 0 < config.readGapMs then
    .ok {
      h1 := config.h1, keepAlive := false, maxInterim := config.maxInterimResponses,
      maxBody := config.maxBodyBytes, readChunk := config.readChunkBytes,
      writeChunk := config.writeChunkBytes, gapMs := config.readGapMs, gapMs_pos := h }
  else
    .error (.invalidRequest "readGapMs must be positive")

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
Joins body chunks given last first.  The result is allocated here, so appending to it is done in
place.
-/
private def joinChunks (chunks : List ByteArray) (size : Nat) : ByteArray :=
  chunks.reverse.foldl (init := ByteArray.emptyWithCapacity size) (· ++ ·)

/--
How an exchange ended, as the shell saw it.
-/
private inductive Ended where
  /--
  The response arrived in full.
  -/
  | response (head : Response.Head) (body : ByteArray)

  /--
  The exchange failed.
  -/
  | failure (failure : Failure)

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
    | .finish _ =>
      if driver.reading.isSome then cancelReceive socket
      return match driver.head with
        | some head => .response head (joinChunks driver.chunks driver.bodySize)
        | none => .failure { cause := .peerClosed, delivery := ex.delivery, written := ex.written }
    | .fail failure =>
      if driver.reading.isSome then cancelReceive socket
      return .failure failure
  let now ← IO.monoMsNow
  let wait := (ex.nextDeadline.getD now) - now
  let pending := driver.reading.toArray ++ driver.writing.toArray
  let (event, next) ← match ← awaitFirst pending wait with
    | none => pure (ExchangeEvent.tick, driver)
    | some (.read result) =>
      let event := match result with
        | .ok (some bytes) => ExchangeEvent.received bytes
        | .ok none => .endOfInput
        | .error err => .readFailed (toString err)
      pure (event, { driver with reading := none })
    | some (.wrote length result) =>
      let event := match result with
        | .ok () => ExchangeEvent.written length
        | .error err => .writeFailed (toString err)
      pure (event, { driver with writing := none })
  let (ex, actions) := ex.step (← IO.monoMsNow) event
  drive socket ex actions next

/--
Sends `req` and reads the whole response.  The request's target must be an absolute `http` URI;
its body is sent with a `Content-Length`, and `Connection: close` is added.

```
let client := LeanHttp.Client.new { deadlineMs := 15 * 60 * 1000, readGapMs := 15 * 60 * 1000 }
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
  let fail (cause : Cause) (delivery : Delivery) (target : String := "") (rounds : Nat := 0)
      (status : Option Status := none) (detail : String := "") (written : Nat := 0) :
      Except Error (Response ByteArray) :=
    .error { cause, delivery, written, target, seed, connectRounds := rounds, status, detail }
  let plan ← match plan req.line with
    | .ok plan => pure plan
    | .error msg => return fail (.invalidRequest msg) .notSent
  let target := s!"{plan.host}:{plan.port}"
  let prepared ← match exchangeConfig config >>= (Exchange.prepare · plan.head req.body) with
    | .ok prepared => pure prepared
    | .error cause => return fail cause .notSent target
  let connected ← match ← Connect.run config (.ofHost plan.host) plan.port seed deadline with
    | .ok connected => pure connected
    | .error (.resolve host detail) => return fail (.resolve host detail) .notSent target
    | .error (.exhausted attempts rounds) => return fail (.connect attempts) .notSent target rounds
    | .error (.deadline attempts rounds) =>
      return fail (.timeout .deadline) .notSent target rounds (detail := (Cause.connect attempts).describe)
  let rounds := connected.rounds
  let now ← IO.monoMsNow
  let (ex, actions) := Exchange.begin prepared now deadline
  -- The whole body is wanted, up to the limit, which the core enforces.
  let (ex, more) := ex.step now (.wantBody (config.maxBodyBytes + 1))
  match ← drive connected.socket ex (actions ++ more) {} with
  | .response head body =>
    let finished ← IO.monoMsNow
    let info : CallInfo := {
      seed, connectRounds := rounds, address := connected.address,
      failedAttempts := connected.attempts, elapsedMs := finished - started }
    return .ok { line := head, body, extensions := Extensions.empty.insert info }
  | .failure f => return fail f.cause f.delivery target rounds f.status f.detail f.written

/--
Like `request`, but throws the error as an `IO.Error` (its message says how far the request got).
-/
def send (client : Client) (req : Request ByteArray) : Async (Response ByteArray) := do
  match ← client.request req with
  | .ok response => return response
  | .error err => throw err.toIOError

end Client

end LeanHttp
