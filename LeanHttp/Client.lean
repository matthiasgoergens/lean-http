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
the whole response into memory.  The calling task does all the work in order: name resolution,
connecting, writing the request, reading the response.  Other tasks exist only where a timer races
an operation, and none outlives the call except an abandoned connect attempt (see
`LeanHttp.Connect`).

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
Reads the response into `ex` until it is complete or fails.  Returns the exchange and, if reading
stopped for a reason the exchange does not record (a timeout, a transport error), that reason with
a detail.
-/
private partial def readResponse (config : Config) (socket : TCP.Socket.Client) (ex : Exchange)
    (deadline : Nat) : Async (Exchange × Option (Cause × String)) := do
  if ex.finished then
    return (ex, none)
  let left ← remainingMs deadline
  if left == 0 then
    return (ex, some (.timeout .deadline, ""))
  let receiving : AsyncTask (Option ByteArray) ← async (socket.recv? config.readChunkBytes.toUInt64)
  match ← awaitWithin receiving (min config.readGapMs left) with
  | none =>
    cancelReceive socket
    let which := if config.readGapMs < left then TimeoutKind.read else .deadline
    return (ex, some (.timeout which, ""))
  | some (.error err) => return (ex, some (.peerClosed, toString err))
  | some (.ok none) => readResponse config socket ex.endOfInput deadline
  | some (.ok (some data)) => readResponse config socket (ex.feed data) deadline

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
      (status : Option Status := none) (detail : String := "") : Except Error (Response ByteArray) :=
    .error { cause, delivery, target, seed, connectRounds := rounds, status, detail }
  let plan ← match plan req.line with
    | .ok plan => pure plan
    | .error msg => return fail (.invalidRequest msg) .notSent
  let target := s!"{plan.host}:{plan.port}"
  let (ex, bytes) :=
    Exchange.start config.h1 config.maxInterimResponses config.maxBodyBytes plan.head req.body
  if let .failed cause := ex.outcome then
    return fail cause .notSent target
  let connected ← match ← Connect.run config (.ofHost plan.host) plan.port seed deadline with
    | .ok connected => pure connected
    | .error (.resolve host detail) => return fail (.resolve host detail) .notSent target
    | .error (.exhausted attempts rounds) => return fail (.connect attempts) .notSent target rounds
    | .error (.deadline attempts rounds) =>
      return fail (.timeout .deadline) .notSent target rounds (detail := (Cause.connect attempts).describe)
  let socket := connected.socket
  let rounds := connected.rounds
  let left ← remainingMs deadline
  if left == 0 then
    return fail (.timeout .deadline) .notSent target rounds
  let writing : AsyncTask Unit ← async (socket.send bytes)
  match ← awaitWithin writing (min config.readGapMs left) with
  | none =>
    let which := if config.readGapMs < left then TimeoutKind.write else .deadline
    return fail (.timeout which) .maybeDelivered target rounds
  | some (.error err) => return fail .peerClosed .maybeDelivered target rounds (detail := toString err)
  | some (.ok ()) => pure ()
  let (ex, stopped) ← readResponse config socket ex deadline
  let delivery := ex.delivery
  let status := ex.head.map (·.status)
  if let some (cause, detail) := stopped then
    return fail cause delivery target rounds status detail
  match ex.outcome with
  | .done head body =>
    let finished ← IO.monoMsNow
    let info : CallInfo := {
      seed, connectRounds := rounds, address := connected.address,
      failedAttempts := connected.attempts, elapsedMs := finished - started }
    return .ok { line := head, body, extensions := Extensions.empty.insert info }
  | .failed cause => return fail cause delivery target rounds status
  | .pending => return fail .peerClosed delivery target rounds status "the response ended early"

/--
Like `request`, but throws the error as an `IO.Error` (its message says how far the request got).
-/
def send (client : Client) (req : Request ByteArray) : Async (Response ByteArray) := do
  match ← client.request req with
  | .ok response => return response
  | .error err => throw err.toIOError

end Client

end LeanHttp
