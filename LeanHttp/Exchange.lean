module

public import LeanHttpProto.Http.Protocol.H1
public import LeanHttp.Error

public section

/-!
# The exchange core

One request and its response on one connection, as pure functions over the HTTP/1.1 machine of the
upstream client stack (`LeanHttpProto.Http.Protocol.H1.Machine`, a renamed copy of
`Std.Http.Protocol.H1.Machine` with the stack's changes, in the client direction).  The shell writes the bytes that
`Exchange.start` returns, feeds every read to `Exchange.feed`, reports end of input with
`Exchange.endOfInput`, and stops when `Exchange.outcome` is no longer `pending`.  No I/O happens
here, so every response shape can be tested by feeding bytes, split at any point.

The machine is used with keep-alive off: the request carries `Connection: close` and the connection
ends with the exchange.  On top of the machine the core counts interim (1xx) responses against a
limit, refuses `101 Switching Protocols` (the client never asks for an upgrade), accumulates the
body, and turns the machine's errors into a `Cause`.
-/

namespace LeanHttp

set_option linter.all true

open Std.Http LeanHttpProto.Http.Protocol

/--
Where an exchange stands.
-/
inductive Exchange.Outcome where
  /--
  The response is not complete yet.
  -/
  | pending

  /--
  The final response arrived in full.
  -/
  | done (head : Response.Head) (body : ByteArray)

  /--
  The exchange failed.
  -/
  | failed (cause : Cause)
deriving Inhabited

/--
The state of one exchange.
-/
structure Exchange where
  /--
  The HTTP/1.1 machine, in the client direction.
  -/
  machine : H1.Machine .sending

  /--
  Most interim responses accepted before the final one.
  -/
  maxInterim : Nat

  /--
  Largest body accepted, in decoded bytes.
  -/
  maxBody : Nat

  /--
  Interim responses seen so far.
  -/
  interim : Nat := 0

  /--
  The head of the final response, once it has been parsed.
  -/
  head : Option Response.Head := none

  /--
  The body bytes received so far.
  -/
  body : ByteArray := .empty

  /--
  Whether the body of the final response is complete.
  -/
  bodyDone : Bool := false

  /--
  Why the exchange failed, if it did.
  -/
  failure : Option Cause := none

  /--
  Whether end of input has been reported.
  -/
  inputEnded : Bool := false

namespace Exchange

/--
Maps an error of the HTTP/1.1 machine to a cause.
-/
def causeOfH1Error : H1.Error → Cause
  | .entityTooLarge => .limit .body
  | .tooManyHeaders | .headersTooLarge => .limit .headers
  | .connectionClosed => .peerClosed
  | err => .protocol (toString err)

/--
Where the exchange stands.
-/
def outcome (ex : Exchange) : Outcome :=
  match ex.failure, ex.head with
  | some cause, _ => .failed cause
  | none, some head => if ex.bodyDone then .done head ex.body else .pending
  | none, none => .pending

/--
How far the request got, for an exchange whose request was written: the response was received if
its final head was parsed, and otherwise the request may or may not have been acted on.
-/
def delivery (ex : Exchange) : Delivery :=
  if ex.head.isSome then .responseReceived else .maybeDelivered

/--
`true` once the exchange has a final outcome.
-/
def finished (ex : Exchange) : Bool :=
  ex.failure.isSome || (ex.head.isSome && ex.bodyDone)

/--
Records the first failure; later ones are ignored.
-/
private def fail (ex : Exchange) (cause : Cause) : Exchange :=
  if ex.failure.isSome then ex else { ex with failure := some cause }

/--
Handles one event of the machine.  Returns whether it changed anything the driver loop must act on.
-/
private def handleEvent (ex : Exchange) : H1.Event .sending → Exchange × Bool
  | .endHeaders head =>
    let head : Response.Head := head
    if head.status.isInformational then
      if head.status.toCode == 101 then
        (ex.fail (.protocol "101 Switching Protocols, but no upgrade was requested"), true)
      else
        let ex := { ex with interim := ex.interim + 1 }
        if ex.interim > ex.maxInterim then (ex.fail (.limit .interim), true) else (ex, true)
    else
      ({ ex with head := some head }, true)
  | .closeBody =>
    -- The machine also closes the (empty) body of each interim response; only the final
    -- response's counts.
    if ex.head.isSome then ({ ex with bodyDone := true }, true) else (ex, true)
  | .failed err => (ex.fail (causeOfH1Error err), true)
  | .needMoreData _ | .close | .needAnswer | .next | .continue => (ex, false)

/--
Handles a batch of events in order.
-/
private def handleEvents (ex : Exchange) (events : Array (H1.Event .sending)) : Exchange × Bool :=
  events.foldl (init := (ex, false)) fun (ex, progressed) event =>
    let (ex, p) := ex.handleEvent event
    (ex, progressed || p)

/--
`true` when the body the machine is about to read is known to exceed the limit: a `Content-Length`
larger than what the limit leaves.
-/
private def announcedTooLarge (ex : Exchange) : Bool :=
  match ex.machine.reader.state with
  | .readBody (.fixed remaining) => ex.body.size + remaining > ex.maxBody
  | _ => false

/--
Pulls every body chunk the machine can produce now, enforcing the body limit.
-/
private partial def pullAll (ex : Exchange) (progressed : Bool) : Exchange × Bool :=
  if ex.finished || !ex.machine.canPullBodyNow then
    (ex, progressed)
  else if ex.announcedTooLarge then
    (ex.fail (.limit .body), true)
  else
    let (machine, chunk?) := ex.machine.pullBody
    let ex := { ex with machine }
    match chunk? with
    | some pulled =>
      if ex.body.size + pulled.chunk.data.size > ex.maxBody then
        (ex.fail (.limit .body), true)
      else
        let ex := { ex with body := ex.body ++ pulled.chunk.data }
        let ex := if pulled.final && ex.head.isSome then { ex with bodyDone := true } else ex
        pullAll ex true
    | none => (ex, progressed)

/--
Runs the machine until it can make no more progress without new input.
-/
private partial def drive (ex : Exchange) : Exchange :=
  if ex.finished then
    ex
  else
    let (machine, result) := ex.machine.step
    let (ex, p₁) := { ex with machine }.handleEvents result.events
    let (ex, p₂) := ex.pullAll false
    let (machine, events) := ex.machine.takeEvents
    let (ex, p₃) := { ex with machine }.handleEvents events
    if p₁ || p₂ || p₃ then
      drive ex
    else if ex.inputEnded && !ex.finished then
      -- Input ended and the machine is idle: whatever is missing will never come.
      if ex.machine.failed then
        ex.fail (.protocol (ex.machine.error.map toString |>.getD "failed"))
      else
        ex.fail .peerClosed
    else
      ex

/--
Starts an exchange.  `head` must already carry its `Host` field; framing fields are replaced by a
`Content-Length` for `body`, and `Connection: close` is added.  Returns the exchange and the bytes
of the request, to be written in one go.

`h1` supplies the parser limits; keep-alive is turned off.  The body limit, `maxBodyBytes` decoded
bytes, is enforced here rather than by the machine, which would refuse an oversized
`Content-Length` before reporting the head: a caller is better served by an error that carries the
status and says the response was received.  The machine still bounds the input it buffers by
`maxBodyBytes` plus its header allowances.
-/
def start (h1 : H1.Config) (maxInterim maxBodyBytes : Nat) (head : Request.Head)
    (body : ByteArray) : Exchange × ByteArray :=
  -- The machine's own limits are lifted out of the way of the exchange's (`pullAll`).
  let unlimited := 2 ^ 62
  let config := { h1 with
    enableKeepAlive := false
    maxBodySize := unlimited
    maxChunkSize := unlimited
    maxBufferedBodyBytes := some maxBodyBytes }
  let headers := head.headers
    |>.erase Header.Name.contentLength
    |>.erase Header.Name.transferEncoding
  let head := { head with headers }
  let machine : H1.Machine .sending := { config }
  let machine := machine.setKnownSize (.fixed body.size)
  let machine := machine.send head
  let machine := if body.isEmpty then machine else machine.sendData #[{ data := body }]
  let machine := machine.userClosedBody
  let (machine, result) := machine.step
  let ex : Exchange := { machine, maxInterim, maxBody := maxBodyBytes }
  let (ex, _) := ex.handleEvents result.events
  let ex :=
    if ex.machine.failed || ex.machine.error.isSome then
      ex.fail (.invalidRequest "the HTTP/1.1 machine refused the request head")
    else
      ex
  (ex, result.output.toByteArray)

/--
Feeds bytes read from the connection.
-/
def feed (ex : Exchange) (data : ByteArray) : Exchange :=
  if ex.finished then ex else drive { ex with machine := ex.machine.feed data }

/--
Reports that the peer closed its side of the connection.
-/
def endOfInput (ex : Exchange) : Exchange :=
  if ex.finished then ex else drive { ex with machine := ex.machine.noMoreInput, inputEnded := true }

end Exchange

end LeanHttp
