module

public import LeanHttpProto.Http.Protocol.H1
public import LeanHttp.Error

public section

/-!
# The exchange core

One request and its response on one connection, as a pure step function over the HTTP/1.1 machine
of the upstream client stack (`LeanHttpProto.Http.Protocol.H1.Machine`, a renamed copy of
`Std.Http.Protocol.H1.Machine` with the stack's changes, in the client direction).

`Exchange.prepare` encodes the request (and refuses one the machine will not write) before any I/O.
`Exchange.begin` starts the exchange on an open connection and returns the first actions; from then
on the shell reports everything that happens as an `ExchangeEvent` to `Exchange.step`, performs the
`ExchangeAction`s it returns, and sleeps no later than `Exchange.nextDeadline`.  Time is an
argument of `step`, deadlines are state, and nothing here performs I/O, so every interleaving of
events can be replayed and checked.

What the core guarantees, by construction:

- **No response without a request.**  Bytes are handed to the machine only once the whole request
  head has been written: the core asks for no read before that, and bytes reported earlier anyway
  fail the exchange unparsed.  Bytes a server sent before it saw the request (on a reused
  connection, a 408 before closing) wait in the socket and are read as the response; catching
  those is the job of the idle check before a pooled connection is reused.
- **One write in flight.**  The request goes out in slices of `ExchangeConfig.writeChunk` bytes, the
  next one only after the previous one completed.
- **Reuse only when it is safe.**  The verdict of `finish` is `true` only when the response's
  framing was certain (not delimited by the end of input), the response was read to its end with no
  byte left over, the request was written in full before the response head arrived, the peer did
  not close, and both sides agreed to keep the connection alive.
- **Early responses are delivered.**  The response is read while the request body is still being
  written, so a server that answers early (a 413, say) and stops reading is heard, and a write that
  fails once the request head is out only stops the upload; the connection is not reused
  afterwards.
- **Errors say how far the request got** (`Failure.delivery`, `Failure.written`).

On top of the machine the core counts interim (1xx) responses against a limit, refuses
`101 Switching Protocols` (the client never asks for an upgrade), enforces the body limit, and turns
the machine's errors into a `Cause`.
-/

namespace LeanHttp

set_option linter.all true

open Std.Http LeanHttpProto.Http.Protocol

/--
A point in time, in milliseconds of a monotonic clock (`IO.monoMsNow` in the shell).
-/
abbrev Timestamp := Nat

/--
The limits and timeouts of one exchange.
-/
structure ExchangeConfig where
  /--
  Parser limits for the response head and framing.  The core sets `enableKeepAlive`, `maxBodySize`,
  `maxChunkSize` and `maxBufferedBodyBytes` itself.
  -/
  h1 : H1.Config := {}

  /--
  Whether the connection may be reused after the exchange.  When `false`, the request carries
  `Connection: close` and `finish` always reports the connection as not reusable.
  -/
  keepAlive : Bool := false

  /--
  Most interim responses accepted before the final one.
  -/
  maxInterim : Nat := 10

  /--
  Largest body accepted, in decoded bytes.
  -/
  maxBody : Nat := 64 * 1024 * 1024

  /--
  Bytes asked for in each read.
  -/
  readChunk : Nat := 64 * 1024

  /--
  Largest slice of the request handed to the connection in one write.
  -/
  writeChunk : Nat := 64 * 1024

  /--
  Longest time without progress: for one write to complete, and, once the request has been written,
  for one read to return.
  -/
  gapMs : Nat := 30 * 1000

  /--
  When the caller abandons a body, how many more decoded body bytes may be read and discarded to
  keep the connection reusable.
  -/
  drainBytes : Nat := 64 * 1024

  /--
  When the caller abandons a body, how long the rest may take to arrive and keep the connection
  reusable.
  -/
  drainMs : Nat := 100

/--
How the end of a response body is marked.
-/
inductive Framing where
  /--
  The response has no body: it answers a HEAD request, or its status is 1xx, 204 or 304.
  -/
  | none

  /--
  The body has a `Content-Length`.
  -/
  | length (bytes : Nat)

  /--
  The body is chunked.
  -/
  | chunked

  /--
  The body ends when the peer closes the connection.
  -/
  | untilClose
deriving Repr, BEq, DecidableEq, Inhabited

namespace Framing

/--
`true` when the end of the body is known without the peer closing the connection.
-/
def certain : Framing → Bool
  | .untilClose => false
  | _ => true

/--
The framing of a response to a request with `method`, as RFC 9112 section 6.3 defines it.  A head
with conflicting or malformed framing fields, which the machine refuses, counts as `untilClose`.
-/
def ofResponse (method : Method) (head : Response.Head) : Framing :=
  let code := head.status.toCode.toNat
  if method == .head || (100 ≤ code && code < 200) || code == 204 || code == 304 then
    .none
  else
    match H1.Message.Head.getSize (dir := .sending) head false with
    | some (.fixed n) => .length n
    | some .chunked => .chunked
    | Option.none => .untilClose

end Framing

/--
Why an exchange failed, and how far its request got.
-/
structure Failure where
  /--
  What went wrong.
  -/
  cause : Cause

  /--
  How far the request got: not sent if no write was ever issued, response received once the final
  response head was delivered, and maybe delivered in between.
  -/
  delivery : Delivery

  /--
  Request bytes whose write completed.
  -/
  written : Nat

  /--
  The status of the final response, when its head was delivered.
  -/
  status : Option Status := none

  /--
  A human-readable detail, such as the operating system's error message.
  -/
  detail : String := ""
deriving Repr, Inhabited

/--
What the shell reports to the core.
-/
inductive ExchangeEvent where
  /--
  A read returned these bytes.
  -/
  | received (bytes : ByteArray)

  /--
  A read reported that the peer closed its side of the connection.
  -/
  | endOfInput

  /--
  The write in flight completed, and the connection accepted `count` of its bytes.
  -/
  | written (count : Nat)

  /--
  The caller wants up to `bytes` more bytes of the response body.
  -/
  | wantBody (bytes : Nat)

  /--
  Time passed.  A tick earlier than `Exchange.nextDeadline` changes nothing.
  -/
  | tick

  /--
  The caller gave up on the response (or, before its head arrived, on the whole exchange).
  -/
  | abandon

  /--
  The read in flight failed.
  -/
  | readFailed (detail : String)

  /--
  The write in flight failed.
  -/
  | writeFailed (detail : String)
deriving Inhabited

/--
What the core asks the shell to do, in order.
-/
inductive ExchangeAction where
  /--
  Write these bytes, and report `written` or `writeFailed`.  At most one write is in flight.
  -/
  | write (bytes : ByteArray)

  /--
  Read up to this many bytes, and report `received`, `endOfInput` or `readFailed`.  At most one read
  is in flight; when the core asks for none, it does not want input now.
  -/
  | read (max : Nat)

  /--
  Hand the final response head to the caller.
  -/
  | deliverHead (head : Response.Head)

  /--
  Hand these body bytes to the caller.
  -/
  | deliverBody (bytes : ByteArray)

  /--
  The exchange ended.  When `reusable`, the connection may serve another exchange; otherwise it must
  be shut down and dropped.  The core emits nothing more.
  -/
  | finish (reusable : Bool)

  /--
  The exchange failed, and its connection must be dropped.  The core emits nothing more.
  -/
  | fail (failure : Failure)
deriving Inhabited

/--
A request encoded for the wire, ready to be started on a connection.
-/
structure PreparedRequest where
  /--
  The limits and timeouts of the exchange.
  -/
  config : ExchangeConfig

  /--
  The HTTP/1.1 machine after encoding the request, in the client direction.
  -/
  machine : H1.Machine .sending

  /--
  The request method, which decides whether the response can have a body.
  -/
  method : Method

  /--
  The request as written: head, then body.
  -/
  bytes : ByteArray

  /--
  The length of the request head at the start of `bytes`.
  -/
  headBytes : Nat

instance : Inhabited PreparedRequest :=
  ⟨{ config := {}, machine := { config := {} }, method := .get, bytes := .empty, headBytes := 0 }⟩

/--
Where an exchange stands.
-/
inductive Exchange.Phase where
  /--
  The request head has not been written in full; no response can be due.
  -/
  | sending

  /--
  The request head has been written (its body may still be going out); waiting for the final
  response head.
  -/
  | awaitingHead

  /--
  The final response head was delivered; its body is being delivered.
  -/
  | receiving

  /--
  The caller abandoned the body; the rest is being read and discarded, within the drain limits, to
  keep the connection reusable.
  -/
  | draining

  /--
  The exchange ended, and the connection is reusable or not.
  -/
  | finished (reusable : Bool)

  /--
  The exchange failed.
  -/
  | failed (failure : Failure)
deriving Repr, Inhabited

/--
The state of one exchange.
-/
structure Exchange where
  /--
  The limits and timeouts.
  -/
  config : ExchangeConfig := {}

  /--
  The HTTP/1.1 machine, in the client direction.
  -/
  machine : H1.Machine .sending := { config := {} }

  /--
  The request method.
  -/
  method : Method := .get

  /--
  The request as written: head, then body.
  -/
  request : ByteArray := .empty

  /--
  The length of the request head at the start of `request`.
  -/
  headBytes : Nat := 0

  /--
  The deadline of the whole exchange.
  -/
  deadline : Timestamp := 0

  /--
  The latest time the core has been told about; it never goes backwards.
  -/
  now : Timestamp := 0

  /--
  Where the exchange stands.
  -/
  phase : Exchange.Phase := .sending

  /--
  Request bytes whose write completed.
  -/
  written : Nat := 0

  /--
  The length of the write in flight, if there is one.
  -/
  writeInFlight : Option Nat := none

  /--
  When the write in flight times out.
  -/
  writeBy : Option Timestamp := none

  /--
  Whether writing stopped before the end of the request, because the write failed or stalled after
  the final response head arrived.
  -/
  uploadStopped : Bool := false

  /--
  Whether any write was ever issued, i.e. whether the server can have seen any of the request.
  -/
  sentAny : Bool := false

  /--
  Why the upload stopped, if a write failed after the request head was out.
  -/
  writeError : Option String := none

  /--
  Whether a read is in flight.
  -/
  readInFlight : Bool := false

  /--
  When the read in flight times out.  Armed only once writing is over: a server is silent while it
  receives a request.
  -/
  readBy : Option Timestamp := none

  /--
  Whether the peer closed its side.
  -/
  inputEnded : Bool := false

  /--
  Interim responses seen so far.
  -/
  interim : Nat := 0

  /--
  The final response head, once delivered.
  -/
  head : Option Response.Head := none

  /--
  The framing of the final response, once its head arrived.
  -/
  framing : Framing := .none

  /--
  Whether the final response head arrived before the request was written in full.
  -/
  early : Bool := false

  /--
  Body bytes the caller has asked for and not yet received.
  -/
  credit : Nat := 0

  /--
  Body bytes delivered so far.
  -/
  bodyBytes : Nat := 0

  /--
  Whether the body of the final response ended.
  -/
  bodyDone : Bool := false

  /--
  Body bytes discarded since the caller abandoned the body.
  -/
  drained : Nat := 0

  /--
  When draining an abandoned body gives up.
  -/
  drainBy : Option Timestamp := none
deriving Inhabited

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
Encodes a request.  `head` must already carry its `Host` field; framing fields are replaced by a
`Content-Length` for `body` (none for a bodiless request whose method does not anticipate one), and
`Connection: close` is added unless `config.keepAlive`.  Fails with `invalidRequest` if the machine
refuses the head.

The body limit, `config.maxBody` decoded bytes, is enforced by the core rather than by the machine,
which would refuse an oversized `Content-Length` before reporting the head: a caller is better served
by an error that carries the status and says the response was received.  The machine still bounds
the input it buffers by `maxBody` plus its header allowances.
-/
def prepare (config : ExchangeConfig) (head : Request.Head) (body : ByteArray) :
    Except Cause PreparedRequest := do
  -- The machine's own limits are lifted out of the way of the core's (`pullAvailable`).
  let unlimited := 2 ^ 62
  let h1 := { config.h1 with
    enableKeepAlive := config.keepAlive
    maxBodySize := unlimited
    maxChunkSize := unlimited
    maxBufferedBodyBytes := some config.maxBody }
  let headers := head.headers
    |>.erase Header.Name.contentLength
    |>.erase Header.Name.transferEncoding
  let head := { head with headers }
  let machine : H1.Machine .sending := { config := h1 }
  let machine := machine.setKnownSize (.fixed body.size)
  let machine := machine.send head
  let machine := if body.isEmpty then machine else machine.sendData #[{ data := body }]
  let machine := machine.userClosedBody
  let (machine, result) := machine.step
  let refused := result.events.any fun | .failed _ => true | _ => false
  if refused || machine.failed || machine.error.isSome then
    throw (.invalidRequest "the HTTP/1.1 machine refused the request head")
  let bytes := result.output.toByteArray
  return { config, machine, method := head.method, bytes, headBytes := bytes.size - body.size }

/--
`true` once the exchange has finished or failed.
-/
def terminal (ex : Exchange) : Bool :=
  match ex.phase with
  | .finished _ | .failed _ => true
  | _ => false

/--
`true` when no more of the request will be written: all of it was, or writing stopped.
-/
def uploadOver (ex : Exchange) : Bool :=
  ex.uploadStopped || ex.written ≥ ex.request.size

/--
How far the request got, as a failure now would report it.
-/
def delivery (ex : Exchange) : Delivery :=
  if ex.head.isSome then .responseReceived
  else if ex.sentAny then .maybeDelivered
  else .notSent

/--
The earliest time at which the core must be ticked, or `none` once it has ended.
-/
def nextDeadline (ex : Exchange) : Option Timestamp :=
  if ex.terminal then
    none
  else
    let timers := [ex.writeBy, ex.readBy, ex.drainBy].filterMap id
    some (timers.foldl min ex.deadline)

/--
Whether the connection may be reused if the exchange ended now.
-/
def reusableNow (ex : Exchange) : Bool :=
  ex.config.keepAlive && ex.machine.keepAlive && ex.framing.certain && ex.bodyDone &&
    ex.written == ex.request.size && !ex.early && !ex.inputEnded && !ex.machine.hasBufferedInput

/--
Whether the core wants input now.
-/
def wantsInput (ex : Exchange) : Bool :=
  !ex.inputEnded &&
    match ex.phase with
    | .awaitingHead | .draining => true
    | .receiving => !ex.bodyDone && ex.credit > 0
    | _ => false

/--
The state of one step: the exchange and the actions emitted so far.
-/
abbrev StepM := StateM (Exchange × Array ExchangeAction)

private def getEx : StepM Exchange :=
  return (← get).1

private def setEx (ex : Exchange) : StepM Unit :=
  modify fun (_, actions) => (ex, actions)

private def modifyEx (f : Exchange → Exchange) : StepM Unit :=
  modify fun (ex, actions) => (f ex, actions)

private def emit (action : ExchangeAction) : StepM Unit :=
  modify fun (ex, actions) => (ex, actions.push action)

/--
Fails the exchange, unless it already ended.
-/
private def failNow (cause : Cause) (detail : String := "") : StepM Unit := do
  let ex ← getEx
  unless ex.terminal do
    -- A failed write that only stopped the upload explains a failure that has no detail of its own.
    let detail :=
      if detail.isEmpty then (ex.writeError.map (s!"a write failed earlier: {·}")).getD "" else detail
    let failure : Failure := {
      cause, delivery := ex.delivery, written := ex.written, status := ex.head.map (·.status),
      detail }
    setEx { ex with phase := .failed failure, writeBy := none, readBy := none, drainBy := none }
    emit (.fail failure)

/--
Finishes the exchange, unless it already ended.  The connection is reusable only if `reusable` and
`reusableNow` agree.
-/
private def finishNow (reusable : Bool) : StepM Unit := do
  let ex ← getEx
  unless ex.terminal do
    let reusable := reusable && ex.reusableNow
    setEx { ex with phase := .finished reusable, writeBy := none, readBy := none, drainBy := none }
    emit (.finish reusable)

/--
Ends the exchange on a failure: while draining an abandoned body nobody waits for an error, so the
exchange finishes with a connection that is not reusable.
-/
private def failOrDrop (cause : Cause) (detail : String := "") : StepM Unit := do
  match (← getEx).phase with
  | .draining => finishNow false
  | _ => failNow cause detail

/--
Stops writing the rest of the request, after the final response head arrived.  The response no
longer depends on the upload, so silence on the read side becomes what counts.
-/
private def stopUpload : StepM Unit :=
  modifyEx fun ex =>
    let readBy := if ex.readInFlight then some (ex.now + ex.config.gapMs) else none
    { ex with uploadStopped := true, writeBy := none, readBy }

/--
`true` when the body still to come is announced larger than what `limit` leaves, given `used`.
-/
private def announcedOver (ex : Exchange) (used limit : Nat) : Bool :=
  match ex.machine.reader.state with
  | .readBody (.fixed remaining) => used + remaining > limit
  | _ => false

/--
Handles one event of the machine.  Returns whether it changed anything the loop must act on.
-/
private def handleH1Event : H1.Event .sending → StepM Bool
  | .endHeaders head => do
    let head : Response.Head := head
    let ex ← getEx
    if ex.terminal then
      return false
    if head.status.isInformational then
      if head.status.toCode == 101 then
        failNow (.protocol "101 Switching Protocols, but no upgrade was requested")
      else
        let ex := { ex with interim := ex.interim + 1 }
        setEx ex
        if ex.interim > ex.config.maxInterim then failNow (.limit .interim)
      return true
    else if ex.head.isSome then
      failNow (.protocol "a second final response head")
      return true
    else
      let framing := Framing.ofResponse ex.method head
      setEx { ex with
        head := some head, framing, phase := .receiving, early := ex.written < ex.request.size }
      emit (.deliverHead head)
      if let .length n := framing then
        if n > ex.config.maxBody then failNow (.limit .body)
      return true
  | .closeBody => do
    -- The machine also closes the (empty) body of each interim response; only the final
    -- response's counts.
    let ex ← getEx
    if ex.head.isSome then setEx { ex with bodyDone := true }
    return true
  | .failed err => do
    failOrDrop (causeOfH1Error err)
    return true
  | .needMoreData _ | .close | .needAnswer | .next | .continue => return false

/--
Handles a batch of events of the machine in order.
-/
private def handleH1Events (events : Array (H1.Event .sending)) : StepM Bool :=
  events.foldlM (init := false) fun progressed event => do
    let p ← handleH1Event event
    return progressed || p

/--
Pulls the body chunks the machine can produce now: as many as the caller's credit allows while
receiving, and all of them, discarded, while draining.  Returns whether anything changed.
-/
private partial def pullAvailable (progressed : Bool) : StepM Bool := do
  let ex ← getEx
  if ex.terminal || ex.bodyDone || !ex.machine.canPullBodyNow then
    return progressed
  match ex.phase with
  | .receiving =>
    if ex.credit == 0 then
      return progressed
    if announcedOver ex ex.bodyBytes ex.config.maxBody then
      failNow (.limit .body)
      return true
    let (machine, chunk?) := ex.machine.pullBody
    let ex := { ex with machine }
    setEx ex
    let some pulled := chunk? | return progressed
    let data := pulled.chunk.data
    if ex.bodyBytes + data.size > ex.config.maxBody then
      failNow (.limit .body)
      return true
    setEx { ex with
      bodyBytes := ex.bodyBytes + data.size
      credit := ex.credit - min ex.credit data.size
      bodyDone := ex.bodyDone || pulled.final }
    unless data.isEmpty do emit (.deliverBody data)
    pullAvailable true
  | .draining =>
    if announcedOver ex ex.drained ex.config.drainBytes then
      finishNow false
      return true
    let (machine, chunk?) := ex.machine.pullBody
    let ex := { ex with machine }
    setEx ex
    let some pulled := chunk? | return progressed
    let ex := { ex with drained := ex.drained + pulled.chunk.data.size }
    setEx { ex with bodyDone := ex.bodyDone || pulled.final }
    if ex.drained > ex.config.drainBytes then
      finishNow false
      return true
    pullAvailable true
  | _ => return progressed

/--
After the machine has made all the progress it can: finishes the exchange if the body ended, or
fails it if input ended and what is missing can never come.
-/
private def settle : StepM Unit := do
  let ex ← getEx
  if ex.terminal then return
  let ending := match ex.phase with | .receiving | .draining => true | _ => false
  if ending && ex.bodyDone then
    finishNow true
  else if ex.inputEnded then
    -- With no credit the caller may still pull body the machine holds (a close-delimited body
    -- ends only when pulled after the end of input), so nothing is decided yet.
    let callerCanPull := match ex.phase with
      | .receiving => ex.credit == 0 && ex.machine.canPullBodyNow
      | _ => false
    unless callerCanPull do
      if ex.machine.failed then
        failOrDrop (.protocol (ex.machine.error.map toString |>.getD "failed"))
      else
        failOrDrop .peerClosed

/--
Runs the machine until it can make no more progress without new input or credit.
-/
private partial def absorb : StepM Unit := do
  let ex ← getEx
  if ex.terminal then return
  let (machine, result) := ex.machine.step
  setEx { ex with machine }
  let p₁ ← handleH1Events result.events
  let p₂ ← pullAvailable false
  let ex ← getEx
  let (machine, events) := ex.machine.takeEvents
  setEx { ex with machine }
  let p₃ ← handleH1Events events
  if (p₁ || p₂ || p₃) && !(← getEx).terminal then absorb else settle

/--
Handles one event from the shell.
-/
private def handle : ExchangeEvent → StepM Unit
  | .received bytes => do
    let ex ← getEx
    let ex := { ex with readInFlight := false, readBy := none }
    setEx ex
    match ex.phase with
    | .sending =>
      -- No response can be due before the server has the whole request head: never parse this.
      failNow (.protocol "bytes arrived before the request head was written")
    | _ =>
      unless bytes.isEmpty do
        setEx { ex with machine := ex.machine.feed bytes }
        absorb
  | .endOfInput => do
    let ex ← getEx
    let ex := { ex with readInFlight := false, readBy := none, inputEnded := true }
    setEx ex
    match ex.phase with
    | .sending => failNow .peerClosed
    | _ =>
      setEx { ex with machine := ex.machine.noMoreInput }
      absorb
  | .written count => do
    let ex ← getEx
    let some len := ex.writeInFlight | return
    let ex := { ex with written := ex.written + min count len, writeInFlight := none, writeBy := none }
    let ex := match ex.phase with
      | .sending => if ex.written ≥ ex.headBytes then { ex with phase := .awaitingHead } else ex
      | _ => ex
    let ex :=
      if ex.uploadOver && ex.readInFlight && ex.readBy.isNone then
        { ex with readBy := some (ex.now + ex.config.gapMs) }
      else ex
    setEx ex
  | .writeFailed detail => do
    let ex ← getEx
    if ex.writeInFlight.isNone then return
    setEx { ex with writeInFlight := none, writeBy := none }
    match ex.phase with
    | .sending => failNow .peerClosed detail
    | _ =>
      -- Once the request head is out a response may be due, perhaps already waiting to be read (a
      -- server that answers early and then closes): stop the upload and keep reading.
      setEx { (← getEx) with writeError := some detail }
      stopUpload
  | .readFailed detail => do
    modifyEx ({ · with readInFlight := false, readBy := none })
    failOrDrop .peerClosed detail
  | .wantBody bytes => do
    let ex ← getEx
    setEx { ex with credit := ex.credit + bytes }
    if ex.phase matches .receiving then absorb
  | .tick => pure ()
  | .abandon => do
    let ex ← getEx
    match ex.phase with
    | .sending | .awaitingHead => failNow .localClose
    | .receiving =>
      let worthDraining :=
        ex.config.keepAlive && ex.machine.keepAlive && ex.framing.certain && !ex.early &&
          ex.written == ex.request.size && !ex.inputEnded &&
          !announcedOver ex 0 ex.config.drainBytes
      if worthDraining then
        setEx { ex with phase := .draining, drainBy := some (ex.now + ex.config.drainMs) }
        absorb
      else
        finishNow false
    | _ => pure ()

/--
Acts on the earliest deadline that has passed, if any; the deadline of the whole exchange wins a
tie.  Returns whether it acted without ending the exchange, in which case a later deadline may have
passed as well.
-/
private def expireOne : StepM Bool := do
  let ex ← getEx
  if ex.terminal then return false
  let now := ex.now
  match ex.phase with
  | .draining =>
    -- The read gap still counts while draining; any deadline ends the drain without reuse.
    if now ≥ ex.deadline || ex.drainBy.any (now ≥ ·) || ex.readBy.any (now ≥ ·) then
      finishNow false
    return false
  | _ =>
    -- Candidates as (when, rank, what); the smallest (when, rank) that has passed wins.
    let candidates : List (Timestamp × Nat × TimeoutKind) :=
      [(ex.deadline, 0, .deadline)] ++
        (ex.writeBy.map fun t => (t, 1, .write)).toList ++
        (ex.readBy.map fun t => (t, 2, .read)).toList
    let passed := candidates.filter fun (t, _, _) => t ≤ now
    let first := passed.foldl (init := none) fun best c =>
      match best with
      | none => some c
      | some b => if c.1 < b.1 || (c.1 == b.1 && c.2.1 < b.2.1) then some c else some b
    match first with
    | none => return false
    | some (_, _, TimeoutKind.write) =>
      if ex.head.isSome then
        stopUpload
        return true
      else
        failNow (.timeout .write) s!"{ex.written} of {ex.request.size} request bytes accepted"
        return false
    | some (_, _, which) =>
      failNow (.timeout which)
      return false

/--
Acts on every deadline that has passed, earliest first.  Only a stalled upload after the response
head lets the exchange go on (it clears the write deadline), so two rounds suffice.
-/
private def expire : StepM Unit := do
  if ← expireOne then
    discard expireOne

/--
Issues the next write and read, if they are due and none is in flight.
-/
private def schedule : StepM Unit := do
  let ex ← getEx
  if ex.terminal then return
  if !ex.uploadStopped && ex.writeInFlight.isNone && ex.written < ex.request.size then
    let size := ex.request.size
    let stop := min size (ex.written + max 1 ex.config.writeChunk)
    let slice :=
      if ex.written == 0 && stop == size then ex.request else ex.request.extract ex.written stop
    setEx { ex with
      writeInFlight := some (stop - ex.written), writeBy := some (ex.now + ex.config.gapMs),
      sentAny := true }
    emit (.write slice)
  let ex ← getEx
  if !ex.readInFlight && ex.wantsInput then
    let readBy := if ex.uploadOver then some (ex.now + ex.config.gapMs) else none
    setEx { ex with readInFlight := true, readBy }
    emit (.read ex.config.readChunk)

/--
Starts `req` on an open connection at time `now`, with `deadline` for the whole exchange.  Returns
the exchange and the first actions: the first write, or a failure if the deadline has passed.
-/
def begin (req : PreparedRequest) (now deadline : Timestamp) : Exchange × Array ExchangeAction :=
  let ex : Exchange := {
    config := req.config, machine := req.machine, method := req.method, request := req.bytes,
    headBytes := req.headBytes, deadline, now }
  let ((), (ex, actions)) := (do expire; schedule : StepM Unit).run (ex, #[])
  (ex, actions)

/--
Advances the exchange by one event that happened at time `now`, and returns the actions to perform,
in order.  An exchange that has ended ignores every event, and a tick earlier than `nextDeadline`
changes nothing.
-/
def step (ex : Exchange) (now : Timestamp) (event : ExchangeEvent) :
    Exchange × Array ExchangeAction :=
  let stale := match event, ex.nextDeadline with
    | .tick, some due => now < due
    | _, _ => false
  if ex.terminal || stale then
    (ex, #[])
  else
    let ex := { ex with now := max ex.now now }
    let ((), (ex, actions)) := (do handle event; expire; schedule : StepM Unit).run (ex, #[])
    (ex, actions)

end Exchange

end LeanHttp
