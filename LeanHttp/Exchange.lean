module

public import LeanHttp.Codec.Response
public import LeanHttp.Codec.Request
public import LeanHttp.Error

public section

/-!
# The exchange core

One request and its response on one connection, as a pure step function over the response codec
(`LeanHttp.Codec.Parser`), which parses the response, and the request serialiser
(`LeanHttp.Codec.encodeRequest`), which encodes the request.

`Exchange.prepare` encodes the request before any I/O.  `Exchange.begin` starts the exchange on an
open connection and returns the first actions; from then on the shell reports everything that
happens as an `ExchangeEvent` to `Exchange.step`, performs the `ExchangeAction`s it returns, and
sleeps no later than `Exchange.nextDeadline`.  Time is an argument of `step`, deadlines are state,
and nothing here performs I/O, so every interleaving of events can be replayed and checked.

What the core guarantees, by construction:

- **No response without a request.**  Bytes are handed to the parser only once the whole request
  head has been written: the core asks for no read before that, and bytes reported earlier anyway
  fail the exchange unparsed.  Bytes a server sent before it saw the request (on a reused
  connection, a 408 before closing) wait in the socket and are read as the response; catching
  those is the job of the idle check before a pooled connection is reused.
- **One write in flight.**  The request goes out in slices of `ExchangeConfig.writeChunk` bytes, the
  next one only after the previous one completed.
- **Reuse only when it is safe.**  The verdict of `finish` is `true` only when the parser says the
  connection could carry another exchange (`Codec.Parser.reusable`: the response ended, framed with
  certainty, with nothing after it, before the end of input, and its keep-alive verdict allowed it),
  the caller has received the whole body, the request asked for keep-alive and was written in full
  before the response head arrived, and the peer did not close.
- **Early responses are delivered.**  The response is read while the request body is still being
  written, so a server that answers early (a 413, say) and stops reading is heard, and a write that
  fails once the request head is out only stops the upload; the connection is not reused
  afterwards.
- **Errors say how far the request got** (`Failure.delivery`, `Failure.written`).

The parser enforces the limits on interim responses and on the body, refuses
`101 Switching Protocols` and a body with a transfer coding other than chunked, and delivers every
body byte it is fed.  The core holds the body bytes the caller has not asked for yet: it reads from
the connection only while the caller wants more, so what it holds never exceeds what one read
returned, and it replaces that list rather than growing it across steps.
-/

namespace LeanHttp

set_option linter.all true

open Std.Http

/--
A point in time, in milliseconds of a monotonic clock (`IO.monoMsNow` in the shell).
-/
abbrev Timestamp := Nat

/--
The limits and timeouts of one exchange.
-/
structure ExchangeConfig where
  /--
  Parser limits for the response head and framing.  Their `maxInterim` and `maxBody` are replaced by
  the fields of the same names below (`ExchangeConfig.codec`).
  -/
  limits : Codec.Config := {}

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
  The read size is positive: a read of zero bytes can return nothing, and so make no progress.
  -/
  readChunk_pos : 0 < readChunk := by omega

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
  The gap is positive.  A write or read issued with no time to complete would be due the moment it
  was issued, and the exchange would have no deadline ahead for the shell to wait for.
  -/
  gapMs_pos : 0 < gapMs := by omega

  /--
  When the caller abandons a body, how many more decoded body bytes may be read and discarded to
  keep the connection reusable.
  -/
  drainBytes : Nat := 64 * 1024

  /--
  When the caller abandons a body, how long the rest may take to arrive and keep the connection
  reusable.  Zero keeps the connection only if the rest has already arrived: the drain's deadline
  passes in the step that starts it.
  -/
  drainMs : Nat := 100

/--
The parser's configuration: the limits, with the interim and body limits of the exchange.
-/
def ExchangeConfig.codec (config : ExchangeConfig) : Codec.Config :=
  { config.limits with maxInterim := config.maxInterim, maxBody := config.maxBody }

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
  A read returned these bytes.  An empty read counts as a `tick`: the read is still in flight as far
  as the core is concerned and its read gap still runs, so a shell that reports empty reads cannot
  hold the exchange open past the gap.  Bytes reported after the end of input are ignored.
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
  The caller wants more of the response body: while it has asked for more than it has received, the
  core delivers what it holds and reads more.  Body bytes come in the pieces the parser cut them
  into, and whatever the core holds goes out at once, so a delivery may exceed what is left of
  `bytes`, by at most what one read returned.
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
  The limits and timeouts of the exchange.  `keepAlive` is on only if it was asked for and the
  request head allows it (`Codec.requestKeepAlive`).
  -/
  config : ExchangeConfig

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
  ⟨{ config := {}, method := .get, bytes := .empty, headBytes := 0 }⟩

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
  The response parser, fed every byte read once the request head was written.
  -/
  parser : Codec.Parser := Codec.Parser.start {} .get

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
  The final response head, once delivered.
  -/
  head : Option Response.Head := none

  /--
  Whether the final response head arrived before the request was written in full.
  -/
  early : Bool := false

  /--
  Body bytes the caller has asked for and not yet received.
  -/
  credit : Nat := 0

  /--
  Body bytes the parser delivered and the caller has not received yet, in order.  Bytes are held
  only while the caller has no credit, and no read is issued while any are held, so this is never
  more than one read's worth.
  -/
  held : List ByteArray := []

  /--
  Whether the caller abandoned the exchange.
  -/
  abandoned : Bool := false

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
The cause the core reports for a rejection by the parser.
-/
def causeOf : Codec.Error → Cause
  | .badMessage => .protocol "Bad message"
  | .unsupportedVersion => .protocol "Unsupported version"
  | .tooManyHeaders | .headersTooLarge => .limit .headers
  | .bodyTooLarge => .limit .body
  | .tooManyInterim => .limit .interim
  | .switchingProtocols => .protocol "101 Switching Protocols, but no upgrade was requested"
  | .unsupportedCoding =>
    .protocol "a transfer coding other than chunked, which the client cannot decode"
  | .closed => .peerClosed

/--
Encodes a request.  `head` must already carry its `Host` field; its framing fields are replaced by
a `Content-Length` for `body` (none for a bodiless request whose method does not anticipate one), and
its `Connection` fields by `Connection: close` unless the connection is to be kept alive
(`Codec.encodeRequest`).  The prepared configuration keeps `keepAlive` on only if the head allows
it.
-/
def prepare (config : ExchangeConfig) (head : Request.Head) (body : ByteArray) : PreparedRequest :=
  let encoded := Codec.encodeRequest config.keepAlive head body
  { config := { config with keepAlive := encoded.keepAlive }, method := head.method,
    bytes := encoded.bytes, headBytes := encoded.headBytes }

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
Interim responses read so far.
-/
def interim (ex : Exchange) : Nat :=
  ex.parser.interim

/--
`true` once the response ended and the caller has received all of its body.
-/
def bodyDone (ex : Exchange) : Bool :=
  ex.parser.complete && ex.held.isEmpty

/--
Whether the connection may be reused if the exchange ended now.
-/
def reusableNow (ex : Exchange) : Bool :=
  ex.config.keepAlive && ex.parser.reusable && ex.held.isEmpty &&
    ex.written == ex.request.size && !ex.early && !ex.inputEnded

/--
Whether the core wants input now.
-/
def wantsInput (ex : Exchange) : Bool :=
  !ex.inputEnded &&
    match ex.phase with
    | .awaitingHead | .draining => true
    | .receiving => !ex.parser.complete && ex.held.isEmpty && ex.credit > 0
    | _ => false

/--
`true` when the body still to come is announced larger than what `limit` leaves, given `used`.
-/
def announcedOver (ex : Exchange) (used limit : Nat) : Bool :=
  match ex.parser.phase with
  | .body (.fixed remaining) => used + remaining > limit
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
Delivers every held body piece, in order, if the caller has credit (all of them, so that bytes
already read are never held back from a caller that wants more, as the machine's buffered bytes were
not); returns the credit left, the pieces still held and the actions.
-/
def releaseList : Nat → List ByteArray → Array ExchangeAction →
    Nat × List ByteArray × Array ExchangeAction
  | 0, held, acts => (0, held, acts)
  | credit + 1, held, acts =>
    (credit + 1 - min (credit + 1) (held.foldl (· + ·.size) 0), [],
      held.foldl (fun a b => a.push (.deliverBody b)) acts)

/--
Delivers the held body bytes the caller has credit for, while receiving.
-/
private def release : StepM Unit := fun s =>
  match s.1.phase with
  | .receiving =>
    let r := releaseList s.1.credit s.1.held s.2
    ((), ({ s.1 with credit := r.1, held := r.2.1 }, r.2.2))
  | _ => ((), s)

/--
Delivers the final head the parser reported.
-/
private def onHead (h : Codec.Head) : StepM Unit := do
  let ex ← getEx
  if ex.terminal || ex.head.isSome then return
  setEx { ex with
    head := some h.response, phase := .receiving, early := decide (ex.written < ex.request.size) }
  emit (.deliverHead h.response)

/--
Takes body bytes the parser delivered: while draining they are counted and discarded, within the
drain limit; otherwise they are held, and delivered as far as the caller's credit goes.
-/
private def onBodies (bodies : List ByteArray) : StepM Unit := do
  let ex ← getEx
  match ex.phase with
  | .draining =>
    let drained := bodies.foldl (· + ·.size) ex.drained
    setEx { ex with drained }
    if drained > ex.config.drainBytes then finishNow false
  | _ =>
    setEx { ex with held := ex.held ++ bodies }
    release

/--
The head among a batch of the parser's events, if there is one.
-/
def headOf (events : Array Codec.Event) : Option Codec.Head :=
  events.findSome? fun | .head h => some h | _ => none

/--
The non-empty body pieces among a batch of the parser's events, in order.
-/
def bodiesOf (events : Array Codec.Event) : List ByteArray :=
  events.toList.filterMap fun | .body b => if b.isEmpty then none else some b | _ => none

/--
The rejection among a batch of the parser's events, if there is one.
-/
def errorOf (events : Array Codec.Event) : Option Codec.Error :=
  events.findSome? fun | .error e => some e | _ => none

/--
Delivers a head the parser reported, if it reported one.
-/
private def onHead? : Option Codec.Head → StepM Unit
  | some h => onHead h
  | none => pure ()

/--
Fails the exchange for a rejection by the parser, if there was one.
-/
private def onError? : Option Codec.Error → StepM Unit
  | some e => failOrDrop (causeOf e)
  | none => pure ()

/--
Acts on a batch of the parser's events.  A batch is a head, body bytes, then the end or a rejection,
each perhaps missing (`Codec.reach_shape`), so the three are taken in that order.
-/
private def onEvents (events : Array Codec.Event) : StepM Unit := do
  onHead? (headOf events)
  onBodies (bodiesOf events)
  onError? (errorOf events)

/--
After the parser has taken what it was given: finishes the exchange once the response ended and the
caller has the whole body, and gives up a drain whose announced rest exceeds the drain limit.
-/
private def settle : StepM Unit := do
  let ex ← getEx
  if ex.terminal then return
  match ex.phase with
  | .receiving =>
    if ex.bodyDone then finishNow true
  | .draining =>
    if ex.bodyDone then finishNow true
    else if ex.announcedOver ex.drained ex.config.drainBytes then finishNow false
  | _ => pure ()

/--
Hands what the parser made of new input to `onEvents`, then settles.
-/
private def absorb (r : Codec.Parser × Array Codec.Event) : StepM Unit := do
  modifyEx ({ · with parser := r.1 })
  onEvents r.2
  settle

/--
Handles one event from the shell.
-/
private def handle : ExchangeEvent → StepM Unit
  | .received bytes =>
    -- An empty read is no completion: like a tick, it leaves the read in flight.
    if bytes.isEmpty then pure () else do
      let ex ← getEx
      let ex := { ex with readInFlight := false, readBy := none }
      setEx ex
      match ex.phase with
      | .sending =>
        -- No response can be due before the server has the whole request head: never parse this.
        failNow (.protocol "bytes arrived before the request head was written")
      | _ =>
        -- Bytes after the end of input (which no read can return) are ignored.
        unless ex.inputEnded do absorb (ex.parser.feed bytes)
  | .endOfInput => do
    let ex ← getEx
    let wasEnded := ex.inputEnded
    let ex := { ex with readInFlight := false, readBy := none, inputEnded := true }
    setEx ex
    if wasEnded then return
    match ex.phase with
    | .sending => failNow .peerClosed
    | _ => absorb ex.parser.finish
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
      -- A write that had already stalled (and stopped the upload) failing at last changes nothing.
      if ex.uploadStopped then return
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
    if ex.phase matches .receiving then
      release
      settle
  | .tick => pure ()
  | .abandon => do
    let ex ← getEx
    let ex := { ex with abandoned := true }
    setEx ex
    match ex.phase with
    | .sending | .awaitingHead => failNow .localClose
    | .receiving =>
      let drained := ex.held.foldl (· + ·.size) 0
      let worthDraining :=
        ex.config.keepAlive && ex.parser.head.any (·.keepAlive) && ex.parser.certain && !ex.early &&
          ex.written == ex.request.size && !ex.inputEnded && drained ≤ ex.config.drainBytes &&
          !ex.announcedOver drained ex.config.drainBytes
      if worthDraining then
        setEx { ex with
          phase := .draining, held := [], drained, drainBy := some (ex.now + ex.config.drainMs) }
        settle
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
    config := req.config, parser := Codec.Parser.start req.config.codec req.method,
    method := req.method, request := req.bytes, headBytes := req.headBytes, deadline, now }
  let ((), (ex, actions)) := (do expire; schedule : StepM Unit).run (ex, #[])
  (ex, actions)

/--
Advances the exchange by one event that happened at time `now`, and returns the actions to perform,
in order.  An exchange that has ended ignores every event.  A tick earlier than `nextDeadline`
changes nothing, not even the time, and an empty read is a tick: it is no completion of the read in
flight.
-/
def step (ex : Exchange) (now : Timestamp) (event : ExchangeEvent) :
    Exchange × Array ExchangeAction :=
  let stale := match event, ex.nextDeadline with
    | .tick, some due => now < due
    | .received bytes, some due => bytes.isEmpty && now < due
    | _, _ => false
  if ex.terminal || stale then
    (ex, #[])
  else
    let ex := { ex with now := max ex.now now }
    let ((), (ex, actions)) := (do handle event; expire; schedule : StepM Unit).run (ex, #[])
    (ex, actions)

end Exchange

end LeanHttp
