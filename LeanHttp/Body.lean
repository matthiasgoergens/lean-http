module

public import Std.Async.TCP
public import Std.Http.Data
public import LeanHttp.Error
public import LeanHttp.Exchange
public import LeanHttp.Wait

public section

/-!
# Driving an exchange, and the body stream

`Live` is an exchange in progress on a socket: the exchange core and the socket operations the shell
started for it.  The shell drives it in pieces: until the final response head (the client then asks
the per-call planner what to do with it), and afterwards one pull of body bytes at a time,
for the caller, or until the end, to discard a body nobody reads.  At most one write and one read
are in flight, and for a streamed request body one call of its producer, the core decides
everything, and the shell waits for the first operation to complete or the core's next deadline,
whichever comes first.  A streamed request body goes on being pulled and written while the response
is read, as long as the exchange goes on; a producer still running when the exchange ends is left to
finish, and what it returns is dropped.

A `BodyStream` is a response body the caller pulls.  A `read` that finds nothing held gives the
core credit for one more read from the socket, so the core reads only as fast as the caller does:
what the shell holds is never more than one read.  The stream is valid only inside the callback of
`Client.withResponse`: when the callback ends, normally or by an exception, whatever is unread is
abandoned (drained within the drain limit to keep the connection, or the connection closed), and the
stream refuses every later use with an error.  A read still in progress in another task when the
callback ends has its receive cancelled, and the callback's end waits for it, so no receive outlives
the callback.
-/

namespace LeanHttp

set_option linter.all true

open Std.Http Std.Async Std.Net

/--
A socket operation the shell started for the exchange core, once it has completed.
-/
inductive Completion where
  /--
  A read ended: bytes, end of input, or an error.
  -/
  | read (result : Except IO.Error (Option ByteArray))

  /--
  A write of `length` bytes ended.
  -/
  | wrote (length : Nat) (result : Except IO.Error Unit)

  /--
  A call of the request body's producer ended: a chunk, the end of the body, or an error.
  -/
  | pulled (result : Except IO.Error (Option ByteArray))

/--
An exchange in progress on a socket.
-/
structure Live where
  /--
  The socket.
  -/
  socket : TCP.Socket.Client

  /--
  The exchange core.
  -/
  ex : Exchange

  /--
  The read in flight.
  -/
  reading : Option (Task Completion) := none

  /--
  The write in flight.
  -/
  writing : Option (Task Completion) := none

  /--
  Whether any read returned bytes.
  -/
  received : Bool := false

  /--
  The producer of a streamed request body, called for each pull.
  -/
  produce : Async (Option ByteArray) := pure none

  /--
  The call of the producer in flight.
  -/
  pulling : Option (Task Completion) := none

/--
What the core handed over in one stretch of driving.
-/
structure Delivered where
  /--
  The final response head, if it was delivered.
  -/
  head : Option Response.Head := none

  /--
  Body bytes delivered, in order.
  -/
  bodies : Array ByteArray := #[]

/--
The exchange's verdict once it has ended: `some true` if the connection may be reused, `some false`
if it must be dropped, `none` while the exchange is still going.
-/
def Live.verdict (live : Live) : Option Bool :=
  match live.ex.phase with
  | .finished reusable => some reusable
  | .failed _ => some false
  | _ => none

/--
The failure the exchange ended with, if it failed.
-/
def Live.failure? (live : Live) : Option Failure :=
  match live.ex.phase with
  | .failed f => some f
  | _ => none

/--
Stops a pending receive, if there is one, so that it releases the socket and no receive
registration outlives the exchange.
-/
def Live.cancelRead (live : Live) : BaseIO Live := do
  if live.reading.isSome then
    live.socket.native.cancelRecv.catchExceptions fun _ => pure ()
  return { live with reading := none }

/--
Performs the core's actions: starts its write and its read, and collects what it delivered.  Once
the exchange has ended, a receive still pending is cancelled.
-/
@[inline] def Live.perform (live : Live) (actions : Array ExchangeAction) (out : Delivered) :
    Async (Live × Delivered) := do
  let mut live := live
  let mut out := out
  for action in actions do
    match action with
    | .write bytes =>
      let task ← start (live.socket.send bytes)
      live := { live with writing := some (Task.map (sync := true) (Completion.wrote bytes.size) task) }
    | .read max =>
      let task ← start (live.socket.recv? max.toUInt64)
      live := { live with reading := some (Task.map (sync := true) Completion.read task) }
    | .pull =>
      let task ← start live.produce
      live := { live with pulling := some (Task.map (sync := true) Completion.pulled task) }
    | .deliverHead head => out := { out with head := some head }
    | .deliverBody bytes => out := { out with bodies := out.bodies.push bytes }
    | .finish _ | .fail _ => live ← live.cancelRead
  return (live, out)

/--
Waits for the first operation in flight to complete, or for the core's next deadline, and reports
what happened to the core.  Returns the core's actions.
-/
@[inline] def Live.next (live : Live) : Async (Live × Array ExchangeAction) := do
  let now ← IO.monoMsNow
  let wait := (live.ex.nextDeadline.getD now) - now
  -- Once the upload has stopped (the response head arrived first), the core makes nothing of the
  -- write still in flight, which may never complete; it is left out of the race, since every race
  -- adds a continuation to each task in it, and a long download would pile them up on that write.
  let writing := if live.ex.uploadStopped then none else live.writing
  let pending := live.reading.toArray ++ writing.toArray ++ live.pulling.toArray
  let (event, live) ← match ← awaitFirst pending wait with
    | none => pure (ExchangeEvent.tick, live)
    | some (.read result) =>
      -- An empty read, which a receive of a positive size should not return, is reported as a
      -- failed read: to the core an empty read is no completion, and it would wait for a read the
      -- shell no longer has in flight.
      let event := match result with
        | .ok (some bytes) =>
          if bytes.isEmpty then ExchangeEvent.readFailed "a receive returned no bytes"
          else .received bytes
        | .ok none => .endOfInput
        | .error err => .readFailed (toString err)
      let got := match result with
        | .ok (some bytes) => !bytes.isEmpty
        | _ => false
      pure (event, { live with reading := none, received := live.received || got })
    | some (.wrote length result) =>
      let event := match result with
        | .ok () => ExchangeEvent.written length
        | .error err => .writeFailed (toString err)
      pure (event, { live with writing := none })
    | some (.pulled result) =>
      let event := match result with
        | .ok chunk => ExchangeEvent.pulled chunk
        | .error err => .pullFailed (toString err)
      pure (event, { live with pulling := none })
  let (ex, actions) := live.ex.step (← IO.monoMsNow) event
  return ({ live with ex }, actions)

/--
Reports `event` to the core now.  Returns the core's actions.
-/
def Live.stepNow (live : Live) (event : ExchangeEvent) : BaseIO (Live × Array ExchangeAction) := do
  let (ex, actions) := live.ex.step (← IO.monoMsNow) event
  return ({ live with ex }, actions)

/--
Performs `actions`, then keeps reporting completions and deadlines to the core and performing its
actions, until `stop` holds of what it delivered or the exchange ends.  It decides nothing itself.

What is delivered is collected only until `stop` holds, which every caller makes true as soon as
anything it waits for arrives, so nothing grows across waits ("Nothing carried across a wait is
updated in place", `NOTES.md`).
-/
partial def Live.until (live : Live) (actions : Array ExchangeAction) (stop : Delivered → Bool)
    (out : Delivered := {}) : Async (Live × Delivered) := do
  let (live, out) ← live.perform actions out
  if live.ex.terminal || stop out then
    return (live, out)
  let (live, actions) ← live.next
  live.until actions stop out

/--
Starts `prepared` on `socket` with `deadline` for the whole call, and drives it until the final
response head arrives or the exchange ends first.  `produce` gives the chunks of a streamed body.  The core holds whatever body bytes come with the
head until the caller asks for them.
-/
def Live.begin (socket : TCP.Socket.Client) (prepared : PreparedRequest) (deadline : Nat)
    (produce : Async (Option ByteArray) := pure none) : Async (Live × Option Response.Head) := do
  let (ex, actions) := Exchange.begin prepared (← IO.monoMsNow) deadline
  let (live, out) ← ({ socket, ex, produce } : Live).until actions (·.head.isSome)
  return (live, out.head)

/--
Abandons the rest of the response: the core drains it within its drain limits, keeping the
connection reusable, or gives up on the connection; drives that to the end.  A body that has already
arrived in full is simply taken.  Returns the exchange's verdict on reuse.  No receive is pending
when it returns; should anything throw, the connection is not reused.
-/
def Live.abandon (live : Live) : Async Bool := do
  if let some verdict := live.verdict then
    discard <| live.cancelRead
    return verdict
  try
    -- A body that has arrived in full keeps the connection whatever its length: the core is given
    -- credit for what it holds, which it hands over and finishes, rather than told to abandon it
    -- and count what it holds against the drain limit.
    let event := if live.ex.parser.complete then .wantBody (2 ^ 62) else .abandon
    let (live, actions) ← live.stepNow event
    let (live, _) ← live.until actions fun _ => false
    discard <| live.cancelRead
    return live.verdict.getD false
  catch _ =>
    -- The receive pending may belong to a later state of the exchange than `live`: cancel whatever
    -- is pending on the socket.
    live.socket.native.cancelRecv.catchExceptions fun _ => pure ()
    return false

/--
Where a body stream stands.
-/
inductive BodyStream.State where
  /--
  Usable.  `live` is the exchange while it goes on; `none` once it ended, when `failure` says how,
  if it failed.  `pending` holds body bytes the core delivered and the caller has not read yet, the
  first piece from `offset` on: never more than one read's worth.
  -/
  | open (live : Option Live) (failure : Option Error) (pending : List ByteArray) (offset : Nat)

  /--
  A read is in progress, on `socket` if the exchange is still going; `done` is resolved when it has
  ended.
  -/
  | busy (socket : Option TCP.Socket.Client) (done : IO.Promise Unit)

  /--
  The callback ended; the stream refuses every use.
  -/
  | released

/--
A response body that the caller pulls, inside the callback of `Client.withResponse`.
-/
structure BodyStream where
  /--
  Where the stream stands.
  -/
  state : IO.Ref BodyStream.State

  /--
  Called once, when the exchange has ended, with its verdict on reusing the connection: gives the
  connection back to the pool or drops it.  It is taken out when called, so that the stream keeps no
  reference to the connection afterwards (a socket closes only when its last reference goes).
  -/
  settleOnce : IO.Ref (Option (Bool → BaseIO Unit))

  /--
  The call's error for a failure of the exchange while the body is read.
  -/
  errorOf : Failure → Error

  /--
  The error the stream raised, if it raised one, and its message: an exception with that message
  that leaves the callback is the call's error.
  -/
  raised : IO.Ref (Option (Error × String))

namespace BodyStream

/--
The message of the error raised by a stream used after its callback ended.
-/
def usedAfterMessage : String :=
  "the response body stream was used after the callback of Client.withResponse ended"

/--
Ends the exchange's hold on its connection with `verdict`, the first time only.
-/
def settle (s : BodyStream) (verdict : Bool) : BaseIO Unit := do
  if let some f ← s.settleOnce.modifyGet fun f => (f, none) then
    f verdict

/--
A stream over the body of the exchange `live`, whose head has been delivered.  If the exchange has
already ended, `settle` is called at once.
-/
def new (live : Live) (settle : Bool → BaseIO Unit) (errorOf : Failure → Error) :
    BaseIO BodyStream := do
  let s : BodyStream := {
    state := ← IO.mkRef (.open (some live) none [] 0), settleOnce := ← IO.mkRef (some settle),
    errorOf, raised := ← IO.mkRef none }
  if let some verdict := live.verdict then
    discard <| live.cancelRead
    s.settle verdict
    -- Body bytes that came with the head, before the failure, are the caller's first: the same as
    -- when the failure arrives in a later read.
    s.state.set (.open none (live.failure?.map errorOf) live.ex.held 0)
  return s

/--
Takes up to `max` bytes from the pending pieces, the first one from `offset` on.
-/
def take (pending : List ByteArray) (offset max : Nat) :
    Option (ByteArray × List ByteArray × Nat) :=
  match pending with
  | [] => none
  | piece :: rest =>
    let left := piece.size - offset
    if left ≤ max then
      some (if offset == 0 then piece else piece.extract offset piece.size, rest, 0)
    else
      some (piece.extract offset (offset + max), piece :: rest, offset + max)

/--
Records and raises `error`.
-/
private def raise {α : Type} (s : BodyStream) (error : Error) : Async α := do
  let message := toString error
  s.raised.set (some (error, message))
  throw (IO.userError message)

/--
Keeps driving the exchange until it delivers body bytes or ends, or the callback has ended.  The
last is checked after the core's actions are performed and before every wait, and the end of the
callback cancels the receive pending, so the wait it finds ends at once.
-/
private partial def drive (s : BodyStream) (live : Live) (actions : Array ExchangeAction) :
    Async (Live × Array ByteArray) := do
  let (live, out) ← live.perform actions {}
  if live.ex.terminal || !out.bodies.isEmpty then
    return (live, out.bodies)
  if (← s.state.get) matches .released then
    return (live, #[])
  let (live, actions) ← live.next
  s.drive live actions

/--
Drives the exchange until it delivers body bytes or ends, after giving the core credit for one more
read if it has none: the core then delivers what it holds or reads once more, and holds nothing
further, so the shell never holds more than one read.  Never throws: an exception from the socket
counts as a failed exchange.  Returns the stream's next state.
-/
private def advance (s : BodyStream) (live : Live) : Async State := do
  try
    let (live, actions) ←
      if live.ex.credit == 0 then live.stepNow (.wantBody 1) else pure (live, #[])
    let (live, bodies) ← s.drive live actions
    let pending := bodies.toList
    match live.verdict with
    | some verdict =>
      s.settle verdict
      return .open none (live.failure?.map s.errorOf) pending 0
    | none => return .open (some live) none pending 0
  catch e =>
    -- The receive pending may belong to a later state of the exchange than `live`.
    live.socket.native.cancelRecv.catchExceptions fun _ => pure ()
    s.settle false
    let failure : Failure := {
      cause := .peerClosed, delivery := .responseReceived, written := live.ex.written,
      status := live.ex.head.map (·.status), detail := s!"the client failed: {e}" }
    return .open none (some (s.errorOf failure)) [] 0

/--
Ends a read: stores the stream's new state, unless the callback ended meanwhile (a read from another
task), in which case the exchange is dropped here, its receive cancelled, and the read fails.  Then
tells a waiting `release` that the read is over.
-/
private def finishRead (s : BodyStream) (done : IO.Promise Unit) (next : State) : Async Unit := do
  let stored ← s.state.modifyGet fun
    | .busy .. => (true, next)
    | other => (false, other)
  unless stored do
    if let .open (some live) .. := next then
      live.socket.native.cancelRecv.catchExceptions fun _ => pure ()
      s.settle false
    done.resolve ()
    throw (IO.userError usedAfterMessage)
  done.resolve ()

/--
Reads the next body bytes, at most `max` (default 64 KiB; zero counts as one): `none` at the end of
the body.  Raises the call's error if the exchange fails while the body is read (the connection
closed early, a timeout, a limit), and an error if the stream is used after its callback ended or by
two reads at once.
-/
partial def read (s : BodyStream) (max : Nat := 64 * 1024) : Async (Option ByteArray) := do
  let max := if max == 0 then 1 else max
  let done ← IO.Promise.new
  let state ← s.state.modifyGet fun
    | st@(.open live ..) => (st, .busy (live.map (·.socket)) done)
    | other => (other, other)
  match state with
  | .busy .. => throw (IO.userError "BodyStream.read: another read of this stream is in progress")
  | .released => throw (IO.userError usedAfterMessage)
  | .open live failure pending _ =>
    -- With nothing held and the exchange going, drive it once; the stream stays busy until the
    -- read has taken what it returns.
    let next ← match pending, failure, live with
      | [], none, some live => s.advance live
      | _, _, _ => pure state
    let .open live failure pending offset := next
      | do s.finishRead done next; throw (IO.userError usedAfterMessage)
    match take pending offset max with
    | some (bytes, pending, offset) =>
      s.finishRead done (.open live failure pending offset)
      return some bytes
    | none =>
      match failure, live with
      | some e, _ =>
        s.finishRead done (.open none (some e) [] 0)
        s.raise e
      | none, none =>
        s.finishRead done (.open none none [] 0)
        return none
      | none, some live =>
        -- The drive stopped with nothing delivered and the exchange going: the callback ended
        -- meanwhile, and `finishRead` raises.  Should it not, the read starts again.
        s.finishRead done (.open (some live) none [] 0)
        s.read max

/--
Keeps driving the exchange, collecting every body piece it delivers (last first, with their total
size), until it ends or the callback has ended.  One loop with the wait in it, so that each read
from the socket costs one continuation, not one per layer of calls.
-/
private partial def collect (s : BodyStream) (live : Live) (actions : Array ExchangeAction)
    (chunks : List ByteArray) (size : Nat) : Async (Live × List ByteArray × Nat) := do
  let (live, out) ← live.perform actions {}
  let (chunks, size) := out.bodies.foldl (init := (chunks, size)) fun (c, n) b => (b :: c, n + b.size)
  if live.ex.terminal then
    return (live, chunks, size)
  if (← s.state.get) matches .released then
    return (live, chunks, size)
  let (live, actions) ← live.next
  s.collect live actions chunks size

/--
Reads the rest of the body into one byte array.  It gives the core credit for the whole body, so
the core reads on without waiting for each piece to be taken.  The pieces are kept in a list and
joined once at the end, in a buffer allocated there: appending each piece to one array would copy
the whole body every time, since a value carried across a wait is never updated in place
(`NOTES.md`).  Raises like `read`.
-/
def readAll (s : BodyStream) : Async ByteArray := do
  let done ← IO.Promise.new
  let state ← s.state.modifyGet fun
    | st@(.open live ..) => (st, .busy (live.map (·.socket)) done)
    | other => (other, other)
  let join (chunks : List ByteArray) (size : Nat) : ByteArray :=
    chunks.reverse.foldl (init := ByteArray.emptyWithCapacity size) (· ++ ·)
  match state with
  | .busy .. => throw (IO.userError "BodyStream.readAll: another read of this stream is in progress")
  | .released => throw (IO.userError usedAfterMessage)
  | .open live failure pending offset =>
    -- What the core delivered and the caller has not read comes first.
    let first := match pending with
      | [] => []
      | piece :: rest => (if offset == 0 then piece else piece.extract offset piece.size) :: rest
    let held := first.reverse
    let heldSize := first.foldl (· + ·.size) 0
    match failure, live with
    | some e, _ =>
      s.finishRead done (.open none (some e) [] 0)
      s.raise e
    | none, none =>
      s.finishRead done (.open none none [] 0)
      return join held heldSize
    | none, some live =>
      let next ← try
          let (live, actions) ← live.stepNow (.wantBody (2 ^ 62))
          let (live, chunks, size) ← s.collect live actions held heldSize
          match live.verdict with
          | some verdict =>
            s.settle verdict
            pure (Sum.inl (live.failure?.map s.errorOf, join chunks size))
          | none => pure (Sum.inr live)
        catch e =>
          live.socket.native.cancelRecv.catchExceptions fun _ => pure ()
          s.settle false
          let failure : Failure := {
            cause := .peerClosed, delivery := .responseReceived, written := live.ex.written,
            status := live.ex.head.map (·.status), detail := s!"the client failed: {e}" }
          pure (Sum.inl (some (s.errorOf failure), .empty))
      match next with
      | .inl (none, body) =>
        s.finishRead done (.open none none [] 0)
        return body
      | .inl (some e, _) =>
        s.finishRead done (.open none (some e) [] 0)
        s.raise e
      | .inr live =>
        -- The callback ended while the body was read (from another task).
        s.finishRead done (.open (some live) none [] 0)
        throw (IO.userError usedAfterMessage)

/--
Ends the stream when the callback ends: abandons the rest of the exchange if it is still going
(draining it within the drain limits, or dropping the connection), and refuses every later use.  A
read still in progress in another task has its receive cancelled, drops the connection, and is
waited for, so that no receive outlives the callback.
-/
def release (s : BodyStream) : Async Unit := do
  match ← s.state.swap .released with
  | .open (some live) .. => s.settle (← live.abandon)
  | .busy socket done =>
    -- Whoever takes the settle function owns the connection.  If the reader has already settled,
    -- the connection may be in the pool, or another call's, and its socket must not be touched.
    match ← s.settleOnce.modifyGet fun f => (f, none) with
    | some settle =>
      if let some socket := socket then
        socket.native.cancelRecv.catchExceptions fun _ => pure ()
      discard <| await done.result?
      settle false
    | none => discard <| await done.result?
  | _ => pure ()

end BodyStream

end LeanHttp
