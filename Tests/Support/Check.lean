import LeanHttp.Exchange

/-!
# Properties of the exchange core, checked at every step

The checker keeps its own model of a run, built only from the events the environment reported and
the actions the core emitted, and checks every step against it.  It does not look inside the core
except for `terminal`, `nextDeadline` and a fingerprint of the state (for the stale-tick property).

Knowledge of the response the environment sends comes from an `Oracle`, written by hand for each
response script, independently of the core and of the HTTP/1.1 machine.
-/

open Std.Http LeanHttp

/-- What the checker knows of the response the environment sends, independently of the core. -/
structure Oracle where
  /-- Whether these bytes, exactly, are one complete response whose framing permits reuse. -/
  exactReusable : ByteArray → Bool := fun _ => false
  /--
  The body a caller must have received if the exchange finishes, unabandoned, after these bytes
  arrived; `none` when finishing after exactly these bytes is wrong.
  -/
  bodyFor : ByteArray → Option ByteArray := fun _ => none
  /-- The whole body of the final response, of which every delivered body must be a prefix. -/
  body : Option ByteArray := none
  /-- Whether the response ends only with the input, so that finishing needs end of input. -/
  needsEnd : Bool := false

instance : Inhabited Oracle := ⟨{}⟩

/-- The checker's model of a run, built from the events and the actions alone. -/
structure Model where
  /-- The request bytes the core must write, in order. -/
  request : ByteArray
  /-- The length of the request head, found independently (the first blank line). -/
  headBytes : Nat
  /-- The deadline of the exchange. -/
  deadline : Nat
  /-- Whether reuse is allowed at all. -/
  keepAlive : Bool
  /-- Request bytes whose write completed. -/
  acked : Nat := 0
  /-- The length of the write in flight. -/
  outstanding : Option Nat := none
  /-- Whether any write was issued. -/
  everWrote : Bool := false
  /-- Whether a read is in flight. -/
  readOutstanding : Bool := false
  /-- Whether the final head was delivered. -/
  headDelivered : Bool := false
  /-- `acked` when the head was delivered. -/
  ackedAtHead : Nat := 0
  /-- Every byte received, in order. -/
  fed : ByteArray := .empty
  /-- Whether bytes arrived before the request head was written. -/
  unsolicited : Bool := false
  /-- Whether end of input was reported. -/
  eofSeen : Bool := false
  /-- Whether the caller abandoned. -/
  abandoned : Bool := false
  /-- Whether `finish` or `fail` was emitted. -/
  ended : Bool := false
  /-- The body delivered. -/
  body : ByteArray := .empty
  /-- The time of the latest step. -/
  now : Nat := 0
deriving Inhabited

/-- A broken property. -/
structure Violation where
  /-- The property's name. -/
  property : String
  /-- What was seen. -/
  detail : String
deriving Inhabited

/-- The length of a request head: up to and including the first blank line. -/
def requestHeadLength (request : ByteArray) : Nat := Id.run do
  for i in [0:request.size] do
    if i + 4 ≤ request.size && request[i]! == 13 && request[i+1]! == 10 && request[i+2]! == 13 &&
        request[i+3]! == 10 then
      return i + 4
  return request.size

/-- `true` when `a` is a prefix of `b`. -/
def ByteArray.isPrefixOf (a b : ByteArray) : Bool :=
  a.size ≤ b.size && b.extract 0 a.size == a

/-- A model for a run of `prepared` with `deadline`. -/
def Model.init (prepared : PreparedRequest) (deadline now : Nat) : Model :=
  { request := prepared.bytes, headBytes := requestHeadLength prepared.bytes, deadline,
    keepAlive := prepared.config.keepAlive, now }

/-- Updates the model with an event the environment reported. -/
def Model.observe (m : Model) (event : ExchangeEvent) : Model :=
  if m.ended then m else
  match event with
  | .written n =>
    match m.outstanding with
    | some len => { m with acked := m.acked + min n len, outstanding := none }
    | none => m
  | .writeFailed _ => { m with outstanding := none }
  | .received bytes =>
    { m with readOutstanding := false, fed := m.fed ++ bytes,
             unsolicited := m.unsolicited || m.acked < m.headBytes }
  | .endOfInput => { m with readOutstanding := false, eofSeen := true }
  | .readFailed _ => { m with readOutstanding := false }
  | .abandon => { m with abandoned := true }
  | .wantBody _ | .tick => m

/-- A comparable summary of the core's state, for "a stale tick changes nothing". -/
def fingerprint (ex : Exchange) : String :=
  let r := ex.machine.reader
  s!"{reprStr ex.phase}|now={ex.now}|w={ex.written}|wf={ex.writeInFlight}|wb={ex.writeBy}|" ++
  s!"us={ex.uploadStopped}|sa={ex.sentAny}|rf={ex.readInFlight}|rb={ex.readBy}|ie={ex.inputEnded}|" ++
  s!"i={ex.interim}|h={ex.head.map (·.status.toCode)}|f={reprStr ex.framing}|e={ex.early}|" ++
  s!"c={ex.credit}|bb={ex.bodyBytes}|bd={ex.bodyDone}|d={ex.drained}|db={ex.drainBy}|" ++
  s!"rs={reprStr r.state}|pos={r.input.pos}|n={r.input.array.size}|nmi={r.noMoreInput}|" ++
  s!"ka={ex.machine.keepAlive}|st={ex.machine.pullBodyStalled}"

/-- A short rendering of an action, for traces and reports. -/
def renderAction : ExchangeAction → String
  | .write bytes => s!"write {bytes.size}"
  | .read _ => "read"
  | .deliverHead head => s!"head {head.status.toCode}"
  | .deliverBody bytes => s!"body {repr (String.fromUTF8? bytes |>.getD s!"<{bytes.size} bytes>")}"
  | .finish reusable => s!"finish reusable={reusable}"
  | .fail f =>
    let detail := if f.detail.isEmpty then "" else s!" ({f.detail})"
    s!"fail {f.cause.describe}{detail} [{f.delivery.name}, written={f.written}]"

/-- A short rendering of an event. -/
def renderEvent : ExchangeEvent → String
  | .received bytes => s!"received {repr (String.fromUTF8? bytes |>.getD s!"<{bytes.size} bytes>")}"
  | .endOfInput => "endOfInput"
  | .written n => s!"written {n}"
  | .wantBody n => s!"wantBody {n}"
  | .tick => "tick"
  | .abandon => "abandon"
  | .readFailed d => s!"readFailed {repr d}"
  | .writeFailed d => s!"writeFailed {repr d}"

/--
Checks one step: the core was in `pre`, the environment reported `event` at time `now`, and the core
went to `post` with `actions`.  Returns the updated model and the first violation, if any.
-/
def checkStep (oracle : Oracle) (m : Model) (pre : Exchange) (now : Nat) (event : ExchangeEvent)
    (post : Exchange) (actions : Array ExchangeAction) : Model × Option Violation := Id.run do
  let wasEnded := m.ended
  let before := m
  let mut m := { m.observe event with now := max m.now now }
  let bad (p d : String) : Option Violation := some { property := p, detail := d }
  if wasEnded && !actions.isEmpty then
    return (m, bad "nothing after the end" s!"{actions.map renderAction}")
  for action in actions do
    if m.ended then
      return (m, bad "one end, last" s!"{renderAction action} after the end")
    match action with
    | .write bytes =>
      if m.outstanding.isSome then
        return (m, bad "one write in flight" s!"write {bytes.size} while {m.outstanding} in flight")
      if bytes.isEmpty || bytes != m.request.extract m.acked (m.acked + bytes.size) then
        return (m, bad "writes follow the request" s!"write {bytes.size} at {m.acked}")
      m := { m with outstanding := some bytes.size, everWrote := true }
    | .read _ =>
      if m.readOutstanding then
        return (m, bad "one read in flight" "read while a read is in flight")
      m := { m with readOutstanding := true }
    | .deliverHead head =>
      if m.headDelivered then
        return (m, bad "one head" s!"second head {head.status.toCode}")
      if m.acked < m.headBytes then
        return (m, bad "no head before the request head is written"
          s!"head {head.status.toCode} with {m.acked} of {m.headBytes} head bytes written")
      if m.unsolicited then
        return (m, bad "unsolicited bytes never make a response" s!"head {head.status.toCode}")
      m := { m with headDelivered := true, ackedAtHead := m.acked }
    | .deliverBody bytes =>
      if !m.headDelivered then
        return (m, bad "no body before the head" s!"{bytes.size} bytes")
      m := { m with body := m.body ++ bytes }
      if let some whole := oracle.body then
        if !m.body.isPrefixOf whole then
          return (m, bad "the body is the response's" s!"{m.body.size} bytes delivered, not a prefix")
    | .finish reusable =>
      m := { m with ended := true }
      if !m.abandoned then
        match oracle.bodyFor m.fed with
        | none =>
          return (m, bad "finish only after a complete response"
            s!"finish after {m.fed.size} bytes {repr (String.fromUTF8? m.fed |>.getD "")}")
        | some expected =>
          if oracle.needsEnd && !m.eofSeen then
            return (m, bad "finish only after a complete response" "a close-delimited body before the end")
          if m.body != expected || !m.headDelivered then
            return (m, bad "a finished response delivered its whole body"
              s!"{m.body.size} body bytes, expected {expected.size}")
      if reusable then
        let reasons := [
          (m.keepAlive, "keep-alive is off"),
          (m.acked == m.request.size, s!"only {m.acked} of {m.request.size} request bytes written"),
          (m.ackedAtHead == m.request.size, s!"the head arrived after {m.ackedAtHead} bytes"),
          (!m.eofSeen, "the peer closed"),
          (oracle.exactReusable m.fed, s!"the {m.fed.size} bytes read are not exactly one reusable response"),
          (m.headDelivered, "no head")]
        if let some (_, why) := reasons.find? (!·.1) then
          return (m, bad "reusable only when safe" why)
    | .fail f =>
      m := { m with ended := true }
      let ok := match f.delivery with
        | .notSent => !m.everWrote
        | .maybeDelivered => m.everWrote && !m.headDelivered
        | .responseReceived => m.headDelivered
      if !ok then
        return (m, bad "delivery follows what was written"
          s!"{f.delivery.name}, wrote={m.everWrote}, head={m.headDelivered}")
      if f.written != m.acked then
        return (m, bad "a failure counts the bytes written" s!"{f.written}, model {m.acked}")
  -- Properties of the state after the step.
  if post.terminal != m.ended then
    return (m, bad "the core ends only with an action" s!"terminal={post.terminal}, ended={m.ended}")
  if m.now ≥ m.deadline && !post.terminal then
    return (m, bad "after the deadline the exchange has ended" s!"now={m.now}, deadline={m.deadline}")
  if !wasEnded && event matches .received _ && before.acked < before.headBytes then
    if !(actions.any fun | .fail _ => true | _ => false) then
      return (m, bad "unsolicited bytes fail the exchange" s!"{actions.map renderAction}")
  if let (.tick, some due) := (event, pre.nextDeadline) then
    if now < due && (!actions.isEmpty || fingerprint post != fingerprint pre) then
      return (m, bad "a stale tick changes nothing" s!"tick at {now}, due {due}")
  if !post.terminal then
    match post.nextDeadline with
    | none => return (m, bad "a live exchange has a deadline" "none")
    | some d =>
      if d > post.deadline then
        return (m, bad "a live exchange has a deadline" s!"{d} after {post.deadline}")
  return (m, none)
