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
  /--
  The request bytes the core must write, in order, as far as they are known: the prepared bytes,
  then, for a streamed body, each chunk the producer returned, framed by the model itself.
  -/
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
  /-- The status code of the final head, once delivered. -/
  headStatus : Option Nat := none
  /-- Every byte received, in order, before the end of input (and before the run ended). -/
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
  /-- How a streamed body is framed, if the request has one. -/
  framing : Option Codec.RequestFraming := none
  /-- The size of the prepared bytes: the request head, for a streamed body. -/
  start : Nat := 0
  /-- Whether the request is known in full: the producer of a streamed body has ended. -/
  complete : Bool := true
  /-- Body bytes the producer returned and the model framed. -/
  taken : Nat := 0
  /-- Whether a pull is in flight. -/
  pullOutstanding : Bool := false
  /-- Whether any pull was issued. -/
  everPulled : Bool := false
  /-- Whether the producer's answer broke the declared size, or the producer failed. -/
  bodyBroken : Bool := false
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
    keepAlive := prepared.config.keepAlive, now, framing := prepared.framing,
    start := prepared.bytes.size, complete := prepared.framing.isNone }

/--
Whether every byte of the request is known: it is complete, or a streamed body's declared size has
been given in full (the producer is then asked once more whether it has ended).
-/
def Model.wireDone (m : Model) : Bool :=
  m.complete ||
    match m.framing with
    | some (.length size) => m.taken == size
    | _ => false

/-- The ASCII hex digits of `n`, lower case, written here independently of the codec. -/
def hexBytes (n : Nat) : ByteArray :=
  (String.ofList (Nat.toDigits 16 n)).toUTF8

/--
The model's own framing of what the producer returned to the pull in flight: a chunk is appended
as it is after a `Content-Length` (unless it would exceed the declared size), or with its size line
and CRLF when chunked; the end appends the last chunk when chunked.  A chunk beyond the declared
size, an end short of it, or a producer error marks the body broken, which the core must answer by
failing the exchange.
-/
def Model.take (m : Model) : Option ByteArray → Model
  | some chunk =>
    if chunk.isEmpty then m else
    match m.framing with
    | some (.length size) =>
      if m.taken + chunk.size ≤ size then
        { m with request := m.request ++ chunk, taken := m.taken + chunk.size }
      else { m with bodyBroken := true }
    | some .chunked =>
      { m with request := m.request ++ hexBytes chunk.size ++ "\r\n".toUTF8 ++ chunk ++ "\r\n".toUTF8,
               taken := m.taken + chunk.size }
    | none => m
  | none =>
    match m.framing with
    | some (.length size) =>
      if m.taken == size then { m with complete := true } else { m with bodyBroken := true }
    | some .chunked => { m with request := m.request ++ "0\r\n\r\n".toUTF8, complete := true }
    | none => { m with complete := true }

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
    -- An empty read completes nothing: the core counts it as a tick.
    -- Bytes after the end of input are ignored by the core, and not counted as received.
    if bytes.isEmpty then m else if m.eofSeen then { m with readOutstanding := false } else
    { m with readOutstanding := false, fed := m.fed ++ bytes,
             unsolicited := m.unsolicited || m.acked < m.headBytes }
  | .endOfInput => { m with readOutstanding := false, eofSeen := true }
  | .readFailed _ => { m with readOutstanding := false }
  | .abandon => { m with abandoned := true }
  | .pulled c => if m.pullOutstanding then { m.take c with pullOutstanding := false } else m
  | .pullFailed _ =>
    if m.pullOutstanding then { m with pullOutstanding := false, bodyBroken := true } else m
  | .wantBody _ | .tick | .cancel _ => m

/-- A comparable summary of the core's state, for "a stale tick changes nothing". -/
def fingerprint (ex : Exchange) : String :=
  let p := ex.parser
  s!"{reprStr ex.phase}|now={ex.now}|w={ex.written}|wf={ex.writeInFlight}|wb={ex.writeBy}|" ++
  s!"us={ex.uploadStopped}|sa={ex.sentAny}|rf={ex.readInFlight}|rb={ex.readBy}|ie={ex.inputEnded}|" ++
  s!"h={ex.head.map (·.status.toCode)}|e={ex.early}|c={ex.credit}|held={ex.held.map (·.size)}|" ++
  s!"ab={ex.abandoned}|d={ex.drained}|db={ex.drainBy}|" ++
  s!"seg={ex.segStart}+{ex.request.size}|co={ex.complete}|tk={ex.taken}|pl={ex.pulling}|" ++
  s!"pp={reprStr p.phase}|ph={p.head.map (·.code)}|pd={p.delivered}|px={p.extra}|pe={p.inputEnded}"

/-- A short rendering of an action, for traces and reports. -/
def renderAction : ExchangeAction → String
  | .write bytes => s!"write {bytes.size}"
  | .read _ => "read"
  | .pull => "pull"
  | .deliverHead head => s!"head {head.status.toCode}"
  | .deliverBody bytes => s!"body {repr (String.fromUTF8? bytes |>.getD s!"<{bytes.size} bytes>")}"
  | .finish reusable => s!"finish reusable={reusable}"
  | .fail f =>
    let detail := if f.detail.isEmpty then "" else s!" ({f.detail})"
    let status := match f.status with
      | some s => s!", status={s.toCode}"
      | none => ""
    s!"fail {f.cause.describe}{detail} [{f.delivery.name}, written={f.written}{status}]"

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
  | .pulled (some b) => s!"pulled {b.size}"
  | .pulled none => "pulled end"
  | .pullFailed d => s!"pullFailed {repr d}"
  | .cancel r => s!"cancel {r}"

/--
Checks one step: the core was in `pre`, the environment reported `event` at time `now`, and the core
went to `post` with `actions`.  Returns the updated model and the first violation, if any.  The
properties named in `skip` are not checked (for showing, in a positive control, that another
property catches a planted bug on its own).
-/
def checkStep (oracle : Oracle) (m : Model) (pre : Exchange) (now : Nat) (event : ExchangeEvent)
    (post : Exchange) (actions : Array ExchangeAction) (skip : List String := []) :
    Model × Option Violation := Id.run do
  let wasEnded := m.ended
  let before := m
  let mut m := { m.observe event with now := max m.now now }
  let mut found : Option Violation := none
  -- Records the first violation: `broken` is true when property `p` does not hold.
  let flag (found : Option Violation) (p : String) (broken : Bool) (detail : Unit → String) :
      Option Violation :=
    if found.isNone && broken && !skip.contains p then some { property := p, detail := detail () }
    else found
  found := flag found "nothing after the end" (wasEnded && !actions.isEmpty)
    fun _ => s!"{actions.map renderAction}"
  for action in actions do
    found := flag found "one end, last" m.ended fun _ => s!"{renderAction action} after the end"
    match action with
    | .write bytes =>
      found := flag found "one write in flight" m.outstanding.isSome
        fun _ => s!"write {bytes.size} while {m.outstanding} in flight"
      found := flag found "writes follow the request"
        (bytes.isEmpty || bytes != m.request.extract m.acked (m.acked + bytes.size))
        fun _ => s!"write {bytes.size} at {m.acked}"
      m := { m with outstanding := some bytes.size, everWrote := true }
    | .pull =>
      found := flag found "one pull in flight" m.pullOutstanding fun _ => "pull while a pull is in flight"
      found := flag found "no pull before the request head is written"
        (!m.everWrote || m.acked < m.headBytes)
        fun _ => s!"pull with {m.acked} of {m.headBytes} head bytes written, wrote={m.everWrote}"
      found := flag found "pull only when the request so far is written"
        (m.acked != m.request.size || m.outstanding.isSome || m.complete)
        fun _ => s!"pull at {m.acked} of {m.request.size}, write in flight {m.outstanding}, complete={m.complete}"
      m := { m with pullOutstanding := true, everPulled := true }
    | .read _ =>
      found := flag found "one read in flight" m.readOutstanding
        fun _ => "read while a read is in flight"
      found := flag found "no read before the request head is written" (m.acked < m.headBytes)
        fun _ => s!"read with {m.acked} of {m.headBytes} head bytes written"
      m := { m with readOutstanding := true }
    | .deliverHead head =>
      found := flag found "one head" m.headDelivered fun _ => s!"second head {head.status.toCode}"
      found := flag found "no head before the request head is written" (m.acked < m.headBytes)
        fun _ => s!"head {head.status.toCode} with {m.acked} of {m.headBytes} head bytes written"
      found := flag found "unsolicited bytes never make a response" m.unsolicited
        fun _ => s!"head {head.status.toCode}"
      m := { m with headDelivered := true, ackedAtHead := m.acked,
                    headStatus := some head.status.toCode.toNat }
    | .deliverBody bytes =>
      found := flag found "no body before the head" (!m.headDelivered) fun _ => s!"{bytes.size} bytes"
      m := { m with body := m.body ++ bytes }
      if let some whole := oracle.body then
        found := flag found "the body is the response's" (!(m.body.isPrefixOf whole))
          fun _ => s!"{m.body.size} bytes delivered, not a prefix"
    | .finish reusable =>
      m := { m with ended := true }
      if !m.abandoned then
        match oracle.bodyFor m.fed with
        | none =>
          found := flag found "finish only after a complete response" true
            fun _ => s!"finish after {m.fed.size} bytes {repr (String.fromUTF8? m.fed |>.getD "")}"
        | some expected =>
          found := flag found "finish only after a complete response"
            (oracle.needsEnd && !m.eofSeen) fun _ => "a close-delimited body before the end"
          found := flag found "a finished response delivered its whole body"
            (m.body != expected || !m.headDelivered)
            fun _ => s!"{m.body.size} body bytes, expected {expected.size}"
      if reusable then
        let reasons := [
          (m.keepAlive, "keep-alive is off"),
          (m.wireDone, "the streamed body was not known in full"),
          (m.acked == m.request.size, s!"only {m.acked} of {m.request.size} request bytes written"),
          (m.ackedAtHead == m.request.size, s!"the head arrived after {m.ackedAtHead} bytes"),
          (!m.eofSeen, "the peer closed"),
          (oracle.exactReusable m.fed,
            s!"the {m.fed.size} bytes read are not exactly one reusable response"),
          (m.headDelivered, "no head")]
        if let some (_, why) := reasons.find? (!·.1) then
          found := flag found "reusable only when safe" true fun _ => why
    | .fail f =>
      m := { m with ended := true }
      let ok := match f.delivery with
        | .notSent => !m.everWrote
        | .maybeDelivered => m.everWrote && !m.headDelivered
        | .responseReceived => m.headDelivered
      found := flag found "delivery follows what was written" (!ok)
        fun _ => s!"{f.delivery.name}, wrote={m.everWrote}, head={m.headDelivered}"
      found := flag found "a failure counts the bytes written" (f.written != m.acked)
        fun _ => s!"{f.written}, model {m.acked}"
      found := flag found "a failure carries the status of the delivered head"
        (f.status.map (·.toCode.toNat) != m.headStatus)
        fun _ => s!"{f.status.map (·.toCode)}, model {m.headStatus}"
      found := flag found "a failure that says not sent pulled nothing"
        (f.delivery == .notSent && m.everPulled) fun _ => "a pull was issued"
  -- Properties of the state after the step.
  -- While an abandoned body is drained, nobody waits for an error: the exchange finishes instead,
  -- with a connection that is not reusable.
  found := flag found "a broken streamed body fails the exchange"
    (!before.bodyBroken && m.bodyBroken && !wasEnded &&
      !(actions.any fun a => match a with
        | .fail f => (match f.cause with | .requestBody _ => true | _ => false)
        | .finish false => (match pre.phase with | .draining => true | _ => false)
        | _ => false))
    fun _ => s!"{actions.map renderAction}"
  if let some (.length size) := m.framing then
    found := flag found "the body written stays within its declared size" (m.acked > m.start + size)
      fun _ => s!"{m.acked} request bytes written, {m.start} of head and {size} of body declared"
  -- A cancel ends the exchange in its step, with that end alone: a failure that says the call was
  -- cancelled, or, while an abandoned body is drained, a finish whose connection is not reusable.
  if let .cancel reason := event then
    found := flag found "a cancel ends the exchange at once"
      (!wasEnded && !(match actions.toList with
        | [.fail f] =>
          (match f.cause with | .cancelled r => r == reason | _ => false) &&
            !(match pre.phase with | .draining => true | _ => false)
        | [.finish false] => (match pre.phase with | .draining => true | _ => false)
        | _ => false))
      fun _ => s!"{actions.map renderAction}"
  found := flag found "the core ends only with an action" (post.terminal != m.ended)
    fun _ => s!"terminal={post.terminal}, ended={m.ended}"
  found := flag found "after the deadline the exchange has ended"
    (m.now ≥ m.deadline && !post.terminal) fun _ => s!"now={m.now}, deadline={m.deadline}"
  found := flag found "unsolicited bytes fail the exchange"
    (!wasEnded && (match event with | .received b => !b.isEmpty | _ => false) &&
      before.acked < before.headBytes &&
      !(actions.any fun | .fail _ => true | _ => false))
    fun _ => s!"{actions.map renderAction}"
  if let .received bytes := event then
    if bytes.isEmpty then
      let (asTick, tickActions) := pre.step now .tick
      found := flag found "an empty read is a tick"
        (fingerprint post != fingerprint asTick ||
          actions.map renderAction != tickActions.map renderAction)
        fun _ => s!"empty read at {now}: {actions.map renderAction}, a tick: {tickActions.map renderAction}"
  if let (.tick, some due) := (event, pre.nextDeadline) then
    found := flag found "a stale tick changes nothing"
      (now < due && (!actions.isEmpty || fingerprint post != fingerprint pre))
      fun _ => s!"tick at {now}, due {due}"
  -- Every deadline that has passed was acted on: what is left is in the future, and no later than
  -- the exchange's own deadline.
  if !post.terminal then
    found := flag found "a live exchange has a deadline ahead"
      (match post.nextDeadline with | none => true | some d => d ≤ m.now || d > post.deadline)
      fun _ => s!"next deadline {post.nextDeadline} at {m.now}, deadline {post.deadline}"
  return (m, found)
