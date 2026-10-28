import LeanHttp.Exchange
import Tests.Support.Check
import Tests.Support.MachineCore

/-!
# Fuzzing harness for the exchange core, with the vendored HTTP/1.1 machine as its oracle

`check` interprets fuzzer bytes as one exchange and checks invariants over it; `fuzzOne`, exported
to C as `lean_http_fuzz_one`, panics when one fails, so that under `LEAN_ABORT_ON_PANIC=1` a broken
invariant is a crash that AFL++ sees (and returns 1 if the panic did not abort, on which
`fuzz/afl-main.c` aborts).  `fuzz/afl-main.c` calls it once per input in AFL++'s persistent mode,
and `Fuzz/Replay.lean` runs the same check over files and prints what happened.

## Input format

- Byte 0 is the control byte.  Bits 0-1 choose the request method (GET, HEAD, POST, OPTIONS), bit 2
  reports end of input after the last byte, bit 3 feeds the response one byte at a time instead of
  by the split table, and bits 4-7 give the number `k` of split-table entries.
- Bytes 1 to `k` are the split table: the lengths of the first `k` reads, each 0 to 255 (0 is an
  empty read).  The rest of the response is the last read.
- The remaining bytes are the response, as the server sends it, up to `maxResponse` bytes (the
  rest is ignored).

## The two drivers

- **The exchange core** (`LeanHttp.Exchange`, which parses responses with `LeanHttp.Codec`),
  driven through `Exchange.begin` and `Exchange.step` as a shell would drive it: the request goes out in `writeChunk`-byte writes, each reported as
  completed in full; the caller asks for more body than any response has; each read the input
  dictates is reported as `received` while the core has a read in flight (an empty read is a tick),
  with one outstanding write completed after each; then end of input, if the input says so.  Time
  moves by 1 ms per event, far from every timer, so the outcome depends on the bytes alone.  A POST
  carries a request body, so that its response can arrive while the body is still going out.  The
  core runs with keep-alive on, the configuration a pooled client will use, and once more over the
  dictated reads with keep-alive off, the configuration the client uses now.
- **A direct driver of the vendored machine** with keep-alive on, started from the machine the former
  core's `prepare` encoded the request with (`Tests/Support/MachineCore.lean`).  It bounds every
  loop, records the events the machine emits, and ends with the machine's reuse decision.  It is the
  differential oracle for the core.

Both use the parser limits in `limits` (for the core, the same limits as a `Codec.Config`,
`coreLimits`): the defaults, lowered so that fuzzer inputs reach them.  Each driver runs over the
response in one read and in the reads the input dictates; the direct driver runs a third time over
the whole response with end of input flipped.

## Invariants of the machine and of the response

- The direct driver ends within a step bound linear in the input (the exchange core is made of
  total functions, so it cannot loop; a hang there would be slowness, which AFL++ reports).
- The events form a well-formed sequence: interim heads, one final head, body data, the end of the
  body, then possibly the machine's reset for the next message; a failure ends the sequence.
- No body after HEAD, after a 1xx used as final, after 204 or after 304, and the end of the body
  follows such a head (and one with `Content-Length: 0`) at once.
- Body bytes never exceed a single valid `Content-Length`; a completed body with
  `Content-Length` matches it exactly, and a completed response never carries an invalid or
  conflicting `Content-Length`, or both `Content-Length` and `Transfer-Encoding`.  The exchange core
  completes a response with a body and a `Transfer-Encoding` only when that is exactly `chunked`
  (the machine also completes one with other codings before `chunked`, which the core refuses).
- Over the whole response, a completed `Content-Length` body is exactly the bytes before the ones
  left unread, and a completed close-delimited body is exactly the bytes after the head.
- A close-delimited body completes only after end of input, and is never reusable; a framed
  response completes, with the same body, whether or not end of input follows it.
- A connection the machine or the core would reuse ended a framed HTTP/1.1 response without `close`
  (or an HTTP/1.0 one with `keep-alive`), was not a `101`, and its peer has not closed.  The core
  reuses a connection only where the machine would, and over the whole response exactly where the
  machine would with no byte left over and the whole request written before the head arrived.
- Split invariance: both drivers produce the same events, body and outcome whether the response
  arrives whole or in pieces.  For a response that does not complete, the machine's body delivered
  so far may differ, and then each body must be a prefix of the other; the exchange core's may not
  (see `exchangeSplitInvariant`).  Keep-alive changes nothing in the core's outcome but the reuse
  verdict.
- For each way of feeding, the two drivers agree: the same completed response (status, body,
  interim count), a failure where the other failed or saw end of input too early, a pending
  response where the other is pending; except where the exchange core refuses by its own rules
  (interim count, body size, `101`, a transfer coding other than chunked), and then the refusal must
  be justified by what the machine saw, and except for the codec's deliberate differences from the
  machine (`NOTES.md`), each of which must be attributed: a chunk announced beyond the body limit,
  refused at its size line; a chunk-size line over its limit, or one extension too many, refused
  before the line is complete; and an HTTP/1.0 response saying both `keep-alive` and `close`, which
  the codec does not reuse.  A body-limit failure always comes after the head, with its status.

## Invariants of the exchange core's theorems

Every step of every run of the core is checked by `checkStep` of `Tests/Support/Check.lean`, the
executable checker's properties, each of which a theorem in `LeanHttp/Exchange/Proofs.lean` or
`Liveness.lean` states: nothing after the end (`step_of_terminal`), one end, last, and only with an
action (`step_ends`), one write in flight and writes that follow the request (`step_writes`,
`Run.inFlight`), one read in flight and none before the request head is written (`step_reads`), no
head before the request head is written and only one (`step_deliverHead`), no body before the head
(`step_chunk_after_head`), unsolicited bytes fail the exchange (`step_unsolicited`), delivery,
written count and status of a failure (`step_fail`, `observed_fail`), the core's side of reuse
(`step_finish_reusable`, `observed_finish_reusable`), after the deadline the exchange has ended
(`step_deadline`, `observed_deadline`), a stale tick and an empty read change nothing beyond a tick
(`step_stale_tick`, `step_empty_received`), and a live exchange has a deadline ahead
(`Reachable.deadlineAhead`, `ObservedMono.deadlineAhead`).  The two properties about the response
bytes, which need the checker's hand-written knowledge of a response, are left to the invariants
above.  Besides, after every step:

- the checker's model agrees with the core (`Observed.agrees`);
- the timers' invariant holds (`Reachable.timers`), and a live exchange is before its deadline with
  every timer ahead (`Reachable.ahead`, `Reachable.beforeDeadline`);

and once per run:

- `begin` emits one write, a non-empty prefix of the request (`begin_write`, `begin_ends`);
- bytes reported before any write completed fail the exchange at once (`step_unsolicited`, on a
  separate run with the input's first non-empty read);
- an event at the deadline ends a live exchange (`Reachable.ended_at_deadline`);
- a shell that then only ticks at the next deadline can always do so (`Reachable.tick_due`), each
  tick ends the exchange or moves its clock forward (`Reachable.due_advances`), and the exchange
  ends within `deadline - now` ticks (`Reachable.ends_of_allDue`).

The theorems say these never fail; the fuzzer exercises them end to end.  The theorems that tie a
finished exchange to the bytes received (`observed_finish_codec`, `observed_finish_complete`) are
about the codec, so their properties are checked here against the machine instead, by the
cross-check above.
-/

open Std.Http LeanHttp LeanHttpProto.Http.Protocol

namespace LeanHttpFuzz

/-! ## Limits and settings -/

/--
The parser limits both drivers use: the defaults, lowered so that inputs of a few kilobytes reach
every one of them.
-/
def limits : H1.Config :=
  { maxHeaders := 16, maxHeaderBytes := 1024, maxStartLineLength := 256,
    maxHeaderNameLength := 64, maxHeaderValueLength := 512, maxReasonPhraseLength := 64,
    maxChunkLineLength := 128, maxChunkExtensions := 4, maxChunkExtNameLength := 32,
    maxChunkExtValueLength := 32, maxTrailerHeaders := 4 }

/-- `limits` for the response codec, with the interim and body limits below. -/
def coreLimits : Codec.Config :=
  { maxHeaders := limits.maxHeaders, maxHeaderBytes := limits.maxHeaderBytes,
    maxHeaderNameLength := limits.maxHeaderNameLength,
    maxHeaderValueLength := limits.maxHeaderValueLength, maxSpaceSequence := limits.maxSpaceSequence,
    maxReasonPhraseLength := limits.maxReasonPhraseLength,
    maxChunkExtensions := limits.maxChunkExtensions,
    maxChunkExtNameLength := limits.maxChunkExtNameLength,
    maxChunkExtValueLength := limits.maxChunkExtValueLength,
    maxChunkLineLength := limits.maxChunkLineLength, maxTrailerHeaders := limits.maxTrailerHeaders,
    maxInterim := 10, maxBody := 1024 }

/-- The exchange core's limit on interim responses, small enough for fuzzer inputs to reach. -/
def maxInterim : Nat := 10

/-- The exchange core's body limit, small enough for fuzzer inputs to reach. -/
def maxBody : Nat := 1024

/--
The longest response the harness feeds: the machine's input buffer limit (the body limit plus the
header allowances).  A longer response would fail in the machine when fed whole but not in small
reads, and that limit is about the reads, not the response.
-/
def maxResponse : Nat :=
  maxBody + limits.maxHeaderBytes + limits.maxStartLineLength + limits.maxChunkLineLength

/-- The deadline of every exchange, which begins at time 0. -/
def deadline : Nat := 20000

/--
The core's settings.  The request goes out in 16-byte writes, so in several; the read gap (10 s) is
longer than any run takes at 1 ms per event, and shorter than the deadline.
-/
def exchangeConfig (keepAlive : Bool) : ExchangeConfig :=
  { limits := coreLimits, keepAlive, maxInterim, maxBody, writeChunk := 16, gapMs := 10000 }

/-- The machine core's settings, as the core's, for encoding the request the direct driver starts
from. -/
def machineConfig (keepAlive : Bool) : MachineCore.ExchangeConfig :=
  { h1 := limits, keepAlive, maxInterim, maxBody, writeChunk := 16, gapMs := 10000 }

/-- The body of a POST request: long enough to be still going out when the response arrives. -/
def postBody : ByteArray := "a request body still being written".toUTF8

/-- The request every input answers. -/
def requestHead (method : Method) : Request.Head :=
  { method, version := .v11, uri := .originForm { segments := #[], absolute := true } none,
    headers := Headers.empty.insert Header.Name.host (.mk "example.test") }

/-- The request, prepared by the core. -/
def prepared (method : Method) (keepAlive : Bool) : PreparedRequest :=
  let body := if method == .post then postBody else .empty
  Exchange.prepare (exchangeConfig keepAlive) (requestHead method) body

/--
The machine after encoding the same request (with keep-alive on), for the direct driver; `none` if
the machine refused it, or encoded it differently from the core, which the harness reports.
-/
def machineFor? (method : Method) : Option (H1.Machine .sending) :=
  let body := if method == .post then postBody else .empty
  match MachineCore.Exchange.prepare (machineConfig true) (requestHead method) body with
  | .ok p => if p.bytes.data == (prepared method true).bytes.data then some p.machine else none
  | .error _ => none

/-! ## Decoding the input -/

/-- The decoded fuzz input. -/
structure Input where
  /-- The request method. -/
  method : Method
  /-- Whether end of input follows the last byte. -/
  eof : Bool
  /-- Whether the response is fed one byte at a time. -/
  bytewise : Bool
  /-- The lengths of the first reads. -/
  splits : Array Nat
  /-- The response bytes. -/
  response : ByteArray

/-- Decodes fuzzer bytes; every byte string is a valid input. -/
def decode (data : ByteArray) : Input :=
  if h : 0 < data.size then
    let ctrl := data[0].toNat
    let method : Method :=
      match ctrl % 4 with
      | 0 => .get
      | 1 => .head
      | 2 => .post
      | _ => .options
    let k := min (ctrl / 16) (data.size - 1)
    let splits := (List.range k).toArray.map fun i => data[i + 1]!.toNat
    { method, eof := (ctrl / 4) % 2 == 1, bytewise := (ctrl / 8) % 2 == 1, splits,
      response := data.extract (k + 1) (min data.size (k + 1 + maxResponse)) }
  else
    { method := .get, eof := true, bytewise := false, splits := #[], response := .empty }

/-- The reads the input dictates. -/
def pieces (inp : Input) : List ByteArray :=
  let r := inp.response
  if inp.bytewise then
    (List.range r.size).map fun i => r.extract i (i + 1)
  else
    let (acc, pos) := inp.splits.foldl (init := (#[], 0)) fun (acc, pos) len =>
      let stop := min (pos + len) r.size
      (acc.push (r.extract pos stop), stop)
    (acc.push (r.extract pos r.size)).toList

/-! ## What the head declares, read independently of the machine -/

/-- The ASCII lowercase form of a string. -/
def lower (s : String) : String := s.map Char.toLower

/-- The comma-separated tokens of all values of a header field, trimmed and lowercased. -/
def tokens (head : Response.Head) (name : Header.Name) : List String :=
  match head.headers.getAll? name with
  | none => []
  | some values =>
    values.toList.flatMap fun v =>
      (v.value.splitOn ",").map fun t => lower (t.trimAscii.toString)

/-- A decimal digit string, parsed without `String.toNat?` (which may accept separators). -/
def decimal? (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.foldl (init := some 0) fun acc c =>
    match acc with
    | some n => if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none
    | none => none

/-- The values of the `Content-Length` fields, if any. -/
def contentLengths (head : Response.Head) : Array String :=
  (head.headers.getAll? Header.Name.contentLength).getD #[] |>.map (·.value)

/-- Whether the head has a `Transfer-Encoding` field. -/
def hasTransferEncoding (head : Response.Head) : Bool :=
  head.headers.contains Header.Name.transferEncoding

/-- Whether the head's transfer codings are exactly `chunked`. -/
def onlyChunked (head : Response.Head) : Bool :=
  tokens head Header.Name.transferEncoding == ["chunked"]

/-- Whether the response to `method` with this head carries no body, whatever its framing fields. -/
def noBody (method : Method) (head : Response.Head) : Bool :=
  let code := head.status.toCode.toNat
  method == .head || (100 ≤ code && code < 200) || code == 204 || code == 304

/-- The single valid `Content-Length`, if the head has exactly one. -/
def singleLength? (head : Response.Head) : Option Nat :=
  match contentLengths head with
  | #[v] => decimal? v
  | _ => none

/-- Whether the body of this response ends only when the connection closes. -/
def closeDelimited (method : Method) (head : Response.Head) : Bool :=
  !noBody method head && !hasTransferEncoding head && (contentLengths head).isEmpty

/-- Whether the head says at once that the body is empty. -/
def emptyAtOnce (method : Method) (head : Response.Head) : Bool :=
  noBody method head || (!hasTransferEncoding head && singleLength? head == some 0)

/-- A short, comparable rendering of a body: its size and a hash of its bytes. -/
def showBody (b : ByteArray) : String :=
  s!"{b.size}B#{hash b.data}"

/-! ## Invariants on one response -/

/-- Fails with `msg` unless `cond`. -/
def ensure (cond : Bool) (msg : String) : Except String Unit :=
  if cond then pure () else throw msg

/--
The body invariants for one final head and the body delivered for it.  `done` says whether the
driver considered the response complete, `eof` whether end of input was reported before.  With
`strict`, a completed body with a `Transfer-Encoding` must have exactly `chunked` (the exchange
core's rule); otherwise its last coding must be `chunked` (the machine's).
-/
def checkBody (who : String) (method : Method) (head : Response.Head) (body : ByteArray)
    (done eof : Bool) (strict : Bool := false) : Except String Unit := do
  let code := head.status.toCode.toNat
  if noBody method head then
    ensure (body.size == 0) s!"{who}: {body.size} body bytes for a bodyless response ({code}, {repr method})"
  else
    let lengths := contentLengths head
    if let some n := singleLength? head then
      ensure (body.size ≤ n) s!"{who}: {body.size} body bytes exceed Content-Length {n}"
    if done then
      if hasTransferEncoding head then
        ensure lengths.isEmpty s!"{who}: completed with both Transfer-Encoding and Content-Length"
        ensure (head.version == .v11) s!"{who}: completed a Transfer-Encoding response to HTTP/1.0"
        ensure ((tokens head Header.Name.transferEncoding).getLast? == some "chunked")
          s!"{who}: completed with Transfer-Encoding whose last coding is not chunked"
        if strict then
          ensure (onlyChunked head)
            s!"{who}: completed with transfer codings {tokens head Header.Name.transferEncoding}, not just chunked"
      else if lengths.isEmpty then
        ensure eof s!"{who}: completed a close-delimited body without end of input"
      else
        match singleLength? head with
        | some n => ensure (body.size == n) s!"{who}: completed with {body.size} body bytes, Content-Length {n}"
        | none => throw s!"{who}: completed despite Content-Length {repr lengths}"

/--
The reuse invariants for a response that a driver would reuse the connection after: a framed
response that allows it, not a `101`.
-/
def checkReusable (who : String) (method : Method) (head : Response.Head) : Except String Unit := do
  ensure (head.status.toCode != 101) s!"{who}: reusable after 101"
  ensure (!closeDelimited method head) s!"{who}: reusable after a close-delimited body"
  let conn := tokens head Header.Name.connection
  if head.version == .v11 then
    ensure (!conn.contains "close") s!"{who}: reusable despite Connection: close"
  else
    ensure (conn.contains "keep-alive") s!"{who}: reusable HTTP/1.0 response without keep-alive"

/-! ## Driver 1: the exchange core -/

/-- What the checker knows of the response: nothing (the response invariants are the harness's). -/
def oracle : Oracle := { exactReusable := fun _ => true }

/--
The checker's properties that compare the outcome with the checker's own knowledge of the response,
which a fuzzed response does not come with; the harness's invariants about the response cover them.
-/
def unchecked : List String :=
  ["finish only after a complete response", "a finished response delivered its whole body"]

/-- A run of the exchange core, with everything its actions delivered. -/
structure Core where
  /-- The request. -/
  prepared : PreparedRequest
  /-- The exchange. -/
  ex : Exchange
  /-- The checker's model of the run. -/
  model : Model
  /-- The time of the latest event. -/
  time : Nat := 0
  /-- The final head, once delivered. -/
  head : Option Response.Head := none
  /-- The body delivered. -/
  body : ByteArray := .empty
  /-- The `finish` or `fail` action, once emitted. -/
  ended : Option ExchangeAction := none
  /-- The first broken invariant. -/
  problem : Option String := none

instance : Inhabited Core :=
  ⟨{ prepared := default, ex := default, model := Model.init default 0 0 }⟩

/-- Records a broken invariant, unless one was recorded already. -/
def Core.flag (c : Core) (problem : Option String) : Core :=
  if c.problem.isSome then c else { c with problem }

/-- Records what one action delivered. -/
def Core.record (c : Core) : ExchangeAction → Core
  | .deliverHead head => { c with head := some head }
  | .deliverBody bytes => { c with body := c.body ++ bytes }
  | a@(.finish _) | a@(.fail _) => { c with ended := some a }
  | _ => c

/--
The invariants of the core's state after every step, against the checker's model: the model agrees
with the core (`Observed.agrees`), the timers' invariant (`Reachable.timers`), and for a live
exchange, its clock before the deadline and every timer ahead (`Reachable.ahead`).
-/
def stateProblem (ex : Exchange) (m : Model) : Option String :=
  let draining := match ex.phase with | .draining => true | _ => false
  let checks : List (Bool × (Unit → String)) := [
    (m.acked == ex.written, fun _ => s!"model and core disagree: written {m.acked} vs {ex.written}"),
    (m.outstanding == ex.writeInFlight,
      fun _ => s!"model and core disagree: write in flight {m.outstanding} vs {ex.writeInFlight}"),
    (m.everWrote == ex.sentAny, fun _ => s!"model and core disagree: wrote {m.everWrote} vs {ex.sentAny}"),
    (m.headDelivered == ex.head.isSome,
      fun _ => s!"model and core disagree: head {m.headDelivered} vs {ex.head.isSome}"),
    (m.ended == ex.terminal, fun _ => s!"model and core disagree: ended {m.ended} vs {ex.terminal}"),
    (!m.headDelivered ||
        (ex.early == decide (m.ackedAtHead < ex.request.size) && m.ackedAtHead ≤ ex.request.size),
      fun _ => s!"model and core disagree: early {ex.early}, head after {m.ackedAtHead} of {ex.request.size}"),
    (m.eofSeen == ex.inputEnded,
      fun _ => s!"model and core disagree: end of input {m.eofSeen} vs {ex.inputEnded}"),
    (ex.writeBy.isNone || ex.writeInFlight.isSome, fun _ => "timers: a write deadline, no write in flight"),
    (ex.writeInFlight.all (· > 0), fun _ => "timers: an empty write in flight"),
    (ex.drainBy.isNone || draining, fun _ => "timers: a drain deadline while not draining"),
    (!draining || (ex.written == ex.request.size && ex.writeInFlight.isNone && ex.head.isSome),
      fun _ => "timers: draining before the request was written or the head delivered"),
    (ex.terminal ||
        (ex.now < ex.deadline && [ex.writeBy, ex.readBy, ex.drainBy].all (·.all (· > ex.now))),
      fun _ => s!"a live exchange with a deadline behind it: now {ex.now}, deadline {ex.deadline}, " ++
        s!"write {ex.writeBy}, read {ex.readBy}, drain {ex.drainBy}")]
  (checks.find? (!·.1)).map (·.2 ())

/-- Applies one event at time `now`, and checks the step. -/
def Core.stepAt (c : Core) (now : Nat) (event : ExchangeEvent) : Core :=
  let pre := c.ex
  let (post, actions) := pre.step now event
  let (model, v) := checkStep oracle c.model pre now event post actions unchecked
  let c := { c with ex := post, model, time := max c.time now }
  let c := actions.foldl Core.record c
  let c := c.flag (v.map fun v => s!"{v.property}: {v.detail} (after {renderEvent event} at {now})")
  c.flag (stateProblem post model)

/-- Applies one event 1 ms after the latest. -/
def Core.next (c : Core) (event : ExchangeEvent) : Core :=
  c.stepAt (c.time + 1) event

/--
Begins `prepared`, and checks that `begin` emits one write, a non-empty prefix of the request, and
does not end the exchange (`begin_write`, `begin_ends`).
-/
def Core.begin (prepared : PreparedRequest) : Core :=
  let (ex, actions) := Exchange.begin prepared 0 deadline
  let model := Model.init prepared deadline 0
  let c : Core := actions.foldl Core.record { prepared, ex, model }
  match actions.toList with
  | [.write bytes] =>
    let ok := bytes.size > 0 && bytes == model.request.extract 0 bytes.size && !ex.terminal
    let model := { model with outstanding := some bytes.size, everWrote := true }
    let c := { c with model }
    let c := c.flag (if ok then none else some s!"begin: write {bytes.size} is not a prefix of the request")
    c.flag (stateProblem ex model)
  | other => c.flag (some s!"begin: expected one write, got {other.map renderAction}")

/-- Completes the write in flight, if there is one. -/
def Core.completeWrite (c : Core) : Core :=
  match c.model.outstanding with
  | some len => if c.ex.terminal then c else c.next (.written len)
  | none => c

/-- Completes writes until a read is in flight or no write is (at most `fuel` of them). -/
def Core.writeUntilRead (c : Core) : Nat → Core
  | 0 => c
  | fuel + 1 =>
    if c.model.readOutstanding || c.model.outstanding.isNone || c.ex.terminal then c
    else c.completeWrite.writeUntilRead fuel

/--
Runs the exchange core over `reads`, as a shell would: see the module comment.  Stops at end of
input; `waitOut` checks what a shell that only waits sees afterwards.
-/
def runCore (prepared : PreparedRequest) (eof : Bool) (reads : List ByteArray) : Core := Id.run do
  let fuel := prepared.bytes.size + 1
  let mut c := (Core.begin prepared).writeUntilRead fuel
  c := c.next (.wantBody (maxBody + maxResponse))
  -- A stale tick, which must change nothing.
  c := c.stepAt c.time .tick
  for piece in reads do
    if !c.ex.terminal && !c.model.readOutstanding then
      c := c.flag (some "no read in flight while the response is awaited")
    c := c.next (.received piece)
    c := c.completeWrite
  c := c.writeUntilRead fuel
  -- Writes that remain once the reads are over (at most the request's slices).
  for _ in [0:fuel] do
    c := c.completeWrite
  if eof then c := c.next .endOfInput
  return c

/--
What a shell that only waits sees after the reads: an event at the deadline ends a live exchange
(`Reachable.ended_at_deadline`); ticking at each next deadline, the shell can always tick
(`Reachable.tick_due`), each tick ends the exchange or moves its clock forward
(`Reachable.due_advances`), and the exchange ends within `deadline - now` ticks
(`Reachable.ends_of_allDue`).  Returns the first broken invariant.
-/
def waitOut (c : Core) : Option String := Id.run do
  if c.ex.terminal then return none
  if !(c.ex.step deadline .tick).1.terminal then
    return some "a tick at the deadline left the exchange live"
  let mut c := c
  for _ in [0:deadline - c.ex.now] do
    if c.ex.terminal then return c.problem
    match c.ex.nextDeadline with
    | none => return some "a live exchange has no next deadline"
    | some due =>
      if !(c.ex.now < due && due ≤ deadline) then
        return some s!"cannot wait: next deadline {due}, clock {c.ex.now}, deadline {deadline}"
      let before := c.ex.now
      c := c.stepAt due .tick
      if c.problem.isSome then return c.problem
      if !c.ex.terminal && c.ex.now ≤ before then
        return some s!"a due tick at {due} did not move the clock from {before}"
  if c.ex.terminal then c.problem else some "still live after deadline - now due ticks"

/--
Bytes reported before any write completed fail the exchange at once (`step_unsolicited`): begins
`prepared` and reports `bytes`, if there are any.
-/
def unsolicited (prepared : PreparedRequest) (bytes : ByteArray) : Option String :=
  if bytes.isEmpty then none
  else
    let c := (Core.begin prepared).next (.received bytes)
    match c.problem, c.ended with
    | some p, _ => some p
    | none, some (.fail _) => none
    | none, _ => some "bytes before the request head was written did not fail the exchange"

/-- How a run of the core ended, without the reuse verdict. -/
def Core.render (c : Core) (withBody : Bool := true) : String :=
  match c.ended, c.head with
  | some (.finish _), some head =>
    s!"done {head.status.toCode} interim={c.ex.interim} body={showBody c.body}"
  | some (.finish _), none => "finished without a head"
  | some (.fail f), _ => s!"failed {repr f.cause} interim={c.ex.interim} head={c.head.isSome}"
  | _, _ => s!"pending interim={c.ex.interim}" ++ (if withBody then s!" body={c.body.size}" else "")

/-- The reuse verdict, once the core finished. -/
def Core.reusable? (c : Core) : Option Bool :=
  match c.ended with
  | some (.finish r) => some r
  | _ => none

/-- The failure, once the core failed. -/
def Core.failure? (c : Core) : Option Failure :=
  match c.ended with
  | some (.fail f) => some f
  | _ => none

/-! ## Driver 2: the machine, directly, with keep-alive on -/

/-- What the direct driver records. -/
inductive Ev where
  /-- A head was parsed: its status code, and whether it is the final response. -/
  | head (code : Nat) (final : Bool)
  /-- Body bytes were pulled. -/
  | data (n : Nat)
  /-- The machine reported the end of the body. -/
  | endBody
  /-- The machine failed. -/
  | failed (err : String)
  /-- The machine closed the connection. -/
  | close
  /-- The machine reset for the next message (keep-alive). -/
  | next
deriving BEq, Repr

/-- The state of the direct driver. -/
structure Run where
  /-- The machine. -/
  machine : H1.Machine .sending
  /-- The events so far. -/
  trace : Array Ev := #[]
  /-- The body bytes of the final response. -/
  body : ByteArray := .empty
  /-- The final head, once parsed. -/
  finalHead : Option Response.Head := none
  /-- Interim heads seen. -/
  interim : Nat := 0
  /-- Whether a step bound was exhausted. -/
  outOfFuel : Bool := false
  /-- Whether end of input was reported. -/
  eof : Bool := false

instance : Inhabited Run := ⟨{ machine := { config := {} } }⟩

/-- Handles one event; returns whether it is progress the loop must act on. -/
def Run.handle (r : Run) : H1.Event .sending → Run × Bool
  | .endHeaders head =>
    let head : Response.Head := head
    let final := !head.status.isInterim
    let r := { r with trace := r.trace.push (.head head.status.toCode.toNat final) }
    if final then ({ r with finalHead := some head }, true)
    else ({ r with interim := r.interim + 1 }, true)
  | .closeBody => ({ r with trace := r.trace.push .endBody }, true)
  | .failed err => ({ r with trace := r.trace.push (.failed (toString err)) }, true)
  | .close => ({ r with trace := r.trace.push .close }, false)
  | .next => ({ r with trace := r.trace.push .next }, false)
  | .needMoreData _ | .needAnswer | .continue => (r, false)

/-- Handles a batch of events. -/
def Run.handleAll (r : Run) (events : Array (H1.Event .sending)) : Run × Bool :=
  events.foldl (init := (r, false)) fun (r, p) e =>
    let (r, q) := r.handle e
    (r, p || q)

/-- Pulls body chunks while the machine offers them, at most `fuel` times. -/
def Run.pullAll (r : Run) (progressed : Bool) : Nat → Run × Bool
  | 0 => (if r.machine.canPullBodyNow then { r with outOfFuel := true } else r, progressed)
  | fuel + 1 =>
    if !r.machine.canPullBodyNow then (r, progressed)
    else
      let (machine, chunk?) := r.machine.pullBody
      let r := { r with machine }
      match chunk? with
      | some pulled =>
        let data := pulled.chunk.data
        let r := if data.size == 0 then r
          else { r with trace := r.trace.push (.data data.size), body := r.body ++ data }
        r.pullAll true fuel
      | none => (r, progressed)

/-- The step bound for one drive: linear in the bytes the machine holds. -/
def Run.budget (r : Run) : Nat :=
  4 * r.machine.reader.input.remainingBytes + 16

/-- Runs the machine until it makes no more progress, at most `fuel` rounds. -/
def Run.drive (r : Run) : Nat → Run
  | 0 => { r with outOfFuel := true }
  | fuel + 1 =>
    let pullFuel := r.machine.reader.input.remainingBytes + 4
    let (machine, result) := r.machine.step
    let (r, p₁) := { r with machine }.handleAll result.events
    let (r, p₂) := r.pullAll false pullFuel
    let (machine, events) := r.machine.takeEvents
    let (r, p₃) := { r with machine }.handleAll events
    if r.outOfFuel then r
    else if p₁ || p₂ || p₃ then r.drive fuel
    else r

/--
Runs the direct driver over `reads`, from `machine`, which encoded the request, then reports end of
input if `eof`.
-/
def runMachine (machine : H1.Machine .sending) (eof : Bool) (reads : List ByteArray) : Run :=
  let r : Run := { machine }
  let r := reads.foldl (init := r) fun r data =>
    if r.outOfFuel then r
    else
      let r := { r with machine := r.machine.feed data }
      r.drive r.budget
  if eof && !r.outOfFuel then
    let r := { r with machine := r.machine.noMoreInput, eof := true }
    r.drive r.budget
  else r

/-- Merges adjacent body data in a trace, so that traces of differently split reads compare. -/
def normalise (trace : Array Ev) : Array Ev :=
  trace.foldl (init := #[]) fun acc e =>
    match e, acc.back? with
    | .data n, some (.data m) => acc.pop.push (.data (m + n))
    | _, _ => acc.push e

/-- Where the event sequence stands. -/
inductive Phase where
  | awaitHead | inBody | ended | reset | failed
deriving BEq, Repr

/-- Checks that a trace is a well-formed event sequence; returns where it ended. -/
def wellFormed (trace : Array Ev) : Except String Phase := do
  let mut phase := Phase.awaitHead
  let mut closes := 0
  for e in trace do
    match e, phase with
    | .head _ false, .awaitHead => pure ()
    | .head _ true, .awaitHead => phase := .inBody
    | .data _, .inBody => pure ()
    | .endBody, .inBody => phase := .ended
    | .next, .ended => phase := .reset
    | .failed _, .awaitHead | .failed _, .inBody => phase := .failed
    | .close, _ =>
      closes := closes + 1
      if closes > 1 then throw s!"two close events in {repr trace}"
    | e, p => throw s!"event {repr e} in phase {repr p}: {repr trace}"
  return phase

/-- Whether the final response completed. -/
def Run.completed (r : Run) : Bool :=
  r.trace.contains .endBody

/-- Whether the machine failed. -/
def Run.failedRun (r : Run) : Bool :=
  r.trace.any (· matches .failed _)

/--
Whether the connection could carry another request: the machine kept keep-alive on, the final
response completed without a failure, and the peer has not closed its side.  The machine's
`keepAlive` stays on after end of input, so a pool must check end of input as well, and also that no
bytes are left over (`renderRun` shows them).
-/
def reusable (r : Run) : Bool :=
  r.machine.keepAlive && r.machine.needsInput && !r.machine.failed && r.finalHead.isSome &&
    r.completed && !r.failedRun

/--
Whether the machine would reuse the connection had the peer not closed: `reusable`, but end of input
reported after the response is allowed for (the machine then needs no more input).  The exchange core
finishes before it hears of end of input after a framed response, and is compared with this.
-/
def reusableBeforeEnd (r : Run) : Bool :=
  r.machine.keepAlive && (r.machine.needsInput || r.eof) && !r.machine.failed &&
    r.finalHead.isSome && r.completed && !r.failedRun

/-- A comparable rendering of the direct driver's result. -/
def renderRun (r : Run) : String :=
  let reuse := reusable r
  -- Bytes left after a reusable response; after a failure or a close the machine ignores later
  -- reads, so the count depends on the split and is not compared.
  let leftover := if reuse then s!" leftover={r.machine.reader.input.remainingBytes}" else ""
  s!"{repr (normalise r.trace)} body={showBody r.body} reuse={reuse}{leftover}"

/-- The invariants of one run of the direct driver. -/
def checkRun (who : String) (method : Method) (r : Run) : Except String Unit := do
  ensure (!r.outOfFuel) s!"{who}: no termination within the step bound: {repr r.trace}"
  let phase ← wellFormed r.trace
  let done := phase == .ended || phase == .reset
  if let some head := r.finalHead then
    checkBody who method head r.body done r.eof
    if emptyAtOnce method head then
      -- The end of the body follows the final head at once (a close event may come between).
      let after := (r.trace.toList.dropWhile (!· matches .head _ true)).drop 1
      ensure ((after.filter (· != .close)).head? == some .endBody)
        s!"{who}: no end of body straight after a head that announces none: {repr r.trace}"
    if reusable r then
      ensure (phase == .reset) s!"{who}: reusable, but the machine did not reset"
      checkReusable who method head
  else
    ensure (r.body.size == 0) s!"{who}: body bytes without a final head"

/--
Checks a completed body against the response bytes, for a run that got the whole response in one
read (so the machine's unread bytes are the end of the response).
-/
def checkBodyBytes (method : Method) (response : ByteArray) (r : Run) : Except String Unit := do
  let some head := r.finalHead | return
  if !r.completed || noBody method head || hasTransferEncoding head then return
  let rest := r.machine.reader.input.remainingBytes
  let stop := response.size - rest
  if closeDelimited method head then
    ensure (rest == 0) s!"machine/whole: {rest} bytes unread after a close-delimited body"
    ensure ((response.extract (response.size - r.body.size) response.size).data == r.body.data)
      s!"machine/whole: the close-delimited body is not the end of the response"
  else if let some n := singleLength? head then
    ensure ((response.extract (stop - n) stop).data == r.body.data)
      s!"machine/whole: the Content-Length body is not the {n} bytes before the {rest} unread ones"

/--
End of input changes nothing about a framed response: run over the same whole response with end of
input flipped, the machine completes it in both runs with the same status and body, or in neither.
A close-delimited body needs end of input; a response that ends some other way has failed or is
pending in both runs.
-/
def checkEofIndependent (method : Method) (withEof withoutEof : Run) : Except String Unit := do
  let msg := s!"end of input changes a framed response:\n  with:    {renderRun withEof}\n  without: {renderRun withoutEof}"
  if withoutEof.completed then
    ensure withEof.completed msg
    ensure (withEof.body.data == withoutEof.body.data) msg
    ensure ((withEof.finalHead.map (·.status.toCode)) == (withoutEof.finalHead.map (·.status.toCode))) msg
  else if withEof.completed then
    let some head := withEof.finalHead | throw msg
    ensure (closeDelimited method head) msg

/-! ## Comparing runs -/

/-- Whether one byte string is a prefix of the other. -/
def prefixConsistent (x y : ByteArray) : Bool :=
  let n := min x.size y.size
  (x.extract 0 n).data == (y.extract 0 n).data

/-- A trace without its body data. -/
def withoutData (trace : Array Ev) : Array Ev :=
  trace.filter fun e => !(e matches .data _)

/--
Split invariance of the direct driver.  A response that completes in either run must produce the
same events, body and reuse decision in both.  Otherwise the body delivered so far may differ: given
a chunk in pieces, the machine streams its data before the chunk's terminator arrives, and given it
whole, it checks the terminator first.  Then the other events must agree and each body must be a
prefix of the other.
-/
def machineSplitInvariant (whole split : Run) : Except String Unit := do
  let (a, b) := (renderRun whole, renderRun split)
  let msg := s!"machine not split-invariant:\n  whole: {a}\n  split: {b}"
  if whole.completed || split.completed then
    ensure (a == b && whole.body.data == split.body.data) msg
  else
    ensure (withoutData whole.trace == withoutData split.trace) msg
    ensure (prefixConsistent whole.body split.body) msg

/--
Split invariance of the exchange core: the same outcome, status, interim count and body, whether the
response came whole or in reads, also for a response still pending (the codec delivers every body
byte it is fed, so the body so far is the same).  The reuse verdict is not compared: bytes after the
response, in a later read, are not there when the core finishes, and a POST's upload may be at a
different point when the head arrives.
-/
def exchangeSplitInvariant (whole split : Core) : Except String Unit := do
  let (a, b) := (whole.render, split.render)
  ensure (a == b && whole.body.data == split.body.data)
    s!"exchange not split-invariant:\n  whole: {a}\n  split: {b}"

/-- Runs the response codec alone over `reads`, with `config`. -/
def codecOver (config : Codec.Config) (method : Method) (eof : Bool) (reads : List ByteArray) :
    Codec.Parser :=
  let p := reads.foldl (init := Codec.Parser.start config method) fun p piece => (p.feed piece).1
  if eof then p.finish.1 else p

/--
Whether a body-limit failure of the core is explained by a chunk announced beyond the body limit:
the codec without a body limit, over the same reads (without the end of input, which would end the
chunk it is in), has delivered or been announced (the rest of that chunk) more than the limit.  The
codec refuses such a chunk at its size line, before its data arrives; the machine only once the data
does.
-/
def chunkOverLimit (method : Method) (reads : List ByteArray) : Bool :=
  -- Above any chunk size a chunk-size line within its limit can announce.
  let unlimited := 16 ^ coreLimits.maxChunkLineLength
  let p := codecOver { coreLimits with maxBody := unlimited } method false reads
  let rest := match p.phase with
    | .body (.chunked (.data r)) => r
    | _ => 0
  p.delivered + rest > maxBody

/--
Whether a protocol failure of the core where the machine did not fail is explained by the codec
measuring chunk-size lines more strictly: without the chunk-size line and chunk extension limits,
the codec does not fail over the same reads.
-/
def chunkLineStricter (method : Method) (eof : Bool) (reads : List ByteArray) : Bool :=
  let p := codecOver { coreLimits with maxChunkLineLength := 2 ^ 20, maxChunkExtensions := 2 ^ 20 }
    method eof reads
  !(p.phase matches .failed _)

/-- Whether an HTTP/1.0 head says both `keep-alive` and `close`, which the codec does not reuse
(RFC 9112 section 9.3) and the machine does. -/
def http10KeepAliveAndClose (head : Response.Head) : Bool :=
  let conn := tokens head Header.Name.connection
  head.version == .v10 && conn.contains "close" && conn.contains "keep-alive"

/--
Keep-alive changes nothing in the exchange core's outcome over the same reads, and without it the
connection is never reusable.
-/
def keepAliveInvariant (on off : Core) : Except String Unit := do
  ensure (on.render == off.render)
    s!"keep-alive changes the outcome:\n  on:  {on.render}\n  off: {off.render}"
  ensure (off.reusable? != some true) "reusable without keep-alive"

/--
The exchange core's own invariants over one run: a completed response obeys the body invariants,
with the core's rule on transfer codings, and its reuse verdict those of `checkReusable`; a pending
response's body so far obeys them too, and nothing is pending after end of input; a body-limit
failure comes after the head, with its status (the machine's own body limit, which would refuse a
`Content-Length` before the head, is out of reach); a refusal of a transfer coding names a final
head with a body and codings other than just `chunked`.
-/
def checkCore (who : String) (method : Method) (c : Core) (eof : Bool) : Except String Unit := do
  if let some p := c.problem then throw s!"{who}: {p}"
  match c.ended, c.head with
  | some (.finish reusable), some head =>
    ensure (!head.status.isInformational) s!"{who}: done with an informational status"
    checkBody who method head c.body true c.model.eofSeen (strict := true)
    if reusable then
      ensure (!c.model.eofSeen) s!"{who}: reusable after end of input"
      checkReusable who method head
      ensure (!http10KeepAliveAndClose head) s!"{who}: reusable despite Connection: close"
  | some (.finish _), none => throw s!"{who}: finished without a head"
  | some (.fail f), head =>
    match f.cause with
    | .limit .body =>
      let some head := head | throw s!"{who}: a body-limit failure before the head"
      ensure (f.status.map (·.toCode) == some head.status.toCode && f.delivery == .responseReceived)
        s!"{who}: a body-limit failure without the response's status: {f.status.map (·.toCode)}, {f.delivery.name}"
    | .protocol msg =>
      if msg.startsWith "a transfer coding" then
        let some head := head | throw s!"{who}: a transfer coding refused before the head"
        ensure (!noBody method head && hasTransferEncoding head && !onlyChunked head)
          s!"{who}: refused for its transfer codings {tokens head Header.Name.transferEncoding}"
    | _ => pure ()
  | _, head =>
    if let some head := head then checkBody who method head c.body false eof (strict := true)
    if eof then throw s!"{who}: still pending after end of input"

/--
Checks that the exchange core and the direct driver agree, given the same reads.  `r` ran with
keep-alive on; nothing in the response's framing depends on that.  The core reuses the connection
only where the machine would (`reusableBeforeEnd`); with `whole`, the response came in one read, and the core reuses it
exactly where the machine would with no byte left over, given keep-alive and the whole request
written before the head arrived.
-/
def crossCheck (who : String) (c : Core) (r : Run) (whole : Bool) (method : Method) (eof : Bool)
    (reads : List ByteArray) : Except String Unit := do
  let phase ← wellFormed r.trace
  let done := phase == .ended || phase == .reset
  let machineCode := r.finalHead.map (·.status.toCode.toNat)
  let both := s!"{c.render} vs {renderRun r}"
  match c.ended, c.head with
  | some (.finish reuse), some head =>
    ensure done s!"{who}: exchange done, machine not: {both}"
    ensure (machineCode == some head.status.toCode.toNat) s!"{who}: final status differs: {both}"
    ensure (c.body.data == r.body.data) s!"{who}: body differs: {both}"
    ensure (c.ex.interim == r.interim) s!"{who}: interim count differs: {both}"
    if reuse then
      ensure (reusableBeforeEnd r) s!"{who}: the core reuses, the machine would not: {both}"
    if whole then
      let m := c.model
      let expected := c.ex.config.keepAlive && reusableBeforeEnd r && !http10KeepAliveAndClose head &&
        r.machine.reader.input.remainingBytes == 0 && m.ackedAtHead == m.request.size &&
        m.acked == m.request.size && !m.eofSeen
      ensure (reuse == expected)
        s!"{who}: reuse {reuse}, expected {expected} (written {m.acked} of {m.request.size}, {m.ackedAtHead} at the head): {both}"
  | some (.finish _), none => throw s!"{who}: finished without a head"
  | some (.fail f), _ =>
    match f.cause with
    | .limit .interim =>
      ensure (r.interim > maxInterim) s!"{who}: interim limit hit with {r.interim} interim responses"
    | .limit .body =>
      -- Both drivers lift the machine's chunk limit to the same bound, so a chunk size above it
      -- fails both the same way.
      let announced := (c.head.bind singleLength?).getD 0
      let machineRefused := r.trace.contains (.failed (toString H1.Error.entityTooLarge))
      ensure (r.body.size > maxBody || announced > maxBody || machineRefused ||
          chunkOverLimit method reads)
        s!"{who}: body limit hit with {r.body.size} bytes and Content-Length {announced}"
    | .protocol msg =>
      if msg.startsWith "101" then
        ensure (machineCode == some 101) s!"{who}: 101 refused, but the machine saw {repr machineCode}"
      else if msg.startsWith "a transfer coding" then
        ensure (machineCode == c.head.map (·.status.toCode.toNat))
          s!"{who}: refused a transfer coding on a head the machine did not see: {both}"
      else
        ensure (phase == .failed || chunkLineStricter method eof reads)
          s!"{who}: exchange failed ({msg}), machine did not: {both}"
    | _ =>
      -- With end of input before any byte, the machine only closes; the exchange reports that the
      -- peer closed.
      ensure (phase == .failed || (r.eof && !done)) s!"{who}: exchange failed, machine did not: {both}"
  | _, _ =>
    ensure (phase == .awaitHead || phase == .inBody) s!"{who}: exchange pending, machine not: {both}"

/--
The codec's deliberate differences from the machine that `crossCheck` allowed in a run of the core
against the direct driver over the same reads, by name: the allowances on which an input relies.
-/
def allowancesIn (c : Core) (r : Run) (whole : Bool) (method : Method) (eof : Bool)
    (reads : List ByteArray) : List String :=
  let phaseFailed := r.failedRun
  let reuseDiff := match c.ended, c.head with
    | some (.finish reuse), some head =>
      whole && !reuse && c.ex.config.keepAlive && reusableBeforeEnd r && http10KeepAliveAndClose head
    | _, _ => false
  let byFailure := match c.ended with
    | some (.fail f) =>
      match f.cause with
      | .limit .body =>
        let announced := (c.head.bind singleLength?).getD 0
        let machineRefused := r.trace.contains (.failed (toString H1.Error.entityTooLarge))
        if r.body.size > maxBody || announced > maxBody || machineRefused then []
        else if chunkOverLimit method reads then ["a chunk announced beyond the body limit"] else []
      | .protocol msg =>
        if msg.startsWith "101" || msg.startsWith "a transfer coding" || phaseFailed then []
        else if chunkLineStricter method eof reads then ["a chunk-size line measured more strictly"]
        else []
      | _ => []
    | _ => []
  byFailure ++ (if reuseDiff then ["HTTP/1.0 saying both keep-alive and close"] else [])

/-- The allowances an input relies on, over the whole response and over its reads. -/
def allowances (data : ByteArray) : List String :=
  let input := decode data
  let reads := pieces input
  let m := input.method
  match machineFor? m with
  | none => []
  | some machine =>
    let keep := prepared m true
    let whole := [input.response]
    (allowancesIn (runCore keep input.eof whole) (runMachine machine input.eof whole) true m
        input.eof whole ++
      allowancesIn (runCore keep input.eof reads) (runMachine machine input.eof reads) false m
        input.eof reads).eraseDups

/-! ## The whole check -/

/-- Everything one input produces, for the replay tool. -/
structure Report where
  /-- The decoded input. -/
  input : Input
  /-- The reads. -/
  reads : List ByteArray
  /-- The direct driver, response whole. -/
  runWhole : Run
  /-- The direct driver, response in reads. -/
  runSplit : Run
  /-- The direct driver, response whole, end of input flipped. -/
  runFlipped : Run
  /-- The exchange core with keep-alive, response whole. -/
  exWhole : Core
  /-- The exchange core with keep-alive, response in reads. -/
  exSplit : Core
  /-- The exchange core without keep-alive, response in reads. -/
  exSplitClose : Core

/-- Runs both drivers every way without checking anything. -/
def run (data : ByteArray) : Except String Report := do
  let input := decode data
  let reads := pieces input
  let whole := [input.response]
  let m := input.method
  let (keep, close) := (prepared m true, prepared m false)
  let some machine := machineFor? m | throw "the machine refused the request, or encoded it differently"
  let runWhole := runMachine machine input.eof whole
  let runSplit := runMachine machine input.eof reads
  let runFlipped := runMachine machine (!input.eof) whole
  let exWhole := runCore keep input.eof whole
  let exSplit := runCore keep input.eof reads
  let exSplitClose := runCore close input.eof reads
  return { input, reads, runWhole, runSplit, runFlipped, exWhole, exSplit, exSplitClose }

/-- Checks every invariant over one input; returns what both drivers did. -/
def check (data : ByteArray) : Except String Report := do
  let input := decode data
  let reads := pieces input
  let whole := [input.response]
  let m := input.method
  let (keep, close) := (prepared m true, prepared m false)
  let some machine := machineFor? m | throw "the machine refused the request, or encoded it differently"
  -- The direct driver first: its step bound catches loops in the machine.
  let runWhole := runMachine machine input.eof whole
  checkRun "machine/whole" m runWhole
  let runSplit := runMachine machine input.eof reads
  checkRun "machine/split" m runSplit
  machineSplitInvariant runWhole runSplit
  checkBodyBytes m input.response runWhole
  let runFlipped := runMachine machine (!input.eof) whole
  checkRun "machine/flipped" m runFlipped
  if input.eof then checkEofIndependent m runWhole runFlipped
  else checkEofIndependent m runFlipped runWhole
  let exWhole := runCore keep input.eof whole
  checkCore "exchange/whole" m exWhole input.eof
  let exSplit := runCore keep input.eof reads
  checkCore "exchange/split" m exSplit input.eof
  let exSplitClose := runCore close input.eof reads
  checkCore "exchange/split, keep-alive off" m exSplitClose input.eof
  exchangeSplitInvariant exWhole exSplit
  keepAliveInvariant exSplit exSplitClose
  crossCheck "whole" exWhole runWhole true m input.eof whole
  crossCheck "split" exSplit runSplit false m input.eof reads
  for (who, c) in [("exchange/whole", exWhole), ("exchange/split", exSplit)] do
    if let some p := waitOut c then throw s!"{who}, waiting: {p}"
  if let some p := unsolicited keep ((reads.find? (!·.isEmpty)).getD .empty) then
    throw s!"exchange, unsolicited bytes: {p}"
  return { input, reads, runWhole, runSplit, runFlipped, exWhole, exSplit, exSplitClose }

/--
The AFL++ entry point: checks one input and panics if an invariant fails.  Returns 0, or 1 after a
failed invariant whose panic did not abort (`LEAN_ABORT_ON_PANIC` unset), so that the caller can.
-/
@[export lean_http_fuzz_one]
def fuzzOne (data : ByteArray) : UInt32 :=
  match check data with
  | .ok _ => 0
  -- `panic!` returns the default value, 0; the result is used, so the panic is not dropped.
  | .error msg => (panic! s!"fuzz invariant failed: {msg}" : UInt32) ||| 1

end LeanHttpFuzz
