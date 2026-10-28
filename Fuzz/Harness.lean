import LeanHttp.Exchange

/-!
# Fuzzing harness for the client direction of the HTTP/1.1 machine

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

- **The exchange core** (`LeanHttp.Exchange`), the client the library ships, with keep-alive off.
- **A direct driver of the machine** with keep-alive on, the configuration a pooled client will
  use.  It mirrors `Exchange.drive` but bounds every loop, records the events the machine emits,
  and ends with the machine's reuse decision.

Both use the parser limits in `limits`: the defaults, lowered so that fuzzer inputs reach them.
Each driver runs twice, with the response in one read and in the reads the input dictates; the
direct driver runs a third time over the whole response with end of input flipped.  The direct
driver runs first, so that an endless loop the two drivers share is reported by its step bound
rather than as a hang in the exchange core.

## Invariants

- The direct driver ends within a step bound linear in the input (the exchange core has no bound
  of its own; an endless loop there shows up as an AFL++ hang).
- The events form a well-formed sequence: interim heads, one final head, body data, the end of the
  body, then possibly the machine's reset for the next message; a failure ends the sequence.
- No body after HEAD, after a 1xx used as final, after 204 or after 304, and the end of the body
  follows such a head (and one with `Content-Length: 0`) at once.
- Body bytes never exceed a single valid `Content-Length`; a completed body with
  `Content-Length` matches it exactly, and a completed response never carries an invalid or
  conflicting `Content-Length`, or both `Content-Length` and `Transfer-Encoding`.
- Over the whole response, a completed `Content-Length` body is exactly the bytes before the ones
  left unread, and a completed close-delimited body is exactly the bytes after the head.
- A close-delimited body completes only after end of input, and is never reusable; a framed
  response completes, with the same body, whether or not end of input follows it.
- A connection the machine would reuse ended a framed HTTP/1.1 response without `close` (or an
  HTTP/1.0 one with `keep-alive`), was not a `101`, and its peer has not closed.  Bytes may be left
  over: a pool must not reuse such a connection, and the harness only reports them.
- Split invariance: both drivers produce the same events, body and outcome whether the response
  arrives whole or in pieces.  For a response that does not complete, only the body delivered so
  far may differ, and then each body must be a prefix of the other; the exchange core may then also
  hit its body limit in one run and not the other (see `exchangeSplitInvariant`).
- For each way of feeding, the two drivers agree: the same completed response (status, body,
  interim count), a failure where the other failed or saw end of input too early, a pending
  response where the other is pending; except where the exchange core refuses by its own limits
  (interim count, body size, `101`), and then the refusal must be justified by what the machine saw.
-/

open Std.Http LeanHttp LeanHttpProto.Http.Protocol

namespace LeanHttpFuzz

/-! ## Limits -/

/--
The parser limits both drivers use: the defaults, lowered so that inputs of a few kilobytes reach
every one of them.
-/
def limits : H1.Config :=
  { maxHeaders := 16, maxHeaderBytes := 1024, maxStartLineLength := 256,
    maxHeaderNameLength := 64, maxHeaderValueLength := 512, maxReasonPhraseLength := 64,
    maxChunkLineLength := 128, maxChunkExtensions := 4, maxChunkExtNameLength := 32,
    maxChunkExtValueLength := 32, maxTrailerHeaders := 4 }

/-- The exchange core's limit on interim responses, small enough for fuzzer inputs to reach. -/
def maxInterim : Nat := 10

/-- The exchange core's body limit, small enough for fuzzer inputs to reach. -/
def maxBody : Nat := 1024

/--
The longest response the harness feeds: the exchange core's input buffer limit (the body limit plus
the header allowances).  A longer response would fail when fed whole but not in small reads, and
that limit is about the reads, not the response.
-/
def maxResponse : Nat :=
  maxBody + limits.maxHeaderBytes + limits.maxStartLineLength + limits.maxChunkLineLength

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
driver considered the response complete, `eof` whether end of input was reported.
-/
def checkBody (who : String) (method : Method) (head : Response.Head) (body : ByteArray)
    (done eof : Bool) : Except String Unit := do
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
      else if lengths.isEmpty then
        ensure eof s!"{who}: completed a close-delimited body without end of input"
      else
        match singleLength? head with
        | some n => ensure (body.size == n) s!"{who}: completed with {body.size} body bytes, Content-Length {n}"
        | none => throw s!"{who}: completed despite Content-Length {repr lengths}"

/-! ## Driver 1: the exchange core -/

/-- The request every input answers. -/
def requestHead (method : Method) : Request.Head :=
  { method, version := .v11, uri := .originForm { segments := #[], absolute := true } none,
    headers := Headers.empty.insert Header.Name.host (.mk "example.test") }

/-- Runs the exchange core over `reads`. -/
def runExchange (inp : Input) (reads : List ByteArray) : Exchange :=
  let (ex, _) := Exchange.start limits maxInterim maxBody (requestHead inp.method) .empty
  let ex := reads.foldl Exchange.feed ex
  if inp.eof then ex.endOfInput else ex

/--
A comparable rendering of the exchange core's outcome.  With `withBody` false, leaves out the size of
a body still pending.
-/
def renderExchange (ex : Exchange) (withBody : Bool := true) : String :=
  match ex.outcome with
  | .pending => s!"pending interim={ex.interim}" ++ (if withBody then s!" body={ex.body.size}" else "")
  | .done head body => s!"done {head.status.toCode} interim={ex.interim} body={showBody body}"
  | .failed cause => s!"failed {repr cause} interim={ex.interim} head={ex.head.isSome}"

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
Starts the machine on a request, as `Exchange.start` does but with keep-alive on: the same parser
limits, and the same lifted body and chunk limits.
-/
def startMachine (method : Method) : Run :=
  let unlimited := 2 ^ 62
  let config : H1.Config := { limits with maxBodySize := unlimited, maxChunkSize := unlimited }
  let machine : H1.Machine .sending := { config }
  let machine := machine.setKnownSize (.fixed 0)
  let machine := machine.send (requestHead method)
  let machine := machine.userClosedBody
  let (machine, result) := machine.step
  let r : Run := { machine }
  let (r, _) := r.handleAll result.events
  r

/-- Runs the direct driver over `reads`, then reports end of input if `eof`. -/
def runMachine (method : Method) (eof : Bool) (reads : List ByteArray) : Run :=
  let r := startMachine method
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
      ensure (head.status.toCode != 101) s!"{who}: reusable after 101"
      ensure (!closeDelimited method head) s!"{who}: reusable after a close-delimited body"
      let conn := tokens head Header.Name.connection
      if head.version == .v11 then
        ensure (!conn.contains "close") s!"{who}: reusable despite Connection: close"
      else
        ensure (conn.contains "keep-alive") s!"{who}: reusable HTTP/1.0 response without keep-alive"
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
Split invariance of the exchange core, with the allowance of `machineSplitInvariant`; and since the
body delivered so far may differ, one run may also hit the body limit while the other is pending or
has failed otherwise (`crossCheck` checks each run's limit against its own machine run).
-/
def exchangeSplitInvariant (whole split : Exchange) : Except String Unit := do
  let (a, b) := (renderExchange whole, renderExchange split)
  let msg := s!"exchange not split-invariant:\n  whole: {a}\n  split: {b}"
  match whole.outcome, split.outcome with
  | .done .., _ | _, .done .. => ensure (a == b) msg
  | .failed (.limit .body), _ | _, .failed (.limit .body) => pure ()
  | _, _ =>
    ensure (renderExchange whole false == renderExchange split false) msg
    ensure (prefixConsistent whole.body split.body) msg

/--
Checks that the exchange core and the direct driver agree, given the same reads.  `r` ran with
keep-alive on; nothing in the response's framing depends on that.
-/
def crossCheck (who : String) (ex : Exchange) (r : Run) : Except String Unit := do
  let phase ← wellFormed r.trace
  let done := phase == .ended || phase == .reset
  let machineCode := r.finalHead.map (·.status.toCode.toNat)
  let both := s!"{renderExchange ex} vs {renderRun r}"
  match ex.outcome with
  | .done head body =>
    ensure done s!"{who}: exchange done, machine not: {both}"
    ensure (machineCode == some head.status.toCode.toNat) s!"{who}: final status differs: {both}"
    ensure (body.data == r.body.data) s!"{who}: body differs: {both}"
    ensure (ex.interim == r.interim) s!"{who}: interim count differs: {both}"
  | .failed (.limit .interim) =>
    ensure (r.interim > maxInterim) s!"{who}: interim limit hit with {r.interim} interim responses"
  | .failed (.limit .body) =>
    -- The machine refuses a `Content-Length` above its own limit before reporting the head, so
    -- read the length from the head it was parsing.  Both drivers lift the machine's body and
    -- chunk limits to the same bound, so a chunk size above it fails both the same way.
    let head : Response.Head := r.finalHead.getD r.machine.reader.messageHead
    let announced := (singleLength? head).getD 0
    let machineRefused := r.trace.contains (.failed (toString H1.Error.entityTooLarge))
    ensure (r.body.size > maxBody || announced > maxBody || machineRefused)
      s!"{who}: body limit hit with {r.body.size} bytes and Content-Length {announced}"
  | .failed (.protocol msg) =>
    if msg.startsWith "101" then
      ensure (machineCode == some 101) s!"{who}: 101 refused, but the machine saw {repr machineCode}"
    else
      ensure (phase == .failed) s!"{who}: exchange failed ({msg}), machine did not: {both}"
  | .failed _ =>
    -- With end of input before any byte, the machine only closes; the exchange reports that the
    -- peer closed.
    ensure (phase == .failed || (r.eof && !done)) s!"{who}: exchange failed, machine did not: {both}"
  | .pending =>
    ensure (phase == .awaitHead || phase == .inBody) s!"{who}: exchange pending, machine not: {both}"

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
  /-- The exchange core, response whole. -/
  exWhole : Exchange
  /-- The exchange core, response in reads. -/
  exSplit : Exchange

/-- Checks every invariant over one input; returns what both drivers did. -/
def check (data : ByteArray) : Except String Report := do
  let input := decode data
  let reads := pieces input
  let whole := [input.response]
  let m := input.method
  -- The direct driver first: its step bound catches loops before the unbounded exchange core.
  let runWhole := runMachine m input.eof whole
  checkRun "machine/whole" m runWhole
  let runSplit := runMachine m input.eof reads
  checkRun "machine/split" m runSplit
  machineSplitInvariant runWhole runSplit
  checkBodyBytes m input.response runWhole
  let runFlipped := runMachine m (!input.eof) whole
  checkRun "machine/flipped" m runFlipped
  if input.eof then checkEofIndependent m runWhole runFlipped
  else checkEofIndependent m runFlipped runWhole
  let exWhole := runExchange input whole
  checkExchange "exchange/whole" m exWhole input.eof
  let exSplit := runExchange input reads
  checkExchange "exchange/split" m exSplit input.eof
  exchangeSplitInvariant exWhole exSplit
  crossCheck "whole" exWhole runWhole
  crossCheck "split" exSplit runSplit
  return { input, reads, runWhole, runSplit, runFlipped, exWhole, exSplit }
where
  /-- The invariants of one run of the exchange core. -/
  checkExchange (who : String) (method : Method) (ex : Exchange) (eof : Bool) :
      Except String Unit := do
    match ex.outcome with
    | .done head body =>
      ensure (!head.status.isInformational) s!"{who}: done with an informational status"
      checkBody who method head body true eof
    | .pending =>
      if let some head := ex.head then checkBody who method head ex.body false eof
      if eof then throw s!"{who}: still pending after end of input"
    | .failed _ => pure ()

/-- Runs both drivers every way without checking anything, for the replay tool. -/
def run (data : ByteArray) : Report :=
  let input := decode data
  let reads := pieces input
  let whole := [input.response]
  let m := input.method
  { input, reads,
    runWhole := runMachine m input.eof whole, runSplit := runMachine m input.eof reads,
    runFlipped := runMachine m (!input.eof) whole,
    exWhole := runExchange input whole, exSplit := runExchange input reads }

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
