import Tests.Support.Gen
import Tests.Support.Drive
import Tests.Support.CodecDrive

/-!
# Differential test: the response codec against the vendored machine

Runs the response codec (`LeanHttp.Codec`) and the exchange core over the vendored HTTP/1.1 machine
on the same responses, and compares what they make of them: the outcome (done with its status,
interim count and body, failed with its cause, or pending), the head (version and fields) and the
reuse verdict.  The exchange core runs with `keepAlive` on, so that its verdict means something.

The responses are the shapes of `Tests/Support/CodecCases.lean`, responses generated at random from a grammar
with deliberate faults, and mutations of both (bytes flipped, inserted, deleted, lines duplicated,
line endings changed, truncation).  Each is run with a GET or HEAD request, default or small limits,
and both without and with the end of input.  Besides the comparison (whole input to both), each
parser is also run with the input cut at random points, against its own whole-input result.

Usage: `codec-diff [seed] [generated] [mutated]`; prints a summary and every class of disagreement
with examples, and exits with status 0 (disagreements are findings to classify, not failures).
-/

open Std.Http LeanHttp

/-! ## Rendering -/

/-- Bytes as printable ASCII with escapes. -/
def escape (bytes : ByteArray) : String := Id.run do
  let mut s := ""
  for b in bytes.data do
    if b == 13 then s := s ++ "\\r"
    else if b == 10 then s := s ++ "\\n"
    else if b == 9 then s := s ++ "\\t"
    else if b == 92 then s := s ++ "\\\\"
    else if 32 ≤ b && b < 127 then s := s.push (Char.ofNat b.toNat)
    else
      let hex := "0123456789abcdef".toList
      s := s ++ "\\x" ++ String.singleton hex[(b.toNat / 16)]! ++ String.singleton hex[(b.toNat % 16)]!
  return s

/-- A head in comparable form. -/
def renderHead (head : Response.Head) : String :=
  let fields := head.headers.toList.map fun (n, v) => s!"{n.value}={v.value}"
  s!"{head.status.toCode} {repr head.version} {fields}"

/-- What came of a run, in comparable parts. -/
structure Outcome where
  /-- `done CODE interim=N`, `failed CAUSE` or `pending`. -/
  kind : String
  /-- The body, when done. -/
  body : ByteArray := .empty
  /-- The head, when one was delivered. -/
  head : String := ""
  /-- The reuse verdict, when done. -/
  reuse : Option Bool := none

/-- The exchange core's outcome. -/
def coreOutcome (r : Run) : Outcome :=
  let head := r.head.map renderHead |>.getD ""
  match r.ended, r.head with
  | some (.fail f), _ => { kind := s!"failed {repr f.cause}", head }
  | some (.finish reusable), some h =>
    { kind := s!"done {h.status.toCode} interim={r.ex.interim}", body := r.body, head,
      reuse := some reusable }
  | _, _ => { kind := "pending", head }

/-- The codec's outcome. -/
def codecOutcome (r : CodecRun) : Outcome :=
  let head := r.head?.map (renderHead ·.response) |>.getD ""
  let err := r.events.findSome? fun | .error e => some e | _ => none
  let done := r.events.any fun | .done => true | _ => false
  match err, done, r.head? with
  | some e, _, _ => { kind := s!"failed {repr (codecCause e)}", head }
  | none, true, some h =>
    { kind := s!"done {h.code} interim={h.interim}", body := r.body, head,
      reuse := some r.p.reusable }
  | _, _, _ => { kind := "pending", head }

/--
Where two outcomes `a` and `b` (named `na` and `nb`) differ, or `none` if they agree: a class, and a
detail for the example.
-/
def compare (a b : Outcome) (withReuse : Bool) (na : String := "core") (nb : String := "codec") :
    Option (String × String) :=
  if a.kind != b.kind then some (s!"outcome: {na} {a.kind} / {nb} {b.kind}", "")
  else if a.kind.startsWith "done" && a.body.data != b.body.data then
    some (s!"body ({a.kind})", "")
  else if a.head != b.head then some (s!"head ({a.kind})", s!"{na} [{a.head}] / {nb} [{b.head}]")
  else if withReuse && a.reuse != b.reuse then
    some (s!"reuse: {na} {a.reuse} / {nb} {b.reuse}", "")
  else none

/-! ## Running both -/

/-- The exchange core's configuration for some limits, with keep-alive on. -/
def coreConfig (l : Limits) : ExchangeConfig :=
  { h1 := l.h1, maxInterim := l.maxInterim, maxBody := l.maxBody, keepAlive := true }

/-- One input, with how to run it. -/
structure Input where
  /-- Where it came from. -/
  origin : String
  /-- The response bytes. -/
  bytes : ByteArray
  /-- The request method. -/
  method : Method := .get
  /-- The limits. -/
  limits : Limits := {}

instance : Inhabited Input := ⟨{ origin := "", bytes := .empty }⟩

/-- Runs the exchange core over `pieces`; returns the outcomes without and with end of input. -/
def runCore (i : Input) (pieces : List ByteArray) : Outcome × Outcome :=
  let r := Run.written (prepare! (coreConfig i.limits) (requestHead i.method) .empty)
  let r := pieces.foldl Run.feed r
  (coreOutcome r, coreOutcome r.endOfInput)

/-- Runs the codec over `pieces`; returns the outcomes without and with end of input.  With `control`,
the codec runs with limits one off from the exchange core's, so that disagreements must appear. -/
def runCodec (i : Input) (pieces : List ByteArray) (control : Bool := false) : Outcome × Outcome :=
  let cfg := codecConfig i.limits
  let cfg := if control then
      { cfg with maxInterim := cfg.maxInterim + 1, maxBody := cfg.maxBody - 1, maxHeaders := cfg.maxHeaders - 1 }
    else cfg
  (codecOutcome (codecRun cfg i.method pieces false), codecOutcome (codecRun cfg i.method pieces true))

/-! ## Generating responses -/

/-- Appends a string's bytes. -/
def str (s : String) : ByteArray := s.toUTF8

/-- A random token. -/
def genToken : Gen String := do
  let n := 1 + (← below 8)
  let chars := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_.!~".toList
  let mut s := ""
  for _ in [0:n] do s := s.push (← pick chars)
  return s

/-- Random printable body bytes. -/
def genBody (n : Nat) : Gen ByteArray := do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do b := b.push (32 + (← below 95)).toUInt8
  return b

/-- A body length, mostly small. -/
def genLength : Gen Nat := do
  pickWeighted [(6, 0), (30, ← below 20), (10, ← below 200), (2, ← below 3000)]

/-- A line ending, almost always CRLF. -/
def genEol : Gen String := pickWeighted [(99, "\r\n"), (1, "\n")]

/-- A header field line from a pool of ordinary fields. -/
def genOtherField : Gen String := do
  let name ← pick ["Content-Type", "Server", "Date", "X-Request-Id", "Cache-Control", "Vary",
    "Set-Cookie", (← genToken)]
  let value ← pick ["text/plain", "a b c", (← genToken), "", "x\ty", "1, 2, 3", "\"q\""]
  let sep ← pickWeighted [(16, ": "), (4, ":"), (2, ":   "), (2, ":\t"), (1, " : ")]
  let trail ← pickWeighted [(9, ""), (1, " "), (1, "\t \t")]
  return s!"{name}{sep}{value}{trail}"

/-- How a generated response frames its body. -/
inductive GenFraming where
  | length (value : String)
  | chunked (value : String)
  | both
  | twoLengths (a b : String)
  | none
deriving Inhabited

/-- A chunked encoding of `body`, with random chunk sizes, digit styles, extensions and trailers. -/
def genChunked (body : ByteArray) : Gen ByteArray := do
  let mut out := ByteArray.empty
  let mut i := 0
  while i < body.size do
    let size := min (body.size - i) (1 + (← below 50))
    let hex := String.ofList (Nat.toDigits 16 size)
    let hex ← pickWeighted [(8, hex), (1, hex.toUpper), (1, "00" ++ hex)]
    let ext ← pickWeighted [(8, ""), (1, ";a=b"), (1, ";name"), (1, ";q=\"x\\\" y\""), (1, " ; a"),
      (1, ";a ;b=c")]
    out := out ++ str s!"{hex}{ext}\r\n" ++ body.extract i (i + size) ++ str "\r\n"
    i := i + size
  let last ← pickWeighted [(8, "0"), (1, "000"), (1, "0;end")]
  let trailers ← pickWeighted [(8, ""), (2, "X-Checksum: abc\r\n"), (1, "Content-Length: 5\r\n"),
    (1, "X-A: 1\r\nX-B: 2\r\n")]
  return out ++ str s!"{last}\r\n{trailers}\r\n"

/-- An interim response. -/
def genInterim : Gen String := do
  let code ← pickWeighted [(10, "100"), (6, "103"), (4, "102"), (1, "101"), (2, "199")]
  let fields ← pickWeighted [(6, ""), (2, "Link: </a>\r\n"), (1, "Content-Length: 5\r\n"),
    (1, "Connection: close\r\n")]
  return s!"HTTP/1.1 {code} Info\r\n{fields}\r\n"

/-- A response from the grammar, with occasional faults. -/
def genResponse : Gen ByteArray := do
  let interim ← pickWeighted [(12, 0), (4, 1), (2, 2), (1, 3), (1, 11)]
  let mut out := ByteArray.empty
  for _ in [0:interim] do out := out ++ str (← genInterim)
  let version ← pickWeighted [(40, "HTTP/1.1"), (8, "HTTP/1.0"), (1, "HTTP/2.0"), (1, "HTTP/1.2"),
    (1, "http/1.1")]
  let code ← pickWeighted [(20, "200"), (2, "201"), (3, "204"), (2, "206"), (2, "301"), (3, "304"),
    (2, "404"), (2, "500"), (1, "599"), (1, "999"), (1, "099"), (1, "100"), (1, "2x0"), (1, "20")]
  let reason ← pickWeighted [(20, " OK"), (4, " "), (1, ""), (4, " Some Reason"), (2, " \tTab"),
    (1, " Café")]
  out := out ++ str s!"{version} {code}{reason}" ++ str (← genEol)
  let body ← genBody (← genLength)
  let framing ← pickWeighted [
    (24, GenFraming.length (toString body.size)),
    (20, .chunked "chunked"),
    (10, .none),
    (1, .length (toString (body.size + 3))),
    (1, .length (toString (body.size - min body.size 2))),
    (1, .length ("00" ++ toString body.size)),
    (1, .length ("+" ++ toString body.size)),
    (1, .length (s!"{body.size}, {body.size}")),
    (1, .chunked "Chunked"),
    (1, .chunked "gzip, chunked"),
    (1, .chunked "chunked, gzip"),
    (1, .chunked "identity"),
    (1, .chunked "chunked;q=1"),
    (1, .both),
    (1, .twoLengths (toString body.size) (toString body.size))]
  let mut fields : Array String := #[]
  for _ in [0:(← below 4)] do fields := fields.push (← genOtherField)
  match framing with
  | .length v => fields := fields.push s!"{← pick ["Content-Length", "content-length", "CONTENT-LENGTH"]}: {v}"
  | .chunked v => fields := fields.push s!"{← pick ["Transfer-Encoding", "transfer-encoding"]}: {v}"
  | .both =>
    fields := fields.push s!"Content-Length: {body.size}"
    fields := fields.push "Transfer-Encoding: chunked"
  | .twoLengths a b =>
    fields := fields.push s!"Content-Length: {a}"
    fields := fields.push s!"Content-Length: {b}"
  | .none => pure ()
  match ← below 6 with
  | 0 => fields := fields.push s!"Connection: {← pick ["close", "keep-alive", "Upgrade, close", "a,,b", "Keep-Alive", "keep-alive, close"]}"
  | _ => pure ()
  -- Shuffle the fields a little.
  if fields.size > 1 && (← below 2) == 0 then
    let j ← below fields.size
    fields := (fields.swapIfInBounds 0 j)
  for f in fields do out := out ++ str f ++ str (← genEol)
  out := out ++ str (← genEol)
  let payload ← match framing with
    | .chunked _ | .both => genChunked body
    | _ => pure body
  out := out ++ payload
  match ← below 10 with
  | 0 => out := out ++ str "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
  | 1 => out := out ++ str "garbage"
  | _ => pure ()
  return out

/-! ## Mutations -/

/-- Bytes that matter to the grammar. -/
def specialBytes : List UInt8 :=
  [13, 10, 32, 9, 58, 59, 61, 34, 92, 44, 48, 97, 70, 0, 0x80, 0xff, 72, 49]

/-- One random mutation. -/
def mutateOnce (b : ByteArray) : Gen ByteArray := do
  if b.size == 0 then return str "HTTP/1.1 200 OK\r\n\r\n"
  let i ← below b.size
  match ← below 11 with
  | 0 => return b.set! i (← below 256).toUInt8
  | 1 => return b.set! i (← pick specialBytes)
  | 2 => return b.extract 0 i |>.push (← pick specialBytes) |>.append (b.extract i b.size)
  | 3 => return b.extract 0 i ++ b.extract (i + 1) b.size
  | 4 =>
    let n := 1 + (← below 12)
    return b.extract 0 (i + n) ++ b.extract i b.size
  | 5 =>
    let n := 1 + (← below 12)
    return b.extract 0 i ++ b.extract (i + n) b.size
  | 6 => return b.extract 0 i
  | 7 =>
    let c := b.get! i
    let c := if 65 ≤ c && c ≤ 90 then c + 32 else if 97 ≤ c && c ≤ 122 then c - 32 else c
    return b.set! i c
  | 8 => return b.extract 0 i ++ str "\r\n" ++ b.extract i b.size
  | 9 =>
    -- Drop a CR before an LF, if there is one at or after `i`.
    let mut j := i
    while j + 1 < b.size && !(b.get! j == 13 && b.get! (j + 1) == 10) do j := j + 1
    if j + 1 < b.size then return b.extract 0 j ++ b.extract (j + 1) b.size else return b
  | _ =>
    let line ← pick ["Content-Length: 3\r\n", "Transfer-Encoding: chunked\r\n", "Connection: close\r\n",
      " folded\r\n", "X: y\r\n", "Content-Length: 99999999999999999999\r\n"]
    return b.extract 0 i ++ str line ++ b.extract i b.size

/-- One to four mutations. -/
def mutate (b : ByteArray) : Gen ByteArray := do
  let mut b := b
  for _ in [0:(1 + (← below 4))] do b ← mutateOnce b
  return b

/-! ## Inputs -/

/-- A limit: usually the default, sometimes one of `small`. -/
def genLimit (default : Nat) (small : List Nat) : Gen Nat := do
  if (← below 4) == 0 then pick small else return default

/-- Random small limits, sometimes, each one separately. -/
def genLimits : Gen Limits := do
  if (← below 10) < 7 then return {}
  return { maxInterim := ← genLimit 10 [0, 1, 2], maxBody := ← genLimit 1024 [0, 10, 100, 4000],
           h1 := { maxHeaders := ← genLimit 100 [1, 2, 3], maxHeaderBytes := ← genLimit 65536 [20, 64, 200],
                   maxHeaderNameLength := ← genLimit 256 [4, 12], maxHeaderValueLength := ← genLimit 8192 [3, 8],
                   maxSpaceSequence := ← genLimit 16 [0, 1, 2], maxReasonPhraseLength := ← genLimit 512 [2, 4],
                   maxChunkExtensions := ← genLimit 16 [0, 1], maxChunkExtNameLength := ← genLimit 256 [1, 3],
                   maxChunkExtValueLength := ← genLimit 256 [1, 3],
                   maxChunkLineLength := ← genLimit 8192 [4, 6, 10],
                   maxTrailerHeaders := ← genLimit 20 [0, 1] } }

/-- A random method. -/
def genMethod : Gen Method := pickWeighted [(8, Method.get), (2, .head), (1, .post)]

/-- Random cut points for `bytes`, as pieces. -/
def genPieces (bytes : ByteArray) : Gen (List ByteArray) := do
  let cuts ← (List.range (1 + (← below 3))).mapM fun _ => below (bytes.size + 1)
  let cuts := (cuts.mergeSort (· ≤ ·)).eraseDups
  let mut pieces := []
  let mut prev := 0
  for c in cuts do
    pieces := bytes.extract prev c :: pieces
    prev := c
  return (bytes.extract prev bytes.size :: pieces).reverse

/-! ## The comparison -/

/-- Disagreements found, by class, with a count and examples. -/
abbrev Findings := Std.HashMap String (Nat × Array String)

/-- Records one disagreement. -/
def Findings.add (f : Findings) (key example_ : String) : Findings :=
  let (n, xs) := f.getD key (0, #[])
  f.insert key (n + 1, if xs.size < 4 then xs.push example_ else xs)

/-- The limits that differ from the defaults of the shapes. -/
def describeLimits (l : Limits) : String :=
  let d : Limits := {}
  let c := codecConfig l
  let dc := codecConfig d
  let diffs := [("maxInterim", c.maxInterim, dc.maxInterim), ("maxBody", c.maxBody, dc.maxBody),
    ("maxHeaders", c.maxHeaders, dc.maxHeaders), ("maxHeaderBytes", c.maxHeaderBytes, dc.maxHeaderBytes),
    ("maxHeaderNameLength", c.maxHeaderNameLength, dc.maxHeaderNameLength),
    ("maxHeaderValueLength", c.maxHeaderValueLength, dc.maxHeaderValueLength),
    ("maxSpaceSequence", c.maxSpaceSequence, dc.maxSpaceSequence),
    ("maxReasonPhraseLength", c.maxReasonPhraseLength, dc.maxReasonPhraseLength),
    ("maxChunkExtensions", c.maxChunkExtensions, dc.maxChunkExtensions),
    ("maxChunkExtNameLength", c.maxChunkExtNameLength, dc.maxChunkExtNameLength),
    ("maxChunkExtValueLength", c.maxChunkExtValueLength, dc.maxChunkExtValueLength),
    ("maxChunkLineLength", c.maxChunkLineLength, dc.maxChunkLineLength),
    ("maxTrailerHeaders", c.maxTrailerHeaders, dc.maxTrailerHeaders)].filterMap fun (n, v, dv) =>
      if v == dv then none else some s!"{n}={v}"
  if diffs.isEmpty then "default" else ",".intercalate diffs

/-- The input with limits changed. -/
def Input.withLimits (i : Input) (f : Limits → Limits) : Input :=
  { i with limits := f i.limits }

/-- No body limit to speak of. -/
def relaxBody (l : Limits) : Limits := { l with maxBody := 2 ^ 40 }

/-- No chunk-size line limit to speak of. -/
def relaxChunkLine (l : Limits) : Limits := { l with h1 := { l.h1 with maxChunkLineLength := 2 ^ 20 } }

/--
Why the codec and the exchange core disagree on an input: an HTTP/1.0 response saying both
`keep-alive` and `close` (which the codec does not keep, RFC 9112 section 9.3), or a limit, found by
relaxing one limit at a time until they agree.
-/
def attributeCodec (i : Input) (eof : Bool) (control : Bool) : String := Id.run do
  let head := (codecRun (codecConfig i.limits) i.method [i.bytes] false).head?
  let agree (i' : Input) : Bool :=
    let (a, ae) := runCore i' [i'.bytes]
    let (b, be) := runCodec i' [i'.bytes] control
    if eof then (compare ae be false).isNone else (compare a b true).isNone
  if let some h := head then
    if let some tokens := Codec.connectionTokens h.fields then
      if h.http10 && tokens.contains (Codec.ascii "close") && tokens.contains (Codec.ascii "keep-alive") then
        return "HTTP/1.0 saying both keep-alive and close"
  let chunked := head.any fun h => h.framing matches .chunked
  if agree (i.withLimits relaxBody) then
    return if chunked then "body limit, chunked body" else "body limit, not chunked"
  if agree (i.withLimits relaxChunkLine) then return "chunk-size line limit"
  if agree (i.withLimits (relaxChunkLine ∘ relaxBody)) then return "body and chunk-size line limits"
  return "UNEXPLAINED"

/-- Why the exchange core's outcome depends on how its input is cut, found the same way. -/
def attributeCore (i : Input) (pieces : List ByteArray) (eof : Bool) : String :=
  let agree (i' : Input) : Bool :=
    let (a, ae) := runCore i' [i'.bytes]
    let (b, be) := runCore i' pieces
    if eof then (compare ae be false).isNone else (compare a b false).isNone
  if agree (i.withLimits relaxBody) then "body limit"
  else if agree (i.withLimits relaxChunkLine) then "chunk-size line limit"
  else "UNEXPLAINED"

/-- Runs one input through every comparison. -/
def check (f : Findings) (i : Input) (pieces : List ByteArray) (control : Bool) : Findings := Id.run do
  let mut f := f
  let (core, coreEof) := runCore i [i.bytes]
  let (codec, codecEof) := runCodec i [i.bytes] control
  -- How often each outcome occurs, to show what the inputs exercise.
  f := f.add s!"(outcome, open) {core.kind}" ""
  f := f.add s!"(outcome, eof) {coreEof.kind}" ""
  let (coreS, coreEofS) := runCore i pieces
  let (codecS, codecEofS) := runCodec i pieces control
  let desc := s!"[{i.origin} {repr i.method} limits={describeLimits i.limits}] {escape i.bytes}"
  let cutDesc := s!"{desc} cut={pieces.map (·.size)}"
  let detail (d : String) (base : String) := if d.isEmpty then base else s!"{d}: {base}"
  if let some (k, d) := compare core codec true then
    f := f.add s!"codec vs core, open: {k} [{attributeCodec i false control}]" (detail d desc)
  if let some (k, d) := compare coreEof codecEof false then
    f := f.add s!"codec vs core, eof: {k} [{attributeCodec i true control}]" (detail d desc)
  if let some (k, d) := compare core coreS false "whole" "cut" then
    f := f.add s!"core split-dependence, open: {k} [{attributeCore i pieces false}]" (detail d cutDesc)
  if let some (k, d) := compare coreEof coreEofS false "whole" "cut" then
    f := f.add s!"core split-dependence, eof: {k} [{attributeCore i pieces true}]" (detail d cutDesc)
  if let some (k, d) := compare codec codecS true "whole" "cut" then
    f := f.add s!"CODEC split-dependence, open: {k}" (detail d cutDesc)
  if let some (k, d) := compare codecEof codecEofS true "whole" "cut" then
    f := f.add s!"CODEC split-dependence, eof: {k}" (detail d cutDesc)
  return f

def main (args : List String) : IO UInt32 := do
  let seed := (args[0]?.bind String.toNat?).getD 1
  let generated := (args[1]?.bind String.toNat?).getD 60000
  let mutated := (args[2]?.bind String.toNat?).getD 60000
  let control := args[3]? == some "control"
  IO.println s!"seed={seed} generated={generated} mutated={mutated} control={control}"
  let mut rng : Rng := ⟨seed.toUInt64⟩
  let mut f : Findings := {}
  let mut total := 0
  -- The shapes, as given, with their limits and method.
  let shapes := cases.map fun c =>
    ({ origin := s!"case {c.name}", bytes := c.response.toUTF8, method := c.method, limits := c.limits }
      : Input)
  for i in shapes do
    let (pieces, r) := (genPieces i.bytes).run rng
    rng := r
    f := check f i pieces control
    total := total + 1
  -- Generated responses.
  for n in [0:generated] do
    let ((i, pieces), r) := (do
      let bytes ← genResponse
      let i : Input := { origin := s!"gen {n}", bytes, method := ← genMethod, limits := ← genLimits }
      return (i, ← genPieces bytes) : Gen _).run rng
    rng := r
    f := check f i pieces control
    total := total + 1
  -- Mutations of shapes and generated responses.
  for n in [0:mutated] do
    let ((i, pieces), r) := (do
      let base ← if (← below 4) == 0 then pure (← pick shapes).bytes else genResponse
      let bytes ← mutate base
      let i : Input := { origin := s!"mut {n}", bytes, method := ← genMethod, limits := ← genLimits }
      return (i, ← genPieces bytes) : Gen _).run rng
    rng := r
    f := check f i pieces control
    total := total + 1
  IO.println s!"{total} inputs, each run whole and cut, open and at end of input"
  let all := f.toList.mergeSort fun a b => a.1 ≤ b.1
  let (stats, classes) := all.partition (·.1.startsWith "(outcome")
  IO.println "outcomes of the exchange core (whole input):"
  for (key, (n, _)) in stats do
    IO.println s!"  {n} {key}"
  IO.println s!"{classes.length} classes of disagreement"
  for (key, (n, examples)) in classes do
    IO.println s!"\n== {key}: {n}"
    for e in examples do
      IO.println s!"   {e.take 600}"
  return 0
