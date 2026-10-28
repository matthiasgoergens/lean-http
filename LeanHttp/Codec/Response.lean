module

public import LeanHttp.Codec.Head
public import LeanHttp.Codec.Chunked

@[expose] public section

/-!
# The response parser

An incremental HTTP/1.1 response parser for the client direction, written to be proved correct
(`LeanHttp.Codec.Proofs`).

- `Parser.start config method` begins a response to a request with `method`.
- `Parser.feed p bytes` reads the next bytes and returns the new parser and the events they caused.
- `Parser.finish p` reports the end of the input.

Events are a final head, body bytes, then the end of the response or an error; the parser emits
nothing after the end or an error, and bytes that arrive after the end are only noted
(`Parser.extra`).

The meaning is given by `Parser.stepByte`, which reads one byte with no loop; `Parser.run` reads a
list of bytes with it.  `Parser.feed` is the fast version: it reads body bytes in bulk, slicing
them out of the input, and is proved to compute the same state and the same events up to how body
bytes are split between events (`feed_eq_run`).  So every way of cutting the input into pieces gives
the same result (`feed_append`), and `feed` makes at most one round per input byte
(`feedSteps_le`).

Nothing here carries a buffer across calls that grows with the body: body bytes are sliced out of
the bytes given to `feed`, and the only buffers kept are those of the current line, bounded by the
limits.
-/

namespace LeanHttp.Codec

set_option linter.all true

open Std.Http

/--
Where a body stands.
-/
inductive Body where
  /-- A `Content-Length` body with `remaining` bytes to go. -/
  | fixed (remaining : Nat)
  /-- A chunked body. -/
  | chunked (c : ChunkState)
  /-- A body delimited by the end of input, of which `room` more bytes are allowed. -/
  | untilClose (room : Nat)
deriving Repr, Inhabited, DecidableEq

/--
Where a response stands.
-/
inductive Phase where
  /-- Reading heads, until the final one. -/
  | head (hs : HeadState)
  /-- Reading the body of the final response. -/
  | body (b : Body)
  /-- The response ended. -/
  | done
  /-- The response was rejected. -/
  | failed (e : Error)
deriving Repr, Inhabited, DecidableEq

/--
The state of the response parser.
-/
structure Parser where
  /-- The limits. -/
  config : Config
  /-- Whether the request was HEAD, so that the response has no body. -/
  isHead : Bool
  /-- Where the response stands. -/
  phase : Phase
  /-- The final head, once it arrived. -/
  head : Option Head := none
  /-- Body bytes delivered so far. -/
  delivered : Nat := 0
  /-- Whether any byte arrived after the end of the response. -/
  extra : Bool := false
  /-- Whether the end of input was reported. -/
  inputEnded : Bool := false
deriving Inhabited

namespace Parser

/--
`true` for the HEAD method, whose responses have no body.
-/
def isHeadMethod : Method → Bool
  | .head => true
  | _ => false

/--
A parser for the response to a request with `method`.
-/
def start (config : Config) (method : Method) : Parser :=
  { config, isHead := isHeadMethod method, phase := .head {} }

/--
A one-byte array.
-/
def single (b : UInt8) : ByteArray :=
  ⟨#[b]⟩

/--
Rejects the response.
-/
def fail (p : Parser) (e : Error) : Parser × Array Event :=
  ({ p with phase := .failed e }, #[.error e])

/--
Begins the body of the final head `h`, after reporting it.
-/
def startBody (p : Parser) (h : Head) : Parser × Array Event :=
  let p := { p with head := some h }
  match h.framing with
  | .none | .length 0 => ({ p with phase := .done }, #[.head h, .done])
  | .length (n + 1) =>
    if p.config.maxBody < n + 1 then
      ({ p with phase := .failed .bodyTooLarge }, #[.head h, .error .bodyTooLarge])
    else ({ p with phase := .body (.fixed (n + 1)) }, #[.head h])
  | .chunked => ({ p with phase := .body (.chunked (.line {})) }, #[.head h])
  | .untilClose => ({ p with phase := .body (.untilClose p.config.maxBody) }, #[.head h])

/--
Reads one byte.  This is the meaning of the parser: `feed` computes the same, faster.
-/
def stepByte (p : Parser) (b : UInt8) : Parser × Array Event :=
  match p.phase with
  | .head hs =>
    match stepHead p.config p.isHead hs b with
    | .more hs => ({ p with phase := .head hs }, #[])
    | .fail e => p.fail e
    | .final h => p.startBody h
  | .body (.fixed r) =>
    if r ≤ 1 then ({ p with phase := .done, delivered := p.delivered + 1 }, #[.body (single b), .done])
    else ({ p with phase := .body (.fixed (r - 1)), delivered := p.delivered + 1 }, #[.body (single b)])
  | .body (.untilClose room) =>
    if room = 0 then p.fail .bodyTooLarge
    else ({ p with phase := .body (.untilClose (room - 1)), delivered := p.delivered + 1 },
      #[.body (single b)])
  | .body (.chunked c) =>
    match stepChunk p.config (p.config.maxBody - p.delivered) c b with
    | .more c => ({ p with phase := .body (.chunked c) }, #[])
    | .data c => ({ p with phase := .body (.chunked c), delivered := p.delivered + 1 }, #[.body (single b)])
    | .ended => ({ p with phase := .done }, #[.done])
    | .fail e => p.fail e
  | .done => ({ p with extra := true }, #[])
  | .failed _ => (p, #[])

/--
Reads bytes one at a time with `stepByte`.
-/
def run (p : Parser) : List UInt8 → Parser × Array Event
  | [] => (p, #[])
  | b :: bs =>
    let r := p.stepByte b
    let r' := r.1.run bs
    (r'.1, r.2 ++ r'.2)

/--
The loop of `feed`, from position `i` of `bytes`, with the events so far in `acc` and the rounds so
far in `steps`.  Each round reads at least one byte: body bytes in bulk, anything else one byte at a
time.
-/
def feedLoop (bytes : ByteArray) (p : Parser) (i : Nat) (acc : Array Event) (steps : Nat) :
    Parser × Array Event × Nat :=
  if h : i < bytes.size then
    let avail := bytes.size - i
    match p.phase with
    | .body (.fixed (r + 1)) =>
      if r + 1 ≤ avail then
        feedLoop bytes { p with phase := .done, delivered := p.delivered + (r + 1) } (i + (r + 1))
          ((acc.push (.body (bytes.extract i (i + (r + 1))))).push .done) (steps + 1)
      else
        ({ p with phase := .body (.fixed (r + 1 - avail)), delivered := p.delivered + avail },
          acc.push (.body (bytes.extract i bytes.size)), steps + 1)
    | .body (.chunked (.data (r + 1))) =>
      if r + 1 ≤ avail then
        feedLoop bytes { p with phase := .body (.chunked .dataCR), delivered := p.delivered + (r + 1) }
          (i + (r + 1)) (acc.push (.body (bytes.extract i (i + (r + 1))))) (steps + 1)
      else
        ({ p with phase := .body (.chunked (.data (r + 1 - avail))), delivered := p.delivered + avail },
          acc.push (.body (bytes.extract i bytes.size)), steps + 1)
    | .body (.untilClose (r + 1)) =>
      if r + 1 ≤ avail then
        feedLoop bytes { p with phase := .body (.untilClose 0), delivered := p.delivered + (r + 1) }
          (i + (r + 1)) (acc.push (.body (bytes.extract i (i + (r + 1))))) (steps + 1)
      else
        ({ p with phase := .body (.untilClose (r + 1 - avail)), delivered := p.delivered + avail },
          acc.push (.body (bytes.extract i bytes.size)), steps + 1)
    | .done => ({ p with extra := true }, acc, steps + 1)
    | .failed _ => (p, acc, steps + 1)
    | _ =>
      let r := p.stepByte bytes[i]
      feedLoop bytes r.1 (i + 1) (acc ++ r.2) (steps + 1)
  else (p, acc, steps)
termination_by bytes.size - i

/--
Reads the next bytes of the response, and returns the new parser and the events they caused.
-/
def feed (p : Parser) (bytes : ByteArray) : Parser × Array Event :=
  let r := feedLoop bytes p 0 #[] 0
  (r.1, r.2.1)

/--
How many rounds `feed` makes on `bytes`: at most `bytes.size` (`feedSteps_le`).
-/
def feedSteps (p : Parser) (bytes : ByteArray) : Nat :=
  (feedLoop bytes p 0 #[] 0).2.2

/--
Feeds several pieces in order.
-/
def feedAll (p : Parser) : List ByteArray → Parser × Array Event
  | [] => (p, #[])
  | piece :: pieces =>
    let r := p.feed piece
    let r' := r.1.feedAll pieces
    (r'.1, r.2 ++ r'.2)

/--
Reports the end of the input.  A body delimited by it ends; any other unfinished response is
rejected with `Error.closed`.
-/
def finish (p : Parser) : Parser × Array Event :=
  let q := { p with inputEnded := true }
  match p.phase with
  | .done | .failed _ => (q, #[])
  | .body (.untilClose _) => ({ q with phase := .done }, #[.done])
  | _ => q.fail .closed

/--
`true` once the response ended.
-/
def complete (p : Parser) : Bool :=
  p.phase matches .done

/--
`true` when the final head arrived and its body's end is marked in the bytes themselves.
-/
def certain (p : Parser) : Bool :=
  p.head.any (·.framing.certain)

/--
`true` when the response ended, framed with certainty: its end was known from its own bytes, not from
the end of the input.
-/
def completeCertain (p : Parser) : Bool :=
  p.complete && p.certain

/--
Whether the connection could carry another exchange, as far as the response is concerned: it ended,
framed with certainty, nothing followed it, the input did not end, and every head allowed the
connection to stay open.
-/
def reusable (p : Parser) : Bool :=
  p.completeCertain && !p.extra && !p.inputEnded && p.head.any (·.keepAlive)

/--
Interim responses read so far.
-/
def interim (p : Parser) : Nat :=
  match p.head, p.phase with
  | some h, _ => h.interim
  | none, .head hs => hs.interim
  | none, _ => 0

end Parser

end LeanHttp.Codec
