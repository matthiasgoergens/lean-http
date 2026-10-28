module

public import LeanHttp.Codec.Lines

@[expose] public section

/-!
# Chunked bodies

Decodes a chunked body one byte at a time (RFC 9112 section 7.1): chunk-size lines, chunk data with
its CRLF, the last chunk, and the trailer section, whose fields are checked and discarded.  Also a
simple encoder, against which the decoder is proved (`LeanHttp.Codec.Proofs`).
-/

namespace LeanHttp.Codec

set_option linter.all true

/--
Where a chunked body decoder stands.
-/
inductive ChunkState where
  /-- In a chunk-size line. -/
  | line (cl : ChunkLine)
  /-- In chunk data, with `remaining` bytes to go. -/
  | data (remaining : Nat)
  /-- Expecting the CR after chunk data. -/
  | dataCR
  /-- Expecting the LF after chunk data. -/
  | dataLF
  /-- In the trailer section, after `count` fields. -/
  | trailer (fl : FieldLine) (count : Nat)
deriving Repr, Inhabited, DecidableEq

/--
What one byte of a chunked body leads to.
-/
inductive ChunkResult where
  /-- The body goes on; this byte was framing. -/
  | more (c : ChunkState)
  /-- The body goes on; this byte was body data. -/
  | data (c : ChunkState)
  /-- The body ended with this byte. -/
  | ended
  /-- The body is rejected. -/
  | fail (e : Error)
deriving Repr, Inhabited, DecidableEq

/--
Fields that must not appear in a trailer section (RFC 9112 section 6.5, as the vendored machine
lists them), in lower case.
-/
def forbiddenTrailers : List (List UInt8) :=
  ["content-length", "transfer-encoding", "host", "connection", "expect", "te", "authorization",
    "max-forwards", "cache-control", "content-encoding", "upgrade", "trailer"].map ascii

/--
Reads one byte of a chunked body.  `room` is how many more body bytes the limit allows; a chunk that
would exceed it is rejected as soon as its size line ends.
-/
def stepChunk (cfg : Config) (room : Nat) (c : ChunkState) (b : UInt8) : ChunkResult :=
  match c with
  | .line cl =>
    match stepChunkLine cfg cl b with
    | .more cl => .more (.line cl)
    | .bad => .fail .badMessage
    | .done 0 => .more (.trailer {} 0)
    | .done (n + 1) => if n + 1 ≤ room then .more (.data (n + 1)) else .fail .bodyTooLarge
  | .data r => .data (if r ≤ 1 then .dataCR else .data (r - 1))
  | .dataCR => if b == cr then .more .dataLF else .fail .badMessage
  | .dataLF => if b == lf then .more (.line {}) else .fail .badMessage
  | .trailer fl count =>
    match stepFieldLine cfg fl b with
    | .more fl => .more (.trailer fl count)
    | .bad => .fail .badMessage
    | .blank => .ended
    | .field name _ _ =>
      if forbiddenTrailers.contains (name.map toLower) then .fail .badMessage
      else if cfg.maxTrailerHeaders ≤ count then .fail .badMessage
      else .more (.trailer {} (count + 1))

/-! ## Encoding -/

/--
The ASCII hex digit for `d < 16` (lower case).
-/
def hexChar (d : Nat) : UInt8 :=
  if d < 10 then (48 + d).toUInt8 else (87 + d).toUInt8

/--
The hex digits of `n`, most significant first, with no leading zeros (one digit for `n < 16`).
-/
def hexDigits (n : Nat) : List UInt8 :=
  if n < 16 then [hexChar n] else hexDigits (n / 16) ++ [hexChar (n % 16)]
termination_by n
decreasing_by omega

/--
One chunk on the wire: its size line, its data and CRLF.  Only for non-empty data, since an empty
chunk would end the body.
-/
def encodeChunk (data : List UInt8) : List UInt8 :=
  hexDigits data.length ++ [cr, lf] ++ data ++ [cr, lf]

/--
A chunked body carrying `chunks` in order: each non-empty one as a chunk, then the last chunk and an
empty trailer section.
-/
def encodeChunkedList (chunks : List (List UInt8)) : List UInt8 :=
  (chunks.filter (!·.isEmpty)).flatMap encodeChunk ++ [48, cr, lf, cr, lf]

/--
A chunked body carrying `chunks` in order.
-/
def encodeChunked (chunks : List ByteArray) : ByteArray :=
  ByteArray.mk (encodeChunkedList (chunks.map (·.data.toList))).toArray

end LeanHttp.Codec
