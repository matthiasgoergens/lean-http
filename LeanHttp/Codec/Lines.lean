module

public import LeanHttp.Codec.Basic

@[expose] public section

/-!
# Line automata

The three kinds of line in a response, each read one byte at a time by a step function with no
loops: the status line, a header or trailer field line, and a chunk-size line.  Each step either
asks for the next byte (`more`), reports a complete line, or rejects the line.

A byte is rejected as soon as no continuation could make the line valid, and a line ends only at
CRLF (a bare LF is rejected).  The grammar and the limits are those the vendored HTTP/1.1 machine
enforces (`LeanHttpProto.Http.Protocol.H1.Parser`), including its quirks: OWS runs are limited to
`Config.maxSpaceSequence`, a field value ends at `Config.maxHeaderValueLength` bytes (whitespace
counted) after which only OWS and CRLF may follow, and a chunk-size line has at most 16 hex digits.

Buffers are lists in reverse, so that adding a byte costs the same whether or not the state is
shared.
-/

namespace LeanHttp.Codec

set_option linter.all true

/-! ## The status line -/

/--
Where the status line reader stands.
-/
inductive StatusSt where
  /-- `k` bytes of `HTTP/` matched. -/
  | expect (k : Nat)
  /-- Expecting the major version digit. -/
  | major
  /-- Expecting the dot. -/
  | dot
  /-- Expecting the minor version digit. -/
  | minor
  /-- Expecting the space before the status code. -/
  | sp1
  /-- `k` digits of the status code read. -/
  | code (k : Nat)
  /-- Expecting the space before the reason phrase. -/
  | sp2
  /-- In the reason phrase. -/
  | reason
  /-- After the CR that ends the line. -/
  | lf
deriving Repr, Inhabited, DecidableEq

/--
The status line read so far.
-/
structure StatusLine where
  /-- Where the reader stands. -/
  st : StatusSt := .expect 0
  /-- The major version digit. -/
  major : Nat := 0
  /-- The minor version digit. -/
  minor : Nat := 0
  /-- The status code. -/
  code : Nat := 0
  /-- The reason phrase, in reverse. -/
  reason : List UInt8 := []
  /-- The length of the reason phrase. -/
  reasonLen : Nat := 0
deriving Repr, Inhabited, DecidableEq

/--
What one byte of a status line leads to.
-/
inductive StatusResult where
  /-- The line goes on. -/
  | more (sl : StatusLine)
  /-- The line ended with this byte. -/
  | done (sl : StatusLine)
  /-- The line is malformed. -/
  | bad
deriving Repr, Inhabited, DecidableEq

/--
The bytes of `HTTP/`.
-/
def httpName : Nat → UInt8
  | 0 => 72
  | 1 => 84
  | 2 => 84
  | 3 => 80
  | _ => 47

/--
Reads one byte of a status line: `HTTP-version SP 3DIGIT SP reason-phrase CRLF`.  The version and
the code are checked once the line is complete, by the caller.
-/
def stepStatusLine (cfg : Config) (sl : StatusLine) (b : UInt8) : StatusResult :=
  match sl.st with
  | .expect k =>
    if b == httpName k then .more { sl with st := if k < 4 then .expect (k + 1) else .major }
    else .bad
  | .major =>
    match digitVal? b with
    | some d => .more { sl with st := .dot, major := d }
    | none => .bad
  | .dot => if b == 46 then .more { sl with st := .minor } else .bad
  | .minor =>
    match digitVal? b with
    | some d => .more { sl with st := .sp1, minor := d }
    | none => .bad
  | .sp1 => if b == 32 then .more { sl with st := .code 0 } else .bad
  | .code k =>
    match digitVal? b with
    | some d => .more { sl with st := if k < 2 then .code (k + 1) else .sp2, code := sl.code * 10 + d }
    | none => .bad
  | .sp2 => if b == 32 then .more { sl with st := .reason } else .bad
  | .reason =>
    if b == cr then .more { sl with st := .lf }
    else if isFieldContent b && sl.reasonLen < cfg.maxReasonPhraseLength then
      .more { sl with reason := b :: sl.reason, reasonLen := sl.reasonLen + 1 }
    else .bad
  | .lf => if b == lf then .done sl else .bad

/-! ## Field lines -/

/--
Where a field line reader stands.
-/
inductive FieldSt where
  /-- At the start of a line. -/
  | start
  /-- After a CR at the start of a line: the empty line that ends a section. -/
  | blankLF
  /-- In the field name. -/
  | name
  /-- After the colon, `k` bytes of whitespace read. -/
  | leadOws (k : Nat)
  /-- In the field value. -/
  | value
  /-- After a value of the greatest length, `k` bytes of whitespace read. -/
  | trailOws (k : Nat)
  /-- After the CR that ends the line. -/
  | lf
deriving Repr, Inhabited, DecidableEq

/--
A field line read so far.
-/
structure FieldLine where
  /-- Where the reader stands. -/
  st : FieldSt := .start
  /-- The name, in reverse. -/
  name : List UInt8 := []
  /-- The length of the name. -/
  nameLen : Nat := 0
  /-- The value, in reverse, with any trailing whitespace. -/
  value : List UInt8 := []
  /-- The length of the value. -/
  valueLen : Nat := 0
  /-- The bytes of the line read so far. -/
  bytes : Nat := 0
deriving Repr, Inhabited, DecidableEq

/--
What one byte of a field line leads to.
-/
inductive FieldResult where
  /-- The line goes on. -/
  | more (fl : FieldLine)
  /-- A field line ended with this byte; `bytes` counts the whole line with its CRLF. -/
  | field (name value : List UInt8) (bytes : Nat)
  /-- The empty line that ends the section ended with this byte. -/
  | blank
  /-- The line is malformed. -/
  | bad
deriving Repr, Inhabited, DecidableEq

/--
A value without its trailing whitespace, given in reverse.
-/
def trimValue (rev : List UInt8) : List UInt8 :=
  (rev.dropWhile isWs).reverse

/--
Reads one byte of a field value, or the CR that ends it.
-/
def valueByte (cfg : Config) (fl : FieldLine) (b : UInt8) : FieldResult :=
  if b == cr then .more { fl with st := .lf }
  else if isFieldContent b then
    if fl.valueLen < cfg.maxHeaderValueLength then
      .more { fl with st := .value, value := b :: fl.value, valueLen := fl.valueLen + 1 }
    else if isWs b && 0 < cfg.maxSpaceSequence then .more { fl with st := .trailOws 1 }
    else .bad
  else .bad

/--
Reads one byte of a field line, `field-name ":" OWS field-value OWS CRLF`, or of the empty line that
ends the section.  A line that starts with whitespace (obsolete line folding) is rejected.
-/
def stepFieldLine (cfg : Config) (fl : FieldLine) (b : UInt8) : FieldResult :=
  let fl := { fl with bytes := fl.bytes + 1 }
  match fl.st with
  | .start =>
    if b == cr then .more { fl with st := .blankLF }
    else if isTChar b && 0 < cfg.maxHeaderNameLength then
      .more { fl with st := .name, name := [b], nameLen := 1 }
    else .bad
  | .blankLF => if b == lf then .blank else .bad
  | .name =>
    if isTChar b then
      if fl.nameLen < cfg.maxHeaderNameLength then
        .more { fl with name := b :: fl.name, nameLen := fl.nameLen + 1 }
      else .bad
    else if b == 58 then .more { fl with st := .leadOws 0 }
    else .bad
  | .leadOws k =>
    if isWs b then
      if k < cfg.maxSpaceSequence then .more { fl with st := .leadOws (k + 1) } else .bad
    else valueByte cfg fl b
  | .value => valueByte cfg fl b
  | .trailOws k =>
    if isWs b then
      if k < cfg.maxSpaceSequence then .more { fl with st := .trailOws (k + 1) } else .bad
    else if b == cr then .more { fl with st := .lf }
    else .bad
  | .lf => if b == lf then .field fl.name.reverse (trimValue fl.value) fl.bytes else .bad

/-! ## Chunk-size lines -/

/--
Where a chunk-size line reader stands.
-/
inductive ChunkLineSt where
  /-- `digits` hex digits of the size read. -/
  | size (digits : Nat)
  /-- Whitespace before a `;`, `k` bytes read. -/
  | preOws (k : Nat)
  /-- After a `;`, `k` bytes of whitespace read. -/
  | postSemi (k : Nat)
  /-- In an extension name of `len` bytes. -/
  | extName (len : Nat)
  /-- After an extension name, `k` bytes of whitespace read. -/
  | nameOws (k : Nat)
  /-- After an `=`, `k` bytes of whitespace read. -/
  | eqOws (k : Nat)
  /-- In a token value of `len` bytes. -/
  | tokenValue (len : Nat)
  /-- In a quoted value of `len` bytes so far (after unescaping). -/
  | quoted (len : Nat)
  /-- After a backslash in a quoted value of `len` bytes. -/
  | quotedEsc (len : Nat)
  /-- After the closing quote of a value. -/
  | afterValue
  /-- After the CR that ends the line. -/
  | lf
deriving Repr, Inhabited, DecidableEq

/--
A chunk-size line read so far.
-/
structure ChunkLine where
  /-- Where the reader stands. -/
  st : ChunkLineSt := .size 0
  /-- The chunk size read so far. -/
  size : Nat := 0
  /-- The extensions begun so far. -/
  exts : Nat := 0
  /-- The bytes of the line read so far. -/
  bytes : Nat := 0
deriving Repr, Inhabited, DecidableEq

/--
What one byte of a chunk-size line leads to.
-/
inductive ChunkLineResult where
  /-- The line goes on. -/
  | more (cl : ChunkLine)
  /-- The line ended with this byte, announcing a chunk of `size` bytes. -/
  | done (size : Nat)
  /-- The line is malformed. -/
  | bad
deriving Repr, Inhabited, DecidableEq

/--
Reads one more byte of an OWS run of `k` bytes, which goes on in state `next (k + 1)`.
-/
def owsMore (cfg : Config) (cl : ChunkLine) (k : Nat) (next : Nat → ChunkLineSt) :
    ChunkLineResult :=
  if k < cfg.maxSpaceSequence then .more { cl with st := next (k + 1) } else .bad

/--
Begins another extension, after its `;`.
-/
def semicolon (cfg : Config) (cl : ChunkLine) : ChunkLineResult :=
  if cl.exts < cfg.maxChunkExtensions then .more { cl with st := .postSemi 0, exts := cl.exts + 1 }
  else .bad

/--
Reads the byte after the size or an extension, when it is not whitespace: a `;` begins another
extension and a CR ends the line.
-/
def afterExtNoWs (cfg : Config) (cl : ChunkLine) (b : UInt8) : ChunkLineResult :=
  if b == 59 then semicolon cfg cl
  else if b == cr then .more { cl with st := .lf }
  else .bad

/--
Reads the byte after the size or an extension value.  Whitespace here can only precede a `;`.
-/
def afterExt (cfg : Config) (cl : ChunkLine) (b : UInt8) : ChunkLineResult :=
  if isWs b then owsMore cfg cl 0 .preOws else afterExtNoWs cfg cl b

/--
Reads one byte of a chunk-size line:
`1*16HEXDIG *( BWS ";" BWS ext-name [ BWS "=" BWS ( token / quoted-string ) ] ) CRLF`.
-/
def stepChunkLine (cfg : Config) (cl : ChunkLine) (b : UInt8) : ChunkLineResult :=
  if cfg.maxChunkLineLength ≤ cl.bytes then .bad else
  let cl := { cl with bytes := cl.bytes + 1 }
  match cl.st with
  | .size n =>
    match hexVal? b with
    | some d => if n < 16 then .more { cl with st := .size (n + 1), size := cl.size * 16 + d } else .bad
    | none => if n == 0 then .bad else afterExt cfg cl b
  | .preOws k =>
    if isWs b then owsMore cfg cl k .preOws
    else if b == 59 then semicolon cfg cl
    else .bad
  | .postSemi k =>
    if isWs b then owsMore cfg cl k .postSemi
    else if isTChar b && 0 < cfg.maxChunkExtNameLength then .more { cl with st := .extName 1 }
    else .bad
  | .extName len =>
    if isTChar b then
      if len < cfg.maxChunkExtNameLength then .more { cl with st := .extName (len + 1) } else .bad
    else if isWs b then owsMore cfg cl 0 .nameOws
    else if b == 61 then .more { cl with st := .eqOws 0 }
    else afterExtNoWs cfg cl b
  | .nameOws k =>
    if isWs b then owsMore cfg cl k .nameOws
    else if b == 61 then .more { cl with st := .eqOws 0 }
    else afterExtNoWs cfg cl b
  | .eqOws k =>
    if isWs b then owsMore cfg cl k .eqOws
    else if b == 34 then .more { cl with st := .quoted 0 }
    else if isTChar b && 0 < cfg.maxChunkExtValueLength then .more { cl with st := .tokenValue 1 }
    else .bad
  | .tokenValue len =>
    if isTChar b then
      if len < cfg.maxChunkExtValueLength then .more { cl with st := .tokenValue (len + 1) }
      else .bad
    else afterExt cfg cl b
  | .quoted len =>
    if b == 34 then .more { cl with st := .afterValue }
    else if b == 92 then .more { cl with st := .quotedEsc len }
    else if isQdText b && len < cfg.maxChunkExtValueLength then
      .more { cl with st := .quoted (len + 1) }
    else .bad
  | .quotedEsc len =>
    if isQuotedPairChar b && len < cfg.maxChunkExtValueLength then
      .more { cl with st := .quoted (len + 1) }
    else .bad
  | .afterValue => afterExt cfg cl b
  | .lf => if b == lf then .done cl.size else .bad

end LeanHttp.Codec
