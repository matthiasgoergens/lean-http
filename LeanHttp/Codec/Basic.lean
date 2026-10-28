module

public import Std.Http.Data

@[expose] public section

/-!
# The response codec: basic definitions

Limits, errors, byte classes, the framing of a response body, the head the parser reports, and the
events it emits.  The parser itself is in `LeanHttp.Codec.Response`.

The codec depends only on `Std.Http`'s data types, not on the vendored protocol layer, so that it
can outlive the vendored copy.
-/

namespace LeanHttp.Codec

set_option linter.all true

open Std.Http

/--
The parser's limits.  The defaults are those of the vendored HTTP/1.1 machine
(`LeanHttpProto.Http.Protocol.H1.Config`) and of the exchange core (`maxInterim`, `maxBody`).
-/
structure Config where
  /--
  Most header fields in one response head.
  -/
  maxHeaders : Nat := 100

  /--
  Most bytes of header field lines in one response head, counting each line with its CRLF.
  -/
  maxHeaderBytes : Nat := 65536

  /--
  Longest header field name.
  -/
  maxHeaderNameLength : Nat := 256

  /--
  Longest header field value, counting the whitespace that ends it.
  -/
  maxHeaderValueLength : Nat := 8192

  /--
  Longest run of optional whitespace.
  -/
  maxSpaceSequence : Nat := 16

  /--
  Longest reason phrase.
  -/
  maxReasonPhraseLength : Nat := 512

  /--
  Most extensions on one chunk-size line.
  -/
  maxChunkExtensions : Nat := 16

  /--
  Longest chunk extension name.
  -/
  maxChunkExtNameLength : Nat := 256

  /--
  Longest chunk extension value (after unescaping, for a quoted string).
  -/
  maxChunkExtValueLength : Nat := 256

  /--
  Longest chunk-size line, counting its CRLF.
  -/
  maxChunkLineLength : Nat := 8192

  /--
  Most fields in the trailer section of a chunked body.
  -/
  maxTrailerHeaders : Nat := 20

  /--
  Most interim (1xx) responses before the final one.
  -/
  maxInterim : Nat := 10

  /--
  Largest body accepted, in decoded bytes.
  -/
  maxBody : Nat := 64 * 1024 * 1024
deriving Repr, Inhabited, DecidableEq

/--
Why the parser rejected a response.
-/
inductive Error where
  /--
  The bytes are not a well-formed HTTP/1.1 response, or its framing fields are missing, malformed
  or contradictory.
  -/
  | badMessage

  /--
  The status line names a version other than HTTP/1.0 and HTTP/1.1.
  -/
  | unsupportedVersion

  /--
  More header fields than `Config.maxHeaders`.
  -/
  | tooManyHeaders

  /--
  More header bytes than `Config.maxHeaderBytes`.
  -/
  | headersTooLarge

  /--
  A body larger than `Config.maxBody`, declared or delivered.
  -/
  | bodyTooLarge

  /--
  More interim responses than `Config.maxInterim`.
  -/
  | tooManyInterim

  /--
  A `101 Switching Protocols` response, which a client that asked for no upgrade must refuse.
  -/
  | switchingProtocols

  /--
  The body has a transfer coding other than chunked (`Transfer-Encoding: gzip, chunked`, say), which
  the client cannot decode; reported after the head, as the exchange core does.
  -/
  | unsupportedCoding

  /--
  The input ended before the response did.
  -/
  | closed
deriving Repr, Inhabited, DecidableEq

/--
How the end of a response body is marked.
-/
inductive Framing where
  /--
  The response has no body: it answers a HEAD request, or its status is 204 or 304.
  -/
  | none

  /--
  The body has a `Content-Length` of this many bytes.
  -/
  | length (bytes : Nat)

  /--
  The body is chunked.
  -/
  | chunked

  /--
  The body ends when the input does.
  -/
  | untilClose
deriving Repr, Inhabited, DecidableEq

namespace Framing

/--
`true` when the end of the body is marked in the bytes themselves, so that it is known without the
input ending.
-/
def certain : Framing → Bool
  | .untilClose => false
  | _ => true

end Framing

/--
A header field as received: its name, and its value without the surrounding whitespace.
-/
structure Field where
  /--
  The field name, as received (not case-folded).
  -/
  name : List UInt8

  /--
  The field value, without leading or trailing whitespace.
  -/
  value : List UInt8
deriving Repr, Inhabited, DecidableEq

/--
The final response head, as the parser reports it.
-/
structure Head where
  /--
  The status code: three digits, at least 200 (interim responses are never reported as heads).
  -/
  code : Nat

  /--
  Whether the status line said HTTP/1.0 (otherwise it said HTTP/1.1).
  -/
  http10 : Bool

  /--
  The reason phrase.
  -/
  reason : List UInt8

  /--
  The header fields, in the order received.
  -/
  fields : List Field

  /--
  How the body is framed, given the request method.
  -/
  framing : Framing

  /--
  Whether this response and every interim response before it allow the connection to stay open
  (by their version and `Connection` fields).
  -/
  keepAlive : Bool

  /--
  How many interim responses preceded this one.
  -/
  interim : Nat

  /--
  The same head in `Std.Http`'s types.
  -/
  response : Response.Head
deriving Inhabited

/--
What the parser reports, in order.
-/
inductive Event where
  /--
  The final response head arrived.
  -/
  | head (h : Head)

  /--
  These bytes of the body arrived.
  -/
  | body (bytes : ByteArray)

  /--
  The response ended.
  -/
  | done

  /--
  The response was rejected.
  -/
  | error (e : Error)
deriving Inhabited

/-! ## Byte classes (RFC 9110 section 5.6, ASCII only) -/

/-- Carriage return. -/
abbrev cr : UInt8 := 13
/-- Line feed. -/
abbrev lf : UInt8 := 10

/--
`tchar`: a byte that may appear in a token.
-/
def isTChar (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) ||
    b == 33 || b == 35 || b == 36 || b == 37 || b == 38 || b == 39 || b == 42 || b == 43 ||
    b == 45 || b == 46 || b == 94 || b == 95 || b == 96 || b == 124 || b == 126

/--
`VCHAR`: a visible ASCII character.
-/
def isVChar (b : UInt8) : Bool :=
  33 ≤ b && b ≤ 126

/--
Optional whitespace: a space or a horizontal tab.
-/
def isWs (b : UInt8) : Bool :=
  b == 32 || b == 9

/--
`field-content` (ASCII only): a byte that may appear in a field value or a reason phrase.
-/
def isFieldContent (b : UInt8) : Bool :=
  isVChar b || isWs b

/--
`qdtext` (ASCII only): a byte that may appear unescaped in a quoted string.
-/
def isQdText (b : UInt8) : Bool :=
  b == 9 || b == 32 || b == 33 || (35 ≤ b && b ≤ 91) || (93 ≤ b && b ≤ 126)

/--
A byte that may follow a backslash in a quoted string.
-/
def isQuotedPairChar (b : UInt8) : Bool :=
  isWs b || isVChar b

/--
The value of an ASCII decimal digit.
-/
def digitVal? (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48) else none

/--
The value of an ASCII hexadecimal digit.
-/
def hexVal? (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48)
  else if 65 ≤ b && b ≤ 70 then some (b.toNat - 55)
  else if 97 ≤ b && b ≤ 102 then some (b.toNat - 87)
  else none

/--
ASCII lower case.
-/
def toLower (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b + 32 else b

/--
The bytes of an ASCII string.
-/
def ascii (s : String) : List UInt8 :=
  s.toList.map Char.toUInt8

end LeanHttp.Codec
