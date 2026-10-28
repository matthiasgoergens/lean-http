module

public import LeanHttp.Codec.Basic

@[expose] public section

/-!
# What a response head's fields mean

The framing of the body (RFC 9112 section 6.3, with the strictness of the vendored machine), whether
the connection may stay open, and the conversion of a head to `Std.Http`'s types.  All of it works
on the bytes of the fields as received, so that proofs can see what each decision depends on.

The rules match `Message.Head.getSize`, `checkSendingMessageHead` and
`Message.Head.shouldKeepAlive` in the vendored machine:

- a `Content-Length` must be the only one, and all digits;
- a `Transfer-Encoding` must be the only one, end in `chunked` (once), come without a
  `Content-Length`, and not be in an HTTP/1.0 response;
- a response with neither is delimited by the end of the input;
- a response to HEAD, and a 1xx, 204 or 304 response, has no body whatever its framing fields say,
  but malformed or contradictory framing fields are rejected all the same.

On top of these, a chunked body whose `Transfer-Encoding` names another coding before `chunked` is
rejected once its head is reported (`onlyChunked`), as the exchange core does, until the client can
decode transfer codings.
-/

namespace LeanHttp.Codec

set_option linter.all true

open Std.Http

/-! ## Token lists -/

/--
Splits at every comma; an empty list gives one empty part, as `String.split` does.
-/
def splitComma : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: bs =>
    match splitComma bs with
    | [] => [[b]]
    | part :: parts => if b == 44 then [] :: part :: parts else (b :: part) :: parts

/--
Removes the whitespace at both ends.
-/
def trimWs (xs : List UInt8) : List UInt8 :=
  ((xs.dropWhile isWs).reverse.dropWhile isWs).reverse

/--
A comma-separated list of tokens, each trimmed and in lower case; `none` if any element is empty or
not a token.
-/
def tokenList (v : List UInt8) : Option (List (List UInt8)) :=
  let parts := (splitComma v).map fun part => (trimWs part).map toLower
  if parts.all (fun part => !part.isEmpty && part.all isTChar) then some parts else none

/--
Whether a field has this name, given in lower case.
-/
def Field.isNamed (f : Field) (lower : List UInt8) : Bool :=
  f.name.map toLower == lower

/-- `content-length` -/
def contentLengthName : List UInt8 := ascii "content-length"
/-- `transfer-encoding` -/
def transferEncodingName : List UInt8 := ascii "transfer-encoding"
/-- `connection` -/
def connectionName : List UInt8 := ascii "connection"
/-- `chunked` -/
def chunkedName : List UInt8 := ascii "chunked"

/-! ## Framing -/

/--
A decimal number of one or more digits.
-/
def parseDecimal (v : List UInt8) : Option Nat :=
  if v.isEmpty then none
  else v.foldl (fun acc b => acc.bind fun n => (digitVal? b).map (n * 10 + ·)) (some 0)

/--
Whether a `Transfer-Encoding` value is a valid list of codings ending in `chunked`, with `chunked`
nowhere else.
-/
def endsChunked (v : List UInt8) : Bool :=
  match tokenList v with
  | some codings => codings.getLast? == some chunkedName && codings.count chunkedName == 1
  | none => false

/--
Whether the head's one `Transfer-Encoding` field is exactly `chunked`.  A chunked body with any other
coding before it would reach the caller still coded, so the parser refuses it (`startBody`).
-/
def onlyChunked (fields : List Field) : Bool :=
  match fields.filter (·.isNamed transferEncodingName) with
  | [te] => tokenList te.value == some [chunkedName]
  | _ => false

/--
What the framing fields of a head declare, before the method and status are considered.
-/
inductive Declared where
  /-- Neither `Content-Length` nor `Transfer-Encoding`. -/
  | none
  /-- One valid `Content-Length`. -/
  | length (n : Nat)
  /-- One valid `Transfer-Encoding` ending in `chunked`, in an HTTP/1.1 response. -/
  | chunked
  /-- Anything else: malformed, repeated or contradictory framing fields. -/
  | invalid
deriving Repr, Inhabited, DecidableEq

/--
What the framing fields of a head declare.
-/
def declared (http10 : Bool) (fields : List Field) : Declared :=
  let lengths := fields.filter (·.isNamed contentLengthName)
  let codings := fields.filter (·.isNamed transferEncodingName)
  match codings, lengths with
  | [], [] => .none
  | [], [cl] =>
    match parseDecimal cl.value with
    | some n => .length n
    | Option.none => .invalid
  | [te], [] => if endsChunked te.value && !http10 then .chunked else .invalid
  | _, _ => .invalid

/--
`true` for a status whose response never has a body: 1xx, 204 and 304.
-/
def noBodyStatus (code : Nat) : Bool :=
  (100 ≤ code && code < 200) || code == 204 || code == 304

/--
The framing of a response, or `none` if its framing fields are invalid (which rejects it).
-/
def framingOf (isHead : Bool) (code : Nat) (http10 : Bool) (fields : List Field) : Option Framing :=
  match declared http10 fields with
  | .invalid => Option.none
  | .none => some (if isHead || noBodyStatus code then .none else .untilClose)
  | .length n => some (if isHead || noBodyStatus code then .none else .length n)
  | .chunked => some (if isHead || noBodyStatus code then .none else .chunked)

/-! ## Keep-alive -/

/--
The tokens of every `Connection` field, or `none` if any of them is malformed.
-/
def connectionTokens (fields : List Field) : Option (List (List UInt8)) :=
  fields.foldl (init := some []) fun acc f =>
    if f.isNamed connectionName then
      acc.bind fun tokens => (tokenList f.value).map (tokens ++ ·)
    else acc

/--
Whether a response allows the connection to stay open (RFC 9112 section 9.3): not if it says
`Connection: close`, whatever its version; otherwise an HTTP/1.1 response does, and an HTTP/1.0
response only if it says `Connection: keep-alive`; and neither if a `Connection` field is malformed.

The vendored machine checks `close` only in HTTP/1.1 responses, so it keeps an HTTP/1.0 connection
that says both `keep-alive` and `close`; this parser does not.
-/
def keepAliveOf (http10 : Bool) (fields : List Field) : Bool :=
  match connectionTokens fields with
  | none => false
  | some tokens =>
    !tokens.contains (ascii "close") && (!http10 || tokens.contains (ascii "keep-alive"))

/-! ## Conversion to `Std.Http` -/

/--
ASCII bytes as a string.
-/
def asString? (bytes : List UInt8) : Option String :=
  String.fromUTF8? (ByteArray.mk bytes.toArray)

/--
The head in `Std.Http`'s types, or `none` if a part of it is not representable there (which the
line automata rule out; the parser rejects the response if it happens anyway).
-/
def toResponseHead? (code : Nat) (http10 : Bool) (reason : List UInt8) (fields : List Field) :
    Option Response.Head := do
  let phrase ← asString? reason
  let status ←
    if h : IsValidReasonPhrase phrase then Status.ofCode (some ⟨phrase, h⟩) code.toUInt16 else none
  let headers ← fields.foldlM (init := Headers.empty) fun headers f => do
    let name ← asString? f.name >>= Header.Name.ofString?
    let value ← asString? f.value >>= Header.Value.ofString?
    pure (headers.insert name value)
  pure { status, version := if http10 then .v10 else .v11, headers }

end LeanHttp.Codec
