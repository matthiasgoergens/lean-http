module

public import Std.Http.Data
public import LeanHttp.Codec.Chunked

@[expose] public section

/-!
# Encoding a request

The client's request serialiser: a request head and a body with a `Content-Length`, or a head for a
body of unknown size sent with `Transfer-Encoding: chunked`, in HTTP/1.1, and the chunks of such a
body.
It makes the same bytes as the vendored HTTP/1.1 machine's writer did for the requests the client
sends, except for one field (`codec-diff` compares the two on generated heads), and decides the same
request-side keep-alive:

- the framing fields of the head are replaced by a `Content-Length` for the body, which is left out
  for an empty body when the method does not anticipate content (RFC 9110 section 8.6), or by
  `Transfer-Encoding: chunked` for a body whose size is not known in advance;
- the head's `Connection` fields are replaced by `Connection: close`, or by `Connection: keep-alive`
  if the connection is to be kept alive, which needs keep-alive asked for and a head that allows it
  (RFC 9112 section 9.3: in HTTP/1.1 no `close` option, in HTTP/1.0 a `keep-alive` option).

The machine's writer sent no `Connection` field at all for a kept-alive request.  In HTTP/1.1 that
asks for keep-alive too, but an HTTP/1.0 request without `keep-alive` asks the server to close, and
some servers and proxies that speak HTTP/1.0 keep a connection open only when asked to, so the
serialiser always says which it wants.

Like the response codec, it depends only on `Std.Http`'s data types.
-/

namespace LeanHttp.Codec

set_option linter.all true

open Std.Http

/--
`false` for the methods whose semantics do not anticipate request content (RFC 9110 section 8.6).
-/
def anticipatesContent (m : Method) : Bool :=
  !(m == .get || m == .head || m == .delete || m == .options || m == .trace || m == .connect)

/--
Whether a request head lets the connection stay open after its exchange, by its version and its
`Connection` fields.  A `Connection` value that is not a list of tokens counts as `close`.
-/
def requestKeepAlive (head : Request.Head) : Bool :=
  let tokens? : Option (Array String) :=
    match head.headers.getAll? Header.Name.connection with
    | none => some #[]
    | some values =>
      values.foldl (init := some #[]) fun acc raw => do
        let acc ← acc
        let parsed ← Header.Connection.parse raw
        pure (acc ++ parsed.tokens)
  match tokens? with
  | none => false
  | some tokens =>
    if head.version == .v11 then !tokens.any (· == "close") else tokens.any (· == "keep-alive")

/--
A request encoded for the wire.
-/
structure EncodedRequest where
  /--
  The head, then the body.
  -/
  bytes : ByteArray

  /--
  The length of the head at the start of `bytes`.
  -/
  headBytes : Nat

  /--
  Whether the request asks for the connection to stay open: keep-alive was asked for and the head
  allows it.  The head carries `Connection: keep-alive` if so, `Connection: close` if not.
  -/
  keepAlive : Bool

/--
How a request body is framed on the wire.
-/
inductive RequestFraming where
  /--
  A `Content-Length` of `size` bytes.
  -/
  | length (size : Nat)

  /--
  `Transfer-Encoding: chunked` (RFC 9112 section 7.1): the size is not known in advance.  HTTP/1.1
  only.
  -/
  | chunked
deriving Repr, Inhabited, DecidableEq

/--
Encodes the head of a request whose body is framed by `framing`, and says whether it asks for the
connection to stay open.  `keepAlive` says whether the caller wants the connection kept open; the
head's own fields may still refuse it (`requestKeepAlive`).  The fields are changed in the order the
vendored writer changed them, so that the bytes are the same for a `Content-Length`.
-/
def encodeHeadWith (keepAlive : Bool) (head : Request.Head) (framing : RequestFraming) :
    ByteArray × Bool :=
  let keepAlive := keepAlive && requestKeepAlive head
  let headers := head.headers
    |>.erase Header.Name.contentLength
    |>.erase Header.Name.transferEncoding
    |>.erase Header.Name.connection
  let headers :=
    headers.insert Header.Name.connection (if keepAlive then .mk "keep-alive" else .mk "close")
  let headers :=
    match framing with
    | .length bodySize =>
      if bodySize == 0 && !anticipatesContent head.method then headers
      else
        headers
          |>.erase Header.Name.contentLength
          |>.erase Header.Name.transferEncoding
          |>.insert Header.Name.contentLength (.ofString! (toString bodySize))
    | .chunked =>
      headers
        |>.erase Header.Name.contentLength
        |>.erase Header.Name.transferEncoding
        |>.insert Header.Name.transferEncoding (.mk "chunked")
  ((Internal.Encode.encode (v := .v11) Internal.ChunkedBuffer.empty { head with headers }).toByteArray,
    keepAlive)

/--
Encodes the head of a request with a body of `bodySize` bytes (`encodeHeadWith` with a
`Content-Length`).
-/
def encodeHead (keepAlive : Bool) (head : Request.Head) (bodySize : Nat) : ByteArray × Bool :=
  encodeHeadWith keepAlive head (.length bodySize)

/--
Encodes `head` with `body` (`encodeHead`, then the body).
-/
def encodeRequest (keepAlive : Bool) (head : Request.Head) (body : ByteArray) : EncodedRequest :=
  let (headBytes, keepAlive) := encodeHead keepAlive head body.size
  { bytes := headBytes ++ body, headBytes := headBytes.size, keepAlive }

/--
One chunk of a chunked body on the wire: its size line, its data and CRLF, as `encodeChunk` lays
it out (`chunkFrame_data`).  Only for non-empty data, since an empty chunk would end the body.
-/
def chunkFrame (data : ByteArray) : ByteArray :=
  ByteArray.mk (hexDigits data.size ++ [cr, lf]).toArray ++ data ++ ByteArray.mk #[cr, lf]

/--
The end of a chunked body: the last chunk and an empty trailer section.
-/
def lastChunk : ByteArray :=
  ByteArray.mk #[48, cr, lf, cr, lf]

end LeanHttp.Codec
