import LeanHttpProto.Http.Protocol.H1

/-!
# Response shapes for the codec tests

The responses `Tests/Codec.lean` drives through the exchange core and the vendored HTTP/1.1 machine,
and `Tests/ResponseCodec.lean` through the response codec (`LeanHttp.Codec`), with the outcome each
must have in every way of splitting it.
-/

open Std.Http

/-- The request every case answers, unless it says otherwise. -/
def requestHead (method : Method) : Request.Head :=
  { method, version := .v11, uri := .originForm { segments := #[], absolute := true } none,
    headers := Headers.empty.insert Header.Name.host (.mk "example.test") }

/-- Limits small enough to be hit by short test inputs. -/
structure Limits where
  maxInterim : Nat := 10
  maxBody : Nat := 1024
  h1 : LeanHttpProto.Http.Protocol.H1.Config := {}

/-- Every way of feeding `bytes` that the tests try, with a label. -/
def splits (bytes : ByteArray) (allPairs : Bool) : List (String × List ByteArray) :=
  let whole := ("whole", [bytes])
  let single := ("bytewise", (List.range bytes.size).map fun i => bytes.extract i (i + 1))
  let pairs :=
    if allPairs then
      (List.range (bytes.size + 1)).map fun i =>
        (s!"split@{i}", [bytes.extract 0 i, bytes.extract i bytes.size])
    else []
  whole :: single :: pairs

/-- One test case. -/
structure Shape where
  name : String
  method : Method := .get
  response : String
  eof : Bool := true
  limits : Limits := {}
  /-- The expected rendering, or `none` to only record what happens. -/
  expect : Option String

def cases : List Shape := [
  { name := "content-length"
    response := "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello"
    expect := some "done 200 interim=0 body=\"hello\"" },
  { name := "content-length, no eof needed"
    response := "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello"
    eof := false
    expect := some "done 200 interim=0 body=\"hello\"" },
  { name := "chunked"
    response := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n"
    eof := false
    expect := some "done 200 interim=0 body=\"hello world\"" },
  { name := "chunked with extensions"
    response := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5;a=1;b=\"x y\"\r\nhello\r\n0;end\r\n\r\n"
    eof := false
    expect := some "done 200 interim=0 body=\"hello\"" },
  { name := "chunked with trailers"
    response := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\nX-Checksum: abc\r\nX-Other: d\r\n\r\n"
    eof := false
    expect := some "done 200 interim=0 body=\"hello\"" },
  { name := "close-delimited"
    response := "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\nabc"
    expect := some "done 200 interim=0 body=\"abc\"" },
  { name := "close-delimited, before eof"
    response := "HTTP/1.1 200 OK\r\n\r\nabc"
    eof := false
    expect := some "pending" },
  { name := "HTTP/1.0 close-delimited"
    response := "HTTP/1.0 200 OK\r\n\r\nold"
    expect := some "done 200 interim=0 body=\"old\"" },
  { name := "HEAD with Content-Length"
    method := .head
    response := "HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\n"
    eof := false
    expect := some "done 200 interim=0 body=\"\"" },
  { name := "HEAD with chunked"
    method := .head
    response := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n"
    eof := false
    expect := some "done 200 interim=0 body=\"\"" },
  { name := "204 with Content-Length"
    response := "HTTP/1.1 204 No Content\r\nContent-Length: 5\r\n\r\n"
    eof := false
    expect := some "done 204 interim=0 body=\"\"" },
  { name := "304 with Content-Length"
    response := "HTTP/1.1 304 Not Modified\r\nContent-Length: 100\r\n\r\n"
    eof := false
    expect := some "done 304 interim=0 body=\"\"" },
  { name := "interim responses"
    response := "HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 103 Early Hints\r\nLink: </a>\r\n\r\nHTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok"
    eof := false
    expect := some "done 200 interim=2 body=\"ok\"" },
  { name := "interim limit (11 > 10)"
    response := String.join (List.replicate 11 "HTTP/1.1 102 Processing\r\n\r\n") ++ "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
    eof := false
    expect := some "failed LeanHttp.Cause.limit (LeanHttp.LimitKind.interim)" },
  { name := "interim at the limit (10)"
    response := String.join (List.replicate 10 "HTTP/1.1 102 Processing\r\n\r\n") ++ "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
    eof := false
    expect := some "done 200 interim=10 body=\"\"" },
  { name := "101 without upgrade"
    response := "HTTP/1.1 101 Switching Protocols\r\nUpgrade: x\r\nConnection: upgrade\r\n\r\n"
    eof := false
    expect := some "failed LeanHttp.Cause.protocol \"101 Switching Protocols, but no upgrade was requested\"" },
  { name := "malformed status code"
    response := "HTTP/1.1 2x0 OK\r\nContent-Length: 0\r\n\r\n"
    expect := some "failed LeanHttp.Cause.protocol \"Bad message\"" },
  { name := "not HTTP"
    response := "SSH-2.0-OpenSSH_9.6\r\n"
    expect := some "failed LeanHttp.Cause.protocol \"Bad message\"" },
  { name := "HTTP/2.0 status line"
    response := "HTTP/2.0 200 OK\r\nContent-Length: 0\r\n\r\n"
    expect := some "failed LeanHttp.Cause.protocol \"Unsupported version\"" },
  { name := "status line without reason phrase or space"
    response := "HTTP/1.1 200\r\nContent-Length: 2\r\n\r\nok"
    expect := none },
  { name := "status line with empty reason phrase"
    response := "HTTP/1.1 200 \r\nContent-Length: 2\r\n\r\nok"
    expect := some "done 200 interim=0 body=\"ok\"" },
  { name := "bare LF line endings"
    response := "HTTP/1.1 200 OK\nContent-Length: 2\n\nok"
    expect := none },
  { name := "obsolete line folding"
    response := "HTTP/1.1 200 OK\r\nX-A: one\r\n two\r\nContent-Length: 2\r\n\r\nok"
    expect := none },
  { name := "conflicting Content-Length"
    response := "HTTP/1.1 200 OK\r\nContent-Length: 2\r\nContent-Length: 3\r\n\r\nokk"
    expect := some "failed LeanHttp.Cause.protocol \"Bad message\"" },
  { name := "Content-Length with Transfer-Encoding"
    response := "HTTP/1.1 200 OK\r\nContent-Length: 2\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n"
    expect := some "failed LeanHttp.Cause.protocol \"Bad message\"" },
  { name := "too many header fields (3 > 2)"
    response := "HTTP/1.1 200 OK\r\nA: 1\r\nB: 2\r\nC: 3\r\nContent-Length: 0\r\n\r\n"
    limits := { h1 := { maxHeaders := 2 } }
    expect := some "failed LeanHttp.Cause.limit (LeanHttp.LimitKind.headers)" },
  { name := "header bytes over the limit"
    response := "HTTP/1.1 200 OK\r\nA: " ++ String.ofList (List.replicate 100 'x') ++ "\r\nContent-Length: 0\r\n\r\n"
    limits := { h1 := { maxHeaderBytes := 64 } }
    expect := some "failed LeanHttp.Cause.limit (LeanHttp.LimitKind.headers)" },
  { name := "body over the limit (Content-Length)"
    response := "HTTP/1.1 200 OK\r\nContent-Length: 2000\r\n\r\n"
    eof := false
    expect := some "failed LeanHttp.Cause.limit (LeanHttp.LimitKind.body)" },
  { name := "body over the limit (chunked)"
    response := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n" ++ String.join (List.replicate 3 ("190\r\n" ++ String.ofList (List.replicate 400 'y') ++ "\r\n"))
    eof := false
    limits := { maxBody := 1000 }
    expect := some "failed LeanHttp.Cause.limit (LeanHttp.LimitKind.body)" },
  { name := "body over the limit (close-delimited)"
    response := "HTTP/1.1 200 OK\r\n\r\n" ++ String.ofList (List.replicate 1100 'z')
    eof := false
    expect := some "failed LeanHttp.Cause.limit (LeanHttp.LimitKind.body)" },
  { name := "eof before any byte"
    response := ""
    expect := some "failed LeanHttp.Cause.peerClosed" },
  { name := "eof in the status line"
    response := "HTTP/1.1 20"
    expect := some "failed LeanHttp.Cause.peerClosed" },
  { name := "eof in the headers"
    response := "HTTP/1.1 200 OK\r\nContent-Len"
    expect := some "failed LeanHttp.Cause.peerClosed" },
  { name := "eof in a Content-Length body"
    response := "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nhello"
    expect := some "failed LeanHttp.Cause.peerClosed" },
  { name := "eof in a chunked body"
    response := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhel"
    expect := some "failed LeanHttp.Cause.peerClosed" },
  { name := "eof before the last chunk"
    response := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n"
    expect := some "failed LeanHttp.Cause.peerClosed" },
  { name := "eof in the trailers"
    response := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\nX-T: 1\r\n"
    expect := some "failed LeanHttp.Cause.peerClosed" }
]
