import Tests.Support.Check

/-!
# Known defects as traces

Each trace is a fixed sequence of events against the exchange core, with the actions every step
must produce.  The cases are the defects the review of the upstream client found
(`http-client-review.md` in the lean-speed notes) and the hazards of connection reuse the design
names: bytes that arrive before the request is written, a second response after the first, stray
bytes after a HEAD response, an early response during an upload, an abandoned body, end of input
mid-body, a stale tick, and the deadline.
-/

open Std.Http LeanHttp

/-- A fixed sequence of events and the actions each must produce. -/
structure Trace where
  /-- What the trace shows. -/
  name : String
  /-- The exchange's settings. -/
  config : ExchangeConfig := { keepAlive := true }
  /-- The request method. -/
  method : Method := .get
  /-- The request body. -/
  body : String := ""
  /-- The deadline of the exchange, which begins at time 0. -/
  deadline : Nat := 10000
  /-- The actions `begin` must produce, given the prepared request. -/
  begins : PreparedRequest → List String := fun p => [s!"write {p.bytes.size}"]
  /-- Each step: the time, the event, and the actions it must produce. -/
  steps : PreparedRequest → List (Nat × ExchangeEvent × List String)

/-- The request every trace makes. -/
def traceHead (method : Method) : Request.Head :=
  { method, version := .v11, uri := .originForm { segments := #[], absolute := true } none,
    headers := Headers.empty.insert Header.Name.host (.mk "example.test") }

/-- Bytes received, from a string. -/
def recv (s : String) : ExchangeEvent := .received s.toUTF8

/-- More body credit than any trace needs. -/
def lots : ExchangeEvent := .wantBody 1000000

/-- A complete reusable response. -/
def okResponse : String := "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok"

/-- The actions a complete `okResponse` produces on a keep-alive exchange. -/
def okActions : List String := ["head 200", "body \"ok\"", "finish reusable=true"]

/-- A response head with a ten-byte body, and the first five bytes of the body. -/
def tenHello : String := "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nhello"

/-- The head of an early response to an upload, and its three-byte body. -/
def early413 : String := "HTTP/1.1 413 Payload Too Large\r\nContent-Length: 3\r\n\r\n"

/-- A request body of 100 bytes. -/
def upload : String := String.ofList (List.replicate 100 'x')

/-- The first steps of most traces: the request written in one write, and the whole body wanted. -/
def writtenSteps (p : PreparedRequest) (t : Nat := 1) : List (Nat × ExchangeEvent × List String) :=
  [(t, .written p.bytes.size, ["read"]), (t, lots, [])]

/-- The first steps of an upload in 64-byte slices: the head is covered by the first one. -/
def uploadSteps : List (Nat × ExchangeEvent × List String) :=
  [(1, .written 64, ["write 64", "read"]), (1, lots, [])]

/-- The traces. -/
def traces : List Trace := [
  { name := "bytes before the request head is written are never parsed"
    steps := fun _ => [
      (1, recv okResponse,
        ["fail invalid response: bytes arrived before the request head was written [maybe delivered, written=0]"])] },
  { name := "bytes after part of the request head was written are never parsed either"
    config := { keepAlive := true, writeChunk := 16 }
    begins := fun _ => ["write 16"]
    steps := fun _ => [
      (1, .written 16, ["write 16"]),
      (2, recv okResponse,
        ["fail invalid response: bytes arrived before the request head was written [maybe delivered, written=16]"])] },
  { name := "a second response in the same read: the first is delivered, the connection is not reusable"
    steps := fun p => writtenSteps p ++ [
      (2, recv (okResponse ++ "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nno"),
        ["head 200", "body \"ok\"", "finish reusable=false"])] },
  { name := "a second response in a later read: the exchange has ended and ignores it"
    steps := fun p => writtenSteps p ++ [
      (2, recv okResponse, okActions),
      (3, recv "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nno", []),
      (4, .endOfInput, [])] },
  { name := "HEAD with stray body bytes in the same read: not reusable"
    method := .head
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello",
        ["head 200", "finish reusable=false"])] },
  { name := "HEAD, then stray bytes in a later read: the exchange has ended and ignores them"
    method := .head
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n", ["head 200", "finish reusable=true"]),
      (3, recv "hello", [])] },
  { name := "an early response during an upload is read to its end, delivered, and not reusable"
    method := .post
    body := upload
    config := { keepAlive := true, writeChunk := 64 }
    begins := fun _ => ["write 64"]
    steps := fun _ => uploadSteps ++ [
      (3, recv (early413 ++ "big"), ["head 413", "body \"big\"", "finish reusable=false"])] },
  { name := "an early response whose upload then completes is still not reusable"
    method := .post
    body := upload
    config := { keepAlive := true, writeChunk := 64 }
    begins := fun _ => ["write 64"]
    steps := fun _ => uploadSteps ++ [
      (3, recv early413, ["head 413", "read"]),
      (4, .written 64, ["write 32"]),
      (5, .written 32, []),
      (6, recv "big", ["body \"big\"", "finish reusable=false"])] },
  { name := "an early response whose upload stalls: the upload stops, the response completes"
    method := .post
    body := upload
    config := { keepAlive := true, writeChunk := 64, gapMs := 100 }
    begins := fun _ => ["write 64"]
    steps := fun _ => uploadSteps ++ [
      (3, recv early413, ["head 413", "read"]),
      (101, .tick, []),
      (150, recv "big", ["body \"big\"", "finish reusable=false"])] },
  { name := "an early response whose upload fails: the response still completes"
    method := .post
    body := upload
    config := { keepAlive := true, writeChunk := 64 }
    begins := fun _ => ["write 64"]
    steps := fun _ => uploadSteps ++ [
      (3, recv early413, ["head 413", "read"]),
      (4, .writeFailed "broken pipe", []),
      (5, recv "big", ["body \"big\"", "finish reusable=false"])] },
  { name := "a failed write before the request head is out fails the exchange, maybe delivered"
    config := { keepAlive := true, writeChunk := 16 }
    begins := fun _ => ["write 16"]
    steps := fun _ => [
      (1, .written 16, ["write 16"]),
      (2, .writeFailed "connection reset",
        ["fail the connection closed before a complete response (connection reset) [maybe delivered, written=16]"])] },
  { name := "a failed write after the request head stops the upload; the end of input then fails the exchange"
    method := .post
    body := upload
    config := { keepAlive := true, writeChunk := 64 }
    begins := fun _ => ["write 64"]
    steps := fun _ => uploadSteps ++ [
      (3, .writeFailed "connection reset", []),
      (4, .endOfInput,
        ["fail the connection closed before a complete response (a write failed earlier: connection reset) [maybe delivered, written=64]"])] },
  { name := "a failed write after the request head: an early response waiting to be read is still delivered"
    method := .post
    body := upload
    config := { keepAlive := true, writeChunk := 64 }
    begins := fun _ => ["write 64"]
    steps := fun _ => uploadSteps ++ [
      (3, .writeFailed "connection reset", []),
      (4, recv (early413 ++ "big"), ["head 413", "body \"big\"", "finish reusable=false"])] },
  { name := "abandoning mid-body: the read gap ends the drain, not reusable"
    config := { keepAlive := true, gapMs := 50 }
    steps := fun p => writtenSteps p 0 ++ [
      (0, recv "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhe", ["head 200", "body \"he\"", "read"]),
      (10, .abandon, []),
      (49, .tick, []),
      (50, .tick, ["finish reusable=false"])] },
  { name := "write slices: one write in flight, a partial write is resumed where it stopped"
    method := .post
    body := upload
    config := { keepAlive := true, writeChunk := 64 }
    begins := fun _ => ["write 64"]
    steps := fun _ => [
      (1, .written 10, ["write 64"]),
      (2, .written 64, ["write 64", "read"]),
      (3, .written 64, ["write 22"]),
      (4, .written 22, []),
      (5, .written 22, []),
      (6, lots, []),
      (7, recv okResponse, okActions)] },
  { name := "abandoning mid-body: the rest arrives within the drain limit, reusable"
    steps := fun p => writtenSteps p ++ [
      (2, recv tenHello, ["head 200", "body \"hello\"", "read"]),
      (3, .abandon, []),
      (4, recv "world", ["finish reusable=true"])] },
  { name := "abandoning mid-body: the rest takes longer than the drain time, not reusable"
    steps := fun p => writtenSteps p ++ [
      (2, recv tenHello, ["head 200", "body \"hello\"", "read"]),
      (5, .abandon, []),
      (104, .tick, []),
      (105, .tick, ["finish reusable=false"])] },
  { name := "abandoning mid-body: more than the drain limit is announced, not reusable at once"
    config := { keepAlive := true, drainBytes := 4 }
    steps := fun p => writtenSteps p ++ [
      (2, recv tenHello, ["head 200", "body \"hello\"", "read"]),
      (3, .abandon, ["finish reusable=false"])] },
  { name := "abandoning a chunked body: the drained bytes overrun the limit, not reusable"
    config := { keepAlive := true, drainBytes := 4 }
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n",
        ["head 200", "body \"hello\"", "read"]),
      (3, .abandon, []),
      (4, recv "6\r\n world\r\n", ["finish reusable=false"])] },
  { name := "abandoning without keep-alive ends at once, not reusable"
    config := { keepAlive := false }
    steps := fun p => writtenSteps p ++ [
      (2, recv tenHello, ["head 200", "body \"hello\"", "read"]),
      (3, .abandon, ["finish reusable=false"])] },
  { name := "abandoning before the response head fails the exchange as a local close"
    steps := fun p => writtenSteps p ++ [
      (2, .abandon, [s!"fail the client closed the connection [maybe delivered, written={p.bytes.size}]"])] },
  { name := "end of input mid-body fails, with the response received"
    steps := fun p => writtenSteps p ++ [
      (2, recv tenHello, ["head 200", "body \"hello\"", "read"]),
      (3, .endOfInput,
        [s!"fail the connection closed before a complete response [response received, written={p.bytes.size}, status=200]"])] },
  { name := "a Content-Length over the body limit fails at once, with the response received and its status"
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 200 OK\r\nContent-Length: 70000000\r\n\r\n",
        ["head 200", s!"fail body size limit exceeded [response received, written={p.bytes.size}, status=200]"])] },
  { name := "a Content-Length above 2^62 fails the same way, not before the head"
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 200 OK\r\nContent-Length: 99999999999999999999999999\r\n\r\n",
        ["head 200", s!"fail body size limit exceeded [response received, written={p.bytes.size}, status=200]"])] },
  { name := "a body with a transfer coding before chunked is refused when the head arrives, with the response received"
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n",
        ["head 200", s!"fail invalid response: a transfer coding other than chunked, which the client cannot decode [response received, written={p.bytes.size}, status=200]"])] },
  { name := "a HEAD response naming another transfer coding has no body to decode, and completes"
    method := .head
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, chunked\r\n\r\n", ["head 200", "finish reusable=true"])] },
  { name := "end of input before any response byte fails, maybe delivered"
    steps := fun p => writtenSteps p ++ [
      (2, .endOfInput,
        [s!"fail the connection closed before a complete response [maybe delivered, written={p.bytes.size}]"])] },
  { name := "a close-delimited body ends with the input, not reusable"
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 200 OK\r\n\r\nabc", ["head 200", "body \"abc\"", "read"]),
      (3, .endOfInput, ["finish reusable=false"])] },
  { name := "Connection: close from the server: not reusable"
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 2\r\n\r\nok",
        ["head 200", "body \"ok\"", "finish reusable=false"])] },
  { name := "without keep-alive a complete response is not reusable"
    config := { keepAlive := false }
    steps := fun p => writtenSteps p ++ [
      (2, recv okResponse, ["head 200", "body \"ok\"", "finish reusable=false"])] },
  { name := "an interim response is not delivered; the final one is"
    steps := fun p => writtenSteps p ++ [
      (2, recv "HTTP/1.1 100 Continue\r\n\r\n", ["read"]),
      (3, recv okResponse, okActions)] },
  { name := "body credit: nothing is read while the caller wants no more"
    steps := fun p => [
      (1, .written p.bytes.size, ["read"]),
      (2, recv "HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\nab", ["head 200"]),
      (3, .wantBody 1, ["body \"ab\""]),
      (4, .wantBody 5, ["read"]),
      (5, recv "cd", ["body \"cd\"", "finish reusable=true"])] },
  { name := "body credit used up exactly by a chunked body: its end is noticed without more credit"
    steps := fun p => [
      (1, .written p.bytes.size, ["read"]),
      (1, .wantBody 5, []),
      (2, recv "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n",
        ["head 200", "body \"hello\"", "finish reusable=true"])] },
  { name := "body credit used up and then the end of input mid-body: the failure is not left for the deadline"
    steps := fun p => [
      (1, .written p.bytes.size, ["read"]),
      (1, .wantBody 5, []),
      (2, recv tenHello, ["head 200", "body \"hello\""]),
      (3, .endOfInput,
        [s!"fail the connection closed before a complete response [response received, written={p.bytes.size}, status=200]"])] },
  { name := "a close-delimited body read with exactly enough credit ends when the caller asks once more"
    steps := fun p => [
      (1, .written p.bytes.size, ["read"]),
      (1, .wantBody 3, []),
      (2, recv "HTTP/1.1 200 OK\r\n\r\nabc", ["head 200", "body \"abc\""]),
      (3, .wantBody 1, ["read"]),
      (4, .endOfInput, ["finish reusable=false"])] },
  { name := "a stalled write that fails late does not restart the read gap"
    method := .post
    body := upload
    config := { keepAlive := true, writeChunk := 64, gapMs := 100 }
    begins := fun _ => ["write 64"]
    steps := fun _ => uploadSteps ++ [
      (3, recv early413, ["head 413", "read"]),
      (101, .tick, []),
      (190, .writeFailed "broken pipe", []),
      (201, .tick, ["fail read timeout [response received, written=64, status=413]"])] },
  { name := "a stale tick changes nothing; the write gap is the next deadline"
    deadline := 60000
    steps := fun p => [
      (5, .tick, []),
      (29999, .tick, []),
      (30000, .tick,
        [s!"fail write timeout (0 of {p.bytes.size} request bytes accepted) [maybe delivered, written=0]"])] },
  { name := "empty reads change nothing before the read gap, and the read gap still ends the exchange"
    config := { keepAlive := true, gapMs := 100 }
    steps := fun p => writtenSteps p 10 ++ [
      (50, recv "", []),
      (109, recv "", []),
      (110, recv "", [s!"fail read timeout [maybe delivered, written={p.bytes.size}]"])] },
  { name := "an empty read before the request head is written is no unsolicited response"
    steps := fun p => [
      (1, recv "", []),
      (2, .written p.bytes.size, ["read"]),
      (3, lots, []),
      (4, recv okResponse, okActions)] },
  { name := "a tick from the past changes nothing"
    steps := fun p => [
      (50, .written p.bytes.size, ["read"]),
      (10, .tick, []),
      (60, lots, []),
      (70, recv okResponse, okActions)] },
  { name := "the deadline ends an exchange waiting for the head"
    deadline := 500
    steps := fun p => writtenSteps p 10 ++ [
      (499, .tick, []),
      (500, .tick, [s!"fail deadline timeout [maybe delivered, written={p.bytes.size}]"])] },
  { name := "the deadline ends an exchange mid-body, with the response received"
    deadline := 500
    steps := fun p => writtenSteps p 10 ++ [
      (20, recv tenHello, ["head 200", "body \"hello\"", "read"]),
      (500, .tick, [s!"fail deadline timeout [response received, written={p.bytes.size}, status=200]"])] },
  { name := "the deadline has passed when the exchange begins: nothing sent"
    deadline := 0
    begins := fun _ => ["fail deadline timeout [not sent, written=0]"]
    steps := fun _ => [(1, recv okResponse, [])] },
  { name := "the read gap ends a silent exchange"
    config := { keepAlive := true, gapMs := 100 }
    steps := fun p => writtenSteps p 10 ++ [
      (109, .tick, []),
      (110, .tick, [s!"fail read timeout [maybe delivered, written={p.bytes.size}]"])] },
  { name := "the read gap and the deadline at the same instant: the deadline wins"
    config := { keepAlive := true, gapMs := 100 }
    deadline := 110
    steps := fun p => writtenSteps p 10 ++ [
      (110, .tick, [s!"fail deadline timeout [maybe delivered, written={p.bytes.size}]"])] },
  { name := "bytes that complete the response at the deadline: delivered"
    deadline := 500
    steps := fun p => writtenSteps p 10 ++ [(500, recv okResponse, okActions)] },
  { name := "bytes at the deadline that leave the response incomplete: delivered so far, then the deadline"
    deadline := 500
    steps := fun p => writtenSteps p 10 ++ [
      (500, recv tenHello,
        ["head 200", "body \"hello\"", s!"fail deadline timeout [response received, written={p.bytes.size}, status=200]"])] },
  { name := "a write that completes after the deadline: the deadline, nothing more written"
    method := .post
    body := upload
    config := { keepAlive := true, writeChunk := 64 }
    deadline := 500
    begins := fun _ => ["write 64"]
    steps := fun _ => [(600, .written 64, ["fail deadline timeout [maybe delivered, written=64]"])] }
]

/-- Runs one trace; returns the lines describing its failures (empty when it passed). -/
def runTrace (t : Trace) : List String := Id.run do
  let prepared := Exchange.prepare t.config (traceHead t.method) t.body.toUTF8
  let (ex, actions) := Exchange.begin prepared 0 t.deadline
  let mut ex := ex
  let mut problems := []
  let got := actions.toList.map renderAction
  let want := t.begins prepared
  if got != want then
    problems := problems ++ [s!"  begin: expected {want}", s!"         got      {got}"]
  for (i, (now, event, want)) in (t.steps prepared).zipIdx.map (fun (s, i) => (i, s)) do
    let (ex', actions) := ex.step now event
    ex := ex'
    let got := actions.toList.map renderAction
    if got != want then
      problems := problems ++ [
        s!"  step {i + 1} at {now}, {renderEvent event}: expected {want}",
        s!"         got      {got}"]
  return problems
