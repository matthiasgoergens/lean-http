import Tests.Support.Drive
import Tests.Support.CodecDrive

/-!
# Codec tests

Drives the exchange core, and through it the response codec, over the response shapes a client
meets.  Each response is fed whole, one byte at a time, and split
in two at every position; the outcome must be the expected one in every case, since TCP may deliver
the bytes in any segmentation.

Prints one line per case and split mode, then a summary; exits with status 1 if any case failed.
-/

open Std.Http LeanHttp

/-- A comparable rendering of an outcome. -/
def render (r : Run) : String :=
  match r.ended, r.head with
  | some (.fail f), _ => s!"failed {repr f.cause}"
  | some (.finish _), some head =>
    let text := String.fromUTF8? r.body |>.getD s!"<{r.body.size} bytes>"
    s!"done {head.status.toCode} interim={r.ex.interim} body={repr text}"
  | _, _ => "pending"

/-- Feeds `pieces` in order, then end of input if `eof`. -/
def run (limits : Limits) (method : Method) (pieces : List ByteArray) (eof : Bool) : Run :=
  let config := { limits := codecConfig limits, maxInterim := limits.maxInterim, maxBody := limits.maxBody }
  let r := Run.written (prepare! config (requestHead method) .empty)
  let r := pieces.foldl Run.feed r
  if eof then r.endOfInput else r

/-- Runs one case in every split mode; returns the number of failing modes. -/
def runCase (c : Shape) : IO Nat := do
  let bytes := c.response.toUTF8
  let modes := splits bytes (bytes.size ≤ 2000)
  let results := modes.map fun (label, pieces) => (label, render (run c.limits c.method pieces c.eof))
  match c.expect with
  | some expected =>
    let bad := results.filter (·.2 != expected)
    if bad.isEmpty then
      IO.println s!"PASS {c.name}: {expected} ({modes.length} modes)"
    else
      IO.println s!"FAIL {c.name}: expected {expected}"
      -- Group the failing modes by what they produced.
      let outcomes := bad.map (·.2) |>.eraseDups
      for o in outcomes do
        let labels := bad.filter (·.2 == o) |>.map (·.1)
        let shown := String.intercalate " " (labels.take 12)
        let more := if labels.length > 12 then s!" (+{labels.length - 12} more)" else ""
        IO.println s!"     got {o} in {labels.length}/{modes.length} modes: {shown}{more}"
    return bad.length
  | none =>
    let outcomes := results.map (·.2) |>.eraseDups
    IO.println s!"INFO {c.name}: {String.intercalate " | " outcomes}"
    return 0

/-- A request encoding: the exact bytes `Exchange.prepare` produces, and its keep-alive verdict. -/
structure RequestCase where
  name : String
  method : Method
  body : String := ""
  keepAlive : Bool := false
  /-- Fields added to the request head after `Host`. -/
  extra : List (String × String) := []
  /-- HTTP/1.0 rather than HTTP/1.1. -/
  http10 : Bool := false
  expected : String
  /-- Whether the prepared request keeps the connection alive. -/
  expectKeepAlive : Bool := false

/-- Request encodings. -/
def requestCases : List RequestCase := [
  { name := "GET without body", method := .get
    expected := "GET / HTTP/1.1\r\nHost: example.test\r\nConnection: close\r\n\r\n" },
  { name := "POST with body", method := .post, body := "{\"a\":1}"
    expected := "POST / HTTP/1.1\r\nHost: example.test\r\nConnection: close\r\nContent-Length: 7\r\n\r\n{\"a\":1}" },
  { name := "POST without body", method := .post
    expected := "POST / HTTP/1.1\r\nHost: example.test\r\nConnection: close\r\nContent-Length: 0\r\n\r\n" },
  { name := "GET with keep-alive", method := .get, keepAlive := true
    expected := "GET / HTTP/1.1\r\nHost: example.test\r\n\r\n", expectKeepAlive := true },
  { name := "DELETE with a body", method := .delete, body := "x", keepAlive := true
    expected := "DELETE / HTTP/1.1\r\nHost: example.test\r\nContent-Length: 1\r\n\r\nx"
    expectKeepAlive := true },
  { name := "the caller's framing and Connection fields are replaced", method := .put, body := "ab"
    keepAlive := true
    extra := [("Transfer-Encoding", "chunked"), ("Content-Length", "9"), ("Connection", "upgrade")]
    expected := "PUT / HTTP/1.1\r\nHost: example.test\r\nContent-Length: 2\r\n\r\nab"
    expectKeepAlive := true },
  { name := "Connection: close from the caller turns keep-alive off", method := .get, keepAlive := true
    extra := [("Connection", "close")]
    expected := "GET / HTTP/1.1\r\nHost: example.test\r\nConnection: close\r\n\r\n" },
  { name := "HTTP/1.0 without keep-alive in its fields turns keep-alive off", method := .get
    keepAlive := true, http10 := true
    expected := "GET / HTTP/1.0\r\nHost: example.test\r\nConnection: close\r\n\r\n" }
]

/-- Checks one request encoding; returns whether it matched. -/
def runRequestCase (c : RequestCase) : IO Bool := do
  let base := requestHead c.method
  let headers := c.extra.foldl (init := base.headers) fun hs (n, v) =>
    hs.insert (Header.Name.ofString! n) (Header.Value.ofString! v)
  let head := { base with headers, version := if c.http10 then .v10 else .v11 }
  let prepared := prepare! { maxBody := 1024, keepAlive := c.keepAlive } head c.body.toUTF8
  let got := String.fromUTF8? prepared.bytes |>.getD "<invalid UTF-8>"
  let headOk := prepared.headBytes + c.body.utf8ByteSize == prepared.bytes.size
  if got == c.expected && prepared.config.keepAlive == c.expectKeepAlive && headOk then
    IO.println s!"PASS request {c.name}: {repr got} keepAlive={prepared.config.keepAlive}"
    return true
  else
    IO.println s!"FAIL request {c.name}: expected {repr c.expected} keepAlive={c.expectKeepAlive}, got {repr got} keepAlive={prepared.config.keepAlive} headBytes={prepared.headBytes}"
    return false

def main : IO UInt32 := do
  let mut failingCases := 0
  for c in requestCases do
    if !(← runRequestCase c) then
      failingCases := failingCases + 1
  for c in cases do
    if (← runCase c) > 0 then
      failingCases := failingCases + 1
  IO.println s!"{requestCases.length + cases.length} cases, {failingCases} failing"
  return if failingCases == 0 then 0 else 1
