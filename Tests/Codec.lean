import Tests.Support.Drive
import Tests.Support.CodecCases

/-!
# Codec tests

Drives the exchange core, and through it the HTTP/1.1 machine in the client direction,
over the response shapes a client meets.  Each response is fed whole, one byte at a time, and split
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
  let config := { h1 := limits.h1, maxInterim := limits.maxInterim, maxBody := limits.maxBody }
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

/-- Request encodings: the exact bytes `Exchange.prepare` produces. -/
def requestCases : List (String × Method × String × String) := [
  ("GET without body", .get, "",
    "GET / HTTP/1.1\r\nHost: example.test\r\nConnection: close\r\n\r\n"),
  ("POST with body", .post, "{\"a\":1}",
    "POST / HTTP/1.1\r\nHost: example.test\r\nConnection: close\r\nContent-Length: 7\r\n\r\n{\"a\":1}"),
  ("POST without body", .post, "",
    "POST / HTTP/1.1\r\nHost: example.test\r\nConnection: close\r\nContent-Length: 0\r\n\r\n")
]

/-- Checks one request encoding; returns whether it matched. -/
def runRequestCase (c : String × Method × String × String) : IO Bool := do
  let (name, method, body, expected) := c
  let bytes := (prepare! { maxBody := 1024 } (requestHead method) body.toUTF8).bytes
  let got := String.fromUTF8? bytes |>.getD "<invalid UTF-8>"
  if got == expected then
    IO.println s!"PASS request {name}: {repr got}"
    return true
  else
    IO.println s!"FAIL request {name}: expected {repr expected}, got {repr got}"
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
