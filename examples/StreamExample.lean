import LeanHttp

/-!
A response body read in pieces, as it arrives, through `Client.withResponse`, and a client with
settings of its own.  Run against `examples/server.py`: `stream-example [base URL]` (default
`http://127.0.0.1:8080`).
-/

open Std.Http LeanHttp

/-- A client for a slow upstream that may take minutes to answer. -/
def patientClient : BaseIO Client :=
  Client.new {
    deadlineMs := 15 * 60 * 1000  -- the whole call, retries and body included
    readGapMs := 5 * 60 * 1000    -- the longest silence while the response arrives
    maxRetriesPerHop := 3
    retry503 := true              -- retried only for idempotent requests
    maxRedirects := 3
    maxIdlePerOrigin := 8
  }

def main (args : List String) : IO UInt32 := do
  let base := args.headD "http://127.0.0.1:8080"
  let client ← patientClient
  let req := Request.get (.parse! s!"{base}/numbers?count=100000") |>.body .empty
  let result ← (client.withResponse req fun response => do
    let mut bytes := 0
    let mut pieces := 0
    while let some piece ← response.body.read do
      bytes := bytes + piece.size
      pieces := pieces + 1
    return (response.line.status.toCode, bytes, pieces)).block
  match result with
  | .ok (status, bytes, pieces) =>
    IO.println s!"streamed {status}: {bytes} bytes in {pieces} pieces"
    return 0
  | .error err =>
    IO.eprintln s!"stream failed: {err}"
    return 1
