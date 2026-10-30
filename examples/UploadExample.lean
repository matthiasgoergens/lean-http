import LeanHttp

/-!
A request body streamed as it is made, through `Client.upload`: of unknown size (sent chunked), and
of known size (sent with a `Content-Length`).  Run against `examples/server.py`:
`upload-example [base URL]` (default `http://127.0.0.1:8080`).
-/

open Std.Http LeanHttp

/--
A body of `count` numbered lines, made a hundred lines at a time as the client asks for them, so that
the whole body is never in memory.
-/
def numberedLines (count : Nat) : BaseIO RequestBody := do
  let next ← IO.mkRef 0
  return .stream none do
    let first ← next.modifyGet fun n => (n, n + 100)
    if first ≥ count then
      return none
    let lines := (List.range (min 100 (count - first))).map fun i => s!"line {first + i}\n"
    return some (String.join lines).toUTF8

def main (args : List String) : IO UInt32 := do
  let base := args.headD "http://127.0.0.1:8080"
  let client ← Client.new
  let body ← numberedLines 10000
  let req := Request.post (.parse! s!"{base}/count") |>.body body
  match ← (client.upload req).block with
  | .ok response =>
    let text := String.fromUTF8? response.body |>.getD "(not UTF-8)"
    IO.println s!"streamed {response.line.status.toCode} {text}"
  | .error err =>
    -- A streamed body is never sent again once any of it may have reached the server.
    IO.eprintln s!"upload failed: {err}"
    return 1
  let known ← RequestBody.ofChunks #["first part, ".toUTF8, "second part\n".toUTF8]
  let req := Request.post (.parse! s!"{base}/count") |>.body known
  match ← (client.upload req).block with
  | .ok response =>
    let text := String.fromUTF8? response.body |>.getD "(not UTF-8)"
    IO.println s!"known size {response.line.status.toCode} {text}"
    return 0
  | .error err =>
    IO.eprintln s!"upload failed: {err}"
    return 1
