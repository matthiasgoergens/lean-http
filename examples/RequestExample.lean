import LeanHttp

/-!
A GET and a POST with a JSON body, through `Client.request`, which reads the whole response body,
a refused connect, and a call cancelled while it waits for its answer.
Run against `examples/server.py`: `request-example [base URL]` (default `http://127.0.0.1:8080`).
-/

open Std.Http LeanHttp

/-- What a failed call tells the caller about trying again. -/
def advice (err : Error) : String :=
  match err.delivery with
  | .notSent => "the server cannot have seen the request: sending it again is safe"
  | .maybeDelivered => "the server may have acted on the request: send it again only if that is harmless"
  | .responseReceived => "the server answered, and the call failed afterwards"

/-- A client for a server whose certificate a private CA issued: it trusts that CA's certificate. -/
def privateCaClient : BaseIO Client :=
  Client.new { tls := { caFile := some "/etc/my-service/ca.pem" } }

def main (args : List String) : IO UInt32 := do
  let base := args.headD "http://127.0.0.1:8080"
  let client ← Client.new

  let req := Request.get (.parse! s!"{base}/hello") |>.body .empty
  match ← (client.request req).block with
  | .ok response =>
    let status := response.line.status.toCode
    let contentType := response.line.headers.get? Header.Name.contentType
    let body := String.fromUTF8? response.body |>.getD "(not UTF-8)"
    IO.println s!"GET {status} {contentType.map (·.value) |>.getD "-"} {body}"
  | .error err =>
    IO.eprintln s!"GET failed: {err}; {advice err}"
    return 1

  let json := "{\"name\": \"lean-http\", \"stars\": 5}"
  let req := Request.post (.parse! s!"{base}/echo")
    |>.header! "Content-Type" "application/json"
    |>.body json.toUTF8
  match ← (client.request req).block with
  | .ok response =>
    IO.println s!"POST {response.line.status.toCode} {response.body.size} bytes: {String.fromUTF8? response.body |>.getD "(not UTF-8)"}"
  | .error err =>
    IO.eprintln s!"POST failed: {err}; {advice err}"
    return 1

  -- A port nothing listens on: the connect fails, the request is not sent.
  let quick ← Client.new { maxRetriesPerHop := 0 }
  match ← (quick.request (Request.get (.parse! "http://127.0.0.1:1/") |>.body .empty)).block with
  | .ok response =>
    IO.eprintln s!"unexpected: {response.line.status.toCode}"
    return 1
  | .error err => IO.println s!"refused: {err.cause.describe}; {advice err}"

  -- A call the caller gives up on: the server takes 5 s to answer, and another task cancels the
  -- call's token after 200 ms.
  let token ← Std.CancellationToken.new
  let slow := Request.get (.parse! s!"{base}/slow?ms=5000") |>.body .empty
  let result ← (do
    let call ← Std.Async.async (client.request slow (cancel := token))
    Std.Async.sleep 200
    token.cancel
    Std.Async.await call).block
  match result with
  | .ok response =>
    IO.eprintln s!"unexpected: {response.line.status.toCode}"
    return 1
  | .error err => IO.println s!"gave up: {err.cause.describe}; {advice err}"
  return 0
