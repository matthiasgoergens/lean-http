module

public import LeanHttp.Address
public import LeanHttp.Backoff
public import LeanHttp.Body
public import LeanHttp.Call
public import LeanHttp.Call.Trace
public import LeanHttp.Client
public import LeanHttp.Config
public import LeanHttp.Connect
public import LeanHttp.Error
public import LeanHttp.Exchange
public import LeanHttp.Pool
public import LeanHttp.RequestBody
public import LeanHttp.Tls
public import LeanHttp.Transport
public import LeanHttp.Wait

/-!
# lean-http

An HTTP/1.1 client for Lean 4.  `LeanHttp.Client.request` (the whole body) and
`LeanHttp.Client.withResponse` (a streamed body) are the entry points, and `LeanHttp.Client.upload`
and `LeanHttp.Client.withUpload` their variants for a request body the caller streams
(`LeanHttp.RequestBody`); `DESIGN.md` describes the
plan and `NOTES.md` the decisions taken while building it.
-/
