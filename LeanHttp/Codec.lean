module

public import LeanHttp.Codec.Response
public import LeanHttp.Codec.Request

/-!
# The codec

The client's HTTP/1.1 codec: a response parser written to be proved correct
(`LeanHttp.Codec.Response`, with its theorems in `LeanHttp.Codec.Proofs`), which the exchange core
parses every response with, and the request serialiser (`LeanHttp.Codec.Request`).
-/
