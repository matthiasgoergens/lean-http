module

public import LeanHttp.Codec.Proofs.Feed
public import LeanHttp.Codec.Proofs.Body
public import LeanHttp.Codec.Proofs.Chunked
public import LeanHttp.Codec.Proofs.Certain
public import LeanHttp.Codec.Proofs.Shape
public import LeanHttp.Codec.Proofs.HeadSound
public import LeanHttp.Codec.Proofs.ResponseSound
public import LeanHttp.Codec.Proofs.Unique

/-!
# Proofs about the response codec

- `LeanHttp.Codec.Proofs.Feed`: `feed` computes what `stepByte` means, so the result does not depend
  on how the input is cut into pieces, and `feed` makes at most one round per input byte.
- `LeanHttp.Codec.Proofs.Body`: what every run delivers: never more than the `Content-Length`, all of
  it when complete, nothing for HEAD, 204 and 304, nothing beyond `Config.maxBody`, nothing before
  the final head; the final head is not 1xx and follows at most `Config.maxInterim` interim
  responses; and its keep-alive verdict rests on its own `Connection` fields.
- `LeanHttp.Codec.Proofs.HeadSound`: the head reported is the head received: the input starts with
  the interim heads and then a status line and field lines that are exactly the head's.
- `LeanHttp.Codec.Proofs.ResponseSound`: the response delivered is the response received: a complete
  response's input is the interim heads, the head, a body of the kind its framing declares (chunked
  bodies in any encoding the parser accepts), then any further bytes, and the body delivered is
  that body's payload.
- `LeanHttp.Codec.Proofs.Unique`: those descriptions read the bytes one way only: a chunked body's
  payload, and a head's version, code, reason phrase and fields, are functions of the bytes.
- `LeanHttp.Codec.Proofs.Shape`: every run is observed as the head, then body bytes, then the end or
  an error; and `Content-Length` and close-delimited bodies are delivered as they are.
- `LeanHttp.Codec.Proofs.Chunked`: decoding what `encodeChunked` encodes gives back the chunks.
- `LeanHttp.Codec.Proofs.Certain`: what "complete, framed with certainty" means, and the lemmas the
  exchange core's reuse verdict needs.
-/
