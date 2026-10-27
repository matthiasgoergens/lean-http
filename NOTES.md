# Notes

## The HTTP/1.1 codec: a vendored copy of the upstream protocol layer

Decided on 2026-10-27, by measurement.

`DESIGN.md` planned to use the HTTP/1.1 machine that v4.34.1 ships (`Std.Http.Protocol.H1.Machine`, client direction).  Nothing in v4.34.1 drives that direction (the server uses only `.receiving`), so `Tests/Codec.lean` drives it through the exchange core over 37 response shapes, each fed whole, one byte at a time and split in two at every position.

Against the v4.34.1 machine, 31 of the 34 cases with an expected outcome pass (Content-Length, chunked, close-delimited, HEAD, 204 and 304 with framing fields, interim responses, malformed status lines, header and body limits, end of input at every stage).  Three fail, all the same way: when a chunk-size line with extensions, or a trailer section, arrives split across two reads, the response is rejected as a bad message (`logs/2026-10-27/codec-v4.34.1/out.txt`).  The cause is `manyItems` in `Protocol/H1/Parser.lean`: it wraps each item in `optional (attempt ...)`, which turns "ran out of input" into "no more items", and the parser then fails hard on the half-received item instead of asking for more bytes.  TCP may segment a response anywhere, so this is a spurious failure in real use, rare only because extensions and trailers are rare.

The upstream client stack (leanprover/lean4 PRs 14546-14548, head 3e6f42a58a955f7fd9a6df4213f3be4bb68e3e3b) fixes exactly this (`optionalItem`), and changes the machine's client direction in a few other ways this client benefits from: `101 Switching Protocols` is no longer treated as an interim response, the end of an interim response's body is not reported as the end of the body, and a request without content gets no `Content-Length: 0`.  With that protocol layer vendored, all 37 cases pass, and the request encodings are checked as well (`logs/2026-10-27/codec-vendored/out.txt`).

So the library uses a copy of the stack's `src/Std/Http/Protocol`, renamed to `LeanHttpProto.Http.Protocol`, generated into the ignored `vendor/` by `scripts/vendor.sh` from a lean4 clone at that commit; `vendor/SOURCE` records the commit.  Two choices differ from a whole-tree copy:

- **Only the protocol layer is copied, not `Data` and `Internal`.**  `Internal` is unchanged in the stack, and its `Data` changes are additive helpers, of which the protocol layer needs two (`Status.isInterim`, `Method.anticipatesContent`); `LeanHttp/VendorCompat.lean` supplies them.  Copying `Data` would fork `Request`, `Response` and `Headers`, and the client's API would no longer speak `Std.Http`'s types, which `DESIGN.md` relies on for moving code between this client, `Std.Http.Server` and a future `Std` client.
- **The copy is a separate Lake library** (`LeanHttpProto`, source directory `vendor/`), with the toolchain's default options; the client's own library builds with `autoImplicit` off.

The exchange core still refuses `101` itself and counts interim responses itself, since neither version of the machine limits them.  When a toolchain ships these protocol changes, delete `vendor/`, `scripts/vendor.sh` and `LeanHttp/VendorCompat.lean` (which would then clash), and point the imports back at `Std.Http.Protocol`.

The three informational cases record behaviour without asserting it: a status line without the space before an empty reason phrase, bare LF line endings and obsolete line folding are all rejected as bad messages, by both versions.
