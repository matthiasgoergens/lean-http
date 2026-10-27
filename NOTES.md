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

## What can outlive a call, and other limits of milestone 1

Measured on 2026-10-27 (`logs/2026-10-27/net/`); v4.34.1 can cancel a pending receive but not a pending connect, write or name lookup.

- **An abandoned connect attempt** keeps its socket until the kernel gives up on the SYN: about 127 s with Linux's default `tcp_syn_retries` of 6.  It holds no worker and does not delay exit (the blackhole scenarios exit within tens of milliseconds), and the tests see the descriptors released once the kernel gives up (with `tcp_syn_retries=2` to keep the run short).  A host whose first address drops SYNs therefore costs one descriptor per call for two minutes; at about 8 calls a second that reaches the common limit of 1024 descriptors.
- **A write the peer never accepts** keeps its socket while the peer keeps the connection open (zero-window probes can keep it alive indefinitely).  The call itself ends at the write gap or the deadline, and exit is not delayed.
- **An abandoned name lookup** keeps running in libuv's thread pool (four threads by default) until the resolver gives up, and libuv joins that pool when the process exits: with a name server that never answers, the process waited 8 s at exit after a call that ended at its 2 s deadline (`dns-timeout`, reported as a known limitation).  Worse, when the lookup ends during exit the process often dies with a segmentation fault: 3 of 10 runs in `logs/2026-10-27/dns-exit/`, and 4 of 6 in an earlier unsaved batch.  The cause is not established; it looks like the runtime-shutdown race in which a libuv callback runs after Lean's task manager has been freed.  So the client bounds lookups only by the deadline and leaves the rest to the resolver's own timeouts (`/etc/resolv.conf`).
- **No early response during an upload.**  The response is read only after the whole request is written, so a server that answers early (a 413, say) and stops reading makes the call end as a write timeout, or as a closed connection, without the response.  Milestone 2's exchange core reads while it writes.
- **The write gap is per slice.**  `readGapMs` bounds each 64 KiB slice of the request (`writeChunkBytes`), since a write's completion is the only progress the client can observe.
- **No cancellation.**  `Cause.localClose` is reserved for closing a client and cancelling a call, which come with connection reuse.

## The exit hang is a runtime bug, fixed by an open upstream PR

A process could hang at exit after leaving a `recvSelector` registration outstanding (`logs/2026-10-27/probes/`).  The cause is in Lean's task manager, not in sockets: a pool task blocked in `Task.get` on a `Task.map` of a promise that is resolved after `main` returns waits forever, because no worker is started during shutdown.  `recvSelector`'s registration callback blocks in exactly that way.  leanprover/lean4 #15743 ("fix: dead locks and memory leaks in task manager finalization", open on 2026-10-27) fixes both: with its toolchain (pr-release-15743, 0f2095f9b5) the socket-free program hung 0 of 5 times and the abandoned-selector loop 0 of 20, against 5 of 5 and 11 of 20 on v4.34.1 (`logs/2026-10-27/probes/out/issue-program-check.txt`).  Until that is in the toolchain we use, the library must end every receive registration it starts before a call returns (an extra alternative in the `Selectable.one` that closing resolves), or use a receive selector that does not block in its callback.
