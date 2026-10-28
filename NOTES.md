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

## A response parser written for proof

Built on 2026-10-28; the client does not use it yet.  `LeanHttp/Codec/` parses an HTTP/1.1 response in the client direction, given the request method, and every function in it is total.  `Parser.stepByte` reads one byte with no loop and is the meaning of the parser; `Parser.feed` reads body bytes in bulk, slicing them out of its input, and is proved to compute the same (`feed_eq_run`).  `LeanHttp/Codec/Proofs.lean` lists what is proved, and `scripts/codec-axioms.lean` prints the axioms of the main theorems, which use `propext`, `Classical.choice` and `Quot.sound` at most.

Its rules and limits are those of the vendored machine, with the exchange core's interim limit, `101` refusal and body limit built in, except in these deliberate differences, each of which the differential test below finds and attributes:

- A chunk whose size line announces more than the body limit leaves is rejected at its size line.  The core rejects it only once the data arrives, so its outcome then depends on what the data holds and on how the bytes are cut: a bad message, still pending, a premature close, or the body limit.
- A chunk-size line longer than its limit is rejected at the byte that exceeds it.  The vendored machine measures an incomplete line only up to its last complete extension, and keeps waiting.
- Chunk extensions are counted at each `;`, so one too many is refused when its `;` arrives rather than when it is complete.
- A `Content-Length` of 2^62 or more is reported with its head and then rejected as over the body limit, like any oversized length.  The core lifts its machine's body limit to 2^62, and the machine refuses such a head before reporting it.
- `Connection: close` ends the connection whatever the version (RFC 9112 section 9.3).  The vendored machine looks for `close` only in HTTP/1.1, so it keeps an HTTP/1.0 connection whose response says both `keep-alive` and `close`.
- There is no `maxStartLineLength`: a status line is bounded by the reason-phrase limit, 527 bytes with the defaults, well inside the machine's default of 8192.

Measured on the build host (`logs/2026-10-28/codec/final/`, commit c94d1e6):

- The 37 response shapes of `Tests/Codec.lean` pass, each fed whole, byte by byte and split in two at every position (`response-codec-tests`).
- `codec-diff` ran 120,037 inputs for each of four seeds: the shapes, responses generated with deliberate faults, and mutations of both, with GET, HEAD or POST and default or partly small limits, each run whole and cut at random points, without and with the end of input.  Every disagreement with the core falls under one of the differences above (the tool finds the cause by relaxing one limit at a time until the two agree), and the codec's outcome never depended on the cut.  The core's did, on 43 inputs, all with a chunk beyond the body limit.  A control run with the codec's limits off by one shows the comparison sees disagreements.
- Parsing a 60 MB body fed in 64 KiB reads, the codec took 0.94 times the core's time for a `Content-Length` body, 0.93 with 16 KiB chunks and 0.75 with 1 KiB chunks (median per-block ratios over 100 randomised blocks on one pinned CPU of a loaded machine; the codec was faster in 60, 61 and 100 of the 100 blocks).  Body bytes are slices of the bytes fed, so nothing carried across calls grows with the body.

Left before it can replace the vendored machine in the client:

- The exchange core has to drive it: feed it the bytes read, turn its events into actions, and account for the caller's body credit itself, since the codec delivers every body byte it is fed (read no more than the credit, or hold the excess).
- Requests are still encoded by the vendored writer (`Exchange.prepare`), and the machine's `maxMessages` and the request's own keep-alive go with it.
- The core's reuse verdict would use `Parser.reusable`, and its proofs could then rest on the certainty lemmas (`LeanHttp/Codec/Proofs/Certain.lean`) instead of treating the machine as opaque.
- Completeness is not proved: no theorem says that a well-formed response within the limits is accepted.  The shape tests and the differential run are the evidence that it is.
- The interim heads' `Connection` fields enter the keep-alive verdict, but no theorem ties that to the bytes.
- CONNECT and protocol upgrades are not handled; the client sends neither.

## What can outlive a call, and other limits of milestone 1

Measured on 2026-10-27 (`logs/2026-10-27/net/`); v4.34.1 can cancel a pending receive but not a pending connect, write or name lookup.

- **An abandoned connect attempt** keeps its socket until the kernel gives up on the SYN: about 127 s with Linux's default `tcp_syn_retries` of 6.  It holds no worker and does not delay exit (the blackhole scenarios exit within tens of milliseconds), and the tests see the descriptors released once the kernel gives up (with `tcp_syn_retries=2` to keep the run short).  A host whose first address drops SYNs therefore costs one descriptor per call for two minutes; at about 8 calls a second that reaches the common limit of 1024 descriptors.
- **A write the peer never accepts** keeps its socket while the peer keeps the connection open (zero-window probes can keep it alive indefinitely).  The call itself ends at the write gap or the deadline, or with an early response that completes, and exit is not delayed (`write-timeout`, `early-response`).
- **An abandoned name lookup** keeps running in libuv's thread pool (four threads by default) until the resolver gives up, and libuv joins that pool when the process exits: with a name server that never answers, the process waited 8 s at exit after a call that ended at its 2 s deadline (`dns-timeout`, reported as a known limitation).  Worse, when the lookup ends during exit the process often dies with a segmentation fault: 3 of 10 runs in `logs/2026-10-27/dns-exit/`, and 4 of 6 in an earlier unsaved batch.  The cause is not established; it looks like the runtime-shutdown race in which a libuv callback runs after Lean's task manager has been freed.  So the client bounds lookups only by the deadline and leaves the rest to the resolver's own timeouts (`/etc/resolv.conf`).
- **An early response during an upload is heard, unless a write fails first.**  Since the exchange core became a step function (2026-10-28), the response is read once the request head is written, while the body is still going out.  A server that answers 413 after the head and stops reading now gets its response delivered in about 24 ms of a 32 MB upload, where milestone 1 ended the call with a write timeout at the 1 s gap (`early-response` in `logs/2026-10-28/core/net/`, and the control against milestone 1's client in `logs/2026-10-28/core/early-response-control/`).  A server that answers and then closes can make the pending write fail before the response is read; the call then fails as a closed connection, maybe delivered, without the response, unless the response head arrived first.  That race is not tested over TCP.
- **The write gap is per slice.**  `readGapMs` bounds each 64 KiB slice of the request (`writeChunkBytes`), since a write's completion is the only progress the client can observe.
- **No cancellation.**  The exchange core fails with `Cause.localClose` when the caller abandons it before the response head, but `Client.request` never abandons; closing a client and cancelling a call come with connection reuse.

## The exit hang is a runtime bug, fixed by an open upstream PR

A process could hang at exit after leaving a `recvSelector` registration outstanding (`logs/2026-10-27/probes/`).  The cause is in Lean's task manager, not in sockets: a pool task blocked in `Task.get` on a `Task.map` of a promise that is resolved after `main` returns waits forever, because no worker is started during shutdown.  `recvSelector`'s registration callback blocks in exactly that way.  leanprover/lean4 #15743 ("fix: dead locks and memory leaks in task manager finalization", open on 2026-10-27) fixes both: with its toolchain (pr-release-15743, 0f2095f9b5) the socket-free program hung 0 of 5 times and the abandoned-selector loop 0 of 20, against 5 of 5 and 11 of 20 on v4.34.1 (`logs/2026-10-27/probes/out/issue-program-check.txt`).  Until that is in the toolchain we use, the library must end every receive registration it starts before a call returns (an extra alternative in the `Selectable.one` that closing resolves), or use a receive selector that does not block in its callback.

## Nothing carried across a wait is updated in place

Measured on 2026-10-28 (`logs/2026-10-28/core/bigbody/`).  A value that async code carries across a wait is captured by a continuation that another thread may run, so the runtime marks it as shared between threads, and `lean_is_exclusive` is false for every such object: updating it copies it.  Appending each chunk of a response body to one `ByteArray` therefore copied the whole body every time, in milestone 1 and in the first version of the new shell: 5.6 to 7.5 s for a 60 MB body over loopback, growing with the square of the size.  Keeping it in an `IO.Ref` does not help, since a value stored in a shared reference is marked as well.  The shell now keeps the chunks in a list and joins them once at the end, in a buffer allocated there: 70 to 100 ms.  Any state the shell accumulates across waits (a streaming body's buffer, a pool's tables) needs the same care; the exchange core is pure and has no such state of its own, but the shell holds its `Exchange` across waits, so the core must not grow a buffer in place either.
