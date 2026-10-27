# lean-http: design

An HTTP/1.1 client for Lean 4, built so that the properties that matter can be tested exhaustively and, where it pays, proved.  It targets Lean v4.34.1 and depends only on `Std` as shipped there (`Std.Async.TCP`, `Std.Async.DNS`, `Std.Time`).

## Why a new design

Our review of the client proposed for `Std.Http` (leanprover/lean4 #14546-#14548; `~/prog/lean-speed/notes/http-client-review.md`) found that its parser and framing held up well under hostile input, and that every serious defect lived in the asynchronous connection loop and the client around it:

- a redirect or failure of one request hard-closes a connection other callers share;
- `Client.close` makes an in-flight GET go out again;
- bytes that arrive while no request is in flight become the next request's response;
- an unread response body blocks every later request until a timeout;
- no `TCP_NODELAY`, duplicate DNS answers, no per-address connect timeout, IPv6 literals rejected;
- no backoff, no deadline for the whole call, a server that trickles bytes can hold a call for many times `requestTimeout`.

These bugs share a cause: the loop's decisions are interleaved with promises, channels, timers and cancellation, so no test or proof can reach them except by running the whole thing.  Lean's program logic gives no semantics to `Async` (`~/prog/lean-speed/notes/http-client-proof-routes.md`), so the loop as written cannot be verified either.  The design below moves every decision into pure functions and leaves a shell that only performs I/O.

## Layers

1. **Types** (`LeanHttp.Types`): methods, status codes, header fields (case-insensitive names, values as bytes), a request target and an origin.  Small and our own, so the library does not depend on the unmerged changes to `Std.Http`.
2. **Codec** (`LeanHttp.Codec`): a pure, incremental HTTP/1.1 response parser and a request serialiser.  The parser is a state machine over bytes: `feed : Parser → ByteArray → Parser × Array ParseEvent`.  Strict by default, with the same rejections the proposed client gets right (duplicate or listed `Content-Length`, `Content-Length` with `Transfer-Encoding`, oversized chunk sizes, obsolete line folding), and limits on header bytes, header count, interim (1xx) responses and chunk sizes.  We write our own rather than vendor the proposed machine: we need only the client direction, the proposed one is bidirectional and depends on changes to `Std.Http` that are not in v4.34.1, and our own can be written for proof.  The proposed machine and Python's h11 serve as test oracles.
3. **Connection core** (`LeanHttp.Conn`): one pure step function per connection, `step : Conn → ConnEvent → Conn × Array ConnAction`, plus `nextDeadline : Conn → Option Timestamp`.
   - Events: bytes received or end of input, a request handed to the connection, a request body chunk or its end, the caller releasing a response body, a tick with the current time, `retire` and `close` with a typed cause, a write failure.
   - Actions: write bytes, close the transport, deliver a response head, deliver body bytes, resolve a request with an error, resolve it as complete.
   - Requests are opaque identifiers; the shell keeps the table from identifier to promise, so the core cannot touch caller state and can only resolve requests it was given.
   - Time is an argument and deadlines are state, so a stale timer is a no-op rather than a race.
   - Bytes received while no request is in flight close the connection (they are never fed to the parser), and so do framing states that leave reuse uncertain (a HEAD response with body bytes, an early response whose body was cut short).
   - Every error carries a cause (`localClose`, `peerClosed`, `timeout`, `protocol`, `limit`) and whether any byte of the request reached the transport.  Retry decisions use that evidence, not the error's text.
4. **Client core** (`LeanHttp.Client`): a pure function over the pool, the queue and the per-call state, `step : ClientState → ClientEvent → ClientState × Array ClientAction`.
   - A pool per origin with a cap (default 4); a request takes an idle connection, or opens one if under the cap, or queues with its own deadline.  No head-of-line blocking across unrelated calls.
   - `retire` (graceful) for a connection that is merely unwanted; a hard close only with a cause from a short list (the caller's `close`, the request's own deadline, a transport or protocol failure on that connection).
   - Redirects: a pure planner, a hop limit that ends in an error, credential headers stripped across origins, no URL-based cycle detection.
   - Retries: only when nothing was sent, or the method is idempotent and the body can be replayed; connect failures back off exponentially with full jitter.  The random source is an explicit seed in the state, so runs replay.
   - One deadline for the whole call, across queueing, connects, redirects and retries; per-gap read timeouts on top; an optional minimum transfer rate.
5. **Shell** (`LeanHttp.Shell`): the only code that touches `Async`.  One task per connection runs `loop { event ← wait (sources, nextDeadline); (conn, actions) := step conn event; perform actions }`.  The client core runs under one mutex.  DNS answers are de-duplicated, addresses are tried with a per-attempt timeout and a short stagger between families, IPv6 literals bypass DNS, every socket gets `TCP_NODELAY`.  Target: under 300 lines, with no branch that decides anything the cores could decide.

## Interface

- `Client.request : Client → Request → Async (Except Error (Response ByteArray))`: the common case.  The body is read whole, up to a limit (default 64 MiB), and the connection goes back to the pool at once.
- `Client.withResponse : Client → Request → (Response BodyStream → Async α) → Async (Except Error α)`: streaming.  The body is open only inside the callback; leaving the callback, normally or by an exception, releases it (draining up to a small limit, otherwise closing the connection).  A forgotten body cannot outlive its scope, so it cannot block anyone.
- `Client.close` stops new calls and aborts calls in flight with cause `localClose`, which is never retried.
- `Error` says what happened and whether the request may have reached the server: `notSent`, `maybeDelivered`, `responseReceived`.

## Defaults

`TCP_NODELAY` on; pool cap 4 per origin; whole-call deadline 5 minutes; read gap timeout 30 s; at most 10 interim responses; buffered body limit 64 MiB; up to 2 retries of connect failures with full-jitter backoff (base 100 ms, cap 5 s); at most 10 redirects, then an error.  Every one is configurable; the timeouts are meant to be raised for slow servers, not removed.

## Verification

In order; each stage is useful even if the next is never reached.

1. **Known defects as traces.**  Each defect from the review becomes a fixed sequence of events against the connection or client core, with the expected actions asserted.  The reproducers on `matthiasgoergens/lean4@matthias/http-client-repros` cover the same ground through the shell.
2. **Properties at every step, on random event sequences.**  A seeded generator (and Plausible where it fits) drives the cores with event sequences an environment could produce, checking invariants after every step and shrinking failures.  The properties:
   - no response is delivered for a request that is not in flight;
   - a `localClose` error is never retried;
   - `retire` never aborts the exchange in flight;
   - every accepted request is in exactly one of queued, in flight or resolved;
   - after the deadline, every request is resolved.
3. **Bounded exhaustive exploration** of the cores over a small alphabet (two or three requests, a few tick values, valid and invalid bytes, end of input, close, retire), to a depth around 10.
4. **Fuzzing the codec** with AFL++ in a container: a harness that feeds response bytes split at fuzzer-chosen points, with assertions on the parser's invariants (aborting under `LEAN_ABORT_ON_PANIC=1`), split invariance (the same bytes in any chunking give the same events) and a differential check against h11 on framing and reuse decisions.  Seeds from the public OSS-Fuzz corpora of httparse and llhttp (`~/prog/lean-speed/notes/http-client-prior-art-tests.md`).
5. **Ported cases from mature suites**: curl's idle-connection and redirect tests, Go's `testTransportNotReadToEndConnectionReuse` and retry table, hyper-util's pool tests, h11's framing cases.
6. **Proofs**, as plain Lean theorems on the pure cores and the codec, once the properties have survived stages 2-4: the first three properties above, credential stripping on cross-origin redirects, and the chunked codec's round trip.  Veil gets a time-boxed experiment for finding the connection core's invariants from counterexamples, not as the proof vehicle.
7. **Real-socket tests** on loopback for what only a kernel shows: `TCP_NODELAY`, connect timeouts per address, IPv6 literals, a server closing an idle connection.

## Not in the first version

TLS (to follow through a transport class: either the upstream TLS stack, when it lands, or a thin OpenSSL binding; the toolchain already ships static OpenSSL), HTTP/2, cookies, authentication handlers, proxies, middleware hooks.  Each is easier to add to pure cores than to retrofit.

## Open questions

- Whether the codec should share code with `Std.Http`'s parser once that is merged, or stay separate.
- How the shell turns caller actions on a body stream into events without a race (the proof-routes survey could not settle whether every one can be).
- Whether the liveness property can be proved, or only tested: it needs a fairness assumption about the transport and the queue deadline, both of which the design supplies.
- Whether this becomes a proposal to the Lean FRO, a library of its own, or the client a downstream service uses in place of `curl`.
