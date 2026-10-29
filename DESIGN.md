# lean-http: design

An HTTP/1.1 client for Lean 4 (v4.34.1), built so that its decisions can be tested exhaustively and, where it pays, proved.  It uses `Std.Http`'s data types as shipped in the toolchain and a codec of its own: a response parser written for proof and a small request serialiser (`LeanHttp.Codec`).  The HTTP/1.1 machine of the proposed upstream client stack (a renamed copy of its protocol layer; see `NOTES.md`) is not part of the library: the tests and the fuzzer use it as the oracle the codec is compared with.  Of that client, what the library replaces besides the codec is the part that went wrong: connection management.

## Position

lean-http is a library of its own, a Lake package that depends only on what ships in the toolchain.  An HTTP client does not belong in the standard library: it needs to release on its own schedule, carry its own codec, TLS and policy, and change faster than `Std` can (Matthias, 2026-10-28).

It started from a review of the client proposed for `Std.Http` (leanprover/lean4 #14546-#14548), which held up well where its tests were thorough (parsing, framing, limits, redirect rewriting) and failed in its connection loop and pool (`~/prog/lean-speed/notes/http-client-review.md`).  The review and fixes for most of those defects were offered upstream (leanprover/lean4#14548, review 5665985837), independently of this library.  Two aims shape the design:

1. **A client to use now**, from code pinned to v4.34.1, in place of running `curl` as a subprocess.
2. **A connection layer whose decisions live in pure functions**, so that the properties the review showed matter ("no response without a request in flight", "close never causes a resend", "retiring never aborts the exchange in flight") can be checked on every interleaving and proved.

## Milestone 1: the smallest useful client

- One connection per request, `Connection: close`.  No pool, no reuse, so none of the stale-connection, idle-bytes or unread-body hazards can arise.
- `Client.request : Request ByteArray → Async (Except Error (Response ByteArray))`, with a throwing variant.  The body is read whole, up to a limit.
- The calling task does everything: DNS, connect, and then the exchange, whose writes and reads it performs for the exchange core, at most one of each in flight, racing them against the core's next deadline.  Other tasks exist only for those operations and the timers.
- DNS answers de-duplicated and interleaved by family; addresses tried with a per-attempt connect timeout and a short stagger between attempts; IPv6 literals bypass DNS; `TCP_NODELAY` on.
- Retries only of connects that failed, with exponential backoff and full jitter seeded from the operating system (the seed is logged so a run can be replayed), within a retry budget.
- One deadline for the whole call; a per-gap read timeout on top; a cap on interim (1xx) responses.
- No redirect following yet.

This is all a service needs that POSTs JSON to a plain-HTTP API with long timeouts, and it is small enough to review in one sitting.

## Milestone 2: pooling, redirects, streaming

### The caller drives its connection

Following httpcore (Python) rather than a task per connection: the task that makes a request owns the connection for the duration of the exchange.  An idle connection in the pool is plain data with no task attached.  When a connection is taken from the pool, it is first checked for bytes or end of input that arrived while it was idle (with `recvSelector`'s non-blocking check), and discarded if there are any; httpcore, urllib3 and curl do the same.  This removes the race between a background loop and the caller's body stream, and with it most of the machinery the upstream loop needed.

### Two pure cores

1. **Pool core** (`LeanHttp.Pool`): which connections exist per origin, which are idle, which are checked out.  No timers and no I/O; a mutex guards it safely because every operation on it is a quick pure step.  Idle connections are capped per origin (default 4) and expire after an idle timeout (default 4 s, below common server keep-alive timeouts); active connections are not capped by default.
2. **Exchange core** (`LeanHttp.Exchange`): one request and response on one connection, as a pure step function over the response codec, `step : Exchange → ExchangeEvent → Exchange × Array ExchangeAction`, with `nextDeadline`.
   - Events: bytes read, end of input, bytes written (with a count), the caller asking for more body (with a size), a tick, the caller abandoning the response, a write or read failure.
   - Actions: write these bytes (one write in flight at a time), read up to this many bytes (or not now: the core says whether it wants input), deliver the response head, deliver body bytes, finish, fail with an error.
   - The codec delivers every body byte it is fed, so the core holds what the caller has not asked for, issues no read while it holds any, and hands everything it holds over once the caller asks for more: what it holds never exceeds one read, and a delivery exceeds the caller's request by at most that.
   - The core decides reuse at the end: the connection goes back to the pool only if the codec says the connection could carry another exchange (the response ended, framed with certainty, with nothing after it and before the end of input, and its heads allowed keep-alive), the caller has the whole body, and the request asked for keep-alive and was written in full.  A HEAD or 204/304 response followed by stray bytes, an early response to an unfinished upload, or a response whose body was abandoned all make the connection non-reusable; it is shut down for writing and dropped, never pooled.  An early response is still read to its end and delivered.
   - No response can be due before the server has the request head, so the core asks for no read until the head has been written (bytes reported earlier anyway fail the exchange unparsed).  Bytes a server sent before it saw the request, such as a 408 on an idle connection, still wait in the socket and are read as the response; the idle check before reuse is what catches them.  From then on the core reads while the body is still going out, so an early response is heard even from a server that stops reading.  Once the request head is out, a failed write only stops the upload, since a response may already be waiting; once the final response head has arrived, so does a stalled one.  The read gap counts only once writing is over: a server is silent while it receives a request.
   - Errors carry a cause (`localClose`, `peerClosed`, `timeout`, `protocol`, `limit`) and the number of request bytes written.  "Nothing written" (no write ever issued: the bytes of a write in flight may already be on the wire) is the evidence that makes a retry safe for any method.  A 408 on a reused connection before any response byte counts as "nothing processed", as Go treats it.

A **per-call planner** (`LeanHttp.Call`) runs in the caller's task.  After each exchange it decides, as a pure function of the call's state, the time and the exchange's outcome (a response head, or a `Failure`), whether to deliver the response, follow a redirect with the next request, send the same request again after a delay, or fail.  This is the split Go makes between `Client` and `Transport`.

- **Redirects** follow RFC 9110 section 15.4 with the Fetch standard's method rules: only 301, 302, 303, 307 and 308; 303 makes the request a GET (a HEAD stays a HEAD), 301 and 302 turn a POST into a GET, and every other case keeps the method, with its body, so a redirect that would have to send a streamed body again is delivered instead.  A method change drops the body and the content fields.  `Location` is resolved against the current URI, userinfo and fragment dropped, and only http and https are followed.  At most 10 redirects; one more fails the call with `tooManyRedirects` rather than delivering the last 3xx; there is no cycle detection keyed on URLs, since POST, 303, GET to the same URL is ordinary.
- **Origins** are compared by scheme, host and port, so https to http changes the origin.  Credential fields (`Authorization`, `Cookie`, `Proxy-Authorization`) go only to the origin of the call's first request: dropped on a hop to any other origin and given back on a hop that returns to it.  Go's client also judges each hop against the first request, but by host alone, with subdomains allowed.  A hop to another origin also drops `Referer` and the cache validators and rewrites `Host`; hop-by-hop fields never carry over.
- **Retries** are per hop and never cross a redirect.  A failure where nothing was sent may be retried whatever the method; once a byte may have reached the server, only an idempotent method with a replayable body; a response head received, a `localClose`, the call's deadline, a name that did not resolve, an invalid request, a malformed response and a limit, never.  Every retry after a failure waits the full-jitter backoff (`LeanHttp.Backoff`, drawn from the call's seed and its retry number).  Retries of 429 and 503 are opt-in, for requests that could be retried after bytes were sent, and wait what `Retry-After` asks (seconds, or an HTTP-date measured from the response's `Date`), up to a limit, or the backoff without it.  No wait reaches the call's deadline: a retry that would have to wait until it is not made.  At most 2 retries per hop and 4 per call.
- **Proved** (`LeanHttp/Call/Proofs.lean`): credentials never reach another origin; the hop limit holds and reaching it is an error; nothing that is not idempotent or replayable is retried after a byte may have been sent; `localClose` is never retried; every delay ends before the deadline and within its cap; 303 yields GET (or HEAD); a method change leaves no body and no content field, on that hop and the ones after it; a redirect never sends a streamed body again; a redirect that is not followed is delivered; a hop to another origin drops `Referer` and the cache validators; the target always addresses the hop's origin, which is http or https.  **Tested** (`call-tests`, `call-diff`): each rule, random calls checked step by step with planted bugs as positive controls, and a differential test against the vendored and toolchain redirect planners and the upstream client's redirect loop, in which every disagreement is one of the deliberate differences `NOTES.md` lists.

### Streaming

`Client.withResponse : Request → (Response BodyStream → Async α) → Async (Except Error α)`.  The body is pulled by the caller, so backpressure is natural: the exchange core reads from the socket only when the caller asks.  Leaving the callback abandons whatever is unread, which makes the connection non-reusable unless the rest arrives within a small drain limit.  Lean cannot stop the stream escaping its scope; using it afterwards raises an error, and the connection has been released regardless.  Holding a body open inside the callback while doing other slow work keeps one connection busy, and nothing else.

Request bodies: bytes (replayable), or a stream (not replayable, so never retried once any of it is written).

## What `Std.Http` provides

From v4.34.1: `Request`, `Response`, `Headers` (with validated names and values, which rules out header injection), `Method`, `Status`, the URI parser (IPv6 literals included) and the head encoder the request serialiser uses.  Responses are parsed by the library's own codec, whose functions are all total so that its properties can be proved; the HTTP/1.1 machine's `H1.lean` has 18 `partial def`s in v4.34.1, which no theorem can unfold.  The upstream stack's protocol layer, vendored under `LeanHttpProto` for the tests (v4.34.1's machine rejects a chunk-size line with extensions or a trailer section that arrives split across reads, which the stack fixes; `NOTES.md`), is the codec's test oracle.  It also holds a pure redirect planner (`Protocol/H1/Redirect.lean`, in v4.34.1 too), which the per-call planner was to use; using it would bring the vendored layer back into the library, so the planner has one of its own, written against `Std.Http`'s types, and the two copies of the upstream one are its test oracles.

## Socket lifecycle

v4.34.1's TCP client socket has `shutdown` (closing the write side) but no explicit close; the descriptor is released when the last reference is dropped.  The design therefore keeps references to a socket in exactly two places, the exchange in progress and the pool entry, and drops both when the connection ends.  An exit test checks that a process with connections closed in each way (end of response, abandoned body, timeout, error) exits promptly: the review saw processes hang at exit after a body was closed unread.  A pending receive can be cancelled, but a pending connect, write or name lookup cannot, and each holds its socket (or a thread of libuv's pool) until it ends: losing connect attempts are therefore abandoned rather than cancelled, and their sockets close when the kernel gives up on them.  `NOTES.md` records what each of these costs, measured.

## Defaults

`TCP_NODELAY` on; connect timeout 10 s per attempt, with a 250 ms stagger between attempts; whole-call deadline 5 minutes, which alone bounds name resolution; read gap 30 s, which also bounds each 64 KiB slice of a request write; at most 10 interim responses; buffered body limit 64 MiB; up to 2 retries of failed connects (full jitter, base 100 ms, cap 5 s), which with the per-call planner become up to 2 retries per hop and 4 per call; 429 and 503 not retried unless asked for, and a `Retry-After` honoured up to 60 s; idle connections: 4 per origin, 4 s; an abandoned body is drained for reuse if the rest is at most 64 KiB and arrives within 100 ms; at most 10 redirects, then an error.  Slow upstream APIs (model calls that think for minutes before answering) need the deadline and the read gap raised; the defaults suit ordinary web APIs.

## Verification

In order of value per effort; each stage stands alone.

1. **Known defects as traces** against the exchange and pool cores (the review's defects plus the survey's cases: early response during an upload, stray bytes after HEAD).
2. **Properties at every step** on random event sequences (seeded generator; Plausible where it fits), shrinking failures:
   - no response head is delivered before the request head has been written (an early response may arrive while the body is still going out);
   - an error with cause `localClose` is never retried;
   - a connection returns to the pool only if its exchange ended with certain framing and fully read;
   - every checked-out connection is returned or dropped exactly once;
   - after the deadline, the call has ended.
3. **Bounded exhaustive exploration** of the pool core with several concurrent calls, and of the exchange core over a small alphabet, to a depth around 10.
4. **Trace validation**: record the events and actions of real-socket runs and replay them through the cores, checking that the shell did what the cores said.
5. **Fuzzing** the exchange core, with the codec inside it, under AFL++ (persistent mode through a small C entry point; assertions abort under `LEAN_ABORT_ON_PANIC=1`): response bytes split at fuzzer-chosen points, with split invariance and a check of the reuse decision, and the vendored machine driven directly as its differential oracle.  h11 as a differential oracle for the machine's framing.
6. **Ported cases** from curl, Go, hyper-util, OkHttp and h11 (`~/prog/lean-speed/notes/http-client-prior-art-tests.md`).
7. **Proofs** of the single-step properties (cheap, once the cores have the right types: cause-typed errors, an in-flight token), then the pool invariant ("returned or dropped exactly once"), then, if it proves tractable, liveness under the deadline.  Veil only if the plain explorer cannot settle an invariant.
8. **Real-socket tests** on loopback for `TCP_NODELAY`, connect timeouts per address, IPv6 literals, idle connections closed by the server, and prompt exit.

## From fuzzed properties to proved ones

Every property the fuzzer or the random runs check should end up as a theorem, with fuzzing kept as the cheap first line (Matthias, 2026-10-28).  Most of the exchange core's properties hold whatever the response parser returns, so they are proved about `Exchange.step` directly, treating the parser as opaque.  `LeanHttp/Exchange/Proofs.lean` and `LeanHttp/Exchange/Liveness.lean` do so for the single-step properties, for "a live exchange has a deadline ahead", and for liveness under the deadline; liveness assumes only that the shell, whenever the exchange is live, eventually reports an event at or after its next deadline, which a shell that sleeps until that deadline and then ticks does, as long as its sleep returns.  The codec's properties (termination, body length within `Content-Length`, no body after HEAD, 204 or 304, split invariance, the response delivered being the response received) are proved about the codec itself (`LeanHttp/Codec/Proofs/`), with the vendored machine as its differential oracle (`codec-diff`, the fuzzer).  `LeanHttp/Exchange/Response.lean` joins the two: in every run of the core, its parser is the codec's run over the bytes received, so a finish proves that those bytes held a complete response, and a reusable finish that they held exactly one, whose body is the body delivered.

## Not yet

TLS (a transport class that carries the server name for SNI and distinguishes a clean TLS close from a truncated one; the request target form is already a parameter of the exchange core, so absolute-form for proxies needs no change to it), HTTP/2, proxies (CONNECT), cookies, authentication handlers, decompression (when it comes: off for HEAD and ranges, with a decompressed-size limit), middleware.

## Open questions

- Whether `recvSelector`'s non-blocking check reports end of input on an idle socket reliably (to be measured before milestone 2 relies on it).
- Whether a pending receive on an idle socket is what causes the exit hang the review saw.
