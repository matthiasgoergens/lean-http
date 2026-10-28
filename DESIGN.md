# lean-http: design

An HTTP/1.1 client for Lean 4 (v4.34.1), built so that its decisions can be tested exhaustively and, where it pays, proved.  It uses `Std.Http`'s data types as shipped in the toolchain and the HTTP/1.1 machine of the proposed upstream client stack (a renamed copy of its protocol layer, until a toolchain ships it; see `NOTES.md`), and replaces only the part where that client went wrong: connection management.

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
2. **Exchange core** (`LeanHttp.Exchange`): one request and response on one connection, as a pure step function over the toolchain's HTTP/1.1 machine, `step : Exchange → ExchangeEvent → Exchange × Array ExchangeAction`, with `nextDeadline`.
   - Events: bytes read, end of input, bytes written (with a count), the caller asking for more body (with a size), a tick, the caller abandoning the response, a write or read failure.
   - Actions: write these bytes (one write in flight at a time), read up to this many bytes (or not now: the core says whether it wants input), deliver the response head, deliver body bytes, finish, fail with an error.
   - The core decides reuse at the end: the connection goes back to the pool only if the response was framed with certainty and read to its end, and the request was written in full.  A HEAD or 204/304 response followed by stray bytes, an early response to an unfinished upload, or a response whose body was abandoned all make the connection non-reusable; it is shut down for writing and dropped, never pooled.  An early response is still read to its end and delivered.
   - No response can be due before the server has the request head, so the core asks for no read until the head has been written (bytes reported earlier anyway fail the exchange unparsed).  Bytes a server sent before it saw the request, such as a 408 on an idle connection, still wait in the socket and are read as the response; the idle check before reuse is what catches them.  From then on the core reads while the body is still going out, so an early response is heard even from a server that stops reading.  Once the request head is out, a failed write only stops the upload, since a response may already be waiting; once the final response head has arrived, so does a stalled one.  The read gap counts only once writing is over: a server is silent while it receives a request.
   - Errors carry a cause (`localClose`, `peerClosed`, `timeout`, `protocol`, `limit`) and the number of request bytes written.  "Nothing written" (no write ever issued: the bytes of a write in flight may already be on the wire) is the evidence that makes a retry safe for any method.  A 408 on a reused connection before any response byte counts as "nothing processed", as Go treats it.

A **per-call planner** (`LeanHttp.Call`) runs in the caller's task: redirects (a hop limit ending in an error, credential headers stripped across origins, `Host` rewritten, content headers dropped when the method changes to GET, no URL-based cycle detection), retries (per hop, never across a redirect), backoff, the whole-call deadline, and opt-in retries of 429 and 503 honouring `Retry-After`.  This is the split Go makes between `Client` and `Transport`.

### Streaming

`Client.withResponse : Request → (Response BodyStream → Async α) → Async (Except Error α)`.  The body is pulled by the caller, so backpressure is natural: the exchange core reads from the socket only when the caller asks.  Leaving the callback abandons whatever is unread, which makes the connection non-reusable unless the rest arrives within a small drain limit.  Lean cannot stop the stream escaping its scope; using it afterwards raises an error, and the connection has been released regardless.  Holding a body open inside the callback while doing other slow work keeps one connection busy, and nothing else.

Request bodies: bytes (replayable), or a stream (not replayable, so never retried once any of it is written).

## What `Std.Http` provides

From v4.34.1: `Request`, `Response`, `Headers` (with validated names and values, which rules out header injection), `Method`, `Status` and the URI parser (IPv6 literals included).  The HTTP/1.1 machine in client mode (`Direction.sending`) and the pure redirect planner (`Protocol/H1/Redirect.lean`) come from the upstream stack's protocol layer instead, vendored under `LeanHttpProto`: v4.34.1's machine rejects a chunk-size line with extensions or a trailer section that arrives split across reads, which the stack fixes (measured; `NOTES.md`).  The per-call planner uses the redirect planner and adds its own hop limit, which ends in an error.  If a proof needs to see inside the machine (its `H1.lean` has 18 `partial def`s in v4.34.1, which no theorem can unfold), a separate codec written for proof becomes a later step, with the upstream machine as its test oracle.

## Socket lifecycle

v4.34.1's TCP client socket has `shutdown` (closing the write side) but no explicit close; the descriptor is released when the last reference is dropped.  The design therefore keeps references to a socket in exactly two places, the exchange in progress and the pool entry, and drops both when the connection ends.  An exit test checks that a process with connections closed in each way (end of response, abandoned body, timeout, error) exits promptly: the review saw processes hang at exit after a body was closed unread.  A pending receive can be cancelled, but a pending connect, write or name lookup cannot, and each holds its socket (or a thread of libuv's pool) until it ends: losing connect attempts are therefore abandoned rather than cancelled, and their sockets close when the kernel gives up on them.  `NOTES.md` records what each of these costs, measured.

## Defaults

`TCP_NODELAY` on; connect timeout 10 s per attempt, with a 250 ms stagger between attempts; whole-call deadline 5 minutes, which alone bounds name resolution; read gap 30 s, which also bounds each 64 KiB slice of a request write; at most 10 interim responses; buffered body limit 64 MiB; up to 2 retries of failed connects (full jitter, base 100 ms, cap 5 s); idle connections: 4 per origin, 4 s; an abandoned body is drained for reuse if the rest is at most 64 KiB and arrives within 100 ms; at most 10 redirects, then an error.  Slow upstream APIs (model calls that think for minutes before answering) need the deadline and the read gap raised; the defaults suit ordinary web APIs.

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
5. **Fuzzing** the exchange core with the toolchain's machine under AFL++ (persistent mode through a small C entry point; assertions abort under `LEAN_ABORT_ON_PANIC=1`): response bytes split at fuzzer-chosen points, with split invariance and a check of the reuse decision.  h11 as a differential oracle for framing.
6. **Ported cases** from curl, Go, hyper-util, OkHttp and h11 (`~/prog/lean-speed/notes/http-client-prior-art-tests.md`).
7. **Proofs** of the single-step properties (cheap, once the cores have the right types: cause-typed errors, an in-flight token), then the pool invariant ("returned or dropped exactly once"), then, if it proves tractable, liveness under the deadline.  Veil only if the plain explorer cannot settle an invariant.
8. **Real-socket tests** on loopback for `TCP_NODELAY`, connect timeouts per address, IPv6 literals, idle connections closed by the server, and prompt exit.

## From fuzzed properties to proved ones

Every property the fuzzer or the random runs check should end up as a theorem, with fuzzing kept as the cheap first line (Matthias, 2026-10-28).  The exchange core's properties hold whatever the HTTP/1.1 machine returns, so they can be proved about `Exchange.step` directly, treating the machine as opaque.  `LeanHttp/Exchange/Proofs.lean` and `LeanHttp/Exchange/Liveness.lean` do so for the single-step properties, for "a live exchange has a deadline ahead", and for liveness under the deadline; liveness assumes only that the shell, whenever the exchange is live, eventually reports an event at or after its next deadline, which a shell that sleeps until that deadline and then ticks does, as long as its sleep returns.  The codec's properties (termination, body length within `Content-Length`, no body after HEAD, 204 or 304, split invariance) live inside the vendored machine, whose `partial def`s no proof can unfold; proving them needs a codec of our own written for proof, with total functions, and the vendored machine and h11 then serve as its differential oracles under the fuzzer.

## Not yet

TLS (a transport class that carries the server name for SNI and distinguishes a clean TLS close from a truncated one; the request target form is already a parameter of the exchange core, so absolute-form for proxies needs no change to it), HTTP/2, proxies (CONNECT), cookies, authentication handlers, decompression (when it comes: off for HEAD and ranges, with a decompressed-size limit), middleware.

## Open questions

- Whether `recvSelector`'s non-blocking check reports end of input on an idle socket reliably (to be measured before milestone 2 relies on it).
- Whether a pending receive on an idle socket is what causes the exit hang the review saw.
- Whether milestone 2's exchange core should wrap the upstream machine or replace it, once a first proof shows how far the machine's `partial def`s get in the way.
