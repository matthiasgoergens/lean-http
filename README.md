# lean-http

An HTTP/1.1 client for Lean 4.  It speaks plain HTTP only for now: there is no TLS, so `https` URLs are refused.

It is a Lake package that depends on nothing but the Lean toolchain.  Requests and responses are `Std.Http`'s types (`Request`, `Response`, `Headers`), and the library adds the client: name resolution, connects with a timeout per address, a connection pool, redirects, retries with backoff, deadlines and streamed response bodies.

## How it is built, and what is proved

Every decision the client makes is taken by one of four pure step functions, which do no I/O:

- the **response codec** (`LeanHttp.Codec`) parses a response, byte by byte or in bulk, given the request method;
- the **exchange core** (`LeanHttp.Exchange`) runs one request and response on one connection: it is told what happened (bytes read, bytes written, end of input, a tick of the clock) and answers with what to do next (write, read, deliver the head or body bytes, finish, fail);
- the **per-call planner** (`LeanHttp.Call`) decides after each exchange whether to deliver the response, follow a redirect, send the request again after a delay, or fail;
- the **pool core** (`LeanHttp.Pool`) decides which connection each exchange uses.

The shell around them (`LeanHttp.Client`, `LeanHttp.Body`, `LeanHttp.Connect`) performs the socket operations and the timers, reports what happened to the cores and does what they say.  `DESIGN.md` describes the design and `NOTES.md` the decisions and measurements behind it.

The cores' properties are proved in Lean:

- **The codec** (`LeanHttp/Codec/Proofs.lean` and `LeanHttp/Codec/Proofs/`): its result does not depend on how the input is cut into reads; it never delivers more body than `Content-Length` says, nothing for HEAD, 204 or 304, and nothing beyond the body limit; and the head and body it reports are the ones received: the bytes are the interim heads, the head and a body of the kind its framing declares, and the body delivered is that body's payload.
- **The exchange core** (`LeanHttp/Exchange/Proofs.lean`, `Liveness.lean`, `Response.lean`): no response head is delivered before the request head has been written; a connection is declared reusable only when the bytes received are exactly one complete response, framed with certainty, with nothing after it; until an exchange fails, and unless the caller abandoned the body, the body delivered is a prefix of the body decoded from the bytes received; and every exchange ends by its deadline, provided the shell keeps reporting events when they fall due.
- **The planner** (`LeanHttp/Call/Proofs.lean`): `Authorization`, `Cookie` and `Proxy-Authorization` never go to an origin other than the first request's; once a byte of a request may have reached the server, it is retried only if its method is idempotent and its body can be replayed (a 307 or 308 redirect still sends a POST again with its body, as the server asked); a call the client gave up on itself is never retried; every retry's delay ends before the call's deadline and within its cap; a call follows at most `maxRedirects` redirects and fails on the next; a 303 turns the request into a GET (a HEAD stays a HEAD), and a method change drops the body and the content fields.
- **The pool** (`LeanHttp/Pool/Proofs.lean`): every connection is idle, checked out or gone, and only one of them; the hand-outs and returns of a connection alternate; a connection given back as not reusable, or dropped, is never handed out again; the caps on idle and active connections per origin hold; and no connection is handed out after its idle timeout.

`lake build` checks every proof: the proof modules are roots of the library target.  The four scripts `scripts/proof-axioms.lean`, `codec-axioms.lean`, `call-axioms.lean` and `pool-axioms.lean` print the axioms of the main theorems, and CI requires that each depends on nothing beyond `propext`, `Classical.choice` and `Quot.sound`, so on no `sorry`.

The theorems are about the cores.  That the shell does what the cores say, and reports to them truthfully what the sockets did, is not proved.  It is tested:

- With `Config.observe` the client records every step of every call: each request as written, each decision with its clock, each wait and the error.  `Call.validate` replays such a record through a planner of its own and rejects any request, wait or error the planner did not call for.  The real-socket suite checks every call it makes this way.
- The real-socket suite (`tests/net/run.sh`) runs the client over loopback against local servers that misbehave on purpose: servers that close idle connections or send a 408 on them, that drop SYNs, stall mid-body, answer an upload early or send malformed responses.  It checks outcomes, connection reuse, timings, and that the process exits promptly afterwards.
- The pure suites drive the cores through fixed traces of known defects, through random runs with properties checked at every step, and through bounded exhaustive exploration, with planted bugs as positive controls.  The codec is compared with the HTTP/1.1 parser of the client proposed for `Std.Http` ([leanprover/lean4#14548](https://github.com/leanprover/lean4/pull/14548)), which `scripts/vendor.sh` generates from a lean4 commit for the tests; the library does not import it.  The exchange core with the codec inside it is also fuzzed with AFL++ (`fuzz/`).

The `Retry-After` parser and the resolution of redirect targets are tested, not proved.

## Installation

Add the package to your `lakefile.lean`, pinned to a commit:

```lean
require «lean-http» from git "https://github.com/matthiasgoergens/lean-http" @ "<commit>"
```

or to your `lakefile.toml`:

```toml
[[require]]
name = "lean-http"
git = "https://github.com/matthiasgoergens/lean-http"
rev = "<commit>"
```

and `import LeanHttp`.  Your package must use the same Lean toolchain as lean-http: `leanprover/lean4:v4.34.1`, the version in `lean-toolchain` and the only one CI checks.

## Making requests

`Client.request` sends a request and reads the whole response body into memory.  It returns `Async (Except Error (Response ByteArray))`; `.block` runs it from `IO`.  From `examples/RequestExample.lean`:

```lean
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
```

A POST with a JSON body:

```lean
let json := "{\"name\": \"lean-http\", \"stars\": 5}"
let req := Request.post (.parse! s!"{base}/echo")
  |>.header! "Content-Type" "application/json"
  |>.body json.toUTF8
```

The target must be an absolute `http` URI.  The client writes the framing and `Connection` fields itself, replacing any the request has: `Content-Length` for the body (none for an empty body when the method does not expect one) and `Connection: keep-alive` (`Connection: close` with pooling off).  It adds `Host` when the request has none.  One `Client` may be shared by any number of tasks; its calls share its connection pool.  `Client.send` is a variant that throws the error as an `IO.Error`.

## Streaming a response body

`Client.withResponse` hands the response to a callback that pulls the body in pieces as it arrives, so a large body is never held in memory.  From `examples/StreamExample.lean`:

```lean
let req := Request.get (.parse! s!"{base}/numbers?count=100000") |>.body .empty
let result ← (client.withResponse req fun response => do
  let mut bytes := 0
  let mut pieces := 0
  while let some piece ← response.body.read do
    bytes := bytes + piece.size
    pieces := pieces + 1
  return (response.line.status.toCode, bytes, pieces)).block
```

The call returns the callback's result, or an `Error`.  Redirects and retries happen before the callback runs: it sees only the final response.  The client reads from the socket only as fast as the callback reads, and a streamed body has no size limit, but the call's deadline covers reading it.  When the callback returns, or throws, the rest of the body is abandoned: read and discarded if it is short and arrives quickly, keeping the connection for reuse, and otherwise the connection is closed.  An error the stream raises (the connection closed early, a timeout) that leaves the callback becomes the call's `Error`; any other exception from the callback is raised again once the connection is released.  The stream must not be used after the callback ends; if it is, it raises an error.

## Configuration

`Client.new` takes a `Config`; every field has a default.  From `examples/StreamExample.lean`, a client for a slow upstream:

```lean
def patientClient : BaseIO Client :=
  Client.new {
    deadlineMs := 15 * 60 * 1000  -- the whole call, retries and body included
    readGapMs := 5 * 60 * 1000    -- the longest silence while the response arrives
    maxRetriesPerHop := 3
    retry503 := true              -- retried only for idempotent requests
    maxRedirects := 3
    maxIdlePerOrigin := 8
  }
```

The main settings, with their defaults (times in milliseconds):

| Setting | Default | Meaning |
| --- | --- | --- |
| `deadlineMs` | 5 minutes | The whole call: name resolution, connects, redirects, retries, the exchanges, and reading a streamed body. |
| `connectTimeoutMs` | 10 s | One connect attempt to one address. |
| `connectStaggerMs` | 250 | Delay before the next address is tried while an attempt is pending. |
| `readGapMs` | 30 s | The longest time without progress: between two reads of the response, or for one 64 KiB slice of the request to be accepted. |
| `maxRetriesPerHop`, `retryBudget` | 2, 4 | Retries of one request, and in the whole call. |
| `backoffBaseMs`, `backoffCapMs` | 100, 5 s | Exponential backoff with full jitter before each retry.  `backoffSeed` fixes the jitter's seed, which every result and error records. |
| `retry429`, `retry503`, `maxRetryAfterMs` | off, off, 60 s | Retry these statuses after their `Retry-After`, up to the limit, for requests that may be sent again. |
| `followRedirects`, `maxRedirects` | on, 10 | Follow 301, 302, 303, 307 and 308; one redirect more than the limit fails the call. |
| `maxBodyBytes` | 64 MiB | The largest body `Client.request` reads; `withResponse` has no limit. |
| `pool` | on | Keep connections open and reuse them for the same origin. |
| `maxIdlePerOrigin`, `idleTimeoutMs` | 4, 4 s | Idle connections kept per origin, and for how long. |
| `maxActivePerOrigin` | none | A cap on connections in use per origin; calls at the cap wait, within their deadline. |
| `idleCheck` | on | Check an idle connection for a close or stray bytes before reusing it. |

A failure is retried only when that is safe: a failed connect, or a closed connection or a read or write timeout when nothing of the request was written, or one of those when the method is idempotent and the body can be sent again.  The call's deadline, a name that does not resolve, a malformed response and a limit are never retried.  Separately, a request whose pooled connection turns out to have been closed by the server is sent once more on a fresh connection when that is safe (`Client.redispatch?`), without counting as a retry.  `LeanHttp/Config.lean` documents every field.

## Errors

`Client.request` never throws: a failure is an `Error`.  Its `cause` says what went wrong (`connect`, `resolve`, `timeout`, `peerClosed`, `protocol`, `limit`, `tooManyRedirects`, `invalidRequest`, `localClose`), and its `delivery` says how far the call got, which decides whether you can safely try again:

- `notSent`: no byte of any request of the call was written, so the server cannot have seen it.  Sending it again is safe whatever the method.
- `maybeDelivered`: request bytes were written but no complete response head came back.  The server may or may not have acted on the request.
- `responseReceived`: the server answered with a final response head, so it received the request; the call failed afterwards, while the body was read or on one redirect too many.

The delivery is the furthest any request of the call got, so a call that followed a redirect or retried a request that may have arrived is never `notSent`.  The error also says why the client did not retry it (`notRetried`), how many redirects and retries it made, and the backoff seed.  From `examples/RequestExample.lean`:

```lean
def advice (err : Error) : String :=
  match err.delivery with
  | .notSent => "the server cannot have seen the request: sending it again is safe"
  | .maybeDelivered => "the server may have acted on the request: send it again only if that is harmless"
  | .responseReceived => "the server answered, and the call failed afterwards"
```

## Current limits

- No TLS: an `https` request, or a redirect to one, fails with `invalidRequest`.  No HTTP/2, no proxies, no cookies and no decompression.
- Request bodies are byte arrays; streamed request bodies are not built.
- A call cannot be cancelled.  `Client.close` closes the idle connections and refuses later calls, but calls in flight run on.
- Exiting the process.  On v4.34.1 a process can hang at exit when a socket receive is still pending, a bug in Lean's task manager that [leanprover/lean4#15743](https://github.com/leanprover/lean4/pull/15743) fixes (open as of 2026-10-27); the client ends every receive before a call returns, and the real-socket suite checks that processes exit promptly.  A pending connect, write or name lookup cannot be cancelled on v4.34.1: an abandoned connect attempt holds its socket until the kernel gives up on it (about two minutes with Linux's defaults), and a name lookup cut off by the deadline keeps running until the resolver gives up, which can delay exit and has crashed the process at exit.  `NOTES.md` has the measurements.

## Running the tests and checking the proofs

`scripts/ci.sh` runs everything CI runs, and `scripts/ci.sh vendor build axioms` just the build and the axiom check.  Any warning or `sorry` in the build fails it.  It needs elan (or the toolchain's `lake` on the `PATH`), Python 3 and Git.  Most test executables import the vendored upstream parser in `vendor/`, which it generates from a shallow fetch of lean4 the first time, or from a lean4 clone that has the commit `scripts/vendor.sh` names (`LEAN4_CLONE`).  Each step's output goes to `out/ci/`.

The pieces, from the repository root:

- `lake build` builds the library and checks every proof.
- `lake env lean scripts/proof-axioms.lean` prints the axioms of the exchange core's main theorems (likewise `codec-`, `call-` and `pool-axioms.lean`); `scripts/check-axioms.py` checks them.
- `lake build unit-tests && .lake/build/bin/unit-tests`, and likewise `pool-tests` and `call-tests`; after `scripts/ci.sh vendor`, also `codec-tests`, `response-codec-tests`, `core-tests`, `codec-diff` and `call-diff`.  Each documents its arguments at the top of its file in `Tests/`.
- `lake build net-client && bash tests/net/run.sh` runs the real-socket suite.  It skips, and says so, what the machine cannot run: some scenarios want IPv6 on loopback, names added to `/etc/hosts` (`tests/net/hosts`), `net.ipv4.tcp_syn_retries` at 2, or root.
- `examples/run.sh` builds the examples and runs them against `examples/server.py`.
