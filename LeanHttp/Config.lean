module

public import LeanHttp.Codec.Basic
public import LeanHttp.Call.Trace

public section

/-!
# Client configuration

Every limit and timeout of a call, with the defaults of the design.  Times are in milliseconds.
-/

namespace LeanHttp

set_option linter.all true

/--
Settings for the calls of a client (`Client.request`, `Client.withResponse`).

The defaults suit ordinary web APIs.  A slow upstream (a model that thinks for minutes before it
answers) needs `deadlineMs` and `readGapMs` raised.
-/
structure Config where
  /--
  Deadline for the whole call, across name resolution, connects, redirects, retries and the
  exchanges, including the time a streamed body is read (default: 5 minutes).  Must be positive:
  a call refuses zero as an invalid request.
  -/
  deadlineMs : Nat := 5 * 60 * 1000

  /--
  Time limit for one connect attempt to one address (default: 10 s).  Must be positive:
  a call refuses zero as an invalid request.
  -/
  connectTimeoutMs : Nat := 10 * 1000

  /--
  Delay before the next address is tried while the current attempt is still pending (default:
  250 ms).  The first attempt to succeed wins; the others are abandoned.  Zero starts every
  attempt of a round at once.
  -/
  connectStaggerMs : Nat := 250

  /--
  Longest time without progress on the connection (default: 30 s): between two reads of the
  response, where every byte resets it, or for one slice of the request (`writeChunkBytes`) to be
  accepted by the kernel.  Must be positive: a call refuses zero as an invalid request.
  -/
  readGapMs : Nat := 30 * 1000

  /--
  Most retries of one request (default: 2): of one hop of the call, counting from its first
  attempt.  The per-call planner retries a failure only when that is safe (`Call.plan`): a failed
  connect, or a closed connection or a read or write timeout when nothing was sent, or when the
  method is idempotent and the body can be sent again.  A connection from the pool that turns out
  to be closed is sent again without counting here (`Client.redispatch?`).
  -/
  maxRetriesPerHop : Nat := 2

  /--
  Most retries in the whole call, over all its hops (default: 4).
  -/
  retryBudget : Nat := 4

  /--
  Base of the exponential backoff before a retry (default: 100 ms).
  -/
  backoffBaseMs : Nat := 100

  /--
  Ceiling of the exponential backoff before a retry (default: 5 s).
  -/
  backoffCapMs : Nat := 5 * 1000

  /--
  Whether redirects (301, 302, 303, 307 and 308 with a `Location`) are followed (default: yes).
  When not, a redirect is delivered like any other response.
  -/
  followRedirects : Bool := true

  /--
  Most redirects followed in one call (default: 10).  One more fails the call with
  `Cause.tooManyRedirects`.
  -/
  maxRedirects : Nat := 10

  /--
  Whether a 429 (Too Many Requests) response is retried, after its `Retry-After` or the backoff
  (default: no).  Only a request that could be sent again after bytes reached the server (an
  idempotent method, a body that can be sent again) is retried.
  -/
  retry429 : Bool := false

  /--
  Whether a 503 (Service Unavailable) response is retried, like a 429 (default: no).
  -/
  retry503 : Bool := false

  /--
  Longest `Retry-After` honoured (default: 60 s).  A 429 or 503 that asks for a longer wait is
  delivered.
  -/
  maxRetryAfterMs : Nat := 60 * 1000

  /--
  Seed for the backoff jitter.  `none` (the default) draws one from the operating system.  The seed
  used is recorded in every error and result, so that a run can be replayed.
  -/
  backoffSeed : Option UInt64 := none

  /--
  Most interim (1xx) responses accepted before the final response (default: 10).
  -/
  maxInterimResponses : Nat := 10

  /--
  Largest response body `Client.request` reads into memory (default: 64 MiB).  A streamed body
  (`Client.withResponse`) has no limit: the caller reads what it wants.
  -/
  maxBodyBytes : Nat := 64 * 1024 * 1024

  /--
  Whether to set `TCP_NODELAY` on every socket (default: `true`).  Turning it off is only useful to
  measure what it does.
  -/
  noDelay : Bool := true

  /--
  Bytes asked for in each read from the socket (default: 64 KiB).  Must be positive:
  a call refuses zero as an invalid request.
  -/
  readChunkBytes : Nat := 64 * 1024

  /--
  Largest slice of the request handed to the socket in one write (default: 64 KiB).  A request no
  larger than this goes out in a single write.
  -/
  writeChunkBytes : Nat := 64 * 1024

  /--
  Whether connections are kept open after a call and reused by later calls to the same origin
  (default: `true`).  Requests then say `Connection: keep-alive`.  With `false`, every call opens a
  connection for each of its exchanges and closes it, sending `Connection: close`.
  -/
  pool : Bool := true

  /--
  Most idle connections kept per origin (default: 4).  A reusable connection that comes back while
  its origin has this many idle is closed instead.
  -/
  maxIdlePerOrigin : Nat := 4

  /--
  How long an idle connection is kept before it is closed (default: 4 s, below the keep-alive
  timeouts common servers use, 5 s and up).  It is closed when a call next uses the pool after that
  time, not by a timer.  Zero keeps no connection idle, which turns reuse off.
  -/
  idleTimeoutMs : Nat := 4 * 1000

  /--
  Most connections in use at once per origin, or `none` (the default) for no limit; only with
  `pool` on.  A call that finds its origin at the limit waits for a connection to come back, within
  its deadline; waiting calls are not served in order.  Zero is refused as an invalid request.
  -/
  maxActivePerOrigin : Option Nat := none

  /--
  Whether a pooled connection is checked before it is reused (default: `true`).  The check watches
  the connection for `idleCheckMs`: bytes, the end of input or an error mean the server closed it or
  sent something unasked (a 408, say), and the connection is closed and another one taken.  Without
  the check, a closed connection is found only when the request fails on it, and only some requests
  can then be sent again (`Client.redispatch?`).
  -/
  idleCheck : Bool := true

  /--
  How long the idle check watches a connection, in milliseconds (default: 0).  Zero still waits for
  one turn of the event loop, which sees whatever arrived while the connection was idle; a longer
  window also sees what arrives during it, and every reuse waits that long.  `NOTES.md` has the
  measurements behind the default.
  -/
  idleCheckMs : Nat := 0

  /--
  When a response body is left unread (a redirect or retried response, or a stream the caller left
  before its end), how many more body bytes may be read and discarded to keep the connection for
  reuse (default: 64 KiB).  A longer rest closes the connection instead.
  -/
  drainBytes : Nat := 64 * 1024

  /--
  How long the rest of an unread body may take to arrive and keep the connection (default:
  100 ms).
  -/
  drainMs : Nat := 100

  /--
  Called with every step of every call (`Call.Event`), in order, and the number of the call (the
  client numbers its calls from 0), for tracing; `Call.validate` checks the events of one call
  against the planner.  `none` (the default) records nothing.
  -/
  observe : Option (Nat → Call.Event → BaseIO Unit) := none

  /--
  Parser limits for the response head and framing.  Their `maxInterim` and `maxBody` are replaced
  by `maxInterimResponses` and `maxBodyBytes` above.
  -/
  limits : Codec.Config := {}

/--
The per-call planner's rules for `config`.
-/
def Config.policy (config : Config) : Call.Policy :=
  { followRedirects := config.followRedirects, maxRedirects := config.maxRedirects,
    maxRetriesPerHop := config.maxRetriesPerHop, retryBudget := config.retryBudget,
    backoffBaseMs := config.backoffBaseMs, backoffCapMs := config.backoffCapMs,
    retry429 := config.retry429, retry503 := config.retry503,
    maxRetryAfterMs := config.maxRetryAfterMs }

end LeanHttp
