module

public import LeanHttp.Codec.Basic

public section

/-!
# Client configuration

Every limit and timeout of a call, with the defaults of the design.  Times are in milliseconds.
-/

namespace LeanHttp

set_option linter.all true

/--
Settings for `Client.request`.

The defaults suit ordinary web APIs.  A slow upstream (a model that thinks for minutes before it
answers) needs `deadlineMs` and `readGapMs` raised.
-/
structure Config where
  /--
  Deadline for the whole call, across name resolution, connects, retries and the exchange
  (default: 5 minutes).  Must be positive: `Client.request` refuses zero as an invalid request.
  -/
  deadlineMs : Nat := 5 * 60 * 1000

  /--
  Time limit for one connect attempt to one address (default: 10 s).  Must be positive:
  `Client.request` refuses zero as an invalid request.
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
  accepted by the kernel.  Must be positive: `Client.request` refuses zero as an invalid request.
  -/
  readGapMs : Nat := 30 * 1000

  /--
  How many times a failed connect is retried, after the first round of attempts (default: 2).
  Nothing has been sent when a connect fails, so this is safe for any method.
  -/
  maxConnectRetries : Nat := 2

  /--
  Base of the exponential backoff between connect rounds (default: 100 ms).
  -/
  backoffBaseMs : Nat := 100

  /--
  Ceiling of the exponential backoff between connect rounds (default: 5 s).
  -/
  backoffCapMs : Nat := 5 * 1000

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
  Largest response body read into memory (default: 64 MiB).
  -/
  maxBodyBytes : Nat := 64 * 1024 * 1024

  /--
  Whether to set `TCP_NODELAY` on every socket (default: `true`).  Turning it off is only useful to
  measure what it does.
  -/
  noDelay : Bool := true

  /--
  Bytes asked for in each read from the socket (default: 64 KiB).  Must be positive:
  `Client.request` refuses zero as an invalid request.
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
  connection of its own and closes it, sending `Connection: close`.
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
  can then be sent again (`Client.request`).
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
  Parser limits for the response head and framing.  Their `maxInterim` and `maxBody` are replaced
  by `maxInterimResponses` and `maxBodyBytes` above.
  -/
  limits : Codec.Config := {}

end LeanHttp
