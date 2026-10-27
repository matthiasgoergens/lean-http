module

public import Std.Http.Protocol.H1.Config

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
  (default: 5 minutes).
  -/
  deadlineMs : Nat := 5 * 60 * 1000

  /--
  Time limit for one connect attempt to one address (default: 10 s).
  -/
  connectTimeoutMs : Nat := 10 * 1000

  /--
  Delay before the next address is tried while the current attempt is still pending (default:
  250 ms).  The first attempt to succeed wins; the others are abandoned.
  -/
  connectStaggerMs : Nat := 250

  /--
  Longest silence allowed between two reads of the response (default: 30 s).  Every byte resets it.
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
  Bytes asked for in each read from the socket (default: 64 KiB).
  -/
  readChunkBytes : Nat := 64 * 1024

  /--
  Parser limits for the response head and framing.  The client sets `enableKeepAlive`,
  `maxBodySize` and `maxChunkSize` itself from the fields above.
  -/
  h1 : Std.Http.Protocol.H1.Config := {}

end LeanHttp
