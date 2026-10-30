module

public import Std.Net.Addr
public import Std.Http.Data.Status

public section

/-!
# Errors

A failed call is described by what went wrong (`Cause`) and by how far the request got
(`Delivery`).  The second is the evidence a caller needs to decide whether trying again is safe: a
request that was never sent can be retried whatever its method.
-/

namespace LeanHttp

set_option linter.all true

open Std.Net

/--
How far the request got before the call failed.
-/
inductive Delivery where
  /--
  No byte of the request was written to a socket, so the server cannot have seen it.  Retrying is
  safe for any method.
  -/
  | notSent

  /--
  Some or all of the request was written, but no complete response head came back.  The server may
  or may not have acted on it.
  -/
  | maybeDelivered

  /--
  The server answered with a final response head, so it received the request; the call failed
  afterwards (while reading the body, for instance).
  -/
  | responseReceived
deriving Repr, BEq, Inhabited, DecidableEq

/--
Which time limit ran out.
-/
inductive TimeoutKind where
  /--
  The per-gap read timeout: nothing arrived for `Config.readGapMs`.
  -/
  | read

  /--
  A slice of the request (`Config.writeChunkBytes`) was not accepted within `Config.readGapMs`.
  -/
  | write

  /--
  The deadline for the whole call, `Config.deadlineMs`.
  -/
  | deadline
deriving Repr, BEq, Inhabited, DecidableEq

/--
Which limit on the response was exceeded.
-/
inductive LimitKind where
  /--
  The body was larger than `Config.maxBodyBytes`.
  -/
  | body

  /--
  The head had too many fields or too many bytes (the `limits` of the parser).
  -/
  | headers

  /--
  More than `Config.maxInterimResponses` interim (1xx) responses arrived.
  -/
  | interim
deriving Repr, BEq, Inhabited, DecidableEq

/--
How one connect attempt to one address ended.
-/
inductive AttemptOutcome where
  /--
  The attempt did not complete within `Config.connectTimeoutMs`.
  -/
  | timedOut

  /--
  The attempt failed, for instance because the connection was refused.
  -/
  | failed (message : String)

  /--
  Another attempt succeeded or the call ended first, so this one was given up.
  -/
  | abandoned
deriving Repr, BEq, Inhabited

/--
One connect attempt: which round of attempts it belonged to (0 for the first, 1 for the first
retry), the address, and how it ended.
-/
structure ConnectAttempt where
  /--
  The round of attempts, counting from 0.
  -/
  round : Nat

  /--
  The address the attempt connected to.
  -/
  address : SocketAddress

  /--
  How the attempt ended.
  -/
  outcome : AttemptOutcome
deriving Inhabited

instance : Repr ConnectAttempt where
  reprPrec a _ := s!"\{ round := {a.round}, address := {a.address}, outcome := {repr a.outcome} }"

/--
What failed when a TLS connection was being set up, before any request byte was written.
-/
inductive TlsFailure where
  /--
  TLS could not be set up locally: no trust store was found, the CA file or a CA directory could
  not be loaded, the OpenSSL linked in is not version 3, or the server's name cannot be checked.
  Never retried.
  -/
  | setup (detail : String)

  /--
  The server's certificate was refused: its chain does not lead to a trusted certificate, it has
  expired, or it does not carry the server's name.  `detail` is OpenSSL's reason.  Never retried.
  -/
  | verify (detail : String)

  /--
  The handshake failed: the server sent an alert or broke the protocol, or the two sides have no
  protocol version or cipher in common, or the server chose an ALPN protocol other than
  `http/1.1`.  Never retried.
  -/
  | handshake (detail : String)

  /--
  The connection closed, or was reset, during the handshake.  Retried like a failed connect.
  -/
  | closed (detail : String)

  /--
  The handshake did not finish within `Config.tlsHandshakeTimeoutMs`.  Retried like a failed
  connect.  (The call's deadline passing during the handshake is `Cause.timeout .deadline`.)
  -/
  | timeout
deriving Repr, Inhabited

/--
What went wrong.
-/
inductive Cause where
  /--
  The client gave up on the call itself: the client was closed (`Client.close`) before the call
  took a connection, or the exchange was abandoned before the response head arrived.  It is never
  retried, so that closing a client cannot make it send a request again.
  -/
  | localClose

  /--
  The peer closed the connection, or the connection was lost, before a complete response arrived.
  -/
  | peerClosed

  /--
  A time limit ran out.
  -/
  | timeout (which : TimeoutKind)

  /--
  The peer sent something that is not a valid HTTP/1.1 response.
  -/
  | protocol (detail : String)

  /--
  The response exceeded a limit.
  -/
  | limit (which : LimitKind)

  /--
  No connection could be established: every attempt of every round failed.
  -/
  | connect (attempts : Array ConnectAttempt)

  /--
  The host name could not be resolved, or resolved to no address.  This is not retried.
  -/
  | resolve (host : String) (detail : String)

  /--
  A request was refused before it was sent: the call's own (an unsupported scheme, a URI without a
  host, a setting no call can meet), or the request of a redirect to a target the client cannot
  reach.
  -/
  | invalidRequest (detail : String)

  /--
  A redirect arrived after `limit` redirects had been followed (`Config.maxRedirects`).  The last
  redirect's status is the error's `status`.
  -/
  | tooManyRedirects (limit : Nat)

  /--
  A TLS connection could not be set up for an `https` target; nothing of the request was sent.  A
  failure of TLS after the handshake (a truncated connection, an alert) is a failed read instead,
  reported as `peerClosed` with a detail that says so.
  -/
  | tls (failure : TlsFailure)

  /--
  A streamed request body could not be sent as declared: its producer raised an error, or gave more
  or fewer bytes than the size it declared.  This is not retried.
  -/
  | requestBody (detail : String)
deriving Repr, Inhabited

namespace Call

/--
Why a failed exchange is not retried.
-/
inductive NoRetry where
  /--
  The cause is never retried: the client closed the connection itself, the call's deadline passed,
  the name did not resolve, the request was invalid, the response was malformed or too large, or TLS
  failed in a way another attempt would repeat (setup, the certificate, the handshake).
  -/
  | cause

  /--
  Request bytes may have reached the server, and the method is not idempotent or the body cannot be
  sent again.
  -/
  | delivered

  /--
  The response head had arrived.
  -/
  | responseReceived

  /--
  The current hop was retried `Policy.maxRetriesPerHop` times already.
  -/
  | hopLimit

  /--
  The call made `Policy.retryBudget` retries already.
  -/
  | budget

  /--
  The backoff would reach the call's deadline.
  -/
  | noTime
deriving Repr, DecidableEq

namespace NoRetry

/--
A short description for messages.
-/
def describe : NoRetry → String
  | .cause => "never retried"
  | .delivered => "the request may have been delivered and cannot be sent again"
  | .responseReceived => "the response had begun"
  | .hopLimit => "the request was retried as often as allowed"
  | .budget => "the call made as many retries as allowed"
  | .noTime => "the backoff would reach the deadline"

end NoRetry

end Call

/--
A failed call.
-/
structure Error where
  /--
  What went wrong.
  -/
  cause : Cause

  /--
  How far the call got: the furthest any of its requests got.  A call that followed a redirect, or
  retried a request that may have reached the server, has had requests delivered even if the one
  that failed was not sent, so `notSent` holds only when no request of the call can have reached a
  server.
  -/
  delivery : Delivery

  /--
  Request bytes the connection accepted before the call failed.
  -/
  written : Nat := 0

  /--
  The origin the call was for, as `scheme://host:port`.
  -/
  target : String := ""

  /--
  The seed of the backoff jitter, for replaying the call's schedule.
  -/
  seed : UInt64 := 0

  /--
  How many rounds of connect attempts were made.
  -/
  connectRounds : Nat := 0

  /--
  The status of the final response, when one arrived.
  -/
  status : Option Std.Http.Status := none

  /--
  A human-readable detail, such as the operating system's error message.
  -/
  detail : String := ""

  /--
  Whether the exchange that failed ran on a connection taken from the pool.
  -/
  reused : Bool := false

  /--
  Whether the call was sent a second time, on a fresh connection, after the pooled connection it
  first took turned out to be closed (`Client.request`); the error then describes the second
  attempt.
  -/
  redispatched : Bool := false

  /--
  Redirects the call followed before it failed: the request that failed is that of hop `hops`, the
  first request being hop 0.
  -/
  hops : Nat := 0

  /--
  Retries the call made (over all its hops) before it failed.
  -/
  retries : Nat := 0

  /--
  Why the failure was not retried, when the per-call planner judged it; `none` for an error found
  before any exchange (an invalid request), for the failures that follow a response (too many
  redirects, a deadline that passed before a redirect, a body that failed while it was read) and for
  a redirect to a target the client cannot reach.
  -/
  notRetried : Option Call.NoRetry := none
deriving Inhabited

namespace TimeoutKind

/--
A short name for messages.
-/
def name : TimeoutKind → String
  | .read => "read"
  | .write => "write"
  | .deadline => "deadline"

end TimeoutKind

namespace LimitKind

/--
A short name for messages.
-/
def name : LimitKind → String
  | .body => "body size"
  | .headers => "header size"
  | .interim => "interim responses"

end LimitKind

namespace Delivery

/--
A short name for messages.
-/
def name : Delivery → String
  | .notSent => "not sent"
  | .maybeDelivered => "maybe delivered"
  | .responseReceived => "response received"

/--
How far a request got, as a number: not sent 0, maybe delivered 1, response received 2.
-/
def rank : Delivery → Nat
  | .notSent => 0
  | .maybeDelivered => 1
  | .responseReceived => 2

/--
The further of two deliveries.
-/
def max (a b : Delivery) : Delivery :=
  if a.rank ≥ b.rank then a else b

end Delivery

namespace Cause

/--
`true` for a connect failure: no connection could be made, so nothing was sent.  The per-call
planner retries connect failures like the other causes it may retry (`Call.retryableCause`).
-/
def isConnect : Cause → Bool
  | .connect _ => true
  | _ => false

/--
A one-line description.
-/
def describe : Cause → String
  | .localClose => "the client closed the connection"
  | .peerClosed => "the connection closed before a complete response"
  | .timeout which => s!"{which.name} timeout"
  | .protocol detail => s!"invalid response: {detail}"
  | .limit which => s!"{which.name} limit exceeded"
  | .connect attempts =>
    let parts := attempts.toList.map fun a =>
      let outcome := match a.outcome with
        | .timedOut => "timed out"
        | .failed msg => msg
        | .abandoned => "abandoned"
      s!"{a.address} (round {a.round}): {outcome}"
    s!"could not connect: {String.intercalate "; " parts}"
  | .resolve host detail => s!"could not resolve {host}: {detail}"
  | .invalidRequest detail => s!"invalid request: {detail}"
  | .tooManyRedirects n => s!"more than {n} redirects"
  | .tls (.setup detail) => s!"TLS setup failed: {detail}"
  | .tls (.verify detail) => s!"TLS certificate verification failed: {detail}"
  | .tls (.handshake detail) => s!"TLS handshake failed: {detail}"
  | .tls (.closed detail) => s!"the connection closed during the TLS handshake: {detail}"
  | .tls .timeout => "TLS handshake timeout"
  | .requestBody detail => s!"request body: {detail}"

end Cause

namespace Error

/--
`true` when the server cannot have seen the request.
-/
def notSent (e : Error) : Bool :=
  e.delivery == .notSent

instance : ToString Error where
  toString e :=
    let detail := if e.detail.isEmpty then "" else s!" ({e.detail})"
    let hops := if e.hops > 0 then s!", after {e.hops} redirects" else ""
    let retries := if e.retries > 0 then s!", after {e.retries} retries" else ""
    s!"{e.target}: {e.cause.describe}{detail} [{e.delivery.name}{hops}{retries}, seed {e.seed}]"

/--
Converts the error for code that works with `IO.Error`, as the throwing `Client.send` does.
-/
def toIOError (e : Error) : IO.Error :=
  .userError (toString e)

end Error

end LeanHttp
