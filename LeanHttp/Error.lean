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
What went wrong.
-/
inductive Cause where
  /--
  The client closed the connection on its own initiative.  Reserved for closing a client and for
  cancellation, which arrive with connection reuse; milestone 1 never produces it.
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
  The request was refused before any I/O (an unsupported scheme, a URI without a host).
  -/
  | invalidRequest (detail : String)
deriving Repr, Inhabited

/--
A failed call.
-/
structure Error where
  /--
  What went wrong.
  -/
  cause : Cause

  /--
  How far the request got.
  -/
  delivery : Delivery

  /--
  Request bytes the connection accepted before the call failed.
  -/
  written : Nat := 0

  /--
  The origin the call was for, as `host:port`.
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

end Delivery

namespace Cause

/--
`true` for a connect failure, the only cause the client retries.
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
    s!"{e.target}: {e.cause.describe}{detail} [{e.delivery.name}, seed {e.seed}]"

/--
Converts the error for code that works with `IO.Error`, as the throwing `Client.send` does.
-/
def toIOError (e : Error) : IO.Error :=
  .userError (toString e)

end Error

end LeanHttp
