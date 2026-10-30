module

public import Std.Http.Data
public import LeanHttp.Exchange

public section

/-!
# What goes on the wire for one exchange

Two pure parts of the client that the record of a call (`LeanHttp.Call.Trace`) is checked against:
where a request goes and the head it is written with (`Client.plan`), and when an exchange on a
connection taken from the pool is sent once more on a fresh one (`Client.redispatch?`).
-/

namespace LeanHttp

set_option linter.all true

open Std.Http

namespace Client

/--
Where a request goes and what goes on the wire, worked out from its absolute-form target.
-/
structure Plan where
  /--
  The host to connect to.
  -/
  host : URI.Host

  /--
  The port to connect to.
  -/
  port : UInt16

  /--
  The request head as sent: origin-form target, `Host` field filled in.
  -/
  head : Request.Head

/--
Works out where `head` goes.  Its target must be an absolute `http` URI; the head sent carries the
origin-form target (`/` for an empty path) and a `Host` field, unless it has one already.
-/
def plan (head : Request.Head) : Except String Plan := do
  let .absoluteForm uri := head.uri
    | throw "the request target must be an absolute URI, such as http://host:port/path"
  if uri.scheme.val != "http" then
    throw s!"unsupported scheme {uri.scheme.val}: this client speaks plain HTTP only (no TLS yet)"
  let some host := uri.host?
    | throw "the URI has no host"
  let port := uri.port
  let path := if uri.path.segments.isEmpty then { uri.path with absolute := true } else uri.path
  let headers ←
    if head.headers.contains Header.Name.host then
      pure head.headers
    else
      let value := URI.Origin.hostHeader { scheme := uri.scheme, host, port }
      match Header.Value.ofString? value with
      | some value => pure (head.headers.insert Header.Name.host value)
      | none => throw s!"cannot write a Host field for {value}"
  return { host, port, head := { head with uri := .originForm path uri.query, headers } }

/--
The origin of a plan, as the pool keys it: `host:port`.
-/
def Plan.target (plan : Plan) : String :=
  s!"{plan.host}:{plan.port}"

/--
How the exchange of a reused connection began, as far as sending it again is concerned.
-/
inductive Ended where
  /--
  The final response head arrived, after `interim` interim responses.
  -/
  | response (head : Response.Head) (interim : Nat)

  /--
  The exchange failed before the final response head; `received` says whether any byte of a
  response had arrived.
  -/
  | failure (failure : Failure) (received : Bool)
deriving Repr

/--
Why an exchange on a reused connection may be sent again on a fresh one.
-/
inductive Redispatch where
  /--
  No byte of the request was written: the server cannot have seen it.  Safe for any method.  The
  exchange core counts a request as possibly delivered from its first write on, so on a reused
  connection this arises only if the exchange fails before writing; the idle check is what catches a
  connection the server closed before the request.
  -/
  | notSent

  /--
  The server answered 408 (Request Timeout) before any other response: it did not process the
  request, and RFC 9110 section 15.5.9 lets a client repeat it.  Bytes a server sent on an idle
  connection before it saw the request are read as the response, and a 408 is what servers send
  before they close an idle connection.  Safe for any method.
  -/
  | requestTimeout

  /--
  The connection closed, or failed, before any byte of a response arrived: most likely the server
  closed the idle connection as the request went out.  The server may have acted on the request, so
  only an idempotent method is sent again, as Go's transport does (RFC 9110 section 9.2.2).
  -/
  | closedBeforeResponse
deriving Repr, DecidableEq

/--
Whether an exchange on a reused connection that began as `ended` is sent again on a fresh
connection, and why.  It never is when the server may have acted on a request whose method is not
idempotent, except after a 408, which says it did not.  A body that cannot be sent again
(`replayable` false: a stream, which may have been read from once anything was written) is sent
again only if nothing was written.
-/
def redispatch? (method : Method) (replayable : Bool) : Ended → Option Redispatch
  | .response head interim =>
    if replayable && head.status == .requestTimeout && interim == 0 then some .requestTimeout
    else none
  | .failure f received =>
    if f.delivery == .notSent && (f.cause matches .peerClosed) then some .notSent
    else if replayable && !received && f.delivery == .maybeDelivered &&
        (f.cause matches .peerClosed) && method.isIdempotent then
      some .closedBeforeResponse
    else none

end Client

end LeanHttp
