module

public import Std.Http.Data

@[expose] public section

/-!
# Redirects

Whether a response is a redirect the client follows, and if so the request of the next hop
(RFC 9110 section 15.4, with the method rules of the Fetch standard's HTTP-redirect fetch):

- Only 301, 302, 303, 307 and 308 are followed.  300 leaves the choice to the user agent, 304 is a
  cache answer, 305 is deprecated and 306 unused (sections 15.4.1 and 15.4.5 to 15.4.7); any other
  3xx code has no defined redirect semantics.  These, and a redirect that is not followed, are
  delivered to the caller as they are.
- 303 makes the request a GET, except that a HEAD stays a HEAD (section 15.4.4); 301 and 302 turn
  a POST into a GET, as every user agent does (sections 15.4.2 and 15.4.3); every other combination
  keeps the method.  A request whose method changes loses its body and its content fields.
- A request that keeps its method keeps its body, and so needs the body to be replayable: a
  redirect that would have to send a streamed body again is not followed (section 15.4.8 says a
  user agent must not redirect such a request automatically).
- `Location` is resolved against the current request's URI (RFC 3986 section 5.2), its userinfo
  and fragment dropped, and only `http` and `https` targets are followed.
- Credential fields (`Authorization`, `Cookie`, `Proxy-Authorization`) go only to the origin they
  were given for, the origin of the call's first request: they are dropped on a hop to any other
  origin and given back on a hop that returns to it.  Origins are compared by scheme, host and port,
  so a hop from https to http is a hop to another origin.
- On a hop to another origin than the current one, `Referer` and the cache validators
  (`If-None-Match`, `If-Modified-Since`) are dropped and `Host` is rewritten.  Hop-by-hop fields
  (`Connection`, `Keep-Alive`, `Transfer-Encoding` and those `Connection` names) never carry over.

The rules follow the redirect planner of the upstream client stack (leanprover/lean4 PR 14548,
`Protocol/H1/Redirect.lean`), which the tests use as an oracle; `Tests/CallDiff.lean` lists where
and why they differ.
-/

namespace LeanHttp.Call

set_option linter.all true

open Std.Http

/--
The body of the call's original request, as far as sending it again is concerned.
-/
inductive BodyKind where
  /--
  No body.
  -/
  | none

  /--
  Bytes held in memory, which can be sent any number of times.
  -/
  | bytes

  /--
  A stream, which can be read only once: once any of it has been written it cannot be sent again.
  -/
  | stream
deriving Repr, DecidableEq, Inhabited

/--
Whether a body of this kind can be sent again.
-/
def BodyKind.replayable : BodyKind → Bool
  | .stream => false
  | _ => true

/--
What the request of a hop carries as its body.
-/
inductive HopBody where
  /--
  The body of the call's original request.
  -/
  | original

  /--
  No body: the method changed on a redirect.
  -/
  | empty
deriving Repr, DecidableEq, Inhabited

/--
One request of a call: the origin it goes to, its head (whose target is always an absolute URI) and
what it carries as its body.
-/
structure Hop where
  /--
  The origin the request is sent to.
  -/
  origin : URI.Origin

  /--
  The request head.  Its target is the absolute URI of the request.
  -/
  head : Request.Head

  /--
  The body the request carries.
  -/
  body : HopBody
deriving Repr

/--
Whether the request of `hop` can be sent again, when the original body is of kind `kind`.
-/
def Hop.replayable (hop : Hop) (kind : BodyKind) : Bool :=
  match hop.body with
  | .empty => true
  | .original => kind.replayable

/--
What makes two origins the same: scheme, host (as written in a URI, so case-normalised) and port.
-/
structure OriginKey where
  /--
  The scheme, lower case.
  -/
  scheme : String

  /--
  The host as it appears in a URI: a lower-case name, an IPv4 address, or an IPv6 address in
  brackets.
  -/
  host : String

  /--
  The port.
  -/
  port : UInt16
deriving Repr, DecidableEq

/--
The key that origins are compared by.
-/
def originKey (o : URI.Origin) : OriginKey :=
  { scheme := o.scheme.val, host := toString o.host, port := o.port }

/--
The fields of a request head, in order.
-/
abbrev Fields := List (Header.Name × Header.Value)

/--
The fields that carry credentials, which go only to the origin they were given for.
-/
def credentialNames : List Header.Name := [.authorization, .cookie, .proxyAuthorization]

/--
`Digest` (RFC 3230), which RFC 9110 section 15.4 names among the content fields.
-/
def digestName : Header.Name := .mk "digest"

/--
`Content-Digest` (RFC 9530).
-/
def contentDigestName : Header.Name := .mk "content-digest"

/--
`Repr-Digest` (RFC 9530).
-/
def reprDigestName : Header.Name := .mk "repr-digest"

/--
The fields that describe the request's content, which a request that loses its body must not keep
(RFC 9110 section 15.4: "remove content-specific header fields, including (but not limited to)
Content-Encoding, Content-Language, Content-Location, Content-Type, Content-Length, Digest,
Last-Modified"), with the framing field `Transfer-Encoding` and the newer digest fields.
-/
def contentNames : List Header.Name :=
  [.contentType, .contentLength, .contentEncoding, .contentLanguage, .contentLocation,
    .lastModified, .transferEncoding, digestName, contentDigestName, reprDigestName]

/--
Cache validators, which belong to a state of the resource the request first named.
-/
def validatorNames : List Header.Name := [.ifNoneMatch, .ifModifiedSince]

/--
Fields that belong to one connection, which never carry over to the next request.
-/
def hopByHopNames : List Header.Name := [.connection, .keepAlive, .transferEncoding]

/--
The field names a request's `Connection` fields nominate as hop-by-hop.  A value that does not
parse is ignored here: the fixed hop-by-hop fields are dropped regardless.
-/
def nominatedNames (fields : Fields) : List Header.Name :=
  fields.flatMap fun (name, value) =>
    if name = .connection then
      match Header.Connection.parse value with
      | some c => c.tokens.toList.filterMap Header.Name.ofString?
      | none => []
    else []

/--
`fields` without the fields named in `names`.
-/
def dropNames (names : List Header.Name) (fields : Fields) : Fields :=
  fields.filter fun (name, _) => !names.contains name

/--
The credential fields of `fields`, in order.
-/
def credentials (fields : Fields) : Fields :=
  fields.filter fun (name, _) => credentialNames.contains name

/--
The method of the next request: 303 makes it a GET unless it is a HEAD, 301 and 302 make a POST a
GET, and otherwise it is kept.
-/
def redirectMethod (method : Method) (code : Nat) : Method :=
  match code with
  | 303 => if method = .head then .head else .get
  | 301 | 302 => if method = .post then .get else method
  | _ => method

/--
The redirect codes the client follows.
-/
def followedCodes : List Nat := [301, 302, 303, 307, 308]

/--
The origin a `Location` reference points to, resolved against the current origin (RFC 3986
section 5.2.2), or `none` when an absolute reference names no host.
-/
def resolveOrigin (current : URI.Origin) : URIReference → Option URI.Origin
  | .absolute uri =>
    uri.authority.map fun auth =>
      let port := match auth.port with
        | .value p => p
        | _ => URI.Scheme.defaultPort uri.scheme
      { scheme := uri.scheme, host := auth.host, port }
  | .relative { authority := some auth, .. } =>
    let port := match auth.port with
      | .value p => p
      | _ => URI.Scheme.defaultPort current.scheme
    some { scheme := current.scheme, host := auth.host, port }
  | .relative _ => some current

/--
A resolved path as it goes on the wire: dot segments removed (RFC 3986 section 5.2.4) and absolute,
so that an empty path is sent as `/` (RFC 9112 section 3.2.1).
-/
def wirePath (path : URI.Path) : URI.Path :=
  { path.normalize with absolute := true }

/--
The path and query of the next request: those of the reference, or for a reference without an
authority, the reference merged with the current request's path and query (RFC 3986 section
5.2.2).
-/
def resolvePathQuery (ref : URIReference) (basePath : URI.Path) (baseQuery : Option URI.Query) :
    URI.Path × Option URI.Query :=
  match ref with
  | .absolute uri => (wirePath uri.path, uri.query)
  | .relative { authority := some _, path, query, .. } => (wirePath path, query)
  | .relative { authority := none, path, query, .. } =>
    let merged :=
      if path.isEmpty then basePath
      else if path.absolute then path
      else basePath.parent.join path
    let query := if path.isEmpty && query.isNone then baseQuery else query
    (wirePath merged, query)

/--
The absolute URI of a request to `origin` with this path and query: no userinfo, no fragment, and
the port written only when it is not the scheme's default.
-/
def targetUri (origin : URI.Origin) (path : URI.Path) (query : Option URI.Query) : URI :=
  let port : URI.Port :=
    if origin.port = URI.Scheme.defaultPort origin.scheme then .omitted else .value origin.port
  { scheme := origin.scheme, authority := some { host := origin.host, port }, path, query,
    fragment := none }

/--
The query of a request target.
-/
def targetQuery : RequestTarget → Option URI.Query
  | .originForm _ q => q
  | .absoluteForm uri => uri.query
  | _ => none

/--
On a hop to another origin than the current one, drops `Referer` and the cache validators.
-/
def crossOriginStep (crossOrigin : Bool) (fields : Fields) : Fields :=
  if crossOrigin then dropNames (.referer :: validatorNames) fields else fields

/--
When the method changes, drops the content fields and the cache validators.
-/
def methodStep (methodChanged : Bool) (fields : Fields) : Fields :=
  if methodChanged then dropNames (contentNames ++ validatorNames) fields else fields

/--
Drops the credential fields unless the next origin is the original one (`toOriginal`); there they
are kept if the current origin is the original one too (`fromOriginal`), and given back from the
original request (`firstCredentials`) if not.
-/
def credentialStep (toOriginal fromOriginal : Bool) (firstCredentials : Fields) (fields : Fields) :
    Fields :=
  if toOriginal then
    (if fromOriginal then fields else dropNames credentialNames fields ++ firstCredentials)
  else dropNames credentialNames fields

/--
On a hop to another origin than the current one, rewrites `Host`, if present, to `host`, or drops
it if the new origin's host cannot be written as a field value.
-/
def hostStep (crossOrigin : Bool) (host : Option Header.Value) (fields : Fields) : Fields :=
  if crossOrigin && fields.any (·.1 = .host) then
    dropNames [.host] fields ++ (host.map fun v => [(.host, v)]).getD []
  else fields

/--
The fields of the next request: hop-by-hop fields, and those the current request's `Connection`
fields name, are dropped, and then come `crossOriginStep`, `methodStep`, `credentialStep` and
`hostStep`.
-/
def nextFields (fields : Fields) (crossOrigin methodChanged toOriginal fromOriginal : Bool)
    (firstCredentials : Fields) (host : Option Header.Value) : Fields :=
  dropNames (hopByHopNames ++ nominatedNames fields) fields
    |> crossOriginStep crossOrigin
    |> methodStep methodChanged
    |> credentialStep toOriginal fromOriginal firstCredentials
    |> hostStep crossOrigin host

/--
Why a redirect response is not followed, and is delivered to the caller instead.
-/
inductive Refusal where
  /--
  There is no `Location` field.
  -/
  | noLocation

  /--
  The `Location` value is not a URI reference.
  -/
  | badLocation

  /--
  The `Location` is an absolute URI without a host.
  -/
  | noHost

  /--
  The `Location` names a scheme other than `http` and `https`.
  -/
  | scheme (name : String)

  /--
  The redirect keeps the method, so the body would have to be sent again, and it is a stream.
  -/
  | bodyNotReplayable
deriving Repr, DecidableEq

/--
What a response means for redirects.
-/
inductive Decision where
  /--
  Not a redirect the client follows (not one of 301, 302, 303, 307 and 308).
  -/
  | final

  /--
  A redirect that is not followed.
  -/
  | refuse (why : Refusal)

  /--
  Follow the redirect with this request.
  -/
  | follow (next : Hop)
deriving Repr

/--
Decides what `response` to the request of `current` means for redirects.  `kind` is the kind of the
call's original body, `original` the origin of the call's first request and `firstCredentials` its
credential fields.
-/
def decideRedirect (kind : BodyKind) (original : URI.Origin) (firstCredentials : Fields)
    (current : Hop) (response : Response.Head) : Decision :=
  let code := response.status.toCode.toNat
  if code ∉ followedCodes then .final else
  match response.headers.get? .location with
  | none => .refuse .noLocation
  | some value =>
  match URIReference.parse? value.value with
  | none => .refuse .badLocation
  | some ref =>
  match resolveOrigin current.origin ref with
  | none => .refuse .noHost
  | some origin =>
  if origin.scheme.val ≠ "http" ∧ origin.scheme.val ≠ "https" then
    .refuse (.scheme origin.scheme.val)
  else
  let method := redirectMethod current.head.method code
  let methodChanged := decide (method ≠ current.head.method)
  let body := if methodChanged then HopBody.empty else current.body
  if (Hop.mk origin current.head body).replayable kind = false then .refuse .bodyNotReplayable else
  let crossOrigin := decide (originKey origin ≠ originKey current.origin)
  let toOriginal := decide (originKey origin = originKey original)
  let fromOriginal := decide (originKey current.origin = originKey original)
  let (path, query) :=
    resolvePathQuery ref current.head.uri.pathOrRoot (targetQuery current.head.uri)
  let fields := nextFields current.head.headers.toList crossOrigin methodChanged toOriginal
    fromOriginal firstCredentials (Header.Value.ofString? origin.hostHeader)
  .follow {
    origin
    head := { current.head with
      method, uri := .absoluteForm (targetUri origin path query), headers := .ofList fields }
    body }

end LeanHttp.Call
