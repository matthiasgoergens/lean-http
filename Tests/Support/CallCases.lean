import LeanHttp.Call

/-!
# Cases for the planner's tests

Builders for requests, responses and failures, and the pools of origins, `Location` values and
fields that the unit tests, the random runs and the differential test draw from.
-/

open Std.Http LeanHttp LeanHttp.Call

instance : Inhabited URI.Origin :=
  ⟨{ scheme := default, host := .ipv4 (Std.Net.IPv4Addr.ofParts 127 0 0 1), port := 80 }⟩

instance : Inhabited State :=
  ⟨{ policy := {}, originalOrigin := default, given := [], bodyKind := .none,
     current := { origin := default, head := default, body := .original }, seed := 0, deadline := 0 }⟩

/-- The status with this code: a named one, or a custom one for a code `Std.Http` has no name for. -/
def statusOf (code : UInt16) : Status :=
  (Status.ofCode none code).getD .ok

/-- A field list from name and value strings (both must be valid). -/
def fieldsOf (pairs : List (String × String)) : Headers :=
  pairs.foldl (fun h (n, v) => h.insert! n v) .empty

/-- A request head for an absolute URI. -/
def headOf (method : Method) (uri : String) (fields : List (String × String) := []) : Request.Head :=
  { method, version := .v11, uri := .absoluteForm (URI.parse! uri), headers := fieldsOf fields }

/-- A response head with a status code and fields. -/
def respOf (code : UInt16) (fields : List (String × String) := []) (version : Version := .v11) :
    Response.Head :=
  { status := statusOf code, version, headers := fieldsOf fields }

/-- A redirect response to `location`. -/
def redirectTo (code : UInt16) (location : String) : Response.Head :=
  respOf code [("Location", location)]

/-- A failure. -/
def failureOf (cause : Cause) (delivery : Delivery) (written : Nat := 0) : Failure :=
  { cause, delivery, written }

/-- A connect failure, which never sends anything. -/
def connectFailure : Failure :=
  failureOf (.connect #[]) .notSent

/-- The fields of a head as (name, value) strings, in order. -/
def fieldStrings (h : Headers) : List (String × String) :=
  h.toList.map fun (n, v) => (n.value, v.value)

/-- The values of the field `name` (lower case). -/
def fieldValues (h : Headers) (name : String) : List String :=
  (fieldStrings h).filterMap fun (n, v) => if n == name then some v else none

/-- The path and query of a request target, as written in origin form. -/
def targetPathQuery : RequestTarget → String
  | .originForm p q => toString (RequestTarget.originForm p q)
  | .absoluteForm u => toString (RequestTarget.originForm u.path u.query)
  | t => toString t

/-- A request target as a string. -/
def targetString (t : RequestTarget) : String := toString t

/-- The methods the tests use. -/
def methodPool : List Method := [.get, .head, .post, .put, .delete, .patch, .options]

/-- The methods RFC 9110 section 9.2.2 calls idempotent, written out independently of `Std.Http`. -/
def idempotentMethods : List Method := [.get, .head, .put, .delete, .options, .trace]

/-- The body kinds. -/
def bodyKindPool : List BodyKind := [.none, .bytes, .stream]

/-- The origins requests start from. -/
def originPool : List String := ["http://a.test", "http://b.test", "https://a.test", "http://a.test:8080"]

/-- `Location` values: relative and absolute, same and other origin, and malformed ones. -/
def locationPool : List String := [
  "/new", "rel/x", "../up?y=2", "?only=query", "", "#frag", "//b.test/p", "//a.test/p",
  "http://a.test/p", "http://b.test/p?q=1#f", "https://a.test/s", "http://a.test:8080/p",
  "http://user:pw@b.test/p", "ftp://a.test/f", "http:/nohost", "http://a.test/x/../y/./z",
  "http://127.0.0.1:9/p", "mailto:x@y.test", "not a uri", "HTTP://A.TEST/caps", "http://a.test",
  "https://b.test:8443/q?z"]

/-- Credential fields, and their values. -/
def credentialPool : List (String × String) :=
  [("Authorization", "Bearer t0k"), ("Cookie", "sid=1"), ("Proxy-Authorization", "Basic eA==")]

/-- Other request fields: content, validators, hop-by-hop, and plain ones. -/
def otherFieldPool : List (String × String) := [
  ("Referer", "http://a.test/from"), ("Content-Type", "text/plain"), ("Content-Length", "5"),
  ("Content-Encoding", "gzip"), ("Content-Language", "en"),
  ("Last-Modified", "Sun, 06 Nov 1994 08:49:37 GMT"), ("If-None-Match", "\"e1\""),
  ("If-Modified-Since", "Sun, 06 Nov 1994 08:49:37 GMT"), ("Connection", "x-hop"), ("X-Hop", "1"),
  ("Keep-Alive", "timeout=5"), ("Transfer-Encoding", "chunked"), ("Accept", "*/*"),
  ("Digest", "sha-256=abc"), ("Origin", "http://a.test"), ("X-Custom", "v")]

/-- The lower-case names of the credential fields, written out independently of the planner. -/
def credentialNameStrings : List String := ["authorization", "cookie", "proxy-authorization"]

/-- The lower-case names of the content fields, written out independently of the planner. -/
def contentNameStrings : List String := ["content-type", "content-length", "content-encoding",
  "content-language", "content-location", "last-modified", "transfer-encoding", "digest",
  "content-digest", "repr-digest"]

/-- The scheme, host and port of an absolute-form target, as the checker computes them. -/
def targetOriginKey : RequestTarget → Option (String × String × Nat)
  | .absoluteForm u =>
    u.authority.map fun a =>
      let port := match a.port with
        | .value p => p.toNat
        | _ => if u.scheme.val == "https" then 443 else 80
      (u.scheme.val, toString a.host, port)
  | _ => none
