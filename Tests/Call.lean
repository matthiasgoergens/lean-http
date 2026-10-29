import LeanHttp.Call
import Tests.Support.CallCases
import Tests.Support.Gen

/-!
# Tests of the per-call planner

Three parts, each printing one line per check:

1. **Unit tests** for each rule of the planner and for the `Retry-After` parser.
2. **Random runs**: seeded sequences of outcomes (responses with random statuses, `Location`s and
   `Retry-After`s, failures with random causes and delivery), driven through `Call.start` and
   `Call.plan` with random policies and clocks.  A checker with its own model of the call, built
   only from the requests the planner returned, checks every step against the rules the theorems
   state.
3. **Planted bugs**: the same runs through planners with one rule broken each (by changing the
   planner's result after the fact); the checker must catch every one.

Exits with status 1 if any check fails.

Usage: `call-tests [runs] [seed]` (defaults: 20000 runs, seed 1).
-/

open Std.Http LeanHttp LeanHttp.Call

/-- The checks run so far: name and whether it passed. -/
abbrev Checks := StateT (Array (String × Bool)) IO

def check (name : String) (ok : Bool) (detail : String := "") : Checks Unit := do
  let suffix := if ok || detail.isEmpty then "" else s!": {detail}"
  IO.println s!"{if ok then "PASS" else "FAIL"} {name}{suffix}"
  modify (·.push (name, ok))

def checkEq {α : Type} [BEq α] [Repr α] (name : String) (got expected : α) : Checks Unit :=
  check name (got == expected) s!"expected {repr expected}, got {repr got}"

/-! ## Helpers -/

/-- A short description of a step. -/
def stepName : Step → String
  | .deliver => "deliver"
  | .follow next => s!"follow {next.head.method} {targetString next.head.uri}"
  | .retry d k => s!"retry {d} {repr k}"
  | .fail (.failure f why) => s!"fail {f.cause.describe} ({repr why})"
  | .fail (.tooManyRedirects n) => s!"fail tooManyRedirects {n}"
  | .fail .deadline => "fail deadline"

/-- Starts a call, panicking if it cannot start. -/
def started (head : Request.Head) (kind : BodyKind := .none) (policy : Policy := {})
    (seed : UInt64 := 0) (deadline : Nat := 1000000) : State :=
  match start policy head kind seed deadline with
  | .ok st => st
  | .error e => panic! s!"start failed: {repr e}"

/-- The clock the unit tests decide at. -/
def at0 : Clock := { now := 0, wallSec := 784111777 }

/-- The next request, if the step follows a redirect. -/
def followed? : Step → Option Hop
  | .follow next => some next
  | _ => none

/-- Whether the step delivers the response. -/
def isDeliver : Step → Bool
  | .deliver => true
  | _ => false

/-- The reason a step fails with a failure, if it does. -/
def noRetry? : Step → Option NoRetry
  | .fail (.failure _ why) => some why
  | _ => none

/-- The delay and kind of a retry step. -/
def retry? : Step → Option (Nat × DelayKind)
  | .retry d k => some (d, k)
  | _ => none

/-- Whether the step fails with `tooManyRedirects`. -/
def isTooMany : Step → Bool
  | .fail (.tooManyRedirects _) => true
  | _ => false

instance : BEq DelayKind := ⟨fun a b => decide (a = b)⟩
instance : BEq NoRetry := ⟨fun a b => decide (a = b)⟩
instance : BEq BodyKind := ⟨fun a b => decide (a = b)⟩
instance : BEq HopBody := ⟨fun a b => decide (a = b)⟩

/-! ## Unit tests: starting a call -/

def startChecks : Checks Unit := do
  let reject (head : Request.Head) : Option StartError :=
    match start {} head .none 0 0 with
    | .ok _ => none
    | .error e => some e
  check "start refuses an origin-form target"
    (reject { method := .get, version := .v11, uri := .originForm! "/x" } == some .notAbsolute)
  check "start refuses ftp" (reject (headOf .get "ftp://a.test/x") == some (.scheme "ftp"))
  check "start refuses a URI without a host" (reject (headOf .get "http:/x") == some .noHost)
  check "start accepts https" (reject (headOf .get "https://a.test/x") == none)
  let head := headOf .post "http://a.test/x" [("Authorization", "a"), ("X-Custom", "v")]
  let st := started head .bytes
  check "the first hop is the request as given"
    (fieldStrings st.current.head.headers == fieldStrings head.headers &&
      targetString st.current.head.uri == targetString head.uri && st.current.body == .original)
  checkEq "the credentials given are recorded" (fieldStrings (Headers.ofList st.firstCredentials))
    [("authorization", "a")]

/-! ## Unit tests: redirects -/

/-- The form a POST of bytes with credentials, content and other fields. -/
def formPost : Request.Head :=
  headOf .post "http://a.test/a/b/c?x=1" [("Host", "a.test"), ("Authorization", "Bearer t0k"),
    ("Cookie", "sid=1"), ("Proxy-Authorization", "Basic eA=="), ("Content-Type", "text/plain"),
    ("Content-Encoding", "gzip"), ("Digest", "sha-256=abc"), ("Referer", "http://a.test/from"),
    ("If-None-Match", "\"e1\""), ("Connection", "x-hop"), ("X-Hop", "1"), ("Keep-Alive", "5"),
    ("X-Custom", "v")]

/-- The step a response leads to from the start of a call of `head`. -/
def firstStep (head : Request.Head) (kind : BodyKind) (resp : Response.Head)
    (policy : Policy := {}) : State × Step :=
  plan (started head kind policy) at0 (.response resp)

def redirectChecks : Checks Unit := do
  -- Method rewriting.
  let methodAfter (m : Method) (kind : BodyKind) (code : UInt16) : Option Method :=
    (followed? (firstStep (headOf m "http://a.test/x") kind (redirectTo code "/y")).2).map
      (·.head.method)
  checkEq "303 turns POST into GET" (methodAfter .post .bytes 303) (some .get)
  checkEq "303 turns PUT into GET" (methodAfter .put .bytes 303) (some .get)
  checkEq "303 keeps HEAD" (methodAfter .head .none 303) (some .head)
  checkEq "303 keeps GET" (methodAfter .get .none 303) (some .get)
  checkEq "301 turns POST into GET" (methodAfter .post .bytes 301) (some .get)
  checkEq "302 turns POST into GET" (methodAfter .post .stream 302) (some .get)
  checkEq "302 keeps PUT with a replayable body" (methodAfter .put .bytes 302) (some .put)
  checkEq "302 does not follow PUT with a streamed body" (methodAfter .put .stream 302) none
  checkEq "307 keeps POST" (methodAfter .post .bytes 307) (some .post)
  checkEq "308 keeps DELETE" (methodAfter .delete .none 308) (some .delete)
  checkEq "307 does not follow POST with a streamed body" (methodAfter .post .stream 307) none
  checkEq "308 does not follow GET with a streamed body" (methodAfter .get .stream 308) none
  checkEq "307 follows GET with a streamed body that is empty" (methodAfter .get .none 307) (some .get)
  -- Body and content fields.
  let (_, s303) := firstStep formPost .bytes (redirectTo 303 "/done")
  match followed? s303 with
  | none => check "303 is followed" false (stepName s303)
  | some next =>
    check "303: no body" (next.body == .empty)
    check "303: content fields and validators dropped"
      ((fieldStrings next.head.headers).all fun (n, _) =>
        !(contentNameStrings.contains n || n == "if-none-match"))
    checkEq "303: target" (targetString next.head.uri) "http://a.test/done"
    check "303 to the same origin keeps the credentials"
      (credentialNameStrings.all fun n => !(fieldValues next.head.headers n).isEmpty)
    check "hop-by-hop fields and those Connection names are dropped"
      ((fieldStrings next.head.headers).all fun (n, _) =>
        !(["connection", "x-hop", "keep-alive", "transfer-encoding"].contains n))
    check "other fields are kept" (fieldValues next.head.headers "x-custom" == ["v"])
    check "a same-origin hop keeps Referer and Host"
      (fieldValues next.head.headers "referer" == ["http://a.test/from"] &&
        fieldValues next.head.headers "host" == ["a.test"])
  let (_, s307) := firstStep formPost .bytes (redirectTo 307 "/again")
  match followed? s307 with
  | none => check "307 is followed" false (stepName s307)
  | some next =>
    check "307: the body goes again" (next.body == .original)
    check "307: content fields kept"
      (fieldValues next.head.headers "content-type" == ["text/plain"] &&
        fieldValues next.head.headers "digest" == ["sha-256=abc"])
  -- Statuses that are not followed.
  for code in [200, 300, 304, 305, 306, 399, 404] do
    check s!"{code} is delivered" (isDeliver (firstStep formPost .bytes (redirectTo code "/y")).2)
  check "a redirect without Location is delivered"
    (isDeliver (firstStep formPost .bytes (respOf 302)).2)
  for loc in ["not a uri", "ftp://a.test/f", "http:/nohost", "mailto:x@y.test"] do
    check s!"a redirect to {loc.quote} is delivered"
      (isDeliver (firstStep formPost .bytes (redirectTo 302 loc)).2)
  check "a redirect is delivered when redirects are off"
    (isDeliver (firstStep formPost .bytes (redirectTo 302 "/y") { followRedirects := false }).2)
  -- Resolution of Location.
  let targetAfter (loc : String) : String :=
    match followed? (firstStep (headOf .get "http://a.test/a/b/c?x=1") .none (redirectTo 302 loc)).2 with
    | some next => targetString next.head.uri
    | none => "(not followed)"
  checkEq "relative path" (targetAfter "rel/x") "http://a.test/a/b/rel/x"
  checkEq "dot segments" (targetAfter "../up?y=2") "http://a.test/a/up?y=2"
  checkEq "query only" (targetAfter "?only=query") "http://a.test/a/b/c?only=query"
  checkEq "empty reference" (targetAfter "") "http://a.test/a/b/c?x=1"
  checkEq "fragment only" (targetAfter "#frag") "http://a.test/a/b/c?x=1"
  checkEq "protocol-relative" (targetAfter "//b.test/p") "http://b.test/p"
  checkEq "userinfo dropped" (targetAfter "http://user:pw@b.test/p") "http://b.test/p"
  checkEq "fragment dropped" (targetAfter "http://b.test/p?q=1#f") "http://b.test/p?q=1"
  checkEq "dot segments in an absolute URI" (targetAfter "http://a.test/x/../y/./z") "http://a.test/y/z"
  checkEq "empty path becomes /" (targetAfter "http://b.test") "http://b.test/"
  checkEq "explicit port kept" (targetAfter "http://a.test:8080/p") "http://a.test:8080/p"
  checkEq "default port omitted" (targetAfter "http://a.test:80/p") "http://a.test/p"
  checkEq "scheme and host lower case" (targetAfter "HTTP://A.TEST/caps") "http://a.test/caps"

def originChecks : Checks Unit := do
  let creds (h : Headers) : List String :=
    credentialNameStrings.filter fun n => !(fieldValues h n).isEmpty
  -- To another host.
  let (st1, s1) := firstStep formPost .bytes (redirectTo 307 "http://b.test/p")
  match followed? s1 with
  | none => check "cross-origin 307 is followed" false (stepName s1)
  | some next =>
    checkEq "cross-origin: no credential field" (creds next.head.headers) []
    checkEq "cross-origin: Host rewritten" (fieldValues next.head.headers "host") ["b.test"]
    checkEq "cross-origin: Referer and validators dropped"
      ((fieldValues next.head.headers "referer") ++ fieldValues next.head.headers "if-none-match") []
    checkEq "cross-origin: other fields kept" (fieldValues next.head.headers "x-custom") ["v"]
    -- And back.
    let (_, s2) := plan st1 at0 (.response (redirectTo 307 "http://a.test/back"))
    match followed? s2 with
    | none => check "back to the original origin is followed" false (stepName s2)
    | some back =>
      checkEq "back at the original origin: credentials given back" (creds back.head.headers)
        credentialNameStrings
      checkEq "back at the original origin: Host rewritten" (fieldValues back.head.headers "host")
        ["a.test"]
  -- A credential field the first request's Connection names is hop-by-hop: never given back.
  let nominated := headOf .get "http://a.test/x" [("Connection", "authorization"), ("Authorization", "a"),
    ("Cookie", "c")]
  let (stN, _) := firstStep nominated .none (redirectTo 302 "http://b.test/")
  match followed? (plan stN at0 (.response (redirectTo 302 "http://a.test/back"))).2 with
  | none => check "back at the original origin after a nominated credential is followed" false
  | some back =>
    checkEq "a credential the first request's Connection names is not given back"
      (creds back.head.headers) ["cookie"]
  -- https to http on the same host.
  let secure := headOf .get "https://a.test/x" [("Authorization", "a"), ("Cookie", "c")]
  match followed? (firstStep secure .none (redirectTo 302 "http://a.test/x")).2 with
  | none => check "https to http is followed" false
  | some next => checkEq "https to http: no credential field" (creds next.head.headers) []
  -- Another port.
  match followed? (firstStep formPost .bytes (redirectTo 307 "http://a.test:8080/p")).2 with
  | none => check "a hop to another port is followed" false
  | some next =>
    checkEq "another port: no credential field" (creds next.head.headers) []
    checkEq "another port: Host has the port" (fieldValues next.head.headers "host") ["a.test:8080"]
  -- No Host to rewrite.
  match followed? (firstStep (headOf .get "http://a.test/x") .none (redirectTo 302 "http://b.test/")).2 with
  | none => check "a hop without Host is followed" false
  | some next => checkEq "no Host field is added" (fieldValues next.head.headers "host") []

def hopChecks : Checks Unit := do
  -- The hop limit fails the call.
  let policy : Policy := { maxRedirects := 2 }
  let st := started (headOf .get "http://a.test/x") .none policy
  let (st, s1) := plan st at0 (.response (redirectTo 302 "/1"))
  let (st, s2) := plan st at0 (.response (redirectTo 302 "/2"))
  let (_, s3) := plan st at0 (.response (redirectTo 302 "/3"))
  check "two redirects followed under a limit of 2" ((followed? s1).isSome && (followed? s2).isSome)
  check "the third fails with tooManyRedirects" (isTooMany s3) (stepName s3)
  check "a limit of 0 fails at the first redirect"
    (isTooMany (firstStep (headOf .get "http://a.test/x") .none (redirectTo 302 "/1")
      { maxRedirects := 0 }).2)
  -- No cycle detection: the same URL again.
  let st0 := started (headOf .post "http://a.test/items") .bytes
  let (st1, s1) := plan st0 at0 (.response (redirectTo 303 "/items"))
  check "POST /items, 303 to /items: GET /items follows"
    ((followed? s1).map (fun n => (n.head.method, targetString n.head.uri)) ==
      some (.get, "http://a.test/items"))
  let mut st := st1
  let mut follows := 1
  let mut last := Step.deliver
  for _ in [0:20] do
    let (st', s) := plan st at0 (.response (redirectTo 302 "/items"))
    st := st'
    last := s
    match s with
    | .follow _ => follows := follows + 1
    | _ => break
  check "the same URL is followed until the hop limit, which fails" (follows == 10 && isTooMany last)
    s!"{follows} followed, then {stepName last}"
  -- The deadline.
  let stLate := started (headOf .get "http://a.test/x") .none {} 0 100
  check "a redirect after the deadline fails"
    (match (plan stLate { now := 100, wallSec := 784111777 } (.response (redirectTo 302 "/y"))).2 with
     | .fail .deadline => true
     | _ => false)

/-! ## Unit tests: retries -/

def retryChecks : Checks Unit := do
  let get := headOf .get "http://a.test/x"
  let post := headOf .post "http://a.test/x"
  let put := headOf .put "http://a.test/x"
  let afterFailure (head : Request.Head) (kind : BodyKind) (f : Failure) (policy : Policy := {}) :
      Step :=
    (plan (started head kind policy 42) at0 (.failure f)).2
  -- Connect failures: any method, with the backoff.
  let s := afterFailure post .stream connectFailure
  checkEq "a connect failure of a streamed POST is retried after the backoff" (retry? s)
    (some (Backoff.delayMs 100 5000 42 0, .backoff))
  let st := started post .stream {} 42
  let (st, _) := plan st at0 (.failure connectFailure)
  let (st, s2) := plan st at0 (.failure connectFailure)
  let (_, s3) := plan st at0 (.failure connectFailure)
  checkEq "the second retry draws the next delay" (retry? s2) (some (Backoff.delayMs 100 5000 42 1, .backoff))
  checkEq "the third failure exceeds the retries per hop" (noRetry? s3) (some .hopLimit)
  -- Maybe delivered.
  let peer (d : Delivery) (written : Nat := 0) := failureOf .peerClosed d written
  checkEq "maybe delivered POST: not retried" (noRetry? (afterFailure post .bytes (peer .maybeDelivered 10)))
    (some .delivered)
  check "maybe delivered GET: retried" ((retry? (afterFailure get .none (peer .maybeDelivered 10))).isSome)
  check "maybe delivered PUT of bytes: retried" ((retry? (afterFailure put .bytes (peer .maybeDelivered 3))).isSome)
  checkEq "maybe delivered PUT of a stream: not retried"
    (noRetry? (afterFailure put .stream (peer .maybeDelivered 3))) (some .delivered)
  checkEq "not sent but bytes counted: treated as maybe delivered"
    (noRetry? (afterFailure post .bytes (peer .notSent 3))) (some .delivered)
  check "not sent POST after the connection closed: retried" ((retry? (afterFailure post .bytes (peer .notSent))).isSome)
  checkEq "a response received: not retried" (noRetry? (afterFailure get .none (peer .responseReceived 10)))
    (some .responseReceived)
  -- Causes.
  checkEq "localClose, nothing sent: not retried"
    (noRetry? (afterFailure get .none (failureOf .localClose .notSent))) (some .cause)
  checkEq "localClose, maybe delivered: not retried"
    (noRetry? (afterFailure get .none (failureOf .localClose .maybeDelivered 5))) (some .cause)
  for (name, cause) in [("deadline", Cause.timeout .deadline), ("protocol", .protocol "x"),
      ("limit", .limit .body), ("resolve", .resolve "a.test" "x"), ("invalidRequest", .invalidRequest "x")] do
    checkEq s!"{name}: not retried" (noRetry? (afterFailure get .none (failureOf cause .notSent))) (some .cause)
  check "read timeout on GET: retried"
    ((retry? (afterFailure get .none (failureOf (.timeout .read) .maybeDelivered 10))).isSome)
  -- Time and budget.
  let late := plan (started get .none {} 42 1000) { now := 1000, wallSec := 784111777 } (.failure connectFailure)
  checkEq "no time left: not retried" (noRetry? late.2) (some .noTime)
  let longBackoff : Policy := { backoffBaseMs := 10000, backoffCapMs := 10000 }
  let d := Backoff.delayMs 10000 10000 42 0
  checkEq "a backoff that ends at the deadline: not retried"
    (noRetry? (plan (started get .none longBackoff 42 d) at0 (.failure connectFailure)).2) (some .noTime)
  checkEq "a backoff that ends just before the deadline: retried"
    (retry? (plan (started get .none longBackoff 42 (d + 1)) at0 (.failure connectFailure)).2)
    (some (d, .backoff))
  let st := started get .none { retryBudget := 1, maxRetriesPerHop := 5 }
  let (st, _) := plan st at0 (.failure connectFailure)
  checkEq "the budget ends retries" (noRetry? (plan st at0 (.failure connectFailure)).2) (some .budget)
  -- Retries stay on the hop.
  let st := started (headOf .post "http://a.test/x" [("Authorization", "a")]) .bytes
  let (st, _) := plan st at0 (.failure connectFailure)
  let (st, _) := plan st at0 (.response (redirectTo 303 "http://b.test/y"))
  let (st', s) := plan st at0 (.failure connectFailure)
  check "after a redirect, a retry sends the redirected request"
    ((retry? s).isSome && targetString st'.current.head.uri == "http://b.test/y" &&
      st'.current.head.method == .get && st'.attempts == 1 && st'.retries == 2)

def statusChecks : Checks Unit := do
  let get := headOf .get "http://a.test/x"
  let opt : Policy := { retry503 := true, retry429 := true }
  let after (head : Request.Head) (kind : BodyKind) (resp : Response.Head) (policy : Policy := opt)
      (clock : Clock := at0) (deadline := 1000000) : Step :=
    (plan (started head kind policy 42 deadline) clock (.response resp)).2
  check "503 is delivered by default" (isDeliver (after get .none (respOf 503 [("Retry-After", "2")]) {}))
  checkEq "opt-in 503 with Retry-After: 2" (retry? (after get .none (respOf 503 [("Retry-After", "2")])))
    (some (2000, .retryAfter))
  checkEq "opt-in 429 with an HTTP-date, from the response's Date"
    (retry? (after get .none (respOf 429 [("Retry-After", "Sun, 06 Nov 1994 08:49:47 GMT"),
      ("Date", "Sun, 06 Nov 1994 08:49:40 GMT")]))) (some (7000, .retryAfter))
  checkEq "an HTTP-date without Date: from the wall clock"
    (retry? (after get .none (respOf 503 [("Retry-After", "Sun, 06 Nov 1994 08:49:47 GMT")])))
    (some (10000, .retryAfter))
  checkEq "a date in the past: no wait"
    (retry? (after get .none (respOf 503 [("Retry-After", "Sun, 06 Nov 1994 08:00:00 GMT")])))
    (some (0, .retryAfter))
  check "Retry-After beyond maxRetryAfterMs: delivered"
    (isDeliver (after get .none (respOf 503 [("Retry-After", "120")])))
  check "Retry-After reaching the deadline: delivered"
    (isDeliver (after get .none (respOf 503 [("Retry-After", "1")]) opt at0 1000))
  checkEq "Retry-After ending just before the deadline: retried"
    (retry? (after get .none (respOf 503 [("Retry-After", "1")]) opt at0 1001)) (some (1000, .retryAfter))
  check "503 to a POST: delivered"
    (isDeliver (after (headOf .post "http://a.test/x") .bytes (respOf 503 [("Retry-After", "1")])))
  check "503 to a PUT of a stream: delivered"
    (isDeliver (after (headOf .put "http://a.test/x") .stream (respOf 503 [("Retry-After", "1")])))
  checkEq "503 without Retry-After: the backoff" (retry? (after get .none (respOf 503)))
    (some (Backoff.delayMs 100 5000 42 0, .backoff))
  checkEq "an invalid Retry-After: the backoff" (retry? (after get .none (respOf 503 [("Retry-After", "soon")])))
    (some (Backoff.delayMs 100 5000 42 0, .backoff))
  check "429 is delivered when only 503 is opted into"
    (isDeliver (after get .none (respOf 429 [("Retry-After", "1")]) { retry503 := true }))

/-! ## Unit tests: `Retry-After` -/

def retryAfterChecks : Checks Unit := do
  let now := 1793232000 -- 2026-10-29T00:00:00Z
  let p (s : String) := RetryAfter.parse s now
  checkEq "delay-seconds" (p "120") (some (.seconds 120))
  checkEq "delay-seconds with whitespace" (p " 7\t") (some (.seconds 7))
  checkEq "empty" (p "") none
  checkEq "a fraction" (p "1.5") none
  checkEq "negative" (p "-1") none
  -- The expected times come from Python's calendar.timegm.
  checkEq "IMF-fixdate" (p "Sun, 06 Nov 1994 08:49:37 GMT") (some (.date 784111777))
  checkEq "RFC 850 date" (p "Sunday, 06-Nov-94 08:49:37 GMT") (some (.date 784111777))
  checkEq "asctime date" (p "Sun Nov  6 08:49:37 1994") (some (.date 784111777))
  checkEq "asctime date with a two-digit day" (p "Wed Mar 01 12:34:56 2000") (some (.date 951914096))
  checkEq "29 February in a leap year" (p "Thu, 29 Feb 2024 00:00:00 GMT") (some (.date 1709164800))
  checkEq "29 February in another year" (p "Wed, 29 Feb 2023 00:00:00 GMT") none
  checkEq "hour 25" (p "Sun, 06 Nov 1994 25:00:00 GMT") none
  checkEq "lower-case day name" (p "sun, 06 Nov 1994 08:49:37 GMT") none
  checkEq "trailing text" (p "Sun, 06 Nov 1994 08:49:37 GMT x") none
  checkEq "a time zone other than GMT" (p "Sun, 06 Nov 1994 08:49:37 UTC") none
  checkEq "two-digit year 50 years ahead" (p "Wednesday, 01-Jan-76 00:00:00 GMT") (some (.date 3345062400))
  checkEq "two-digit year more than 50 years ahead" (p "Saturday, 01-Jan-77 00:00:00 GMT")
    (some (.date 220924800))
  checkEq "year of the epoch" (RetryAfter.yearOf 0) 1970
  checkEq "year of the last second of 2024" (RetryAfter.yearOf 1735689599) 2024
  checkEq "year of the first second of 2025" (RetryAfter.yearOf 1735689600) 2025
  checkEq "a date before 1970 counts as 1970" (p "Thu, 01 Jan 1960 00:00:00 GMT") (some (.date 0))

/-! ## Random runs -/

/-- Which rule a planted bug breaks, or none. -/
inductive Mutation where
  | none
  | leakCredentials
  | resendDelivered
  | retryLocalClose
  | delayToDeadline
  | deliverAtLimit
  | keepPostOn303
  | keepContentOnChange
  | retryAcrossRedirect
  | keepHost
deriving Repr, BEq, Inhabited

/-- All planted bugs. -/
def mutations : List Mutation := [.leakCredentials, .resendDelivered, .retryLocalClose,
  .delayToDeadline, .deliverAtLimit, .keepPostOn303, .keepContentOnChange, .retryAcrossRedirect,
  .keepHost]

/-- The planner, with one rule broken by changing its result. -/
def mutatedPlan (m : Mutation) (st : State) (clock : Clock) (outcome : Outcome) : State × Step :=
  let (st', step) := plan st clock outcome
  let withFields (hop : Hop) (extra : Fields) : Hop :=
    { hop with head := { hop.head with headers := .ofList (hop.head.headers.toList ++ extra) } }
  match m, step, outcome with
  | .leakCredentials, .follow next, _ =>
    let next := withFields next (st.firstCredentials.filter fun e => !(next.head.headers.toList.contains e))
    ({ st' with current := next }, .follow next)
  | .resendDelivered, .fail (.failure _ .delivered), _ => (st.retried, .retry 0 .backoff)
  | .retryLocalClose, .fail (.failure f .cause), _ =>
    match f.cause with
    | .localClose => (st.retried, .retry 0 .backoff)
    | _ => (st', step)
  | .delayToDeadline, .retry _ k, _ => (st', .retry (st.deadline - clock.now) k)
  | .deliverAtLimit, .fail (.tooManyRedirects _), _ => (st', .deliver)
  | .keepPostOn303, .follow next, .response head =>
    if head.status.toCode == 303 && st.current.head.method == .post then
      let next := { next with head := { next.head with method := .post } }
      ({ st' with current := next }, .follow next)
    else (st', step)
  | .keepContentOnChange, .follow next, _ =>
    if next.head.method != st.current.head.method then
      let next := withFields next [(.contentType, .mk "text/plain")]
      ({ st' with current := next }, .follow next)
    else (st', step)
  | .retryAcrossRedirect, .follow next, _ =>
    -- Sends the previous request again instead of following.
    let _ := next
    (st.retried, .retry 0 .backoff)
  | .keepHost, .follow next, _ =>
    let old := st.current.head.headers.toList.filter (·.1 == .host)
    let fields := next.head.headers.toList.filter (·.1 != .host)
    let next := { next with head := { next.head with headers := .ofList (fields ++ old) } }
    ({ st' with current := next }, .follow next)
  | _, _, _ => (st', step)

/-- The checker's model of a call, built only from the requests the planner returned. -/
structure CallModel where
  /-- The policy (from the generator). -/
  policy : Policy
  /-- The body kind. -/
  kind : BodyKind
  /-- The origin of the first request, from its target. -/
  originalKey : String × String × Nat
  /-- The request being sent. -/
  sent : Request.Head
  /-- Whether it carries the original body. -/
  carriesBody : Bool := true
  /-- The deadline. -/
  deadline : Nat
  /-- Redirects followed. -/
  follows : Nat := 0
  /-- Retries of this hop. -/
  hopRetries : Nat := 0
  /-- Retries in the call. -/
  totalRetries : Nat := 0

/-- The `Location` values in the pool that no planner should follow. -/
def unfollowable : List String := ["not a uri", "ftp://a.test/f", "http:/nohost", "mailto:x@y.test"]

/-- The method after a redirect, by the rules written out independently. -/
def expectedMethod (m : Method) (code : Nat) : Method :=
  if code == 303 then (if m == .head then .head else .get)
  else if (code == 301 || code == 302) && m == .post then .get
  else m

/-- `Host` for an origin key, as the checker writes it. -/
def hostFor (key : String × String × Nat) : String :=
  let (scheme, host, port) := key
  if port == (if scheme == "https" then 443 else 80) then host else s!"{host}:{port}"

/-- Whether a failure may have sent bytes, as the checker sees it. -/
def sentBytes : Outcome → Bool
  | .response _ => true
  | .failure f => f.delivery != .notSent || f.written > 0

/--
Checks one step: the model before it, what happened, and the planner's answer.  Returns the
violations, and the model after the step.
-/
def checkCallStep (model : CallModel) (clock : Clock) (outcome : Outcome) (st' : State) (step : Step) :
    List String × CallModel := Id.run do
  let mut bad : List String := []
  let fields (h : Request.Head) := fieldStrings h.headers
  match step with
  | .follow next =>
    let code := match outcome with
      | .response h => h.status.toCode.toNat
      | .failure _ => 0
    if model.follows + 1 > model.policy.maxRedirects then bad := "hop limit exceeded" :: bad
    let key := targetOriginKey next.head.uri
    if key.isNone then bad := "next target is not absolute" :: bad
    let key := key.getD ("", "", 0)
    if key != model.originalKey && (fields next.head).any (credentialNameStrings.contains ·.1) then
      bad := "credentials sent to another origin" :: bad
    if code == 303 && next.head.method != (if model.sent.method == .head then .head else .get) then
      bad := "303 did not yield GET (or HEAD)" :: bad
    if next.head.method != model.sent.method then
      if next.head.method != .get then bad := "method changed to something other than GET" :: bad
      if next.body != .empty then bad := "body kept across a method change" :: bad
      if (fields next.head).any (contentNameStrings.contains ·.1) then
        bad := "content field kept across a method change" :: bad
    if next.head.method != expectedMethod model.sent.method code then
      bad := "method not as RFC 9110 and Fetch say" :: bad
    let prevKey := (targetOriginKey model.sent.uri).getD ("", "", 0)
    if key != prevKey && (fields next.head).any (fun (n, v) => n == "host" && v != hostFor key) then
      bad := "Host not rewritten" :: bad
    let expectKey : OriginKey := { scheme := key.1, host := key.2.1, port := key.2.2.toUInt16 }
    if originKey next.origin != expectKey then
      bad := "hop origin disagrees with its target" :: bad
    if st'.current.head.method != next.head.method then bad := "state does not hold the next request" :: bad
    if outcome matches .failure _ then bad := "followed a failure" :: bad
    let carries := next.body == .original
    if next.head.method == model.sent.method && carries != model.carriesBody then
      bad := "body changed without a method change" :: bad
    if carries && model.kind == .stream && sentBytes outcome then
      bad := "a streamed body would be sent again" :: bad
    let model' : CallModel :=
      { model with sent := next.head, carriesBody := carries, follows := model.follows + 1, hopRetries := 0 }
    return (bad, model')
  | .retry d k =>
    if sentBytes outcome &&
        !(idempotentMethods.contains model.sent.method && (!model.carriesBody || model.kind != .stream)) then
      bad := "resent after bytes may have reached the server" :: bad
    match outcome with
    | .failure f =>
      if f.cause matches .localClose then bad := "localClose retried" :: bad
      if f.delivery == .responseReceived then bad := "retried after the response arrived" :: bad
    | .response h =>
      let code := h.status.toCode.toNat
      if !((code == 429 && model.policy.retry429) || (code == 503 && model.policy.retry503)) then
        bad := "retried a response that is not an opted-in 429 or 503" :: bad
    if !(d < model.deadline - clock.now) then bad := "delay reaches the deadline" :: bad
    if k == .backoff && d > model.policy.backoffCapMs then bad := "backoff beyond its cap" :: bad
    if k == .retryAfter && d > model.policy.maxRetryAfterMs then bad := "Retry-After beyond its limit" :: bad
    if targetString st'.current.head.uri != targetString model.sent.uri ||
        st'.current.head.method != model.sent.method || fields st'.current.head != fields model.sent then
      bad := "a retry changed the request" :: bad
    if model.hopRetries + 1 > model.policy.maxRetriesPerHop then bad := "retries per hop exceeded" :: bad
    if model.totalRetries + 1 > model.policy.retryBudget then bad := "retry budget exceeded" :: bad
    return (bad, { model with hopRetries := model.hopRetries + 1, totalRetries := model.totalRetries + 1 })
  | .fail (.tooManyRedirects _) =>
    if model.follows != model.policy.maxRedirects then bad := "tooManyRedirects below the limit" :: bad
    return (bad, model)
  | .deliver =>
    match outcome with
    | .response h =>
      let code := h.status.toCode.toNat
      let location := (h.headers.get? .location).map (·.value)
      let methodChanges := expectedMethod model.sent.method code != model.sent.method
      let followable := [301, 302, 303, 307, 308].contains code && model.policy.followRedirects &&
        (match location with
         | some l => !unfollowable.contains l
         | none => false) &&
        (methodChanges || !model.carriesBody || model.kind != .stream)
      if followable then bad := "a followable redirect was delivered" :: bad
    | .failure _ => bad := "delivered a failure" :: bad
    return (bad, model)
  | .fail _ => return (bad, model)

/-- One random step's outcome and the time that passes before it. -/
def genOutcome : Gen (Nat × Outcome) := do
  let dt ← pick [0, 1, 10, 100, 1000, 5000]
  if (← below 10) < 6 then
    let code ← pickWeighted ([(6, 301), (6, 302), (6, 303), (6, 307), (6, 308), (4, 429), (4, 503),
      (2, 200), (1, 300), (1, 304), (1, 404)] : List (Nat × UInt16))
    let mut fields : List (String × String) := []
    if (← below 10) < 9 then fields := fields ++ [("Location", ← pick locationPool)]
    if (← below 2) == 0 then
      fields := fields ++ [("Retry-After", ← pick ["0", "1", "2", "120", "Sun, 06 Nov 1994 08:49:47 GMT",
        "Sun, 06 Nov 1994 08:00:00 GMT", "soon"])]
    if (← below 3) == 0 then fields := fields ++ [("Date", "Sun, 06 Nov 1994 08:49:37 GMT")]
    return (dt, .response (respOf code fields))
  else
    let cause ← pickWeighted [(5, Cause.connect #[]), (5, .peerClosed), (3, .timeout .read),
      (2, .timeout .write), (1, .timeout .deadline), (3, .localClose), (1, .protocol "x"),
      (1, .limit .body), (1, .resolve "a.test" "x"), (1, .invalidRequest "x")]
    let delivery ← pick [Delivery.notSent, .notSent, .maybeDelivered, .responseReceived]
    let written ← pick [0, 0, 7]
    return (dt, .failure (failureOf cause delivery written))

/-- A random first request, policy, seed and deadline. -/
def genCall : Gen (Request.Head × BodyKind × Policy × UInt64 × Nat) := do
  let origin ← pick originPool
  let path ← pick ["/", "/a/b/c?x=1", "/items"]
  let method ← pick methodPool
  let kind ← pick bodyKindPool
  let mut fields : List (String × String) := []
  for f in credentialPool ++ otherFieldPool do
    if (← below 3) == 0 then fields := fields ++ [f]
  if (← below 2) == 0 then
    fields := fields ++ [("Host", hostFor ((targetOriginKey (.absoluteForm (URI.parse! origin))).get!))]
  let policy : Policy := {
    followRedirects := (← below 10) != 0, maxRedirects := (← below 5), maxRetriesPerHop := (← below 4),
    retryBudget := (← below 6), backoffBaseMs := (← pick [0, 10, 100]), backoffCapMs := (← pick [0, 50, 5000]),
    retry429 := (← below 2) == 0, retry503 := (← below 2) == 0,
    maxRetryAfterMs := (← pick [0, 1000, 60000]) }
  let seed := (← below 1000000).toUInt64
  let deadline ← pick [0, 50, 1000, 100000, 10000000]
  return (headOf method (origin ++ path) fields, kind, policy, seed, deadline)

/-- What the random runs found. -/
structure RunStats where
  /-- Runs made. -/
  runs : Nat := 0
  /-- Steps checked. -/
  steps : Nat := 0
  /-- Steps by kind: deliver, follow, retry, fail. -/
  delivers : Nat := 0
  follows : Nat := 0
  retries : Nat := 0
  fails : Nat := 0
  /-- Violations by property, with the first run index for each. -/
  violations : List (String × Nat × Nat) := []
  /-- How often each kind of step was taken. -/
  kinds : List (String × Nat) := []

/-- The kind of a step, for the coverage histogram. -/
def stepKind (st : State) : Step → String
  | .deliver => "deliver"
  | .follow next =>
    if originKey next.origin != originKey st.current.origin then "follow to another origin"
    else if next.head.method != st.current.head.method then "follow with a method change"
    else "follow"
  | .retry _ .backoff => "retry after the backoff"
  | .retry _ .retryAfter => "retry after Retry-After"
  | .fail (.failure _ why) =>
    "fail: " ++ match why with
      | .cause => "cause" | .delivered => "delivered" | .responseReceived => "responseReceived"
      | .hopLimit => "hopLimit" | .budget => "budget" | .noTime => "noTime"
  | .fail (.tooManyRedirects _) => "fail: tooManyRedirects"
  | .fail .deadline => "fail: deadline"

/-- Counts a step kind. -/
def RunStats.count (s : RunStats) (kind : String) : RunStats :=
  if s.kinds.any (·.1 == kind) then
    { s with kinds := s.kinds.map fun (k, n) => if k == kind then (k, n + 1) else (k, n) }
  else { s with kinds := s.kinds ++ [(kind, 1)] }

/-- Records a violation. -/
def RunStats.record (s : RunStats) (property : String) (run : Nat) : RunStats :=
  match s.violations.find? (·.1 == property) with
  | some _ => { s with violations := s.violations.map fun (p, n, r) =>
      if p == property then (p, n + 1, r) else (p, n, r) }
  | none => { s with violations := s.violations ++ [(property, 1, run)] }

/-- Runs `n` random calls through the planner broken by `m`. -/
def randomRuns (m : Mutation) (n : Nat) (seed : UInt64) : RunStats := Id.run do
  let mut rng : Rng := ⟨seed⟩
  let mut stats : RunStats := {}
  for run in [0:n] do
    let ((head, kind, policy, cseed, deadline), r) := genCall.run rng
    rng := r
    let wall := 784111777
    let mut now := 0
    match start policy head kind cseed deadline with
    | .error _ => stats := stats.record "start refused a valid request" run
    | .ok st0 =>
      let mut st := st0
      let mut model : CallModel := {
        policy, kind, sent := head, deadline,
        originalKey := (targetOriginKey head.uri).getD ("", "", 0) }
      stats := { stats with runs := stats.runs + 1 }
      for _ in [0:30] do
        let ((dt, outcome), r) := genOutcome.run rng
        rng := r
        now := now + dt
        let clock : Clock := { now, wallSec := wall }
        let (st', step) := mutatedPlan m st clock outcome
        let (bad, model') := checkCallStep model clock outcome st' step
        stats := stats.count (stepKind st step)
        for b in bad do stats := stats.record b run
        stats := { stats with steps := stats.steps + 1 }
        model := model'
        st := st'
        match step with
        | .deliver => stats := { stats with delivers := stats.delivers + 1 }; break
        | .fail _ => stats := { stats with fails := stats.fails + 1 }; break
        | .follow _ => stats := { stats with follows := stats.follows + 1 }
        | .retry d _ =>
          stats := { stats with retries := stats.retries + 1 }
          now := now + d
  return stats

def randomChecks (n : Nat) (seed : UInt64) : Checks Unit := do
  let stats := randomRuns .none n seed
  IO.println s!"random runs: {stats.runs} calls, {stats.steps} steps: {stats.follows} follows, \
    {stats.retries} retries, {stats.delivers} delivers, {stats.fails} fails"
  for (k, n) in stats.kinds do
    IO.println s!"  {k}: {n}"
  for (p, k, r) in stats.violations do
    IO.println s!"  violation: {p} ({k} times, first in run {r})"
  check s!"{n} random calls (seed {seed}) break no rule" stats.violations.isEmpty
  let kinds := ["deliver", "follow", "follow to another origin", "follow with a method change",
    "retry after the backoff", "retry after Retry-After", "fail: tooManyRedirects", "fail: deadline",
    "fail: cause", "fail: delivered", "fail: responseReceived", "fail: hopLimit", "fail: budget",
    "fail: noTime"]
  let missing := kinds.filter fun k => !stats.kinds.any (·.1 == k)
  check "the random calls take every kind of step" missing.isEmpty s!"never: {missing}"
  for m in mutations do
    let stats := randomRuns m n seed
    let found := stats.violations.map fun (p, k, _) => s!"{p} ×{k}"
    check s!"planted bug {repr m} is caught" (!stats.violations.isEmpty)
    IO.println s!"  caught as: {found}"

def main (args : List String) : IO UInt32 := do
  let n := (args[0]?.bind String.toNat?).getD 20000
  let seed := ((args[1]?.bind String.toNat?).getD 1).toUInt64
  let ((), results) ← (do
    startChecks; redirectChecks; originChecks; hopChecks; retryChecks; statusChecks;
    retryAfterChecks; randomChecks n seed : Checks Unit).run #[]
  let failed := results.filter (!·.2)
  IO.println s!"{results.size} checks, {failed.size} failing"
  return if failed.isEmpty then 0 else 1
