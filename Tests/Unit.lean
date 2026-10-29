import LeanHttp
import Tests.Support.Drive

/-!
# Unit tests

Pure parts of the client: the backoff schedule, address ordering and de-duplication, request
planning, error classification, the pool's settings, when an exchange is sent again, the check of
a call's steps against the planner (with mutated traces as positive controls) and how the body
stream hands out what it holds.  Prints one line per check and exits with status 1 if any
failed.
-/

open Std.Http Std.Net LeanHttp

/-- The checks run so far: name and whether it passed. -/
abbrev Checks := StateT (Array (String × Bool)) IO

def check (name : String) (ok : Bool) (detail : String := "") : Checks Unit := do
  let suffix := if ok || detail.isEmpty then "" else s!": {detail}"
  IO.println s!"{if ok then "PASS" else "FAIL"} {name}{suffix}"
  modify (·.push (name, ok))

def checkEq {α : Type} [BEq α] [Repr α] (name : String) (got expected : α) : Checks Unit :=
  check name (got == expected) s!"expected {repr expected}, got {repr got}"

/-! ## Backoff -/

def backoffChecks : Checks Unit := do
  let base := 100
  let cap := 5000
  checkEq "ceiling doubles from the base" ((List.range 7).map (Backoff.ceiling base cap))
    [100, 200, 400, 800, 1600, 3200, 5000]
  checkEq "ceiling stays at the cap" (Backoff.ceiling base cap 1000) 5000
  checkEq "ceiling with a zero base" (Backoff.ceiling 0 cap 70) 0
  checkEq "a delay does not depend on the schedule's length"
    (Backoff.schedule base cap 7 2) ((Backoff.schedule base cap 7 5).take 2)
  -- SplitMix64's published first outputs for seed 0.
  checkEq "draw is SplitMix64" [Backoff.draw 0 0, Backoff.draw 0 1]
    [0xe220a8397b1dcdaf, 0x6e789e6aa1b965f4]
  -- Pinned values, which an independent Python implementation reproduces: a change here changes
  -- how recorded seeds replay.
  checkEq "pinned schedule for seed 42" (Backoff.schedule base cap 42 4) [23, 49, 111, 657]
  checkEq "pinned schedule for seed 0" (Backoff.schedule base cap 0 4) [67, 48, 223, 115]
  -- Every delay lies within [0, ceiling].
  let mut inRange := true
  for seed in [0:1000] do
    for attempt in [0:12] do
      if Backoff.delayMs base cap seed.toUInt64 attempt > Backoff.ceiling base cap attempt then
        inRange := false
  check "delays within [0, ceiling] for 1000 seeds and 12 attempts" inRange
  -- Full jitter: draws for one attempt spread over the whole range, with mean near half the
  -- ceiling.
  let draws := (List.range 10000).map fun s => Backoff.delayMs base cap s.toUInt64 0
  let mean := draws.foldl (· + ·) 0 / draws.length
  check "attempt 0 draws have mean near 50 ms" (45 ≤ mean && mean ≤ 55) s!"mean {mean}"
  check "attempt 0 draws reach 0 and 100 ms" (draws.contains 0 && draws.contains 100)
  let buckets := (List.range 10).map fun b => (draws.filter fun d => d / 10 == b).length
  check "attempt 0 draws fill every tenth of the range" (buckets.all (· > 800)) s!"{buckets}"
  -- Different seeds give different schedules, so that clients do not retry in lockstep.
  let schedules := (List.range 1000).map fun s => Backoff.schedule base cap s.toUInt64 3
  check "1000 seeds give at least 990 distinct schedules" (schedules.eraseDups.length ≥ 990)
    s!"{schedules.eraseDups.length} distinct"

/-! ## Addresses -/

def v4 (a b c d : UInt8) : IPAddr := .v4 (.ofParts a b c d)
def v6 (last : UInt16) : IPAddr := .v6 { segments := #v[0, 0, 0, 0, 0, 0, 0, last] }

instance : Repr IPAddr where
  reprPrec a _ := toString a

instance : Repr Target where
  reprPrec
    | .literal a, _ => s!"literal {a}"
    | .name h, _ => s!"name {h}"

def addressChecks : Checks Unit := do
  let a := v4 10 0 0 1
  let b := v4 10 0 0 2
  let c := v6 1
  let d := v6 2
  checkEq "dedup keeps the first occurrence, in order" (Address.dedup #[a, b, a, c, b]) #[a, b, c]
  checkEq "dedup of getaddrinfo's triplicates" (Address.dedup #[a, a, a, c, c, c]) #[a, c]
  checkEq "interleave starts with the first family" (Address.interleave #[c, d, a, b]) #[c, a, d, b]
  checkEq "interleave from IPv4 first" (Address.interleave #[a, c, d]) #[a, c, d]
  checkEq "interleave keeps a single family" (Address.interleave #[b, a]) #[b, a]
  checkEq "interleave of nothing" (Address.interleave #[]) #[]
  checkEq "connect order de-duplicates, then interleaves"
    (Address.connectOrder #[c, c, c, d, d, d, a, a, a]) #[c, a, d]
  checkEq "withPort for IPv6" (toString (Address.withPort c 8080)) "[::1]:8080"
  let host (url : String) : Option Target := (URI.parse? url).bind (·.host?) |>.map Target.ofHost
  checkEq "an IPv6 literal bypasses resolution" (host "http://[::1]:8080/x") (some (.literal c))
  checkEq "an IPv4 literal bypasses resolution" (host "http://10.0.0.2/") (some (.literal b))
  checkEq "a name is resolved" (host "http://Example.COM/") (some (.name "example.com"))

/-! ## Request planning -/

/-- The origin-form target `/`. -/
def rootTarget : RequestTarget := .originForm { segments := #[], absolute := true } none

def planOf (url : String) (headers : Headers := .empty) : Except String Client.Plan :=
  match URI.parse? url with
  | some uri => Client.plan { method := .get, version := .v11, uri := .absoluteForm uri, headers }
  | none => .error s!"test: cannot parse {url}"

def planText (url : String) (headers : Headers := .empty) : String :=
  match planOf url headers with
  | .ok p =>
    let hostField := (p.head.headers.get? Header.Name.host).map (·.value) |>.getD "-"
    s!"{p.host}:{p.port} {p.head.uri} Host={hostField}"
  | .error msg => s!"error: {msg}"

def planChecks : Checks Unit := do
  checkEq "plan for a name with a path and query" (planText "http://example.com/a/b?c=1")
    "example.com:80 /a/b?c=1 Host=example.com"
  checkEq "plan for an empty path" (planText "http://example.com") "example.com:80 / Host=example.com"
  checkEq "plan for an IPv6 literal and a port" (planText "http://[::1]:8080")
    "[::1]:8080 / Host=[::1]:8080"
  checkEq "plan drops the user information from Host" (planText "http://u:p@example.com:81/")
    "example.com:81 / Host=example.com:81"
  checkEq "plan keeps a Host the caller set"
    (planText "http://127.0.0.1:9/" (Headers.empty.insert Header.Name.host (.mk "api.test")))
    "127.0.0.1:9 / Host=api.test"
  check "plan refuses https" (planText "https://example.com/" |>.startsWith "error: unsupported scheme")
  let origin := Client.plan { method := .get, version := .v11, uri := rootTarget }
  check "plan refuses an origin-form target" (origin matches .error _)
  -- A zero read gap would make every write and read due the moment it is issued.
  check "a zero read gap is an invalid request"
    (Client.exchangeConfig { readGapMs := 0 } matches .error (.invalidRequest _))
  check "a read gap of 1 ms is accepted"
    (match Client.exchangeConfig { readGapMs := 1 } with | .ok c => c.gapMs == 1 | .error _ => false)
  -- A zero read size asks for reads that can return nothing.
  check "a zero read size is an invalid request"
    (Client.exchangeConfig { readChunkBytes := 0 } matches .error (.invalidRequest _))
  check "a read size of 1 byte is accepted"
    (match Client.exchangeConfig { readChunkBytes := 1 } with | .ok c => c.readChunk == 1 | .error _ => false)
  -- No call can meet a zero deadline; a zero connect timeout connects only within one turn of the
  -- event loop; a zero stagger starts every attempt at once.
  check "a zero deadline is an invalid request"
    (Client.checkConfig { deadlineMs := 0 } matches .error (.invalidRequest _))
  check "a zero connect timeout is an invalid request"
    (Client.checkConfig { connectTimeoutMs := 0 } matches .error (.invalidRequest _))
  check "a zero connect stagger is accepted" (Client.checkConfig { connectStaggerMs := 0 } matches .ok ())
  check "the default settings are accepted"
    (Client.checkConfig {} matches .ok () && Client.exchangeConfig {} matches .ok _)

/-! ## Error classification -/

instance : BEq Cause where
  beq a b := reprStr a == reprStr b

def errorChecks : Checks Unit := do
  let cases : List (Codec.Error × Cause) := [
    (.bodyTooLarge, .limit .body),
    (.tooManyHeaders, .limit .headers),
    (.headersTooLarge, .limit .headers),
    (.tooManyInterim, .limit .interim),
    (.closed, .peerClosed),
    (.badMessage, .protocol "Bad message"),
    (.unsupportedVersion, .protocol "Unsupported version"),
    (.switchingProtocols, .protocol "101 Switching Protocols, but no upgrade was requested"),
    (.unsupportedCoding,
      .protocol "a transfer coding other than chunked, which the client cannot decode")
  ]
  for (err, cause) in cases do
    checkEq s!"parser error {reprStr err} is {reprStr cause}" (Exchange.causeOf err) cause
  -- Delivery after the request was written: received once the final head is parsed.
  let head : Request.Head := {
    method := .get, version := .v11, uri := rootTarget,
    headers := Headers.empty.insert Header.Name.host (.mk "t") }
  let r := Run.written (prepare! { maxBody := 1024 } head .empty)
  checkEq "nothing received: maybe delivered" r.ex.delivery .maybeDelivered
  let r1 := r.feed "HTTP/1.1 200 OK\r\nContent-Le".toUTF8
  checkEq "half a head: maybe delivered" r1.ex.delivery .maybeDelivered
  let r2 := r.feed "HTTP/1.1 100 Continue\r\n\r\n".toUTF8
  checkEq "an interim response only: maybe delivered" r2.ex.delivery .maybeDelivered
  let r3 := r.feed "HTTP/1.1 200 OK\r\nContent-Length: 9\r\n\r\nabc".toUTF8
  checkEq "a final head: response received" r3.ex.delivery .responseReceived
  checkEq "and the body cut short is peerClosed" r3.endOfInput.failedCause? (some .peerClosed)
  let big := r.feed "HTTP/1.1 200 OK\r\nContent-Length: 2000\r\n\r\n".toUTF8
  checkEq "an announced body over the limit fails at once" big.failedCause? (some (.limit .body))
  checkEq "with the response received" big.ex.delivery .responseReceived
  let e : Error := { cause := .connect #[], delivery := .notSent, target := "h:1", seed := 7 }
  check "an error's text names the delivery and the seed"
    ((toString e).contains "not sent" && (toString e).contains "seed 7") (toString e)
  check "only connect failures count as connect"
    (!(Cause.peerClosed).isConnect && !(Cause.resolve "h" "x").isConnect
      && !(Cause.timeout .deadline).isConnect)

/-! ## Pooling: settings and re-dispatch -/

def poolChecks : Checks Unit := do
  let d : Config := {}
  checkEq "pooling is on by default" d.pool true
  checkEq "the exchange keeps the connection alive when pooling is on"
    ((Client.exchangeConfig d).toOption.map (·.keepAlive)) (some true)
  checkEq "and not when it is off"
    ((Client.exchangeConfig { d with pool := false }).toOption.map (·.keepAlive)) (some false)
  let pc := Client.poolConfig { d with maxIdlePerOrigin := 2, idleTimeoutMs := 77, maxActivePerOrigin := some 3 }
  checkEq "the pool's limits come from the configuration" (pc.maxIdle, pc.idleTimeoutMs, pc.maxActive)
    (2, 77, some 3)
  checkEq "the pool's default limits" (Client.poolConfig d).maxIdle 4
  check "a cap of zero active connections is refused"
    (Client.checkConfig { d with maxActivePerOrigin := some 0 } matches .error (.invalidRequest _))
  check "a cap of one is accepted" (Client.checkConfig { d with maxActivePerOrigin := some 1 } matches .ok ())
  let head (status : Status) : Response.Head := { status }
  let response (status : Status) (interim : Nat := 0) : Client.Ended :=
    .response (head status) interim
  let failure (cause : Cause) (delivery : Delivery) (received : Bool := false) : Client.Ended :=
    .failure { cause, delivery, written := 0 } received
  let r := fun (m : Method) (e : Client.Ended) => Client.redispatch? m e
  checkEq "a 408 before any other response is sent again, whatever the method"
    (r .post (response .requestTimeout)) (some .requestTimeout)
  checkEq "a 408 after an interim response is not" (r .get (response .requestTimeout 1)) none
  checkEq "any other response is not" (r .get (response .ok)) none
  checkEq "a 503 is not" (r .get (response .serviceUnavailable)) none
  checkEq "nothing sent: sent again, whatever the method" (r .post (failure .peerClosed .notSent))
    (some .notSent)
  checkEq "closed before any response byte: a GET is sent again"
    (r .get (failure .peerClosed .maybeDelivered)) (some .closedBeforeResponse)
  checkEq "so is a PUT" (r .put (failure .peerClosed .maybeDelivered)) (some .closedBeforeResponse)
  checkEq "a POST is not" (r .post (failure .peerClosed .maybeDelivered)) none
  checkEq "nor a PATCH" (r .patch (failure .peerClosed .maybeDelivered)) none
  checkEq "closed after part of a response: a GET is not"
    (r .get (failure .peerClosed .maybeDelivered (received := true))) none
  checkEq "closed after the response head: not" (r .get (failure .peerClosed .responseReceived)) none
  checkEq "a read timeout is not" (r .get (failure (.timeout .read) .maybeDelivered)) none
  checkEq "a deadline before anything was sent is not" (r .get (failure (.timeout .deadline) .notSent))
    none
  checkEq "an invalid response is not" (r .get (failure (.protocol "x") .maybeDelivered)) none

/-! ## Checking what the client did against the planner -/

/-- Whether `validate` rejects a trace. -/
def rejects (events : Array Call.Event) : Bool :=
  Call.validate events matches .error _

def traceChecks : Checks Unit := do
  let uriA := (URI.parse? "http://127.0.0.1:1/a").get!
  let headA : Request.Head := { method := .get, version := .v11, uri := .absoluteForm uriA }
  let policy : Call.Policy := {}
  let seed : UInt64 := 42
  let deadline := 10000
  let some st0 := (Call.start policy headA .none seed deadline).toOption
    | check "the planner starts a GET" false
  let redirect : Response.Head :=
    { status := .found, headers := Headers.empty.insert Header.Name.location (.mk "/b") }
  let ok : Response.Head := { status := .ok }
  let refused : Failure := { cause := .connect #[], delivery := .notSent, written := 0 }
  -- What the client writes for a hop's request: the origin and the encoded head.
  let send (hop : Call.Hop) (time : Nat) : Call.Event :=
    match Call.expectedWire hop 0 true with
    | .ok (target, wire) => .send hop.head target wire 0 time
    | .error _ => .send hop.head "" .empty 0 time
  -- A call that is refused once, retried, redirected, and answered.
  let c1 : Call.Clock := { now := 100, wallSec := 1700000000 }
  let (st1, s1) := Call.plan st0 c1 (.failure refused)
  let delay := match s1 with
    | .retry d _ => d
    | _ => 0
  check "the planner retries a refused connect" (s1 matches .retry _ .backoff)
  let c2 : Call.Clock := { now := 100 + delay + 5, wallSec := 1700000000 }
  let (st2, s2) := Call.plan st1 c2 (.response redirect)
  check "and follows the redirect" (s2 matches .follow _)
  let c3 : Call.Clock := { now := c2.now + 10, wallSec := 1700000000 }
  let (_, s3) := Call.plan st2 c3 (.response ok)
  check "and delivers the answer" (s3 matches .deliver)
  let good : Array Call.Event := #[
    .start policy headA .none 0 seed deadline true, send st0.current 10,
    .decide c1 (.failure refused) s1, .wait (100 + delay), send st1.current (100 + delay),
    .decide c2 (.response redirect) s2, send st2.current (c2.now + 1), .decide c3 (.response ok) s3,
    .deliver]
  checkEq "a faithful trace replays, three steps" (Call.validate good).toOption (some 3)
  check "the retry delay of seed 42 is positive, so sending early can be seen" (delay > 0)
  check "a retry sent before its delay is caught" (rejects (good.set! 4 (send st1.current (100 + delay - 1))))
  check "a wait shorter than the delay is caught" (rejects (good.set! 3 (.wait (100 + delay - 1))))
  check "a retry without its wait is caught" (rejects (good.eraseIdx! 3))
  check "the old request sent after a redirect is caught" (rejects (good.set! 6 (send st0.current (c2.now + 1))))
  check "a request sent with a body the hop does not carry is caught"
    (rejects (good.set! 6 (.send st2.current.head "127.0.0.1:1" .empty 7 (c2.now + 1))))
  let wrongWire := match good[6]! with
    | .send h t w n time => Call.Event.send h t (w.push 32) n time
    | e => e
  check "a head written differently from the request's is caught" (rejects (good.set! 6 wrongWire))
  let wrongTarget := match good[6]! with
    | .send h _ w n time => Call.Event.send h "127.0.0.1:2" w n time
    | e => e
  check "a connection to another origin is caught" (rejects (good.set! 6 wrongTarget))
  check "a step the planner did not take is caught" (rejects (good.set! 7 (.decide c3 (.response ok) s2)))
  check "a decision that misreports the outcome is caught"
    (rejects (good.set! 7 (.decide c3 (.failure refused) s3)))
  check "a decision before the request went out is caught"
    (rejects (good.set! 7 (.decide { c3 with now := c2.now } (.response ok) s3)))
  check "a trace that stops before the delivery is caught" (rejects good.pop)
  check "anything after the delivery is caught" (rejects (good.push .deliver))
  check "a trace without its start is caught" (rejects (good.extract 1 good.size))
  -- Re-dispatch: an exchange on a reused connection sent again on a fresh one.
  let closedFirst : Client.Ended :=
    .failure { cause := .peerClosed, delivery := .maybeDelivered, written := 30 } false
  let withRedispatch := (good.extract 0 7).push (.redispatch true closedFirst .closedBeforeResponse)
    |>.append (good.extract 7 good.size)
  checkEq "a re-dispatch redispatch? allows replays" (Call.validate withRedispatch).toOption (some 3)
  check "a re-dispatch of an exchange on a fresh connection is caught"
    (rejects ((good.extract 0 7).push (.redispatch false closedFirst .closedBeforeResponse)
      |>.append (good.extract 7 good.size)))
  let postHead : Request.Head := { headA with method := .post }
  let some sPost := (Call.start policy postHead .bytes seed deadline).toOption
    | check "the planner starts a POST" false
  let (_, sp) := Call.plan sPost c3 (.response ok)
  let postSend := match Call.expectedWire sPost.current 5 true with
    | .ok (target, wire) => Call.Event.send postHead target wire 5 10
    | .error _ => Call.Event.deliver
  let postTrace : Array Call.Event := #[
    .start policy postHead .bytes 5 seed deadline true, postSend,
    .redispatch true closedFirst .closedBeforeResponse, .decide c3 (.response ok) sp, .deliver]
  check "a POST sent again after it may have been delivered is caught" (rejects postTrace)
  check "two re-dispatches of one request are caught"
    (rejects ((withRedispatch.extract 0 8).push (.redispatch true closedFirst .closedBeforeResponse)
      |>.append (withRedispatch.extract 8 withRedispatch.size)))
  -- A call that fails: no retries allowed.
  let strict : Call.Policy := { maxRetriesPerHop := 0 }
  let some sStrict := (Call.start strict headA .none seed deadline).toOption
    | check "the planner starts a GET with no retries" false
  let (_, sf) := Call.plan sStrict c1 (.failure refused)
  let failed : Error := { cause := .connect #[], delivery := .notSent, notRetried := some .hopLimit }
  let failing : Array Call.Event := #[
    .start strict headA .none 0 seed deadline true, send sStrict.current 10,
    .decide c1 (.failure refused) sf, .fail failed]
  checkEq "a failed call replays" (Call.validate failing).toOption (some 1)
  check "an error that gives the wrong reason for not retrying is caught"
    (rejects (failing.set! 3 (.fail { failed with notRetried := some .budget })))
  check "an error with another cause is caught"
    (rejects (failing.set! 3 (.fail { failed with cause := .peerClosed })))
  check "an error with the wrong retry count is caught"
    (rejects (failing.set! 3 (.fail { failed with retries := 1 })))
  check "an error with the wrong hop count is caught"
    (rejects (failing.set! 3 (.fail { failed with hops := 1 })))
  check "a delivery instead of the failure is caught" (rejects (failing.set! 3 .deliver))
  -- A call whose first attempt was answered (a 503, retried) and whose retries then failed to
  -- connect: its error must not say not sent.
  let lenient : Call.Policy := { retry503 := true, maxRetriesPerHop := 1 }
  let some sL := (Call.start lenient headA .none seed deadline).toOption
    | check "the planner starts a GET that retries 503" false
  let busy : Response.Head := { status := .serviceUnavailable }
  let (sL1, l1) := Call.plan sL c1 (.response busy)
  let delay503 := match l1 with
    | .retry d _ => d
    | _ => 0
  check "the planner retries the 503" (l1 matches .retry _ .backoff)
  let cL : Call.Clock := { now := 100 + delay503 + 5, wallSec := 1700000000 }
  let (_, l2) := Call.plan sL1 cL (.failure refused)
  check "and fails the refused retry" (l2 matches .fail (.failure _ .hopLimit))
  let answered : Error := {
    cause := .connect #[], delivery := .responseReceived, retries := 1, notRetried := some .hopLimit }
  let answeredTrace : Array Call.Event := #[
    .start lenient headA .none 0 seed deadline true, send sL.current 10, .decide c1 (.response busy) l1,
    .wait (100 + delay503), send sL1.current (100 + delay503), .decide cL (.failure refused) l2,
    .fail answered]
  checkEq "a call answered once, then refused, replays" (Call.validate answeredTrace).toOption (some 2)
  check "its error saying not sent is caught"
    (rejects (answeredTrace.set! 6 (.fail { answered with delivery := .notSent })))
  -- After a re-dispatch of a request that may have reached the server, the error must not say
  -- not sent.
  let failingAfter := (failing.extract 0 2).push (.redispatch true closedFirst .closedBeforeResponse)
    |>.append (failing.extract 2 failing.size)
  check "a failure reported as not sent after a re-dispatch is caught" (rejects failingAfter)
  -- The client may fail a call when it cannot send the planner's next request (https).
  let httpsRedirect : Response.Head := {
    status := .found,
    headers := Headers.empty.insert Header.Name.location (.mk "https://127.0.0.1:1/b") }
  let (stH, sH) := Call.plan st1 c2 (.response httpsRedirect)
  let refusedHop : Error := {
    cause := .invalidRequest "https", delivery := .responseReceived, hops := stH.hops,
    retries := stH.retries }
  let httpsTrace := (good.extract 0 5).push (.decide c2 (.response httpsRedirect) sH)
  check "after a redirect to https, the client may refuse to send it"
    ((Call.validate (httpsTrace.push (.fail refusedHop))).toOption.isSome)
  check "but not with another cause"
    (rejects (httpsTrace.push (.fail { refusedHop with cause := .peerClosed })))
  check "nor with a delivery short of the response received"
    (rejects (httpsTrace.push (.fail { refusedHop with delivery := .notSent })))
  check "and an http redirect may not be refused"
    (rejects ((good.extract 0 6).push (.fail { refusedHop with hops := 1 })))

/-! ## The body stream's pieces -/

def streamChecks : Checks Unit := do
  let piece := ByteArray.mk #[1, 2, 3, 4, 5]
  let other := ByteArray.mk #[6, 7]
  let view (r : Option (ByteArray × List ByteArray × Nat)) : Option (List UInt8 × Nat × Nat) :=
    r.map fun (b, rest, off) => (b.toList, rest.length, off)
  checkEq "nothing pending, nothing taken" (view (BodyStream.take [] 0 4)) none
  checkEq "a piece that fits is taken whole" (view (BodyStream.take [piece, other] 0 8)) (some ([1, 2, 3, 4, 5], 1, 0))
  checkEq "a larger piece is split at the limit" (view (BodyStream.take [piece, other] 0 2)) (some ([1, 2], 2, 2))
  checkEq "and continued from the offset" (view (BodyStream.take [piece, other] 2 2)) (some ([3, 4], 2, 4))
  checkEq "to its end" (view (BodyStream.take [piece, other] 4 2)) (some ([5], 1, 0))

def main : IO UInt32 := do
  let ((), results) ←
    (do backoffChecks; addressChecks; planChecks; errorChecks; poolChecks; traceChecks; streamChecks
      : Checks Unit).run #[]
  let failed := results.filter (!·.2)
  IO.println s!"{results.size} checks, {failed.size} failing"
  return if failed.isEmpty then 0 else 1
