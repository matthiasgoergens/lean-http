import LeanHttp
import Tests.Support.Drive

/-!
# Unit tests

Pure parts of the client: the backoff schedule, address ordering and de-duplication, request
planning, error classification, the pool's settings, when an exchange is sent again, the check of
a call's steps against the planner (with mutated traces as positive controls), how the body
stream hands out what it holds, TLS: the choice of trust store, the name a certificate must
carry and what the planner retries, a call's cancellation, and that a wait never times out early,
whatever its timer does.  Prints one line per check and exits with status 1 if any
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
  checkEq "plan for https" (planText "https://example.com/x") "example.com:443 /x Host=example.com"
  checkEq "an https plan says TLS" ((planOf "https://example.com/").toOption.map (·.scheme)) (some .https)
  checkEq "an http plan says plain" ((planOf "http://example.com/").toOption.map (·.scheme)) (some .http)
  -- The pool's origin key: a TLS and a plain connection to the same host and port never mix.
  checkEq "an https origin key" ((planOf "https://example.com:8443/").toOption.map (·.target))
    (some "https://example.com:8443")
  checkEq "an http origin key" ((planOf "http://example.com:8443/").toOption.map (·.target))
    (some "http://example.com:8443")
  check "plan refuses another scheme" (planText "ftp://example.com/" |>.startsWith "error: unsupported scheme")
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
  let r := fun (m : Method) (e : Client.Ended) => Client.redispatch? m true e
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
  -- A body that cannot be sent again (a stream) is sent again only if nothing was written.
  let u := fun (m : Method) (e : Client.Ended) => Client.redispatch? m false e
  checkEq "a stream with nothing sent is sent again" (u .post (failure .peerClosed .notSent))
    (some .notSent)
  checkEq "a stream answered with a 408 is not" (u .put (response .requestTimeout)) none
  checkEq "a stream closed before any response byte is not, even for a PUT"
    (u .put (failure .peerClosed .maybeDelivered)) none

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
    match Call.expectedWire hop (.length 0) true with
    | .ok (target, wire) => .send hop.head target wire (.length 0) time
    | .error _ => .send hop.head "" .empty (.length 0) time
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
    .start policy headA .none (.length 0) seed deadline true, send st0.current 10,
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
    (rejects (good.set! 6 (.send st2.current.head "127.0.0.1:1" .empty (.length 7) (c2.now + 1))))
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
  -- A call cancelled while it waits to retry: in place of the retry, the planner hears of a
  -- failure whose cause is the cancellation, with nothing sent, and fails the call.
  let cancelled : Failure := {
    cause := .cancelled .cancel, delivery := .notSent, written := 0,
    detail := "cancelled while waiting to retry" }
  let cC : Call.Clock := { now := 100 + delay / 2, wallSec := 1700000000 }
  let (_, sc) := Call.plan st1 cC (.failure cancelled)
  check "the planner fails a cancelled call" (sc matches .fail (.failure _ .cause))
  let cancelError : Error := {
    cause := .cancelled .cancel, delivery := .notSent, retries := 1, notRetried := some .cause }
  let cancelTrace : Array Call.Event :=
    (good.extract 0 4).push (.decide cC (.failure cancelled) sc) |>.push (.fail cancelError)
  checkEq "a call cancelled while it waits to retry replays, two steps"
    (Call.validate cancelTrace).toOption (some 2)
  check "a cancellation in place of a request that says maybe delivered is caught"
    (rejects (cancelTrace.set! 4 (.decide cC (.failure { cancelled with delivery := .maybeDelivered })
      (Call.plan st1 cC (.failure { cancelled with delivery := .maybeDelivered })).2)))
  check "a cancellation in place of a request that counts bytes written is caught"
    (rejects (cancelTrace.set! 4 (.decide cC (.failure { cancelled with written := 3 })
      (Call.plan st1 cC (.failure { cancelled with written := 3 })).2)))
  -- A failure the planner never retries, with the error it calls for: only the rule that a request
  -- may give way to a cancellation alone rejects it.
  let unresolved : Failure := { cause := .resolve "a.test" "x", delivery := .notSent, written := 0 }
  let unresolvedStep := (Call.plan st1 cC (.failure unresolved)).2
  let unresolvedError : Error := {
    cause := .resolve "a.test" "x", delivery := .notSent, retries := 1, notRetried := some .cause }
  check "a failure other than a cancellation in place of a request is caught"
    (rejects ((good.extract 0 4).push (.decide cC (.failure unresolved) unresolvedStep)
      |>.push (.fail unresolvedError)))
  check "a cancelled call's error with another cause is caught"
    (rejects (cancelTrace.set! 5 (.fail { cancelError with cause := .timeout .deadline })))
  check "a cancelled call's error that says it was retried for the cancellation is caught"
    (rejects (cancelTrace.set! 5 (.fail { cancelError with notRetried := some .noTime })))
  -- A call cancelled before its first request went out.
  let c0 : Call.Clock := { now := 5, wallSec := 1700000000 }
  let (_, s0) := Call.plan st0 c0 (.failure cancelled)
  let cancelFirst : Array Call.Event := #[
    .start policy headA .none (.length 0) seed deadline true, .decide c0 (.failure cancelled) s0,
    .fail { cancelError with retries := 0 }]
  checkEq "a call cancelled before its first request replays, one step"
    (Call.validate cancelFirst).toOption (some 1)
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
  let postSend := match Call.expectedWire sPost.current (.length 5) true with
    | .ok (target, wire) => Call.Event.send postHead target wire (.length 5) 10
    | .error _ => Call.Event.deliver
  let postTrace : Array Call.Event := #[
    .start policy postHead (.bytes) (.length 5) seed deadline true, postSend,
    .redispatch true closedFirst .closedBeforeResponse, .decide c3 (.response ok) sp, .deliver]
  check "a POST sent again after it may have been delivered is caught" (rejects postTrace)
  -- A streamed PUT: sent chunked, and never sent again once anything may have been written.
  let putHead : Request.Head := { headA with method := .put }
  let some sPut := (Call.start policy putHead .stream seed deadline).toOption
    | check "the planner starts a streamed PUT" false
  let (_, sq) := Call.plan sPut c3 (.response ok)
  let putSend := match Call.expectedWire sPut.current .chunked true with
    | .ok (target, wire) => Call.Event.send putHead target wire .chunked 10
    | .error _ => Call.Event.deliver
  let putTrace : Array Call.Event := #[
    .start policy putHead .stream .chunked seed deadline true, putSend, .decide c3 (.response ok) sq,
    .deliver]
  checkEq "a streamed PUT, sent chunked, replays" (Call.validate putTrace).toOption (some 1)
  check "the chunked head carries Transfer-Encoding: chunked and no Content-Length"
    (match putSend with
     | .send _ _ wire _ _ =>
       let text := ((String.fromUTF8? wire).getD "").toLower
       (text.splitOn "transfer-encoding: chunked\r\n").length == 2 &&
         (text.splitOn "content-length").length == 1
     | _ => false)
  check "a streamed PUT sent with a Content-Length it did not declare is caught"
    (rejects (putTrace.set! 1 (match Call.expectedWire sPut.current (.length 5) true with
      | .ok (target, wire) => Call.Event.send putHead target wire (.length 5) 10
      | .error _ => Call.Event.deliver)))
  check "a streamed PUT sent again after it may have been delivered is caught"
    (rejects (#[putTrace[0]!, putSend, .redispatch true closedFirst .closedBeforeResponse] ++
      putTrace.extract 2 putTrace.size))
  let notSentFirst : Client.Ended :=
    .failure { cause := .peerClosed, delivery := .notSent, written := 0 } false
  checkEq "a streamed PUT sent again when nothing of it was written replays"
    (Call.validate (#[putTrace[0]!, putSend, .redispatch true notSentFirst .notSent] ++
      putTrace.extract 2 putTrace.size)).toOption (some 1)
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
    .start strict headA .none (.length 0) seed deadline true, send sStrict.current 10,
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
    .start lenient headA .none (.length 0) seed deadline true, send sL.current 10, .decide c1 (.response busy) l1,
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
  -- The client reaches https now: refusing the planner's redirect to https is caught.
  let httpsRedirect : Response.Head := {
    status := .found,
    headers := Headers.empty.insert Header.Name.location (.mk "https://127.0.0.1:1/b") }
  let (stH, sH) := Call.plan st1 c2 (.response httpsRedirect)
  let refusedHop : Error := {
    cause := .invalidRequest "https", delivery := .responseReceived, hops := stH.hops,
    retries := stH.retries }
  let httpsTrace := (good.extract 0 5).push (.decide c2 (.response httpsRedirect) sH)
  check "after a redirect to https, the client may not refuse to send it"
    (rejects (httpsTrace.push (.fail refusedHop)))
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

/-! ## Streamed request bodies -/

def uploadChecks : Checks Unit := do
  let head : Request.Head := {
    method := .put, version := .v11, uri := .originForm { segments := #[], absolute := true } none,
    headers := Headers.empty.insert Header.Name.host (.mk "example.test") }
  let text (p : PreparedRequest) : String := ((String.fromUTF8? p.bytes).getD "").toLower
  let known := Exchange.prepareStream { keepAlive := true } head (some 5)
  check "a stream of known size is sent with its Content-Length"
    (((text known).splitOn "content-length: 5\r\n").length == 2)
  check "and without Transfer-Encoding" (((text known).splitOn "transfer-encoding").length == 1)
  checkEq "its prepared bytes are the head alone" (known.bytes.size, known.framing)
    (known.headBytes, some (.length 5))
  let unknown := Exchange.prepareStream { keepAlive := true } head none
  check "a stream of unknown size is sent chunked"
    (((text unknown).splitOn "transfer-encoding: chunked\r\n").length == 2)
  check "and without Content-Length" (((text unknown).splitOn "content-length").length == 1)
  let framingFields := head.headers.insert Header.Name.contentLength (.mk "99")
    |>.insert Header.Name.transferEncoding (.mk "gzip")
  let withFraming := { head with headers := framingFields }
  let replaced := Exchange.prepareStream { keepAlive := true } withFraming none
  check "the request's own framing fields are replaced"
    (((text replaced).splitOn "content-length").length == 1 &&
      ((text replaced).splitOn "transfer-encoding").length == 2 &&
      ((text replaced).splitOn "gzip").length == 1)
  checkEq "the chunk framing is the size in hex, CRLF, the data, CRLF"
    (String.fromUTF8? (Codec.chunkFrame (ByteArray.mk (Array.replicate 26 97))))
    (some ("1a\r\n" ++ String.ofList (List.replicate 26 'a') ++ "\r\n"))
  checkEq "the last chunk" (String.fromUTF8? Codec.lastChunk) (some "0\r\n\r\n")
  let next : Std.Async.Async (Option ByteArray) := pure none
  checkEq "a stream's kind is a stream" (RequestBody.stream none next).kind .stream
  checkEq "an empty byte array is no body" (RequestBody.bytes .empty).kind .none
  checkEq "bytes are bytes" (RequestBody.bytes (ByteArray.mk #[1])).kind .bytes
  -- A stream of unknown size needs HTTP/1.1: the client refuses it otherwise, without sending.
  let client ← Client.new
  let uri := (URI.parse? "http://127.0.0.1:1/x").get!
  let req : Request RequestBody :=
    { line := { method := .put, version := .v10, uri := .absoluteForm uri }, body := .stream none next }
  let result ← (client.upload req).block
  check "a chunked stream in HTTP/1.0 is refused, not sent"
    (match result with
     | .error e => e.delivery == .notSent && (e.cause matches .invalidRequest _)
     | .ok _ => false)

/-! ## TLS: the trust store, the server's name, errors -/

def hostOf (url : String) : Option URI.Host :=
  URI.parse? url >>= (·.host?)

def nameText (url : String) : String :=
  match hostOf url with
  | none => "test: no host"
  | some h => match Tls.serverName h with
    | .ok (.host n) => s!"host {n}"
    | .ok (.ip a) => s!"ip {a}"
    | .error msg => s!"error: {msg}"

def trustText (p : Tls.TrustProbe) : String :=
  match Tls.chooseTrust p with
  | .ok t => s!"file={t.file} dirs={t.dirs.toList}"
  | .error msg => s!"error: {msg}"

def tlsChecks : Checks Unit := do
  -- The OpenSSL linked in: the toolchain's static OpenSSL 3.
  let v ← Tls.opensslVersionNumber ()
  check "the OpenSSL linked in is version 3" (v >>> 28 == 3) s!"version number {v}"
  -- Which certificates to trust.
  let ubuntu : Tls.TrustProbe := {
    isFile := (· == "/etc/ssl/certs/ca-certificates.crt"), isDir := (· == "/etc/ssl/certs"),
    hasHashed := (· == "/etc/ssl/certs") }
  checkEq "the caFile setting wins" (trustText { ubuntu with caFile := some "/my/ca.pem", envFile := some "/x" })
    "file=/my/ca.pem dirs=[]"
  checkEq "SSL_CERT_FILE is honoured"
    (trustText { ubuntu with envFile := some "/e.pem", isFile := fun f => f == "/e.pem" || ubuntu.isFile f })
    "file=/e.pem dirs=[]"
  checkEq "SSL_CERT_DIR is a list of directories"
    (trustText { ubuntu with envDir := some "/a::/b", isDir := fun d => d == "/a" || d == "/b" })
    "file= dirs=[/a, /b]"
  let both : Tls.TrustProbe :=
    { ubuntu with envFile := some "/e.pem", envDir := some "/a", isFile := (· == "/e.pem"), isDir := (· == "/a") }
  checkEq "both variables together" (trustText both) "file=/e.pem dirs=[/a]"
  check "an SSL_CERT_FILE that names nothing is an error, not a reason to look elsewhere"
    (trustText { ubuntu with envFile := some "/missing.pem" } |>.startsWith "error: SSL_CERT_FILE names /missing.pem")
  check "likewise SSL_CERT_DIR"
    (trustText { ubuntu with envDir := some "/missing" } |>.startsWith "error: SSL_CERT_DIR names /missing")
  check "an SSL_CERT_DIR of separators only is an error"
    (trustText { ubuntu with envDir := some "::" } |>.startsWith "error: SSL_CERT_DIR is")
  checkEq "empty variables count as unset" (trustText { ubuntu with envFile := some "", envDir := some "" })
    "file=/etc/ssl/certs/ca-certificates.crt dirs=[]"
  checkEq "Debian and Ubuntu's bundle" (trustText ubuntu) "file=/etc/ssl/certs/ca-certificates.crt dirs=[]"
  checkEq "Fedora's bundle" (trustText { isFile := (· == "/etc/pki/tls/certs/ca-bundle.crt") })
    "file=/etc/pki/tls/certs/ca-bundle.crt dirs=[]"
  checkEq "Alpine's and macOS's bundle" (trustText { isFile := (· == "/etc/ssl/cert.pem") })
    "file=/etc/ssl/cert.pem dirs=[]"
  checkEq "a bundle file before a directory"
    (trustText { ubuntu with isFile := (· == "/etc/ssl/cert.pem") }) "file=/etc/ssl/cert.pem dirs=[]"
  checkEq "a directory with hashed names when no bundle exists"
    (trustText { ubuntu with isFile := fun _ => false }) "file= dirs=[/etc/ssl/certs]"
  check "a directory without hashed names is not a trust store"
    (trustText { ubuntu with isFile := fun _ => false, hasHashed := fun _ => false } |>.startsWith "error: no trusted certificates found")
  check "nothing at all is an error that says what to set"
    ((trustText {}).startsWith "error: no trusted certificates found" &&
      ((trustText {}).splitOn "Config.tls.caFile").length == 2)
  check "never OpenSSL's compiled-in default (a Nix store path)"
    (!(Tls.wellKnownFiles ++ Tls.wellKnownDirs).any (·.startsWith "/nix"))
  checkEq "hashed names" (["5ad8a5d6.0", "5ad8a5d6.12", "5AD8A5D6.0", "5ad8a5d.0", "5ad8a5d6",
      "5ad8a5d6.r0", "ca.pem"].map Tls.isHashedName) [true, true, false, false, false, false, false]
  -- The name the certificate must carry.
  checkEq "a host name" (nameText "https://example.com/") "host example.com"
  checkEq "a host name is lowercase" (nameText "https://API.Example.COM/") "host api.example.com"
  checkEq "an IPv4 literal" (nameText "https://127.0.0.1:8443/") "ip 127.0.0.1"
  checkEq "an IPv6 literal, without brackets" (nameText "https://[::1]:8443/") "ip ::1"
  check "a name of digits and dots is refused" (nameText "https://1.2.3/" |>.startsWith "error:")
  check "a hexadecimal IPv4 address is refused" (nameText "https://0x7f000001/" |>.startsWith "error:")
  check "a name whose last label is hexadecimal is refused" (nameText "https://a.0x1f/" |>.startsWith "error:")
    (nameText "https://a.0x1f/")
  check "127.0.0.0x1 is refused, by the URI parser or as a name"
    ((nameText "https://127.0.0.0x1/").startsWith "error:" || (hostOf "https://127.0.0.0x1/").isNone)
    (nameText "https://127.0.0.0x1/")
  checkEq "a name with a digit in its last label is a name" (nameText "https://a.b2c/") "host a.b2c"
  checkEq "a name with digits before its last label is a name" (nameText "https://1.2.example/") "host 1.2.example"
  -- The URI parser already refuses the names `SSL_set1_host` must never see.
  checkEq "the URI parser refuses a trailing dot" (hostOf "https://example.com./").isNone true
  checkEq "and an empty label" (hostOf "https://a..b/").isNone true
  -- Errors and what the planner retries.
  checkEq "a refused certificate says why"
    (Cause.describe (.tls (.verify "certificate has expired"))) "TLS certificate verification failed: certificate has expired"
  check "a handshake cut short by the connection closing is retried"
    (Call.retryableCause (.tls (.closed "reset")))
  check "a handshake timeout is retried" (Call.retryableCause (.tls .timeout))
  check "a refused certificate is not retried" (!Call.retryableCause (.tls (.verify "expired")))
  check "a failed handshake is not retried" (!Call.retryableCause (.tls (.handshake "protocol version")))
  check "a TLS setup failure is not retried" (!Call.retryableCause (.tls (.setup "no trust store")))
  check "a zero TLS handshake timeout is an invalid request"
    (Client.checkConfig { tlsHandshakeTimeoutMs := 0 } matches .error (.invalidRequest _))

/-! ## A call's cancellation -/

def cancelChecks : Checks Unit := do
  -- A token cancelled before the watch starts is seen at once, and fires the call.
  let early ← Std.CancellationToken.new
  early.cancel .shutdown
  let c ← Cancel.watch #[early] #[early]
  check "a token cancelled before the watch is seen at once" (reprStr (← c.reason?) == reprStr (some Std.CancellationReason.shutdown))
  let ran ← IO.mkRef false
  c.onCancel (ran.set true)
  check "and a hook registered afterwards runs at once" (← ran.get)
  c.finish
  -- A token cancelled during the call: the check asks the token, so it holds as cancel returns.
  let token ← Std.CancellationToken.new
  let c ← Cancel.watch #[token] #[token]
  check "an uncancelled call has no reason" (← c.reason?).isNone
  token.cancel .cancel
  check "a check right after cancel sees it" (← c.reason?).isSome
  let hooked ← IO.mkRef false
  c.onCancel (hooked.set true)
  check "a hook registered after the cancellation runs at once" (← hooked.get)
  let waited ← (c.race (#[] : Array (Task Unit)) 10000).block
  check "a wait after the cancellation ends at once" (waited matches .cancelled _)
  c.finish
  -- A wait that the timer ends: its bell, the last of the call, is released when the call ends
  -- (what is chained on it then runs, with nothing), so an uncancelled call keeps nothing alive.
  let quiet ← Std.CancellationToken.new
  let c ← Cancel.watch #[quiet] #[quiet]
  let waited ← (c.race (#[] : Array (Task Unit)) 1).block
  check "a wait with nothing to wait for ends at its time" (waited matches .timedOut)
  let lastBell := ((← c.bell.get).map (·.result?)).getD (Task.pure none)
  check "the last wait's bell is unresolved while the call goes on" !(← IO.hasFinished lastBell)
  c.finish
  IO.sleep 50
  check "the last wait's bell is released when the call ends" (← IO.hasFinished lastBell)
  quiet.cancel .cancel
  check "a token cancelled after the call ended does not cancel it" (← c.reason?).isNone
  -- A token shared by many calls keeps nothing of the calls that have ended.
  let shared ← Std.CancellationToken.new
  let entries : BaseIO Nat := shared.state.atomically (m := BaseIO) do
    return (← get).consumers.toArray.size
  let calls ← (List.range 5).mapM fun _ => Cancel.watch #[shared] #[shared]
  check "each call in flight is registered with its token" ((← entries) == 5)
  for c in calls do c.finish
  check "and a call that has ended is not" ((← entries) == 0)
  -- A token cancelled while a wait is in progress ends it.
  let later ← Std.CancellationToken.new
  let c ← Cancel.watch #[later] #[later]
  let fired ← IO.mkRef false
  c.onCancel (fired.set true)
  let wait ← start (c.race (#[] : Array (Task Unit)) 10000)
  IO.sleep 20
  later.cancel .deadline
  check "a hook registered before runs as the token is cancelled" (← fired.get)
  let t0 ← IO.monoMsNow
  let waited ← IO.wait wait
  check "a wait in progress ends at the cancellation, with the token's reason"
    ((waited matches .ok (.cancelled .deadline)) && (← IO.monoMsNow) - t0 < 2000)
  c.finish

/-! ## Waits that a timer ends -/

/--
A timer that fires at half the time it is asked for, as a timer of the event loop does when the loop's
clock is behind (`NOTES.md`, "Timers fire early").
-/
def earlyTimer : StartTimer := fun ms => libuvTimer (ms / 2)

/--
Waits through `awaitFirst` and `Cancel.race` with `earlyTimer`, all at once: a wait with nothing to
wait for must still end at its time, and a task that finishes, or a cancellation that comes, after
the timer first fired early must still win.  The times leave seconds of margin for a loaded host: the
first early firing comes at 3 s of 6, and the task and the cancellation at 3.5 s.
-/
def timerChecks : Checks Unit := do
  let t0 ← IO.monoMsNow
  -- The control: the timer of these checks fires early.
  let (fired, _) ← (earlyTimer 6000).block
  let ctl ← BaseIO.mapTask (sync := true) (fun _ => IO.monoMsNow) fired
  let lone ← start do
    let r ← awaitFirst (#[] : Array (Task Unit)) 6000 earlyTimer
    return (r, (← IO.monoMsNow) - t0)
  let c ← Cancel.watch #[] #[]
  let loneRace ← start do
    let r ← c.race (#[] : Array (Task Unit)) 6000 earlyTimer
    return (r, (← IO.monoMsNow) - t0)
  let p : IO.Promise Nat ← IO.Promise.new
  let c2 ← Cancel.watch #[] #[]
  let withTask ← start (awaitFirst #[p.result!] 6000 earlyTimer)
  let raceTask ← start (c2.race #[p.result!] 6000 earlyTimer)
  let token ← Std.CancellationToken.new
  let c3 ← Cancel.watch #[token] #[token]
  let raceCancel ← start (c3.race (#[] : Array (Task Unit)) 6000 earlyTimer)
  IO.sleep 3500
  p.resolve 7
  token.cancel .cancel
  let ms := (← IO.wait ctl) - t0
  check "control: the early timer fires at half its time" (ms < 5000) s!"after {ms} ms"
  let (r, ms) ← IO.ofExcept (← IO.wait lone)
  check "awaitFirst times out no earlier than its time, whatever the timer" (r.isNone && ms ≥ 6000)
    s!"after {ms} ms"
  let (r, ms) ← IO.ofExcept (← IO.wait loneRace)
  check "Cancel.race times out no earlier than its time, whatever the timer"
    ((r matches .timedOut) && ms ≥ 6000) s!"after {ms} ms"
  check "a task that finishes after an early timer fired still wins awaitFirst"
    ((← IO.wait withTask) matches .ok (some 7))
  check "and Cancel.race" ((← IO.wait raceTask) matches .ok (.done 7))
  check "and so does a cancellation" ((← IO.wait raceCancel) matches .ok (.cancelled .cancel))
  c.finish; c2.finish; c3.finish

/-- Every check, in order. -/
def allChecks : Checks Unit := do
  backoffChecks; addressChecks; planChecks; errorChecks; poolChecks; traceChecks; streamChecks
  uploadChecks; tlsChecks; cancelChecks; timerChecks

def main : IO UInt32 := do
  let ((), results) ← allChecks.run #[]
  let failed := results.filter (!·.2)
  IO.println s!"{results.size} checks, {failed.size} failing"
  return if failed.isEmpty then 0 else 1
