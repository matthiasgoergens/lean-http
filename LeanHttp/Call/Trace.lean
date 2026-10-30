module

public import LeanHttp.Call
public import LeanHttp.Wire

public section

/-!
# What the client did in a call, and checking it against the planner

The client's loop around the exchanges is meant to be a thin driver of the per-call planner: it
sends the current request, reports how the exchange ended to `Call.plan` with the time, and does
what the step says.  The theorems about the planner (`LeanHttp.Call.Proofs`) hold for the requests
the client sends only if it does exactly that, which no theorem covers.

So the client can report every call as a list of `Event`s (`Config.observe`), and `validate` replays
them through a planner of its own, started from the recorded start and fed the recorded outcomes at
the recorded times.  It checks:

- that every step the client took is the planner's;
- that every request the client wrote is the planner's current request: the origin it connected to
  and the head it encoded are what `Client.plan` and the request serialiser make of `State.current`,
  with the body the hop carries;
- that every exchange sent a second time on a fresh connection was one `Client.redispatch?` allows,
  on a connection from the pool, at most once per request, and that a failure after a re-dispatch
  that may have reached the server is not reported as not sent;
- that a retry waited until the time the planner's delay ends (or the deadline), and went out no
  earlier;
- that the call ended as the last step said, with an error whose cause and reason are the planner's,
  whose hop and retry counts are the planner's, and whose delivery is at least the furthest any
  recorded exchange got.  The record of a delivered call ends at the delivery: an error while the
  caller reads the body comes after the planner's last step, and is not in it.

The record is the client's own account: a client that wrote one thing and recorded another would
pass.  What the check rules out is a loop that decides anything itself.
-/

namespace LeanHttp.Call

set_option linter.all true

open Std.Http

/--
One thing the client did in a call, in order.
-/
inductive Event where
  /--
  The call started: the planner's inputs, how the call's body is framed (its size, or chunked for a
  stream of unknown size), and whether requests ask for the connection to be kept alive.
  -/
  | start (policy : Policy) (head : Request.Head) (kind : BodyKind) (body : Codec.RequestFraming)
      (seed : UInt64) (deadline : Timestamp) (keepAlive : Bool)

  /--
  The request of a hop went out (the client began taking a connection for it) at monotonic time
  `time`: the planner's head `head` (its target absolute), the origin the client connects to
  (`host:port`), the head it encoded (`wire`) and how the body after it is framed.
  -/
  | send (head : Request.Head) (target : String) (wire : ByteArray) (body : Codec.RequestFraming)
      (time : Timestamp)

  /--
  The exchange began on a connection from the pool (`reused`) as `first`, and was sent again on a
  fresh connection, for `reason`.
  -/
  | redispatch (reused : Bool) (first : Client.Ended) (reason : Client.Redispatch)

  /--
  The client asked the planner what follows an exchange that ended with `outcome`, at `clock`, and
  the planner answered `step`.
  -/
  | decide (clock : Clock) (outcome : Outcome) (step : Step)

  /--
  The client waited, before a retry, until monotonic time `endsAt`.
  -/
  | wait (endsAt : Timestamp)

  /--
  The response was delivered to the caller.
  -/
  | deliver

  /--
  The call failed with `error`.
  -/
  | fail (error : Error)

instance : Inhabited Event := ⟨.deliver⟩

/--
How a body framed by `framing` is described in messages: its size, or `chunked`.
-/
def framingText : Codec.RequestFraming → String
  | .length size => toString size
  | .chunked => "chunked"

/--
A one-line description of an event, for messages.
-/
def Event.describe : Event → String
  | .start _ head _ body _ deadline _ =>
    s!"start {head.method} {head.uri} body={framingText body} deadline={deadline}"
  | .send head target _ body time =>
    s!"send {head.method} {head.uri} to {target} body={framingText body} at={time}"
  | .redispatch reused _ reason => s!"redispatch reused={reused} {reprStr reason}"
  | .decide clock outcome step =>
    let o := match outcome with
      | .response head => s!"response {head.status.toCode}"
      | .failure f => s!"failure {reprStr f.cause} {f.delivery.name}"
    s!"decide at={clock.now} {o} -> {reprStr step}"
  | .wait endsAt => s!"wait until={endsAt}"
  | .deliver => "deliver"
  | .fail e => s!"fail {reprStr e.cause}"

/--
What `validate` expects next.
-/
private inductive Expect where
  /-- A `send` of the state's current request, no earlier than `notBefore`; after a redirect the
  client may instead fail, if it cannot reach the next request's target (`refusable`). -/
  | send (notBefore : Timestamp) (refusable : Bool)
  /-- A `decide`, or a `redispatch` unless the request was already sent again. -/
  | decide (redispatched : Option Client.Redispatch)
  /-- A `wait` until this time. -/
  | wait (endsAt : Timestamp)
  /-- A `deliver`, and nothing after it. -/
  | deliver
  /-- A `fail` with an error that matches `reason`, and nothing after it. -/
  | fail (reason : FailReason)
  /-- Nothing more. -/
  | done

/--
Whether the cause of a call's error is the cause of the exchange that failed it.  A connect failure
is the exception: the error lists the failed attempts of every round of the call, which end with
those of the last round.
-/
def causeMatches (error failure : Cause) : Bool :=
  match error, failure with
  | .connect all, .connect last =>
    reprStr (all.extract (all.size - last.size) all.size) == reprStr last
  | _, _ => reprStr error == reprStr failure

/--
Whether a call's error reports the planner's reason for failing it.
-/
def errorMatches (reason : FailReason) (e : Error) : Bool :=
  match reason with
  | .failure f why => causeMatches e.cause f.cause && e.notRetried == some why
  | .tooManyRedirects limit =>
    reprStr e.cause == reprStr (Cause.tooManyRedirects limit) && e.notRetried.isNone
  | .deadline => reprStr e.cause == reprStr (Cause.timeout .deadline) && e.notRetried.isNone

/--
How the body of the request of `hop` is framed, when the call's body is framed by `body`.
-/
def hopBody (hop : Hop) (body : Codec.RequestFraming) : Codec.RequestFraming :=
  match hop.body with
  | .original => body
  | .empty => .length 0

/--
Where the request of `hop` goes and the head it is encoded with, as the client must write it: the
origin (`host:port`) of `Client.plan` and the head of the request serialiser, for a body framed by
`body`; or why the client cannot send it.
-/
def expectedWire (hop : Hop) (body : Codec.RequestFraming) (keepAlive : Bool) :
    Except String (String × ByteArray) := do
  let plan ← Client.plan hop.head
  return (plan.target, (Codec.encodeHeadWith keepAlive plan.head body).1)

/--
How far an exchange that began as `first` may have got: a response means request bytes were
written, whatever the server then said.
-/
def endedDelivery : Client.Ended → Delivery
  | .response .. => .maybeDelivered
  | .failure f _ => f.delivery

/--
How far an exchange that ended with `outcome` got.
-/
def outcomeDelivery : Outcome → Delivery
  | .response _ => .responseReceived
  | .failure f => f.delivery

/--
Replays `events` through the planner, and returns the first place where the client did something
the planner did not say, or `ok` with the number of steps checked.
-/
def validate (events : Array Event) : Except String Nat := do
  let some (Event.start policy head kind body seed deadline keepAlive) := events[0]?
    | throw "the trace does not begin with the call's start"
  let mut st ← match Call.start policy head kind seed deadline with
    | .ok st => pure st
    | .error e =>
      throw s!"the planner refuses to start this call ({reprStr e}), but the client started it"
  let mut expect := Expect.send 0 false
  let mut lastSend := 0
  let mut steps := 0
  let mut furthest := Delivery.notSent
  for h : i in [1:events.size] do
    let event := events[i]
    let here := s!"event {i} ({event.describe})"
    match expect, event with
    | .send notBefore _, .send sent target wire sentBody time =>
      if reprStr sent != reprStr st.current.head then
        throw s!"{here}: the client sent {reprStr sent}, the planner's request is {reprStr st.current.head}"
      if sentBody != hopBody st.current body then
        throw s!"{here}: the client sent a body of {framingText sentBody}, the hop carries {framingText (hopBody st.current body)}"
      match expectedWire st.current sentBody keepAlive with
      | .error msg => throw s!"{here}: the client sent a request it cannot reach ({msg})"
      | .ok (t, w) =>
        if t != target then
          throw s!"{here}: the client connected to {target}, the request goes to {t}"
        if w != wire then
          throw s!"{here}: the client wrote the head {repr (String.fromUTF8? wire)}, the request's is {repr (String.fromUTF8? w)}"
      if time < notBefore then
        throw s!"{here}: the retry went out at {time}, before its delay ended at {notBefore}"
      lastSend := time
      expect := .decide none
    | .send _ true, .fail e =>
      -- The client could not send the planner's next request (a target it cannot reach).
      unless e.cause matches .invalidRequest _ do
        throw s!"{here}: the client failed instead of sending the next request, with {reprStr e.cause}"
      unless (expectedWire st.current (hopBody st.current body) keepAlive) matches .error _ do
        throw s!"{here}: the client refused a request it can send"
      unless e.hops == st.hops && e.retries == st.retries && e.delivery.rank ≥ furthest.rank do
        throw s!"{here}: the error's hops, retries or delivery are not the call's"
      expect := .done
    | .decide none, .redispatch reused first reason =>
      unless reused do throw s!"{here}: an exchange on a fresh connection was sent again"
      unless Client.redispatch? st.current.head.method (st.current.replayable st.bodyKind) first ==
          some reason do
        throw s!"{here}: an exchange that began as {reprStr first} was sent again for {reprStr reason}, which redispatch? does not allow"
      furthest := furthest.max (endedDelivery first)
      expect := .decide (some reason)
    | .decide redispatched, .decide clock outcome step =>
      if clock.now < lastSend then
        throw s!"{here}: the planner was asked at {clock.now}, before the request went out at {lastSend}"
      -- Once an exchange that may have reached the server was sent again, a failure of the second
      -- one does not tell the planner the request was not sent.
      if redispatched == some .closedBeforeResponse then
        if let .failure f := outcome then
          if f.delivery == .notSent then
            throw s!"{here}: after a request that may have been delivered was sent again, the failure says not sent"
      furthest := furthest.max (outcomeDelivery outcome)
      let (st', mine) := plan st clock outcome
      if reprStr mine != reprStr step then
        throw s!"{here}: the client took the step {reprStr step}, the planner says {reprStr mine}"
      steps := steps + 1
      st := st'
      expect := match mine with
        | .deliver => .deliver
        | .follow _ => .send clock.now true
        | .retry delay _ => .wait (min (clock.now + delay) deadline)
        | .fail reason => .fail reason
    | .wait endsAt, .wait waited =>
      if waited != endsAt then
        throw s!"{here}: the client waited until {waited}, the planner's delay ends at {endsAt}"
      expect := .send endsAt false
    | .deliver, .deliver => expect := .done
    | .fail reason, .fail e =>
      unless errorMatches reason e do
        throw s!"{here}: the call failed with {reprStr e.cause} ({reprStr e.notRetried}), the planner said {reprStr reason}"
      unless e.hops == st.hops && e.retries == st.retries do
        throw s!"{here}: the error says {e.hops} redirects and {e.retries} retries, the planner {st.hops} and {st.retries}"
      unless e.delivery.rank ≥ furthest.rank do
        throw s!"{here}: the error says {e.delivery.name}, but a request of the call got as far as {furthest.name}"
      expect := .done
    | _, _ => throw s!"{here}: not what the planner's last step calls for"
  match expect with
  | .done => return steps
  | .decide _ => throw "the trace ends after a request went out, without a decision"
  | _ => throw "the trace ends before the call did"

end LeanHttp.Call
