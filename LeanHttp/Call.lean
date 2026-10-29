module

public import LeanHttp.Backoff
public import LeanHttp.Exchange
public import LeanHttp.Call.Redirect
public import LeanHttp.Call.RetryAfter

@[expose] public section

/-!
# The per-call planner

One call can take several exchanges: redirects, and retries of a hop that failed.  The planner
decides, after each exchange, what comes next, as a pure function of the call's state, the time and
how the exchange ended (`Call.plan`).  The shell that runs the exchanges performs the step it
returns: deliver the response to the caller, follow a redirect with the next request, send the same
request again after a delay, or fail.

- **Redirects** (`LeanHttp.Call.Redirect`): at most `Policy.maxRedirects` are followed; a redirect
  beyond them fails the call with `tooManyRedirects`, rather than delivering the last 3xx as a
  success.  There is no cycle detection keyed on URLs: a POST answered by 303 to the same URL, or a
  302 to the page it came from, is legitimate, and the hop limit alone ends a real loop.
- **Retries** are per hop and never cross a redirect: a retry sends the current hop's request again,
  and following a redirect starts the new hop with no retries.  A failure where nothing was sent may
  be retried whatever the method; once any request byte may have reached the server, only an
  idempotent method with a body that can be sent again; a failure after the response head arrived,
  never; a failure the client caused itself (`localClose`), never, whatever was sent, since closing
  a client must not make it send a request again.
- **Delays**: a retry after a failure waits a full-jitter backoff (`LeanHttp.Backoff`), drawn from
  the call's seed and the number of retries so far.  Retries of 429 and 503 responses are opt-in
  and wait what `Retry-After` asks for (in seconds, or until an HTTP-date, measured from the
  response's `Date` when it has one), the backoff when it is absent, and are given up when the wait
  is longer than `Policy.maxRetryAfterMs`.  No delay reaches the call's deadline: a retry that would
  have to wait until the deadline is not made.
- **Budget**: at most `Policy.maxRetriesPerHop` retries of one hop, and `Policy.retryBudget` in the
  whole call.

This is the split Go makes between its `Client`, which follows redirects, and its `Transport`.
-/

namespace LeanHttp.Call

set_option linter.all true

open Std.Http

/--
The rules of a call.
-/
structure Policy where
  /--
  Whether redirects are followed at all (default: yes).  When not, a redirect is delivered to the
  caller like any other response.
  -/
  followRedirects : Bool := true

  /--
  Most redirects followed in one call (default: 10).  A redirect beyond them fails the call with
  `tooManyRedirects`.
  -/
  maxRedirects : Nat := 10

  /--
  Most retries of one hop (default: 2).
  -/
  maxRetriesPerHop : Nat := 2

  /--
  Most retries in the whole call, over all its hops (default: 4).
  -/
  retryBudget : Nat := 4

  /--
  Base of the exponential backoff, in milliseconds (default: 100 ms).
  -/
  backoffBaseMs : Nat := 100

  /--
  Ceiling of the exponential backoff, in milliseconds (default: 5 s).
  -/
  backoffCapMs : Nat := 5 * 1000

  /--
  Whether a 429 (Too Many Requests) response is retried (default: no).
  -/
  retry429 : Bool := false

  /--
  Whether a 503 (Service Unavailable) response is retried (default: no).
  -/
  retry503 : Bool := false

  /--
  Longest `Retry-After` honoured, in milliseconds (default: 60 s).  A response that asks for a
  longer wait is delivered to the caller.
  -/
  maxRetryAfterMs : Nat := 60 * 1000
deriving Repr, Inhabited

/--
The planner's view of a call.
-/
structure State where
  /--
  The rules of the call.
  -/
  policy : Policy

  /--
  The origin of the call's first request, the one its credentials were given for.
  -/
  originalOrigin : URI.Origin

  /--
  The credential fields of the call's first request.
  -/
  given : Fields

  /--
  The kind of the call's body.
  -/
  bodyKind : BodyKind

  /--
  The request of the current hop.
  -/
  current : Hop

  /--
  Redirects followed so far.
  -/
  hops : Nat := 0

  /--
  Retries of the current hop so far.
  -/
  attempts : Nat := 0

  /--
  Retries in the whole call so far.
  -/
  retries : Nat := 0

  /--
  The seed of the backoff jitter.
  -/
  seed : UInt64

  /--
  The deadline of the whole call, on the monotonic clock of `Clock.now`.
  -/
  deadline : Timestamp
deriving Repr

/--
The time at which the planner decides.
-/
structure Clock where
  /--
  Milliseconds of the monotonic clock the deadline is on.
  -/
  now : Timestamp

  /--
  Seconds since 1970-01-01T00:00:00Z on the wall clock, for a `Retry-After` date when the response
  has no `Date`, and to place the two-digit years of obsolete dates.  It has no default, so that a
  shell cannot leave it at 1970 by mistake, which would make every date look decades away.
  -/
  wallSec : Nat
deriving Repr

/--
How an exchange ended.
-/
inductive Outcome where
  /--
  The final response head arrived.  Its body has not been read.
  -/
  | response (head : Response.Head)

  /--
  The exchange failed (or no connection was made).
  -/
  | failure (failure : Failure)
deriving Repr

/--
What a retry waits for.
-/
inductive DelayKind where
  /--
  The full-jitter backoff.
  -/
  | backoff

  /--
  The response's `Retry-After`.
  -/
  | retryAfter
deriving Repr, DecidableEq

/--
Why a call fails.
-/
inductive FailReason where
  /--
  The exchange failed and is not retried, for the reason `why`.  `NoRetry` is defined with the
  client's errors (`LeanHttp.Error`), so that a call's error can say it.
  -/
  | failure (failure : Failure) (why : NoRetry)

  /--
  Another redirect arrived after `limit` had been followed.
  -/
  | tooManyRedirects (limit : Nat)

  /--
  A redirect arrived when the call's deadline had passed.
  -/
  | deadline
deriving Repr

/--
What the shell does next.
-/
inductive Step where
  /--
  Deliver the response to the caller.  The call is over.
  -/
  | deliver

  /--
  Discard the response and send `next`, the request of the next hop.
  -/
  | follow (next : Hop)

  /--
  Send the current hop's request again after `delayMs` milliseconds.
  -/
  | retry (delayMs : Nat) (kind : DelayKind)

  /--
  Fail the call.
  -/
  | fail (reason : FailReason)
deriving Repr

/--
Why a call cannot start.
-/
inductive StartError where
  /--
  The request's target is not an absolute URI.
  -/
  | notAbsolute

  /--
  The URI has no host.
  -/
  | noHost

  /--
  The scheme is neither `http` nor `https`.
  -/
  | scheme (name : String)
deriving Repr, DecidableEq

/--
The origin a URI addresses: its scheme, host and port (the scheme's default when it names none).
-/
def uriOrigin (uri : URI) : Option URI.Origin :=
  uri.host?.map fun host => { scheme := uri.scheme, host, port := uri.port }

/--
Starts a call of `head`, whose target must be an absolute `http` or `https` URI, with a body of kind
`kind`, the backoff seed `seed` and the deadline `deadline`.  The first hop sends `head` as it is.
The credential fields kept to give back at the original origin are those of `head`, less any its
`Connection` fields name as hop-by-hop.
-/
def start (policy : Policy) (head : Request.Head) (kind : BodyKind) (seed : UInt64)
    (deadline : Timestamp) : Except StartError State :=
  match head.uri with
  | .absoluteForm uri =>
    match uriOrigin uri with
    | none => .error .noHost
    | some origin =>
      if origin.scheme.val ≠ "http" ∧ origin.scheme.val ≠ "https" then
        .error (.scheme origin.scheme.val)
      else
        .ok {
          policy, originalOrigin := origin,
          given := credentials (dropNames (nominatedNames head.headers.toList) head.headers.toList),
          bodyKind := kind, current := { origin, head, body := .original }, seed, deadline }
  | _ => .error .notAbsolute

/--
Whether a cause can be retried at all: a connect failure, the connection closing under the request,
or a read or write timeout.  The client closing the connection itself, the call's deadline, name
resolution, an invalid request, a malformed response and a limit are never retried.
-/
def retryableCause : Cause → Bool
  | .connect _ => true
  | .peerClosed => true
  | .timeout .read => true
  | .timeout .write => true
  | _ => false

/--
Whether any request byte may have reached the server: the failure says the request may have been
delivered or was answered, or counts a byte written.
-/
def mayHaveSent (f : Failure) : Bool :=
  f.delivery ≠ .notSent || f.written > 0

/--
Whether any request byte may have reached the server: always for a response, and for a failure as
`mayHaveSent` says.
-/
def Outcome.mayHaveSent : Outcome → Bool
  | .response _ => true
  | .failure f => Call.mayHaveSent f

/--
The time left before the call's deadline.
-/
def State.remaining (st : State) (clock : Clock) : Nat :=
  st.deadline - clock.now

/--
Whether the current request can be sent again: its method is idempotent and its body replayable.
-/
def State.resendable (st : State) : Bool :=
  st.current.head.method.isIdempotent && st.current.replayable st.bodyKind

/--
The backoff before the next retry: the full-jitter draw for the call's retry number `retries`.
-/
def State.backoff (st : State) : Nat :=
  Backoff.delayMs st.policy.backoffBaseMs st.policy.backoffCapMs st.seed st.retries

/--
Whether the retry counters allow another retry.
-/
def State.mayRetry (st : State) : Bool :=
  st.attempts < st.policy.maxRetriesPerHop && st.retries < st.policy.retryBudget

/--
The state after deciding to retry the current hop.
-/
def State.retried (st : State) : State :=
  { st with attempts := st.attempts + 1, retries := st.retries + 1 }

/--
Decides whether a failed exchange is retried, and after what delay.
-/
def retryFailure (st : State) (clock : Clock) (f : Failure) : Except NoRetry Nat :=
  if !retryableCause f.cause then .error .cause
  else if f.delivery = .responseReceived then .error .responseReceived
  else if mayHaveSent f && !st.resendable then .error .delivered
  else if st.attempts ≥ st.policy.maxRetriesPerHop then .error .hopLimit
  else if st.retries ≥ st.policy.retryBudget then .error .budget
  else if st.backoff < st.remaining clock then .ok st.backoff
  else .error .noTime

/--
`Retry-After` field name.
-/
def retryAfterName : Header.Name := .mk "retry-after"

/--
The wait a response asks for, in milliseconds, if its `Retry-After` parses: seconds, or the time
until a date, from the response's `Date` if that parses and from the wall clock otherwise.
-/
def retryAfterMs (head : Response.Head) (wallSec : Nat) : Option Nat := do
  let value ← head.headers.get? retryAfterName
  let parsed ← RetryAfter.parse value.value wallSec
  let reference :=
    match head.headers.get? .date >>= fun d => RetryAfter.httpDate (RetryAfter.yearOf wallSec)
        (RetryAfter.trimOws d.value.toList) with
    | some t => t
    | none => wallSec
  return parsed.delayMs reference

/--
Decides whether a response is retried as a 429 or 503 the policy opts into, and after what delay:
only for a request that can be sent again, within the retry counters, and when the wait is within
`Policy.maxRetryAfterMs` (for a `Retry-After`) and ends before the deadline.
-/
def retryStatus (st : State) (clock : Clock) (head : Response.Head) : Option (Nat × DelayKind) :=
  let code := head.status.toCode.toNat
  if !((code = 429 && st.policy.retry429) || (code = 503 && st.policy.retry503)) then none
  else if !st.resendable || !st.mayRetry then none
  else
    let (delay, kind) := match retryAfterMs head clock.wallSec with
      | some ms => (ms, DelayKind.retryAfter)
      | none => (st.backoff, .backoff)
    if kind = .retryAfter && delay > st.policy.maxRetryAfterMs then none
    else if delay < st.remaining clock then some (delay, kind)
    else none

/--
Decides what follows an exchange of the current hop that ended with `outcome`, at `clock`: the
planner's one step.  Returns the call's new state and what the shell does next.
-/
def plan (st : State) (clock : Clock) (outcome : Outcome) : State × Step :=
  match outcome with
  | .failure f =>
    match retryFailure st clock f with
    | .ok delay => (st.retried, .retry delay .backoff)
    | .error why => (st, .fail (.failure f why))
  | .response head =>
    match retryStatus st clock head with
    | some (delay, kind) => (st.retried, .retry delay kind)
    | none =>
      if !st.policy.followRedirects then (st, .deliver) else
      match decideRedirect st.bodyKind st.originalOrigin st.given st.current head with
      | .follow next =>
        if st.hops ≥ st.policy.maxRedirects then (st, .fail (.tooManyRedirects st.policy.maxRedirects))
        else if clock.now ≥ st.deadline then (st, .fail .deadline)
        else ({ st with current := next, hops := st.hops + 1, attempts := 0 }, .follow next)
      | _ => (st, .deliver)

/--
The states a call can be in: the state `start` returns, and every state `plan` returns from one of
them.
-/
inductive Reachable : State → Prop where
  /--
  A started call.
  -/
  | start {policy head kind seed deadline st} :
      Call.start policy head kind seed deadline = .ok st → Reachable st

  /--
  One step of the planner.
  -/
  | step {st} (clock : Clock) (outcome : Outcome) : Reachable st → Reachable (plan st clock outcome).1

end LeanHttp.Call
