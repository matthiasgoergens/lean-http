module

import all LeanHttp.Call.Proofs
import all LeanHttp.RequestBody
import all LeanHttp.Wire
import all LeanHttp.Error

/-!
# Proofs about streamed request bodies in a call

What the per-call planner and the re-dispatch rule guarantee for a body the caller streams
(`RequestBody.stream`).  The client starts the planner with the body's kind (`RequestBody.kind`),
which for a stream is `BodyKind.stream`; every state the planner reaches keeps that kind
(`ReachableWith.bodyKind`); and the planner's theorems then say:

- once any byte of the request may have reached the server, the planner never retries a request
  that carries the stream (`streamed_no_resend`, from `plan_no_resend`);
- a redirect the planner follows never carries the stream (`streamed_follow_empty`, from
  `plan_follow_replayable`), so a 307 or 308, which keeps the method and the body, is never followed
  while the request carries it (`streamed_no_follow_same_method`), and the response is delivered;
- an exchange on a pooled connection is sent again on a fresh one, for a stream, only if nothing of
  it was written (`redispatch?_unreplayable`).

A retry after a failure that sent nothing is allowed whatever the body, and sends the stream again:
that is safe because the exchange core pulls nothing from the stream before it has issued a write
(`LeanHttp.Exchange.observed_notSent_unpulled`), so such a failure has read none of it.

What they do not cover: that the client passes the planner the kind of the body it sends, that it
sends the planner's current request, and that it passes `redispatch?` the hop's replayability are
the wiring's obligations (`Client.run`, `CallSpec.loop`), checked by `Call.validate` on the record of
each call in the real-socket tests.
-/

namespace LeanHttp

open Std.Http

/-- A streamed body is, to the planner, a body that cannot be sent again. -/
theorem RequestBody.kind_stream (size : Option Nat) (next : Std.Async.Async (Option ByteArray)) :
    (RequestBody.stream size next).kind = .stream := rfl

namespace Call

/-- The states a call started with a body of kind `kind` can be in. -/
inductive ReachableWith (kind : BodyKind) : State → Prop where
  /-- A started call. -/
  | start {policy head seed deadline st} :
      Call.start policy head kind seed deadline = .ok st → ReachableWith kind st
  /-- One step of the planner. -/
  | step {st} (clock : Clock) (outcome : Outcome) :
      ReachableWith kind st → ReachableWith kind (plan st clock outcome).1

theorem start_bodyKind {policy : Policy} {head : Request.Head} {kind : BodyKind} {seed : UInt64}
    {deadline : Timestamp} {st : State} (h : Call.start policy head kind seed deadline = .ok st) :
    st.bodyKind = kind ∧ st.current.body = .original := by
  unfold Call.start at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- **The kind of the body is the kind the call started with**, in every state of the call. -/
theorem ReachableWith.bodyKind {kind : BodyKind} {st : State} (h : ReachableWith kind st) :
    st.bodyKind = kind := by
  induction h with
  | start hs => exact (start_bodyKind hs).1
  | step clock outcome _ ih => rw [(plan_frame _ clock outcome).2.2.2]; exact ih

/--
**A streamed body is never sent again once a byte may have reached the server.**  In every state of
a call whose body is a stream, while the current request carries that body, an outcome after which
any request byte may have reached the server (a response, or a failure that is not `notSent` or
counts a byte written) is never retried.
-/
theorem streamed_no_resend {size : Option Nat} {next : Std.Async.Async (Option ByteArray)}
    {st : State} {clock : Clock} {outcome : Outcome}
    (h : ReachableWith (RequestBody.stream size next).kind st) (hb : st.current.body = .original)
    (hs : outcome.mayHaveSent = true) :
    ∀ st' d k, plan st clock outcome ≠ (st', .retry d k) := by
  apply plan_no_resend hs
  right
  simp [Hop.replayable, hb, h.bodyKind, RequestBody.kind, BodyKind.replayable]

/--
**A followed redirect never carries a streamed body.**  In every state of a call whose body is a
stream, the request of a redirect the planner follows carries no body.
-/
theorem streamed_follow_empty {size : Option Nat} {next' : Std.Async.Async (Option ByteArray)}
    {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (h : ReachableWith (RequestBody.stream size next').kind st)
    (hp : plan st clock outcome = (st', .follow next)) : next.body = .empty := by
  have hr := plan_follow_replayable hp
  rw [h.bodyKind] at hr
  cases hb : next.body with
  | empty => rfl
  | original => simp [Hop.replayable, hb, RequestBody.kind, BodyKind.replayable] at hr

/--
**A redirect that keeps the method is not followed while the request carries a streamed body.**
A 307 or 308, or any redirect that leaves the method as it is (a 301 or 302 to a request that is not
a POST), would have to send the body again; while the current request carries a streamed body, the
planner never follows it.  (`plan_refused_delivered` and `plan_no_follow` say what it does instead:
the response is delivered.)
-/
theorem streamed_no_follow_same_method {size : Option Nat}
    {next' : Std.Async.Async (Option ByteArray)} {st : State} {clock : Clock} {head : Response.Head}
    (h : ReachableWith (RequestBody.stream size next').kind st) (hb : st.current.body = .original)
    (hm : redirectMethod st.current.head.method head.status.toCode.toNat = st.current.head.method) :
    ∀ st' next, plan st clock (.response head) ≠ (st', .follow next) := by
  intro st' next hp
  have he := streamed_follow_empty h hp
  obtain ⟨head', ho, hd, _⟩ := plan_follow hp
  cases ho
  obtain ⟨_, _, hbody, _⟩ := decideRedirect_follow hd
  simp [hm, hb] at hbody
  rw [hbody] at he
  cases he

/--
**A streamed body is sent again on a fresh connection only if nothing of it was written.**  For a
body that cannot be sent again, `Client.redispatch?` allows a re-dispatch only for an exchange that
failed with nothing sent.
-/
theorem redispatch?_unreplayable {method : Method} {e : Client.Ended} {r : Client.Redispatch}
    (h : Client.redispatch? method false e = some r) :
    r = .notSent ∧ ∃ f received, e = .failure f received ∧ f.delivery = .notSent := by
  cases e with
  | response head interim => simp [Client.redispatch?] at h
  | failure f received =>
    refine ⟨?_, f, received, rfl, ?_⟩ <;>
      cases hd : f.delivery <;> cases hcz : f.cause <;> simp_all +decide [Client.redispatch?]

end Call

end LeanHttp
