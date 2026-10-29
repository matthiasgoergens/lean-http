module

import all Std.Http.Internal.IndexMultiMap
import all Std.Http.Data.Headers
import all Std.Http.Data.Headers.Name
import all Std.Http.Data.URI
public import LeanHttp.Call

/-!
# Proofs about the per-call planner

Theorems about `Call.start` and `Call.plan` for the rules of the planner.  Each main theorem's
docstring names its rule in bold.  Two kinds of statement:

- **Single steps** (`plan_*`): what one step of the planner returns, for any state.
- **Runs** (`Reachable.*`): invariants of every state reachable from `start` by steps, at any times
  and with any outcomes.  The request the shell sends is always the state's current request (first,
  after a `follow`, and again after a `retry`), so an invariant of `State.current` holds for every
  request of the call.

Fields are stated through `Headers.toList`, which lists the entries the request encoder writes
(`Headers`' `Encode` instance folds over the same entries); the header lemmas below say what
`Headers.ofList` gives back, by unfolding `Std.Http`'s multimap.

What they do not cover:

- Origins are compared by `originKey`: scheme, the host as written in a URI (lower case for names)
  and port.  Two spellings of one host that `Std.Http`'s URI parser does not normalise to the same
  string count as different origins, which only drops credentials more often.
- The encoder (`Codec.encodeRequest`) adds `Connection` and `Content-Length` of its own; nothing
  here looks at it.  An empty body with GET gets no `Content-Length` (RFC 9110 section 8.6), so a
  request whose method changed carries no content field on the wire either.
- That the shell sends the request a step names, waits the delay it names from the time it passed,
  and reports outcomes truthfully (in particular `Failure.delivery` and `Failure.written`) is the
  wiring's obligation.  The theorems of the exchange core (`LeanHttp.Exchange.Proofs`) cover how
  `delivery` is computed there.  `Call.validate` checks the client's record of each call
  (`Config.observe`) against the planner: the steps, the requests as written, the waits and the
  errors; the real-socket tests do so for every call they make.  That the outcomes in the record are
  the true ones it cannot check.
- A retry after a `notSent` failure may send a streamed body, which is safe only if the shell has
  not read any of the stream before the failure; the exchange core takes the whole body as bytes
  today, so this is an obligation on the streaming shell to come.
- A 307 or 308 answer to a POST is followed with the same method and body (when the body is
  replayable): that is a redirect the server asked for, not a retry, and the retry theorems do not
  speak of it.  `plan_follow_replayable` says that such a request can be sent again.
- The `Retry-After` parser and the redirect target's path resolution are tested, not proved.
-/

namespace LeanHttp.Call

open Std.Http Std.Internal

private theorem foldl_insert_entries (l : Fields) (acc : IndexMultiMap Header.Name Header.Value) :
    (l.foldl (fun acc (kv : Header.Name × Header.Value) => acc.insert kv.1 kv.2) acc).entries =
      acc.entries ++ l.toArray := by
  induction l generalizing acc with
  | nil => simp
  | cons kv l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    show (acc.entries.push kv) ++ l.toArray = _
    simp

theorem toList_ofList (l : Fields) : (Headers.ofList l).toList = l := by
  show (IndexMultiMap.ofList l).entries.toList = l
  unfold IndexMultiMap.ofList
  rw [foldl_insert_entries]
  simp [IndexMultiMap.empty]

/-! ## Field lists -/

theorem mem_dropNames {names : List Header.Name} {fs : Fields} {e : Header.Name × Header.Value} :
    e ∈ dropNames names fs ↔ e ∈ fs ∧ e.1 ∉ names := by
  simp [dropNames, List.mem_filter]

theorem mem_credentials {fs : Fields} {e : Header.Name × Header.Value} :
    e ∈ credentials fs ↔ e ∈ fs ∧ e.1 ∈ credentialNames := by
  simp [credentials, List.mem_filter]

private theorem host_not_credential : Header.Name.host ∉ credentialNames := by
  simp [credentialNames, Header.Name.host, Header.Name.authorization, Header.Name.cookie,
    Header.Name.proxyAuthorization, Header.Name.ext_iff]

private theorem host_not_content : Header.Name.host ∉ contentNames := by
  simp [contentNames, Header.Name.host, Header.Name.contentType, Header.Name.contentLength,
    Header.Name.contentEncoding, Header.Name.contentLanguage, Header.Name.contentLocation,
    Header.Name.lastModified, Header.Name.transferEncoding, digestName, contentDigestName,
    reprDigestName, Header.Name.ext_iff]

private theorem credential_not_content : ∀ n ∈ credentialNames, n ∉ contentNames := by
  intro n hn
  simp only [credentialNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl <;>
  simp [contentNames, Header.Name.authorization, Header.Name.cookie,
    Header.Name.proxyAuthorization, Header.Name.contentType, Header.Name.contentLength,
    Header.Name.contentEncoding, Header.Name.contentLanguage, Header.Name.contentLocation,
    Header.Name.lastModified, Header.Name.transferEncoding, digestName, contentDigestName,
    reprDigestName, Header.Name.ext_iff]

private theorem crossOrigin_not_credential :
    ∀ n ∈ Header.Name.referer :: validatorNames, n ∉ credentialNames := by
  intro n hn
  simp only [validatorNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl <;>
  simp [credentialNames, Header.Name.referer, Header.Name.ifNoneMatch, Header.Name.ifModifiedSince,
    Header.Name.authorization, Header.Name.cookie, Header.Name.proxyAuthorization, Header.Name.ext_iff]

private theorem host_not_crossOrigin : Header.Name.host ∉ Header.Name.referer :: validatorNames := by
  simp [validatorNames, Header.Name.referer, Header.Name.ifNoneMatch, Header.Name.ifModifiedSince,
    Header.Name.host, Header.Name.ext_iff]

theorem mem_crossOriginStep {co : Bool} {fs : Fields} {e : Header.Name × Header.Value}
    (h : e ∈ crossOriginStep co fs) : e ∈ fs ∧ (co = true → e.1 ∉ Header.Name.referer :: validatorNames) := by
  unfold crossOriginStep at h
  split at h
  · exact ⟨(mem_dropNames.1 h).1, fun _ => (mem_dropNames.1 h).2⟩
  · exact ⟨h, by simp_all⟩

theorem mem_methodStep {mc : Bool} {fs : Fields} {e : Header.Name × Header.Value}
    (h : e ∈ methodStep mc fs) : e ∈ fs ∧ (mc = true → e.1 ∉ contentNames ++ validatorNames) := by
  unfold methodStep at h
  split at h
  · exact ⟨(mem_dropNames.1 h).1, fun _ => (mem_dropNames.1 h).2⟩
  · exact ⟨h, by simp_all⟩

theorem mem_credentialStep {toO fo : Bool} {given fs : Fields} {e : Header.Name × Header.Value}
    (h : e ∈ credentialStep toO fo given fs) :
    (e ∈ fs ∧ (toO = false → e.1 ∉ credentialNames)) ∨ (toO = true ∧ e ∈ given) := by
  unfold credentialStep at h
  split at h
  · split at h
    · exact .inl ⟨h, by simp_all⟩
    · rcases List.mem_append.1 h with h | h
      · exact .inl ⟨(mem_dropNames.1 h).1, by simp_all⟩
      · exact .inr ⟨by assumption, h⟩
  · exact .inl ⟨(mem_dropNames.1 h).1, fun _ => (mem_dropNames.1 h).2⟩

theorem mem_hostStep {co : Bool} {host : Option Header.Value} {fs : Fields}
    {e : Header.Name × Header.Value} (h : e ∈ hostStep co host fs) :
    (e ∈ fs ∧ (co = true → e.1 ≠ Header.Name.host)) ∨
      (co = true ∧ e.1 = Header.Name.host ∧ host = some e.2) := by
  unfold hostStep at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    rcases List.mem_append.1 h with h | h
    · exact .inl ⟨(mem_dropNames.1 h).1, fun _ => by simpa using (mem_dropNames.1 h).2⟩
    · cases host <;> simp at h
      subst h
      exact .inr ⟨hc.1, rfl, rfl⟩
  · rename_i hc
    refine .inl ⟨h, fun hco he => hc ?_⟩
    simp only [hco, Bool.true_and, List.any_eq_true, decide_eq_true_eq]
    exact ⟨e, h, he⟩

/--
What a field of the next request can be: a field of the current request that survived every step,
a credential field given back, or the rewritten `Host`.
-/
theorem mem_nextFields {fields : Fields} {co mc toO fo : Bool} {given : Fields}
    {host : Option Header.Value} {e : Header.Name × Header.Value}
    (h : e ∈ nextFields fields co mc toO fo given host) :
    (e ∈ fields ∧ (co = true → e.1 ∉ Header.Name.referer :: validatorNames ∧ e.1 ≠ Header.Name.host) ∧
        (mc = true → e.1 ∉ contentNames ++ validatorNames) ∧ (toO = false → e.1 ∉ credentialNames)) ∨
      (toO = true ∧ e ∈ given ∧ (co = true → e.1 ≠ Header.Name.host)) ∨
      (co = true ∧ e.1 = Header.Name.host ∧ host = some e.2) := by
  unfold nextFields at h
  rcases mem_hostStep h with ⟨h, hh⟩ | h
  · rcases mem_credentialStep h with ⟨h, hc⟩ | ⟨ht, hg⟩
    · have ⟨h, hm⟩ := mem_methodStep h
      have ⟨h, hx⟩ := mem_crossOriginStep h
      exact .inl ⟨(mem_dropNames.1 h).1, fun hco => ⟨hx hco, hh hco⟩, hm, hc⟩
    · exact .inr (.inl ⟨ht, hg, hh⟩)
  · exact .inr (.inr h)

/--
Credential fields are dropped from the next request unless it goes to the original origin.
-/
theorem nextFields_credentials {fields : Fields} {co mc fo : Bool} {given : Fields}
    {host : Option Header.Value} :
    ∀ e ∈ nextFields fields co mc false fo given host, e.1 ∉ credentialNames := by
  intro e he
  rcases mem_nextFields he with ⟨_, _, _, hc⟩ | ⟨h, _⟩ | ⟨_, hh, _⟩
  · exact hc rfl
  · cases h
  · rw [hh]; exact host_not_credential

/--
When the method changes, the next request has no content field, provided the credentials given
back are credential fields.
-/
theorem nextFields_content {fields : Fields} {co toO fo : Bool} {given : Fields}
    {host : Option Header.Value} (hg : ∀ e ∈ given, e.1 ∈ credentialNames) :
    ∀ e ∈ nextFields fields co true toO fo given host, e.1 ∉ contentNames := by
  intro e he
  rcases mem_nextFields he with ⟨_, _, hm, _⟩ | ⟨_, h, _⟩ | ⟨_, hh, _⟩
  · exact fun hn => hm rfl (List.mem_append_left _ hn)
  · exact credential_not_content _ (hg e h)
  · rw [hh]; exact host_not_content

/--
On a hop to another origin, every `Host` field of the next request is the rewritten one.
-/
theorem nextFields_host {fields : Fields} {mc toO fo : Bool} {given : Fields}
    {host : Option Header.Value} :
    ∀ e ∈ nextFields fields true mc toO fo given host, e.1 = Header.Name.host → host = some e.2 := by
  intro e he hn
  rcases mem_nextFields he with ⟨_, hx, _, _⟩ | ⟨_, _, hx⟩ | ⟨_, _, hh⟩
  · exact absurd hn (hx rfl).2
  · exact absurd hn (hx rfl)
  · exact hh

/-! ## The redirect decision -/

/--
The shape of a followed redirect: the code is one the client follows, the method is
`redirectMethod`'s, the body goes only with an unchanged method, and the fields are `nextFields`'.
-/
theorem decideRedirect_follow {kind : BodyKind} {orig : URI.Origin} {given : Fields} {cur : Hop}
    {resp : Response.Head} {next : Hop}
    (h : decideRedirect kind orig given cur resp = .follow next) :
    resp.status.toCode.toNat ∈ followedCodes ∧
    next.head.method = redirectMethod cur.head.method resp.status.toCode.toNat ∧
    next.body = (if redirectMethod cur.head.method resp.status.toCode.toNat ≠ cur.head.method
      then .empty else cur.body) ∧
    next.head.headers.toList = nextFields cur.head.headers.toList
      (decide (originKey next.origin ≠ originKey cur.origin))
      (decide (redirectMethod cur.head.method resp.status.toCode.toNat ≠ cur.head.method))
      (decide (originKey next.origin = originKey orig))
      (decide (originKey cur.origin = originKey orig)) given
      (Header.Value.ofString? next.origin.hostHeader) := by
  unfold decideRedirect at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · split at h <;> split at h <;> (try contradiction) <;>
              (injection h with h; subst h; simp_all [toList_ofList])

/--
A changed method is always GET.
-/
theorem redirectMethod_changed {m : Method} {code : Nat} (h : redirectMethod m code ≠ m) :
    redirectMethod m code = .get := by
  unfold redirectMethod at *
  split <;> (try split) <;> simp_all

/--
A followed redirect's request can be sent again: it carries no body, or the original body when
that is replayable.
-/
theorem decideRedirect_follow_replayable {kind : BodyKind} {orig : URI.Origin} {given : Fields}
    {cur : Hop} {resp : Response.Head} {next : Hop}
    (h : decideRedirect kind orig given cur resp = .follow next) : next.replayable kind = true := by
  unfold decideRedirect at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · split at h <;> split at h <;> (try contradiction) <;>
              (injection h with h; subst h; simp_all [Hop.replayable])

/--
A followed redirect's target is the absolute URI of its origin and a resolved path and query.
-/
theorem decideRedirect_follow_target {kind : BodyKind} {orig : URI.Origin} {given : Fields}
    {cur : Hop} {resp : Response.Head} {next : Hop}
    (h : decideRedirect kind orig given cur resp = .follow next) :
    ∃ path query, next.head.uri = .absoluteForm (targetUri next.origin path query) := by
  unfold decideRedirect at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · split at h <;> split at h <;> (try contradiction) <;>
              (injection h with h; subst h; exact ⟨_, _, rfl⟩)

/--
A followed redirect goes to an http or https origin.
-/
theorem decideRedirect_follow_scheme {kind : BodyKind} {orig : URI.Origin} {given : Fields}
    {cur : Hop} {resp : Response.Head} {next : Hop}
    (h : decideRedirect kind orig given cur resp = .follow next) :
    next.origin.scheme.val = "http" ∨ next.origin.scheme.val = "https" := by
  unfold decideRedirect at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · rename_i hs
            split at h <;> split at h <;> (try contradiction) <;>
              (injection h with h; subst h; simp only [ne_eq, not_and, Decidable.not_not] at hs;
               exact (Classical.em _).elim Or.inl (fun hp => Or.inr (hs hp)))

/--
A redirect the planner refuses has a code it follows.
-/
theorem decideRedirect_refuse_code {kind : BodyKind} {orig : URI.Origin} {given : Fields}
    {cur : Hop} {resp : Response.Head} {why : Refusal}
    (h : decideRedirect kind orig given cur resp = .refuse why) :
    resp.status.toCode.toNat ∈ followedCodes := by
  unfold decideRedirect at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hc
    simpa using hc

/--
The URI `targetUri` writes addresses the origin it was written for.
-/
theorem uriOrigin_targetUri (o : URI.Origin) (path : URI.Path) (query : Option URI.Query) :
    uriOrigin (targetUri o path query) = some o := by
  unfold uriOrigin targetUri
  simp only [URI.host?, URI.port, Option.map_some]
  by_cases hp : o.port = URI.Scheme.defaultPort o.scheme
  · simp only [hp, ↓reduceIte]
    obtain ⟨scheme, host, port⟩ := o
    simp only at hp
    simp [hp]
  · simp only [hp, ↓reduceIte]

/--
Origins with different schemes have different keys: a hop from https to http changes the origin.
-/
theorem originKey_ne_of_scheme {a b : URI.Origin} (h : a.scheme.val ≠ b.scheme.val) :
    originKey a ≠ originKey b :=
  fun he => h (congrArg OriginKey.scheme he)

/--
Origins with different ports have different keys.
-/
theorem originKey_ne_of_port {a b : URI.Origin} (h : a.port ≠ b.port) : originKey a ≠ originKey b :=
  fun he => h (congrArg OriginKey.port he)

/-! ## The steps of the planner -/

/--
What a `follow` step requires and does.
-/
theorem plan_follow {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (h : plan st clock outcome = (st', .follow next)) :
    ∃ head, outcome = .response head ∧
      decideRedirect st.bodyKind st.originalOrigin st.given st.current head = .follow next ∧
      st.hops < st.policy.maxRedirects ∧ clock.now < st.deadline ∧
      st' = { st with current := next, hops := st.hops + 1, attempts := 0 } := by
  unfold plan at h
  split at h
  · split at h <;> simp at h
  · rename_i head
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i next' hd
          split at h
          · simp at h
          · rename_i hhops
            split at h
            · simp at h
            · rename_i hnow
              simp only [Prod.mk.injEq, Step.follow.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨head, rfl, hd, Nat.lt_of_not_le hhops, Nat.lt_of_not_le hnow, rfl⟩
        · simp at h

/--
A `follow` step needs redirects to be on.
-/
theorem plan_follow_on {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (h : plan st clock outcome = (st', .follow next)) : st.policy.followRedirects = true := by
  unfold plan at h
  split at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp_all

/--
What a `retry` step requires and does.
-/
theorem plan_retry {st st' : State} {clock : Clock} {outcome : Outcome} {d : Nat} {k : DelayKind}
    (h : plan st clock outcome = (st', .retry d k)) :
    st' = st.retried ∧
      ((∃ f, outcome = .failure f ∧ retryFailure st clock f = .ok d ∧ k = .backoff) ∨
       (∃ head, outcome = .response head ∧ retryStatus st clock head = some (d, k))) := by
  unfold plan at h
  split at h
  · rename_i f
    split at h
    · rename_i d' hr
      simp only [Prod.mk.injEq, Step.retry.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, .inl ⟨f, rfl, hr, rfl⟩⟩
    · simp at h
  · rename_i head
    split at h
    · rename_i d' k' hr
      simp only [Prod.mk.injEq, Step.retry.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, .inr ⟨head, rfl, hr⟩⟩
    · split at h
      · simp at h
      · split at h
        · split at h
          · simp at h
          · split at h <;> simp at h
        · simp at h

/--
What a retry after a failure requires.
-/
theorem retryFailure_ok {st : State} {clock : Clock} {f : Failure} {d : Nat}
    (h : retryFailure st clock f = .ok d) :
    retryableCause f.cause = true ∧ f.delivery ≠ .responseReceived ∧
      (mayHaveSent f = true → st.resendable = true) ∧
      st.attempts < st.policy.maxRetriesPerHop ∧ st.retries < st.policy.retryBudget ∧
      d = st.backoff ∧ d < st.remaining clock := by
  unfold retryFailure at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp only [Except.ok.injEq] at h
              subst h
              refine ⟨by simp_all, by assumption, fun hs => by simp_all, by omega, by omega, rfl,
                by assumption⟩
            · simp at h

/--
What a retry of a 429 or 503 requires.
-/
theorem retryStatus_some {st : State} {clock : Clock} {head : Response.Head} {d : Nat}
    {k : DelayKind} (h : retryStatus st clock head = some (d, k)) :
    ((head.status.toCode.toNat = 429 ∧ st.policy.retry429 = true) ∨
      (head.status.toCode.toNat = 503 ∧ st.policy.retry503 = true)) ∧ st.resendable = true ∧
      st.attempts < st.policy.maxRetriesPerHop ∧ st.retries < st.policy.retryBudget ∧
      d < st.remaining clock ∧ (k = .backoff → d = st.backoff) ∧
      (k = .retryAfter → d ≤ st.policy.maxRetryAfterMs) := by
  unfold retryStatus at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hcode
    split at h
    · simp at h
    · rename_i hres
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        Bool.not_eq_false, not_or] at hcode hres
      have hc : (head.status.toCode.toNat = 429 ∧ st.policy.retry429 = true) ∨
          (head.status.toCode.toNat = 503 ∧ st.policy.retry503 = true) := by
        rcases hcode with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
      unfold State.mayRetry at hres
      cases hr : retryAfterMs head clock.wallSec with
      | none =>
        simp only [hr] at h
        split at h
        · simp at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨hc, ?_, ?_, ?_, by assumption, fun _ => rfl, ?_⟩
            · simp_all
            · simp_all
            · simp_all
            · intro hk; cases hk
          · simp at h
      | some ms =>
        simp only [hr] at h
        split at h
        · simp at h
        · rename_i hmax
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨hc, ?_, ?_, ?_, by assumption, ?_, ?_⟩
            · simp_all
            · simp_all
            · simp_all
            · intro hk; cases hk
            · intro _; simp_all
          · simp at h

/--
The backoff never exceeds its cap.
-/
theorem backoff_le_cap (st : State) : st.backoff ≤ st.policy.backoffCapMs := by
  unfold State.backoff
  exact Backoff.delayMs_le_cap st.policy.backoffBaseMs st.policy.backoffCapMs st.seed st.retries

/--
A 429 or 503 is never a followed redirect, so a redirect is never retried as one.
-/
theorem retryStatus_of_followed {st : State} {clock : Clock} {head : Response.Head}
    (h : head.status.toCode.toNat ∈ followedCodes) : retryStatus st clock head = none := by
  cases hr : retryStatus st clock head with
  | none => rfl
  | some p =>
    obtain ⟨d, k⟩ := p
    have := (retryStatus_some hr).1
    revert h this
    generalize head.status.toCode.toNat = n
    intro h this
    simp only [followedCodes, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases this with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

/--
What `plan` never changes.
-/
theorem plan_frame (st : State) (clock : Clock) (outcome : Outcome) :
    (plan st clock outcome).1.policy = st.policy ∧
      (plan st clock outcome).1.originalOrigin = st.originalOrigin ∧
      (plan st clock outcome).1.given = st.given ∧
      (plan st clock outcome).1.bodyKind = st.bodyKind := by
  unfold plan
  repeat' split
  all_goals simp [State.retried]

/--
The current request changes only by following a redirect.
-/
theorem plan_current (st : State) (clock : Clock) (outcome : Outcome) :
    (plan st clock outcome).1.current = st.current ∨
      ((plan st clock outcome).2 = .follow (plan st clock outcome).1.current ∧
       (plan st clock outcome).1.hops = st.hops + 1 ∧ st.hops < st.policy.maxRedirects) := by
  rcases hp : plan st clock outcome with ⟨st', step⟩
  cases step with
  | follow next =>
    obtain ⟨_, _, _, hlt, _, rfl⟩ := plan_follow hp
    exact .inr ⟨rfl, rfl, hlt⟩
  | retry d k =>
    obtain ⟨rfl, _⟩ := plan_retry hp
    exact .inl rfl
  | deliver | fail _ =>
    left
    unfold plan at hp
    repeat' split at hp
    all_goals simp_all [State.retried]

/--
Hops change only by following a redirect.
-/
theorem plan_hops (st : State) (clock : Clock) (outcome : Outcome) :
    (plan st clock outcome).1.hops = st.hops ∨
      ((plan st clock outcome).1.hops = st.hops + 1 ∧ st.hops < st.policy.maxRedirects) := by
  rcases hp : plan st clock outcome with ⟨st', step⟩
  cases step with
  | follow next =>
    obtain ⟨_, _, _, hlt, _, rfl⟩ := plan_follow hp
    exact .inr ⟨rfl, hlt⟩
  | retry d k =>
    obtain ⟨rfl, _⟩ := plan_retry hp
    exact .inl rfl
  | deliver | fail _ =>
    left
    unfold plan at hp
    repeat' split at hp
    all_goals simp_all [State.retried]

/-! ## The rules -/

/--
**Credentials stay with their origin** (one step).  When the planner follows a redirect to an
origin other than the call's original one, the next request carries no `Authorization`, `Cookie` or
`Proxy-Authorization` field.
-/
theorem plan_follow_credentials {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (h : plan st clock outcome = (st', .follow next))
    (hne : originKey next.origin ≠ originKey st.originalOrigin) :
    ∀ e ∈ next.head.headers.toList, e.1 ∉ credentialNames := by
  obtain ⟨head, -, hd, -⟩ := plan_follow h
  obtain ⟨-, -, -, hf⟩ := decideRedirect_follow hd
  rw [hf, show decide (originKey next.origin = originKey st.originalOrigin) = false by simp [hne]]
  exact nextFields_credentials

/--
**Credentials stay with their origin.**  In every state a call can reach, if the current request
goes to an origin other than the call's original one, it carries no `Authorization`, `Cookie` or
`Proxy-Authorization` field.  The current request is the one the shell is to send, first, after a
`follow` and again after a `retry`, and its target addresses its origin (`Reachable.target`).
Origins are compared by `originKey`, which differs when the scheme or the port does
(`originKey_ne_of_scheme`, `originKey_ne_of_port`), so a hop from https to http changes the origin.
-/
theorem Reachable.credentials {st : State} (h : Reachable st)
    (hne : originKey st.current.origin ≠ originKey st.originalOrigin) :
    ∀ e ∈ st.current.head.headers.toList, e.1 ∉ credentialNames := by
  induction h with
  | start hs =>
    exfalso
    unfold Call.start at hs
    split at hs
    · split at hs
      · simp at hs
      · split at hs
        · simp at hs
        · simp only [Except.ok.injEq] at hs
          subst hs
          exact hne rfl
    · simp at hs
  | @step st clock outcome _ ih =>
    obtain ⟨-, horig, -, -⟩ := plan_frame st clock outcome
    rw [horig] at hne
    rcases plan_current st clock outcome with hc | ⟨hf, -⟩
    · rw [hc] at hne ⊢
      exact ih hne
    · exact plan_follow_credentials (Prod.ext rfl hf) (horig ▸ hne)

/--
**The hop limit holds.**  In every state a call can reach, the number of redirects followed is at
most `Policy.maxRedirects`.
-/
theorem Reachable.hops_le {st : State} (h : Reachable st) : st.hops ≤ st.policy.maxRedirects := by
  induction h with
  | start hs =>
    unfold Call.start at hs
    split at hs
    · split at hs
      · simp at hs
      · split at hs
        · simp at hs
        · simp only [Except.ok.injEq] at hs
          subst hs
          simp
    · simp at hs
  | @step st clock outcome _ ih =>
    obtain ⟨hpol, -⟩ := plan_frame st clock outcome
    rw [hpol]
    rcases plan_hops st clock outcome with hh | ⟨hh, hlt⟩ <;> omega

/--
**Reaching the hop limit is an error.**  A redirect that would be followed when
`Policy.maxRedirects` redirects have been followed already fails the call with `tooManyRedirects`:
the last 3xx is not delivered as if it were the answer.
-/
theorem plan_hop_limit {st : State} {clock : Clock} {head : Response.Head} {next : Hop}
    (hf : st.policy.followRedirects = true)
    (hd : decideRedirect st.bodyKind st.originalOrigin st.given st.current head = .follow next)
    (hmax : st.policy.maxRedirects ≤ st.hops) :
    plan st clock (.response head) = (st, .fail (.tooManyRedirects st.policy.maxRedirects)) := by
  have hr := retryStatus_of_followed (st := st) (clock := clock) (decideRedirect_follow hd).1
  unfold plan
  simp only [hr, hf, hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp [Nat.le_iff_lt_or_eq] at hmax ⊢
  omega

/--
**No resend after bytes may have reached the server, unless safe.**  If the current request's
method is not idempotent, or its body cannot be sent again, then after an outcome where any request
byte may have reached the server (a response, or a failure that is not `notSent` or counts a byte
written) the planner never retries it.
-/
theorem plan_no_resend {st : State} {clock : Clock} {outcome : Outcome}
    (hs : outcome.mayHaveSent = true)
    (hr : st.current.head.method.isIdempotent = false ∨ st.current.replayable st.bodyKind = false) :
    ∀ st' d k, plan st clock outcome ≠ (st', .retry d k) := by
  intro st' d k h
  have hres : st.resendable = false := by
    unfold State.resendable
    rcases hr with hr | hr <;> simp [hr]
  rcases (plan_retry h).2 with ⟨f, rfl, hf, -⟩ | ⟨head, rfl, hst⟩
  · have := (retryFailure_ok hf).2.2.1 hs
    simp_all
  · have := (retryStatus_some hst).2.1
    simp_all

/--
**Closing never causes a resend.**  A failure caused by the client closing the connection itself
(`localClose`) is never retried, whatever was sent.
-/
theorem plan_localClose {st : State} {clock : Clock} {f : Failure} (hc : f.cause = .localClose) :
    ∀ st' d k, plan st clock (.failure f) ≠ (st', .retry d k) := by
  intro st' d k h
  rcases (plan_retry h).2 with ⟨f', hf', hr, -⟩ | ⟨_, hh, _⟩
  · cases hf'
    have := (retryFailure_ok hr).1
    simp [hc, retryableCause] at this
  · cases hh

/--
**Delays are bounded.**  Every retry the planner plans waits less than the time left before the
call's deadline; a backoff delay is at most `Policy.backoffCapMs`, and a `Retry-After` delay at most
`Policy.maxRetryAfterMs`.
-/
theorem plan_retry_delay {st st' : State} {clock : Clock} {outcome : Outcome} {d : Nat}
    {k : DelayKind} (h : plan st clock outcome = (st', .retry d k)) :
    d < st.deadline - clock.now ∧ (k = .backoff → d ≤ st.policy.backoffCapMs) ∧
      (k = .retryAfter → d ≤ st.policy.maxRetryAfterMs) := by
  rcases (plan_retry h).2 with ⟨f, -, hf, rfl⟩ | ⟨head, -, hst⟩
  · obtain ⟨-, -, -, -, -, rfl, hlt⟩ := retryFailure_ok hf
    exact ⟨hlt, fun _ => backoff_le_cap st, fun h => by cases h⟩
  · obtain ⟨-, -, -, -, hlt, hb, ha⟩ := retryStatus_some hst
    exact ⟨hlt, fun hk => hb hk ▸ backoff_le_cap st, ha⟩

/--
**Retries never cross a redirect** (the retry half).  After a `retry`, the state's current request,
which the shell sends again, and the number of redirects followed are unchanged.
-/
theorem plan_retry_same_hop {st st' : State} {clock : Clock} {outcome : Outcome} {d : Nat}
    {k : DelayKind} (h : plan st clock outcome = (st', .retry d k)) :
    st'.current = st.current ∧ st'.hops = st.hops := by
  obtain ⟨rfl, -⟩ := plan_retry h
  exact ⟨rfl, rfl⟩

/--
**303 means GET.**  A followed 303 makes the next request a GET, or a HEAD if the current one is a
HEAD.
-/
theorem plan_follow_303 {st st' : State} {clock : Clock} {head : Response.Head} {next : Hop}
    (h : plan st clock (.response head) = (st', .follow next)) (hc : head.status.toCode = 303) :
    next.head.method = if st.current.head.method = .head then .head else .get := by
  obtain ⟨head', hh, hd, -⟩ := plan_follow h
  cases hh
  rw [(decideRedirect_follow hd).2.1, hc]
  rfl

/--
The fields a reachable call keeps to give back at its original origin are credential fields.
-/
theorem Reachable.given {st : State} (h : Reachable st) : ∀ e ∈ st.given, e.1 ∈ credentialNames := by
  induction h with
  | start hs =>
    unfold Call.start at hs
    split at hs
    · split at hs
      · simp at hs
      · split at hs
        · simp at hs
        · simp only [Except.ok.injEq] at hs
          subst hs
          intro e he
          exact (mem_credentials.1 he).2
    · simp at hs
  | @step st clock outcome _ ih =>
    rw [(plan_frame st clock outcome).2.2.1]
    exact ih

/--
**A method change drops the body and the content fields.**  When a followed redirect changes the
method of a call's request, the new method is GET, and the next request carries no body and no
content field (`Content-Type`, `Content-Length`, `Content-Encoding`, `Content-Language`,
`Content-Location`, `Last-Modified`, `Transfer-Encoding`, `Digest`, `Content-Digest`,
`Repr-Digest`).
-/
theorem plan_follow_method_change {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (hst : Reachable st) (h : plan st clock outcome = (st', .follow next))
    (hm : next.head.method ≠ st.current.head.method) :
    next.head.method = .get ∧ next.body = .empty ∧
      ∀ e ∈ next.head.headers.toList, e.1 ∉ contentNames := by
  obtain ⟨head, -, hd, -⟩ := plan_follow h
  obtain ⟨-, hmeth, hbody, hf⟩ := decideRedirect_follow hd
  rw [hmeth] at hm
  refine ⟨hmeth ▸ redirectMethod_changed hm, by simp [hbody, hm], ?_⟩
  rw [hf, show decide (redirectMethod st.current.head.method head.status.toCode.toNat ≠
    st.current.head.method) = true by simp [hm]]
  exact nextFields_content hst.given

/--
**`Host` follows the origin.**  When a followed redirect changes the origin, every `Host` field the
next request carries names the new origin (`URI.Origin.hostHeader`).  It may carry none (the first
request had none, its `Connection` field named `Host`, or the new host cannot be written as a field
value); the client is then to write one from the target, which addresses the new origin
(`Reachable.target`).  On a hop that keeps the origin, `Host` is left as it was, so a `Host` the
first request gave for a virtual host is kept.
-/
theorem plan_follow_host {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (h : plan st clock outcome = (st', .follow next))
    (hne : originKey next.origin ≠ originKey st.current.origin) :
    ∀ e ∈ next.head.headers.toList, e.1 = .host →
      Header.Value.ofString? next.origin.hostHeader = some e.2 := by
  obtain ⟨head, -, hd, -⟩ := plan_follow h
  obtain ⟨-, -, -, hf⟩ := decideRedirect_follow hd
  rw [hf, show decide (originKey next.origin ≠ originKey st.current.origin) = true by simp [hne]]
  exact nextFields_host

/--
**The retry counters hold.**  In every state a call can reach, the current hop has been retried at
most `Policy.maxRetriesPerHop` times, and the call at most `Policy.retryBudget` times.
-/
theorem Reachable.retries_le {st : State} (h : Reachable st) :
    st.attempts ≤ st.policy.maxRetriesPerHop ∧ st.retries ≤ st.policy.retryBudget := by
  induction h with
  | start hs =>
    unfold Call.start at hs
    split at hs
    · split at hs
      · simp at hs
      · split at hs
        · simp at hs
        · simp only [Except.ok.injEq] at hs
          subst hs
          simp
    · simp at hs
  | @step st clock outcome _ ih =>
    rcases hp : plan st clock outcome with ⟨st', step⟩
    simp only
    cases step with
    | follow next =>
      obtain ⟨_, _, _, _, _, rfl⟩ := plan_follow hp
      simp only
      omega
    | retry d k =>
      obtain ⟨rfl, hr⟩ := plan_retry hp
      unfold State.retried
      simp only
      rcases hr with ⟨f, -, hf, -⟩ | ⟨head, -, hst⟩
      · have := retryFailure_ok hf
        omega
      · have := retryStatus_some hst
        omega
    | deliver | fail _ =>
      have : st' = st := by
        unfold plan at hp
        repeat' split at hp
        all_goals simp_all [State.retried]
      subst this
      exact ih

/--
**Retries never cross a redirect** (the redirect half).  A `follow` makes the next request the
current one, counts the redirect, and starts the new hop with no retries; the call's retry count is
kept.
-/
theorem plan_follow_new_hop {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (h : plan st clock outcome = (st', .follow next)) :
    st'.current = next ∧ st'.hops = st.hops + 1 ∧ st'.attempts = 0 ∧ st'.retries = st.retries := by
  obtain ⟨_, _, _, _, _, rfl⟩ := plan_follow h
  exact ⟨rfl, rfl, rfl, rfl⟩

/--
**A redirect never sends a streamed body again.**  The request of a followed redirect can always be
sent: it carries no body, or the original body when that is replayable.  (A redirect that would
have to send a streamed body again is refused, and `plan_refused_delivered` says it is delivered.)
-/
theorem plan_follow_replayable {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (h : plan st clock outcome = (st', .follow next)) : next.replayable st.bodyKind = true := by
  obtain ⟨_, _, hd, _⟩ := plan_follow h
  exact decideRedirect_follow_replayable hd

/--
**Retries of 429 and 503 are opt-in.**  A retry after a response is made only for a 429 when
`Policy.retry429` is set, or a 503 when `Policy.retry503` is.
-/
theorem plan_retry_status {st st' : State} {clock : Clock} {head : Response.Head} {d : Nat}
    {k : DelayKind} (h : plan st clock (.response head) = (st', .retry d k)) :
    (head.status.toCode.toNat = 429 ∧ st.policy.retry429 = true) ∨
      (head.status.toCode.toNat = 503 ∧ st.policy.retry503 = true) := by
  rcases (plan_retry h).2 with ⟨_, hf, _, _⟩ | ⟨head', hh, hst⟩
  · cases hf
  · cases hh
    exact (retryStatus_some hst).1

/--
**Redirects can be turned off.**  With `Policy.followRedirects` off, the planner never follows a
redirect.
-/
theorem plan_no_follow {st : State} {clock : Clock} {outcome : Outcome}
    (hoff : st.policy.followRedirects = false) :
    ∀ st' next, plan st clock outcome ≠ (st', .follow next) := by
  intro st' next h
  simp [plan_follow_on h] at hoff

/--
**The target addresses the origin.**  In every state a call can reach, the current request's target
is an absolute URI whose scheme, host and port are those of the current origin, so a shell that
connects by the URI and one that connects by `Hop.origin` reach the same place.
-/
theorem Reachable.target {st : State} (h : Reachable st) :
    ∃ u, st.current.head.uri = .absoluteForm u ∧ uriOrigin u = some st.current.origin := by
  induction h with
  | start hs =>
    unfold Call.start at hs
    split at hs
    · rename_i u hu
      split at hs
      · simp at hs
      · rename_i o ho
        split at hs
        · simp at hs
        · simp only [Except.ok.injEq] at hs
          subst hs
          exact ⟨u, hu, ho⟩
    · simp at hs
  | @step st clock outcome _ ih =>
    rcases plan_current st clock outcome with hc | ⟨hf, -⟩
    · rw [hc]; exact ih
    · obtain ⟨_, _, hd, _⟩ := plan_follow (Prod.ext rfl hf)
      obtain ⟨p, q, hu⟩ := decideRedirect_follow_target hd
      exact ⟨_, hu, uriOrigin_targetUri _ _ _⟩

/--
**No content field without a body.**  In every state a call can reach, a current request that
carries no body (because a redirect changed its method, on this hop or an earlier one) carries no
content field either.
-/
theorem Reachable.emptyBody {st : State} (h : Reachable st) (he : st.current.body = .empty) :
    ∀ e ∈ st.current.head.headers.toList, e.1 ∉ contentNames := by
  induction h with
  | start hs =>
    exfalso
    unfold Call.start at hs
    split at hs
    · split at hs
      · simp at hs
      · split at hs
        · simp at hs
        · simp only [Except.ok.injEq] at hs
          subst hs
          cases he
    · simp at hs
  | @step st clock outcome hst ih =>
    rcases plan_current st clock outcome with hc | ⟨hf, -⟩
    · rw [hc] at he ⊢; exact ih he
    · have hp : plan st clock outcome = ((plan st clock outcome).1, .follow (plan st clock outcome).1.current) :=
        Prod.ext rfl hf
      by_cases hm : (plan st clock outcome).1.current.head.method = st.current.head.method
      · obtain ⟨head, -, hd, -⟩ := plan_follow hp
        obtain ⟨-, hmeth, hbody, hfields⟩ := decideRedirect_follow hd
        rw [hmeth] at hm
        rw [hbody] at he
        simp only [hm, ne_eq, not_true_eq_false, ↓reduceIte] at he
        intro e hmem
        rw [hfields] at hmem
        rcases mem_nextFields hmem with ⟨hin, -⟩ | ⟨-, hg, -⟩ | ⟨-, hh, -⟩
        · exact ih he e hin
        · exact credential_not_content _ (hst.given e hg)
        · rw [hh]; exact host_not_content
      · exact (plan_follow_method_change hst hp hm).2.2

/--
**No content field without a body** (the hops after a method change).  A followed redirect from a
request that carries no body carries none either: once a redirect has changed the method, every
later request of the call goes without a body, and so (`Reachable.emptyBody`) without content
fields.
-/
theorem plan_follow_keeps_empty {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (h : plan st clock outcome = (st', .follow next)) (he : st.current.body = .empty) :
    next.body = .empty := by
  obtain ⟨_, _, hd, _⟩ := plan_follow h
  obtain ⟨-, -, hbody, -⟩ := decideRedirect_follow hd
  rw [hbody]
  split <;> simp_all

/--
**A redirect that is not followed is the answer.**  A 301, 302, 303, 307 or 308 that the planner
refuses (no `Location`, one it cannot use, or a body it cannot send again) is delivered to the caller.
-/
theorem plan_refused_delivered {st : State} {clock : Clock} {head : Response.Head} {why : Refusal}
    (hd : decideRedirect st.bodyKind st.originalOrigin st.given st.current head = .refuse why) :
    plan st clock (.response head) = (st, .deliver) := by
  have hr := retryStatus_of_followed (st := st) (clock := clock) (decideRedirect_refuse_code hd)
  unfold plan
  simp only [hr, hd]
  split <;> rfl

/--
**Redirects can be turned off** (what happens instead).  With `Policy.followRedirects` off, a
redirect (301, 302, 303, 307 or 308) is delivered to the caller like any other response.
-/
theorem plan_off_delivered {st : State} {clock : Clock} {head : Response.Head}
    (hoff : st.policy.followRedirects = false) (hc : head.status.toCode.toNat ∈ followedCodes) :
    plan st clock (.response head) = (st, .deliver) := by
  have hr := retryStatus_of_followed (st := st) (clock := clock) hc
  unfold plan
  simp [hr, hoff]

/--
**What is never retried.**  A failure is never retried when its cause is not one that can be
retried (anything but a connect failure, the connection closing, or a read or write timeout: so
never `localClose`, the call's deadline, name resolution, an invalid request, a malformed response or
a limit), nor when the response head had arrived.
-/
theorem plan_no_retry {st : State} {clock : Clock} {f : Failure}
    (h : retryableCause f.cause = false ∨ f.delivery = .responseReceived) :
    ∀ st' d k, plan st clock (.failure f) ≠ (st', .retry d k) := by
  intro st' d k hp
  rcases (plan_retry hp).2 with ⟨f', hf', hr, -⟩ | ⟨_, hh, _⟩
  · cases hf'
    have := retryFailure_ok hr
    rcases h with h | h <;> simp_all
  · cases hh

/--
**A hop to another origin drops `Referer` and the cache validators.**  When a followed redirect
changes the origin, the next request carries no `Referer`, `If-None-Match` or `If-Modified-Since`
field.
-/
theorem plan_follow_cross_origin {st st' : State} {clock : Clock} {outcome : Outcome} {next : Hop}
    (hst : Reachable st) (h : plan st clock outcome = (st', .follow next))
    (hne : originKey next.origin ≠ originKey st.current.origin) :
    ∀ e ∈ next.head.headers.toList, e.1 ∉ Header.Name.referer :: validatorNames := by
  obtain ⟨head, -, hd, -⟩ := plan_follow h
  obtain ⟨-, -, -, hf⟩ := decideRedirect_follow hd
  rw [hf, show decide (originKey next.origin ≠ originKey st.current.origin) = true by simp [hne]]
  intro e he hn
  rcases mem_nextFields he with ⟨-, hx, -⟩ | ⟨-, hg, -⟩ | ⟨-, hh, -⟩
  · exact (hx rfl).1 hn
  · exact crossOrigin_not_credential _ hn (hst.given e hg)
  · rw [hh] at hn; exact host_not_crossOrigin hn

/--
**Only http and https.**  In every state a call can reach, the current request goes to an http or
https origin.
-/
theorem Reachable.scheme {st : State} (h : Reachable st) :
    st.current.origin.scheme.val = "http" ∨ st.current.origin.scheme.val = "https" := by
  induction h with
  | start hs =>
    unfold Call.start at hs
    split at hs
    · split at hs
      · simp at hs
      · rename_i o _
        split at hs
        · simp at hs
        · rename_i hsch
          simp only [Except.ok.injEq] at hs
          subst hs
          by_cases hh : o.scheme.val = "http" <;> simp_all
    · simp at hs
  | @step st clock outcome _ ih =>
    rcases plan_current st clock outcome with hc | ⟨hf, -⟩
    · rw [hc]; exact ih
    · obtain ⟨_, _, hd, _⟩ := plan_follow (Prod.ext rfl hf)
      exact decideRedirect_follow_scheme hd

end LeanHttp.Call
