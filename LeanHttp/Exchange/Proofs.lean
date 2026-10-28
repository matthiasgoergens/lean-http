module

import all LeanHttp.Exchange

/-!
# Proofs about the exchange core

Theorems about `Exchange.begin` and `Exchange.step` for the properties that `Tests/Core.lean` checks
by random runs and bounded exploration (`Tests/Support/Check.lean`).  Each main theorem's docstring
names the checker property it corresponds to.

They hold whatever the response parser returns: no proof here looks inside it, so every parser state
and event it returns is arbitrary.

Three kinds of statement:

- **Single steps** (`step_*`), for any exchange satisfying `Inv`.  `Inv` does not hold for every
  exchange (from a hand-built state no run reaches, a step can deliver a head with nothing written),
  but `Reachable.inv` proves it for every exchange reachable from `begin` by steps.
- **Runs** (`Reachable`, `Run`, `Observed`): inductive predicates over `begin` followed by any
  sequence of steps at any times, with the shell's count of writes and reads in flight (`Run`) or
  the checker's model of the run (`Observed`, with `Obs` mirroring the checker's `Model`).
- **`begin`** (`begin_*`), for its own actions.

What they do not cover:

- The request head is measured by `prepare` (`headBytes`, from what the serialiser encoded); the
  checker measures it independently, as the first blank line.  That the two agree depends on the
  encoding of `Std.Http`'s header fields and is not proved.
- The checker's properties that compare the response with the bytes sent ("finish only after a
  complete response", "a finished response delivered its whole body", "the body is the response's",
  and the clause of "reusable only when safe" that the bytes read are exactly one reusable response)
  are about the parser, and are not proved here.
- "A live exchange has a deadline ahead", and liveness under the deadline, are proved in
  `LeanHttp.Exchange.Liveness`, which builds on this module.

## Within a step

A step runs `handle`, `expire` and `schedule` over the state `(ex, actions)`.  `Good` is what holds
at every point in between: fields that do not change, the invariant `Inv`, that every action emitted
so far is still justified by the state (`ActOK`), that the exchange is terminal exactly when an
ending action was emitted, which is last, how many writes, reads and heads were emitted, and that
body bytes come after a head.
-/

namespace LeanHttp.Exchange

open Std.Http

/-- The state of a step. -/
abbrev S := Exchange × Array ExchangeAction

/-! ## Running the state monad -/

@[simp] theorem bind_run {α β : Type} (m : StepM α) (f : α → StepM β) (s : S) :
    (m >>= f).run s = (f (m.run s).1).run (m.run s).2 := rfl
@[simp] theorem pure_run {α : Type} (a : α) (s : S) : (pure a : StepM α).run s = (a, s) := rfl
@[simp] theorem ite_run {α : Type} (c : Prop) [Decidable c] (m₁ m₂ : StepM α) (s : S) :
    (if c then m₁ else m₂).run s = if c then m₁.run s else m₂.run s := by
  split <;> rfl
/-- Reading the exchange at the start of a computation, kept syntactically in terms of `ex`. -/
theorem getEx_bind_run {β : Type} (f : Exchange → StepM β) (ex : Exchange)
    (acts : Array ExchangeAction) : (getEx >>= f).run (ex, acts) = (f ex).run (ex, acts) := rfl
@[simp] theorem getEx_run (s : S) : getEx.run s = (s.1, s) := rfl
@[simp] theorem setEx_run (ex : Exchange) (s : S) : (setEx ex).run s = ((), (ex, s.2)) := rfl
@[simp] theorem modifyEx_run (f : Exchange → Exchange) (s : S) :
    (modifyEx f).run s = ((), (f s.1, s.2)) := rfl
@[simp] theorem emit_run (a : ExchangeAction) (s : S) :
    (emit a).run s = ((), (s.1, s.2.push a)) := rfl

/-! ## Kinds of actions and phases -/

/-- `true` for the actions that end an exchange. -/
def isEnd : ExchangeAction → Bool
  | .finish _ | .fail _ => true
  | _ => false

/-- `true` for `finish true`. -/
def reuses : ExchangeAction → Bool
  | .finish true => true
  | _ => false

/-- `true` for writes. -/
def isWrite : ExchangeAction → Bool
  | .write _ => true
  | _ => false

/-- `true` for reads. -/
def isRead : ExchangeAction → Bool
  | .read _ => true
  | _ => false

/-- `true` for the delivery of the final head. -/
def isHead : ExchangeAction → Bool
  | .deliverHead _ => true
  | _ => false

/-- `true` for the delivery of body bytes. -/
def isChunk : ExchangeAction → Bool
  | .deliverBody _ => true
  | _ => false

/-- `true` in the phase before the request head has been written. -/
def Phase.isSending : Phase → Bool
  | .sending => true
  | _ => false

/-- `true` in the phases after the request head was written and before the end. -/
def Phase.isActive : Phase → Bool
  | .awaitingHead | .receiving | .draining => true
  | _ => false

/-- `true` in the phases with a delivered final head and a body to read. -/
def Phase.isBody : Phase → Bool
  | .receiving | .draining => true
  | _ => false

/-! ## What holds at every point -/

/-- The conditions for reporting the connection reusable. -/
structure Reusable (ex : Exchange) : Prop where
  /-- Keep-alive was asked for. -/
  keepAlive : ex.config.keepAlive = true
  /--
  The parser says the connection could carry another exchange: the response ended, framed with
  certainty, with nothing after it and before the end of input, and its keep-alive verdict (of the
  final head's version and `Connection` fields, and in the codec's code of every interim head's too)
  allowed it.
  -/
  codec : ex.parser.reusable = true
  /-- The caller received the whole body: nothing is held back. -/
  delivered : ex.held = []
  /-- The whole request was written. -/
  writtenAll : ex.written = ex.request.size
  /-- The final head did not arrive before the request was written in full. -/
  notEarly : ex.early = false
  /-- The peer did not close. -/
  noEnd : ex.inputEnded = false
  /-- A final head was delivered. -/
  head : ex.head.isSome = true

/-- What an emitted action says about the state, from its emission to the end of the step. -/
def ActOK (ex : Exchange) : ExchangeAction → Prop
  | .write b =>
    0 < b.size ∧ b = ex.request.extract ex.written (ex.written + b.size) ∧
      ex.writeInFlight = some b.size ∧ ex.sentAny = true
  | .read _ => ex.headBytes ≤ ex.written ∧ ex.readInFlight = true
  | .deliverHead h =>
    ex.head = some h ∧ ex.headBytes ≤ ex.written ∧ ex.early = decide (ex.written < ex.request.size)
  | .deliverBody _ => ex.head.isSome = true
  | .finish r => ex.phase = .finished r ∧ (r = true → Reusable ex)
  | .fail f =>
    ex.phase = .failed f ∧ f.delivery = ex.delivery ∧ f.written = ex.written ∧
      f.status = ex.head.map (·.status)

/-- The invariant of the exchange, at every point of every step from `begin`. -/
structure Inv (ex : Exchange) : Prop where
  /-- Past the sending phase, the request head has been written. -/
  headWritten : ex.phase.isActive = true → ex.headBytes ≤ ex.written
  /-- While a body is read, the final head was delivered. -/
  hasHead : ex.phase.isBody = true → ex.head.isSome = true
  /-- No more is written than the request. -/
  writtenLe : ex.written ≤ ex.request.size
  /-- Nor once the write in flight completes. -/
  inFlightLe : ∀ k, ex.writeInFlight = some k → ex.written + k ≤ ex.request.size

/-- The fields that no step changes after it set the time. -/
structure Fixed (a b : Exchange) : Prop where
  config : b.config = a.config
  request : b.request = a.request
  headBytes : b.headBytes = a.headBytes
  method : b.method = a.method
  deadline : b.deadline = a.deadline
  now : b.now = a.now
  written : b.written = a.written
  inputEnded : b.inputEnded = a.inputEnded

/-- Every ending action is the last one. -/
def EndLast (acts : Array ExchangeAction) : Prop :=
  ∀ (i : Nat) (h : i < acts.size), isEnd acts[i] = true → i + 1 = acts.size

/--
What holds at every point of a step that started from `ex₀`.  `w` is the write in flight once the
event was taken into account, and `r` whether a read was; `schedule` may issue one of each, and
nothing else issues any.
-/
structure Good (ex₀ : Exchange) (w : Option Nat) (r : Bool) (s : S) : Prop where
  fixed : Fixed ex₀ s.1
  inv : Inv s.1
  acts : ∀ a ∈ s.2, ActOK s.1 a
  ends : s.1.terminal = true → ∃ a ∈ s.2, isEnd a = true
  endLast : EndLast s.2
  writes : (s.2.countP isWrite = 0 ∧ s.1.writeInFlight = w) ∨ (s.2.countP isWrite = 1 ∧ w = none)
  reads : (s.2.countP isRead = 0 ∧ s.1.readInFlight = r) ∨ (s.2.countP isRead = 1 ∧ r = false)
  heads : (s.2.countP isHead = 0 ∧ s.1.head = ex₀.head ∧ s.1.early = ex₀.early) ∨
    (s.2.countP isHead = 1 ∧ ex₀.head = none ∧ s.1.head.isSome = true)
  sent : s.1.sentAny = (ex₀.sentAny || decide (0 < s.2.countP isWrite))
  chunkAfterHead : ∀ (i : Nat) (h : i < s.2.size), isChunk s.2[i] = true →
    ex₀.head.isSome = true ∨ ∃ (j : Nat) (hj : j < s.2.size), j < i ∧ isHead s.2[j] = true

/-- The fields an update keeps for every action but `finish true` to stay justified. -/
structure Agree (a b : Exchange) : Prop where
  config : b.config = a.config
  request : b.request = a.request
  headBytes : b.headBytes = a.headBytes
  method : b.method = a.method
  deadline : b.deadline = a.deadline
  now : b.now = a.now
  written : b.written = a.written
  head : b.head = a.head
  sentAny : b.sentAny = a.sentAny
  writeInFlight : b.writeInFlight = a.writeInFlight
  readInFlight : b.readInFlight = a.readInFlight
  early : b.early = a.early
  inputEnded : b.inputEnded = a.inputEnded

/-! ## Basic facts -/

theorem terminal_iff (ex : Exchange) :
    ex.terminal = true ↔ (∃ r, ex.phase = .finished r) ∨ (∃ f, ex.phase = .failed f) := by
  unfold terminal
  split <;> simp_all

theorem actOK_end_terminal {ex : Exchange} {a : ExchangeAction} (h : ActOK ex a)
    (he : isEnd a = true) : ex.terminal = true := by
  cases a <;> simp_all [isEnd, ActOK, terminal_iff]

/-- In a state that has not ended, no ending action has been emitted. -/
theorem Good.noEnd {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (hg : Good ex₀ w r s)
    (ht : s.1.terminal = false) : ∀ a ∈ s.2, isEnd a = false := by
  intro a ha
  cases he : isEnd a
  · rfl
  · have := actOK_end_terminal (hg.acts a ha) he
    simp_all

theorem noReuse_of_noEnd {acts : Array ExchangeAction} (h : ∀ a ∈ acts, isEnd a = false) :
    ∀ a ∈ acts, reuses a = false := by
  intro a ha
  have := h a ha
  cases a <;> simp_all [isEnd, reuses]

theorem endLast_push {acts : Array ExchangeAction} {a : ExchangeAction}
    (h : ∀ b ∈ acts, isEnd b = false) : EndLast (acts.push a) := by
  intro i hi he
  simp only [Array.size_push] at hi ⊢
  by_cases hlt : i < acts.size
  · rw [Array.getElem_push_lt hlt] at he
    have := h _ (Array.getElem_mem hlt)
    simp_all
  · omega

theorem delivery_agree {ex ex' : Exchange} (ha : Agree ex ex') : ex'.delivery = ex.delivery := by
  unfold delivery; rw [ha.head, ha.sentAny]

/-- Actions other than the ending ones stay justified by an update that keeps `Agree`. -/
theorem actOK_keep {ex ex' : Exchange} (ha : Agree ex ex') {a : ExchangeAction}
    (he : isEnd a = false) (h : ActOK ex a) : ActOK ex' a := by
  cases a with
  | write b =>
    simp only [ActOK] at h ⊢; rw [ha.request, ha.written, ha.writeInFlight, ha.sentAny]; exact h
  | read n => simp only [ActOK] at h ⊢; rw [ha.headBytes, ha.written, ha.readInFlight]; exact h
  | deliverHead h' =>
    simp only [ActOK] at h ⊢; rw [ha.head, ha.headBytes, ha.written, ha.early, ha.request]; exact h
  | deliverBody b => simp only [ActOK] at h ⊢; rw [ha.head]; exact h
  | finish r => simp [isEnd] at he
  | fail f => simp [isEnd] at he

/-- So do the ending ones but `finish true`, if the phase is kept. -/
theorem actOK_agree {ex ex' : Exchange} (ha : Agree ex ex') (hp : ex'.phase = ex.phase)
    {a : ExchangeAction} (hr : reuses a = false) (h : ActOK ex a) : ActOK ex' a := by
  cases he : isEnd a
  · exact actOK_keep ha he h
  · cases a with
    | finish r =>
      cases r
      · simp only [ActOK] at h ⊢; rw [hp]; exact ⟨h.1, by simp⟩
      · simp [reuses] at hr
    | fail f =>
      simp only [ActOK] at h ⊢; rw [hp, ha.written, ha.head, delivery_agree ha]; exact h
    | _ => simp [isEnd] at he

theorem terminal_of_phase {ex ex' : Exchange} (hp : ex'.phase = ex.phase) :
    ex'.terminal = ex.terminal := by
  simp [terminal, hp]

theorem inv_agree {ex ex' : Exchange} (ha : Agree ex ex') (hp : ex'.phase = ex.phase) (h : Inv ex) :
    Inv ex' :=
  ⟨by rw [hp, ha.headBytes, ha.written]; exact h.headWritten,
   by rw [hp, ha.head]; exact h.hasHead,
   by rw [ha.written, ha.request]; exact h.writtenLe,
   by rw [ha.written, ha.request, ha.writeInFlight]; exact h.inFlightLe⟩

theorem fixed_agree {ex₀ ex ex' : Exchange} (ha : Agree ex ex') (h : Fixed ex₀ ex) :
    Fixed ex₀ ex' :=
  ⟨by rw [ha.config, h.config], by rw [ha.request, h.request], by rw [ha.headBytes, h.headBytes],
   by rw [ha.method, h.method], by rw [ha.deadline, h.deadline], by rw [ha.now, h.now],
   by rw [ha.written, h.written], by rw [ha.inputEnded, h.inputEnded]⟩

/-- An update that keeps the fields of `Agree` keeps `Good`, unless `finish true` was emitted. -/
theorem Good.agree {ex₀ : Exchange} {w : Option Nat} {r : Bool} {ex ex' : Exchange}
    {acts : Array ExchangeAction} (hg : Good ex₀ w r (ex, acts)) (ha : Agree ex ex')
    (hp : ex'.phase = ex.phase) (hr : ∀ a ∈ acts, reuses a = false) : Good ex₀ w r (ex', acts) where
  fixed := fixed_agree ha hg.fixed
  inv := inv_agree ha hp hg.inv
  acts a h := actOK_agree ha hp (hr a h) (hg.acts a h)
  ends h := hg.ends (by rw [← terminal_of_phase hp]; exact h)
  endLast := hg.endLast
  writes := by rw [ha.writeInFlight]; exact hg.writes
  reads := by rw [ha.readInFlight]; exact hg.reads
  heads := by rw [ha.head, ha.early]; exact hg.heads
  sent := by rw [ha.sentAny]; exact hg.sent
  chunkAfterHead := hg.chunkAfterHead

theorem countP_push_false {p : ExchangeAction → Bool} {acts : Array ExchangeAction}
    {a : ExchangeAction} (h : p a = false) : (acts.push a).countP p = acts.countP p := by
  simp only [Array.countP_push, h, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem exists_of_countP {p : ExchangeAction → Bool} {acts : Array ExchangeAction}
    (h : 0 < acts.countP p) : ∃ (j : Nat) (hj : j < acts.size), p acts[j] = true := by
  obtain ⟨a, ha, hp⟩ := Array.countP_pos_iff.mp h
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp ha
  exact ⟨j, hj, hp⟩

/-- Pushing an action that is not body bytes keeps `chunkAfterHead`. -/
theorem chunkAfterHead_push {ex₀ : Exchange} {acts : Array ExchangeAction} {a : ExchangeAction}
    (h : ∀ (i : Nat) (h : i < acts.size), isChunk acts[i] = true →
      ex₀.head.isSome = true ∨ ∃ (j : Nat) (hj : j < acts.size), j < i ∧ isHead acts[j] = true)
    (ha : isChunk a = true → ex₀.head.isSome = true ∨
      ∃ (j : Nat) (hj : j < acts.size), isHead acts[j] = true) :
    ∀ (i : Nat) (hi : i < (acts.push a).size), isChunk (acts.push a)[i] = true →
      ex₀.head.isSome = true ∨
        ∃ (j : Nat) (hj : j < (acts.push a).size), j < i ∧ isHead (acts.push a)[j] = true := by
  intro i hi hc
  simp only [Array.size_push] at hi
  by_cases hlt : i < acts.size
  · rw [Array.getElem_push_lt hlt] at hc
    rcases h i hlt hc with h | ⟨j, hj, hji, hh⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, by simp; omega, hji, by rw [Array.getElem_push_lt hj]; exact hh⟩
  · have hi' : i = acts.size := by omega
    subst hi'
    rw [Array.getElem_push_eq] at hc
    rcases ha hc with h | ⟨j, hj, hh⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, by simp; omega, hj, by rw [Array.getElem_push_lt hj]; exact hh⟩

/-- Ending the exchange with an action that the new state justifies. -/
theorem Good.finalize {ex₀ : Exchange} {w : Option Nat} {r : Bool} {ex ex' : Exchange}
    {acts : Array ExchangeAction} {a : ExchangeAction} (hg : Good ex₀ w r (ex, acts))
    (ht : ex.terminal = false) (ha : Agree ex ex') (hi : ex'.phase.isActive = false)
    (hb : ex'.phase.isBody = false) (he : isEnd a = true) (hok : ActOK ex' a) :
    Good ex₀ w r (ex', acts.push a) where
  fixed := fixed_agree ha hg.fixed
  inv := ⟨by simp [hi], by simp [hb], by rw [ha.written, ha.request]; exact hg.inv.writtenLe,
    by rw [ha.written, ha.request, ha.writeInFlight]; exact hg.inv.inFlightLe⟩
  acts b h := by
    rcases Array.mem_push.mp h with h | h
    · exact actOK_keep ha (hg.noEnd ht b h) (hg.acts b h)
    · exact h ▸ hok
  ends _ := ⟨a, by simp, he⟩
  endLast := endLast_push (hg.noEnd ht)
  writes := by
    have : isWrite a = false := by cases a <;> simp_all [isEnd, isWrite]
    simp only [Array.countP_push, this, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [ha.writeInFlight]; exact hg.writes
  reads := by
    have : isRead a = false := by cases a <;> simp_all [isEnd, isRead]
    simp only [Array.countP_push, this, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [ha.readInFlight]; exact hg.reads
  heads := by
    have : isHead a = false := by cases a <;> simp_all [isEnd, isHead]
    rw [countP_push_false this, ha.head, ha.early]; exact hg.heads
  sent := by
    have : isWrite a = false := by cases a <;> simp_all [isEnd, isWrite]
    rw [countP_push_false this, ha.sentAny]; exact hg.sent
  chunkAfterHead := chunkAfterHead_push hg.chunkAfterHead (fun h => by
    cases a <;> simp_all [isEnd, isChunk])

/-- Emitting a head or body chunk that the state justifies, before the end. -/
theorem Good.emit {ex₀ : Exchange} {w : Option Nat} {r : Bool} {ex : Exchange}
    {acts : Array ExchangeAction} {a : ExchangeAction} (hg : Good ex₀ w r (ex, acts))
    (ht : ex.terminal = false) (hw : isWrite a = false) (hrd : isRead a = false)
    (_he : isEnd a = false) (hhd : isHead a = false) (hok : ActOK ex a) :
    Good ex₀ w r (ex, acts.push a) where
  fixed := hg.fixed
  inv := hg.inv
  acts b h := by
    rcases Array.mem_push.mp h with h | h
    · exact hg.acts b h
    · exact h ▸ hok
  ends h := by simp_all
  endLast := endLast_push (hg.noEnd ht)
  writes := by
    simp only [Array.countP_push, hw, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact hg.writes
  reads := by
    simp only [Array.countP_push, hrd, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact hg.reads
  heads := by rw [countP_push_false hhd]; exact hg.heads
  sent := by rw [countP_push_false hw]; exact hg.sent
  chunkAfterHead := chunkAfterHead_push hg.chunkAfterHead (fun hc => by
    have hh : ex.head.isSome = true := by cases a <;> simp_all [isChunk, ActOK]
    rcases hg.heads with ⟨_, h, _⟩ | ⟨h, _, _⟩
    · left; simp only at h; rw [← h]; exact hh
    · right; exact exists_of_countP (by simp only at h; omega))

/-! ## The helpers of a step -/

/-- The failure `failNow cause detail` reports in `ex`. -/
def failureOf (ex : Exchange) (cause : Cause) (detail : String) : Failure :=
  { cause, delivery := ex.delivery, written := ex.written, status := ex.head.map (·.status),
    detail :=
      if detail.isEmpty then (ex.writeError.map (s!"a write failed earlier: {·}")).getD "" else detail }

theorem failNow_run (ex : Exchange) (acts : Array ExchangeAction) (c : Cause) (d : String) :
    (failNow c d).run (ex, acts) =
      if ex.terminal then ((), (ex, acts)) else
        ((), ({ ex with phase := .failed (failureOf ex c d), writeBy := none, readBy := none,
                        drainBy := none },
              acts.push (.fail (failureOf ex c d)))) := by
  cases h : ex.terminal <;> simp [failNow, h, failureOf, -StateT.run_bind, -StateT.run_pure]

theorem finishNow_run (ex : Exchange) (acts : Array ExchangeAction) (r : Bool) :
    (finishNow r).run (ex, acts) =
      if ex.terminal then ((), (ex, acts)) else
        ((), ({ ex with phase := .finished (r && ex.reusableNow), writeBy := none, readBy := none,
                        drainBy := none },
              acts.push (.finish (r && ex.reusableNow)))) := by
  cases h : ex.terminal <;> simp [finishNow, h, -StateT.run_bind, -StateT.run_pure]

theorem reusable_of {ex : Exchange} (h : ex.reusableNow = true) (hh : ex.head.isSome = true) :
    Reusable ex := by
  simp only [reusableNow, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, hh⟩

theorem failNow_good {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (c : Cause) (d : String)
    (hg : Good ex₀ w r s) : Good ex₀ w r ((failNow c d).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  rw [failNow_run]
  cases ht : ex.terminal
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine hg.finalize ht ?_ (by simp [Phase.isActive]) (by simp [Phase.isBody]) (by simp [isEnd]) ?_
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, by simp [failureOf, delivery], rfl, rfl⟩
  · simpa using hg

theorem finishNow_good {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (reusable : Bool)
    (hg : Good ex₀ w r s) (hh : reusable = true → s.1.head.isSome = true) :
    Good ex₀ w r ((finishNow reusable).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  rw [finishNow_run]
  cases ht : ex.terminal
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine hg.finalize ht ?_ (by simp [Phase.isActive]) (by simp [Phase.isBody]) (by simp [isEnd]) ?_
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · refine ⟨rfl, fun h => ?_⟩
      simp only [Bool.and_eq_true] at h
      have hr := reusable_of (ex := ex) h.2 (hh h.1)
      exact ⟨hr.keepAlive, hr.codec, hr.delivered, hr.writtenAll, hr.notEarly, hr.noEnd, hr.head⟩
  · simpa using hg

/-- `Good`, inside `absorb`: no `finish true` yet, and past the sending phase. -/
structure GoodA (ex₀ : Exchange) (w : Option Nat) (r : Bool) (s : S) : Prop where
  good : Good ex₀ w r s
  noReuse : ∀ a ∈ s.2, reuses a = false
  notSending : s.1.phase.isSending = false

theorem failNow_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (c : Cause) (d : String)
    (hg : GoodA ex₀ w r s) : GoodA ex₀ w r ((failNow c d).run s).2 := by
  refine ⟨failNow_good c d hg.good, ?_, ?_⟩ <;> obtain ⟨ex, acts⟩ := s <;> rw [failNow_run] <;>
    cases ex.terminal
  · intro a ha
    rcases Array.mem_push.mp ha with h | h
    · exact hg.noReuse a h
    · simp [h, reuses]
  · exact hg.noReuse
  · simp [Phase.isSending]
  · exact hg.notSending

theorem finishNow_false_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (hg : GoodA ex₀ w r s) : GoodA ex₀ w r ((finishNow false).run s).2 := by
  refine ⟨finishNow_good false hg.good (by simp), ?_, ?_⟩ <;> obtain ⟨ex, acts⟩ := s <;>
    rw [finishNow_run] <;> cases ex.terminal
  · intro a ha
    rcases Array.mem_push.mp ha with h | h
    · exact hg.noReuse a h
    · simp [h, reuses]
  · exact hg.noReuse
  · simp [Phase.isSending]
  · exact hg.notSending

theorem failOrDrop_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (c : Cause)
    (d : String) (hg : GoodA ex₀ w r s) : GoodA ex₀ w r ((failOrDrop c d).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [failOrDrop, bind_run, getEx_run]
  split
  · exact finishNow_false_goodA hg
  · exact failNow_goodA c d hg

theorem GoodA.agree {ex₀ : Exchange} {w : Option Nat} {r : Bool} {ex ex' : Exchange}
    {acts : Array ExchangeAction} (hg : GoodA ex₀ w r (ex, acts)) (ha : Agree ex ex')
    (hp : ex'.phase = ex.phase) : GoodA ex₀ w r (ex', acts) :=
  ⟨hg.good.agree ha hp hg.noReuse, hg.noReuse, by rw [hp]; exact hg.notSending⟩

theorem isActive_of {p : Phase} (hs : p.isSending = false) (ht : (∃ r, p = .finished r) ∨
    (∃ f, p = .failed f) → False) : p.isActive = true := by
  cases p <;> simp_all [Phase.isSending, Phase.isActive]

theorem isActive_of_terminal {ex : Exchange} (hs : ex.phase.isSending = false)
    (ht : ex.terminal = false) : ex.phase.isActive = true := by
  apply isActive_of hs
  intro h
  have := (terminal_iff ex).mpr h
  simp_all

theorem GoodA.emit {ex₀ : Exchange} {w : Option Nat} {r : Bool} {ex : Exchange}
    {acts : Array ExchangeAction} {a : ExchangeAction} (hg : GoodA ex₀ w r (ex, acts))
    (ht : ex.terminal = false) (hw : isWrite a = false) (hrd : isRead a = false)
    (he : isEnd a = false) (hhd : isHead a = false) (hok : ActOK ex a) :
    GoodA ex₀ w r (ex, acts.push a) := by
  refine ⟨hg.good.emit ht hw hrd he hhd hok, ?_, hg.notSending⟩
  intro b hb
  rcases Array.mem_push.mp hb with h | h
  · exact hg.noReuse b h
  · subst h; cases b <;> simp_all [isEnd, reuses]

/-- Delivering the final head. -/
theorem deliverHead_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {ex : Exchange}
    {acts : Array ExchangeAction} (hg : GoodA ex₀ w r (ex, acts)) (ht : ex.terminal = false)
    (hh : ex.head.isSome = false) (h : Response.Head) :
    GoodA ex₀ w r
      ({ ex with head := some h, phase := .receiving,
                 early := decide (ex.written < ex.request.size) },
        acts.push (.deliverHead h)) := by
  have hw := hg.good.inv.headWritten (isActive_of_terminal hg.notSending ht)
  have hf := hg.good.fixed
  have hh0 : acts.countP isHead = 0 ∧ ex₀.head = none := by
    rcases hg.good.heads with ⟨h1, h2, _⟩ | ⟨_, _, h3⟩
    · simp only at h1 h2; rw [← h2]; exact ⟨h1, by simpa using hh⟩
    · simp only at h3; simp [h3] at hh
  refine ⟨⟨⟨hf.config, hf.request, hf.headBytes, hf.method, hf.deadline, hf.now, hf.written,
    hf.inputEnded⟩,
    ⟨fun _ => hw, fun _ => rfl, hg.good.inv.writtenLe, hg.good.inv.inFlightLe⟩, ?_, ?_,
    endLast_push (hg.good.noEnd ht), ?_, ?_, ?_, ?_, ?_⟩,
    ?_, rfl⟩
  · intro b hb
    rcases Array.mem_push.mp hb with hb | hb
    · have hok := hg.good.acts b hb
      cases b with
      | write b => exact hok
      | read n => exact hok
      | deliverHead h' => simp [ActOK] at hok; simp [hok.1] at hh
      | deliverBody b => simp [ActOK]
      | finish r => have := hg.good.noEnd ht _ hb; simp [isEnd] at this
      | fail f => have := hg.good.noEnd ht _ hb; simp [isEnd] at this
    · subst hb; exact ⟨rfl, hw, rfl⟩
  · intro h; simp [terminal] at h
  · rw [countP_push_false (by rfl)]; exact hg.good.writes
  · rw [countP_push_false (by rfl)]; exact hg.good.reads
  · right
    simp only [Array.countP_push, isHead, ↓reduceIte, hh0.1]
    exact ⟨by simp, hh0.2, rfl⟩
  · rw [countP_push_false (by rfl)]; exact hg.good.sent
  · exact chunkAfterHead_push hg.good.chunkAfterHead (fun h => by simp [isChunk] at h)
  · intro b hb
    rcases Array.mem_push.mp hb with h | h
    · exact hg.noReuse b h
    · simp [h, reuses]

/-- `Fixed` for an update of other fields. -/
macro "fixed_rfl" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `Agree` for an update of fields outside it. -/
macro "agree_rfl" : tactic =>
  `(tactic| exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- Pushing body bytes, in order, onto the actions of a state with a head keeps `GoodA`. -/
theorem GoodA.emitBodies {ex₀ : Exchange} {w : Option Nat} {r : Bool} {ex : Exchange}
    (ht : ex.terminal = false) (hh : ex.head.isSome = true) :
    ∀ (bs : List ByteArray) {acts : Array ExchangeAction}, GoodA ex₀ w r (ex, acts) →
      GoodA ex₀ w r (ex, bs.foldl (fun a b => a.push (.deliverBody b)) acts)
  | [], _, hg => hg
  | _ :: bs, _, hg => GoodA.emitBodies ht hh bs (hg.emit ht rfl rfl rfl rfl hh)

/--
What `releaseList` does: it delivers a prefix `pre` of the held pieces (all of them, or none), in
order, keeps the rest, and keeps any only when the credit is used up.
-/
theorem releaseList_spec : ∀ (c : Nat) (l : List ByteArray) (acts : Array ExchangeAction),
    ∃ pre, l = pre ++ (releaseList c l acts).2.1 ∧
      (releaseList c l acts).2.2 = pre.foldl (fun a b => a.push (.deliverBody b)) acts ∧
      ((releaseList c l acts).1 = 0 ∨ (releaseList c l acts).2.1 = [])
  | 0, _, _ => ⟨[], rfl, rfl, Or.inl rfl⟩
  | _ + 1, l, _ => ⟨l, by simp [releaseList], rfl, Or.inr rfl⟩

theorem release_run (s : S) :
    release.run s =
      match s.1.phase with
      | .receiving =>
        ((), ({ s.1 with credit := (releaseList s.1.credit s.1.held s.2).1,
                         held := (releaseList s.1.credit s.1.held s.2).2.1 },
              (releaseList s.1.credit s.1.held s.2).2.2))
      | _ => ((), s) := rfl

theorem release_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (hg : GoodA ex₀ w r s) : GoodA ex₀ w r (release.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  rw [release_run]
  split
  · rename_i hp
    have hp' : ex.phase = .receiving := hp
    have ht : ex.terminal = false := by simp [terminal, hp']
    have hh := hg.good.inv.hasHead (by simp [hp', Phase.isBody])
    obtain ⟨pre, _, h2, _⟩ := releaseList_spec ex.credit ex.held acts
    have := GoodA.emitBodies ht hh pre hg
    rw [← h2] at this
    exact this.agree (by agree_rfl) rfl
  · exact hg

theorem onHead_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (h : Codec.Head)
    (hg : GoodA ex₀ w r s) : GoodA ex₀ w r ((onHead h).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [onHead, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true (ex.terminal || ex.head.isSome) with hc | hc <;>
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · exact hg
  · simp only [Bool.or_eq_false_iff] at hc
    simp only [bind_run, setEx_run, emit_run]
    exact deliverHead_goodA hg hc.1 hc.2 h.response

theorem onHead?_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (h : Option Codec.Head)
    (hg : GoodA ex₀ w r s) : GoodA ex₀ w r ((onHead? h).run s).2 := by
  cases h with
  | none => exact hg
  | some h => exact onHead_goodA h hg

theorem onBodies_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (bodies : List ByteArray) (hg : GoodA ex₀ w r s) : GoodA ex₀ w r ((onBodies bodies).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [onBodies, getEx_bind_run]
  split
  · simp only [bind_run, setEx_run]
    have hg' := hg.agree (ex' := { ex with drained := bodies.foldl (· + ·.size) ex.drained })
      (by agree_rfl) rfl
    split
    · exact finishNow_false_goodA hg'
    · exact hg'
  · simp only [bind_run, setEx_run]
    exact release_goodA (hg.agree (by agree_rfl) rfl)

theorem onError?_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (e : Option Codec.Error)
    (hg : GoodA ex₀ w r s) : GoodA ex₀ w r ((onError? e).run s).2 := by
  cases e with
  | none => exact hg
  | some e => exact failOrDrop_goodA _ _ hg

theorem onEvents_goodA {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (events : Array Codec.Event) (hg : GoodA ex₀ w r s) :
    GoodA ex₀ w r ((onEvents events).run s).2 := by
  simp only [onEvents, bind_run]
  exact onError?_goodA _ (onBodies_goodA _ (onHead?_goodA _ hg))

theorem failOrDrop_good {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (c : Cause)
    (d : String) (hg : GoodA ex₀ w r s) : Good ex₀ w r ((failOrDrop c d).run s).2 :=
  (failOrDrop_goodA c d hg).good

theorem settle_good {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (hg : GoodA ex₀ w r s) : Good ex₀ w r (settle.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [settle, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact hg.good
  have hh : ex.phase.isBody = true → ex.head.isSome = true := hg.good.inv.hasHead
  cases hp : ex.phase <;> simp only [hp] at hh ⊢
  case receiving =>
    split
    · exact finishNow_good true hg.good (fun _ => hh rfl)
    · exact hg.good
  case draining =>
    split
    · exact finishNow_good true hg.good (fun _ => hh rfl)
    · split
      · exact finishNow_good false hg.good (by simp)
      · exact hg.good
  all_goals exact hg.good

theorem absorb_good {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (p : Codec.Parser × Array Codec.Event) (hg : GoodA ex₀ w r s) :
    Good ex₀ w r ((absorb p).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [absorb, bind_run, modifyEx_run]
  exact settle_good (onEvents_goodA _ (hg.agree (by agree_rfl) rfl))

/-! ## The parts of a step -/

/-- `Good` at the start of a step, before any action. -/
theorem Good.empty {ex₀ ex : Exchange} (hf : Fixed ex₀ ex) (hi : Inv ex) (ht : ex.terminal = false)
    (hs : ex.sentAny = ex₀.sentAny) (hh : ex.head = ex₀.head) (he : ex.early = ex₀.early) :
    Good ex₀ ex.writeInFlight ex.readInFlight (ex, #[]) where
  fixed := hf
  inv := hi
  acts := by simp
  ends h := by simp_all
  endLast := by intro i h; simp at h
  writes := by simp
  reads := by simp
  heads := by left; simp [hh, he]
  sent := by simp [hs]
  chunkAfterHead := by intro i h; simp at h

theorem fixed_refl (ex : Exchange) : Fixed ex ex := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem failOrDrop_good' {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S} (c : Cause)
    (d : String) (hg : Good ex₀ w r s) : Good ex₀ w r ((failOrDrop c d).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [failOrDrop, bind_run, getEx_run]
  split
  · exact finishNow_good false hg (by simp)
  · exact failNow_good c d hg

/-- `GoodA` at the start of `absorb`, from a state that has not ended and is past sending. -/
theorem GoodA.empty {ex₀ ex : Exchange} {w : Option Nat} {r : Bool} (hg : Good ex₀ w r (ex, #[]))
    (hs : ex.phase.isSending = false) : GoodA ex₀ w r (ex, #[]) :=
  ⟨hg, by simp, hs⟩

theorem stopUpload_good {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (hg : Good ex₀ w r s) (ht : s.1.terminal = false) : Good ex₀ w r (stopUpload.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [stopUpload, modifyEx_run]
  exact hg.agree (by agree_rfl) rfl (noReuse_of_noEnd (hg.noEnd ht))

theorem expireOne_good {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (hg : Good ex₀ w r s) : Good ex₀ w r (expireOne.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [expireOne, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact hg
  split
  · split
    · simp only [bind_run]; exact finishNow_good false hg (by simp)
    · exact hg
  · split
    · exact hg
    · split
      · simp only [bind_run]; exact stopUpload_good hg ht
      · simp only [bind_run]; exact failNow_good _ _ hg
    · simp only [bind_run]; exact failNow_good _ _ hg

theorem expire_good {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (hg : Good ex₀ w r s) : Good ex₀ w r (expire.run s).2 := by
  simp only [expire, bind_run]
  have h1 := expireOne_good hg
  generalize expireOne.run s = x at h1 ⊢
  obtain ⟨b, x⟩ := x
  cases b
  · exact h1
  · simp only [↓reduceIte]
    exact expireOne_good h1

theorem slice_ok (req : ByteArray) (written chunk : Nat) (h : written < req.size) :
    let stop := min req.size (written + max 1 chunk)
    let slice := if written == 0 && stop == req.size then req else req.extract written stop
    0 < slice.size ∧ slice = req.extract written (written + slice.size) ∧
      slice.size = stop - written := by
  intro stop slice
  have hstop : stop ≤ req.size := Nat.min_le_left _ _
  have hlt : written < stop := by
    simp only [stop]; have := Nat.le_max_left 1 chunk; omega
  have hsz : slice.size = stop - written := by
    simp only [slice]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      omega
    · rw [ByteArray.size_extract]; omega
  refine ⟨by omega, ?_, hsz⟩
  rw [hsz, show written + (stop - written) = stop by omega]
  simp only [slice]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.1, hc.2, ByteArray.extract_zero_size]
  · rfl

theorem wantsInput_active {ex : Exchange} (h : ex.wantsInput = true) : ex.phase.isActive = true := by
  unfold wantsInput at h
  split at h <;> simp_all [Phase.isActive]

theorem schedule_good {ex₀ : Exchange} {w : Option Nat} {r : Bool} {s : S}
    (hg : Good ex₀ w r s) : Good ex₀ w r (schedule.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [schedule, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact hg
  have hne := hg.noEnd ht
  -- After the write, if any: still `Good`, not terminal.
  have hw : ∀ s' : S, Good ex₀ w r s' → s'.1.terminal = false →
      Good ex₀ w r ((do
        let ex ← getEx
        if !ex.readInFlight && ex.wantsInput then
          let readBy := if ex.uploadOver then some (ex.now + ex.config.gapMs) else none
          setEx { ex with readInFlight := true, readBy }
          emit (.read ex.config.readChunk) : StepM Unit).run s').2 := by
    intro ⟨ex', acts'⟩ hg' ht'
    simp only [getEx_bind_run]
    rcases Bool.eq_false_or_eq_true (!ex'.readInFlight && ex'.wantsInput) with hc | hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run, emit_run]
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      obtain ⟨hrf, hwi⟩ := hc
      have hhb := hg'.inv.headWritten (wantsInput_active hwi)
      have hne' := hg'.noEnd ht'
      have hnr : acts'.countP isRead = 0 := by
        rcases hg'.reads with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exfalso
          have h' : acts'.countP isRead = 1 := h
          obtain ⟨a, ha, hra⟩ := Array.countP_pos_iff.mp (by omega : 0 < acts'.countP isRead)
          cases a <;> simp [isRead] at hra
          exact absurd ((hg'.acts _ ha).2) (by simp [hrf])
      have hr0 : r = false := by
        rcases hg'.reads with ⟨_, h⟩ | ⟨_, h⟩
        · rw [← h]; exact hrf
        · exact h
      refine ⟨⟨hg'.fixed.config, hg'.fixed.request, hg'.fixed.headBytes, hg'.fixed.method,
        hg'.fixed.deadline, hg'.fixed.now, hg'.fixed.written, hg'.fixed.inputEnded⟩,
        ⟨hg'.inv.headWritten, hg'.inv.hasHead, hg'.inv.writtenLe, hg'.inv.inFlightLe⟩,
        ?_, ?_, endLast_push hne', ?_, ?_, ?_, ?_, ?_⟩
      · intro b hb
        rcases Array.mem_push.mp hb with hb | hb
        · have hok := hg'.acts b hb
          cases b with
          | read n =>
            exfalso
            have := Array.countP_eq_zero.mp hnr _ hb
            simp [isRead] at this
          | finish _ => have := hne' _ hb; simp [isEnd] at this
          | fail _ => have := hne' _ hb; simp [isEnd] at this
          | _ => exact hok
        · subst hb; exact ⟨hhb, rfl⟩
      · intro h; simp only [terminal] at h ht'; simp_all
      · rw [countP_push_false (by rfl)]; exact hg'.writes
      · right; simp [Array.countP_push, isRead, hnr, hr0]
      · rw [countP_push_false (by rfl)]; exact hg'.heads
      · rw [countP_push_false (by rfl)]; exact hg'.sent
      · exact chunkAfterHead_push hg'.chunkAfterHead (fun h => by simp [isChunk] at h)
    · exact hg'
  rcases Bool.eq_false_or_eq_true
      (!ex.uploadStopped && ex.writeInFlight.isNone && decide (ex.written < ex.request.size)) with
    hc | hc <;> simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Option.isNone_iff_eq_none,
      decide_eq_true_eq] at hc
    obtain ⟨⟨_, hwf⟩, hlt⟩ := hc
    obtain ⟨hpos, heq, hsz⟩ := slice_ok ex.request ex.written ex.config.writeChunk hlt
    have hnw : acts.countP isWrite = 0 := by
      rcases hg.writes with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exfalso
        have h' : acts.countP isWrite = 1 := h
        obtain ⟨a, ha, hwa⟩ := Array.countP_pos_iff.mp (by omega : 0 < acts.countP isWrite)
        cases a <;> simp [isWrite] at hwa
        exact absurd ((hg.acts _ ha).2.2.1) (by simp [hwf])
    have hw0 : w = none := by
      rcases hg.writes with ⟨_, h⟩ | ⟨_, h⟩
      · rw [← h]; exact hwf
      · exact h
    let stop := min ex.request.size (ex.written + max 1 ex.config.writeChunk)
    let slice := if ex.written == 0 && stop == ex.request.size then ex.request
      else ex.request.extract ex.written stop
    let ex' : Exchange := { ex with
      writeInFlight := some (stop - ex.written), writeBy := some (ex.now + ex.config.gapMs),
      sentAny := true }
    have key : Good ex₀ w r (ex', acts.push (.write slice)) := by
      refine ⟨⟨hg.fixed.config, hg.fixed.request, hg.fixed.headBytes, hg.fixed.method,
          hg.fixed.deadline, hg.fixed.now, hg.fixed.written, hg.fixed.inputEnded⟩,
          ⟨hg.inv.headWritten, hg.inv.hasHead, hg.inv.writtenLe, fun k hk => by
            simp only [ex', Option.some.injEq] at hk
            subst hk
            have h1 : ex.written ≤ stop := Nat.le_of_lt (Nat.lt_of_sub_pos (hsz ▸ hpos))
            have h2 : stop ≤ ex.request.size := Nat.min_le_left _ _
            show ex.written + (stop - ex.written) ≤ ex.request.size
            rw [Nat.add_sub_cancel' h1]; exact h2⟩,
          ?_, ?_, endLast_push hne, ?_, ?_, ?_, ?_, ?_⟩
      · intro b hb
        rcases Array.mem_push.mp hb with hb | hb
        · have hok := hg.acts b hb
          cases b with
          | write b' =>
            exfalso
            have := Array.countP_eq_zero.mp hnw _ hb
            simp [isWrite] at this
          | finish _ => have := hne _ hb; simp [isEnd] at this
          | fail _ => have := hne _ hb; simp [isEnd] at this
          | _ => exact hok
        · subst hb
          exact ⟨hpos, heq, by simp only [ex']; rw [hsz], rfl⟩
      · intro h; simp only [terminal, ex'] at h ht; simp_all
      · right; simp [Array.countP_push, isWrite, hnw, hw0]
      · rw [countP_push_false (by rfl)]; exact hg.reads
      · rw [countP_push_false (by rfl)]; exact hg.heads
      · simp [ex', Array.countP_push, isWrite]
      · exact chunkAfterHead_push hg.chunkAfterHead (fun h => by simp [isChunk] at h)
    exact hw _ key (by simp only [terminal] at ht ⊢; exact ht)
  · exact hw _ hg ht
/-- The write in flight once `e` was taken into account. -/
def wAfter (ex : Exchange) : ExchangeEvent → Option Nat
  | .written _ | .writeFailed _ => none
  | _ => ex.writeInFlight

/-- Whether a read is in flight once `e` was taken into account. -/
def rAfter (ex : Exchange) : ExchangeEvent → Bool
  | .received b => b.isEmpty && ex.readInFlight
  | .endOfInput | .readFailed _ => false
  | _ => ex.readInFlight

theorem isSending_false_of {p : Phase} (h : p = .sending → False) : p.isSending = false := by
  cases p <;> simp_all [Phase.isSending]

/-- `Good.empty` for an update of `ex₀` that keeps the fixed fields. -/
theorem Good.start {ex₀ ex' : Exchange} (hf : Fixed ex₀ ex') (hi : Inv ex')
    (ht : ex'.terminal = false) (hs : ex'.sentAny = ex₀.sentAny) (hh : ex'.head = ex₀.head)
    (he : ex'.early = ex₀.early) {w : Option Nat} {r : Bool} (hw : ex'.writeInFlight = w)
    (hr : ex'.readInFlight = r) : Good ex₀ w r (ex', #[]) := hw ▸ hr ▸ Good.empty hf hi ht hs hh he

/-- The state after a write completed. -/
theorem writtenLeaf {ex₀ ex ex' : Exchange} (hi : Inv ex) (ht : ex.terminal = false)
    (hfix : Fixed ex₀ ex') (hs : ex'.sentAny = ex₀.sentAny) (hh : ex'.head = ex₀.head)
    (he : ex'.early = ex₀.early) (hw : ex'.writeInFlight = none)
    (hsz : ex'.written ≤ ex'.request.size) (hr : ex'.readInFlight = ex.readInFlight)
    (hhead : ex'.head = ex.head) (hwr : ex.written ≤ ex'.written) (hhb : ex'.headBytes = ex.headBytes)
    (hph : ex'.phase = ex.phase ∨ (ex'.phase = .awaitingHead ∧ ex'.headBytes ≤ ex'.written)) :
    Good ex₀ none ex.readInFlight (ex', #[]) := by
  apply Good.start hfix _ _ hs hh he hw hr
  · refine ⟨?_, ?_, hsz, fun k hk => by rw [hw] at hk; cases hk⟩
    · intro ha
      rcases hph with h | ⟨_, h⟩
      · rw [h] at ha; have := hi.headWritten ha; omega
      · exact h
    · intro hb
      rcases hph with h | ⟨h, _⟩
      · rw [h] at hb; rw [hhead]; exact hi.hasHead hb
      · simp [h, Phase.isBody] at hb
  · rcases hph with h | ⟨h, _⟩
    · rw [terminal_of_phase h]; exact ht
    · simp [terminal, h]

/-- The state a step's handler starts from, once a completed write is counted. -/
def startOf (ex : Exchange) : ExchangeEvent → Exchange
  | .written n =>
    match ex.writeInFlight with
    | some len => { ex with written := ex.written + min n len }
    | none => ex
  | .endOfInput => { ex with inputEnded := true }
  | _ => ex

theorem handle_good (e : ExchangeEvent) {ex : Exchange} (hi : Inv ex) (ht : ex.terminal = false) :
    Good (startOf ex e) (wAfter ex e) (rAfter ex e) ((handle e).run (ex, #[])).2 := by
  have hf := fixed_refl ex
  cases e with
  | received bytes =>
    simp only [handle, wAfter, rAfter, startOf]
    rcases Bool.eq_false_or_eq_true bytes.isEmpty with hb | hb <;>
      simp only [hb, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.false_eq_true]
    · exact Good.start (ex₀ := ex) (ex' := ex) hf hi ht rfl rfl rfl rfl rfl
    simp only [getEx_bind_run]
    simp only [bind_run, setEx_run]
    have hg := Good.start (ex₀ := ex) (ex' := { ex with readInFlight := false, readBy := none })
      (w := ex.writeInFlight) (r := false) (by fixed_rfl) ⟨hi.headWritten, hi.hasHead, hi.writtenLe, hi.inFlightLe⟩ ht rfl rfl rfl rfl rfl
    split
    · exact failNow_good _ _ hg
    · rename_i hp
      split
      · exact hg
      · exact absorb_good _ (GoodA.empty hg (isSending_false_of hp))
  | endOfInput =>
    simp only [handle, wAfter, rAfter, startOf]
    simp only [getEx_bind_run]
    simp only [bind_run, setEx_run]
    have hg := Good.start (ex₀ := { ex with inputEnded := true })
      (ex' := { ex with readInFlight := false, readBy := none, inputEnded := true })
      (w := ex.writeInFlight) (r := false) (by fixed_rfl) ⟨hi.headWritten, hi.hasHead, hi.writtenLe, hi.inFlightLe⟩ ht rfl rfl rfl rfl rfl
    split
    · exact hg
    · split
      · exact failNow_good _ _ hg
      · rename_i hp
        exact absorb_good _ (GoodA.empty hg (isSending_false_of hp))
  | written count =>
    simp only [handle, wAfter, rAfter, startOf]
    simp only [getEx_bind_run]
    cases hl : ex.writeInFlight with
    | none => exact Good.start (ex₀ := ex) (ex' := ex) hf hi ht rfl rfl rfl hl rfl
    | some len =>
      simp only [setEx_run]
      have hle : ex.written ≤ ex.written + min count len := Nat.le_add_right _ _
      have hsz : ex.written + min count len ≤ ex.request.size := by
        have := hi.inFlightLe len hl
        have := Nat.min_le_right count len
        omega
      cases hp : ex.phase <;> simp only
      case sending =>
        by_cases hd : ex.written + min count len ≥ ex.headBytes <;> simp only [hd, ↓reduceIte]
        · split
          · exact writtenLeaf hi ht (by fixed_rfl) rfl rfl rfl rfl hsz rfl rfl hle rfl (Or.inr ⟨rfl, hd⟩)
          · exact writtenLeaf hi ht (by fixed_rfl) rfl rfl rfl rfl hsz rfl rfl hle rfl (Or.inr ⟨rfl, hd⟩)
        · split
          · exact writtenLeaf hi ht (by fixed_rfl) rfl rfl rfl rfl hsz rfl rfl hle rfl (Or.inl (by simp [hp]))
          · exact writtenLeaf hi ht (by fixed_rfl) rfl rfl rfl rfl hsz rfl rfl hle rfl (Or.inl (by simp [hp]))
      all_goals
        split
        · exact writtenLeaf hi ht (by fixed_rfl) rfl rfl rfl rfl hsz rfl rfl hle rfl (Or.inl (by simp [hp]))
        · exact writtenLeaf hi ht (by fixed_rfl) rfl rfl rfl rfl hsz rfl rfl hle rfl (Or.inl (by simp [hp]))
  | writeFailed detail =>
    simp only [handle, wAfter, rAfter, startOf]
    simp only [getEx_bind_run]
    rcases Bool.eq_false_or_eq_true ex.writeInFlight.isNone with hn | hn <;>
      simp only [hn, ↓reduceIte, Bool.false_eq_true]
    · exact Good.start (ex₀ := ex) (ex' := ex) hf hi ht rfl rfl rfl (by simpa using hn) rfl
    · simp only [bind_run, setEx_run]
      have hg := Good.start (ex₀ := ex) (ex' := { ex with writeInFlight := none, writeBy := none })
        (w := none) (r := ex.readInFlight) (by fixed_rfl)
        ⟨hi.headWritten, hi.hasHead, hi.writtenLe, fun _ hk => by cases hk⟩ ht rfl rfl rfl rfl rfl
      split
      · exact failNow_good _ _ hg
      · rcases Bool.eq_false_or_eq_true ex.uploadStopped with hu | hu <;>
          simp only [hu, ↓reduceIte, Bool.false_eq_true, bind_run, getEx_run, setEx_run]
        · exact hg.agree (by agree_rfl) rfl (by simp)
        · exact stopUpload_good (hg.agree (by agree_rfl) rfl (by simp)) ht
  | readFailed detail =>
    simp only [handle, wAfter, rAfter, startOf, bind_run, modifyEx_run]
    exact failOrDrop_good' _ _ (Good.start (ex₀ := ex)
      (ex' := { ex with readInFlight := false, readBy := none }) (w := ex.writeInFlight) (r := false)
      (by fixed_rfl) ⟨hi.headWritten, hi.hasHead, hi.writtenLe, hi.inFlightLe⟩ ht rfl rfl rfl rfl rfl)
  | wantBody bytes =>
    simp only [handle, wAfter, rAfter, startOf]
    simp only [getEx_bind_run]
    simp only [bind_run, setEx_run]
    have hg := Good.start (ex₀ := ex) (ex' := { ex with credit := ex.credit + bytes })
      (w := ex.writeInFlight) (r := ex.readInFlight) (by fixed_rfl) ⟨hi.headWritten, hi.hasHead, hi.writtenLe, hi.inFlightLe⟩ ht
      rfl rfl rfl rfl rfl
    split
    · rename_i hp
      simp only [↓reduceIte, bind_run]
      exact settle_good (release_goodA (GoodA.empty hg (by simp [hp, Phase.isSending])))
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hg
  | tick =>
    simp only [handle, wAfter, rAfter, startOf]
    exact Good.start (ex₀ := ex) (ex' := ex) hf hi ht rfl rfl rfl rfl rfl
  | abandon =>
    simp only [handle, wAfter, rAfter, startOf]
    simp only [bind_run, setEx_run]
    have hg := Good.start (ex₀ := ex) (ex' := { ex with abandoned := true })
      (w := ex.writeInFlight) (r := ex.readInFlight) (by fixed_rfl)
      ⟨hi.headWritten, hi.hasHead, hi.writtenLe, hi.inFlightLe⟩ ht rfl rfl rfl rfl rfl
    split
    · exact failNow_good _ _ hg
    · exact failNow_good _ _ hg
    · rename_i hp
      have hp' : ex.phase = .receiving := hp
      split
      · simp only [bind_run, setEx_run]
        have hact := hi.headWritten (by simp [hp', Phase.isActive])
        have hhd := hi.hasHead (by simp [hp', Phase.isBody])
        exact settle_good (GoodA.empty (Good.start (ex₀ := ex)
          (ex' := { ex with abandoned := true, phase := .draining, held := [],
                            drained := ex.held.foldl (· + ·.size) 0,
                            drainBy := some (ex.now + ex.config.drainMs) })
          (w := ex.writeInFlight) (r := ex.readInFlight)
          (by fixed_rfl) ⟨fun _ => hact, fun _ => hhd, hi.writtenLe, hi.inFlightLe⟩ (by simp [terminal])
          rfl rfl rfl rfl rfl)
          (by simp [Phase.isSending]))
      · exact finishNow_good false hg (by simp)
    · exact hg

theorem expire_terminal {s : S} (h : s.1.terminal = true) : (expire.run s).2 = s := by
  obtain ⟨ex, acts⟩ := s
  simp only [expire, bind_run, expireOne]
  simp only at h
  simp [h]
  rfl

theorem schedule_terminal {s : S} (h : s.1.terminal = true) : (schedule.run s).2 = s := by
  obtain ⟨ex, acts⟩ := s
  simp only [schedule, getEx_bind_run]
  simp only at h
  simp [h]
  rfl

/-! ## Whole steps -/

/-- The exchange a step works on: the time advanced, nothing else changed. -/
abbrev advanced (ex : Exchange) (now : Timestamp) : Exchange := { ex with now := max ex.now now }

/-- `true` when `step` ignores `e` at `now`: a tick, or an empty read, before the next deadline. -/
def stale (ex : Exchange) (now : Timestamp) (e : ExchangeEvent) : Bool :=
  match e, ex.nextDeadline with
  | .tick, some due => decide (now < due)
  | .received bytes, some due => bytes.isEmpty && decide (now < due)
  | _, _ => false

theorem step_def (ex : Exchange) (now : Timestamp) (e : ExchangeEvent) :
    ex.step now e =
      if (ex.terminal || stale ex now e) = true then (ex, #[]) else
        ((do handle e; expire; schedule : StepM Unit).run (advanced ex now, #[])).2 := by
  rfl

theorem step_ignored {ex : Exchange} {now : Timestamp} {e : ExchangeEvent}
    (h : (ex.terminal || stale ex now e) = true) : ex.step now e = (ex, #[]) := by
  rw [step_def]; simp [h]

theorem step_run {ex : Exchange} {now : Timestamp} {e : ExchangeEvent}
    (h : (ex.terminal || stale ex now e) = false) :
    ex.step now e = ((do handle e; expire; schedule : StepM Unit).run (advanced ex now, #[])).2 := by
  rw [step_def]; simp [h]

theorem not_terminal_of {ex : Exchange} {now : Timestamp} {e : ExchangeEvent}
    (h : (ex.terminal || stale ex now e) = false) : ex.terminal = false := by
  simp only [Bool.or_eq_false_iff] at h; exact h.1

/-- `Good` holds at the end of every step that does not ignore its event. -/
theorem step_good {ex : Exchange} (hi : Inv ex) {now : Timestamp} {e : ExchangeEvent}
    (h : (ex.terminal || stale ex now e) = false) :
    Good (startOf (advanced ex now) e) (wAfter (advanced ex now) e) (rAfter (advanced ex now) e)
      (ex.step now e) := by
  rw [step_run h]
  simp only [bind_run]
  apply schedule_good
  apply expire_good
  exact handle_good e ⟨hi.headWritten, hi.hasHead, hi.writtenLe, hi.inFlightLe⟩ (not_terminal_of h)

/-- The exchange `begin` starts from. -/
def initial (req : PreparedRequest) (now deadline : Timestamp) : Exchange :=
  { config := req.config, parser := Codec.Parser.start req.config.codec req.method,
    method := req.method, request := req.bytes,
    headBytes := req.headBytes, deadline, now }

theorem begin_def (req : PreparedRequest) (now deadline : Timestamp) :
    begin req now deadline = ((do expire; schedule : StepM Unit).run (initial req now deadline, #[])).2 :=
  rfl

/-- `Good` holds at the end of `begin`. -/
theorem begin_good (req : PreparedRequest) (now deadline : Timestamp) :
    Good (initial req now deadline) none false (begin req now deadline) := by
  rw [begin_def]
  simp only [bind_run]
  apply schedule_good
  apply expire_good
  exact Good.start (fixed_refl _) ⟨by simp [initial, Phase.isActive], by simp [initial, Phase.isBody],
    Nat.zero_le _, by simp [initial]⟩
    (by simp [initial, terminal]) rfl rfl rfl rfl rfl

/-- The exchanges a run can reach: `begin`, then any sequence of steps, at any times. -/
inductive Reachable : Exchange → Prop where
  /-- The start. -/
  | begin (req : PreparedRequest) (now deadline : Timestamp) :
      Reachable (Exchange.begin req now deadline).1
  /-- One more step. -/
  | step {ex : Exchange} (now : Timestamp) (e : ExchangeEvent) :
      Reachable ex → Reachable (ex.step now e).1

/-- Every reachable exchange satisfies `Inv`. -/
theorem Reachable.inv {ex : Exchange} (h : Reachable ex) : Inv ex := by
  induction h with
  | begin req now deadline => exact (begin_good req now deadline).inv
  | @step ex now e _ ih =>
    cases hc : (ex.terminal || stale ex now e)
    · exact (step_good ih hc).inv
    · rw [step_ignored hc]; exact ih

theorem startOf_head (ex : Exchange) (e : ExchangeEvent) : (startOf ex e).head = ex.head := by
  cases e <;> simp only [startOf] <;> split <;> rfl

theorem startOf_sentAny (ex : Exchange) (e : ExchangeEvent) :
    (startOf ex e).sentAny = ex.sentAny := by
  cases e <;> simp only [startOf] <;> split <;> rfl

theorem wAfter_advanced (ex : Exchange) (now : Timestamp) (e : ExchangeEvent) :
    wAfter (advanced ex now) e = wAfter ex e := by
  cases e <;> rfl

theorem rAfter_advanced (ex : Exchange) (now : Timestamp) (e : ExchangeEvent) :
    rAfter (advanced ex now) e = rAfter ex e := by
  cases e <;> rfl

/-- What a step does: ignore its event, or end in a state where `Good` holds. -/
theorem step_cases (ex : Exchange) (now : Timestamp) (e : ExchangeEvent) :
    ((ex.terminal || stale ex now e) = true ∧ ex.step now e = (ex, #[])) ∨
      ((ex.terminal || stale ex now e) = false ∧ (Inv ex →
        Good (startOf (advanced ex now) e) (wAfter ex e) (rAfter ex e) (ex.step now e))) := by
  cases hc : (ex.terminal || stale ex now e)
  · right
    refine ⟨rfl, fun hi => ?_⟩
    rw [← wAfter_advanced ex now, ← rAfter_advanced ex now]
    exact step_good hi hc
  · exact Or.inl ⟨rfl, step_ignored hc⟩

/-! ## The properties the checker asserts at every step -/

/--
**Nothing after the end** (checker: "nothing after the end").  An exchange that has finished or
failed ignores every event: it stays as it is and emits nothing.
-/
theorem step_of_terminal {ex : Exchange} (h : ex.terminal = true) (now : Timestamp)
    (e : ExchangeEvent) : ex.step now e = (ex, #[]) :=
  step_ignored (by simp [h])

/--
**A stale tick changes nothing** (checker: "a stale tick changes nothing").  A tick earlier than
`nextDeadline` returns the exchange unchanged, with no actions.
-/
theorem step_stale_tick {ex : Exchange} {now due : Timestamp} (hd : ex.nextDeadline = some due)
    (hlt : now < due) : ex.step now .tick = (ex, #[]) :=
  step_ignored (by simp [stale, hd, hlt])

/--
**An empty read is a tick** (checker: "an empty read is a tick").  A read reported with no bytes
does exactly what a tick at the same time does: it completes no read, so the read stays in flight
and its read gap keeps running.  Before the next deadline it changes nothing (`step_stale_tick`).
-/
theorem step_empty_received {ex : Exchange} (now : Timestamp) {bytes : ByteArray}
    (hb : bytes.isEmpty = true) : ex.step now (.received bytes) = ex.step now .tick := by
  rw [step_def, step_def]
  have hs : stale ex now (.received bytes) = stale ex now .tick := by
    simp only [stale]; split <;> simp_all
  have hh : handle (.received bytes) = handle .tick := by simp [handle, hb]
  rw [hs, hh]

/--
**No head before the request head is written, and only one** (checker: "no head before the request
head is written", "one head").  When a step delivers a final head, the request head (`headBytes`
bytes, as `prepare` measured it) has been written, no head had been delivered before, the step
delivers no other, and the exchange records whether the head came before the rest of the request was
written (`early`, which reuse depends on).
-/
theorem step_deliverHead {ex : Exchange} (hi : Inv ex) {now : Timestamp} {e : ExchangeEvent}
    {h : Response.Head} (hm : .deliverHead h ∈ (ex.step now e).2) :
    let ex' := (ex.step now e).1
    ex'.headBytes ≤ ex'.written ∧ ex.head = none ∧ (ex.step now e).2.countP isHead = 1 ∧
      ex'.head = some h ∧ ex'.early = decide (ex'.written < ex'.request.size) := by
  intro ex'
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨_, hg⟩
  · rw [hs] at hm; simp at hm
  · have g := hg hi
    obtain ⟨h1, h2, h3⟩ := g.acts _ hm
    have hpos : 0 < (ex.step now e).2.countP isHead :=
      Array.countP_pos_iff.mpr ⟨_, hm, rfl⟩
    rcases g.heads with ⟨h4, _, _⟩ | ⟨h4, h5, _⟩
    · omega
    · rw [startOf_head] at h5
      exact ⟨h2, h5, h4, h1, h3⟩

/--
**Reusable only when safe** (checker: "reusable only when safe"), on the core's side.  A step
reports the connection reusable only when keep-alive was asked for; the parser says the connection
could carry another exchange (`Codec.Parser.reusable`: the response ended, framed with certainty,
with nothing after it and before the end of input, and its keep-alive verdict allowed it); the caller
received the whole body; the whole request was written, and not after the final head arrived
(`early` is false; `observed_finish_reusable` ties this to the bytes written when the head was
delivered); the peer did not close; and a final head was delivered.
-/
theorem step_finish_reusable {ex : Exchange} (hi : Inv ex) {now : Timestamp} {e : ExchangeEvent}
    (hm : .finish true ∈ (ex.step now e).2) :
    (ex.step now e).1.phase = .finished true ∧ Reusable (ex.step now e).1 := by
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨_, hg⟩
  · rw [hs] at hm; simp at hm
  · obtain ⟨h1, h2⟩ := (hg hi).acts _ hm
    exact ⟨h1, h2 rfl⟩

/--
**A failure says how far the request got** (checker: "delivery follows what was written", "a failure
counts the bytes written", "a failure carries the status of the delivered head").  A failure reported
by a step carries the delivery, the count of written request bytes and the status of the final head
of the exchange it ends.  `Exchange.delivery` is `notSent` exactly when
no write was ever issued and no head delivered, `responseReceived` exactly when a final head was
delivered, and `maybeDelivered` otherwise (`delivery_iff`); `Observed.agrees` shows that `sentAny`
and `head` record whether the run emitted a write and a final head, and `observed_fail` states the
property in the checker's terms.
-/
theorem step_fail {ex : Exchange} (hi : Inv ex) {now : Timestamp} {e : ExchangeEvent} {f : Failure}
    (hm : .fail f ∈ (ex.step now e).2) :
    let ex' := (ex.step now e).1
    ex'.phase = .failed f ∧ f.delivery = ex'.delivery ∧ f.written = ex'.written ∧
      f.status = ex'.head.map (·.status) := by
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨_, hg⟩
  · rw [hs] at hm; simp at hm
  · exact (hg hi).acts _ hm

/-- What `Exchange.delivery` says, case by case. -/
theorem delivery_iff (ex : Exchange) :
    (ex.delivery = .notSent ↔ ex.head = none ∧ ex.sentAny = false) ∧
      (ex.delivery = .maybeDelivered ↔ ex.head = none ∧ ex.sentAny = true) ∧
      (ex.delivery = .responseReceived ↔ ex.head.isSome = true) := by
  unfold delivery
  cases ex.head <;> cases ex.sentAny <;> simp

/--
**One end, last, and only with an action** (checker: "one end, last", "the core ends only with an
action").  A step from an exchange that has not ended ends it exactly when it emits `finish` or
`fail`, and that action is its last.
-/
theorem step_ends {ex : Exchange} (hi : Inv ex) (ht : ex.terminal = false) (now : Timestamp)
    (e : ExchangeEvent) :
    ((ex.step now e).1.terminal = true ↔ ∃ a ∈ (ex.step now e).2, isEnd a = true) ∧
      EndLast (ex.step now e).2 := by
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨_, hg⟩
  · rw [hs]; simp [ht, EndLast]
  · have g := hg hi
    exact ⟨⟨g.ends, fun ⟨a, ha, he⟩ => actOK_end_terminal (g.acts a ha) he⟩, g.endLast⟩

/--
**One write in flight, and writes follow the request** (checker: "one write in flight", "writes
follow the request").  A step emits at most one write, only when no write is in flight once its
event is taken into account (`wAfter`: a reported completion or failure ends the write in flight),
and that write is the next non-empty slice of the request after the bytes written; the exchange then
records it as in flight, and that some write was issued.  Otherwise the write in flight is as the
event left it.
-/
theorem step_writes {ex : Exchange} (hi : Inv ex) (ht : ex.terminal = false) (now : Timestamp)
    (e : ExchangeEvent) :
    let ex' := (ex.step now e).1
    let acts := (ex.step now e).2
    (acts.countP isWrite = 0 ∧ ex'.writeInFlight = wAfter ex e ∧ ex'.sentAny = ex.sentAny) ∨
      (acts.countP isWrite = 1 ∧ wAfter ex e = none ∧ ex'.sentAny = true ∧
        ∀ b, .write b ∈ acts →
          0 < b.size ∧ b = ex'.request.extract ex'.written (ex'.written + b.size) ∧
            ex'.writeInFlight = some b.size) := by
  intro ex' acts
  rcases step_cases ex now e with ⟨hc, hs⟩ | ⟨_, hg⟩
  · left
    simp only [ex', acts, hs, Array.countP_empty, true_and]
    simp only [ht, Bool.false_or, stale] at hc
    cases e <;> simp_all [wAfter]
  · have g := hg hi
    have hsent := g.sent
    rw [startOf_sentAny] at hsent
    rcases g.writes with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, h2, by simp only [ex', hsent, h1]; simp⟩
    · right
      refine ⟨h1, h2, by simp only [ex', hsent, h1]; simp, fun b hb => ?_⟩
      obtain ⟨h3, h4, h5, _⟩ := g.acts _ hb
      exact ⟨h3, h4, h5⟩

/--
**One read in flight, none before the request head is written** (checker: "one read in flight", "no
read before the request head is written").  A step emits at most one read, only when no read is in
flight once its event is taken into account (`rAfter`), and only once the request head (`headBytes`
bytes) has been written.
-/
theorem step_reads {ex : Exchange} (hi : Inv ex) (ht : ex.terminal = false) (now : Timestamp)
    (e : ExchangeEvent) :
    let ex' := (ex.step now e).1
    let acts := (ex.step now e).2
    (acts.countP isRead = 0 ∧ ex'.readInFlight = rAfter ex e) ∨
      (acts.countP isRead = 1 ∧ rAfter ex e = false ∧ ex'.readInFlight = true ∧
        ∀ n, .read n ∈ acts → ex'.headBytes ≤ ex'.written) := by
  intro ex' acts
  rcases step_cases ex now e with ⟨hc, hs⟩ | ⟨_, hg⟩
  · left
    simp only [ex', acts, hs, Array.countP_empty, true_and]
    simp only [ht, Bool.false_or, stale] at hc
    cases e <;> (cases hnd : ex.nextDeadline <;> simp only [hnd] at hc) <;> simp_all [rAfter]
  · have g := hg hi
    rcases g.reads with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · right
      obtain ⟨j, hj, hr⟩ := exists_of_countP (p := isRead) (acts := (ex.step now e).2) (by omega)
      have hok := g.acts _ (Array.getElem_mem hj)
      revert hok hr
      cases acts[j] <;> simp [isRead, ActOK]
      intro hb hrf
      exact ⟨h1, h2, hrf, fun n hn => (g.acts _ hn).1⟩

/--
**No body before the head** (checker: "no body before the head").  Every body chunk a step delivers
comes after a final head: one delivered by an earlier step, or one earlier in the same step's actions.
-/
theorem step_chunk_after_head {ex : Exchange} (hi : Inv ex) (now : Timestamp) (e : ExchangeEvent) :
    let acts := (ex.step now e).2
    ∀ (i : Nat) (h : i < acts.size), isChunk acts[i] = true →
      ex.head.isSome = true ∨ ∃ (j : Nat) (hj : j < acts.size), j < i ∧ isHead acts[j] = true := by
  intro acts
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨_, hg⟩
  · intro i h; simp [acts, hs] at h
  · have := (hg hi).chunkAfterHead
    rw [startOf_head] at this
    exact this

/--
**Bytes before the request head fail the exchange** (checker: "unsolicited bytes fail the exchange",
and with `step_of_terminal`, "unsolicited bytes never make a response").  Bytes (at least one)
reported while fewer than `headBytes` request bytes have been written end the exchange with that
failure and nothing else; they are not handed to the parser, and the exchange emits nothing more.
-/
theorem step_unsolicited {ex : Exchange} (hi : Inv ex) (ht : ex.terminal = false)
    (hw : ex.written < ex.headBytes) (now : Timestamp) (bytes : ByteArray)
    (hb : bytes.isEmpty = false) :
    ∃ f, (ex.step now (.received bytes)).2 = #[.fail f] ∧
      f.cause = .protocol "bytes arrived before the request head was written" := by
  have hs : ex.phase = .sending := by
    cases hp : ex.phase
    case sending => rfl
    case finished => simp [terminal, hp] at ht
    case failed => simp [terminal, hp] at ht
    all_goals
      have := hi.headWritten (by simp [hp, Phase.isActive])
      omega
  have hc : (ex.terminal || stale ex now (.received bytes)) = false := by
    cases hnd : ex.nextDeadline <;> simp [ht, stale, hb, hnd]
  rw [step_run hc]
  simp only [bind_run]
  let ex1 : Exchange := { ex with now := max ex.now now, readInFlight := false, readBy := none }
  let f := failureOf ex1 (.protocol "bytes arrived before the request head was written") ""
  have hh : ((handle (.received bytes)).run (advanced ex now, #[])).2 =
      ({ ex1 with phase := .failed f, writeBy := none, readBy := none, drainBy := none },
        #[.fail f]) := by
    simp only [handle, hb, Bool.false_eq_true, ↓reduceIte]
    simp only [getEx_bind_run]
    simp only [bind_run, setEx_run]
    split
    · rw [failNow_run]
      simp only [terminal, hs, Bool.false_eq_true, ↓reduceIte]
      rfl
    · rename_i hp; exact absurd hs hp
  rw [hh, expire_terminal, schedule_terminal]
  · exact ⟨f, rfl, rfl⟩
  all_goals simp [terminal]

/-! ## Runs -/

/-- `true` for the events that end the write in flight. -/
def clearsWrite : ExchangeEvent → Bool
  | .written _ | .writeFailed _ => true
  | _ => false

/-- `true` for the events that end the read in flight. -/
def clearsRead : ExchangeEvent → Bool
  | .received b => !b.isEmpty
  | .endOfInput | .readFailed _ => true
  | _ => false

theorem wAfter_eq (ex : Exchange) (e : ExchangeEvent) :
    wAfter ex e = if clearsWrite e then none else ex.writeInFlight := by
  cases e <;> rfl

theorem rAfter_eq (ex : Exchange) (e : ExchangeEvent) :
    rAfter ex e = if clearsRead e then false else ex.readInFlight := by
  cases e <;> try rfl
  rename_i b
  cases h : b.isEmpty <;> simp [rAfter, clearsRead, h]

/--
A run as the shell sees it: the exchange, the writes it was asked for whose outcome it has not yet
reported, and the same for reads.  As in the checker's model, a reported completion or failure ends
the write (or read) in flight, if there is one (an empty read is no completion), and nothing changes
once the exchange has ended.
-/
inductive Run : Exchange → Nat → Nat → Prop where
  /-- The start. -/
  | begin (req : PreparedRequest) (now deadline : Timestamp) :
      Run (Exchange.begin req now deadline).1 ((Exchange.begin req now deadline).2.countP isWrite)
        ((Exchange.begin req now deadline).2.countP isRead)
  /-- One more step. -/
  | step {ex : Exchange} {w r : Nat} (now : Timestamp) (e : ExchangeEvent) : Run ex w r →
      Run (ex.step now e).1
        ((if ex.terminal || !clearsWrite e then w else 0) + (ex.step now e).2.countP isWrite)
        ((if ex.terminal || !clearsRead e then r else 0) + (ex.step now e).2.countP isRead)

theorem Run.reachable {ex : Exchange} {w r : Nat} (h : Run ex w r) : Reachable ex := by
  induction h with
  | begin req now deadline => exact .begin req now deadline
  | step now e _ ih => exact .step now e ih

/--
**At most one write and one read in flight** (checker: "one write in flight", "one read in flight",
over whole runs).  In every run, the writes the shell was asked for and has not reported on number
the same as the core's write in flight, so at most one, and likewise for reads.
-/
theorem Run.inFlight {ex : Exchange} {w r : Nat} (h : Run ex w r) :
    w = (if ex.writeInFlight.isSome then 1 else 0) ∧ r = (if ex.readInFlight then 1 else 0) := by
  induction h with
  | begin req now deadline =>
    have g := begin_good req now deadline
    constructor
    · rcases g.writes with ⟨h1, h2⟩ | ⟨h1, _⟩
      · rw [h1, h2]; rfl
      · obtain ⟨j, hj, hw⟩ := exists_of_countP (p := isWrite)
          (acts := (Exchange.begin req now deadline).2) (by omega)
        have hok := g.acts _ (Array.getElem_mem hj)
        revert hok hw
        cases (Exchange.begin req now deadline).2[j] <;> simp [isWrite, ActOK]
        intro _ _ h3 _; rw [h1, h3]; rfl
    · rcases g.reads with ⟨h1, h2⟩ | ⟨h1, _⟩
      · rw [h1, h2]; rfl
      · obtain ⟨j, hj, hr⟩ := exists_of_countP (p := isRead)
          (acts := (Exchange.begin req now deadline).2) (by omega)
        have hok := g.acts _ (Array.getElem_mem hj)
        revert hok hr
        cases (Exchange.begin req now deadline).2[j] <;> simp [isRead, ActOK]
        intro _ h3; rw [h1, h3]; rfl
  | @step ex w r now e hrun ih =>
    have hi := hrun.reachable.inv
    rcases ih with ⟨ihw, ihr⟩
    cases ht : ex.terminal
    · have hw := step_writes hi ht now e
      have hr := step_reads hi ht now e
      simp only [Bool.false_or]
      constructor
      · rw [wAfter_eq] at hw
        rcases hw with ⟨h1, h2, _⟩ | ⟨h1, h2, _, h4⟩
        · rw [h1, h2]; cases clearsWrite e <;> simp [ihw]
        · obtain ⟨j, hj, hwj⟩ := exists_of_countP (p := isWrite) (acts := (ex.step now e).2) (by omega)
          revert hwj
          have hmem := Array.getElem_mem hj
          revert hmem
          cases (ex.step now e).2[j] <;> simp [isWrite]
          intro hb
          rw [(h4 _ hb).2.2, h1]
          cases hc : clearsWrite e <;> simp [hc] at h2 ⊢ <;> simp [ihw, h2]
      · rw [rAfter_eq] at hr
        rcases hr with ⟨h1, h2⟩ | ⟨h1, h2, h3, _⟩
        · rw [h1, h2]; cases clearsRead e <;> simp [ihr]
        · rw [h1, h3]
          cases hc : clearsRead e <;> simp [hc] at h2 ⊢ <;> simp [ihr, h2]
    · rw [step_of_terminal ht]
      simp [ihw, ihr]

/-! ## Deadlines -/

/-- A fold that picks one element of a list: it ends with an element of the list or its start. -/
theorem foldl_pick {α : Type} (f : Option α → α → Option α) (h1 : ∀ c, f none c = some c)
    (h2 : ∀ b c, f (some b) c = some c ∨ f (some b) c = some b) :
    ∀ (l : List α) (o : Option α), (l ≠ [] ∨ o.isSome = true) →
      ∃ c, l.foldl f o = some c ∧ (o = some c ∨ c ∈ l) := by
  intro l
  induction l with
  | nil =>
    intro o h
    simp only [ne_eq, not_true_eq_false, false_or] at h
    obtain ⟨c, rfl⟩ := Option.isSome_iff_exists.mp h
    exact ⟨c, rfl, Or.inl rfl⟩
  | cons a l ih =>
    intro o _
    have hsome : ∃ c', f o a = some c' ∧ (c' = a ∨ o = some c') := by
      cases o with
      | none => exact ⟨a, h1 a, Or.inl rfl⟩
      | some b =>
        rcases h2 b a with h | h
        · exact ⟨a, h, Or.inl rfl⟩
        · exact ⟨b, h, Or.inr rfl⟩
    obtain ⟨c', hc', hc'o⟩ := hsome
    obtain ⟨c, hc, hco⟩ := ih (f o a) (Or.inr (by simp [hc']))
    refine ⟨c, by simpa using hc, ?_⟩
    rcases hco with h | h
    · rw [hc'] at h
      cases h
      rcases hc'o with h | h
      · exact Or.inr (by simp [h])
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The fold of `expireOne` picks one of the deadlines that passed... -/
theorem first_mem {l : List (Timestamp × Nat × TimeoutKind)} {c : Timestamp × Nat × TimeoutKind}
    (h : l.foldl (init := none) (fun best c =>
      match best with
      | none => some c
      | some b => if c.1 < b.1 || (c.1 == b.1 && c.2.1 < b.2.1) then some c else some b) = some c) :
    c ∈ l := by
  cases l with
  | nil => simp at h
  | cons a l =>
    obtain ⟨c', h', hm⟩ := foldl_pick (fun (best : Option (Timestamp × Nat × TimeoutKind)) c =>
        match best with
        | none => some c
        | some b => if c.1 < b.1 || (c.1 == b.1 && c.2.1 < b.2.1) then some c else some b)
      (fun _ => rfl) (fun b c => by simp only; split <;> simp) (a :: l) none (Or.inl (by simp))
    rw [h] at h'
    cases h'
    rcases hm with h | h
    · cases h
    · exact h

/-- ...and picks one if any passed. -/
theorem first_ne_none {l : List (Timestamp × Nat × TimeoutKind)} (hne : l ≠ [])
    (h : l.foldl (init := none) (fun best c =>
      match best with
      | none => some c
      | some b => if c.1 < b.1 || (c.1 == b.1 && c.2.1 < b.2.1) then some c else some b) = none) :
    False := by
  obtain ⟨c', h', _⟩ := foldl_pick (fun (best : Option (Timestamp × Nat × TimeoutKind)) c =>
      match best with
      | none => some c
      | some b => if c.1 < b.1 || (c.1 == b.1 && c.2.1 < b.2.1) then some c else some b)
    (fun _ => rfl) (fun b c => by simp only; split <;> simp) l none (Or.inl hne)
  rw [h] at h'
  cases h'

/-- With the deadline passed, one round of `expireOne` ends the exchange, or stops the upload. -/
theorem expireOne_deadline {ex : Exchange} {acts : Array ExchangeAction} (ht : ex.terminal = false)
    (hd : ex.deadline ≤ ex.now) :
    let r := expireOne.run (ex, acts)
    r.2.1.terminal = true ∨
      (r.1 = true ∧ r.2.1.writeBy = none ∧ r.2.1.deadline = ex.deadline ∧ r.2.1.now = ex.now ∧
        ex.writeBy.isSome = true) := by
  intro r
  simp only [r, expireOne, getEx_bind_run, ht, Bool.false_eq_true, ↓reduceIte]
  split
  · have hc : (decide (ex.now ≥ ex.deadline) || ex.drainBy.any (ex.now ≥ ·) ||
        ex.readBy.any (ex.now ≥ ·)) = true := by simp [hd]
    left
    simp only [hc, ↓reduceIte, bind_run, finishNow_run, ht, Bool.false_eq_true]
    rfl
  · have hne : ∀ l : List (Timestamp × Nat × TimeoutKind),
        List.filter (fun x => decide (x.fst ≤ ex.now))
          ([(ex.deadline, 0, TimeoutKind.deadline)] ++ l) ≠ [] := by
      intro l; simp [hd]
    split
    · rename_i heq
      exact absurd (first_ne_none (hne _) heq) id
    · rename_i t k heq
      have hm := first_mem heq
      have hwb : ex.writeBy.isSome = true := by
        cases hw : ex.writeBy <;> simp [hw] at hm ⊢
      split
      · right
        simp only [bind_run, stopUpload, modifyEx_run]
        exact ⟨rfl, rfl, rfl, rfl, hwb⟩
      · left
        simp only [bind_run, failNow_run, ht, Bool.false_eq_true, ↓reduceIte]
        rfl
    · left
      simp only [bind_run, failNow_run, ht, Bool.false_eq_true, ↓reduceIte]
      rfl

theorem expireOne_terminal {s : S} (h : s.1.terminal = true) : expireOne.run s = (false, s) := by
  obtain ⟨ex, acts⟩ := s
  simp only at h
  simp only [expireOne, getEx_bind_run, h, ↓reduceIte]
  rfl

theorem discard_run {α : Type} (m : StepM α) (s : S) :
    (discard m : StepM PUnit).run s = (PUnit.unit, (m.run s).2) := rfl

/-- With the deadline passed, `expire` ends the exchange. -/
theorem expire_deadline {ex : Exchange} {acts : Array ExchangeAction} (ht : ex.terminal = false)
    (hd : ex.deadline ≤ ex.now) : (expire.run (ex, acts)).2.1.terminal = true := by
  simp only [expire, bind_run]
  have h1 := expireOne_deadline (acts := acts) ht hd
  generalize expireOne.run (ex, acts) = x at h1 ⊢
  obtain ⟨b, ex', acts'⟩ := x
  simp only at h1 ⊢
  cases b
  · rcases h1 with h | ⟨h, _⟩
    · exact h
    · cases h
  · simp only [↓reduceIte]
    cases ht' : ex'.terminal
    · rcases h1 with h | ⟨_, hw, hdl, hn, _⟩
      · rw [h] at ht'; cases ht'
      · rcases expireOne_deadline (acts := acts') ht' (by rw [hdl, hn]; exact hd) with h | ⟨_, _, _, _, h⟩
        · exact h
        · rw [hw] at h; cases h
    · rw [discard_run, expireOne_terminal (s := (ex', acts')) ht']
      exact ht'

theorem foldl_min_le (l : List Nat) (a : Nat) : l.foldl min a ≤ a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl a
  | cons b l ih => exact Nat.le_trans (ih (min a b)) (Nat.min_le_left a b)

theorem nextDeadline_le {ex : Exchange} {due : Timestamp} (h : ex.nextDeadline = some due) :
    due ≤ ex.deadline := by
  unfold nextDeadline at h
  split at h
  · cases h
  · cases h; exact foldl_min_le _ _

/-- The state after a step's handler: `Good`, with the time and the deadline of the step. -/
theorem handle_state {ex : Exchange} (hi : Inv ex) {now : Timestamp} {e : ExchangeEvent}
    (h : (ex.terminal || stale ex now e) = false) :
    let s1 := ((handle e).run (advanced ex now, #[])).2
    s1.1.now = max ex.now now ∧ s1.1.deadline = ex.deadline := by
  intro s1
  have g := handle_good e (ex := advanced ex now) ⟨hi.headWritten, hi.hasHead, hi.writtenLe, hi.inFlightLe⟩ (not_terminal_of h)
  have hf := g.fixed
  refine ⟨?_, ?_⟩
  · rw [hf.now]; cases e <;> simp only [startOf] <;> (try split) <;> rfl
  · rw [hf.deadline]; cases e <;> simp only [startOf] <;> (try split) <;> rfl

/-- After a step that does not ignore its event, the exchange has ended if the deadline passed. -/
theorem step_deadline_aux {ex : Exchange} (hi : Inv ex) {now : Timestamp} {e : ExchangeEvent}
    (h : (ex.terminal || stale ex now e) = false) (hd : ex.deadline ≤ max ex.now now) :
    (ex.step now e).1.terminal = true := by
  rw [step_run h]
  simp only [bind_run]
  obtain ⟨hn, hdl⟩ := handle_state hi h
  generalize ((handle e).run (advanced ex now, #[])).2 = s1 at hn hdl ⊢
  obtain ⟨ex1, acts1⟩ := s1
  simp only at hn hdl
  cases ht1 : ex1.terminal
  · have := expire_deadline (acts := acts1) ht1 (by rw [hn, hdl]; exact hd)
    rw [schedule_terminal this]
    exact this
  · rw [expire_terminal (s := (ex1, acts1)) ht1, schedule_terminal (s := (ex1, acts1)) ht1]
    exact ht1

/-- A reachable exchange that has not ended is before its deadline. -/
theorem Reachable.beforeDeadline {ex : Exchange} (h : Reachable ex) (ht : ex.terminal = false) :
    ex.now < ex.deadline := by
  induction h with
  | begin req now deadline =>
    have hf := (begin_good req now deadline).fixed
    rw [hf.now, hf.deadline]
    simp only [initial]
    apply Nat.lt_of_not_le
    intro hd
    revert ht
    rw [begin_def]
    simp only [bind_run]
    have := expire_deadline (acts := #[]) (ex := initial req now deadline) (by simp [initial, terminal])
      hd
    rw [schedule_terminal this, this]
    simp
  | @step ex now e hr ih =>
    rcases step_cases ex now e with ⟨_, hs⟩ | ⟨hc, hg⟩
    · rw [hs] at ht ⊢; exact ih ht
    · have g := hg hr.inv
      rw [g.fixed.now, g.fixed.deadline]
      have h1 : (startOf (advanced ex now) e).now = max ex.now now := by
        cases e <;> simp only [startOf] <;> (try split) <;> rfl
      have h2 : (startOf (advanced ex now) e).deadline = ex.deadline := by
        cases e <;> simp only [startOf] <;> (try split) <;> rfl
      rw [h1, h2]
      apply Nat.lt_of_not_le
      intro hd
      have := step_deadline_aux hr.inv hc hd
      rw [this] at ht
      cases ht

/--
**After the deadline the exchange has ended** (checker: "after the deadline the exchange has ended").
In every run, a step at a time at or past the exchange's deadline (counting the latest time the
core was told of) leaves the exchange finished or failed.
-/
theorem step_deadline {ex : Exchange} (hr : Reachable ex) {now : Timestamp} {e : ExchangeEvent}
    (hd : ex.deadline ≤ max ex.now now) : (ex.step now e).1.terminal = true := by
  rcases step_cases ex now e with ⟨hc, hs⟩ | ⟨hc, _⟩
  · rw [hs]
    cases ht : ex.terminal
    · exfalso
      simp only [ht, Bool.false_or, stale] at hc
      have hb := hr.beforeDeadline ht
      split at hc
      · rename_i due hn
        have := nextDeadline_le hn
        simp only [decide_eq_true_eq] at hc
        exact absurd hd (Nat.not_le.mpr (Nat.max_lt.mpr ⟨hb, Nat.lt_of_lt_of_le hc this⟩))
      · rename_i b due hn
        have := nextDeadline_le hn
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact absurd hd (Nat.not_le.mpr (Nat.max_lt.mpr ⟨hb, Nat.lt_of_lt_of_le hc.2 this⟩))
      · cases hc
    · rfl
  · exact step_deadline_aux hr.inv hc hd

/-! ## The run as the checker's model sees it -/

/--
What the checker's model knows of a run, built from the events reported and the actions emitted
only (the fields of `Model` in `Tests/Support/Check.lean` that the properties below use).
-/
structure Obs where
  /-- Request bytes whose write completed. -/
  acked : Nat := 0
  /-- The length of the write in flight. -/
  outstanding : Option Nat := none
  /-- Whether any write was issued. -/
  everWrote : Bool := false
  /-- Whether the final head was delivered. -/
  headDelivered : Bool := false
  /-- Whether `finish` or `fail` was emitted. -/
  ended : Bool := false
  /-- `acked` when the head was delivered. -/
  ackedAtHead : Nat := 0
  /-- Whether end of input was reported. -/
  eofSeen : Bool := false
  /-- The time of the latest step. -/
  now : Nat := 0

/-- The model's update for an event, as `Model.observe`. -/
def Obs.observe (m : Obs) (e : ExchangeEvent) : Obs :=
  if m.ended then m else
  match e with
  | .written n =>
    match m.outstanding with
    | some len => { m with acked := m.acked + min n len, outstanding := none }
    | none => m
  | .writeFailed _ => { m with outstanding := none }
  | .endOfInput => { m with eofSeen := true }
  | _ => m

/-- The model's update for an action, as in `checkStep`. -/
def Obs.see (m : Obs) : ExchangeAction → Obs
  | .write b => { m with outstanding := some b.size, everWrote := true }
  | .deliverHead _ => { m with headDelivered := true, ackedAtHead := m.acked }
  | .finish _ | .fail _ => { m with ended := true }
  | _ => m

/-- A run with the checker's model of it. -/
inductive Observed : Exchange → Obs → Prop where
  /-- The start. -/
  | begin (req : PreparedRequest) (now deadline : Timestamp) :
      Observed (Exchange.begin req now deadline).1
        ((Exchange.begin req now deadline).2.foldl Obs.see { now })
  /-- One more step. -/
  | step {ex : Exchange} {m : Obs} (now : Timestamp) (e : ExchangeEvent) : Observed ex m →
      Observed (ex.step now e).1
        ((ex.step now e).2.foldl Obs.see { m.observe e with now := max m.now now })

theorem Observed.reachable {ex : Exchange} {m : Obs} (h : Observed ex m) : Reachable ex := by
  induction h with
  | begin req now deadline => exact .begin req now deadline
  | step now e _ ih => exact .step now e ih

theorem see_acked (l : List ExchangeAction) (m : Obs) : (l.foldl Obs.see m).acked = m.acked := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih]; cases a <;> rfl

theorem see_everWrote (l : List ExchangeAction) (m : Obs) :
    (l.foldl Obs.see m).everWrote = (m.everWrote || l.any isWrite) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih]; cases a <;> simp [Obs.see, isWrite]

theorem see_headDelivered (l : List ExchangeAction) (m : Obs) :
    (l.foldl Obs.see m).headDelivered = (m.headDelivered || l.any isHead) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih]; cases a <;> simp [Obs.see, isHead]

theorem see_ended (l : List ExchangeAction) (m : Obs) :
    (l.foldl Obs.see m).ended = (m.ended || l.any isEnd) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih]; cases a <;> simp [Obs.see, isEnd]

theorem see_outstanding_none (l : List ExchangeAction) (m : Obs) (h : l.countP isWrite = 0) :
    (l.foldl Obs.see m).outstanding = m.outstanding := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    · cases a <;> simp_all [Obs.see, isWrite, List.countP_cons]
    · cases a <;> simp_all [isWrite, List.countP_cons]

theorem see_outstanding_some (l : List ExchangeAction) (m : Obs) (h : l.countP isWrite = 1)
    {b : ByteArray} (hb : .write b ∈ l) : (l.foldl Obs.see m).outstanding = some b.size := by
  induction l generalizing m with
  | nil => simp at hb
  | cons a l ih =>
    rw [List.foldl_cons]
    cases a with
    | write b' =>
      simp only [List.countP_cons, isWrite, ↓reduceIte] at h
      have h0 : l.countP isWrite = 0 := by omega
      rw [see_outstanding_none l _ h0]
      rcases List.mem_cons.mp hb with hb | hb
      · cases hb; rfl
      · exfalso
        have := List.countP_eq_zero.mp h0 _ hb
        simp [isWrite] at this
    | _ =>
      simp only [List.countP_cons, isWrite, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
      exact ih _ h (by simpa using hb)

theorem see_eofSeen (l : List ExchangeAction) (m : Obs) : (l.foldl Obs.see m).eofSeen = m.eofSeen := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih]; cases a <;> rfl

theorem see_now (l : List ExchangeAction) (m : Obs) : (l.foldl Obs.see m).now = m.now := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih]; cases a <;> rfl

theorem see_ackedAtHead_none (l : List ExchangeAction) (m : Obs) (h : l.countP isHead = 0) :
    (l.foldl Obs.see m).ackedAtHead = m.ackedAtHead := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    · cases a <;> simp_all [Obs.see, isHead, List.countP_cons]
    · cases a <;> simp_all [isHead, List.countP_cons]

theorem see_ackedAtHead_one (l : List ExchangeAction) (m : Obs) (h : l.countP isHead = 1) :
    (l.foldl Obs.see m).ackedAtHead = m.acked := by
  induction l generalizing m with
  | nil => simp at h
  | cons a l ih =>
    rw [List.foldl_cons]
    cases a with
    | deliverHead h' =>
      simp only [List.countP_cons, isHead, ↓reduceIte] at h
      rw [see_ackedAtHead_none l _ (by omega)]
      rfl
    | _ =>
      simp only [List.countP_cons, isHead, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
      exact ih _ h

/-- The model and the core agree, at every point of every run. -/
structure Agrees (ex : Exchange) (m : Obs) : Prop where
  acked : m.acked = ex.written
  outstanding : m.outstanding = ex.writeInFlight
  everWrote : m.everWrote = ex.sentAny
  headDelivered : m.headDelivered = ex.head.isSome
  ended : m.ended = ex.terminal
  early : m.headDelivered = true →
    ex.early = decide (m.ackedAtHead < ex.request.size) ∧ m.ackedAtHead ≤ ex.request.size
  eofSeen : m.eofSeen = ex.inputEnded

theorem any_eq_countP (acts : Array ExchangeAction) (p : ExchangeAction → Bool) :
    acts.any p = decide (0 < acts.countP p) := by
  rw [← Array.any_toList, ← Array.countP_toList]
  cases h : acts.toList.any p
  · simp only [List.any_eq_false] at h
    have : acts.toList.countP p = 0 := List.countP_eq_zero.mpr (by simpa using h)
    simp [this]
  · obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
    have : 0 < acts.toList.countP p := List.countP_pos_iff.mpr ⟨a, ha, hp⟩
    rw [Array.countP_toList] at this
    simp [this]

/-- From a model that agrees with where a step started, the model agrees with where it ended. -/
theorem Good.agrees {ex₀ : Exchange} {w : Option Nat} {r : Bool} {ex : Exchange}
    {acts : Array ExchangeAction} (g : Good ex₀ w r (ex, acts)) {m : Obs}
    (ha : m.acked = ex₀.written) (ho : m.outstanding = w) (hw : m.everWrote = ex₀.sentAny)
    (hh : m.headDelivered = ex₀.head.isSome) (he : m.ended = false)
    (hea : m.headDelivered = true →
      ex₀.early = decide (m.ackedAtHead < ex₀.request.size) ∧ m.ackedAtHead ≤ ex₀.request.size)
    (heo : m.eofSeen = ex₀.inputEnded) :
    Agrees ex (acts.foldl Obs.see m) := by
  rw [← Array.foldl_toList]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [see_acked, ha, g.fixed.written]
  · rcases g.writes with ⟨h1, h2⟩ | ⟨h1, _⟩
    · rw [see_outstanding_none _ _ (by rw [Array.countP_toList]; exact h1), ho, ← h2]
    · obtain ⟨j, hj, hwj⟩ := exists_of_countP (p := isWrite) (acts := acts) (by simp only at h1; omega)
      have hmem := Array.getElem_mem hj
      generalize acts[j] = a at hwj hmem
      cases a with
      | write b =>
        obtain ⟨_, _, h3, _⟩ := g.acts _ hmem
        rw [see_outstanding_some _ _ (by rw [Array.countP_toList]; exact h1)
          (Array.mem_toList_iff.mpr hmem), h3]
      | _ => simp [isWrite] at hwj
  · rw [see_everWrote, hw, g.sent, Array.any_toList, any_eq_countP]
  · rw [see_headDelivered, hh, Array.any_toList, any_eq_countP]
    rcases g.heads with ⟨h1, h2, _⟩ | ⟨h1, h2, h3⟩
    · simp only at h1 h2; simp [h1, h2]
    · simp only at h1 h3; simp [h1, h2, h3]
  · rw [see_ended, he]
    simp only [Bool.false_or]
    cases ht : ex.terminal
    · rw [List.any_eq_false]
      intro a ha
      have := g.noEnd ht _ (Array.mem_toList_iff.mp ha)
      simp [this]
    · obtain ⟨a, ha, hae⟩ := g.ends ht
      exact List.any_eq_true.mpr ⟨a, Array.mem_toList_iff.mpr ha, hae⟩
  · rw [see_headDelivered, Array.any_toList, any_eq_countP]
    intro hd
    rcases g.heads with ⟨h1, _, h3⟩ | ⟨h1, _, _⟩
    · simp only at h1 h3
      rw [see_ackedAtHead_none _ _ (by rw [Array.countP_toList]; exact h1), h3, g.fixed.request]
      simp only [h1] at hd
      exact hea (by simpa using hd)
    · simp only at h1
      rw [see_ackedAtHead_one _ _ (by rw [Array.countP_toList]; exact h1), ha, ← g.fixed.written]
      obtain ⟨j, hj, hhj⟩ := exists_of_countP (p := isHead) (acts := acts) (by omega)
      have hmem := Array.getElem_mem hj
      generalize acts[j] = a at hhj hmem
      cases a with
      | deliverHead h => exact ⟨(g.acts _ hmem).2.2, g.inv.writtenLe⟩
      | _ => simp [isHead] at hhj
  · rw [see_eofSeen, heo, g.fixed.inputEnded]

/-- The checker's model agrees with the core at every point of every run. -/
theorem Observed.agrees {ex : Exchange} {m : Obs} (h : Observed ex m) : Agrees ex m := by
  induction h with
  | begin req now deadline =>
    exact (begin_good req now deadline).agrees rfl rfl rfl rfl rfl (fun h => by simp at h) rfl
  | @step ex m now e hob ih =>
    obtain ⟨ia, io, iw, ihd, ie, iea, ieo⟩ := ih
    rcases step_cases ex now e with ⟨hc, hs⟩ | ⟨hc, hg⟩
    · rw [hs]
      have hobs : m.observe e = m := by
        cases ht : ex.terminal
        · simp only [ht, Bool.false_or, stale] at hc
          cases e <;> first
            | (simp only [Obs.observe, ie, ht]; done)
            | (simp only [Obs.observe, ie, ht]; rfl)
            | (exfalso; revert hc; simp)
        · simp only [Obs.observe, ie, ht, ↓reduceIte]
      simp only [hobs, Array.foldl_empty]
      exact ⟨ia, io, iw, ihd, ie, iea, ieo⟩
    · have g := hg hob.reachable.inv
      have ht := not_terminal_of hc
      have hne : m.ended = false := by rw [ie, ht]
      apply g.agrees
      · simp only [Obs.observe, hne]
        cases e <;> simp only [startOf, Bool.false_eq_true, ↓reduceIte] <;> try exact ia
        rw [io]
        split <;> simp_all
      · simp only [Obs.observe, hne, wAfter]
        cases e <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> try exact io
        rw [io]
        split <;> simp_all
      · simp only [Obs.observe, hne, startOf_sentAny]
        cases e <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> try exact iw
        split <;> exact iw
      · simp only [Obs.observe, hne, startOf_head]
        cases e <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> try exact ihd
        split <;> exact ihd
      · simp only [Obs.observe, hne]
        cases e <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> try exact hne
        split <;> first | exact hne | rfl
      · simp only [Obs.observe, hne]
        cases e <;> simp only [startOf, Bool.false_eq_true, ↓reduceIte] <;> try exact iea
        rw [io]
        split <;> exact iea
      · simp only [Obs.observe, hne]
        cases e <;> simp only [startOf, Bool.false_eq_true, ↓reduceIte] <;> try exact ieo
        rw [io]
        split <;> exact ieo

/-- The model's clock: never behind the core's, and past the deadline only once the exchange ended. -/
theorem Observed.clock {ex : Exchange} {m : Obs} (h : Observed ex m) :
    ex.now ≤ m.now ∧ (ex.deadline ≤ m.now → ex.terminal = true) := by
  induction h with
  | begin req now deadline =>
    have hf := (begin_good req now deadline).fixed
    rw [← Array.foldl_toList, see_now, hf.now]
    simp only [initial]
    refine ⟨Nat.le_refl _, fun hd => ?_⟩
    cases ht : (Exchange.begin req now deadline).1.terminal
    · have := (Reachable.begin req now deadline).beforeDeadline ht
      rw [hf.now, hf.deadline] at this
      rw [hf.deadline] at hd
      simp only [initial] at this hd
      exact absurd hd (Nat.not_le.mpr this)
    · rfl
  | @step ex m now e hob ih =>
    obtain ⟨ihn, ihl⟩ := ih
    rw [← Array.foldl_toList, see_now]
    simp only
    rcases step_cases ex now e with ⟨hc, hs⟩ | ⟨hc, hg⟩
    · rw [hs]
      refine ⟨Nat.le_trans ihn (Nat.le_max_left _ _), fun hd => ?_⟩
      simp only at hd
      cases ht : ex.terminal
      · exfalso
        simp only [ht, Bool.false_or, stale] at hc
        have hb := hob.reachable.beforeDeadline ht
        split at hc
        · rename_i due hn
          have := nextDeadline_le hn
          simp only [decide_eq_true_eq] at hc
          have h1 : ¬ ex.deadline ≤ m.now := fun h2 => by rw [ihl h2] at ht; cases ht
          have h3 : now < ex.deadline := Nat.lt_of_lt_of_le hc this
          exact absurd hd (Nat.not_le.mpr (Nat.max_lt.mpr ⟨Nat.lt_of_not_le h1, h3⟩))
        · rename_i b due hn
          have := nextDeadline_le hn
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          have h1 : ¬ ex.deadline ≤ m.now := fun h2 => by rw [ihl h2] at ht; cases ht
          have h3 : now < ex.deadline := Nat.lt_of_lt_of_le hc.2 this
          exact absurd hd (Nat.not_le.mpr (Nat.max_lt.mpr ⟨Nat.lt_of_not_le h1, h3⟩))
        · cases hc
      · rfl
    · have g := hg hob.reachable.inv
      have hn : (ex.step now e).1.now = max ex.now now := by
        rw [g.fixed.now]; cases e <;> simp only [startOf] <;> (try split) <;> rfl
      refine ⟨?_, fun hd => ?_⟩
      · rw [hn]; exact Nat.max_le.mpr ⟨Nat.le_trans ihn (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
      · have hdl : (ex.step now e).1.deadline = ex.deadline := by
          rw [g.fixed.deadline]; cases e <;> simp only [startOf] <;> (try split) <;> rfl
        rw [hdl] at hd
        by_cases h1 : ex.deadline ≤ m.now
        · have := ihl h1
          simp only [this, Bool.true_or] at hc
          cases hc
        · have h2 : ex.deadline ≤ now := by
            rcases Nat.le_total m.now now with h3 | h3
            · rw [Nat.max_eq_right h3] at hd; exact hd
            · rw [Nat.max_eq_left h3] at hd; exact absurd hd h1
          exact step_deadline hob.reachable (Nat.le_trans h2 (Nat.le_max_right _ _))

/--
**Delivery follows what was written, and a failure counts the bytes written** (checker: "delivery
follows what was written", "a failure counts the bytes written"), in the terms of the checker's model:
a failure says `notSent` only if no write was ever issued, `maybeDelivered` only if one was and no
final head was delivered, `responseReceived` only if a final head was delivered, and it counts the
request bytes whose writes completed.  The model is the one after the step; the failure is the
step's last action (`step_ends`), and the model's update for it changes none of these fields, so this
is also the model the checker consults when it meets the failure.
-/
theorem observed_fail {ex : Exchange} {m : Obs} (h : Observed ex m) {now : Timestamp}
    {e : ExchangeEvent} {f : Failure} (hm : .fail f ∈ (ex.step now e).2) :
    let m' := (ex.step now e).2.foldl Obs.see { m.observe e with now := max m.now now }
    (f.delivery = .notSent → m'.everWrote = false) ∧
      (f.delivery = .maybeDelivered → m'.everWrote = true ∧ m'.headDelivered = false) ∧
      (f.delivery = .responseReceived → m'.headDelivered = true) ∧ f.written = m'.acked := by
  intro m'
  have ha := (Observed.step now e h).agrees
  obtain ⟨_, hd, hw, _⟩ := step_fail h.reachable.inv hm
  obtain ⟨d1, d2, d3⟩ := delivery_iff (ex.step now e).1
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, ?_⟩
  · rw [ha.everWrote]; exact (d1.mp (hd ▸ h1)).2
  · obtain ⟨h2, h3⟩ := d2.mp (hd ▸ h1)
    exact ⟨by rw [ha.everWrote]; exact h3, by rw [ha.headDelivered, h2]; rfl⟩
  · rw [ha.headDelivered]; exact d3.mp (hd ▸ h1)
  · rw [ha.acked]; exact hw

/--
**One write in flight, following the request** (checker: "one write in flight", "writes follow the
request"), in the terms of the checker's model: a step emits a write only when the model has no write
in flight once it has taken the event into account, emits at most one, and that write is the
non-empty slice of the request that starts at the bytes the model counts as written.
-/
theorem observed_write {ex : Exchange} {m : Obs} (h : Observed ex m) (now : Timestamp)
    (e : ExchangeEvent) :
    (ex.step now e).2.countP isWrite ≤ 1 ∧
      ∀ b, .write b ∈ (ex.step now e).2 →
        (m.observe e).outstanding = none ∧ 0 < b.size ∧
          b = ex.request.extract (m.observe e).acked ((m.observe e).acked + b.size) := by
  have ia := h.agrees
  cases ht : ex.terminal
  · have hw := step_writes h.reachable.inv ht now e
    have ha := (Observed.step now e h).agrees
    have hacked : (m.observe e).acked = (ex.step now e).1.written := by
      rw [← ha.acked, ← Array.foldl_toList, see_acked]
    have hreq : (ex.step now e).1.request = ex.request := by
      rcases step_cases ex now e with ⟨_, hs⟩ | ⟨_, hg⟩
      · rw [hs]
      · rw [(hg h.reachable.inv).fixed.request]
        cases e <;> simp only [startOf] <;> (try split) <;> rfl
    have hout : (m.observe e).outstanding = wAfter ex e := by
      have hne : m.ended = false := by rw [ia.ended, ht]
      simp only [Obs.observe, hne, wAfter, Bool.false_eq_true, ↓reduceIte]
      cases e <;> simp only <;> try exact ia.outstanding
      split
      · rfl
      · rename_i hn; exact hn
    rcases hw with ⟨h1, _⟩ | ⟨h1, h2, _, h4⟩
    · refine ⟨by omega, fun b hb => ?_⟩
      exfalso
      have := Array.countP_eq_zero.mp h1 _ hb
      simp [isWrite] at this
    · refine ⟨by omega, fun b hb => ?_⟩
      obtain ⟨h5, h6, _⟩ := h4 b hb
      exact ⟨by rw [hout, h2], h5, by rw [hacked, ← hreq]; exact h6⟩
  · rw [step_of_terminal ht]
    simp

theorem step_fixed {ex : Exchange} (hi : Inv ex) (now : Timestamp) (e : ExchangeEvent) :
    (ex.step now e).1.config = ex.config ∧ (ex.step now e).1.request = ex.request ∧
      (ex.step now e).1.deadline = ex.deadline := by
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨_, hg⟩
  · rw [hs]; exact ⟨rfl, rfl, rfl⟩
  · have hf := (hg hi).fixed
    rw [hf.config, hf.request, hf.deadline]
    cases e <;> simp only [startOf] <;> (try split) <;> first | exact ⟨rfl, rfl, rfl⟩ | simp

/--
**Reusable only when safe** (checker: "reusable only when safe"), in the terms of the checker's
model: a step reports the connection reusable only when keep-alive was asked for, the whole request
was written, all of it before the final head was delivered, the peer did not close, and a final head
was delivered.  The checker's remaining reason, that the bytes read are exactly one response whose
framing permits reuse, is about the response bytes and so about the parser, whose verdict
`step_finish_reusable` shows the core requires.
-/
theorem observed_finish_reusable {ex : Exchange} {m : Obs} (h : Observed ex m) {now : Timestamp}
    {e : ExchangeEvent} (hm : .finish true ∈ (ex.step now e).2) :
    let m' := (ex.step now e).2.foldl Obs.see { m.observe e with now := max m.now now }
    ex.config.keepAlive = true ∧ m'.acked = ex.request.size ∧ m'.ackedAtHead = ex.request.size ∧
      m'.eofSeen = false ∧ m'.headDelivered = true := by
  intro m'
  have hi := h.reachable.inv
  have ha := (Observed.step now e h).agrees
  obtain ⟨_, hr⟩ := step_finish_reusable hi hm
  obtain ⟨hc, hrq, _⟩ := step_fixed hi now e
  have hhd : m'.headDelivered = true := by rw [ha.headDelivered]; exact hr.head
  obtain ⟨he1, he2⟩ := ha.early hhd
  rw [hr.notEarly, hrq] at he1
  rw [hrq] at he2
  refine ⟨by rw [← hc]; exact hr.keepAlive, by rw [ha.acked, hr.writtenAll, hrq], ?_,
    by rw [ha.eofSeen]; exact hr.noEnd, hhd⟩
  have : ¬ m'.ackedAtHead < ex.request.size := by simpa using he1.symm
  exact Nat.le_antisymm he2 (Nat.not_lt.mp this)

/--
**After the deadline the exchange has ended** (checker: "after the deadline the exchange has
ended"), in the terms of the checker's model: once the model's clock (the latest time of any event)
is at or past the deadline, the exchange has ended.
-/
theorem observed_deadline {ex : Exchange} {m : Obs} (h : Observed ex m) {now : Timestamp}
    {e : ExchangeEvent} (hd : ex.deadline ≤ max m.now now) : (ex.step now e).1.terminal = true := by
  have hc := (Observed.step now e h).clock
  rw [← Array.foldl_toList, see_now] at hc
  apply hc.2
  rw [(step_fixed h.reachable.inv now e).2.2]
  exact hd

/-! ## `begin` -/

/--
**One end, last, and only with an action, for `begin`** (checker: "one end, last", "the core ends only
with an action", on `begin`'s actions): `begin` ends the exchange exactly when it emits `finish` or
`fail`, and that action is its last.
-/
theorem begin_ends (req : PreparedRequest) (now deadline : Timestamp) :
    ((begin req now deadline).1.terminal = true ↔ ∃ a ∈ (begin req now deadline).2, isEnd a = true) ∧
      EndLast (begin req now deadline).2 := by
  have g := begin_good req now deadline
  exact ⟨⟨g.ends, fun ⟨a, ha, he⟩ => actOK_end_terminal (g.acts a ha) he⟩, g.endLast⟩

/--
**One write, following the request, for `begin`** (checker: "one write in flight", "writes follow the
request", on `begin`'s actions): `begin` emits at most one write, and it is a non-empty slice at the
start of the request.
-/
theorem begin_write (req : PreparedRequest) (now deadline : Timestamp) :
    (begin req now deadline).2.countP isWrite ≤ 1 ∧
      ∀ b, .write b ∈ (begin req now deadline).2 → 0 < b.size ∧ b = req.bytes.extract 0 b.size := by
  have g := begin_good req now deadline
  refine ⟨by rcases g.writes with ⟨h, _⟩ | ⟨h, _⟩ <;> omega, fun b hb => ?_⟩
  obtain ⟨h1, h2, _⟩ := g.acts _ hb
  rw [g.fixed.request, g.fixed.written] at h2
  simp only [initial, Nat.zero_add] at h2
  exact ⟨h1, h2⟩

/--
**A failure of `begin` says how far the request got** (checker: "delivery follows what was written",
"a failure counts the bytes written", on `begin`'s actions), in the terms of the checker's model.
-/
theorem begin_fail (req : PreparedRequest) (now deadline : Timestamp) {f : Failure}
    (hm : .fail f ∈ (begin req now deadline).2) :
    let m' := (begin req now deadline).2.foldl Obs.see { now }
    (f.delivery = .notSent → m'.everWrote = false) ∧
      (f.delivery = .maybeDelivered → m'.everWrote = true ∧ m'.headDelivered = false) ∧
      (f.delivery = .responseReceived → m'.headDelivered = true) ∧ f.written = m'.acked := by
  intro m'
  have ha := (Observed.begin req now deadline).agrees
  obtain ⟨_, hd, hw, _⟩ := (begin_good req now deadline).acts _ hm
  obtain ⟨d1, d2, d3⟩ := delivery_iff (begin req now deadline).1
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, ?_⟩
  · rw [ha.everWrote]; exact (d1.mp (hd ▸ h1)).2
  · obtain ⟨h2, h3⟩ := d2.mp (hd ▸ h1)
    exact ⟨by rw [ha.everWrote]; exact h3, by rw [ha.headDelivered, h2]; rfl⟩
  · rw [ha.headDelivered]; exact d3.mp (hd ▸ h1)
  · rw [ha.acked]; exact hw

end LeanHttp.Exchange
