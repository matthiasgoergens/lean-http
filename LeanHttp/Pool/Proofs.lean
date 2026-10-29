module

import all LeanHttp.Pool

/-!
# Proofs about the pool core

Theorems about `Pool.take`, `Pool.giveBack`, `Pool.drop`, `Pool.sweep` and `Pool.closeAll`, over
single operations and over every sequence of them (`Pool.run`, `Pool.trace`), for the properties
the shell relies on and `Tests/Pool.lean` checks by random runs and bounded exploration:

- **The invariant** (`WF`, `wf_run`): every connection is in at most one of the idle and checked-out
  lists, only once, and was allocated; no origin has more than `maxIdle` idle connections, nor more
  than `maxActive` checked out; a closed pool has no idle connections.  So every allocated connection
  is in exactly one of the states idle, checked out and gone (`WF.state_out`, `state_idle`,
  `state_gone`).
- **Returned or dropped once per checkout** (`trace_alternates`): for any connection, the operations
  that hand it out and the operations that take it back alternate, starting with a hand-out unless
  it is checked out already, so a checkout ends in at most one `giveBack` or `drop` (exactly one if
  the shell ends every call).  A `giveBack` or `drop` takes it back only if it is checked out
  (`giveBack_notOut`, `drop_notOut`); otherwise the pool is as `sweep` leaves it, or unchanged.  The
  pool knows connections by id, not by the call holding them: that a call gives back only the
  connection it took is the shell's part.
- **Gone stays gone** (`state_gone_run`, `trace_gone`): once a connection is gone, no sequence of
  operations hands it out or takes it back again.  A connection given back as not reusable, or
  dropped, is gone (`giveBack_unreusable_gone`, `drop_gone`), so it is never handed out again
  (`giveBack_unreusable_never_again`).
- **The idle cap** (`idleCount_run`) and **the active cap** (`activeCount_run`).
- **No expired connection is handed out** (`take_reuse`): `take` reuses only an idle connection of
  the origin that has not expired at the `now` given; a new connection gets an id never allocated
  before (`take_fresh`, `take_fresh_unused`).
- **What the shell closes** (`letGo_gone`): every connection an operation lets go was idle and is
  gone afterwards.  **Closing** (`apply_closed`, `run_closed`, `take_closed`): once closed, a pool
  stays closed and hands nothing out.

Not proved: that `take` prefers the most recently returned idle connection (`Tests/Pool.lean`
checks it), and anything about the shell.
-/

namespace LeanHttp.Pool

variable {κ : Type} [DecidableEq κ]

/-! ## The invariant -/

/--
The pool invariant.  Every id in the idle and checked-out lists appears once in the two together
and has been allocated; no origin has more than `maxIdle` idle connections, nor, with `maxActive`
set, more than that many checked out; a closed pool has no idle connections.
-/
structure WF (p : Pool κ) : Prop where
  /-- No connection is both idle and checked out, or twice in either. -/
  nodup : (p.idleIds ++ p.outIds).Nodup
  /-- Every connection in the pool was allocated. -/
  lt_next : ∀ id ∈ p.idleIds ++ p.outIds, id < p.next
  /-- The idle cap. -/
  idleCap : ∀ origin, p.idleCount origin ≤ p.config.maxIdle
  /-- The active cap. -/
  activeCap : ∀ m, p.config.maxActive = some m → ∀ origin, p.activeCount origin ≤ m
  /-- A closed pool keeps nothing idle. -/
  closedIdle : p.closed = true → p.idle = []

theorem wf_empty (config : PoolConfig) : (Pool.empty config : Pool κ).WF where
  nodup := by simp [empty, idleIds, outIds]
  lt_next := by simp [empty, idleIds, outIds]
  idleCap := by simp [empty, idleCount]
  activeCap := by simp [empty, activeCount]
  closedIdle := by simp [empty]

omit [DecidableEq κ] in
theorem mem_idleIds {p : Pool κ} {id : ConnId} : id ∈ p.idleIds ↔ ∃ c ∈ p.idle, c.id = id := by
  simp [idleIds]

omit [DecidableEq κ] in
theorem mem_outIds {p : Pool κ} {id : ConnId} : id ∈ p.outIds ↔ ∃ o, (id, o) ∈ p.out := by
  simp [outIds]

/--
No connection is both idle and checked out.
-/
theorem WF.not_out_of_idle {p : Pool κ} (h : p.WF) {id : ConnId} (hi : id ∈ p.idleIds) :
    id ∉ p.outIds :=
  fun ho => (List.nodup_append.mp h.nodup).2.2 id hi id ho rfl

/--
An idle connection is idle (`state_idle`), a checked-out one checked out: the states are exclusive.
-/
theorem WF.state_out {p : Pool κ} (h : p.WF) {id : ConnId} : p.state id = .out ↔ id ∈ p.outIds := by
  unfold state
  by_cases hi : id ∈ p.idleIds
  · simp [hi, h.not_out_of_idle hi]
  · by_cases ho : id ∈ p.outIds
    · simp [hi, ho]
    · simp only [hi, ho, ite_false]
      split <;> simp

omit [DecidableEq κ] in
theorem state_idle {p : Pool κ} {id : ConnId} : p.state id = .idle ↔ id ∈ p.idleIds := by
  unfold state
  by_cases hi : id ∈ p.idleIds
  · simp [hi]
  · simp only [hi, ite_false]
    split
    · simp
    · split <;> simp

omit [DecidableEq κ] in
theorem state_gone {p : Pool κ} {id : ConnId} :
    p.state id = .gone ↔ id ∉ p.idleIds ∧ id ∉ p.outIds ∧ id < p.next := by
  unfold state
  by_cases hi : id ∈ p.idleIds
  · simp [hi]
  · by_cases ho : id ∈ p.outIds
    · simp [hi, ho]
    · by_cases hn : id < p.next
      · simp [hi, ho, hn]
      · simp [hi, ho, hn]

/--
A pool whose idle and checked-out lists are sublists of those of a pool satisfying the invariant,
with the same limits and no smaller next id, satisfies it too, if it keeps nothing idle when closed.
-/
theorem WF.of_sub {p q : Pool κ} (h : p.WF) (hc : q.config = p.config) (hn : p.next ≤ q.next)
    (hi : q.idle.Sublist p.idle) (ho : q.out.Sublist p.out)
    (hcl : q.closed = true → q.idle = []) : q.WF := by
  have hs : (q.idleIds ++ q.outIds).Sublist (p.idleIds ++ p.outIds) :=
    (hi.map _).append (ho.map _)
  refine ⟨h.nodup.sublist hs,
    fun id hid => Nat.lt_of_lt_of_le (h.lt_next id (hs.subset hid)) hn, ?_, ?_, hcl⟩
  · intro k
    have := h.idleCap k
    simp only [idleCount] at this ⊢
    rw [hc]
    exact Nat.le_trans (hi.filter _).length_le this
  · intro m hm k
    rw [hc] at hm
    have := h.activeCap m hm k
    simp only [activeCount] at this ⊢
    exact Nat.le_trans (ho.filter _).length_le this

/-! ## Single operations preserve the invariant -/

omit [DecidableEq κ] in
@[simp] theorem sweep_out (p : Pool κ) (now : Nat) : (p.sweep now).1.out = p.out := rfl
omit [DecidableEq κ] in
@[simp] theorem sweep_next (p : Pool κ) (now : Nat) : (p.sweep now).1.next = p.next := rfl
omit [DecidableEq κ] in
@[simp] theorem sweep_config (p : Pool κ) (now : Nat) : (p.sweep now).1.config = p.config := rfl
omit [DecidableEq κ] in
@[simp] theorem sweep_closed (p : Pool κ) (now : Nat) : (p.sweep now).1.closed = p.closed := rfl
omit [DecidableEq κ] in
@[simp] theorem sweep_idle (p : Pool κ) (now : Nat) :
    (p.sweep now).1.idle = p.idle.filter (!p.expired now ·) := rfl

theorem sweep_wf {p : Pool κ} (h : p.WF) (now : Nat) : (p.sweep now).1.WF :=
  h.of_sub rfl (Nat.le_refl _) List.filter_sublist (List.Sublist.refl _)
    (fun hc => by simp [h.closedIdle hc])

theorem drop_wf {p : Pool κ} (h : p.WF) (id : ConnId) : (p.drop id).1.WF := by
  unfold drop
  split
  · exact h.of_sub rfl (Nat.le_refl _) (List.Sublist.refl _) List.filter_sublist h.closedIdle
  · exact h

theorem closeAll_wf {p : Pool κ} (h : p.WF) : p.closeAll.1.WF :=
  h.of_sub rfl (Nat.le_refl _) (List.nil_sublist _) (List.Sublist.refl _) (fun _ => rfl)

/--
Adding a checked-out connection of `origin` to a pool not at its cap for `origin` keeps the active
cap.
-/
theorem activeCap_cons {p q : Pool κ} (h : p.WF) {origin : κ} (hcap : p.atCap origin = false)
    {i : ConnId} (hq : q.out = (i, origin) :: p.out) (hc : q.config = p.config) :
    ∀ m, q.config.maxActive = some m → ∀ k, q.activeCount k ≤ m := by
  intro m hm k
  rw [hc] at hm
  have hle := h.activeCap m hm k
  have hlt : p.activeCount origin < m := by
    simp only [atCap, hm] at hcap
    exact Nat.lt_of_not_le (by simpa using hcap)
  simp only [activeCount, hq, List.filter_cons] at hle hlt ⊢
  by_cases hk : origin = k
  · subst hk
    simp only [decide_true, ite_true, List.length_cons]
    omega
  · simp [hk, hle]

theorem checkout_wf {p : Pool κ} (h : p.WF) (origin : κ) (reuse : Bool) :
    (p.checkout origin reuse).1.WF := by
  unfold checkout
  split
  · exact h
  rename_i hcl
  split
  · exact h
  rename_i hcap
  have hcap : p.atCap origin = false := by simpa using hcap
  have hcl : p.closed = false := by simpa using hcl
  split
  · rename_i c hc
    have hf : p.idle.find? (·.origin = origin) = some c := by
      cases reuse <;> simp_all
    have hmem : c ∈ p.idle := List.mem_of_find?_eq_some hf
    have hci : c.id ∈ p.idleIds := mem_idleIds.mpr ⟨c, hmem, rfl⟩
    have hsub : ((p.idle.filter (·.id ≠ c.id)).map (·.id) ++ p.outIds).Sublist
        (p.idleIds ++ p.outIds) :=
      (List.filter_sublist.map _).append (List.Sublist.refl _)
    have hnot : c.id ∉ (p.idle.filter (·.id ≠ c.id)).map (·.id) ++ p.outIds := by
      simp only [List.mem_append, List.mem_map, List.mem_filter]
      rintro (⟨d, ⟨_, hd⟩, hdc⟩ | ho)
      · simp at hd
        exact hd hdc
      · exact h.not_out_of_idle hci ho
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show ((p.idle.filter (·.id ≠ c.id)).map (·.id) ++ c.id :: p.outIds).Nodup
      exact List.perm_middle.nodup_iff.mpr (List.nodup_cons.mpr ⟨hnot, h.nodup.sublist hsub⟩)
    · intro id hid
      show id < p.next
      have hid : id ∈ (p.idle.filter (·.id ≠ c.id)).map (·.id) ++ c.id :: p.outIds := hid
      rcases List.mem_append.mp hid with hl | hr
      · exact h.lt_next id (hsub.subset (List.mem_append_left _ hl))
      · rcases List.mem_cons.mp hr with rfl | ho
        · exact h.lt_next _ (List.mem_append_left _ hci)
        · exact h.lt_next id (List.mem_append_right _ ho)
    · intro k
      have := h.idleCap k
      simp only [idleCount] at this ⊢
      exact Nat.le_trans (List.filter_sublist.filter _).length_le this
    · exact activeCap_cons h hcap rfl rfl
    · intro hc'
      simp [hcl] at hc'
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (p.idleIds ++ p.next :: p.outIds).Nodup
      refine List.perm_middle.nodup_iff.mpr (List.nodup_cons.mpr ⟨?_, h.nodup⟩)
      intro hn
      exact Nat.lt_irrefl _ (h.lt_next _ hn)
    · intro id hid
      show id < p.next + 1
      have hid : id ∈ p.idleIds ++ p.next :: p.outIds := hid
      rcases List.mem_append.mp hid with hl | hr
      · exact Nat.lt_succ_of_lt (h.lt_next id (List.mem_append_left _ hl))
      · rcases List.mem_cons.mp hr with rfl | ho
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (h.lt_next id (List.mem_append_right _ ho))
    · exact h.idleCap
    · exact activeCap_cons h hcap rfl rfl
    · intro hc'
      simp [hcl] at hc'

theorem take_wf {p : Pool κ} (h : p.WF) (origin : κ) (now : Nat) (reuse : Bool) :
    (p.take origin now reuse).1.WF :=
  checkout_wf (sweep_wf h now) origin reuse

omit [DecidableEq κ] in
/--
What `find?` finds among the checked-out connections is checked out, under the id looked for.
-/
theorem find_out {p : Pool κ} {id i : ConnId} {o : κ} (hf : p.out.find? (·.1 = id) = some (i, o)) :
    i = id ∧ (id, o) ∈ p.out := by
  have hi : i = id := by simpa using List.find?_some hf
  subst hi
  exact ⟨rfl, List.mem_of_find?_eq_some hf⟩

theorem checkin_wf {p : Pool κ} (h : p.WF) (id : ConnId) (reusable : Bool) (now : Nat) :
    (p.checkin id reusable now).1.WF := by
  unfold checkin
  split
  · exact h
  rename_i i origin hf
  obtain ⟨-, hmem⟩ := find_out hf
  have hid : id ∈ p.outIds := mem_outIds.mpr ⟨origin, hmem⟩
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
    obtain ⟨⟨-, hcl⟩, hcount⟩ := hcond
    have hsub : (p.idleIds ++ (p.out.filter (·.1 ≠ id)).map (·.1)).Sublist
        (p.idleIds ++ p.outIds) :=
      (List.Sublist.refl _).append (List.filter_sublist.map _)
    have hnot : id ∉ p.idleIds ++ (p.out.filter (·.1 ≠ id)).map (·.1) := by
      simp only [List.mem_append, List.mem_map, List.mem_filter]
      rintro (hi | ⟨d, ⟨_, hd⟩, hdi⟩)
      · exact h.not_out_of_idle hi hid
      · simp at hd
        exact hd hdi
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (id :: (p.idleIds ++ (p.out.filter (·.1 ≠ id)).map (·.1))).Nodup
      exact List.nodup_cons.mpr ⟨hnot, h.nodup.sublist hsub⟩
    · intro j hj
      show j < p.next
      have hj : j ∈ id :: (p.idleIds ++ (p.out.filter (·.1 ≠ id)).map (·.1)) := hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact h.lt_next _ (List.mem_append_right _ hid)
      · exact h.lt_next j (hsub.subset hj)
    · intro k
      have := h.idleCap k
      simp only [idleCount] at this hcount ⊢
      show (List.filter _ ({ id, origin, since := now } :: p.idle)).length ≤ p.config.maxIdle
      rw [List.filter_cons]
      by_cases hk : origin = k
      · subst hk
        simp only [decide_true, ite_true, List.length_cons]
        omega
      · simp [hk, this]
    · intro m hm k
      have := h.activeCap m hm k
      simp only [activeCount] at this ⊢
      exact Nat.le_trans (List.filter_sublist.filter _).length_le this
    · intro hc'
      simp [hcl] at hc'
  · exact h.of_sub rfl (Nat.le_refl _) (List.Sublist.refl _) List.filter_sublist h.closedIdle

theorem giveBack_wf {p : Pool κ} (h : p.WF) (id : ConnId) (reusable : Bool) (now : Nat) :
    (p.giveBack id reusable now).1.WF :=
  checkin_wf (sweep_wf h now) id reusable now

theorem apply_wf {p : Pool κ} (h : p.WF) (op : PoolOp κ) : (p.apply op).WF := by
  cases op with
  | take origin now reuse => exact take_wf h origin now reuse
  | giveBack id reusable now => exact giveBack_wf h id reusable now
  | drop id => exact drop_wf h id
  | sweep now => exact sweep_wf h now
  | closeAll => exact closeAll_wf h

/--
Every sequence of operations preserves the invariant.
-/
theorem wf_run {p : Pool κ} (h : p.WF) (ops : List (PoolOp κ)) : (p.run ops).WF := by
  induction ops generalizing p with
  | nil => exact h
  | cons op ops ih => exact ih (apply_wf h op)

theorem apply_config (p : Pool κ) (op : PoolOp κ) : (p.apply op).config = p.config := by
  cases op with
  | take origin now reuse =>
    simp only [apply, take, checkout]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | giveBack id reusable now =>
    simp only [apply, giveBack, checkin]
    split
    · rfl
    · split <;> rfl
  | drop id =>
    simp only [apply, drop]
    split <;> rfl
  | sweep now => rfl
  | closeAll => rfl

theorem run_config (p : Pool κ) (ops : List (PoolOp κ)) : (p.run ops).config = p.config := by
  induction ops generalizing p with
  | nil => rfl
  | cons op ops ih => exact (ih (p.apply op)).trans (apply_config p op)

/--
**The idle cap.**  In every pool reachable from an empty one, no origin has more than `maxIdle` idle
connections.
-/
theorem idleCount_run (config : PoolConfig) (ops : List (PoolOp κ)) (origin : κ) :
    ((Pool.empty config : Pool κ).run ops).idleCount origin ≤ config.maxIdle := by
  have := (wf_run (wf_empty config) ops).idleCap origin
  rwa [run_config] at this

/--
**The active cap.**  In every pool reachable from an empty one with `maxActive` set, no origin has
more than that many connections checked out.
-/
theorem activeCount_run (config : PoolConfig) (m : Nat) (hm : config.maxActive = some m)
    (ops : List (PoolOp κ)) (origin : κ) :
    ((Pool.empty config : Pool κ).run ops).activeCount origin ≤ m := by
  have h := (wf_run (wf_empty config) ops).activeCap m
  rw [run_config] at h
  exact h hm origin

/-! ## Taking a connection -/

/--
**No expired connection is handed out.**  When `take` reuses connection `id`, it was idle, of the
origin asked for, and had not expired at the `now` given: less than `idleTimeoutMs` had passed since
it was given back.
-/
theorem take_reuse {p : Pool κ} {origin : κ} {now : Nat} {reuse : Bool} {id : ConnId}
    (h : (p.take origin now reuse).2.1 = .reuse id) :
    ∃ c ∈ p.idle, c.id = id ∧ c.origin = origin ∧ now < c.since + p.config.idleTimeoutMs := by
  simp only [take, checkout] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · rename_i c hc
    cases h
    have hf : (p.sweep now).1.idle.find? (·.origin = origin) = some c := by
      cases reuse <;> simp_all
    have hmem := List.mem_of_find?_eq_some hf
    have horigin : c.origin = origin := by simpa using List.find?_some hf
    simp only [sweep_idle, List.mem_filter, expired, Bool.not_eq_true', decide_eq_false_iff_not,
      Nat.not_le] at hmem
    exact ⟨c, hmem.1, rfl, horigin, hmem.2⟩
  · cases h

/--
A new connection gets the next id, which no connection had before (`take_fresh_unused`).
-/
theorem take_fresh {p : Pool κ} {origin : κ} {now : Nat} {reuse : Bool} {id : ConnId}
    (h : (p.take origin now reuse).2.1 = .fresh id) : id = p.next := by
  simp only [take, checkout] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · cases h
    rfl

/--
In a pool satisfying the invariant, the id `take` gives a new connection was never allocated.
-/
theorem take_fresh_unused {p : Pool κ} (h : p.WF) {origin : κ} {now : Nat} {reuse : Bool}
    {id : ConnId} (hf : (p.take origin now reuse).2.1 = .fresh id) : p.state id = .unused := by
  have hn := take_fresh hf
  subst hn
  have hi : p.next ∉ p.idleIds := fun hx => Nat.lt_irrefl _ (h.lt_next _ (List.mem_append_left _ hx))
  have ho : p.next ∉ p.outIds := fun hx => Nat.lt_irrefl _ (h.lt_next _ (List.mem_append_right _ hx))
  simp [state, hi, ho]

/--
A closed pool hands nothing out.
-/
theorem take_closed {p : Pool κ} (hc : p.closed = true) (origin : κ) (now : Nat) (reuse : Bool) :
    (p.take origin now reuse).2.1 = .closed := by
  simp [take, checkout, hc]

/-! ## Giving back and dropping -/

theorem checkin_none {q : Pool κ} {i : ConnId} (hf : q.out.find? (·.1 = i) = none)
    (reusable : Bool) (now : Nat) : q.checkin i reusable now = (q, .notOut) := by
  simp only [checkin, hf]

theorem checkin_idle {q : Pool κ} {i j : ConnId} {o : κ} (hf : q.out.find? (·.1 = i) = some (j, o))
    {reusable : Bool} (hc : (reusable && !q.closed && decide (q.idleCount o < q.config.maxIdle)) = true)
    (now : Nat) :
    q.checkin i reusable now =
      ({ q with out := q.out.filter (·.1 ≠ i), idle := { id := i, origin := o, since := now } :: q.idle },
        .idle) := by
  simp only [checkin, hf]
  rw [ite_eq_left hc]

theorem checkin_dropped {q : Pool κ} {i j : ConnId} {o : κ} (hf : q.out.find? (·.1 = i) = some (j, o))
    {reusable : Bool}
    (hc : ¬(reusable && !q.closed && decide (q.idleCount o < q.config.maxIdle)) = true) (now : Nat) :
    q.checkin i reusable now = ({ q with out := q.out.filter (·.1 ≠ i) }, .dropped) := by
  simp only [checkin, hf]
  rw [ite_eq_right hc]

omit [DecidableEq κ] in
theorem mem_filter_outIds {p : Pool κ} {i id : ConnId} :
    id ∈ (p.out.filter (·.1 ≠ i)).map (·.1) ↔ id ∈ p.outIds ∧ id ≠ i := by
  simp only [outIds, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by simpa using hxi⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxi⟩
    exact ⟨x, ⟨hx, by simpa using hxi⟩, rfl⟩

/--
**Only a checked-out connection can be given back.**  Giving back any other connection reports
`notOut` and leaves the pool as `sweep` leaves it.
-/
theorem giveBack_notOut {p : Pool κ} {id : ConnId} (hid : id ∉ p.outIds) (reusable : Bool)
    (now : Nat) :
    (p.giveBack id reusable now).1 = (p.sweep now).1 ∧
      (p.giveBack id reusable now).2.1 = .notOut := by
  have hf : (p.sweep now).1.out.find? (·.1 = id) = none := by
    rw [List.find?_eq_none]
    intro ⟨i, o⟩ hx hxid
    have hi : i = id := by simpa using hxid
    subst hi
    exact hid (mem_outIds.mpr ⟨o, hx⟩)
  have := checkin_none hf reusable now
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/--
Giving back a checked-out connection never reports `notOut`.
-/
theorem giveBack_out {p : Pool κ} {id : ConnId} (hid : id ∈ p.outIds) (reusable : Bool)
    (now : Nat) : (p.giveBack id reusable now).2.1 ≠ .notOut := by
  obtain ⟨o, ho⟩ := mem_outIds.mp hid
  have hf : (p.sweep now).1.out.find? (·.1 = id) ≠ none := by
    rw [ne_eq, List.find?_eq_none]
    intro hall
    exact hall _ ho (by simp)
  simp only [giveBack, checkin]
  split
  · contradiction
  · split <;> simp

omit [DecidableEq κ] in
/--
**Only a checked-out connection can be dropped.**  Dropping any other connection changes nothing.
-/
theorem drop_notOut {p : Pool κ} {id : ConnId} (hid : id ∉ p.outIds) : p.drop id = (p, false) := by
  simp [drop, hid]

/--
After `giveBack` of a connection, it is not checked out, whether or not it was before.
-/
theorem giveBack_not_out (p : Pool κ) (id : ConnId) (reusable : Bool) (now : Nat) :
    id ∉ (p.giveBack id reusable now).1.outIds := by
  simp only [giveBack, checkin]
  split
  · rename_i hf
    rw [List.find?_eq_none] at hf
    intro hid
    obtain ⟨o, ho⟩ := mem_outIds.mp hid
    exact hf _ ho (by simp)
  · split <;> simp [outIds]

omit [DecidableEq κ] in
/--
After `drop` of a connection, it is not checked out, whether or not it was before.
-/
theorem drop_not_out (p : Pool κ) (id : ConnId) : id ∉ (p.drop id).1.outIds := by
  by_cases hid : id ∈ p.outIds
  · have hd : p.drop id = ({ p with out := p.out.filter (·.1 ≠ id) }, true) := by simp [drop, hid]
    rw [hd]
    exact fun hx => (mem_filter_outIds.mp hx).2 rfl
  · rw [drop_notOut hid]
    exact hid

theorem checkin_dropped_gone {q : Pool κ} (h : q.WF) {id : ConnId} (hid : id ∈ q.outIds)
    {reusable : Bool} {now : Nat} (hd : (q.checkin id reusable now).2 = .dropped) :
    (q.checkin id reusable now).1.state id = .gone := by
  have hlt : id < q.next := h.lt_next id (List.mem_append_right _ hid)
  have hidle : id ∉ q.idleIds := fun hi => h.not_out_of_idle hi hid
  rcases hfind : q.out.find? (·.1 = id) with _ | ⟨j, o⟩
  · rw [checkin_none hfind] at hd
    cases hd
  · by_cases hc : (reusable && !q.closed && decide (q.idleCount o < q.config.maxIdle)) = true
    · rw [checkin_idle hfind hc] at hd
      cases hd
    · rw [checkin_dropped hfind hc, state_gone]
      exact ⟨hidle, fun hx => (mem_filter_outIds.mp hx).2 rfl, hlt⟩

/--
A connection given back and not kept idle (not reusable, the origin's idle connections at the cap,
or the pool closed) is gone.
-/
theorem giveBack_dropped_gone {p : Pool κ} (h : p.WF) {id : ConnId} (hid : id ∈ p.outIds)
    {reusable : Bool} {now : Nat} (hd : (p.giveBack id reusable now).2.1 = .dropped) :
    (p.giveBack id reusable now).1.state id = .gone :=
  checkin_dropped_gone (sweep_wf h now) hid hd

/--
**A checked-out connection given back as not reusable is gone.**
-/
theorem giveBack_unreusable_gone {p : Pool κ} (h : p.WF) {id : ConnId} (hid : id ∈ p.outIds)
    (now : Nat) : (p.giveBack id false now).1.state id = .gone := by
  apply giveBack_dropped_gone h hid
  obtain ⟨o, ho⟩ := mem_outIds.mp hid
  simp only [giveBack, checkin]
  split
  · rename_i hf
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf _ ho)
  · simp

/--
**A checked-out connection that is dropped is gone.**
-/
theorem drop_gone {p : Pool κ} (h : p.WF) {id : ConnId} (hid : id ∈ p.outIds) :
    (p.drop id).1.state id = .gone := by
  have hlt : id < p.next := h.lt_next id (List.mem_append_right _ hid)
  have hidle : id ∉ p.idleIds := fun hi => h.not_out_of_idle hi hid
  rw [state_gone]
  simp only [drop, hid, ite_true]
  refine ⟨hidle, ?_, hlt⟩
  simp [outIds]

/-! ## Sequences of operations -/

/--
What an operation does to connection `id`: hands it out (`take`) or takes it back (`giveBack` or
`drop`, when it was checked out).
-/
inductive Event where
  /-- `take` handed the connection out. -/
  | handedOut
  /-- `giveBack` or `drop` took the connection back. -/
  | returned
deriving Repr, DecidableEq

/--
The event, if any, that `op` makes for connection `id` in `p`.
-/
def eventOf (p : Pool κ) (id : ConnId) : PoolOp κ → Option Event
  | .take origin now reuse =>
    if handed (p.take origin now reuse).2.1 = some id then some .handedOut else none
  | .giveBack i reusable now =>
    if i = id ∧ (p.giveBack i reusable now).2.1 ≠ .notOut then some .returned else none
  | .drop i => if i = id ∧ (p.drop i).2 = true then some .returned else none
  | .sweep _ | .closeAll => none

/--
The events that `ops` make for connection `id`, starting from `p`.
-/
def trace (p : Pool κ) (id : ConnId) : List (PoolOp κ) → List Event
  | [] => []
  | op :: ops => (p.eventOf id op).toList ++ (p.apply op).trace id ops

/--
Events that alternate between hand-outs and returns, starting with a return if `out` holds (the
connection is checked out) and with a hand-out otherwise.
-/
def Alternates : Bool → List Event → Prop
  | _, [] => True
  | false, .handedOut :: es => Alternates true es
  | true, .returned :: es => Alternates false es
  | false, .returned :: _ => False
  | true, .handedOut :: _ => False

theorem checkout_out {p : Pool κ} (h : p.WF) (origin : κ) (reuse : Bool) (id : ConnId) :
    (id ∈ (p.checkout origin reuse).1.outIds ↔
      id ∈ p.outIds ∨ handed (p.checkout origin reuse).2 = some id) ∧
    (handed (p.checkout origin reuse).2 = some id → id ∉ p.outIds) := by
  unfold checkout
  split
  · simp [handed]
  split
  · simp [handed]
  split
  · rename_i c hc
    have hf : p.idle.find? (·.origin = origin) = some c := by
      cases reuse <;> simp_all
    have hci : c.id ∈ p.idleIds := mem_idleIds.mpr ⟨c, List.mem_of_find?_eq_some hf, rfl⟩
    simp only [outIds, List.map_cons, List.mem_cons, handed, Option.some.injEq]
    constructor
    · constructor
      · rintro (rfl | ho) <;> simp_all
      · rintro (ho | rfl) <;> simp_all
    · rintro rfl
      exact h.not_out_of_idle hci
  · simp only [outIds, List.map_cons, List.mem_cons, handed, Option.some.injEq]
    constructor
    · constructor
      · rintro (rfl | ho) <;> simp_all
      · rintro (ho | rfl) <;> simp_all
    · rintro rfl hn
      exact Nat.lt_irrefl _ (h.lt_next _ (List.mem_append_right _ hn))

theorem checkin_out (q : Pool κ) (i : ConnId) (reusable : Bool) (now : Nat) (id : ConnId) :
    ((q.checkin i reusable now).2 = .notOut ↔ i ∉ q.outIds) ∧
    (id ∈ (q.checkin i reusable now).1.outIds ↔
      id ∈ q.outIds ∧ ((q.checkin i reusable now).2 = .notOut ∨ id ≠ i)) := by
  rcases hfind : q.out.find? (·.1 = i) with _ | ⟨j, o⟩
  · have hi : i ∉ q.outIds := by
      intro hi
      obtain ⟨o, ho⟩ := mem_outIds.mp hi
      exact (List.find?_eq_none.mp hfind) _ ho (by simp)
    rw [checkin_none hfind]
    simp [hi]
  · obtain ⟨-, hmem⟩ := find_out hfind
    have hi : i ∈ q.outIds := mem_outIds.mpr ⟨o, hmem⟩
    by_cases hc : (reusable && !q.closed && decide (q.idleCount o < q.config.maxIdle)) = true
    · rw [checkin_idle hfind hc]
      refine ⟨by simp [hi], ?_⟩
      show id ∈ (q.out.filter (·.1 ≠ i)).map (·.1) ↔ _
      rw [mem_filter_outIds]
      simp
    · rw [checkin_dropped hfind hc]
      refine ⟨by simp [hi], ?_⟩
      show id ∈ (q.out.filter (·.1 ≠ i)).map (·.1) ↔ _
      rw [mem_filter_outIds]
      simp

/--
How a single operation moves connection `id` in and out of the checked-out list: a hand-out moves
it in, a return moves it out, and an operation with no event for it leaves it where it was.
-/
theorem out_step {p : Pool κ} (h : p.WF) (id : ConnId) (op : PoolOp κ) :
    (p.eventOf id op = some .handedOut → id ∉ p.outIds ∧ id ∈ (p.apply op).outIds) ∧
    (p.eventOf id op = some .returned → id ∈ p.outIds ∧ id ∉ (p.apply op).outIds) ∧
    (p.eventOf id op = none → (id ∈ (p.apply op).outIds ↔ id ∈ p.outIds)) := by
  cases op with
  | take origin now reuse =>
    obtain ⟨hmem, hnew⟩ := checkout_out (sweep_wf h now) origin reuse id
    have he : p.eventOf id (.take origin now reuse) =
        if handed ((p.sweep now).1.checkout origin reuse).2 = some id then some .handedOut
        else none := rfl
    have ha : p.apply (.take origin now reuse) = ((p.sweep now).1.checkout origin reuse).1 := rfl
    have ho : (p.sweep now).1.outIds = p.outIds := rfl
    rw [he, ha]
    rw [ho] at hmem hnew
    by_cases hh : handed ((p.sweep now).1.checkout origin reuse).2 = some id
    · rw [ite_eq_left hh]
      exact ⟨fun _ => ⟨hnew hh, hmem.mpr (Or.inr hh)⟩, (fun h => nomatch h), (fun h => nomatch h)⟩
    · rw [ite_eq_right hh]
      exact ⟨(fun h => nomatch h), (fun h => nomatch h),
        fun _ => ⟨fun hx => (hmem.mp hx).resolve_right hh, fun hx => hmem.mpr (Or.inl hx)⟩⟩
  | giveBack i reusable now =>
    obtain ⟨hnot, hmem⟩ := checkin_out (p.sweep now).1 i reusable now id
    have he : p.eventOf id (.giveBack i reusable now) =
        if i = id ∧ ((p.sweep now).1.checkin i reusable now).2 ≠ .notOut then some .returned
        else none := rfl
    have ha : p.apply (.giveBack i reusable now) = ((p.sweep now).1.checkin i reusable now).1 := rfl
    have ho : (p.sweep now).1.outIds = p.outIds := rfl
    rw [he, ha]
    rw [ho] at hnot hmem
    by_cases hc : i = id ∧ ((p.sweep now).1.checkin i reusable now).2 ≠ .notOut
    · rw [ite_eq_left hc]
      obtain ⟨rfl, hc⟩ := hc
      have hi : i ∈ p.outIds := Classical.byContradiction fun hi => hc (hnot.mpr hi)
      exact ⟨(fun h => nomatch h),
        fun _ => ⟨hi, fun hx => (hmem.mp hx).2.elim hc (fun hne => hne rfl)⟩, (fun h => nomatch h)⟩
    · rw [ite_eq_right hc]
      refine ⟨(fun h => nomatch h), (fun h => nomatch h),
        fun _ => ⟨fun hx => (hmem.mp hx).1, fun hx => hmem.mpr ⟨hx, ?_⟩⟩⟩
      by_cases hid : id = i
      · subst hid
        exact Or.inl (Classical.byContradiction fun hn => hc ⟨rfl, hn⟩)
      · exact Or.inr hid
  | drop i =>
    have he : p.eventOf id (.drop i) =
        if i = id ∧ (p.drop i).2 = true then some .returned else none := rfl
    have ha : p.apply (.drop i) = (p.drop i).1 := rfl
    rw [he, ha]
    by_cases hi : i ∈ p.outIds
    · have hd : p.drop i = ({ p with out := p.out.filter (·.1 ≠ i) }, true) := by simp [drop, hi]
      rw [hd]
      by_cases hid : i = id
      · subst hid
        rw [ite_eq_left ⟨rfl, rfl⟩]
        exact ⟨(fun h => nomatch h), fun _ => ⟨hi, fun hx => (mem_filter_outIds.mp hx).2 rfl⟩,
          (fun h => nomatch h)⟩
      · rw [ite_eq_right (fun h => hid h.1)]
        exact ⟨(fun h => nomatch h), (fun h => nomatch h),
          fun _ => ⟨fun hx => (mem_filter_outIds.mp hx).1,
            fun hx => mem_filter_outIds.mpr ⟨hx, fun h => hid h.symm⟩⟩⟩
    · rw [drop_notOut hi, ite_eq_right ((fun h => nomatch h.2))]
      exact ⟨(fun h => nomatch h), (fun h => nomatch h), fun _ => Iff.rfl⟩
  | sweep now =>
    have he : p.eventOf id (.sweep now) = none := rfl
    rw [he]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), fun _ => Iff.rfl⟩
  | closeAll =>
    have he : p.eventOf id .closeAll = none := rfl
    rw [he]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h), fun _ => Iff.rfl⟩

/--
**Returned or dropped once per checkout.**  For any connection and any sequence of operations from a
pool satisfying the invariant, the hand-outs and returns of the connection alternate, starting with
a return if it is checked out and with a hand-out otherwise.  So every checkout ends in at most one
`giveBack` or `drop` (exactly one, if the shell ends every call), and none without a checkout.  The
pool tells connections apart by id, not by the call holding them.
-/
theorem trace_alternates {p : Pool κ} (h : p.WF) (id : ConnId) (ops : List (PoolOp κ)) :
    Alternates (decide (id ∈ p.outIds)) (p.trace id ops) := by
  induction ops generalizing p with
  | nil => simp [trace, Alternates]
  | cons op ops ih =>
    obtain ⟨h1, h2, h3⟩ := out_step h id op
    have ih := ih (apply_wf h op)
    simp only [trace]
    cases he : p.eventOf id op with
    | none =>
      have hs := h3 he
      simpa [hs] using ih
    | some e =>
      cases e with
      | handedOut =>
        obtain ⟨hn, hy⟩ := h1 he
        simpa [hn, hy, Alternates] using ih
      | returned =>
        obtain ⟨hy, hn⟩ := h2 he
        simpa [hn, hy, Alternates] using ih

/--
Every id an operation puts in the idle list was idle or checked out before.
-/
theorem apply_idle {p : Pool κ} (op : PoolOp κ) {id : ConnId} (hid : id ∈ (p.apply op).idleIds) :
    id ∈ p.idleIds ∨ id ∈ p.outIds := by
  have sw : ∀ now, id ∈ (p.sweep now).1.idleIds → id ∈ p.idleIds := fun now hx => by
    simp only [idleIds, sweep_idle, List.mem_map, List.mem_filter] at hx ⊢
    obtain ⟨c, ⟨hc, _⟩, rfl⟩ := hx
    exact ⟨c, hc, rfl⟩
  cases op with
  | take origin now reuse =>
    left
    apply sw now
    simp only [apply, take, checkout] at hid
    split at hid
    · exact hid
    split at hid
    · exact hid
    split at hid
    · simp only [idleIds, List.mem_map, List.mem_filter] at hid ⊢
      obtain ⟨c, ⟨hc, _⟩, rfl⟩ := hid
      exact ⟨c, hc, rfl⟩
    · exact hid
  | giveBack i reusable now =>
    have hid : id ∈ ((p.sweep now).1.checkin i reusable now).1.idleIds := hid
    rcases hfind : (p.sweep now).1.out.find? (·.1 = i) with _ | ⟨j, o⟩
    · rw [checkin_none hfind] at hid
      exact Or.inl (sw now hid)
    · obtain ⟨-, hmem⟩ := find_out hfind
      by_cases hc : (reusable && !(p.sweep now).1.closed &&
          decide ((p.sweep now).1.idleCount o < (p.sweep now).1.config.maxIdle)) = true
      · rw [checkin_idle hfind hc] at hid
        simp only [idleIds, List.map_cons, List.mem_cons] at hid
        rcases hid with rfl | hx
        · exact Or.inr (mem_outIds.mpr ⟨o, hmem⟩)
        · exact Or.inl (sw now hx)
      · rw [checkin_dropped hfind hc] at hid
        exact Or.inl (sw now hid)
  | drop i =>
    left
    simp only [apply, drop] at hid
    split at hid <;> exact hid
  | sweep now => exact Or.inl (sw now hid)
  | closeAll => simp [apply, closeAll, idleIds] at hid

/--
Every id an operation puts in the checked-out list was checked out or idle before, or is new.
-/
theorem apply_out {p : Pool κ} (op : PoolOp κ) {id : ConnId} (hid : id ∈ (p.apply op).outIds) :
    id ∈ p.outIds ∨ id ∈ p.idleIds ∨ p.next ≤ id := by
  cases op with
  | take origin now reuse =>
    simp only [apply, take, checkout] at hid
    split at hid
    · exact Or.inl hid
    split at hid
    · exact Or.inl hid
    split at hid
    · rename_i c hc
      have hf : (p.sweep now).1.idle.find? (·.origin = origin) = some c := by
        cases reuse <;> simp_all
      have hmem := List.mem_of_find?_eq_some hf
      simp only [sweep_idle, List.mem_filter] at hmem
      simp only [outIds, List.map_cons, List.mem_cons] at hid
      rcases hid with rfl | hx
      · exact Or.inr (Or.inl (mem_idleIds.mpr ⟨c, hmem.1, rfl⟩))
      · exact Or.inl (by simpa [outIds] using hx)
    · simp only [outIds, List.map_cons, List.mem_cons] at hid
      rcases hid with rfl | hx
      · exact Or.inr (Or.inr (Nat.le_refl _))
      · exact Or.inl (by simpa [outIds] using hx)
  | giveBack i reusable now =>
    exact Or.inl ((checkin_out (p.sweep now).1 i reusable now id).2.mp hid).1
  | drop i =>
    left
    simp only [apply, drop] at hid
    split at hid
    · simp only [outIds, List.mem_map, List.mem_filter] at hid ⊢
      obtain ⟨x, ⟨hx, _⟩, rfl⟩ := hid
      exact ⟨x, hx, rfl⟩
    · exact hid
  | sweep now => exact Or.inl hid
  | closeAll => exact Or.inl hid

theorem apply_next (p : Pool κ) (op : PoolOp κ) : p.next ≤ (p.apply op).next := by
  cases op with
  | take origin now reuse =>
    simp only [apply, take, checkout]
    split
    · exact Nat.le_refl _
    split
    · exact Nat.le_refl _
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ _
  | giveBack i reusable now =>
    simp only [apply, giveBack, checkin]
    split
    · exact Nat.le_refl _
    · split <;> exact Nat.le_refl _
  | drop i =>
    simp only [apply, drop]
    split <;> exact Nat.le_refl _
  | sweep now => exact Nat.le_refl _
  | closeAll => exact Nat.le_refl _

/--
**Gone stays gone**, over one operation.
-/
theorem state_gone_apply {p : Pool κ} {id : ConnId} (hg : p.state id = .gone) (op : PoolOp κ) :
    (p.apply op).state id = .gone := by
  obtain ⟨hi, ho, hn⟩ := state_gone.mp hg
  refine state_gone.mpr ⟨fun hx => ?_, fun hx => ?_, Nat.lt_of_lt_of_le hn (apply_next p op)⟩
  · rcases apply_idle op hx with h1 | h1
    · exact hi h1
    · exact ho h1
  · rcases apply_out op hx with h1 | h1 | h1
    · exact ho h1
    · exact hi h1
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hn h1)

/--
**Gone stays gone**, over any sequence of operations.
-/
theorem state_gone_run {p : Pool κ} {id : ConnId} (hg : p.state id = .gone)
    (ops : List (PoolOp κ)) : (p.run ops).state id = .gone := by
  induction ops generalizing p with
  | nil => exact hg
  | cons op ops ih => exact ih (state_gone_apply hg op)

/--
A gone connection has no events: no sequence of operations hands it out or takes it back.
-/
theorem trace_gone {p : Pool κ} (h : p.WF) {id : ConnId} (hg : p.state id = .gone)
    (ops : List (PoolOp κ)) : p.trace id ops = [] := by
  induction ops generalizing p with
  | nil => rfl
  | cons op ops ih =>
    obtain ⟨h1, h2, -⟩ := out_step h id op
    have hg' := state_gone_apply hg op
    have ho := (state_gone.mp hg).2.1
    have ho' := (state_gone.mp hg').2.1
    simp only [trace, ih (apply_wf h op) hg', List.append_nil]
    cases he : p.eventOf id op with
    | none => rfl
    | some e =>
      cases e with
      | handedOut => exact absurd (h1 he).2 ho'
      | returned => exact absurd (h2 he).1 ho

/--
**A connection given back as not reusable is never handed out again** (nor taken back again), by
any sequence of operations.
-/
theorem giveBack_unreusable_never_again {p : Pool κ} (h : p.WF) {id : ConnId}
    (hid : id ∈ p.outIds) (now : Nat) (ops : List (PoolOp κ)) :
    ((p.giveBack id false now).1).trace id ops = [] :=
  trace_gone (giveBack_wf h id false now) (giveBack_unreusable_gone h hid now) ops

/--
A dropped connection is never handed out again (nor taken back again), by any sequence of
operations.
-/
theorem drop_never_again {p : Pool κ} (h : p.WF) {id : ConnId} (hid : id ∈ p.outIds)
    (ops : List (PoolOp κ)) : ((p.drop id).1).trace id ops = [] :=
  trace_gone (drop_wf h id) (drop_gone h hid) ops

/-! ## The connections an operation lets go, and closing -/

/--
The connections `op` lets go, for the shell to close: the expired idle ones for `take`, `giveBack`
and `sweep`, every idle one for `closeAll`, none for `drop`.
-/
def letGo (p : Pool κ) : PoolOp κ → List ConnId
  | .take origin now reuse => (p.take origin now reuse).2.2
  | .giveBack id reusable now => (p.giveBack id reusable now).2.2
  | .drop _ => []
  | .sweep now => (p.sweep now).2
  | .closeAll => p.closeAll.2

omit [DecidableEq κ] in
theorem nodup_map_inj {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hxy : f x = f y) : x = y := by
  induction l with
  | nil => nomatch hx
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (by rw [hxy]; exact List.mem_map.mpr ⟨y, hy', rfl⟩) h.1
    · exact absurd (by rw [← hxy]; exact List.mem_map.mpr ⟨x, hx', rfl⟩) h.1
    · exact ih h.2 hx' hy'

omit [DecidableEq κ] in
theorem sweep_idem (p : Pool κ) (now : Nat) : ((p.sweep now).1.sweep now).1 = (p.sweep now).1 := by
  simp only [sweep, expired, List.filter_filter]
  congr 2
  funext c
  by_cases hle : c.since + p.config.idleTimeoutMs ≤ now <;> simp [hle]

/--
What `sweep` lets go was idle, and is gone afterwards.
-/
theorem sweep_letGo {p : Pool κ} (h : p.WF) {now : Nat} {id : ConnId} (hid : id ∈ (p.sweep now).2) :
    p.state id = .idle ∧ (p.sweep now).1.state id = .gone := by
  obtain ⟨c, hc, rfl⟩ : ∃ c, c ∈ p.idle.filter (p.expired now ·) ∧ c.id = id := by
    simpa [sweep] using hid
  rw [List.mem_filter] at hc
  have hidle : c.id ∈ p.idleIds := mem_idleIds.mpr ⟨c, hc.1, rfl⟩
  have hnodup : p.idleIds.Nodup := (List.nodup_append.mp h.nodup).1
  refine ⟨state_idle.mpr hidle, state_gone.mpr ⟨?_, h.not_out_of_idle hidle, ?_⟩⟩
  · intro hx
    obtain ⟨d, hd, hdc⟩ : ∃ d, d ∈ p.idle.filter (!p.expired now ·) ∧ d.id = c.id := by
      simpa [idleIds] using hx
    rw [List.mem_filter] at hd
    have := nodup_map_inj hnodup hd.1 hc.1 hdc
    subst this
    simp [hc.2] at hd
  · exact h.lt_next _ (List.mem_append_left _ hidle)

/--
**Every connection an operation lets go was idle, and is gone afterwards**, so the connections the
shell closes are exactly ones nobody holds and nobody will be handed.
-/
theorem letGo_gone {p : Pool κ} (h : p.WF) (op : PoolOp κ) {id : ConnId} (hid : id ∈ p.letGo op) :
    p.state id = .idle ∧ (p.apply op).state id = .gone := by
  cases op with
  | take origin now reuse =>
    obtain ⟨hi, hg⟩ := sweep_letGo h (now := now) hid
    refine ⟨hi, ?_⟩
    have := state_gone_apply hg (.take origin now reuse)
    simpa [apply, take, sweep_idem] using this
  | giveBack i reusable now =>
    obtain ⟨hi, hg⟩ := sweep_letGo h (now := now) hid
    refine ⟨hi, ?_⟩
    have := state_gone_apply hg (.giveBack i reusable now)
    simpa [apply, giveBack, sweep_idem] using this
  | drop i => nomatch hid
  | sweep now => exact sweep_letGo h hid
  | closeAll =>
    have hidle : id ∈ p.idleIds := hid
    refine ⟨state_idle.mpr hidle, state_gone.mpr ⟨by simp [apply, closeAll, idleIds],
      h.not_out_of_idle hidle, h.lt_next _ (List.mem_append_left _ hidle)⟩⟩

/--
**Once closed, a pool stays closed**, and so hands nothing out again (`take_closed`).
-/
theorem apply_closed {p : Pool κ} (hc : p.closed = true) (op : PoolOp κ) :
    (p.apply op).closed = true := by
  cases op with
  | take origin now reuse => simp [apply, take, checkout, hc]
  | giveBack i reusable now =>
    show ((p.sweep now).1.checkin i reusable now).1.closed = true
    rcases hfind : (p.sweep now).1.out.find? (·.1 = i) with _ | ⟨j, o⟩
    · rw [checkin_none hfind]
      exact hc
    · by_cases hcond : (reusable && !(p.sweep now).1.closed &&
          decide ((p.sweep now).1.idleCount o < (p.sweep now).1.config.maxIdle)) = true
      · rw [checkin_idle hfind hcond]
        exact hc
      · rw [checkin_dropped hfind hcond]
        exact hc
  | drop i =>
    simp only [apply, drop]
    split <;> exact hc
  | sweep now => exact hc
  | closeAll => rfl

theorem run_closed {p : Pool κ} (hc : p.closed = true) (ops : List (PoolOp κ)) :
    (p.run ops).closed = true := by
  induction ops generalizing p with
  | nil => exact hc
  | cons op ops ih => exact ih (apply_closed hc op)

end LeanHttp.Pool
