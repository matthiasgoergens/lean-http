module

public import LeanHttp.Codec.Response

@[expose] public section

/-!
# `feed` computes what `stepByte` means

`Parser.feed` reads body bytes in bulk; `Parser.run` reads every byte with `Parser.stepByte`.  They
reach the same state and emit the same observations (`obs`: events with body bytes split into single
bytes), which is `feed_eq_run`.  Since `run` is a fold over the bytes, it follows that every way of
cutting the input into pieces gives the same state and observations (`feed_append`, `feedAll_eq`).
`feed` makes at most one round per byte of input (`feedSteps_le`).
-/

namespace LeanHttp.Codec


/--
What a client observes of a response, with body bytes one at a time: the events with every `body`
event split into its bytes, so that two runs that cut the body into different events have the same
observations.
-/
inductive Obs where
  /-- The final head. -/
  | head (h : Head)
  /-- One body byte. -/
  | byte (b : UInt8)
  /-- The end of the response. -/
  | done
  /-- The rejection of the response. -/
  | error (e : Error)

/--
The observations of one event.
-/
def Event.obs : Event → List Obs
  | .head h => [.head h]
  | .body bytes => bytes.data.toList.map .byte
  | .done => [.done]
  | .error e => [.error e]

/--
The observations of a sequence of events.
-/
def obsOf (es : Array Event) : List Obs :=
  es.toList.flatMap Event.obs

attribute [simp] Event.obs

@[simp] theorem obsOf_empty : obsOf #[] = [] := rfl

@[simp] theorem obsOf_append (a b : Array Event) : obsOf (a ++ b) = obsOf a ++ obsOf b := by
  simp [obsOf]

@[simp] theorem obsOf_push (a : Array Event) (e : Event) : obsOf (a.push e) = obsOf a ++ e.obs := by
  simp [obsOf]

@[simp] theorem obsOf_singleton (e : Event) : obsOf #[e] = e.obs := by
  simp [obsOf]

@[simp] theorem obsOf_pair (e e' : Event) : obsOf #[e, e'] = e.obs ++ e'.obs := by
  simp [obsOf]

@[simp] theorem single_data_toList (b : UInt8) : (Parser.single b).data.toList = [b] := rfl

namespace Parser

/-! ## `run` -/

@[simp] theorem run_nil (p : Parser) : p.run [] = (p, #[]) := rfl

theorem run_cons (p : Parser) (b : UInt8) (bs : List UInt8) :
    p.run (b :: bs) = ((p.stepByte b).1.run bs |>.1, (p.stepByte b).2 ++ ((p.stepByte b).1.run bs).2) :=
  rfl

/--
Reading `xs ++ ys` is reading `xs`, then `ys`.
-/
theorem run_append (p : Parser) (xs ys : List UInt8) :
    p.run (xs ++ ys) = (((p.run xs).1.run ys).1, (p.run xs).2 ++ ((p.run xs).1.run ys).2) := by
  induction xs generalizing p with
  | nil => simp
  | cons b bs ih => simp [run_cons, ih, Array.append_assoc]

/-! ## Runs of body bytes -/

theorem run_fixed (p : Parser) (r : Nat) (xs : List UInt8) (hp : p.phase = .body (.fixed (r + 1)))
    (hlen : xs.length ≤ r + 1) :
    (p.run xs).1 = { p with
      phase := if xs.length = r + 1 then .done else .body (.fixed (r + 1 - xs.length)),
      delivered := p.delivered + xs.length } ∧
    obsOf (p.run xs).2 = xs.map .byte ++ (if xs.length = r + 1 then [.done] else []) := by
  induction xs generalizing p r with
  | nil =>
    cases p
    simp_all
  | cons b bs ih =>
    rcases r with _ | r
    · have : bs = [] := by cases bs with | nil => rfl | cons _ _ => simp at hlen
      subst this
      simp [run_cons, stepByte, hp]
    · have h1 := ih { p with phase := .body (.fixed (r + 1)), delivered := p.delivered + 1 } r rfl
        (by simp at hlen; omega)
      simp only [run_cons, stepByte, hp]
      simp only [show ¬ r + 1 + 1 ≤ 1 by omega, ite_false, Nat.add_sub_cancel] at h1 ⊢
      refine ⟨?_, ?_⟩
      · rw [h1.1]
        simp only [List.length_cons]
        congr 1
        · by_cases hb : bs.length = r + 1 <;> simp [hb]
        · omega
      · rw [obsOf_append, h1.2]
        by_cases hb : bs.length = r + 1 <;> simp [hb]

theorem run_chunkData (p : Parser) (r : Nat) (xs : List UInt8)
    (hp : p.phase = .body (.chunked (.data (r + 1)))) (hlen : xs.length ≤ r + 1) :
    (p.run xs).1 = { p with
      phase := if xs.length = r + 1 then .body (.chunked .dataCR)
        else .body (.chunked (.data (r + 1 - xs.length))),
      delivered := p.delivered + xs.length } ∧
    obsOf (p.run xs).2 = xs.map .byte := by
  induction xs generalizing p r with
  | nil =>
    cases p
    simp_all
  | cons b bs ih =>
    rcases r with _ | r
    · have : bs = [] := by cases bs with | nil => rfl | cons _ _ => simp at hlen
      subst this
      simp [run_cons, stepByte, hp, stepChunk]
    · have h1 := ih { p with phase := .body (.chunked (.data (r + 1))), delivered := p.delivered + 1 } r
        rfl (by simp at hlen; omega)
      simp only [run_cons, stepByte, hp, stepChunk]
      simp only [show ¬ r + 1 + 1 ≤ 1 by omega, ite_false, Nat.add_sub_cancel] at h1 ⊢
      refine ⟨?_, ?_⟩
      · rw [h1.1]
        simp only [List.length_cons]
        congr 1
        · by_cases hb : bs.length = r + 1 <;> simp [hb]
        · omega
      · rw [obsOf_append, h1.2]
        simp

theorem run_untilClose (p : Parser) (r : Nat) (xs : List UInt8)
    (hp : p.phase = .body (.untilClose (r + 1))) (hlen : xs.length ≤ r + 1) :
    (p.run xs).1 = { p with
      phase := .body (.untilClose (r + 1 - xs.length)),
      delivered := p.delivered + xs.length } ∧
    obsOf (p.run xs).2 = xs.map .byte := by
  induction xs generalizing p r with
  | nil =>
    cases p
    simp_all
  | cons b bs ih =>
    rcases r with _ | r
    · have : bs = [] := by cases bs with | nil => rfl | cons _ _ => simp at hlen
      subst this
      simp [run_cons, stepByte, hp]
    · have h1 := ih { p with phase := .body (.untilClose (r + 1)), delivered := p.delivered + 1 } r
        rfl (by simp at hlen; omega)
      simp only [run_cons, stepByte, hp, Nat.add_one_ne_zero, ite_false]
      simp only [Nat.add_sub_cancel] at h1 ⊢
      refine ⟨?_, ?_⟩
      · rw [h1.1]
        simp only [List.length_cons]
        congr 1
        · simp only [Body.untilClose.injEq, Phase.body.injEq]
          omega
        · omega
      · rw [obsOf_append, h1.2]
        simp

theorem run_done (p : Parser) (xs : List UInt8) (hp : p.phase = .done) (hxs : xs ≠ []) :
    (p.run xs).1 = { p with extra := true } ∧ obsOf (p.run xs).2 = [] := by
  induction xs generalizing p with
  | nil => exact absurd rfl hxs
  | cons b bs ih =>
    rcases bs with _ | ⟨b', bs⟩
    · simp [run_cons, stepByte, hp]
    · have h1 := ih { p with extra := true } hp (by simp)
      simp only [run_cons, stepByte, hp] at h1 ⊢
      simp_all

theorem run_failed (p : Parser) (xs : List UInt8) (e : Error) (hp : p.phase = .failed e) :
    (p.run xs).1 = p ∧ obsOf (p.run xs).2 = [] := by
  induction xs with
  | nil => simp
  | cons b bs ih => simp_all [run_cons, stepByte]

/-! ## `feed` -/

theorem data_extract_toList (bytes : ByteArray) (i j : Nat) :
    (bytes.extract i j).data.toList = (bytes.data.toList.drop i).take (j - i) := by
  simp [ByteArray.data_extract, Array.toList_extract]

theorem drop_eq_cons (bytes : ByteArray) (i : Nat) (h : i < bytes.size) :
    bytes.data.toList.drop i = bytes[i] :: bytes.data.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp [ByteArray.getElem_eq_getElem_data]

theorem length_drop (bytes : ByteArray) (i : Nat) :
    (bytes.data.toList.drop i).length = bytes.size - i := by
  simp

theorem take_drop_split (l : List UInt8) (i k : Nat) :
    l.drop i = (l.drop i).take k ++ l.drop (i + k) := by
  rw [← List.drop_drop, List.take_append_drop]

/--
The loop of `feed`, from any position: the same state as `run` on the rest of the input, and the
observations of `acc` followed by those of `run`.
-/
theorem feedLoop_eq (bytes : ByteArray) (p : Parser) (i : Nat) (acc : Array Event) (steps : Nat) :
    (feedLoop bytes p i acc steps).1 = (p.run (bytes.data.toList.drop i)).1 ∧
    obsOf (feedLoop bytes p i acc steps).2.1 =
      obsOf acc ++ obsOf (p.run (bytes.data.toList.drop i)).2 := by
  fun_induction feedLoop bytes p i acc steps with
  | case1 p i acc steps h avail r hp hle ih =>
    rw [take_drop_split bytes.data.toList i (r + 1), run_append]
    have hlen : ((bytes.data.toList.drop i).take (r + 1)).length = r + 1 := by
      simp [List.length_take]; omega
    have hf := run_fixed p r ((bytes.data.toList.drop i).take (r + 1)) hp (by omega)
    rw [hlen] at hf
    simp only [ite_true] at hf
    rw [hf.1, Nat.add_comm i (r + 1)] at *
    refine ⟨ih.1, ?_⟩
    rw [ih.2]
    simp only [obsOf_push, obsOf_append, hf.2, Event.obs, data_extract_toList,
      List.append_assoc, List.singleton_append]
    simp [Nat.add_comm]
  | case2 p i acc steps h avail r hp hle =>
    have hlen : (bytes.data.toList.drop i).length = avail := length_drop bytes i
    have hf := run_fixed p r (bytes.data.toList.drop i) hp (by omega)
    rw [hlen] at hf
    simp only [show ¬ avail = r + 1 by omega, ite_false] at hf
    refine ⟨hf.1.symm, ?_⟩
    rw [hf.2]
    have ht : (bytes.data.toList.drop i).take (bytes.size - i) = bytes.data.toList.drop i :=
      List.take_of_length_le (by simp)
    simp [ht]
  | case3 p i acc steps h avail r hp hle ih =>
    rw [take_drop_split bytes.data.toList i (r + 1), run_append]
    have hlen : ((bytes.data.toList.drop i).take (r + 1)).length = r + 1 := by
      simp [List.length_take]; omega
    have hf := run_chunkData p r ((bytes.data.toList.drop i).take (r + 1)) hp (by omega)
    rw [hlen] at hf
    simp only [ite_true] at hf
    rw [hf.1, Nat.add_comm i (r + 1)] at *
    refine ⟨ih.1, ?_⟩
    rw [ih.2]
    simp [hf.2, Nat.add_sub_cancel]
  | case4 p i acc steps h avail r hp hle =>
    have hlen : (bytes.data.toList.drop i).length = avail := length_drop bytes i
    have hf := run_chunkData p r (bytes.data.toList.drop i) hp (by omega)
    rw [hlen] at hf
    simp only [show ¬ avail = r + 1 by omega, ite_false] at hf
    refine ⟨hf.1.symm, ?_⟩
    rw [hf.2]
    have ht : (bytes.data.toList.drop i).take (bytes.size - i) = bytes.data.toList.drop i :=
      List.take_of_length_le (by simp)
    simp [ht]
  | case5 p i acc steps h avail r hp hle ih =>
    rw [take_drop_split bytes.data.toList i (r + 1), run_append]
    have hlen : ((bytes.data.toList.drop i).take (r + 1)).length = r + 1 := by
      simp [List.length_take]; omega
    have hf := run_untilClose p r ((bytes.data.toList.drop i).take (r + 1)) hp (by omega)
    rw [hlen] at hf
    simp only [Nat.sub_self] at hf
    rw [hf.1, Nat.add_comm i (r + 1)] at *
    refine ⟨ih.1, ?_⟩
    rw [ih.2]
    simp [hf.2, Nat.add_sub_cancel]
  | case6 p i acc steps h avail r hp hle =>
    have hlen : (bytes.data.toList.drop i).length = avail := length_drop bytes i
    have hf := run_untilClose p r (bytes.data.toList.drop i) hp (by omega)
    rw [hlen] at hf
    refine ⟨hf.1.symm, ?_⟩
    rw [hf.2]
    have ht : (bytes.data.toList.drop i).take (bytes.size - i) = bytes.data.toList.drop i :=
      List.take_of_length_le (by simp)
    simp [ht]
  | case7 p i acc steps h hp =>
    have hd := run_done p (bytes.data.toList.drop i) hp (by simp; omega)
    exact ⟨hd.1.symm, by simp [hd.2]⟩
  | case8 p i acc steps h e hp =>
    have hd := run_failed p (bytes.data.toList.drop i) e hp
    exact ⟨hd.1.symm, by simp [hd.2]⟩
  | case9 p i acc steps h r _ _ _ _ _ ih =>
    rw [drop_eq_cons bytes i h, run_cons]
    refine ⟨ih.1, ?_⟩
    rw [ih.2]
    simp only [obsOf_append, List.append_assoc]
    rfl
  | case10 p i acc steps h =>
    have : bytes.data.toList.drop i = [] := by simp; omega
    simp [this]

/--
`feed` reaches the state `run` reaches on the same bytes, with the same observations.
-/
theorem feed_eq_run (p : Parser) (bytes : ByteArray) :
    (p.feed bytes).1 = (p.run bytes.data.toList).1 ∧
    obsOf (p.feed bytes).2 = obsOf (p.run bytes.data.toList).2 := by
  have h := feedLoop_eq bytes p 0 #[] 0
  simp only [List.drop_zero, obsOf_empty, List.nil_append] at h
  exact h

/--
**Split invariance.**  Feeding `a ++ b` reaches the same state as feeding `a` then `b`, with the same
observations: the events are the same up to how body bytes are split between `body` events.
-/
theorem feed_append (p : Parser) (a b : ByteArray) :
    (p.feed (a ++ b)).1 = ((p.feed a).1.feed b).1 ∧
    obsOf (p.feed (a ++ b)).2 = obsOf (p.feed a).2 ++ obsOf ((p.feed a).1.feed b).2 := by
  have hab := feed_eq_run p (a ++ b)
  have ha := feed_eq_run p a
  have hb := feed_eq_run (p.feed a).1 b
  rw [ByteArray.toList_data_append, run_append] at hab
  refine ⟨?_, ?_⟩
  · rw [hab.1, hb.1, ha.1]
  · rw [hab.2, obsOf_append, ha.2, hb.2, ha.1]

/--
**Split invariance, for any number of pieces.**  Feeding pieces one after another reaches the same
state as feeding them joined, with the same observations.
-/
theorem feedAll_eq (p : Parser) (pieces : List ByteArray) :
    (p.feedAll pieces).1 = (p.feed (pieces.foldl (· ++ ·) .empty)).1 ∧
    obsOf (p.feedAll pieces).2 = obsOf (p.feed (pieces.foldl (· ++ ·) .empty)).2 := by
  suffices h : ∀ (q : Parser) (init : ByteArray) (hq : q = (p.feed init).1),
      (q.feedAll pieces).1 = (p.feed (pieces.foldl (· ++ ·) init)).1 ∧
      obsOf (p.feed init).2 ++ obsOf (q.feedAll pieces).2 =
        obsOf (p.feed (pieces.foldl (· ++ ·) init)).2 by
    have h0 := h p .empty (by
      have := feed_eq_run p .empty
      simp at this
      exact this.1.symm)
    have he : obsOf (p.feed .empty).2 = [] := by
      have := feed_eq_run p .empty
      simpa using this.2
    rw [he, List.nil_append] at h0
    exact h0
  induction pieces with
  | nil => intro q init hq; simp [feedAll, hq]
  | cons piece pieces ih =>
    intro q init hq
    have hs := feed_append p init piece
    have h1 := ih (q.feed piece).1 (init ++ piece) (by rw [hs.1, hq])
    simp only [List.foldl_cons]
    refine ⟨h1.1, ?_⟩
    rw [← h1.2, hs.2, hq]
    simp [feedAll, List.append_assoc]

/-! ## The number of rounds -/

theorem feedLoop_steps (bytes : ByteArray) (p : Parser) (i : Nat) (acc : Array Event)
    (steps : Nat) : (feedLoop bytes p i acc steps).2.2 ≤ steps + (bytes.size - i) := by
  fun_induction feedLoop bytes p i acc steps <;> simp_all <;> omega

/--
**Bounded rounds.**  `feed` makes at most one round per input byte.  A round is one `stepByte`, or
one slice of body bytes (which copies the bytes it delivers).  `stepByte` has no loop of its own, but
where a field line ends it reverses that line's buffers, and where a head ends it examines the
head's fields; both are bounded by the limits in `Config`.  The theorem bounds the rounds; what a
round costs is read off the code, not proved.
-/
theorem feedSteps_le (p : Parser) (bytes : ByteArray) : p.feedSteps bytes ≤ bytes.size := by
  have := feedLoop_steps bytes p 0 #[] 0
  simpa [feedSteps] using this

/-! ## Body events are never empty -/

/--
No body event in `es` is empty.
-/
def NoEmptyBody (es : Array Event) : Prop :=
  ∀ e ∈ es, ∀ bytes, e = .body bytes → 0 < bytes.size

theorem noEmptyBody_append {a b : Array Event} (ha : NoEmptyBody a) (hb : NoEmptyBody b) :
    NoEmptyBody (a ++ b) := by
  intro e he bytes hbe
  rcases Array.mem_append.mp he with he | he
  · exact ha e he bytes hbe
  · exact hb e he bytes hbe

theorem stepByte_noEmptyBody (p : Parser) (b : UInt8) : NoEmptyBody (p.stepByte b).2 := by
  intro e he bytes hbe
  unfold stepByte at he
  split at he
  · split at he
    · simp at he
    · simp [fail] at he; subst he; cases hbe
    · unfold startBody at he
      dsimp only at he
      split at he <;> (try split at he) <;> simp at he <;>
        (try (rcases he with rfl | rfl)) <;> (try subst he) <;> cases hbe
  all_goals
    (try split at he) <;> (try split at he) <;> simp [fail] at he <;>
      (try (rcases he with rfl | rfl)) <;> (try subst he) <;> cases hbe <;> exact Nat.zero_lt_one

theorem feedLoop_noEmptyBody (bytes : ByteArray) (p : Parser) (i : Nat) (acc : Array Event)
    (steps : Nat) (hacc : NoEmptyBody acc) : NoEmptyBody (feedLoop bytes p i acc steps).2.1 := by
  fun_induction feedLoop bytes p i acc steps with
  | case1 p i acc steps h avail r hp hle ih =>
    apply ih
    intro e he x hx
    simp only [Array.mem_push] at he
    rcases he with (he | rfl) | rfl
    · exact hacc e he x hx
    · cases hx; simp; omega
    · cases hx
  | case2 p i acc steps h avail r hp hle =>
    intro e he x hx
    simp only [Array.mem_push] at he
    rcases he with he | rfl
    · exact hacc e he x hx
    · cases hx; simp; omega
  | case3 p i acc steps h avail r hp hle ih =>
    apply ih
    intro e he x hx
    simp only [Array.mem_push] at he
    rcases he with he | rfl
    · exact hacc e he x hx
    · cases hx; simp; omega
  | case4 p i acc steps h avail r hp hle =>
    intro e he x hx
    simp only [Array.mem_push] at he
    rcases he with he | rfl
    · exact hacc e he x hx
    · cases hx; simp; omega
  | case5 p i acc steps h avail r hp hle ih =>
    apply ih
    intro e he x hx
    simp only [Array.mem_push] at he
    rcases he with he | rfl
    · exact hacc e he x hx
    · cases hx; simp; omega
  | case6 p i acc steps h avail r hp hle =>
    intro e he x hx
    simp only [Array.mem_push] at he
    rcases he with he | rfl
    · exact hacc e he x hx
    · cases hx; simp; omega
  | case7 => exact hacc
  | case8 => exact hacc
  | case9 p i acc steps h r _ _ _ _ _ ih =>
    exact ih (noEmptyBody_append hacc (stepByte_noEmptyBody _ _))
  | case10 => exact hacc

/--
**No empty body events.**  `feed` and `finish` never emit an empty `body` event, so two runs with
the same observations emit the same events but for how body bytes are grouped into `body` events.
-/
theorem feed_noEmptyBody (p : Parser) (bytes : ByteArray) : NoEmptyBody (p.feed bytes).2 :=
  feedLoop_noEmptyBody bytes p 0 #[] 0 (by intro e he; simp at he)

theorem finish_noEmptyBody (p : Parser) : NoEmptyBody p.finish.2 := by
  intro e he x hx
  unfold finish at he
  split at he <;> simp [fail] at he <;> subst he <;> cases hx

end Parser

end LeanHttp.Codec
