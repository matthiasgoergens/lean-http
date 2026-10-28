module

import all LeanHttp.Exchange
import all LeanHttp.Exchange.Proofs

/-!
# Deadlines ahead

A property of the exchange core beyond those of `LeanHttp.Exchange.Proofs`, which this module
builds on.  Like those, it holds whatever the HTTP/1.1 machine does.

**A live exchange has a deadline ahead** (`Reachable.deadlineAhead`).  Every reachable exchange that
has not ended has a next deadline strictly after its clock and no later than the deadline of the
whole exchange.  It rests on the gap being positive (`ExchangeConfig.gapMs_pos`) and on a companion
invariant of the timers (`Timers`): a write's deadline is set only while a write is in flight, and
the drain's only while draining, when the whole request has been written.
-/

namespace LeanHttp.Exchange

open Std.Http LeanHttpProto.Http.Protocol

/-! ## The timers' invariant -/

/-- The invariant of the timers, at every point of every step from `begin`. -/
structure Timers (ex : Exchange) : Prop where
  /-- A write's deadline is set only while a write is in flight. -/
  writeBy : ex.writeBy.isSome = true → ex.writeInFlight.isSome = true
  /-- The write in flight is not empty. -/
  inFlightPos : ∀ k, ex.writeInFlight = some k → 0 < k
  /-- The drain's deadline is set only while draining. -/
  drainBy : ex.drainBy.isSome = true → ex.phase = .draining
  /-- While draining, the whole request has been written, -/
  drainingWritten : ex.phase = .draining → ex.written = ex.request.size
  /-- no write is in flight, -/
  drainingIdle : ex.phase = .draining → ex.writeInFlight = none
  /-- and the final head was delivered. -/
  drainingHead : ex.phase = .draining → ex.head.isSome = true

/-- The fields `Timers` depends on. -/
structure TAgree (a b : Exchange) : Prop where
  phase : b.phase = a.phase
  written : b.written = a.written
  request : b.request = a.request
  head : b.head = a.head
  writeInFlight : b.writeInFlight = a.writeInFlight
  writeBy : b.writeBy = a.writeBy
  drainBy : b.drainBy = a.drainBy

/-- `TAgree` for an update of other fields. -/
macro "tagree_rfl" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem Timers.agree {a b : Exchange} (h : Timers a) (ha : TAgree a b) : Timers b where
  writeBy := by rw [ha.writeBy, ha.writeInFlight]; exact h.writeBy
  inFlightPos := by rw [ha.writeInFlight]; exact h.inFlightPos
  drainBy := by rw [ha.drainBy, ha.phase]; exact h.drainBy
  drainingWritten := by rw [ha.phase, ha.written, ha.request]; exact h.drainingWritten
  drainingIdle := by rw [ha.phase, ha.writeInFlight]; exact h.drainingIdle
  drainingHead := by rw [ha.phase, ha.head]; exact h.drainingHead

/-- An exchange that ended, with its timers cleared. -/
theorem Timers.stop {ex : Exchange} (h : Timers ex) {p : Phase} (hp : p = .draining → False) :
    Timers { ex with phase := p, writeBy := none, readBy := none, drainBy := none } where
  writeBy := by simp
  inFlightPos := h.inFlightPos
  drainBy := by simp
  drainingWritten := fun h' => absurd h' hp
  drainingIdle := fun h' => absurd h' hp
  drainingHead := fun h' => absurd h' hp

theorem failNow_timers {s : S} (c : Cause) (d : String) (h : Timers s.1) :
    Timers ((failNow c d).run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  rw [failNow_run]
  split
  · exact h
  · exact Timers.stop h (fun h' => (by cases h'))

theorem finishNow_timers {s : S} (r : Bool) (h : Timers s.1) :
    Timers ((finishNow r).run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  rw [finishNow_run]
  split
  · exact h
  · exact Timers.stop h (fun h' => (by cases h'))

theorem failOrDrop_timers {s : S} (c : Cause) (d : String) (h : Timers s.1) :
    Timers ((failOrDrop c d).run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [failOrDrop, bind_run, getEx_run]
  split
  · exact finishNow_timers false h
  · exact failNow_timers c d h

theorem stopUpload_timers {s : S} (h : Timers s.1) : Timers (stopUpload.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [stopUpload, modifyEx_run]
  exact ⟨by simp, h.inFlightPos, h.drainBy, h.drainingWritten, h.drainingIdle, h.drainingHead⟩

/-- Delivering the final head: no head yet, so not draining, so no drain deadline. -/
theorem Timers.receive {ex : Exchange} (h : Timers ex) (hh : ex.head.isSome = false)
    (head : Response.Head) (fr : Framing) (early : Bool) :
    Timers { ex with head := some head, framing := fr, phase := .receiving, early } := by
  have hdb : ex.drainBy.isSome = false := by
    cases hd : ex.drainBy.isSome
    · rfl
    · have := h.drainingHead (h.drainBy hd)
      rw [hh] at this
      cases this
  exact ⟨h.writeBy, h.inFlightPos, fun h' => (by simp only at h'; rw [hdb] at h'; cases h'),
    fun h' => (by cases h'), fun h' => (by cases h'), fun h' => (by cases h')⟩

theorem handleH1Event_timers {s : S} (e : H1.Event .sending) (h : Timers s.1) :
    Timers ((handleH1Event e).run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  cases e with
  | endHeaders head =>
    simp only [handleH1Event, bind_run, getEx_run]
    rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;> simp only [ht, ↓reduceIte]
    · exact h
    rcases Bool.eq_false_or_eq_true head.status.isInformational with hi | hi <;>
      simp only [hi, ↓reduceIte, Bool.false_eq_true]
    · rcases Bool.eq_false_or_eq_true (head.status.toCode == 101) with hc | hc <;>
        simp only [hc, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run]
      · exact failNow_timers _ _ h
      · have h' := h.agree (b := { ex with interim := ex.interim + 1 }) (by tagree_rfl)
        by_cases hn : ex.interim + 1 > ex.config.maxInterim <;> simp only [hn, ↓reduceIte, bind_run]
        · exact failNow_timers _ _ h'
        · exact h'
    · rcases Bool.eq_false_or_eq_true ex.head.isSome with hh | hh <;>
        simp only [hh, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run, emit_run]
      · exact failNow_timers _ _ h
      · have h' := h.receive hh head (Framing.ofResponse ex.method head)
          (decide (ex.written < ex.request.size))
        split
        · rename_i n _
          by_cases hn : n > ex.config.maxBody <;> simp only [hn, ↓reduceIte, bind_run]
          · exact failNow_timers _ _ h'
          · exact h'
        · exact h'
  | closeBody =>
    simp only [handleH1Event, bind_run, getEx_run]
    rcases Bool.eq_false_or_eq_true ex.head.isSome with hh | hh <;>
      simp only [hh, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run]
    · exact h.agree (by tagree_rfl)
    · exact h
  | failed err =>
    simp only [handleH1Event, bind_run]
    exact failOrDrop_timers _ _ h
  | _ => exact h

theorem handleH1Events_timers {s : S} (events : Array (H1.Event .sending)) (h : Timers s.1) :
    Timers ((handleH1Events events).run s).2.1 := by
  unfold handleH1Events
  rw [← Array.foldlM_toList]
  generalize events.toList = l
  generalize false = b
  induction l generalizing s b with
  | nil => exact h
  | cons e l ih =>
    simp only [List.foldlM_cons, bind_run]
    exact ih (handleH1Event_timers e h) _

theorem pullOnce_timers {s : S} (h : Timers s.1) : Timers (pullOnce.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [pullOnce, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true (ex.terminal || ex.bodyDone || !ex.machine.canPullBodyNow)
    with hc | hc <;> simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · exact h
  split
  · rcases Bool.eq_false_or_eq_true (ex.credit == 0) with hc | hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true]
    · split
      · rename_i pulled _
        rcases Bool.eq_false_or_eq_true (!pulled.chunk.data.isEmpty) with he | he <;>
          simp only [he, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run]
        · exact h
        · exact h.agree (by tagree_rfl)
      · simp only [bind_run, setEx_run]
        exact h.agree (by tagree_rfl)
    · rcases Bool.eq_false_or_eq_true (ex.announcedOver ex.bodyBytes ex.config.maxBody) with ho | ho <;>
        simp only [ho, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run]
      · exact failNow_timers _ _ h
      · have h1 := h.agree (b := { ex with machine := ex.machine.pullBody.1 }) (by tagree_rfl)
        split
        · rename_i pulled _
          by_cases hn : ex.bodyBytes + pulled.chunk.data.size > ex.config.maxBody <;>
            simp only [hn, ↓reduceIte, bind_run, setEx_run]
          · exact failNow_timers _ _ h1
          · have h2 := h1.agree (b := { ex with
              machine := ex.machine.pullBody.1,
              credit := ex.credit - min ex.credit pulled.chunk.data.size,
              bodyBytes := ex.bodyBytes + pulled.chunk.data.size,
              bodyDone := ex.bodyDone || pulled.final }) (by tagree_rfl)
            rcases Bool.eq_false_or_eq_true pulled.chunk.data.isEmpty with he | he <;>
              simp only [he, ↓reduceIte, Bool.false_eq_true, bind_run, emit_run]
            · exact h2
            · exact h2
        · exact h1
  · rcases Bool.eq_false_or_eq_true (ex.announcedOver ex.drained ex.config.drainBytes) with ho | ho <;>
      simp only [ho, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run]
    · exact finishNow_timers false h
    · have h1 := h.agree (b := { ex with machine := ex.machine.pullBody.1 }) (by tagree_rfl)
      split
      · rename_i pulled _
        simp only [bind_run, setEx_run]
        have h2 := h1.agree (b := { ex with
          machine := ex.machine.pullBody.1,
          drained := ex.drained + pulled.chunk.data.size,
          bodyDone := ex.bodyDone || pulled.final }) (by tagree_rfl)
        by_cases hn : ex.drained + pulled.chunk.data.size > ex.config.drainBytes <;>
          simp only [hn, ↓reduceIte, bind_run]
        · exact finishNow_timers false h2
        · exact h2
      · exact h1
  · exact h

theorem pullAvailable_timers {s : S} (p : Bool) (h : Timers s.1) :
    Timers ((pullAvailable p).run s).2.1 := by
  show Timers (loopWhile pullRound (p, s)).1.2.1
  apply loopWhile_inv pullRound (fun x => Timers x.2.1) _ (p, s) h
  intro ⟨q, s'⟩ hs
  simp only [pullRound]
  have := pullOnce_timers (s := s') hs
  split <;> simp_all

theorem settle_timers {s : S} (h : Timers s.1) : Timers (settle.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [settle, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;> simp only [ht, ↓reduceIte]
  · exact h
  cases hp : ex.phase <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_and, Bool.false_and]
  all_goals
    first
    | (rcases Bool.eq_false_or_eq_true ex.bodyDone with hb | hb <;>
        simp only [hb, ↓reduceIte, Bool.false_eq_true]
       · exact finishNow_timers true h)
    | skip
  all_goals
    rcases Bool.eq_false_or_eq_true ex.inputEnded with hi | hi <;>
      simp only [hi, ↓reduceIte, Bool.false_eq_true]
  all_goals
    first
    | exact h
    | (rcases Bool.eq_false_or_eq_true (ex.credit == 0 && ex.machine.canPullBodyNow) with hc | hc <;>
        simp only [hc, ↓reduceIte, Bool.false_eq_true]
       · exact h)
    | skip
  all_goals
    rcases Bool.eq_false_or_eq_true ex.machine.failed with hf | hf <;>
      simp only [hf, ↓reduceIte, Bool.false_eq_true] <;> exact failOrDrop_timers _ _ h

theorem absorbOnce_timers {s : S} (h : Timers s.1) : Timers (absorbOnce.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [absorbOnce, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact h
  simp only [bind_run, setEx_run]
  have h1 := h.agree (b := { ex with machine := ex.machine.step.1 }) (by tagree_rfl)
  have h2 := handleH1Events_timers ex.machine.step.2.events (s := ({ ex with machine := ex.machine.step.1 }, acts)) h1
  generalize (handleH1Events ex.machine.step.2.events).run
    ({ ex with machine := ex.machine.step.1 }, acts) = x at h2 ⊢
  have h3 := pullAvailable_timers false h2
  generalize (pullAvailable false).run x.2 = y at h3 ⊢
  simp only [getEx_run]
  have h4 := h3.agree (b := { y.2.1 with machine := y.2.1.machine.takeEvents.1 }) (by tagree_rfl)
  have h5 := handleH1Events_timers y.2.1.machine.takeEvents.2
    (s := ({ y.2.1 with machine := y.2.1.machine.takeEvents.1 }, y.2.2)) h4
  generalize (handleH1Events y.2.1.machine.takeEvents.2).run
    ({ y.2.1 with machine := y.2.1.machine.takeEvents.1 }, y.2.2) = z at h5 ⊢
  exact h5

theorem absorb_timers {s : S} (h : Timers s.1) : Timers (absorb.run s).2.1 := by
  show Timers (settle.run (loopWhile absorbOnce.run s).1).2.1
  apply settle_timers
  exact loopWhile_inv _ (fun x => Timers x.1) (fun _ h => absorbOnce_timers h) s h

theorem expireOne_timers {s : S} (h : Timers s.1) : Timers (expireOne.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [expireOne, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact h
  split
  · split
    · simp only [bind_run]; exact finishNow_timers false h
    · exact h
  · split
    · exact h
    · split
      · simp only [bind_run]; exact stopUpload_timers h
      · simp only [bind_run]; exact failNow_timers _ _ h
    · simp only [bind_run]; exact failNow_timers _ _ h

theorem expire_timers {s : S} (h : Timers s.1) : Timers (expire.run s).2.1 := by
  simp only [expire, bind_run]
  have h1 := expireOne_timers h
  generalize expireOne.run s = x at h1 ⊢
  obtain ⟨b, x⟩ := x
  cases b
  · exact h1
  · simp only [↓reduceIte]
    exact expireOne_timers h1

theorem schedule_timers {s : S} (h : Timers s.1) : Timers (schedule.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  change Timers ex at h
  simp only [schedule, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact h
  have hr : ∀ s' : S, Timers s'.1 →
      Timers ((do
        let ex ← getEx
        if !ex.readInFlight && ex.wantsInput then
          let readBy := if ex.uploadOver then some (ex.now + ex.config.gapMs) else none
          setEx { ex with readInFlight := true, readBy }
          emit (.read ex.config.readChunk) : StepM Unit).run s').2.1 := by
    intro ⟨ex', acts'⟩ h'
    simp only [getEx_bind_run]
    rcases Bool.eq_false_or_eq_true (!ex'.readInFlight && ex'.wantsInput) with hc | hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run, emit_run]
    · exact h'.agree (by tagree_rfl)
    · exact h'
  rcases Bool.eq_false_or_eq_true
      (!ex.uploadStopped && ex.writeInFlight.isNone && decide (ex.written < ex.request.size)) with
    hc | hc <;> simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Option.isNone_iff_eq_none,
      decide_eq_true_eq] at hc
    obtain ⟨⟨_, _⟩, hlt⟩ := hc
    let stop := min ex.request.size (ex.written + max 1 ex.config.writeChunk)
    let slice := if ex.written == 0 && stop == ex.request.size then ex.request
      else ex.request.extract ex.written stop
    let ex' : Exchange := { ex with
      writeInFlight := some (stop - ex.written), writeBy := some (ex.now + ex.config.gapMs),
      sentAny := true }
    have key : Timers ex' := by
      refine ⟨by simp [ex'], fun k hk => ?_, h.drainBy, h.drainingWritten, fun hp => ?_,
        h.drainingHead⟩
      · simp only [ex', Option.some.injEq] at hk
        have := Nat.le_max_left 1 ex.config.writeChunk
        simp only [stop] at hk
        omega
      · have := h.drainingWritten hp
        omega
    exact hr (ex', acts.push (.write slice)) key
  · exact hr _ h

/-- `Timers` holds where `begin` starts. -/
theorem initial_timers (req : PreparedRequest) (now deadline : Timestamp) :
    Timers (initial req now deadline) :=
  ⟨by simp [initial], by simp [initial], by simp [initial], fun h => (by cases h),
    fun h => (by cases h), fun h => (by cases h)⟩

/-- A step's handler keeps `Timers`. -/
theorem handle_timers (e : ExchangeEvent) {ex : Exchange} (hi : Inv ex) (h : Timers ex) :
    Timers ((handle e).run (ex, #[])).2.1 := by
  cases e with
  | received bytes =>
    simp only [handle, bind_run, setEx_run]
    have h1 := h.agree (b := { ex with readInFlight := false, readBy := none }) (by tagree_rfl)
    split
    · exact failNow_timers _ _ h1
    · rcases Bool.eq_false_or_eq_true bytes.isEmpty with hb | hb <;>
        simp only [hb, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run]
      · exact h1
      · exact absorb_timers (h1.agree (by tagree_rfl))
  | endOfInput =>
    simp only [handle, bind_run, setEx_run]
    have h1 := h.agree (b := { ex with readInFlight := false, readBy := none, inputEnded := true })
      (by tagree_rfl)
    split
    · exact failNow_timers _ _ h1
    · simp only [bind_run, setEx_run]
      exact absorb_timers (h1.agree (by tagree_rfl))
  | written count =>
    simp only [handle, getEx_bind_run]
    cases hl : ex.writeInFlight with
    | none => exact h
    | some len =>
      simp only [setEx_run]
      have hnd : ex.phase = .draining → False := fun hp => by rw [h.drainingIdle hp] at hl; cases hl
      have hdb : ex.drainBy = none := by
        cases hd : ex.drainBy with
        | none => rfl
        | some _ => exact absurd (h.drainBy (by simp [hd])) hnd
      have leaf : ∀ ex' : Exchange, ex'.writeInFlight = none → ex'.writeBy = none →
          ex'.drainBy = none → (ex'.phase = .draining → False) → Timers ex' :=
        fun ex' hw hwb hd hp => ⟨by simp [hwb], by simp [hw], by simp [hd], fun h' => absurd h' hp,
          fun h' => absurd h' hp, fun h' => absurd h' hp⟩
      cases hp : ex.phase <;> simp only
      case draining => exact absurd hp hnd
      case sending =>
        by_cases hd : ex.written + min count len ≥ ex.headBytes <;> simp only [hd, ↓reduceIte]
        · split
          · exact leaf _ rfl rfl hdb (fun h' => (by cases h'))
          · exact leaf _ rfl rfl hdb (fun h' => (by cases h'))
        · split
          · exact leaf _ rfl rfl hdb (fun h' => (by cases h'))
          · exact leaf _ rfl rfl hdb (fun h' => (by cases h'))
      all_goals
        split
        · exact leaf _ rfl rfl hdb (fun h' => (by cases h'))
        · exact leaf _ rfl rfl hdb (fun h' => (by cases h'))
  | writeFailed detail =>
    simp only [handle, getEx_bind_run]
    rcases Bool.eq_false_or_eq_true ex.writeInFlight.isNone with hn | hn <;>
      simp only [hn, ↓reduceIte, Bool.false_eq_true]
    · exact h
    · simp only [bind_run, setEx_run]
      have h1 : Timers { ex with writeInFlight := none, writeBy := none } :=
        ⟨by simp, by simp, h.drainBy, h.drainingWritten, fun _ => rfl, h.drainingHead⟩
      split
      · exact failNow_timers _ _ h1
      · rcases Bool.eq_false_or_eq_true ex.uploadStopped with hu | hu <;>
          simp only [hu, ↓reduceIte, Bool.false_eq_true, bind_run, getEx_run, setEx_run]
        · exact h1.agree (by tagree_rfl)
        · exact stopUpload_timers (h1.agree (by tagree_rfl))
  | readFailed detail =>
    simp only [handle, bind_run, modifyEx_run]
    exact failOrDrop_timers _ _ (h.agree (by tagree_rfl))
  | wantBody bytes =>
    simp only [handle, bind_run, setEx_run]
    have h1 := h.agree (b := { ex with credit := ex.credit + bytes }) (by tagree_rfl)
    split
    · simp only [↓reduceIte]; exact absorb_timers h1
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact h1
  | tick =>
    simp only [handle]
    exact h
  | abandon =>
    simp only [handle, getEx_bind_run]
    split
    · exact failNow_timers _ _ h
    · exact failNow_timers _ _ h
    · rename_i hp
      split
      · rename_i hw
        simp only [bind_run, setEx_run]
        have hwr : ex.written = ex.request.size := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hw
          exact hw.1.1.2
        have hidle : ex.writeInFlight = none := by
          cases hk : ex.writeInFlight with
          | none => rfl
          | some k =>
            have := hi.inFlightLe k hk
            have := h.inFlightPos k hk
            omega
        have hhd := hi.hasHead (by simp [hp, Phase.isBody])
        exact absorb_timers ⟨h.writeBy, h.inFlightPos, fun _ => rfl, fun _ => hwr, fun _ => hidle,
          fun _ => hhd⟩
      · exact finishNow_timers false h
    · exact h

/-- Every step keeps `Timers`. -/
theorem step_timers {ex : Exchange} (hi : Inv ex) (h : Timers ex) (now : Timestamp)
    (e : ExchangeEvent) : Timers (ex.step now e).1 := by
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨hc, _⟩
  · rw [hs]; exact h
  · rw [step_run hc]
    simp only [bind_run]
    apply schedule_timers
    apply expire_timers
    exact handle_timers e ⟨hi.headWritten, hi.hasHead, hi.writtenLe, hi.inFlightLe⟩
      (h.agree (by tagree_rfl))

/-- `begin` establishes `Timers`. -/
theorem begin_timers (req : PreparedRequest) (now deadline : Timestamp) :
    Timers (Exchange.begin req now deadline).1 := by
  rw [begin_def]
  simp only [bind_run]
  apply schedule_timers
  apply expire_timers
  exact initial_timers req now deadline

/--
**The timers' invariant** holds for every reachable exchange: a write's deadline is set only while a
write is in flight, which is never empty, and the drain's only while draining, when the whole request
has been written, no write is in flight and the final head was delivered.
-/
theorem Reachable.timers {ex : Exchange} (h : Reachable ex) : Timers ex := by
  induction h with
  | begin req now deadline => exact begin_timers req now deadline
  | @step ex now e hr ih => exact step_timers hr.inv ih now e

/-! ## Deadlines ahead -/

/-- Every deadline still set is strictly after the exchange's clock. -/
structure Ahead (ex : Exchange) : Prop where
  /-- The deadline of the whole exchange. -/
  deadline : ex.now < ex.deadline
  /-- The write's. -/
  writeBy : ∀ t, ex.writeBy = some t → ex.now < t
  /-- The read's. -/
  readBy : ∀ t, ex.readBy = some t → ex.now < t
  /-- The drain's. -/
  drainBy : ∀ t, ex.drainBy = some t → ex.now < t

/-- When the fold of `expireOne` picks nothing, no candidate has passed. -/
theorem none_passed {l : List (Timestamp × Nat × TimeoutKind)} {now : Timestamp}
    (h : (l.filter fun x => decide (x.1 ≤ now)).foldl (init := none) (fun best c =>
      match best with
      | none => some c
      | some b => if c.1 < b.1 || (c.1 == b.1 && c.2.1 < b.2.1) then some c else some b) = none) :
    ∀ c ∈ l, now < c.1 := by
  intro c hc
  apply Nat.lt_of_not_le
  intro hle
  have hm : c ∈ l.filter fun x => decide (x.1 ≤ now) := List.mem_filter.mpr ⟨hc, by simpa using hle⟩
  exact first_ne_none (List.ne_nil_of_mem hm) h

/--
One round of `expireOne` on an exchange that has not ended: it ends the exchange, or acts on nothing
and leaves every deadline ahead, or stops the upload, which clears the write's deadline.
-/
theorem expireOne_ahead {ex : Exchange} {acts : Array ExchangeAction} (ht : ex.terminal = false)
    (h : Timers ex) :
    let r := expireOne.run (ex, acts)
    r.2.1.terminal = true ∨ (r.1 = false ∧ Ahead r.2.1) ∨
      (r.1 = true ∧ r.2.1.writeBy = none ∧ r.2.1.terminal = false) := by
  intro r
  simp only [r, expireOne, getEx_bind_run, ht, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i hp
    rcases Bool.eq_false_or_eq_true (decide (ex.now ≥ ex.deadline) || ex.drainBy.any (ex.now ≥ ·) ||
        ex.readBy.any (ex.now ≥ ·)) with hc | hc
    · left
      simp only [hc, ↓reduceIte, bind_run, finishNow_run, ht, Bool.false_eq_true]
      rfl
    · right; left
      simp only [hc, Bool.false_eq_true, ↓reduceIte, pure_run]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      refine ⟨trivial, h1, fun t ht' => ?_, fun t ht' => ?_, fun t ht' => ?_⟩
      · have := h.writeBy (by simp [ht'])
        rw [h.drainingIdle hp] at this
        cases this
      · rw [ht'] at h3; simpa using h3
      · rw [ht'] at h2; simpa using h2
  · rename_i hnd
    split
    · rename_i heq
      right; left
      have hall := none_passed heq
      have ha : Ahead ex :=
        ⟨hall (ex.deadline, 0, .deadline) (by simp),
          fun t ht' => hall (t, 1, .write) (by simp [ht']),
          fun t ht' => hall (t, 2, .read) (by simp [ht']),
          fun t ht' => absurd (h.drainBy (by simp [ht'])) hnd⟩
      exact ⟨rfl, ha⟩
    · split
      · right; right
        simp only [bind_run, stopUpload, modifyEx_run]
        exact ⟨rfl, rfl, ht⟩
      · left
        simp only [bind_run, failNow_run, ht, Bool.false_eq_true, ↓reduceIte]
        rfl
    · left
      simp only [bind_run, failNow_run, ht, Bool.false_eq_true, ↓reduceIte]
      rfl

/-- With no write deadline, `expireOne` never asks for another round. -/
theorem expireOne_noWrite {ex : Exchange} {acts : Array ExchangeAction} (hw : ex.writeBy = none) :
    (expireOne.run (ex, acts)).1 = false := by
  simp only [expireOne, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · rfl
  split
  · split <;> rfl
  · split
    · rfl
    · rename_i t k heq
      have hm := first_mem heq
      simp [hw] at hm
    · simp only [bind_run]; rfl

/-- After `expire`, an exchange that has not ended has every deadline ahead. -/
theorem expire_ahead {ex : Exchange} {acts : Array ExchangeAction} (ht : ex.terminal = false)
    (h : Timers ex) :
    (expire.run (ex, acts)).2.1.terminal = true ∨ Ahead (expire.run (ex, acts)).2.1 := by
  simp only [expire, bind_run]
  have h1 := expireOne_ahead (acts := acts) ht h
  have hT := expireOne_timers (s := (ex, acts)) h
  generalize expireOne.run (ex, acts) = x at h1 hT ⊢
  obtain ⟨b, ex', acts'⟩ := x
  simp only at h1 hT ⊢
  cases b
  · rcases h1 with h1 | ⟨_, h1⟩ | ⟨h1, _⟩
    · left; exact h1
    · right; exact h1
    · cases h1
  · simp only [↓reduceIte]
    rcases h1 with h1 | ⟨h1, _⟩ | ⟨_, hw, ht'⟩
    · rw [discard_run, expireOne_terminal (s := (ex', acts')) h1]
      left; exact h1
    · cases h1
    · rw [discard_run]
      rcases expireOne_ahead (acts := acts') ht' hT with h2 | ⟨_, h2⟩ | ⟨h2, _⟩
      · left; exact h2
      · right; exact h2
      · rw [expireOne_noWrite hw] at h2; cases h2

/-- `schedule` keeps every deadline ahead: the gap is positive. -/
theorem schedule_ahead {s : S} (h : Ahead s.1) : Ahead (schedule.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [schedule, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact h
  have hr : ∀ s' : S, Ahead s'.1 →
      Ahead ((do
        let ex ← getEx
        if !ex.readInFlight && ex.wantsInput then
          let readBy := if ex.uploadOver then some (ex.now + ex.config.gapMs) else none
          setEx { ex with readInFlight := true, readBy }
          emit (.read ex.config.readChunk) : StepM Unit).run s').2.1 := by
    intro ⟨ex', acts'⟩ h'
    simp only [getEx_bind_run]
    rcases Bool.eq_false_or_eq_true (!ex'.readInFlight && ex'.wantsInput) with hc | hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run, emit_run]
    · refine ⟨h'.deadline, h'.writeBy, fun t ht' => ?_, h'.drainBy⟩
      simp only at ht'
      split at ht'
      · cases ht'; exact Nat.lt_add_of_pos_right ex'.config.gapMs_pos
      · cases ht'
    · exact h'
  rcases Bool.eq_false_or_eq_true
      (!ex.uploadStopped && ex.writeInFlight.isNone && decide (ex.written < ex.request.size)) with
    hc | hc <;> simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · let stop := min ex.request.size (ex.written + max 1 ex.config.writeChunk)
    let slice := if ex.written == 0 && stop == ex.request.size then ex.request
      else ex.request.extract ex.written stop
    let ex' : Exchange := { ex with
      writeInFlight := some (stop - ex.written), writeBy := some (ex.now + ex.config.gapMs),
      sentAny := true }
    have key : Ahead ex' := by
      refine ⟨h.deadline, fun t ht' => ?_, h.readBy, h.drainBy⟩
      simp only [ex', Option.some.injEq] at ht'
      subst ht'
      exact Nat.lt_add_of_pos_right ex.config.gapMs_pos
    exact hr (ex', acts.push (.write slice)) key
  · exact hr _ h

/-- Every reachable exchange that has not ended has every deadline ahead. -/
theorem Reachable.ahead {ex : Exchange} (h : Reachable ex) (ht : ex.terminal = false) : Ahead ex := by
  induction h with
  | begin req now deadline =>
    revert ht
    rw [begin_def]
    simp only [bind_run]
    intro ht
    rcases expire_ahead (acts := #[]) (ex := initial req now deadline) (by simp [initial, terminal])
      (initial_timers req now deadline) with h1 | h1
    · rw [schedule_terminal h1, h1] at ht; cases ht
    · exact schedule_ahead h1
  | @step ex now e hr ih =>
    rcases step_cases ex now e with ⟨_, hs⟩ | ⟨hc, _⟩
    · rw [hs] at ht ⊢; exact ih ht
    · revert ht
      rw [step_run hc]
      simp only [bind_run]
      intro ht
      have hT := handle_timers e (ex := advanced ex now)
        ⟨hr.inv.headWritten, hr.inv.hasHead, hr.inv.writtenLe, hr.inv.inFlightLe⟩
        (hr.timers.agree (by tagree_rfl))
      generalize ((handle e).run (advanced ex now, #[])).2 = s1 at hT ht ⊢
      obtain ⟨ex1, acts1⟩ := s1
      cases ht1 : ex1.terminal
      · rcases expire_ahead (acts := acts1) ht1 hT with h1 | h1
        · rw [schedule_terminal h1, h1] at ht; cases ht
        · exact schedule_ahead h1
      · rw [expire_terminal (s := (ex1, acts1)) ht1, schedule_terminal (s := (ex1, acts1)) ht1] at ht
        simp only at ht
        rw [ht1] at ht
        cases ht

theorem foldl_min_gt {a : Nat} : ∀ (l : List Nat) (b : Nat), (∀ x ∈ l, a < x) → a < b →
    a < l.foldl min b
  | [], _, _, hb => hb
  | x :: l, b, hl, hb =>
    foldl_min_gt l (min b x) (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      (Nat.lt_min.mpr ⟨hb, hl x (by simp)⟩)

/-- With every deadline ahead, the next one is ahead, and no later than the exchange's. -/
theorem Ahead.nextDeadline {ex : Exchange} (h : Ahead ex) (ht : ex.terminal = false) :
    ∃ t, ex.nextDeadline = some t ∧ ex.now < t ∧ t ≤ ex.deadline := by
  have hn : ex.nextDeadline =
      some (([ex.writeBy, ex.readBy, ex.drainBy].filterMap id).foldl min ex.deadline) := by
    simp only [Exchange.nextDeadline, ht, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, hn, foldl_min_gt _ _ ?_ h.deadline, foldl_min_le _ _⟩
  intro x hx
  obtain ⟨a, ha, hax⟩ := List.mem_filterMap.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h.writeBy x hax
  · exact h.readBy x hax
  · exact h.drainBy x hax

/--
**A live exchange has a deadline ahead** (checker: "a live exchange has a deadline ahead").  Every
reachable exchange that has not ended has a next deadline strictly after its clock, and no later
than the deadline of the whole exchange: every deadline that has passed was acted on, and the shell
never sleeps past the exchange's deadline.
-/
theorem Reachable.deadlineAhead {ex : Exchange} (h : Reachable ex) (ht : ex.terminal = false) :
    ∃ t, ex.nextDeadline = some t ∧ ex.now < t ∧ t ≤ ex.deadline :=
  (h.ahead ht).nextDeadline ht

end LeanHttp.Exchange
