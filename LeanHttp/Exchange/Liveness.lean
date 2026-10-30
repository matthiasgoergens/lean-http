module

import all LeanHttp.Exchange
import all LeanHttp.Exchange.Proofs

/-!
# Deadlines ahead, and liveness

Two properties of the exchange core beyond those of `LeanHttp.Exchange.Proofs`, which this module
builds on.  Like those, they hold whatever the response parser returns.

- **A live exchange has a deadline ahead** (`Reachable.deadlineAhead`).  Every reachable exchange
  that has not ended has a next deadline strictly after its clock and no later than the deadline of
  the whole exchange.  It rests on the gap being positive (`ExchangeConfig.gapMs_pos`) and on a
  companion invariant of the timers (`Timers`): a write's deadline is set only while a write is in
  flight, and the drain's only while draining, when the whole request has been written.  The
  checker states the property against its model's clock rather than the exchange's;
  `ObservedMono.deadlineAhead` proves that form for runs in which no event but a tick is earlier
  than the latest event before it, and it is false without that condition.
- **Liveness.**  An event the shell reports at or after the next deadline (a *due* event) either
  ends the exchange or moves its clock strictly forward (`Reachable.due_advances`), and the clock of
  a live exchange stays before its deadline.  So `deadline - now` ranks every run: the due events
  counted so far plus the time left never exceed the time left at the start
  (`Reachable.dueCount_le`), whatever else the shell reported in between, so a live exchange has
  had fewer than `deadline - now` due events (`Reachable.ended_after_waits`; a worst-case bound,
  since a due event usually moves the clock by far more than 1 ms).  If, whenever the exchange is
  live, the shell eventually delivers a due event or the exchange ends, it ends
  (`Reachable.ends_of_fair`); if every event is due, within `deadline - now` events
  (`Reachable.ends_of_allDue`); and the first event at or after the deadline ends it in any case
  (`Reachable.ended_at_deadline`).

What is assumed about the shell is the hypothesis of each theorem and nothing more.  A run is any
sequence of events at any times (the shell's clock may even go backwards); termination needs the
shell to deliver due events, which it always can, since the next deadline is ahead and no later than
the deadline (`Reachable.tick_due`).  That a real shell does (that its sleep returns, and its clock
reaches the next deadline) is not proved.
-/

namespace LeanHttp.Exchange

open Std.Http

/-! ## The timers' invariant -/

/-- The invariant of the timers, at every point of every step from `begin`. -/
structure Timers (ex : Exchange) : Prop where
  /-- A write's deadline is set only while a write is in flight. -/
  writeBy : ex.writeBy.isSome = true → ex.writeInFlight.isSome = true
  /-- The write in flight is not empty. -/
  inFlightPos : ∀ k, ex.writeInFlight = some k → 0 < k
  /-- The drain's deadline is set only while draining. -/
  drainBy : ex.drainBy.isSome = true → ex.phase = .draining
  /-- While draining, every byte of the request is known -/
  drainingComplete : ex.phase = .draining → ex.wireDone = true
  /-- and has been written, -/
  drainingWritten : ex.phase = .draining → ex.written = ex.known
  /-- no write is in flight, -/
  drainingIdle : ex.phase = .draining → ex.writeInFlight = none
  /-- and the final head was delivered. -/
  drainingHead : ex.phase = .draining → ex.head.isSome = true

/-- The fields `Timers` depends on. -/
structure TAgree (a b : Exchange) : Prop where
  phase : b.phase = a.phase
  written : b.written = a.written
  request : b.request = a.request
  segStart : b.segStart = a.segStart
  complete : b.complete = a.complete
  framing : b.framing = a.framing
  taken : b.taken = a.taken
  head : b.head = a.head
  writeInFlight : b.writeInFlight = a.writeInFlight
  writeBy : b.writeBy = a.writeBy
  drainBy : b.drainBy = a.drainBy

/-- `TAgree` for an update of other fields. -/
macro "tagree_rfl" : tactic =>
  `(tactic| exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem Timers.agree {a b : Exchange} (h : Timers a) (ha : TAgree a b) : Timers b where
  writeBy := by rw [ha.writeBy, ha.writeInFlight]; exact h.writeBy
  inFlightPos := by rw [ha.writeInFlight]; exact h.inFlightPos
  drainBy := by rw [ha.drainBy, ha.phase]; exact h.drainBy
  drainingComplete := by
    rw [ha.phase, wireDone_eq ha.complete ha.framing ha.taken]; exact h.drainingComplete
  drainingWritten := by
    rw [ha.phase, ha.written, known_eq ha.segStart ha.request]; exact h.drainingWritten
  drainingIdle := by rw [ha.phase, ha.writeInFlight]; exact h.drainingIdle
  drainingHead := by rw [ha.phase, ha.head]; exact h.drainingHead

/-- An exchange that ended, with its timers cleared. -/
theorem Timers.stop {ex : Exchange} (h : Timers ex) {p : Phase} (hp : p = .draining → False) :
    Timers { ex with phase := p, writeBy := none, readBy := none, drainBy := none } where
  writeBy := by simp
  inFlightPos := h.inFlightPos
  drainBy := by simp
  drainingComplete := fun h' => absurd h' hp
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
  exact ⟨by simp, h.inFlightPos, h.drainBy, h.drainingComplete, h.drainingWritten, h.drainingIdle,
    h.drainingHead⟩

/-- Delivering the final head: no head yet, so not draining, so no drain deadline. -/
theorem Timers.receive {ex : Exchange} (h : Timers ex) (hh : ex.head.isSome = false)
    (head : Response.Head) (early : Bool) :
    Timers { ex with head := some head, phase := .receiving, early } := by
  have hdb : ex.drainBy.isSome = false := by
    cases hd : ex.drainBy.isSome
    · rfl
    · have := h.drainingHead (h.drainBy hd)
      rw [hh] at this
      cases this
  exact ⟨h.writeBy, h.inFlightPos, fun h' => (by simp only at h'; rw [hdb] at h'; cases h'),
    fun h' => (by cases h'), fun h' => (by cases h'), fun h' => (by cases h'), fun h' => (by cases h')⟩

theorem release_timers {s : S} (h : Timers s.1) : Timers (release.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  rw [release_run]
  split
  · exact h.agree (by tagree_rfl)
  · exact h

theorem onHead_timers {s : S} (hd : Codec.Head) (h : Timers s.1) :
    Timers ((onHead hd).run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [onHead, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true (ex.terminal || ex.head.isSome) with hc | hc <;>
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · exact h
  · simp only [Bool.or_eq_false_iff] at hc
    simp only [bind_run, setEx_run, emit_run]
    exact h.receive hc.2 hd.response ex.unsent

theorem onHead?_timers {s : S} (hd : Option Codec.Head) (h : Timers s.1) :
    Timers ((onHead? hd).run s).2.1 := by
  cases hd with
  | none => exact h
  | some hd => exact onHead_timers hd h

theorem onBodies_timers {s : S} (bodies : List ByteArray) (h : Timers s.1) :
    Timers ((onBodies bodies).run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [onBodies, getEx_bind_run]
  split
  · simp only [bind_run, setEx_run]
    have h' := h.agree (b := { ex with drained := bodies.foldl (· + ·.size) ex.drained }) (by tagree_rfl)
    split
    · exact finishNow_timers false h'
    · exact h'
  · simp only [bind_run, setEx_run]
    exact release_timers (h.agree (by tagree_rfl))

theorem onError?_timers {s : S} (e : Option Codec.Error) (h : Timers s.1) :
    Timers ((onError? e).run s).2.1 := by
  cases e with
  | none => exact h
  | some e => exact failOrDrop_timers _ _ h

theorem onEvents_timers {s : S} (events : Array Codec.Event) (h : Timers s.1) :
    Timers ((onEvents events).run s).2.1 := by
  simp only [onEvents, bind_run]
  exact onError?_timers _ (onBodies_timers _ (onHead?_timers _ h))

theorem settle_timers {s : S} (h : Timers s.1) : Timers (settle.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [settle, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact h
  cases hp : ex.phase <;> simp only
  case receiving =>
    split
    · exact finishNow_timers true h
    · exact h
  case draining =>
    split
    · exact finishNow_timers true h
    · split
      · exact finishNow_timers false h
      · exact h
  all_goals exact h

theorem absorb_timers {s : S} (p : Codec.Parser × Array Codec.Event) (h : Timers s.1) :
    Timers ((absorb p).run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  simp only [absorb, bind_run, modifyEx_run]
  exact settle_timers (onEvents_timers _ (h.agree (by tagree_rfl)))

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

theorem scheduleWrite_timers {s : S} (h : Timers s.1) : Timers (scheduleWrite.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  change Timers ex at h
  simp only [scheduleWrite, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true (!ex.uploadStopped && ex.writeInFlight.isNone &&
      decide (ex.written - ex.segStart < ex.request.size)) with
    hc | hc <;> simp only [hc, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run, emit_run]
  · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Option.isNone_iff_eq_none,
      decide_eq_true_eq] at hc
    obtain ⟨⟨_, _⟩, hlt⟩ := hc
    refine ⟨by simp, fun k hk => ?_, h.drainBy, h.drainingComplete, h.drainingWritten, fun hp => ?_,
      h.drainingHead⟩
    · simp only [Option.some.injEq] at hk
      have := Nat.le_max_left 1 ex.config.writeChunk
      omega
    · have := h.drainingWritten hp
      have hk : ex.known = ex.segStart + ex.request.size := rfl
      omega
  · exact h

theorem schedulePull_timers {s : S} (h : Timers s.1) : Timers (schedulePull.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  change Timers ex at h
  simp only [schedulePull, getEx_bind_run]
  split
  · simp only [bind_run, setEx_run, emit_run]; exact h.agree (by tagree_rfl)
  · exact h

theorem scheduleRead_timers {s : S} (h : Timers s.1) : Timers (scheduleRead.run s).2.1 := by
  obtain ⟨ex', acts'⟩ := s
  change Timers ex' at h
  simp only [scheduleRead, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true (!ex'.readInFlight && ex'.wantsInput) with hc | hc <;>
    simp only [hc, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run, emit_run]
  · exact h.agree (by tagree_rfl)
  · exact h

theorem schedule_timers {s : S} (h : Timers s.1) : Timers (schedule.run s).2.1 := by
  obtain ⟨ex, acts⟩ := s
  change Timers ex at h
  simp only [schedule, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true, bind_run]
  · exact h
  exact scheduleRead_timers (schedulePull_timers (scheduleWrite_timers h))

/-- `Timers` holds where `begin` starts. -/
theorem initial_timers (req : PreparedRequest) (now deadline : Timestamp) :
    Timers (initial req now deadline) :=
  ⟨by simp [initial], by simp [initial], by simp [initial], fun h => (by cases h),
    fun h => (by cases h), fun h => (by cases h), fun h => (by cases h)⟩

/-- A step's handler keeps `Timers`. -/
theorem handle_timers (e : ExchangeEvent) {ex : Exchange} (hi : Inv ex) (h : Timers ex) :
    Timers ((handle e).run (ex, #[])).2.1 := by
  cases e with
  | received bytes =>
    simp only [handle]
    rcases Bool.eq_false_or_eq_true bytes.isEmpty with hb | hb <;>
      simp only [hb, ↓reduceIte, Bool.false_eq_true]
    · exact h
    simp only [bind_run, setEx_run]
    have h1 := h.agree (b := { ex with readInFlight := false, readBy := none }) (by tagree_rfl)
    split
    · exact failNow_timers _ _ h1
    · split
      · exact h1
      · exact absorb_timers _ h1
  | endOfInput =>
    simp only [handle, bind_run, setEx_run]
    have h1 := h.agree (b := { ex with readInFlight := false, readBy := none, inputEnded := true })
      (by tagree_rfl)
    split
    · exact h1
    · split
      · exact failNow_timers _ _ h1
      · exact absorb_timers _ h1
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
          fun h' => absurd h' hp, fun h' => absurd h' hp, fun h' => absurd h' hp⟩
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
        ⟨by simp, by simp, h.drainBy, h.drainingComplete, h.drainingWritten, fun _ => rfl,
          h.drainingHead⟩
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
    · simp only [↓reduceIte, bind_run]; exact settle_timers (release_timers h1)
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact h1
  | pulled chunk =>
    simp only [handle, getEx_bind_run]
    rcases Bool.eq_false_or_eq_true ex.pulling with hp | hp <;>
      simp only [hp, ↓reduceIte, Bool.false_eq_true]
    · have hcomp := (hi.pullIdle hp).2.1
      cases ha : ex.accept chunk with
      | ok ex' =>
        simp only [setEx_run]
        have hdone := fun hd => accept_wireDone (h.drainingComplete hd) hcomp ha
        obtain ⟨⟨_, _, _, _, rfl⟩, _⟩ := accept_ok ha
        exact ⟨h.writeBy, h.inFlightPos, h.drainBy, fun hd => (hdone hd).2,
          fun hd => (h.drainingWritten hd).trans (hdone hd).1.symm, h.drainingIdle, h.drainingHead⟩
      | error cause =>
        simp only [bind_run, setEx_run]
        exact failOrDrop_timers _ _ (h.agree (by tagree_rfl))
    · exact h
  | pullFailed detail =>
    simp only [handle, getEx_bind_run]
    rcases Bool.eq_false_or_eq_true ex.pulling with hp | hp <;>
      simp only [hp, ↓reduceIte, Bool.false_eq_true]
    · simp only [bind_run, setEx_run]
      exact failOrDrop_timers _ _ (h.agree (by tagree_rfl))
    · exact h
  | tick =>
    simp only [handle]
    exact h
  | abandon =>
    simp only [handle, bind_run, setEx_run]
    have h0 := h.agree (b := { ex with abandoned := true }) (by tagree_rfl)
    split
    · exact failNow_timers _ _ h0
    · exact failNow_timers _ _ h0
    · rename_i hp
      have hp' : ex.phase = .receiving := hp
      split
      · rename_i hw
        simp only [bind_run, setEx_run]
        have hwr : ex.written = ex.known := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hw
          exact hw.1.1.1.2
        have hcomp : ex.wireDone = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hw
          exact hw.1.1.1.1.2
        have hidle : ex.writeInFlight = none := by
          cases hk : ex.writeInFlight with
          | none => rfl
          | some k =>
            have := hi.inFlightLe k hk
            have := h.inFlightPos k hk
            omega
        have hhd := hi.hasHead (by simp [hp', Phase.isBody])
        exact settle_timers ⟨h.writeBy, h.inFlightPos, fun _ => rfl, fun _ => hcomp, fun _ => hwr,
          fun _ => hidle, fun _ => hhd⟩
      · exact finishNow_timers false h0
    · exact h0

/-- Every step keeps `Timers`. -/
theorem step_timers {ex : Exchange} (hi : Inv ex) (h : Timers ex) (now : Timestamp)
    (e : ExchangeEvent) : Timers (ex.step now e).1 := by
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨hc, _⟩
  · rw [hs]; exact h
  · rw [step_run hc]
    simp only [bind_run]
    apply schedule_timers
    apply expire_timers
    exact handle_timers e ⟨hi.headWritten, hi.hasHead, hi.writtenLe, hi.inFlightLe, hi.segLe, hi.pullIdle⟩
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
    simp only [ht, ↓reduceIte, Bool.false_eq_true, bind_run]
  · exact h
  have hw : ∀ s' : S, Ahead s'.1 → Ahead (scheduleWrite.run s').2.1 := by
    intro ⟨ex', acts'⟩ h'
    simp only [scheduleWrite, getEx_bind_run]
    split
    · simp only [bind_run, setEx_run, emit_run]
      refine ⟨h'.deadline, fun t ht' => ?_, h'.readBy, h'.drainBy⟩
      simp only [Option.some.injEq] at ht'
      subst ht'
      exact Nat.lt_add_of_pos_right ex'.config.gapMs_pos
    · exact h'
  have hp : ∀ s' : S, Ahead s'.1 → Ahead (schedulePull.run s').2.1 := by
    intro ⟨ex', acts'⟩ h'
    simp only [schedulePull, getEx_bind_run]
    split
    · simp only [bind_run, setEx_run, emit_run]
      exact ⟨h'.deadline, h'.writeBy, h'.readBy, h'.drainBy⟩
    · exact h'
  have hr : ∀ s' : S, Ahead s'.1 → Ahead (scheduleRead.run s').2.1 := by
    intro ⟨ex', acts'⟩ h'
    simp only [scheduleRead, getEx_bind_run]
    rcases Bool.eq_false_or_eq_true (!ex'.readInFlight && ex'.wantsInput) with hc | hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run, emit_run]
    · refine ⟨h'.deadline, h'.writeBy, fun t ht' => ?_, h'.drainBy⟩
      simp only at ht'
      split at ht'
      · cases ht'; exact Nat.lt_add_of_pos_right ex'.config.gapMs_pos
      · cases ht'
    · exact h'
  exact hr _ (hp _ (hw _ h))

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
        ⟨hr.inv.headWritten, hr.inv.hasHead, hr.inv.writtenLe, hr.inv.inFlightLe, hr.inv.segLe,
          hr.inv.pullIdle⟩
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

/-! ## Liveness -/

/-- The exchange after `ex` has taken the first `n` events of `ev`, each at its time. -/
def stateAt (ex : Exchange) (ev : Nat → Timestamp × ExchangeEvent) : Nat → Exchange
  | 0 => ex
  | n + 1 => ((stateAt ex ev n).step (ev n).1 (ev n).2).1

/--
`true` when an event at `t` comes at or after the exchange's next deadline, i.e. the shell waited
as long as the core let it; `false` once the exchange has ended.
-/
def dueAt (ex : Exchange) (t : Timestamp) : Bool :=
  match ex.nextDeadline with
  | some d => decide (d ≤ t)
  | none => false

/-- How many of the first `n` events of a run were due when they came. -/
def dueCount (ex : Exchange) (ev : Nat → Timestamp × ExchangeEvent) : Nat → Nat
  | 0 => 0
  | n + 1 => dueCount ex ev n + if dueAt (stateAt ex ev n) (ev n).1 then 1 else 0

theorem Reachable.stateAt_reachable {ex : Exchange} (h : Reachable ex) (ev : Nat → Timestamp × ExchangeEvent) :
    ∀ n, Reachable (stateAt ex ev n)
  | 0 => h
  | n + 1 => .step _ _ (h.stateAt_reachable ev n)

theorem Reachable.stateAt_deadline {ex : Exchange} (h : Reachable ex)
    (ev : Nat → Timestamp × ExchangeEvent) : ∀ n, (stateAt ex ev n).deadline = ex.deadline
  | 0 => rfl
  | n + 1 => by
    simp only [Exchange.stateAt]
    rw [(step_fixed (h.stateAt_reachable ev n).inv _ _).2]
    exact h.stateAt_deadline ev n

theorem stateAt_terminal {ex : Exchange} {ev : Nat → Timestamp × ExchangeEvent} {n : Nat}
    (h : (stateAt ex ev n).terminal = true) : ∀ k, (stateAt ex ev (n + k)).terminal = true
  | 0 => h
  | k + 1 => by
    show ((stateAt ex ev (n + k)).step _ _).1.terminal = true
    rw [step_of_terminal (stateAt_terminal h k)]
    exact stateAt_terminal h k

/-- A step never moves the clock back, and moves it to the event's time unless it ignores it. -/
theorem step_now {ex : Exchange} (hi : Inv ex) (now : Timestamp) (e : ExchangeEvent) :
    ((ex.terminal || stale ex now e) = true ∧ (ex.step now e).1.now = ex.now) ∨
      ((ex.terminal || stale ex now e) = false ∧ (ex.step now e).1.now = max ex.now now) := by
  rcases step_cases ex now e with ⟨hc, hs⟩ | ⟨hc, hg⟩
  · left; rw [hs]; exact ⟨hc, rfl⟩
  · right
    refine ⟨hc, ?_⟩
    rw [(hg hi).fixed.now, startOf_now]

theorem step_now_le {ex : Exchange} (hi : Inv ex) (now : Timestamp) (e : ExchangeEvent) :
    ex.now ≤ (ex.step now e).1.now := by
  rcases step_now hi now e with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

theorem terminal_of_nextDeadline {ex : Exchange} {d : Timestamp} (h : ex.nextDeadline = some d) :
    ex.terminal = false := by
  unfold Exchange.nextDeadline at h
  split at h
  · cases h
  · rename_i ht; simpa using ht

/--
**A due event moves the clock forward.**  An event at or after the next deadline of a reachable
exchange is not ignored, and leaves the exchange's clock strictly later than it was.
-/
theorem Reachable.due_advances {ex : Exchange} (h : Reachable ex) {t : Timestamp}
    (hd : dueAt ex t = true) (e : ExchangeEvent) : ex.now < (ex.step t e).1.now := by
  unfold dueAt at hd
  split at hd
  · rename_i d hn
    simp only [decide_eq_true_eq] at hd
    have ht := terminal_of_nextDeadline hn
    obtain ⟨d', hn', hlt, _⟩ := h.deadlineAhead ht
    rw [hn] at hn'
    cases hn'
    rcases step_now h.inv t e with ⟨hc, _⟩ | ⟨_, hs⟩
    · exfalso
      cases e <;> simp only [ht, Bool.false_or, stale, hn, decide_eq_true_eq, Bool.false_eq_true,
        Bool.and_eq_true] at hc
      all_goals first
        | exact Nat.lt_irrefl t (Nat.lt_of_lt_of_le hc hd)
        | exact Nat.lt_irrefl t (Nat.lt_of_lt_of_le hc.2 hd)
    · rw [hs]
      exact Nat.lt_of_lt_of_le hlt (Nat.le_trans hd (Nat.le_max_right _ _))
  · cases hd

/--
The ranking of a run: due events, counted, plus the time left before the deadline, never exceed the
time left at the start.
-/
theorem Reachable.dueCount_le {ex : Exchange} (h : Reachable ex)
    (ev : Nat → Timestamp × ExchangeEvent) (n : Nat) :
    dueCount ex ev n + (ex.deadline - (stateAt ex ev n).now) ≤ ex.deadline - ex.now := by
  induction n with
  | zero => simp [dueCount, Exchange.stateAt]
  | succ n ih =>
    have hr := h.stateAt_reachable ev n
    have hdl := h.stateAt_deadline ev n
    simp only [dueCount, Exchange.stateAt]
    rcases Bool.eq_false_or_eq_true (dueAt (stateAt ex ev n) (ev n).1) with hd | hd <;>
      simp only [hd, ↓reduceIte, Bool.false_eq_true]
    · have h1 := hr.due_advances hd (ev n).2
      have h2 : (stateAt ex ev n).now < (stateAt ex ev n).deadline := by
        unfold dueAt at hd
        split at hd
        · rename_i d hn
          exact hr.beforeDeadline (terminal_of_nextDeadline hn)
        · cases hd
      rw [hdl] at h2
      dsimp only [Timestamp] at *
      omega
    · have h1 := step_now_le hr.inv (ev n).1 (ev n).2
      dsimp only [Timestamp] at *
      omega

/--
**Finitely many waits.**  In every run from a reachable exchange, whatever events the shell reports
and at whatever times, at most `deadline - now` of them come when due (at or after the next
deadline of a live exchange).
-/
theorem Reachable.dueCount_bound {ex : Exchange} (h : Reachable ex)
    (ev : Nat → Timestamp × ExchangeEvent) (n : Nat) : dueCount ex ev n ≤ ex.deadline - ex.now := by
  have := h.dueCount_le ev n
  dsimp only [Timestamp] at *
  omega

/--
**Ended after `deadline - now` waits.**  In every run from a reachable exchange, once `deadline - now`
of the events have come when due, whatever else the shell reported in between, the exchange has
ended; that is, a live exchange has had fewer than `deadline - now` due events.  The bound is the
worst case, in which every due event moves the clock by 1 ms and no other event moves it; with a
gap of 2 ms or more no run reaches it, and `Reachable.dueCount_le` gives the exact accounting.
-/
theorem Reachable.ended_after_waits {ex : Exchange} (h : Reachable ex)
    (ev : Nat → Timestamp × ExchangeEvent) (n : Nat) (hn : ex.deadline - ex.now ≤ dueCount ex ev n) :
    (stateAt ex ev n).terminal = true := by
  cases ht : (stateAt ex ev n).terminal
  · have h1 := h.dueCount_le ev n
    have h2 := (h.stateAt_reachable ev n).beforeDeadline ht
    rw [h.stateAt_deadline ev n] at h2
    dsimp only [Timestamp] at *
    omega
  · rfl

/--
**The deadline ends the exchange.**  In every run from a reachable exchange, the first event at or
after the exchange's deadline ends it, and it stays ended (and, by `step_of_terminal`, unchanged and
silent).
-/
theorem Reachable.ended_at_deadline {ex : Exchange} (h : Reachable ex)
    (ev : Nat → Timestamp × ExchangeEvent) {n : Nat} (hd : ex.deadline ≤ (ev n).1) :
    ∀ m, n < m → (stateAt ex ev m).terminal = true := by
  intro m hm
  have h1 : (stateAt ex ev (n + 1)).terminal = true := by
    show ((stateAt ex ev n).step (ev n).1 (ev n).2).1.terminal = true
    apply step_deadline (h.stateAt_reachable ev n)
    rw [h.stateAt_deadline ev n]
    exact Nat.le_trans hd (Nat.le_max_right _ _)
  have := stateAt_terminal h1 (m - (n + 1))
  rwa [show n + 1 + (m - (n + 1)) = m by omega] at this

theorem dueCount_mono {ex : Exchange} {ev : Nat → Timestamp × ExchangeEvent} {n m : Nat}
    (h : n ≤ m) : dueCount ex ev n ≤ dueCount ex ev m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · simp only [dueCount]
      have := ih (by omega)
      omega
    · rw [h']; exact Nat.le_refl _

/--
**Liveness under fairness.**  If, whenever the exchange is live, the shell eventually delivers an
event when it is due (at or after the next deadline), unless the exchange has ended by then, the
exchange ends.  The events in between are arbitrary, in kind and time.
-/
theorem Reachable.ends_of_fair {ex : Exchange} (h : Reachable ex)
    (ev : Nat → Timestamp × ExchangeEvent)
    (fair : ∀ n, (stateAt ex ev n).terminal = false →
      ∃ m, n ≤ m ∧ ((stateAt ex ev m).terminal = true ∨ dueAt (stateAt ex ev m) (ev m).1 = true)) :
    ∃ n, (stateAt ex ev n).terminal = true := by
  apply Classical.byContradiction
  intro hno
  have live : ∀ n, (stateAt ex ev n).terminal = false := fun n => by
    cases ht : (stateAt ex ev n).terminal
    · rfl
    · exact absurd ⟨n, ht⟩ hno
  have grow : ∀ k, ∃ N, k ≤ dueCount ex ev N := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨m, hm, hd⟩ := fair N (live N)
      have hd : dueAt (stateAt ex ev m) (ev m).1 = true := by
        rcases hd with hd | hd
        · rw [live m] at hd; cases hd
        · exact hd
      refine ⟨m + 1, ?_⟩
      have := dueCount_mono (ex := ex) (ev := ev) hm
      simp only [dueCount, hd, ↓reduceIte]
      omega
  obtain ⟨N, hN⟩ := grow (ex.deadline - ex.now + 1)
  have := h.dueCount_bound ev N
  omega

/--
**A shell that only waits ends the exchange in time.**  If every event the shell reports while the
exchange is live is due (a tick at the next deadline, say), the exchange has ended after
`deadline - now` events.
-/
theorem Reachable.ends_of_allDue {ex : Exchange} (h : Reachable ex)
    (ev : Nat → Timestamp × ExchangeEvent)
    (hall : ∀ n, (stateAt ex ev n).terminal = false → dueAt (stateAt ex ev n) (ev n).1 = true) :
    (stateAt ex ev (ex.deadline - ex.now)).terminal = true := by
  have key : ∀ n, (stateAt ex ev n).terminal = true ∨ dueCount ex ev n = n := by
    intro n
    induction n with
    | zero => right; rfl
    | succ n ih =>
      rcases ih with ih | ih
      · left; exact stateAt_terminal ih 1
      · cases ht : (stateAt ex ev n).terminal
        · right
          simp only [dueCount, hall n ht, ↓reduceIte, ih]
        · left; exact stateAt_terminal ht 1
  rcases key (ex.deadline - ex.now) with hk | hk
  · exact hk
  · exact h.ended_after_waits ev _ (by rw [hk]; exact Nat.le_refl _)

/--
**The shell can always wait.**  A reachable exchange that has not ended can be ticked at its next
deadline: the tick is due, so it is not ignored, and it comes after the exchange's clock and no
later than its deadline.
-/
theorem Reachable.tick_due {ex : Exchange} (h : Reachable ex) (ht : ex.terminal = false) :
    ∃ t, ex.nextDeadline = some t ∧ dueAt ex t = true ∧ stale ex t .tick = false ∧ ex.now < t ∧
      t ≤ ex.deadline := by
  obtain ⟨t, hn, hlt, hle⟩ := h.deadlineAhead ht
  exact ⟨t, hn, by simp [dueAt, hn], by simp [stale, hn], hlt, hle⟩

/-! ## The checker's clock -/

/--
A run with the checker's model of it (`Observed`) in which no event but a tick is earlier than the
model's clock: the shell's clock never goes backwards, except that a tick may come late.  The
checker's random runs and its exploration are such runs.
-/
inductive ObservedMono : Exchange → Obs → Prop where
  /-- The start. -/
  | begin (req : PreparedRequest) (now deadline : Timestamp) :
      ObservedMono (Exchange.begin req now deadline).1
        ((Exchange.begin req now deadline).2.foldl Obs.see (Obs.init req now))
  /-- One more step: a tick, or an event no earlier than the model's clock. -/
  | step {ex : Exchange} {m : Obs} (now : Timestamp) (e : ExchangeEvent)
      (hm : e = .tick ∨ m.now ≤ now) : ObservedMono ex m →
      ObservedMono (ex.step now e).1
        ((ex.step now e).2.foldl Obs.see { m.observe e with now := max m.now now })

theorem ObservedMono.reachable {ex : Exchange} {m : Obs} (h : ObservedMono ex m) : Reachable ex := by
  induction h with
  | begin req now deadline => exact .begin req now deadline
  | step now e _ _ ih => exact .step now e ih

/--
**A live exchange has a deadline ahead, by the checker's clock** (checker: "a live exchange has a
deadline ahead", literally).  The checker compares the next deadline with its model's clock, the
latest time of any event, which a stale tick moves past the exchange's own clock.  When no event but
a tick is earlier than the model's clock, every reachable exchange that has not ended has a next
deadline strictly after the model's clock and no later than its deadline.  Without that hypothesis
the statement is false: an event earlier than a stale tick sets its timers from the exchange's
older clock (`logs/2026-10-28/live/clock/`).
-/
theorem ObservedMono.deadlineAhead {ex : Exchange} {m : Obs} (h : ObservedMono ex m)
    (ht : ex.terminal = false) : ∃ t, ex.nextDeadline = some t ∧ m.now < t ∧ t ≤ ex.deadline := by
  induction h with
  | begin req now deadline =>
    obtain ⟨t, hn, hlt, hle⟩ := (Reachable.begin req now deadline).deadlineAhead ht
    refine ⟨t, hn, ?_, hle⟩
    rw [← Array.foldl_toList, see_now]
    have := (begin_good req now deadline).fixed.now
    rw [this] at hlt
    exact hlt
  | @step ex m now e hm hob ih =>
    rw [← Array.foldl_toList, see_now]
    simp only
    have hr := hob.reachable
    rcases step_now hr.inv now e with ⟨hc, _⟩ | ⟨hc, hs⟩
    · rw [step_ignored hc] at ht ⊢
      obtain ⟨t, hn, hlt, hle⟩ := ih ht
      refine ⟨t, hn, ?_, hle⟩
      cases e <;> simp only [ht, Bool.false_or, stale, hn, decide_eq_true_eq, Bool.false_eq_true,
        Bool.and_eq_true] at hc
      all_goals first
        | exact Nat.max_lt.mpr ⟨hlt, hc⟩
        | exact Nat.max_lt.mpr ⟨hlt, hc.2⟩
    · -- A tick that is not ignored is due, so no earlier than the model's clock either.
      have hm' : m.now ≤ now := by
        rcases hm with rfl | hm
        · have ht0 := not_terminal_of hc
          obtain ⟨t, hn, hlt, _⟩ := ih ht0
          simp only [ht0, Bool.false_or, stale, hn, decide_eq_false_iff_not, Nat.not_lt] at hc
          exact Nat.le_of_lt (Nat.lt_of_lt_of_le hlt hc)
        · exact hm
      obtain ⟨t, hn, hlt, hle⟩ := (Reachable.step now e hr).deadlineAhead ht
      refine ⟨t, hn, ?_, hle⟩
      rw [hs] at hlt
      rw [Nat.max_eq_right hm']
      exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hlt

end LeanHttp.Exchange
