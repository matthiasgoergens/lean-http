module

import all LeanHttp.Exchange
import all LeanHttp.Exchange.Proofs
import LeanHttp.Codec.Proofs

/-!
# What a finished exchange received and delivered

The theorems of `LeanHttp.Exchange.Proofs` hold whatever the response parser returns.  Here the
parser is the codec, and its own theorems (`LeanHttp.Codec.Proofs`) say what its verdicts mean for
the bytes it read.  This module carries them over to the exchange core, in the terms of the
checker's model of a run (`Observed`, whose `Obs` records the bytes received, the body delivered and
whether the caller abandoned):

- **A reusable finish is exactly one response** (`observed_finish_codec`).  When a step reports the
  connection reusable, the codec run over every byte received is complete, framed with certainty
  (`Codec.Parser.completeCertain`), and reusable (`Codec.Parser.reusable`); the bytes received are
  interim heads, the final head and a body of the kind its framing declares, with nothing after it
  (`Codec.response_sound`); the head the core delivered is that head; and unless the caller
  abandoned the body, the body the core delivered is that body's payload.
- **Any finish the caller did not abandon is after a complete response** (`observed_finish_complete`):
  the codec run over the bytes received, and the end of input if it came, is complete; the bytes
  received are interim heads, the head, a body and perhaps bytes after it; and the body delivered is
  that body's payload.  This is the checker's "finish only after a complete response" and "a
  finished response delivered its whole body".
- **The body is the response's** (`observed_body_prefix`): until the exchange fails, and unless the
  caller abandoned it, the body delivered so far is a prefix of what the codec decoded from the
  bytes received (`Codec.feed_respSound` relates that to the bytes).

In each, the head reported is tied to its bytes (`Codec.HeadBytesOf`), its framing and `Std.Http`
form to its status line and fields, and its keep-alive verdict bounded by them (`Codec.HeadOK`).
The interim heads' part in the keep-alive verdict rests on the codec's code: no theorem ties it to
their bytes.

They rest on an invariant of every run (`CInv`, `Observed.cinv`): until the exchange fails, its parser
is the codec's run over the bytes received (and the end of input, once reported) and its head is the
codec's head; unless the caller abandoned, the body delivered followed by the body held back is the
body the codec decoded; and a finish nobody abandoned comes after a complete response with nothing
held back.
-/

namespace LeanHttp.Exchange

open Std.Http

/-! ## Bytes received, body delivered -/

/-- The body bytes an action delivers. -/
def bodyOf : ExchangeAction → List UInt8
  | .deliverBody b => b.data.toList
  | _ => []

/-- The body bytes some actions deliver, in order. -/
def actBody (acts : Array ExchangeAction) : List UInt8 :=
  acts.toList.flatMap bodyOf

@[simp] theorem actBody_empty : actBody #[] = [] := rfl

@[simp] theorem actBody_push (acts : Array ExchangeAction) (a : ExchangeAction) :
    actBody (acts.push a) = actBody acts ++ bodyOf a := by
  simp [actBody]

/-- The bytes of some body pieces, in order. -/
def heldBytes (held : List ByteArray) : List UInt8 :=
  held.flatMap (·.data.toList)

@[simp] theorem heldBytes_nil : heldBytes [] = [] := rfl

@[simp] theorem heldBytes_append (a b : List ByteArray) :
    heldBytes (a ++ b) = heldBytes a ++ heldBytes b := by
  simp [heldBytes]

@[simp] theorem heldBytes_cons (b : ByteArray) (l : List ByteArray) :
    heldBytes (b :: l) = b.data.toList ++ heldBytes l := by
  simp [heldBytes]

theorem actBody_foldl (pre : List ByteArray) (acts : Array ExchangeAction) :
    actBody (pre.foldl (fun a b => a.push (.deliverBody b)) acts) = actBody acts ++ heldBytes pre := by
  induction pre generalizing acts with
  | nil => simp
  | cons b pre ih =>
    rw [List.foldl_cons, ih]
    simp [bodyOf, List.append_assoc]

/--
The response parser of an exchange with `config` and `method` after reading `fed` and, if `ended`,
the end of input, with what it reported: the codec's own run, from `Codec.Parser.start`.
-/
def parsed (config : ExchangeConfig) (method : Method) (fed : ByteArray) (ended : Bool) :
    Codec.Parser × List Codec.Obs :=
  let r := (Codec.Parser.start config.codec method).feed fed
  if ended then (r.1.finish.1, Codec.obsOf r.2 ++ Codec.obsOf r.1.finish.2)
  else (r.1, Codec.obsOf r.2)

theorem parsed_reach (config : ExchangeConfig) (method : Method) (fed : ByteArray) (ended : Bool) :
    Codec.Reach config.codec method (parsed config method fed ended).1
      (parsed config method fed ended).2 := by
  have h := Codec.Reach.feed fed (Codec.Reach.start (config := config.codec) (method := method))
  simp only [List.nil_append] at h
  cases ended
  · exact h
  · have := Codec.Reach.finish h
    simpa [parsed] using this

theorem parsed_empty (config : ExchangeConfig) (method : Method) :
    parsed config method .empty false = (Codec.Parser.start config.codec method, []) := by
  have h := Codec.Parser.feed_eq_run (Codec.Parser.start config.codec method) .empty
  simp only [parsed, Bool.false_eq_true, ↓reduceIte]
  rw [h.1, h.2]
  rfl

/-! ## What one batch of events says -/

theorem obs_head_mem {events : Array Codec.Event} {h : Codec.Head} :
    Codec.Obs.head h ∈ Codec.obsOf events ↔ Codec.Event.head h ∈ events := by
  simp only [Codec.obsOf, List.mem_flatMap, Array.mem_toList_iff]
  constructor
  · rintro ⟨e, he, hm⟩
    cases e <;> simp_all
  · intro he
    exact ⟨_, he, by simp⟩

theorem headOf_some {events : Array Codec.Event} {h : Codec.Head} (hh : headOf events = some h) :
    Codec.Obs.head h ∈ Codec.obsOf events := by
  obtain ⟨e, he, hf⟩ := Array.exists_of_findSome?_eq_some hh
  cases e <;> simp at hf
  subst hf
  exact obs_head_mem.2 he

theorem headOf_none {events : Array Codec.Event} (hh : headOf events = none) (h : Codec.Head) :
    Codec.Obs.head h ∉ Codec.obsOf events := by
  intro hm
  have he := obs_head_mem.1 hm
  have := Array.findSome?_eq_none_iff.1 hh _ he
  simp at this

theorem bytes_of_isEmpty {b : ByteArray} (hb : b.isEmpty = true) : b.data.toList = [] := by
  have h : b.size = 0 := by
    unfold ByteArray.isEmpty at hb
    simpa using hb
  have h' : b.data.toList.length = 0 := by
    rw [Array.length_toList]
    exact h
  exact List.eq_nil_of_length_eq_zero h'

theorem bodiesOf_bytes (events : Array Codec.Event) :
    heldBytes (bodiesOf events) = Codec.bodyBytes (Codec.obsOf events) := by
  simp only [bodiesOf, Codec.obsOf]
  generalize events.toList = l
  induction l with
  | nil => rfl
  | cons e l ih =>
    cases e with
    | head h => simpa using ih
    | body b =>
      by_cases hb : b.isEmpty = true
      · simp [hb, bytes_of_isEmpty hb, ih]
      · simp [hb, ih, Codec.bodyBytes_map_byte]
    | done => simpa using ih
    | error e => simpa using ih

/-! ## The invariant -/

/-- `true` unless the exchange failed. -/
def Live (ex : Exchange) : Prop :=
  ∀ f, ex.phase ≠ .failed f

/--
The codec relation of an exchange, given the bytes received (`fed`), whether the caller abandoned
(`ab`) and the body delivered (`body`): until the exchange fails, its parser is the codec's run over
`fed` (and the end of input once reported), its head is that run's head, and, unless the caller
abandoned, the body delivered and then the body held back are the body the run decoded; and once
finished without being abandoned, the response was complete and nothing was held back.
-/
structure CInv (ex : Exchange) (fed : ByteArray) (ab : Bool) (body : List UInt8) : Prop where
  /-- The abandonment recorded. -/
  abandoned : ex.abandoned = ab
  /-- Draining follows an abandonment. -/
  draining : ex.phase = .draining → ab = true
  /-- The parser is the codec's run over the bytes received. -/
  parser : Live ex → ex.parser = (parsed ex.config ex.method fed ex.inputEnded).1
  /-- The head is the run's head. -/
  head : Live ex → ex.head = ex.parser.head.map (·.response)
  /-- The body delivered and held back is the body decoded. -/
  body : Live ex → ab = false →
    body ++ heldBytes ex.held = Codec.bodyBytes (parsed ex.config ex.method fed ex.inputEnded).2
  /-- A finish nobody abandoned comes after a complete response, all of it handed over. -/
  finished : ∀ r, ex.phase = .finished r → ab = false → ex.parser.complete = true ∧ ex.held = []

/-- `CInv` within a step: of the state, with the body delivered before the step and by the actions. -/
def SInv (fed : ByteArray) (ab : Bool) (body : List UInt8) (s : S) : Prop :=
  CInv s.1 fed ab (body ++ actBody s.2)

/-- The fields `CInv` depends on, besides the phase. -/
structure CFrame (a b : Exchange) : Prop where
  parser : b.parser = a.parser
  config : b.config = a.config
  method : b.method = a.method
  inputEnded : b.inputEnded = a.inputEnded
  head : b.head = a.head
  held : b.held = a.held
  abandoned : b.abandoned = a.abandoned

/-- `CFrame` for an update of other fields. -/
macro "cframe_rfl" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem SInv.frame {fed : ByteArray} {ab : Bool} {body : List UInt8} {s s' : S}
    (h : SInv fed ab body s) (hf : CFrame s.1 s'.1) (hl : Live s'.1 → Live s.1)
    (hd : s'.1.phase = .draining → s.1.phase = .draining)
    (hfin : ∀ r, s'.1.phase = .finished r → ab = false →
      s'.1.parser.complete = true ∧ s'.1.held = [])
    (hb : actBody s'.2 = actBody s.2) : SInv fed ab body s' where
  abandoned := by rw [hf.abandoned]; exact h.abandoned
  draining hp := h.draining (hd hp)
  parser hl' := by rw [hf.parser, hf.config, hf.method, hf.inputEnded]; exact h.parser (hl hl')
  head hl' := by rw [hf.head, hf.parser]; exact h.head (hl hl')
  body hl' ha := by rw [hb, hf.held, hf.config, hf.method, hf.inputEnded]; exact h.body (hl hl') ha
  finished := hfin

/-- An update of other fields than `CInv`'s that keeps the phase and the body delivered. -/
theorem SInv.keep {fed : ByteArray} {ab : Bool} {body : List UInt8} {s s' : S}
    (h : SInv fed ab body s) (hf : CFrame s.1 s'.1) (hp : s'.1.phase = s.1.phase)
    (hb : actBody s'.2 = actBody s.2) : SInv fed ab body s' :=
  h.frame hf (fun hl f => by rw [← hp]; exact hl f) (fun h' => by rw [← hp]; exact h')
    (fun r h' ha => by rw [hf.parser, hf.held]; exact h.finished r (by rw [← hp]; exact h') ha) hb

/-- A failed exchange satisfies `SInv` for any bytes received and body delivered. -/
theorem SInv.failed {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S} {f : Failure}
    (hp : s.1.phase = .failed f) (ha : s.1.abandoned = ab) : SInv fed ab body s where
  abandoned := ha
  draining h := by rw [hp] at h; cases h
  parser hl := absurd hp (hl f)
  head hl := absurd hp (hl f)
  body hl := absurd hp (hl f)
  finished r h := by rw [hp] at h; cases h

theorem live_of_terminal {ex : Exchange} (ht : ex.terminal = false) : Live ex := by
  intro f hp
  simp [terminal, hp] at ht

/-! ## The parts of a step -/

theorem failNow_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S} (c : Cause)
    (d : String) (h : SInv fed ab body s) : SInv fed ab body ((failNow c d).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  rw [failNow_run]
  split
  · exact h
  · exact SInv.failed rfl h.abandoned

theorem finishNow_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S} (r : Bool)
    (h : SInv fed ab body s)
    (hok : s.1.terminal = false → ab = false → s.1.parser.complete = true ∧ s.1.held = []) :
    SInv fed ab body ((finishNow r).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  rw [finishNow_run]
  split
  · exact h
  · rename_i ht
    have ht' : ex.terminal = false := by simpa using ht
    exact h.frame (by cframe_rfl) (fun _ => live_of_terminal ht') (fun hp => by cases hp)
      (fun _ _ ha => hok ht' ha) (by simp [bodyOf])

theorem failOrDrop_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S} (c : Cause)
    (d : String) (h : SInv fed ab body s) : SInv fed ab body ((failOrDrop c d).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [failOrDrop, bind_run, getEx_run]
  split
  · rename_i hp
    exact finishNow_sinv false h (fun _ ha => by rw [h.draining hp] at ha; cases ha)
  · exact failNow_sinv c d h

theorem stopUpload_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S}
    (h : SInv fed ab body s) : SInv fed ab body (stopUpload.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [stopUpload, modifyEx_run]
  exact h.keep (by cframe_rfl) rfl rfl

theorem expireOne_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S}
    (h : SInv fed ab body s) : SInv fed ab body (expireOne.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [expireOne, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact h
  cases hp : ex.phase <;> simp only
  case draining =>
    split
    · simp only [bind_run]
      exact finishNow_sinv false h (fun _ ha => by rw [h.draining hp] at ha; cases ha)
    · exact h
  all_goals
    split
    · exact h
    · split
      · simp only [bind_run]; exact stopUpload_sinv h
      · simp only [bind_run]; exact failNow_sinv _ _ h
    · simp only [bind_run]; exact failNow_sinv _ _ h

theorem expire_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S}
    (h : SInv fed ab body s) : SInv fed ab body (expire.run s).2 := by
  simp only [expire, bind_run]
  have h1 := expireOne_sinv h
  generalize expireOne.run s = x at h1 ⊢
  obtain ⟨b, x⟩ := x
  cases b
  · exact h1
  · simp only [↓reduceIte]
    exact expireOne_sinv h1

theorem schedule_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S}
    (h : SInv fed ab body s) : SInv fed ab body (schedule.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [schedule, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact h
  have hr : ∀ s' : S, SInv fed ab body s' →
      SInv fed ab body ((do
        let ex ← getEx
        if !ex.readInFlight && ex.wantsInput then
          let readBy := if ex.uploadOver then some (ex.now + ex.config.gapMs) else none
          setEx { ex with readInFlight := true, readBy }
          emit (.read ex.config.readChunk) : StepM Unit).run s').2 := by
    intro ⟨ex', acts'⟩ h'
    simp only [getEx_bind_run]
    rcases Bool.eq_false_or_eq_true (!ex'.readInFlight && ex'.wantsInput) with hc | hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true, bind_run, setEx_run, emit_run]
    · exact h'.keep (by cframe_rfl) rfl (by simp [bodyOf])
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
    have key : SInv fed ab body (ex', acts.push (.write slice)) :=
      h.keep (by cframe_rfl) rfl (by simp [bodyOf])
    exact hr _ key
  · exact hr _ h

theorem release_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S}
    (h : SInv fed ab body s) : SInv fed ab body (release.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  rw [release_run]
  split
  · rename_i hp
    have hp' : ex.phase = .receiving := hp
    obtain ⟨pre, h1, h2, _⟩ := releaseList_spec ex.credit ex.held acts
    have hab : (body ++ actBody (releaseList ex.credit ex.held acts).2.2) ++
        heldBytes (releaseList ex.credit ex.held acts).2.1 =
        (body ++ actBody acts) ++ heldBytes ex.held := by
      rw [h2, actBody_foldl]
      conv => rhs; rw [h1]
      simp [List.append_assoc]
    refine ⟨h.abandoned, fun hd => by simp [hp'] at hd, fun hl => h.parser hl,
      fun hl => h.head hl, fun hl ha => ?_, fun r hr => by simp [hp'] at hr⟩
    simp only
    rw [hab]
    exact h.body hl ha
  · exact h

theorem settle_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S}
    (h : SInv fed ab body s) : SInv fed ab body (settle.run s).2 := by
  obtain ⟨ex, acts⟩ := s
  simp only [settle, getEx_bind_run]
  rcases Bool.eq_false_or_eq_true ex.terminal with ht | ht <;>
    simp only [ht, ↓reduceIte, Bool.false_eq_true]
  · exact h
  cases hp : ex.phase <;> simp only
  case receiving =>
    split
    · rename_i hb
      exact finishNow_sinv true h (fun _ _ => by
        simp only [bodyDone, Bool.and_eq_true, List.isEmpty_iff] at hb
        exact hb)
    · exact h
  case draining =>
    have hd := h.draining hp
    split
    · exact finishNow_sinv true h (fun _ ha => by rw [hd] at ha; cases ha)
    · split
      · exact finishNow_sinv false h (fun _ ha => by rw [hd] at ha; cases ha)
      · exact h
  all_goals exact h


theorem onError?_sinv {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S}
    (e : Option Codec.Error) (h : SInv fed ab body s) : SInv fed ab body ((onError? e).run s).2 := by
  cases e with
  | none => exact h
  | some e => exact failOrDrop_sinv _ _ h

/-- What `onHead?` changes: at most the head (if there was none) and the phase (to `receiving`). -/
theorem onHead?_spec (ho : Option Codec.Head) (ex : Exchange) (acts : Array ExchangeAction)
    (ht : ex.terminal = false) :
    let s' := ((onHead? ho).run (ex, acts)).2
    s'.1.parser = ex.parser ∧ s'.1.config = ex.config ∧ s'.1.method = ex.method ∧
      s'.1.inputEnded = ex.inputEnded ∧ s'.1.held = ex.held ∧ s'.1.abandoned = ex.abandoned ∧
      actBody s'.2 = actBody acts ∧ s'.1.terminal = false ∧
      (s'.1.phase = ex.phase ∨ s'.1.phase = .receiving) ∧
      (s'.1.head = ex.head ∧ (ho = none ∨ ex.head.isSome = true) ∨
        ex.head = none ∧ ∃ h, ho = some h ∧ s'.1.head = some h.response) := by
  cases ho with
  | none =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ht, Or.inl ?_, Or.inl ⟨rfl, Or.inl rfl⟩⟩ <;> trivial
  | some h =>
    simp only [onHead?, onHead, getEx_bind_run]
    rcases Bool.eq_false_or_eq_true (ex.terminal || ex.head.isSome) with hc | hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true]
    · simp only [ht, Bool.false_or] at hc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ht, Or.inl ?_, Or.inl ⟨rfl, Or.inr hc⟩⟩ <;> trivial
    · simp only [Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hc
      simp only [bind_run, setEx_run, emit_run]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp [bodyOf], by simp [terminal], Or.inr ?_,
        Or.inr ⟨hc.2, h, ?_, ?_⟩⟩ <;> trivial

/--
What `onBodies` changes: while draining, the phase may end, and nothing that `CInv` cares about
otherwise; in any other phase it keeps the phase and appends the pieces to the body delivered and
held back.
-/
theorem onBodies_spec (bs : List ByteArray) (ex : Exchange) (acts : Array ExchangeAction) :
    let s' := ((onBodies bs).run (ex, acts)).2
    s'.1.parser = ex.parser ∧ s'.1.config = ex.config ∧ s'.1.method = ex.method ∧
      s'.1.inputEnded = ex.inputEnded ∧ s'.1.head = ex.head ∧ s'.1.abandoned = ex.abandoned ∧
      (ex.phase = .draining → s'.1.phase = .draining ∨ s'.1.phase = .finished false) ∧
      (ex.phase ≠ .draining → s'.1.phase = ex.phase ∧
        actBody s'.2 ++ heldBytes s'.1.held = actBody acts ++ heldBytes ex.held ++ heldBytes bs) := by
  simp only [onBodies, getEx_bind_run]
  split
  · rename_i hp
    simp only [bind_run, setEx_run]
    split
    · rw [finishNow_run]
      simp only [terminal, hp, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => Or.inr (by simp [reusableNow]),
        fun h => absurd rfl h⟩ <;> trivial
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => Or.inl hp, fun h => absurd hp h⟩ <;> trivial
  · rename_i hp
    simp only [bind_run, setEx_run]
    rw [release_run]
    split
    · obtain ⟨pre, h1, h2, _⟩ := releaseList_spec ex.credit (ex.held ++ bs) acts
      refine ⟨by trivial, by trivial, by trivial, by trivial, by trivial, by trivial,
        fun h => absurd h hp, fun _ => ⟨by trivial, ?_⟩⟩
      simp only
      rw [h2, actBody_foldl, List.append_assoc, ← heldBytes_append, ← h1, heldBytes_append]
      simp [List.append_assoc]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hp,
        fun _ => ⟨?_, by simp [List.append_assoc]⟩⟩ <;> trivial

/--
**`absorb` keeps the codec relation**, given what the parser it takes over was fed (`fed₀`, before
the end of input) and what it is now (`fed₁`, `ended`): the parser and events `absorb` acts on are the
codec's next step.
-/
theorem absorb_sinv {fed₀ fed₁ : ByteArray} {ab : Bool} {body : List UInt8} {ex : Exchange}
    {acts : Array ExchangeAction} {p₁ : Codec.Parser} {events : Array Codec.Event} {ended : Bool}
    (ht : ex.terminal = false) (hab : ex.abandoned = ab) (hdr : ex.phase = .draining → ab = true)
    (hp : ex.parser = (parsed ex.config ex.method fed₀ false).1)
    (hh : ex.head = ex.parser.head.map (·.response))
    (hb : ab = false →
      body ++ actBody acts ++ heldBytes ex.held = Codec.bodyBytes (parsed ex.config ex.method fed₀ false).2)
    (hie : ex.inputEnded = ended)
    (hnext : parsed ex.config ex.method fed₁ ended =
      (p₁, (parsed ex.config ex.method fed₀ false).2 ++ Codec.obsOf events)) :
    SInv fed₁ ab body ((absorb (p₁, events)).run (ex, acts)).2 := by
  -- What the codec says about the step from the old parser to the new one.
  have g₀ := (parsed_reach ex.config ex.method fed₀ false).good
  have g₁ := (parsed_reach ex.config ex.method fed₁ ended).good
  rw [hnext] at g₁
  have keep : ∀ h, (parsed ex.config ex.method fed₀ false).1.head = some h → p₁.head = some h :=
    fun h h0 => (g₁.head h).1 (List.mem_append_left _ ((g₀.head h).2 h0))
  have newHead : ∀ h, headOf events = some h → p₁.head = some h :=
    fun h h0 => (g₁.head h).1 (List.mem_append_right _ (headOf_some h0))
  have sameHead : headOf events = none → p₁.head = (parsed ex.config ex.method fed₀ false).1.head := by
    intro hn
    cases hq : p₁.head with
    | none =>
      cases hq0 : (parsed ex.config ex.method fed₀ false).1.head with
      | none => rfl
      | some h => rw [keep h hq0] at hq; cases hq
    | some h =>
      rcases List.mem_append.1 ((g₁.head h).2 hq) with h1 | h1
      · exact ((g₀.head h).1 h1).symm
      · exact absurd h1 (headOf_none hn h)
  let ex1 : Exchange := { ex with parser := p₁ }
  have ht1 : ex1.terminal = false := ht
  simp only [absorb, onEvents, bind_run, modifyEx_run]
  apply settle_sinv
  apply onError?_sinv
  -- The state after `onHead?` and after `onBodies`.
  show SInv fed₁ ab body
    ((onBodies (bodiesOf events)).run ((onHead? (headOf events)).run (ex1, acts)).2).2
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := onHead?_spec (headOf events) ex1 acts ht1
  generalize ((onHead? (headOf events)).run (ex1, acts)).2 = s2 at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ⊢
  obtain ⟨ex2, acts2⟩ := s2
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := onBodies_spec (bodiesOf events) ex2 acts2
  generalize ((onBodies (bodiesOf events)).run (ex2, acts2)).2 = s3 at b1 b2 b3 b4 b5 b6 b7 b8 ⊢
  obtain ⟨ex3, acts3⟩ := s3
  simp only at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 b1 b2 b3 b4 b5 b6 b7 b8
  -- The head after `onHead?` is the new parser's.
  have hhead : ex2.head = p₁.head.map (·.response) := by
    rw [hp] at hh
    rcases a10 with ⟨h', hor⟩ | ⟨hn, h, hho, h'⟩
    · rw [h']
      show ex.head = _
      rcases hor with hn | hs
      · rw [sameHead hn]; exact hh
      · cases hq0 : (parsed ex.config ex.method fed₀ false).1.head with
        | none => rw [hq0] at hh; change ex.head.isSome = true at hs; rw [hh] at hs; cases hs
        | some h0 => rw [hq0] at hh; rw [hh, keep h0 hq0] <;> rfl
    · rw [h', newHead h hho]; rfl
  -- Phases: draining only if it was draining before.
  have hdr2 : ex2.phase = .draining → ab = true := by
    intro hd
    rcases a9 with h' | h'
    · exact hdr (by rw [← h']; exact hd)
    · rw [h'] at hd; cases hd
  refine ⟨by rw [b6, a6]; exact hab, ?_, ?_, ?_, ?_, ?_⟩
  · intro hd
    by_cases h2 : ex2.phase = .draining
    · exact hdr2 h2
    · rw [(b8 h2).1] at hd; exact absurd hd h2
  · intro _
    rw [b1, a1, b2, a2, b3, a3, b4, a4, hie, hnext]
  · intro _
    rw [b5, hhead, b1, a1]
  · intro _ ha
    have h2 : ex2.phase ≠ .draining := fun hd => by rw [hdr2 hd] at ha; cases ha
    rw [b2, a2, b3, a3, b4, a4, hie, hnext, Codec.bodyBytes_append, ← hb ha, ← bodiesOf_bytes]
    rw [List.append_assoc, (b8 h2).2, a7, a5]
    simp [List.append_assoc] <;> rfl
  · intro r hr ha
    have h2 : ex2.phase ≠ .draining := fun hd => by rw [hdr2 hd] at ha; cases ha
    rw [(b8 h2).1] at hr
    rcases a9 with h' | h'
    · rw [h'] at hr
      have hr' : ex.phase = .finished r := hr
      simp [terminal, hr'] at ht
    · rw [h'] at hr; cases hr

/-- A failure on a state that has not ended satisfies `SInv` for any bytes received. -/
theorem failNow_sinv_any {fed : ByteArray} {ab : Bool} {body : List UInt8} {s : S} (c : Cause)
    (d : String) (ht : s.1.terminal = false) (ha : s.1.abandoned = ab) :
    SInv fed ab body ((failNow c d).run s).2 := by
  obtain ⟨ex, acts⟩ := s
  rw [failNow_run]
  simp only at ht
  simp only [ht, Bool.false_eq_true, ↓reduceIte]
  exact SInv.failed rfl ha

/-- The bytes received after an event, as the checker's model counts them. -/
def fedAfter (ex : Exchange) (fed : ByteArray) : ExchangeEvent → ByteArray
  | .received b => if b.isEmpty || ex.inputEnded then fed else fed ++ b
  | _ => fed

/-- Whether the caller has abandoned, after an event. -/
def abAfter (ab : Bool) : ExchangeEvent → Bool
  | .abandon => true
  | _ => ab

/-- Once abandoned, `CInv` asks nothing of the body. -/
theorem CInv.abandon {ex ex' : Exchange} {fed : ByteArray} {ab : Bool} {body body' : List UInt8}
    (hc : CInv ex fed ab body) (hl : Live ex' → Live ex) (hpa : ex'.parser = ex.parser)
    (hco : ex'.config = ex.config) (hme : ex'.method = ex.method)
    (hie : ex'.inputEnded = ex.inputEnded) (hhe : ex'.head = ex.head)
    (hab : ex'.abandoned = true) : CInv ex' fed true body' where
  abandoned := hab
  draining _ := rfl
  parser h := by rw [hpa, hco, hme, hie]; exact hc.parser (hl h)
  head h := by rw [hhe, hpa]; exact hc.head (hl h)
  body _ h := by cases h
  finished _ _ h := by cases h

theorem handle_sinv (e : ExchangeEvent) {ex : Exchange} {fed : ByteArray} {ab : Bool}
    {body : List UInt8} (hc : CInv ex fed ab body) (ht : ex.terminal = false) :
    SInv (fedAfter ex fed e) (abAfter ab e) body ((handle e).run (ex, #[])).2 := by
  have h0 : SInv fed ab body (ex, #[]) := by simpa [SInv] using hc
  have hl := live_of_terminal ht
  cases e with
  | received bytes =>
    simp only [handle, fedAfter, abAfter]
    rcases Bool.eq_false_or_eq_true bytes.isEmpty with hb | hb <;>
      simp only [hb, ↓reduceIte, Bool.true_or, Bool.false_or, Bool.false_eq_true]
    · exact h0
    simp only [bind_run, setEx_run, getEx_run]
    rcases Bool.eq_false_or_eq_true ex.inputEnded with hie' | hie' <;>
      simp only [hie', Bool.false_eq_true, ↓reduceIte]
    · split
      · exact failNow_sinv_any _ _ ht hc.abandoned
      · exact h0.keep ⟨rfl, rfl, rfl, hie'.symm, rfl, rfl, rfl⟩ rfl rfl
    · split
      · exact failNow_sinv_any _ _ ht hc.abandoned
      · have hp := hc.parser hl
        rw [hie'] at hp
        have hb' := hc.body hl
        rw [hie'] at hb'
        refine absorb_sinv (fed₀ := fed) (p₁ := (ex.parser.feed bytes).1)
          (events := (ex.parser.feed bytes).2) ht hc.abandoned hc.draining hp (hc.head hl)
          (fun ha => by simpa using hb' ha) rfl ?_
        have hs := Codec.Parser.feed_append (Codec.Parser.start ex.config.codec ex.method) fed bytes
        simp only [parsed, Bool.false_eq_true, ↓reduceIte] at hp ⊢
        rw [hs.1, hs.2, hp]
  | endOfInput =>
    simp only [handle, fedAfter, abAfter, bind_run, setEx_run, getEx_run]
    rcases Bool.eq_false_or_eq_true ex.inputEnded with hie' | hie' <;>
      simp only [hie', Bool.false_eq_true, ↓reduceIte]
    · exact h0.keep ⟨rfl, rfl, rfl, hie'.symm, rfl, rfl, rfl⟩ rfl rfl
    · split
      · exact failNow_sinv_any _ _ ht hc.abandoned
      · have hp := hc.parser hl
        rw [hie'] at hp
        have hb' := hc.body hl
        rw [hie'] at hb'
        refine absorb_sinv (fed₀ := fed) (p₁ := ex.parser.finish.1)
          (events := ex.parser.finish.2) ht hc.abandoned hc.draining hp (hc.head hl)
          (fun ha => by simpa using hb' ha) rfl ?_
        simp only [parsed, Bool.false_eq_true, ↓reduceIte] at hp ⊢
        rw [hp]
  | written count =>
    simp only [handle, fedAfter, abAfter, getEx_bind_run]
    cases hw : ex.writeInFlight with
    | none => exact h0
    | some len =>
      simp only [setEx_run]
      have leaf : ∀ ex' : Exchange, CFrame ex ex' →
          (ex'.phase = ex.phase ∨ ex'.phase = .awaitingHead) → SInv fed ab body (ex', #[]) :=
        fun ex' hf hp => h0.frame hf (fun _ => hl)
          (fun hd => by rcases hp with hp | hp <;> rw [hp] at hd <;> first | exact hd | cases hd)
          (fun r hr ha => by
            rcases hp with hp | hp <;> rw [hp] at hr
            · simp [terminal, hr] at ht
            · cases hr)
          rfl
      cases hp : ex.phase <;> simp only
      case sending =>
        by_cases hd : ex.written + min count len ≥ ex.headBytes <;> simp only [hd, ↓reduceIte] <;>
          split <;> first
            | exact leaf _ (by cframe_rfl) (Or.inr rfl)
            | exact leaf _ (by cframe_rfl) (Or.inl hp.symm ▸ Or.inl rfl)
            | exact leaf _ (by cframe_rfl) (Or.inl (by simp [hp]))
      all_goals split <;> exact leaf _ (by cframe_rfl) (Or.inl (by simp [hp]))
  | writeFailed detail =>
    simp only [handle, fedAfter, abAfter, getEx_bind_run]
    rcases Bool.eq_false_or_eq_true ex.writeInFlight.isNone with hn | hn <;>
      simp only [hn, ↓reduceIte, Bool.false_eq_true]
    · exact h0
    · simp only [bind_run, setEx_run]
      have h1 : SInv fed ab body ({ ex with writeInFlight := none, writeBy := none }, #[]) :=
        h0.keep (by cframe_rfl) rfl rfl
      split
      · exact failNow_sinv _ _ h1
      · rcases Bool.eq_false_or_eq_true ex.uploadStopped with hu | hu <;>
          simp only [hu, ↓reduceIte, Bool.false_eq_true, bind_run, getEx_run, setEx_run]
        · exact h1.keep (by cframe_rfl) rfl rfl
        · exact stopUpload_sinv (h1.keep (by cframe_rfl) rfl rfl)
  | readFailed detail =>
    simp only [handle, fedAfter, abAfter, bind_run, modifyEx_run]
    exact failOrDrop_sinv _ _ (h0.keep (by cframe_rfl) rfl rfl)
  | wantBody bytes =>
    simp only [handle, fedAfter, abAfter, bind_run, setEx_run]
    have h1 : SInv fed ab body ({ ex with credit := ex.credit + bytes }, #[]) :=
      h0.keep (by cframe_rfl) rfl rfl
    split
    · simp only [↓reduceIte, bind_run]
      exact settle_sinv (release_sinv h1)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact h1
  | tick =>
    simp only [handle, fedAfter, abAfter]
    exact h0
  | abandon =>
    simp only [handle, fedAfter, abAfter, bind_run, setEx_run]
    let ex1 : Exchange := { ex with abandoned := true }
    have h1 : SInv fed true body (ex1, #[]) :=
      CInv.abandon hc (fun _ => hl) rfl rfl rfl rfl rfl rfl
    split
    · exact failNow_sinv _ _ h1
    · exact failNow_sinv _ _ h1
    · split
      · simp only [bind_run, setEx_run]
        exact settle_sinv (CInv.abandon hc (fun _ => hl) rfl rfl rfl rfl rfl rfl)
      · exact finishNow_sinv false h1 (fun _ h => by cases h)
    · exact h1

/-- The model's bytes received, abandonment and body after a step that does not ignore its event. -/
theorem see_fed (l : List ExchangeAction) (m : Obs) : (l.foldl Obs.see m).fed = m.fed := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih]; cases a <;> rfl

theorem see_abandoned (l : List ExchangeAction) (m : Obs) :
    (l.foldl Obs.see m).abandoned = m.abandoned := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih]; cases a <;> rfl

theorem see_body (l : List ExchangeAction) (m : Obs) :
    (l.foldl Obs.see m).body = m.body ++ l.flatMap bodyOf := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    cases a <;> simp [Obs.see, bodyOf, List.append_assoc]

/--
**The codec relation holds in every run**: until the exchange fails, its parser is the codec's run
over the bytes the checker's model counts as received (and the end of input once reported), its head
is that run's head, and unless the caller abandoned, the body delivered and the body held back are
the body the run decoded; a finish nobody abandoned comes after a complete response, all of it
handed over.
-/
theorem Observed.cinv {ex : Exchange} {m : Obs} (h : Observed ex m) :
    CInv ex m.fed m.abandoned m.body := by
  induction h with
  | begin req now deadline =>
    have h0 : SInv .empty false [] (initial req now deadline, #[]) := by
      refine (show CInv (initial req now deadline) .empty false ([] ++ actBody #[]) from
        ⟨rfl, fun hp => by simp [initial] at hp, fun _ => ?_, fun _ => ?_, fun _ _ => ?_,
          fun _ hp => by simp [initial] at hp⟩)
      · simp [initial, parsed_empty]
      · simp [initial, Codec.Parser.start]
      · simp [initial, parsed_empty]
    have h1 := schedule_sinv (expire_sinv h0)
    have hb := begin_def req now deadline
    simp only [bind_run] at hb
    rw [← hb] at h1
    rw [← Array.foldl_toList, see_fed, see_abandoned, see_body]
    simpa [SInv, actBody] using h1
  | @step ex m now e hob ih =>
    have ha := hob.agrees
    rcases step_cases ex now e with ⟨hc, hs⟩ | ⟨hc, _⟩
    · rw [hs]
      simp only [Array.foldl_empty]
      cases ht : ex.terminal
      · simp only [ht, Bool.false_or, stale] at hc
        have hne : m.ended = false := by rw [ha.ended, ht]
        cases e
        case received b =>
          cases hnd : ex.nextDeadline <;> simp only [hnd, Bool.and_eq_true, decide_eq_true_eq] at hc
          · cases hc
          · simpa [Obs.observe, hne, hc.1] using ih
        case tick => simpa [Obs.observe, hne] using ih
        all_goals (exfalso; revert hc; simp)
      · have hne : m.ended = true := by rw [ha.ended, ht]
        simpa [Obs.observe, hne] using ih
    · have ht := not_terminal_of hc
      have hne : m.ended = false := by rw [ha.ended, ht]
      rw [step_run hc]
      simp only [bind_run]
      have ih' : CInv (advanced ex now) m.fed m.abandoned m.body :=
        ⟨ih.1, ih.2, ih.3, ih.4, ih.5, ih.6⟩
      have h1 := handle_sinv e ih' ht
      have h2 := schedule_sinv (expire_sinv h1)
      rw [← Array.foldl_toList, see_fed, see_abandoned, see_body]
      have hfed : (m.observe e).fed = fedAfter (advanced ex now) m.fed e := by
        cases e <;> simp [Obs.observe, hne, fedAfter, ha.eofSeen] <;> (try split) <;> rfl
      have hab : (m.observe e).abandoned = abAfter m.abandoned e := by
        cases e <;> simp [Obs.observe, hne, abAfter] <;> (try split) <;> rfl
      have hbody : (m.observe e).body = m.body := by
        cases e <;> simp [Obs.observe, hne] <;> split <;> rfl
      simp only
      rw [hfed, hab, hbody]
      simpa [SInv, actBody] using h2

/-! ## What a finish means for the bytes received -/

theorem step_method {ex : Exchange} (hi : Inv ex) (now : Timestamp) (e : ExchangeEvent) :
    (ex.step now e).1.method = ex.method := by
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨_, hg⟩
  · rw [hs]
  · rw [(hg hi).fixed.method]
    cases e <;> simp only [startOf] <;> (try split) <;> rfl

theorem step_finish {ex : Exchange} (hi : Inv ex) {now : Timestamp} {e : ExchangeEvent}
    {r : Bool} (hm : .finish r ∈ (ex.step now e).2) : (ex.step now e).1.phase = .finished r := by
  rcases step_cases ex now e with ⟨_, hs⟩ | ⟨_, hg⟩
  · rw [hs] at hm; simp at hm
  · exact ((hg hi).acts _ hm).1

/--
**A reusable finish is exactly one response** (checker: "reusable only when safe", the clause that
the bytes read are exactly one reusable response; and, unless abandoned, "a finished response
delivered its whole body").  When a step reports the connection reusable, the codec run over every
byte the checker's model counts as received is complete, framed with certainty, and reusable; those
bytes are `hd.interim` interim heads, then the final head `hd` exactly as the codec reports it, then a
body of the kind its framing declares, carrying the payload the codec decoded, and nothing after it;
`hd`'s framing and `Std.Http` head are the ones its status line and fields give for the request's
method, and it allows keep-alive only if its own version and fields do (`Codec.HeadOK`); its framing
is certain and it allows keep-alive; the head the core holds (the one its `deliverHead` handed over,
`step_deliverHead`) is `hd`'s; and unless the caller abandoned the body, the body the core delivered
is that payload.  The interim heads' part in the keep-alive
verdict is the codec's code, not a theorem.
-/
theorem observed_finish_codec {ex : Exchange} {m : Obs} (h : Observed ex m) {now : Timestamp}
    {e : ExchangeEvent} (hm : .finish true ∈ (ex.step now e).2) :
    let m' := (ex.step now e).2.foldl Obs.see { m.observe e with now := max m.now now }
    let r := (Codec.Parser.start ex.config.codec ex.method).feed m'.fed
    r.1.completeCertain = true ∧ r.1.reusable = true ∧
      ∃ hd pre hb body, m'.fed.data.toList = pre ++ hb ++ body ∧
        Codec.InterimHeads pre hd.interim ∧
        Codec.HeadBytesOf hd.http10 hd.code hd.reason hd.fields hb ∧ r.1.head = some hd ∧
        Codec.HeadOK (Codec.Parser.isHeadMethod ex.method) hd ∧
        hd.framing.certain = true ∧ hd.keepAlive = true ∧
        (ex.step now e).1.head = some hd.response ∧
        Codec.BodyOf hd.framing body (Codec.bodyBytes (Codec.obsOf r.2)) ∧
        (m'.abandoned = false → m'.body = Codec.bodyBytes (Codec.obsOf r.2)) := by
  intro m' r
  have hi := h.reachable.inv
  have hc := (Observed.step now e h).cinv
  obtain ⟨hph, hre⟩ := step_finish_reusable hi hm
  obtain ⟨hcfg, _, _⟩ := step_fixed hi now e
  have hme := step_method hi now e
  have hl : Live (ex.step now e).1 := by intro f hf; rw [hph] at hf; cases hf
  have hpr : (ex.step now e).1.parser = r.1 := by
    have hp := hc.parser hl
    rw [hre.noEnd, hcfg, hme] at hp
    simpa [parsed] using hp
  have hreu : r.1.reusable = true := by rw [← hpr]; exact hre.codec
  have hri := (Codec.Parser.reusable_iff r.1).1 hreu
  have hcc : r.1.completeCertain = true := by
    simp only [Codec.Parser.reusable, Bool.and_eq_true] at hreu
    exact hreu.1.1.1
  obtain ⟨hd, pre, hb, body, extra, hmem, hbytes, hint, hhb, hbody, hext, _⟩ :=
    Codec.response_sound ex.config.codec ex.method m'.fed false r.1 (Codec.obsOf r.2)
      (by simp [r]) (by simp [r]) hri.1
  have hrr := Codec.Reach.feed m'.fed
    (Codec.Reach.start (config := ex.config.codec) (method := ex.method))
  have g := hrr.good
  have hhd : r.1.head = some hd := (g.head hd).1 (by simpa [r] using hmem)
  have hok := g.inv.1 hd (by simpa [r] using hhd)
  rw [hrr.isHead] at hok
  obtain ⟨h', hh', hcert, hka⟩ := hri.2.1
  rw [hhd] at hh'
  cases hh'
  have hx : extra = [] := hext.2 hri.2.2.1
  refine ⟨hcc, hreu, hd, pre, hb, body, by rw [hbytes, hx, List.append_nil], hint, hhb, hhd, hok,
    hcert, hka, ?_, hbody, fun ha => ?_⟩
  · rw [hc.head hl, hpr, hhd]
    rfl
  · have hbd := hc.body hl ha
    rw [hre.delivered, heldBytes_nil, List.append_nil, hre.noEnd, hcfg, hme] at hbd
    simp only [parsed, Bool.false_eq_true, ↓reduceIte] at hbd
    exact hbd

/--
**Any finish the caller did not abandon is after a complete response** (checker: "finish only after
a complete response", "a finished response delivered its whole body").  When a step finishes the
exchange, reusable or not, and the caller did not abandon it, the codec run over the bytes the
checker's model counts as received, and the end of input if the model saw it, is complete; those
bytes are `hd.interim` interim heads, the final head `hd` exactly as the codec reports it, a body of
the kind its framing declares, and perhaps bytes after it (none for a body delimited by the end of
input, which the model saw end); `hd`'s framing and `Std.Http` head are the ones its status line and
fields give for the request's method, and it allows keep-alive only if its own version and fields do
(`Codec.HeadOK`); the head the core holds
(the one its `deliverHead` handed over) is `hd`'s; and the body it delivered is that body's payload.
-/
theorem observed_finish_complete {ex : Exchange} {m : Obs} (h : Observed ex m) {now : Timestamp}
    {e : ExchangeEvent} {reusable : Bool} (hm : .finish reusable ∈ (ex.step now e).2) :
    let m' := (ex.step now e).2.foldl Obs.see { m.observe e with now := max m.now now }
    let p := parsed ex.config ex.method m'.fed m'.eofSeen
    m'.abandoned = false →
    p.1.complete = true ∧
      ∃ hd pre hb body extra, m'.fed.data.toList = pre ++ hb ++ body ++ extra ∧
        Codec.InterimHeads pre hd.interim ∧
        Codec.HeadBytesOf hd.http10 hd.code hd.reason hd.fields hb ∧ p.1.head = some hd ∧
        Codec.HeadOK (Codec.Parser.isHeadMethod ex.method) hd ∧
        (ex.step now e).1.head = some hd.response ∧ Codec.BodyOf hd.framing body m'.body ∧
        (hd.framing = .untilClose → extra = [] ∧ m'.eofSeen = true) := by
  intro m' p ha
  have hi := h.reachable.inv
  have hob := Observed.step now e h
  have hc := hob.cinv
  have hag := hob.agrees
  have hph := step_finish hi hm
  obtain ⟨hcfg, _, _⟩ := step_fixed hi now e
  have hme := step_method hi now e
  have hl : Live (ex.step now e).1 := by intro f hf; rw [hph] at hf; cases hf
  obtain ⟨hcomp, hheld⟩ := hc.finished reusable hph ha
  have hpp : (ex.step now e).1.parser = p.1 := by
    have hp := hc.parser hl
    rw [← hag.eofSeen, hcfg, hme] at hp
    exact hp
  have hdone : p.1.phase = .done := by
    rw [← hpp]
    unfold Codec.Parser.complete at hcomp
    split at hcomp
    · assumption
    · cases hcomp
  obtain ⟨hd, pre, hb, body, extra, hmem, hbytes, hint, hhb, hbody, _, huc⟩ :=
    Codec.response_sound ex.config.codec ex.method m'.fed m'.eofSeen p.1 p.2
      (by simp only [p, parsed]; split <;> rfl) (by simp only [p, parsed]; split <;> rfl) hdone
  have hrr := parsed_reach ex.config ex.method m'.fed m'.eofSeen
  have g := hrr.good
  have hhd : p.1.head = some hd := (g.head hd).1 hmem
  have hok := g.inv.1 hd hhd
  rw [hrr.isHead] at hok
  -- Before the end of input, the codec never completes a body delimited by it.
  have heof : hd.framing = .untilClose → m'.eofSeen = true := by
    intro hu
    cases hE : m'.eofSeen
    · exfalso
      have hn1 : Codec.NoUCDone
          ((Codec.Parser.start ex.config.codec ex.method).feed m'.fed).1 := by
        have := Codec.Parser.run_noUCDone m'.fed.data.toList
          (Codec.start_good ex.config.codec ex.method) (p := Codec.Parser.start ex.config.codec ex.method)
          (by intro h hh; simp [Codec.Parser.start] at hh)
        rw [← (Codec.Parser.feed_eq_run _ m'.fed).1] at this
        exact this
      have hp1 : p.1 = ((Codec.Parser.start ex.config.codec ex.method).feed m'.fed).1 := by
        simp [p, parsed, hE]
      rw [hp1] at hhd hdone
      exact hn1 hd hhd hdone hu
    · rfl
  refine ⟨by rw [← hpp]; exact hcomp, hd, pre, hb, body, extra, hbytes, hint, hhb, hhd, hok, ?_, ?_,
    fun hu => ⟨huc hu, heof hu⟩⟩
  · rw [hc.head hl, hpp, hhd]
    rfl
  · have hbd := hc.body hl ha
    rw [hheld, heldBytes_nil, List.append_nil, ← hag.eofSeen, hcfg, hme] at hbd
    rw [hbd]
    exact hbody

/--
**The body is the response's** (checker: "the body is the response's").  In every run, until the
exchange fails and unless the caller abandoned it, the body delivered so far is a prefix of the body
the codec decoded from the bytes the checker's model counts as received (and the end of input if it
saw it).  `Codec.feed_respSound` says how that body sits in the bytes, and `Codec.finish_respSound`
how the end of input changes that.
-/
theorem observed_body_prefix {ex : Exchange} {m : Obs} (h : Observed ex m)
    (hl : ∀ f, ex.phase ≠ .failed f) (ha : m.abandoned = false) :
    ∃ rest, m.body ++ rest = Codec.bodyBytes (parsed ex.config ex.method m.fed m.eofSeen).2 := by
  have hc := h.cinv
  rw [h.agrees.eofSeen]
  exact ⟨_, hc.body hl ha⟩

end LeanHttp.Exchange
