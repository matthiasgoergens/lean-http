module

public import LeanHttp.Codec.Proofs.Body

@[expose] public section

/-!
# The shape of what a run delivers, and what its body bytes are

- **Shape** (`reach_shape`): every run is observed as nothing yet, as an error, or as the final head
  followed by body bytes, then nothing more yet, the end, or an error.  So the head comes first and
  once, body bytes come only after it, and nothing follows the end or an error.
- **Content-Length bodies** (`roundtrip_length`): after a head that declares `n` bytes, the next `n`
  bytes, however they are cut into pieces, are delivered as the body, as they are, and end the
  response.
- **Bodies delimited by the end of input** (`roundtrip_untilClose`): the bytes after the head, up to
  the body limit, are delivered as they are, and the end of input ends the response.
-/

namespace LeanHttp.Codec

/--
The observations a phase ends with: the end once done, the error once failed, nothing otherwise.
-/
def tailObs : Phase → List Obs
  | .done => [.done]
  | .failed e => [.error e]
  | _ => []

/--
The observations agree with the state's shape: before the final head, nothing or the error; after
it, the head, body bytes, then the end of the phase.
-/
def Shape (p : Parser) (obs : List Obs) : Prop :=
  match p.head with
  | none => obs = tailObs p.phase
  | some h => ∃ bytes : List UInt8, obs = .head h :: (bytes.map .byte ++ tailObs p.phase)

namespace Parser

theorem startBody_shape {p : Parser} {h : Head} :
    Shape (p.startBody h).1 (obsOf (p.startBody h).2) := by
  have hhead : (p.startBody h).1.head = some h := by
    unfold startBody; dsimp only; split <;> (try split) <;> rfl
  unfold Shape
  rw [hhead]
  dsimp only
  refine ⟨[], ?_⟩
  unfold startBody
  dsimp only
  split <;> (try split) <;> simp [tailObs]

theorem shape_some {p : Parser} {obs : List Obs} {h : Head} (hs : Shape p obs)
    (hh : p.head = some h) :
    ∃ bytes : List UInt8, obs = .head h :: (bytes.map .byte ++ tailObs p.phase) := by
  simpa [Shape, hh] using hs

theorem head_of_body {p : Parser} {b : Body}
    (hphase : PhaseOK p.config.maxBody p.head p.phase p.delivered) (hp : p.phase = .body b) :
    ∃ h, p.head = some h := by
  cases hh : p.head with
  | none => simp_all [PhaseOK]
  | some h => exact ⟨h, rfl⟩

/--
Every byte keeps the observations in the state's shape.
-/
theorem stepByte_shape {p : Parser} {obs : List Obs} (b : UInt8) (hg : Good p obs)
    (hs : Shape p obs) : Shape (p.stepByte b).1 (obs ++ obsOf (p.stepByte b).2) := by
  have hphase := hg.inv.2
  unfold stepByte
  split
  · rename_i hsh hp
    have hnone : p.head = none := by cases hph : p.head <;> simp_all [PhaseOK]
    have hobs : obs = [] := by simpa [Shape, hnone, hp, tailObs] using hs
    subst hobs
    split
    · simp [Shape, hnone, tailObs]
    · simp [Shape, fail, hnone, tailObs]
    · simpa using startBody_shape
  · -- Content-Length
    rename_i r hp
    obtain ⟨h, hh⟩ := head_of_body hphase hp
    obtain ⟨bytes, rfl⟩ := shape_some hs hh
    split
    · simp only [Shape, hh]
      exact ⟨bytes ++ [b], by simp [hp, tailObs]⟩
    · simp only [Shape, hh]
      exact ⟨bytes ++ [b], by simp [hp, tailObs]⟩
  · -- until close
    rename_i room hp
    obtain ⟨h, hh⟩ := head_of_body hphase hp
    obtain ⟨bytes, rfl⟩ := shape_some hs hh
    split
    · simp only [Shape, fail, hh]
      exact ⟨bytes, by simp [hp, tailObs]⟩
    · simp only [Shape, hh]
      exact ⟨bytes ++ [b], by simp [hp, tailObs]⟩
  · -- chunked
    rename_i c hp
    obtain ⟨h, hh⟩ := head_of_body hphase hp
    obtain ⟨bytes, rfl⟩ := shape_some hs hh
    split
    · simp only [Shape, hh]
      exact ⟨bytes, by simp [hp, tailObs]⟩
    · simp only [Shape, hh]
      exact ⟨bytes ++ [b], by simp [hp, tailObs]⟩
    · simp only [Shape, hh]
      exact ⟨bytes, by simp [hp, tailObs]⟩
    · simp only [Shape, fail, hh]
      exact ⟨bytes, by simp [hp, tailObs]⟩
  · simpa [Shape] using hs
  · simpa using hs

theorem run_shape {p : Parser} {obs : List Obs} (xs : List UInt8) (hg : Good p obs)
    (hs : Shape p obs) : Shape (p.run xs).1 (obs ++ obsOf (p.run xs).2) := by
  induction xs generalizing p obs with
  | nil => simpa using hs
  | cons b bs ih =>
    have := ih (stepByte_good b hg) (stepByte_shape b hg hs)
    simpa [run_cons, List.append_assoc] using this

theorem finish_shape {p : Parser} {obs : List Obs} (hg : Good p obs) (hs : Shape p obs) :
    Shape p.finish.1 (obs ++ obsOf p.finish.2) := by
  have hphase := hg.inv.2
  unfold finish
  split
  · simpa [Shape] using hs
  · simpa [Shape] using hs
  · rename_i room hp
    cases hh : p.head with
    | none => simp_all [PhaseOK]
    | some h =>
      simp only [Shape, hh] at hs
      obtain ⟨bytes, rfl⟩ := hs
      exact ⟨bytes, by simp [hp, tailObs]⟩
  · rename_i hnd hnf hnu
    cases hh : p.head with
    | none =>
      simp only [Shape, hh] at hs
      have : obs = [] := by
        rw [hs]
        cases hp : p.phase <;> simp_all [tailObs]
      subst this
      simp [Shape, fail, tailObs]
    | some h =>
      simp only [Shape, hh] at hs
      obtain ⟨bytes, rfl⟩ := hs
      refine ⟨bytes, ?_⟩
      have : tailObs p.phase = [] := by cases hp : p.phase <;> simp_all [tailObs]
      simp [fail, tailObs]

end Parser

theorem Reach.shape {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    (hr : Reach config method p obs) : Shape p obs := by
  induction hr with
  | start => simp [Shape, Parser.start, tailObs]
  | feed bytes hr' ih =>
    rw [(Parser.feed_eq_run _ bytes).1, (Parser.feed_eq_run _ bytes).2]
    exact Parser.run_shape _ hr'.good ih
  | finish hr' ih => exact Parser.finish_shape hr'.good ih

/--
**Shape.**  Every run is observed as nothing yet, as one error, or as the final head followed by
body bytes and then nothing more yet, the end, or one error.
-/
theorem reach_shape {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    (hr : Reach config method p obs) :
    obs = [] ∨ (∃ e, obs = [.error e]) ∨
    ∃ (h : Head) (bytes : List UInt8) (tail : List Obs), obs = .head h :: (bytes.map .byte ++ tail) ∧
      (tail = [] ∨ tail = [.done] ∨ ∃ e, tail = [.error e]) := by
  have hs := hr.shape
  unfold Shape at hs
  split at hs
  · rename_i hh
    rw [hs]
    unfold tailObs
    split
    · -- done with no head: excluded by the invariant
      have hph := hr.good.inv.2
      simp_all [PhaseOK]
    · exact .inr (.inl ⟨_, rfl⟩)
    · exact .inl rfl
  · rename_i h hh
    obtain ⟨bytes, hb⟩ := hs
    refine .inr (.inr ⟨h, bytes, tailObs p.phase, hb, ?_⟩)
    unfold tailObs
    split
    · exact .inr (.inl rfl)
    · exact .inr (.inr ⟨_, rfl⟩)
    · exact .inl rfl

/-! ## Body contents -/

/--
**Content-Length bodies are delivered as they are.**  If some head bytes leave a parser expecting a
`Content-Length` body of `body.size` bytes, then that head followed by `body`, cut into pieces in any
way, is observed as what the head alone is observed as, then the bytes of `body`, then the end.
-/
theorem roundtrip_length (config : Config) (method : Std.Http.Method) (head body : ByteArray)
    (pieces : List ByteArray) (hpieces : pieces.foldl (· ++ ·) .empty = head ++ body)
    (hhead : ((Parser.start config method).feed head).1.phase = .body (.fixed body.size))
    (hpos : 0 < body.size) :
    ((Parser.start config method).feedAll pieces).1.phase = .done ∧
    obsOf ((Parser.start config method).feedAll pieces).2 =
      obsOf ((Parser.start config method).feed head).2 ++ body.data.toList.map .byte ++ [.done] := by
  have hall := Parser.feedAll_eq (Parser.start config method) pieces
  rw [hpieces] at hall
  have hs := Parser.feed_append (Parser.start config method) head body
  obtain ⟨r, hr⟩ : ∃ r, body.size = r + 1 := ⟨body.size - 1, by omega⟩
  rw [hr] at hhead
  have hb := Parser.feed_eq_run ((Parser.start config method).feed head).1 body
  have hlen : body.data.toList.length = r + 1 := by simp [hr]
  have hf := Parser.run_fixed _ r body.data.toList hhead (by omega)
  rw [hlen] at hf
  simp only [ite_true] at hf
  refine ⟨by rw [hall.1, hs.1, hb.1, hf.1], ?_⟩
  rw [hall.2, hs.2, hb.2, hf.2, List.append_assoc]

/--
**Bodies delimited by the end of input are delivered as they are.**  If some head bytes leave a
parser reading a body delimited by the end of input, with room for `body`, then that head followed by
`body`, cut into pieces in any way, and then the end of input, is observed as what the head alone is
observed as, then the bytes of `body`, then the end.
-/
theorem roundtrip_untilClose (config : Config) (method : Std.Http.Method) (head body : ByteArray)
    (pieces : List ByteArray) (hpieces : pieces.foldl (· ++ ·) .empty = head ++ body) (room : Nat)
    (hhead : ((Parser.start config method).feed head).1.phase = .body (.untilClose room))
    (hroom : body.size ≤ room) :
    ((Parser.start config method).feedAll pieces).1.finish.1.phase = .done ∧
    obsOf ((Parser.start config method).feedAll pieces).2 ++
        obsOf ((Parser.start config method).feedAll pieces).1.finish.2 =
      obsOf ((Parser.start config method).feed head).2 ++ body.data.toList.map .byte ++ [.done] := by
  have hall := Parser.feedAll_eq (Parser.start config method) pieces
  rw [hpieces] at hall
  have hs := Parser.feed_append (Parser.start config method) head body
  have hb := Parser.feed_eq_run ((Parser.start config method).feed head).1 body
  -- The state after the body.
  have hafter : ∃ q, ((Parser.start config method).feed (head ++ body)).1 = q ∧
      (∃ room', q.phase = .body (.untilClose room')) ∧
      obsOf ((Parser.start config method).feed (head ++ body)).2 =
        obsOf ((Parser.start config method).feed head).2 ++ body.data.toList.map .byte := by
    rcases hroomc : room with _ | r
    · have : body.size = 0 := by omega
      have hnil : body.data.toList = [] := List.length_eq_zero_iff.mp (by simpa using this)
      refine ⟨_, rfl, ⟨0, ?_⟩, ?_⟩
      · rw [hs.1, hb.1, hnil]; simpa [hroomc] using hhead
      · rw [hs.2, hb.2, hnil]; simp
    · rw [hroomc] at hhead
      have hf := Parser.run_untilClose _ r body.data.toList hhead (by simp; omega)
      refine ⟨_, rfl, ⟨r + 1 - body.data.toList.length, ?_⟩, ?_⟩
      · rw [hs.1, hb.1, hf.1]
      · rw [hs.2, hb.2, hf.2]
  obtain ⟨q, hq, ⟨room', hphase⟩, hobs⟩ := hafter
  rw [hall.1, hq]
  rw [hall.2, hobs]
  unfold Parser.finish
  simp [hphase, List.append_assoc]

end LeanHttp.Codec
