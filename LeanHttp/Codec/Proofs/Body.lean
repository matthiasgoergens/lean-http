module

public import LeanHttp.Codec.Proofs.Feed

@[expose] public section

/-!
# What the parser delivers

Properties of every run of the parser, from `Parser.start` through any sequence of `feed` and
`finish` (`Reach`), stated about what a client observes (`Obs`):

- the body delivered never exceeds a declared `Content-Length`, and equals it once the response is
  reported complete (`reach_length_le`, `reach_length_done`), and the `Content-Length` is the one
  field the head carries for it (`reach_length_declared`);
- a response to HEAD, and a 204 or 304 response, delivers no body bytes (`reach_head_request`,
  `reach_noBody_status`);
- no body exceeds `Config.maxBody` (`reach_body_le_max`), and body bytes come only once the final
  head arrived (`reach_body_after_head`);
- the final head is never an interim (1xx) response, and at most `Config.maxInterim` interim
  responses preceded it (`reach_final_head`).

They rest on an invariant of the parser's state (`Inv`), and on a relation between the state and the
observations so far (`Good`), both preserved by every byte (`stepByte_good`) and by the end of the
input (`finish_good`).  Nothing here looks inside the line automata: of the head reader, only the
facts in `HeadOK` are used.
-/

namespace LeanHttp.Codec


/--
The body bytes among some observations.
-/
def bodyBytes (obs : List Obs) : List UInt8 :=
  obs.filterMap fun | .byte b => some b | _ => none

@[simp] theorem bodyBytes_nil : bodyBytes [] = [] := rfl

@[simp] theorem bodyBytes_append (a b : List Obs) : bodyBytes (a ++ b) = bodyBytes a ++ bodyBytes b := by
  simp [bodyBytes]

@[simp] theorem bodyBytes_cons_byte (b : UInt8) (obs : List Obs) :
    bodyBytes (.byte b :: obs) = b :: bodyBytes obs := rfl

@[simp] theorem bodyBytes_cons_head (h : Head) (obs : List Obs) :
    bodyBytes (.head h :: obs) = bodyBytes obs := rfl

@[simp] theorem bodyBytes_cons_done (obs : List Obs) : bodyBytes (.done :: obs) = bodyBytes obs := rfl

@[simp] theorem bodyBytes_cons_error (e : Error) (obs : List Obs) :
    bodyBytes (.error e :: obs) = bodyBytes obs := rfl

@[simp] theorem bodyBytes_map_byte (xs : List UInt8) : bodyBytes (xs.map .byte) = xs := by
  induction xs <;> simp_all

/-! ## What the head reader guarantees -/

/--
What every final head reported for a request (HEAD or not, by `isHead`) satisfies: its framing is the
one its fields, status and the method give, and it is not an interim response.
-/
structure HeadOK (isHead : Bool) (h : Head) : Prop where
  /-- The framing is computed from the head. -/
  framing : framingOf isHead h.code h.http10 h.fields = some h.framing
  /-- The final head is not 1xx. -/
  notInterim : ¬ (100 ≤ h.code ∧ h.code < 200)
  /-- The connection may stay open only if the final head's own version and fields allow it. -/
  keepAlive : h.keepAlive = true → keepAliveOf h.http10 h.fields = true
  /-- The head in `Std.Http`'s types is the conversion of the head's parts. -/
  response : toResponseHead? h.code h.http10 h.reason h.fields = some h.response

theorem endOfHead_final {cfg : Config} {isHead : Bool} {hs : HeadState} {sl : StatusLine}
    {fields : List Field} {h : Head} (he : endOfHead cfg isHead hs sl fields = .final h) :
    HeadOK isHead h := by
  unfold endOfHead at he
  dsimp only at he
  split at he
  · cases he
  · rename_i framing hf
    split at he
    · split at he
      · cases he
      · split at he <;> cases he
    · rename_i hc
      split at he
      · cases he
      · rename_i response hresp
        cases he
        refine ⟨hf, by simpa using hc, ?_, hresp⟩
        intro hk
        simp only [Bool.and_eq_true] at hk
        exact hk.2

/--
Every final head the head reader reports satisfies `HeadOK`.
-/
theorem stepHead_final {cfg : Config} {isHead : Bool} {hs : HeadState} {b : UInt8} {h : Head}
    (he : stepHead cfg isHead hs b = .final h) : HeadOK isHead h := by
  unfold stepHead at he
  split at he
  · split at he
    · cases he
    · cases he
    · split at he
      · cases he
      · split at he <;> cases he
  · split at he
    · cases he
    · cases he
    · split at he
      · cases he
      · split at he <;> cases he
    · exact endOfHead_final he

/-! ## What framing fields mean -/

theorem framingOf_isHead {code : Nat} {http10 : Bool} {fields : List Field} {fr : Framing}
    (hf : framingOf true code http10 fields = some fr) : fr = .none := by
  unfold framingOf at hf
  split at hf <;> simp_all

theorem framingOf_noBody {isHead : Bool} {code : Nat} {http10 : Bool} {fields : List Field}
    {fr : Framing} (hc : code = 204 ∨ code = 304) (hf : framingOf isHead code http10 fields = some fr) :
    fr = .none := by
  have hn : noBodyStatus code = true := by rcases hc with hc | hc <;> simp [noBodyStatus, hc]
  unfold framingOf at hf
  split at hf <;> simp_all

theorem framingOf_length {isHead : Bool} {code : Nat} {http10 : Bool} {fields : List Field} {n : Nat}
    (hf : framingOf isHead code http10 fields = some (.length n)) :
    isHead = false ∧ noBodyStatus code = false ∧ declared http10 fields = .length n := by
  unfold framingOf at hf
  split at hf
  · simp at hf
  all_goals
    rename_i hd
    by_cases hb : (isHead || noBodyStatus code) = true
    · simp [hb] at hf
    · simp only [hb, Bool.false_eq_true, ite_false, Option.some.injEq] at hf
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hb
      first
        | (cases hf; exact ⟨hb.1, hb.2, hd⟩)
        | (cases hf)

theorem declared_length {http10 : Bool} {fields : List Field} {n : Nat}
    (hd : declared http10 fields = .length n) :
    fields.filter (·.isNamed transferEncodingName) = [] ∧
    ∃ cl, fields.filter (·.isNamed contentLengthName) = [cl] ∧ parseDecimal cl.value = some n := by
  unfold declared at hd
  dsimp only at hd
  split at hd
  · cases hd
  · rename_i hte hcl
    split at hd
    · rename_i m hm
      cases hd
      exact ⟨hte, _, hcl, hm⟩
    · cases hd
  · split at hd <;> cases hd
  · cases hd

/-! ## The invariant -/

/--
How an ended body relates to its framing: none for no body, and the whole `Content-Length` if it
ended complete (at most that, if it failed).
-/
def Ended (framing : Framing) (delivered : Nat) (complete : Bool) : Prop :=
  match framing with
  | .none => delivered = 0
  | .length n => if complete then delivered = n else delivered ≤ n
  | _ => True

/--
How the phase relates to the final head and the body delivered so far.
-/
def PhaseOK (maxBody : Nat) : Option Head → Phase → Nat → Prop
  | none, .head _, d => d = 0
  | none, .failed _, d => d = 0
  | none, _, _ => False
  | some _, .head _, _ => False
  | some h, .body (.fixed r), d => 0 < r ∧ h.framing = .length (d + r) ∧ d + r ≤ maxBody
  | some h, .body (.chunked c), d =>
    h.framing = .chunked ∧ d ≤ maxBody ∧ ∀ r, c = .data r → 0 < r ∧ d + r ≤ maxBody
  | some h, .body (.untilClose room), d => h.framing = .untilClose ∧ d + room = maxBody
  | some h, .done, d => d ≤ maxBody ∧ Ended h.framing d true
  | some h, .failed _, d => d ≤ maxBody ∧ Ended h.framing d false

/--
The invariant of the parser's state: the final head satisfies `HeadOK`, and the phase agrees with it
and with the body delivered (`PhaseOK`).
-/
def Inv (p : Parser) : Prop :=
  (∀ h, p.head = some h → HeadOK p.isHead h) ∧ PhaseOK p.config.maxBody p.head p.phase p.delivered

theorem PhaseOK.le {maxBody : Nat} {head : Option Head} {phase : Phase} {d : Nat}
    (h : PhaseOK maxBody head phase d) : d ≤ maxBody := by
  unfold PhaseOK at h
  split at h <;> first | omega | exact h.2.1 | exact h.1 | (obtain ⟨_, _, h⟩ := h; omega) | simp_all

/--
The state and the observations so far agree: the invariant holds, the body observed is the body
delivered, and the head, end and error observed are those of the state.
-/
structure Good (p : Parser) (obs : List Obs) : Prop where
  /-- The invariant. -/
  inv : Inv p
  /-- The body observed, counted. -/
  body : (bodyBytes obs).length = p.delivered
  /-- The head observed. -/
  head : ∀ h, Obs.head h ∈ obs ↔ p.head = some h
  /-- The end observed. -/
  done : Obs.done ∈ obs ↔ p.phase = .done
  /-- The error observed. -/
  error : ∀ e, Obs.error e ∈ obs ↔ p.phase = .failed e

/-! ## Chunked decoding, from the outside -/

theorem stepChunk_more_data {cfg : Config} {room : Nat} {c : ChunkState} {b : UInt8} {r : Nat}
    (hs : stepChunk cfg room c b = .more (.data r)) : 0 < r ∧ r ≤ room := by
  unfold stepChunk at hs
  split at hs
  · split at hs
    · cases hs
    · cases hs
    · cases hs
    · split at hs
      · cases hs; omega
      · cases hs
  · cases hs
  · split at hs <;> cases hs
  · split at hs <;> cases hs
  · split at hs
    · cases hs
    · cases hs
    · cases hs
    · split at hs
      · cases hs
      · split at hs <;> cases hs

theorem stepChunk_data {cfg : Config} {room : Nat} {c c' : ChunkState} {b : UInt8}
    (hs : stepChunk cfg room c b = .data c') :
    ∃ r, c = .data r ∧ c' = if r ≤ 1 then .dataCR else .data (r - 1) := by
  unfold stepChunk at hs
  split at hs
  · split at hs <;> (try split at hs) <;> cases hs
  · cases hs; exact ⟨_, rfl, rfl⟩
  · split at hs <;> cases hs
  · split at hs <;> cases hs
  · split at hs <;> (try split at hs) <;> (try split at hs) <;> cases hs

/-! ## One byte -/

namespace Parser

@[simp] theorem stepByte_config (p : Parser) (b : UInt8) : (p.stepByte b).1.config = p.config := by
  unfold stepByte
  split
  · split <;> simp [fail, startBody] <;> split <;> (try split) <;> simp
  all_goals (try split) <;> (try split) <;> simp [fail]

@[simp] theorem stepByte_isHead (p : Parser) (b : UInt8) : (p.stepByte b).1.isHead = p.isHead := by
  unfold stepByte
  split
  · split <;> simp [fail, startBody] <;> split <;> (try split) <;> simp
  all_goals (try split) <;> (try split) <;> simp [fail]

theorem startBody_good {p : Parser} {obs : List Obs} {h : Head} (hg : Good p obs)
    (hp : ∃ hs, p.phase = .head hs) (hh : HeadOK p.isHead h) :
    Good (p.startBody h).1 (obs ++ obsOf (p.startBody h).2) := by
  obtain ⟨⟨_, hphase⟩, hbody, hheads, hdone, herr⟩ := hg
  obtain ⟨hs, hp⟩ := hp
  have hnone : p.head = none := by
    cases hph : p.head <;> simp_all [PhaseOK]
  have hd0 : p.delivered = 0 := by simpa [hnone, hp, PhaseOK] using hphase
  have hnodone : Obs.done ∉ obs := by simp [hdone, hp]
  have hnoerr : ∀ e, Obs.error e ∉ obs := by simp [herr, hp]
  have hnohead : ∀ h', Obs.head h' ∉ obs := by simp [hheads, hnone]
  unfold startBody
  dsimp only
  split
  · refine ⟨⟨by simp [hh], ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK, Ended] <;> grind
  · refine ⟨⟨by simp [hh], ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK, Ended] <;> grind
  · rename_i n hfr
    split
    · refine ⟨⟨by simp [hh], ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK, Ended] <;> grind
    · refine ⟨⟨by simp [hh], ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK] <;> grind
  · refine ⟨⟨by simp [hh], ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK] <;> grind
  · refine ⟨⟨by simp [hh], ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK] <;> grind

/--
Every byte keeps the state and the observations in agreement.
-/
theorem stepByte_good {p : Parser} {obs : List Obs} (b : UInt8) (hg : Good p obs) :
    Good (p.stepByte b).1 (obs ++ obsOf (p.stepByte b).2) := by
  have hle := hg.inv.2.le
  obtain ⟨⟨hhead, hphase⟩, hbody, hheads, hdone, herr⟩ := hg
  unfold stepByte
  split
  · -- reading heads
    rename_i hs hp
    have hnone : p.head = none := by cases hph : p.head <;> simp_all [PhaseOK]
    have hd0 : p.delivered = 0 := by simpa [hnone, hp, PhaseOK] using hphase
    split
    · refine ⟨⟨by simp [hnone], ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK]
    · refine ⟨⟨by simp [fail, hnone], ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [fail, PhaseOK] <;> grind
    · rename_i h hf
      exact startBody_good ⟨⟨hhead, hphase⟩, hbody, hheads, hdone, herr⟩ ⟨hs, hp⟩ (stepHead_final hf)
  · -- a Content-Length body
    rename_i r hp
    cases hh : p.head with
    | none => simp [hh, hp, PhaseOK] at hphase
    | some h =>
      simp only [hh, hp, PhaseOK] at hphase
      obtain ⟨hr, hfr, hmax⟩ := hphase
      split
      · have : r = 1 := by omega
        subst this
        refine ⟨⟨by simpa [hh] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp_all [PhaseOK, Ended] <;> grind
      · refine ⟨⟨by simpa [hh] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp_all [PhaseOK] <;> grind
  · -- a body delimited by the end of input
    rename_i room hp
    cases hh : p.head with
    | none => simp [hh, hp, PhaseOK] at hphase
    | some h =>
      simp only [hh, hp, PhaseOK] at hphase
      obtain ⟨hfr, hroom⟩ := hphase
      split
      · refine ⟨⟨by simpa [fail, hh] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp_all [fail, PhaseOK, Ended] <;> grind
      · refine ⟨⟨by simpa [hh] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp_all [PhaseOK] <;> grind
  · -- a chunked body
    rename_i c hp
    cases hh : p.head with
    | none => simp [hh, hp, PhaseOK] at hphase
    | some h =>
      simp only [hh, hp, PhaseOK] at hphase
      obtain ⟨hfr, hmax, hdata⟩ := hphase
      split
      · rename_i c' hs
        refine ⟨⟨by simpa [hh] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK]
        intro r hr
        subst hr
        have := stepChunk_more_data hs
        omega
      · rename_i c' hs
        obtain ⟨r, hc, hc'⟩ := stepChunk_data hs
        obtain ⟨hr, hrmax⟩ := hdata r hc
        refine ⟨⟨by simpa [hh] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK]
        · refine ⟨by omega, ?_⟩
          intro r' hr'
          split at hr'
          · cases hr'
          · cases hr'; omega
        all_goals grind
      · refine ⟨⟨by simpa [hh] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all [PhaseOK, Ended] <;>
          grind
      · refine ⟨⟨by simpa [fail, hh] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp_all [fail, PhaseOK, Ended] <;> grind
  · -- after the end
    rename_i hp
    refine ⟨⟨by simpa using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all
  · -- after an error
    exact ⟨⟨hhead, hphase⟩, by simpa using hbody, by simpa using hheads, by simpa using hdone,
      by simpa using herr⟩

/--
Reading bytes one at a time keeps the state and the observations in agreement.
-/
theorem run_good {p : Parser} {obs : List Obs} (xs : List UInt8) (hg : Good p obs) :
    Good (p.run xs).1 (obs ++ obsOf (p.run xs).2) := by
  induction xs generalizing p obs with
  | nil => simpa using hg
  | cons b bs ih =>
    have := ih (stepByte_good b hg)
    simpa [run_cons, List.append_assoc] using this

/--
Feeding bytes keeps the state and the observations in agreement.
-/
theorem feed_good {p : Parser} {obs : List Obs} (bytes : ByteArray) (hg : Good p obs) :
    Good (p.feed bytes).1 (obs ++ obsOf (p.feed bytes).2) := by
  have h := feed_eq_run p bytes
  rw [h.1, h.2]
  exact run_good _ hg

/--
The end of input keeps the state and the observations in agreement.
-/
theorem finish_good {p : Parser} {obs : List Obs} (hg : Good p obs) :
    Good p.finish.1 (obs ++ obsOf p.finish.2) := by
  have hle := hg.inv.2.le
  obtain ⟨⟨hhead, hphase⟩, hbody, hheads, hdone, herr⟩ := hg
  unfold finish
  split
  · refine ⟨⟨by simpa using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all
  · refine ⟨⟨by simpa using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp_all
  · rename_i room hp
    cases hh : p.head with
    | none => simp [hh, hp, PhaseOK] at hphase
    | some h =>
      simp only [hh, hp, PhaseOK] at hphase
      refine ⟨⟨by simpa [hh] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [PhaseOK, Ended] <;> grind
  · rename_i hnd hnf hnu
    refine ⟨⟨by simpa [fail] using hhead, ?_⟩, ?_, ?_, ?_, ?_⟩
    · cases hh : p.head with
      | none =>
        simp only [hh] at hphase
        simp only [fail, PhaseOK]
        unfold PhaseOK at hphase
        split at hphase <;> simp_all
      | some h =>
        simp only [hh] at hphase
        simp only [fail, PhaseOK]
        refine ⟨hle, ?_⟩
        unfold PhaseOK at hphase
        split at hphase <;> simp_all [Ended] <;> grind
    all_goals simp_all [fail] <;> grind

end Parser

/-! ## Runs -/

/--
`Reach config method p obs`: some run of a parser for a request with `method` reaches `p`, having
emitted events whose observations are `obs`.  A run is `Parser.start`, then any sequence of `feed`
and `finish`.
-/
inductive Reach (config : Config) (method : Std.Http.Method) : Parser → List Obs → Prop where
  /-- The start. -/
  | start : Reach config method (Parser.start config method) []
  /-- Feeding bytes. -/
  | feed {p : Parser} {obs : List Obs} (bytes : ByteArray) :
      Reach config method p obs → Reach config method (p.feed bytes).1 (obs ++ obsOf (p.feed bytes).2)
  /-- The end of input. -/
  | finish {p : Parser} {obs : List Obs} :
      Reach config method p obs → Reach config method p.finish.1 (obs ++ obsOf p.finish.2)

theorem start_good (config : Config) (method : Std.Http.Method) :
    Good (Parser.start config method) [] :=
  ⟨⟨by simp [Parser.start], by simp [Parser.start, PhaseOK]⟩, by simp [Parser.start],
    by simp [Parser.start], by simp [Parser.start], by simp [Parser.start]⟩

theorem Reach.good {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    (hr : Reach config method p obs) : Good p obs := by
  induction hr with
  | start => exact start_good config method
  | feed bytes _ ih => exact Parser.feed_good bytes ih
  | finish _ ih => exact Parser.finish_good ih

theorem feed_isHead (p : Parser) (bytes : ByteArray) : (p.feed bytes).1.isHead = p.isHead := by
  rw [(Parser.feed_eq_run p bytes).1]
  induction bytes.data.toList generalizing p with
  | nil => rfl
  | cons b bs ih => simp [Parser.run_cons, ih]

theorem feed_config (p : Parser) (bytes : ByteArray) : (p.feed bytes).1.config = p.config := by
  rw [(Parser.feed_eq_run p bytes).1]
  induction bytes.data.toList generalizing p with
  | nil => rfl
  | cons b bs ih => simp [Parser.run_cons, ih]

theorem Reach.isHead {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    (hr : Reach config method p obs) : p.isHead = Parser.isHeadMethod method := by
  induction hr with
  | start => rfl
  | feed bytes _ ih => rw [feed_isHead, ih]
  | finish _ ih =>
    unfold Parser.finish
    split <;> simp_all [Parser.fail]

theorem Reach.config {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    (hr : Reach config method p obs) : p.config = config := by
  induction hr with
  | start => rfl
  | feed bytes _ ih => rw [feed_config, ih]
  | finish _ ih =>
    unfold Parser.finish
    split <;> simp_all [Parser.fail]

/-! ## The body -/

/--
**Content-Length, an upper bound.**  Once a final head with `Content-Length: n` framing is observed,
no more than `n` body bytes are ever delivered.
-/
theorem reach_length_le {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    {h : Head} {n : Nat} (hr : Reach config method p obs) (hh : Obs.head h ∈ obs)
    (hn : h.framing = .length n) : (bodyBytes obs).length ≤ n := by
  have hg := hr.good
  have hph := hg.inv.2
  rw [(hg.head h).1 hh] at hph
  rw [hg.body]
  unfold PhaseOK at hph
  split at hph <;> simp_all [Ended] <;> grind

/--
**Content-Length, complete.**  A response with `Content-Length: n` framing that is reported complete
delivered exactly `n` body bytes.
-/
theorem reach_length_done {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    {h : Head} {n : Nat} (hr : Reach config method p obs) (hh : Obs.head h ∈ obs)
    (hn : h.framing = .length n) (hd : Obs.done ∈ obs) : (bodyBytes obs).length = n := by
  have hg := hr.good
  have hph := hg.inv.2
  rw [(hg.head h).1 hh, hg.done.1 hd] at hph
  rw [hg.body]
  simp_all [PhaseOK, Ended]

/--
**Content-Length, declared.**  A final head with `Content-Length: n` framing has exactly one
`Content-Length` field, whose value reads as `n`, and no `Transfer-Encoding` field; and it answers a
request other than HEAD, with a status other than 1xx, 204 and 304.
-/
theorem reach_length_declared {config : Config} {method : Std.Http.Method} {p : Parser}
    {obs : List Obs} {h : Head} {n : Nat} (hr : Reach config method p obs) (hh : Obs.head h ∈ obs)
    (hn : h.framing = .length n) :
    method ≠ .head ∧ noBodyStatus h.code = false ∧
    h.fields.filter (·.isNamed transferEncodingName) = [] ∧
    ∃ cl, h.fields.filter (·.isNamed contentLengthName) = [cl] ∧ parseDecimal cl.value = some n := by
  have hg := hr.good
  have hok := hg.inv.1 h ((hg.head h).1 hh)
  have hf := hok.framing
  rw [hn] at hf
  obtain ⟨hi, hs, hd⟩ := framingOf_length hf
  rw [hr.isHead] at hi
  refine ⟨?_, hs, declared_length hd⟩
  intro hm
  subst hm
  simp [Parser.isHeadMethod] at hi

/--
**HEAD.**  A response to a HEAD request delivers no body bytes, whatever its framing fields say.
-/
theorem reach_head_request {config : Config} {p : Parser} {obs : List Obs}
    (hr : Reach config .head p obs) : bodyBytes obs = [] := by
  have hg := hr.good
  have hph := hg.inv.2
  rw [← List.length_eq_zero_iff, hg.body]
  cases hh : p.head with
  | none =>
    rw [hh] at hph
    unfold PhaseOK at hph
    split at hph <;> simp_all
  | some h =>
    have hok := hg.inv.1 h hh
    have hi : p.isHead = true := by rw [hr.isHead]; rfl
    have hfr := framingOf_isHead (hi ▸ hok.framing)
    rw [hh] at hph
    unfold PhaseOK at hph
    split at hph <;> simp_all [Ended]

/--
**204 and 304.**  A 204 or 304 response delivers no body bytes, whatever its framing fields say.
-/
theorem reach_noBody_status {config : Config} {method : Std.Http.Method} {p : Parser}
    {obs : List Obs} {h : Head} (hr : Reach config method p obs) (hh : Obs.head h ∈ obs)
    (hc : h.code = 204 ∨ h.code = 304) : bodyBytes obs = [] := by
  have hg := hr.good
  have hph := hg.inv.2
  have hsome := (hg.head h).1 hh
  have hfr := framingOf_noBody hc (hg.inv.1 h hsome).framing
  rw [← List.length_eq_zero_iff, hg.body]
  rw [hsome] at hph
  unfold PhaseOK at hph
  split at hph <;> simp_all [Ended]

/--
**The body limit.**  No run delivers more than `Config.maxBody` body bytes.
-/
theorem reach_body_le_max {config : Config} {method : Std.Http.Method} {p : Parser}
    {obs : List Obs} (hr : Reach config method p obs) : (bodyBytes obs).length ≤ config.maxBody := by
  have hg := hr.good
  rw [hg.body, ← hr.config]
  exact hg.inv.2.le

/--
**Body after head.**  Body bytes are observed only once the final head has been.
-/
theorem reach_body_after_head {config : Config} {method : Std.Http.Method} {p : Parser}
    {obs : List Obs} (hr : Reach config method p obs) (hb : bodyBytes obs ≠ []) :
    ∃ h, Obs.head h ∈ obs := by
  have hg := hr.good
  cases hh : p.head with
  | none =>
    have hph := hg.inv.2
    rw [hh] at hph
    have : (bodyBytes obs).length = 0 := by
      rw [hg.body]
      unfold PhaseOK at hph
      split at hph <;> simp_all
    simp_all
  | some h => exact ⟨h, (hg.head h).2 hh⟩

/-! ## Interim responses and status codes -/

theorem endOfHead_more {cfg : Config} {isHead : Bool} {hs hs' : HeadState} {sl : StatusLine}
    {fields : List Field} (he : endOfHead cfg isHead hs sl fields = .more hs') :
    hs'.interim ≤ cfg.maxInterim ∧ hs'.part = .status {} := by
  unfold endOfHead at he
  dsimp only at he
  split at he
  · cases he
  · split at he
    · split at he
      · cases he
      · split at he
        · cases he
        · rename_i hlt
          cases he
          simp only at hlt ⊢
          exact ⟨by omega, trivial⟩
    · split at he <;> cases he

theorem endOfHead_final_fields {cfg : Config} {isHead : Bool} {hs : HeadState} {sl : StatusLine}
    {fields : List Field} {h : Head} (he : endOfHead cfg isHead hs sl fields = .final h) :
    h.interim = hs.interim ∧ h.code = sl.code := by
  unfold endOfHead at he
  dsimp only at he
  split at he
  · cases he
  · split at he
    · split at he
      · cases he
      · split at he <;> cases he
    · split at he
      · cases he
      · cases he; exact ⟨rfl, rfl⟩

/--
What the head reader keeps true while it reads heads: interim responses within the limit, and a
status code of at least 100 once the status line has been read.
-/
def HeadStateOK (cfg : Config) (hs : HeadState) : Prop :=
  hs.interim ≤ cfg.maxInterim ∧
    ∀ sl fl fields count bytes, hs.part = .fields sl fl fields count bytes → 100 ≤ sl.code

theorem stepHead_more_ok {cfg : Config} {isHead : Bool} {hs hs' : HeadState} {b : UInt8}
    (he : stepHead cfg isHead hs b = .more hs') (hi : HeadStateOK cfg hs) : HeadStateOK cfg hs' := by
  obtain ⟨hint, hcode⟩ := hi
  unfold stepHead at he
  split at he
  · rename_i sl hp
    split at he
    · cases he; exact ⟨hint, by simp⟩
    · cases he
    · rename_i sl' _
      split at he
      · cases he
      · rename_i hge
        split at he
        · cases he
          refine ⟨hint, ?_⟩
          intro sl'' fl fields count bytes hpart
          simp only [HeadPart.fields.injEq] at hpart
          rw [← hpart.1]
          omega
        · cases he
  · rename_i sl fl fields count bytes hp
    have hsl := hcode sl fl fields count bytes hp
    split at he
    · cases he
      exact ⟨hint, by intro _ _ _ _ _ h; simp only [HeadPart.fields.injEq] at h; rw [← h.1]; exact hsl⟩
    · cases he
    · split at he
      · cases he
      · split at he
        · cases he
        · cases he
          exact ⟨hint, by intro _ _ _ _ _ h; simp only [HeadPart.fields.injEq] at h; rw [← h.1]; exact hsl⟩
    · obtain ⟨h1, h2⟩ := endOfHead_more he
      exact ⟨h1, by intro _ _ _ _ _ h; rw [h2] at h; cases h⟩

theorem stepHead_final_ok {cfg : Config} {isHead : Bool} {hs : HeadState} {b : UInt8} {h : Head}
    (he : stepHead cfg isHead hs b = .final h) (hi : HeadStateOK cfg hs) :
    h.interim ≤ cfg.maxInterim ∧ 200 ≤ h.code := by
  have hok := stepHead_final he
  obtain ⟨hint, hcode⟩ := hi
  unfold stepHead at he
  split at he
  · split at he
    · cases he
    · cases he
    · split at he
      · cases he
      · split at he <;> cases he
  · rename_i sl fl fields count bytes hp
    have hsl := hcode sl fl fields count bytes hp
    split at he
    · cases he
    · cases he
    · split at he
      · cases he
      · split at he <;> cases he
    · obtain ⟨h1, h2⟩ := endOfHead_final_fields he
      have := hok.notInterim
      refine ⟨by omega, by omega⟩

/--
Interim responses within the limit and status codes in range: while heads are read, and in the final
head.
-/
def InterimOK (p : Parser) : Prop :=
  (∀ hs, p.phase = .head hs → HeadStateOK p.config hs) ∧
  (∀ h, p.head = some h → h.interim ≤ p.config.maxInterim ∧ 200 ≤ h.code)

namespace Parser

theorem stepByte_interimOK (p : Parser) (b : UInt8) (hint : InterimOK p) :
    InterimOK (p.stepByte b).1 := by
  obtain ⟨hph, hhd⟩ := hint
  unfold stepByte
  split
  · rename_i hs hp
    split
    · rename_i hs' he
      exact ⟨by simpa using stepHead_more_ok he (hph hs hp), by simpa using hhd⟩
    · exact ⟨by simp [fail], by simpa [fail] using hhd⟩
    · rename_i h he
      have := stepHead_final_ok he (hph hs hp)
      have hhead : (p.startBody h).1.head = some h := by
        unfold startBody; dsimp only; split <;> (try split) <;> rfl
      have hcfg : (p.startBody h).1.config = p.config := by
        unfold startBody; dsimp only; split <;> (try split) <;> rfl
      refine ⟨?_, ?_⟩
      · unfold startBody; dsimp only; split <;> (try split) <;> simp
      · intro h' hh'
        rw [hhead] at hh'
        cases hh'
        rw [hcfg]
        exact this
  all_goals
    first
      | exact ⟨by simp_all, by simpa using hhd⟩
      | (split <;> (try split) <;> exact ⟨by simp_all [fail], by simpa [fail] using hhd⟩)

theorem run_interimOK (p : Parser) (xs : List UInt8) (hi : InterimOK p) : InterimOK (p.run xs).1 := by
  induction xs generalizing p with
  | nil => exact hi
  | cons b bs ih => exact ih _ (stepByte_interimOK p b hi)

theorem finish_interimOK (p : Parser) (hi : InterimOK p) : InterimOK p.finish.1 := by
  obtain ⟨hph, hhd⟩ := hi
  unfold finish
  split <;> exact ⟨by simp_all [fail], by simpa [fail] using hhd⟩

end Parser

theorem Reach.interimOK {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    (hr : Reach config method p obs) : InterimOK p := by
  induction hr with
  | start =>
    exact ⟨by simp [Parser.start, HeadStateOK], by simp [Parser.start]⟩
  | feed bytes _ ih =>
    rw [(Parser.feed_eq_run _ bytes).1]
    exact Parser.run_interimOK _ _ ih
  | finish _ ih => exact Parser.finish_interimOK _ ih

/--
**Interim responses.**  The final head observed is never an interim (1xx) response: its status is
at least 200, and at most `Config.maxInterim` interim responses preceded it.
-/
theorem reach_final_head {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    {h : Head} (hr : Reach config method p obs) (hh : Obs.head h ∈ obs) :
    200 ≤ h.code ∧ h.interim ≤ config.maxInterim := by
  have hg := hr.good
  have hsome := (hg.head h).1 hh
  have := hr.interimOK.2 h hsome
  rw [hr.config] at this
  exact ⟨this.2, this.1⟩

/-! ## Keep-alive -/

/-- One step of `connectionTokens`. -/
def connStep (acc : Option (List (List UInt8))) (f : Field) : Option (List (List UInt8)) :=
  if f.isNamed connectionName then acc.bind fun tokens => (tokenList f.value).map (tokens ++ ·)
  else acc

theorem connectionTokens_eq (fields : List Field) :
    connectionTokens fields = fields.foldl connStep (some []) := rfl

theorem foldl_connStep_none (fields : List Field) : fields.foldl connStep none = none := by
  induction fields with
  | nil => rfl
  | cons f fs ih => simpa [connStep] using ih

theorem foldl_connStep_some (fields : List Field) (acc : List (List UInt8)) :
    fields.foldl connStep (some acc) = none ∨
    ∃ more, fields.foldl connStep (some acc) = some (acc ++ more) := by
  induction fields generalizing acc with
  | nil => exact .inr ⟨[], by simp⟩
  | cons f fs ih =>
    simp only [List.foldl_cons, connStep]
    split
    · cases ht : tokenList f.value with
      | none => left; simpa using foldl_connStep_none fs
      | some ts =>
        simp only [Option.bind_some, Option.map_some]
        rcases ih (acc ++ ts) with h | ⟨more, h⟩
        · exact .inl h
        · exact .inr ⟨ts ++ more, by simp [h]⟩
    · exact ih acc

theorem foldl_connStep_mem (fields : List Field) (acc ts : List (List UInt8)) (t : List UInt8)
    (h : fields.foldl connStep (some acc) = some ts) (ht : t ∈ ts) :
    t ∈ acc ∨ ∃ f ∈ fields, f.isNamed connectionName = true ∧
      ∃ vs, tokenList f.value = some vs ∧ t ∈ vs := by
  induction fields generalizing acc with
  | nil => simp at h; subst h; exact .inl ht
  | cons f fs ih =>
    simp only [List.foldl_cons, connStep] at h
    split at h
    · rename_i hn
      cases hv : tokenList f.value with
      | none => rw [hv] at h; simp [foldl_connStep_none] at h
      | some vs =>
        rw [hv] at h
        simp only [Option.bind_some, Option.map_some] at h
        rcases ih (acc ++ vs) h with h1 | ⟨g, hg, hgn, ws, hws, hw⟩
        · rcases List.mem_append.mp h1 with h2 | h2
          · exact .inl h2
          · exact .inr ⟨f, by simp, hn, vs, hv, h2⟩
        · exact .inr ⟨g, by simp [hg], hgn, ws, hws, hw⟩
    · rcases ih acc h with h1 | ⟨g, hg, hgn, ws, hws, hw⟩
      · exact .inl h1
      · exact .inr ⟨g, by simp [hg], hgn, ws, hws, hw⟩

/--
A `Connection` field listing `close` forbids keeping the connection open, whatever the version.
-/
theorem keepAliveOf_close {http10 : Bool} {fields : List Field} {f : Field} (hf : f ∈ fields)
    (hn : f.isNamed connectionName = true) {ts : List (List UInt8)} (ht : tokenList f.value = some ts)
    (hc : ascii "close" ∈ ts) : keepAliveOf http10 fields = false := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hf
  unfold keepAliveOf
  rw [connectionTokens_eq, List.foldl_append, List.foldl_cons]
  rcases foldl_connStep_some pre [] with h | ⟨a, h⟩
  · rw [h]; simp [connStep, hn, foldl_connStep_none]
  · rw [h]
    simp only [connStep, hn, ite_true, Option.bind_some, ht, Option.map_some]
    rcases foldl_connStep_some post ([] ++ a ++ ts) with h' | ⟨more, h'⟩
    · rw [h']
    · rw [h']
      simp [hc]

/--
A malformed `Connection` field forbids keeping the connection open.
-/
theorem keepAliveOf_malformed {http10 : Bool} {fields : List Field} {f : Field} (hf : f ∈ fields)
    (hn : f.isNamed connectionName = true) (ht : tokenList f.value = none) :
    keepAliveOf http10 fields = false := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hf
  unfold keepAliveOf
  rw [connectionTokens_eq, List.foldl_append, List.foldl_cons]
  rcases foldl_connStep_some pre [] with h | ⟨a, h⟩
  · rw [h]; simp [connStep, hn, foldl_connStep_none]
  · rw [h]; simp [connStep, hn, ht, foldl_connStep_none]

/--
An HTTP/1.0 response allows keeping the connection open only with a `Connection` field listing
`keep-alive`.
-/
theorem keepAliveOf_http10 {fields : List Field} (h : keepAliveOf true fields = true) :
    ∃ f ∈ fields, f.isNamed connectionName = true ∧
      ∃ ts, tokenList f.value = some ts ∧ ascii "keep-alive" ∈ ts := by
  unfold keepAliveOf at h
  split at h
  · cases h
  · rename_i ts hts
    simp only [Bool.and_eq_true, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
    replace h := h.2
    rw [connectionTokens_eq] at hts
    rcases foldl_connStep_mem fields [] ts _ hts h with h1 | h1
    · simp at h1
    · exact h1

/--
**Keep-alive.**  If the final head observed allows the connection to stay open, then its own version
and fields do: no `Connection` field lists `close` (`keepAliveOf_close`), none is malformed
(`keepAliveOf_malformed`), and in HTTP/1.0 one lists `keep-alive` (`keepAliveOf_http10`).
-/
theorem reach_keepAlive {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    {h : Head} (hr : Reach config method p obs) (hh : Obs.head h ∈ obs) (hk : h.keepAlive = true) :
    keepAliveOf h.http10 h.fields = true :=
  (hr.good.inv.1 h ((hr.good.head h).1 hh)).keepAlive hk

/--
**The `Std.Http` head.**  The final head observed carries, as `response`, the conversion of its
status code, version, reason phrase and fields to `Std.Http`'s types.
-/
theorem reach_response {config : Config} {method : Std.Http.Method} {p : Parser} {obs : List Obs}
    {h : Head} (hr : Reach config method p obs) (hh : Obs.head h ∈ obs) :
    toResponseHead? h.code h.http10 h.reason h.fields = some h.response :=
  (hr.good.inv.1 h ((hr.good.head h).1 hh)).response

end LeanHttp.Codec
