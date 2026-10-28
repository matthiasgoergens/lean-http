module

public import LeanHttp.Codec.Proofs.Body

@[expose] public section

/-!
# A complete response, framed with certainty

`Parser.completeCertain p` says that the response ended (`Phase.done`) and that its final head's
framing marks the end of the body in the bytes themselves (`Framing.certain`: no body, a
`Content-Length`, or chunked; not a body delimited by the end of input).  The exchange core may reuse
a connection only after such a response, read to its end with nothing after it.  The lemmas here are
what that verdict needs:

- **The end of input never completes a certain response** (`finish_completeCertain`): if a response
  is complete and certain after the end of input, it already was before.  So whether a response is
  complete and certain does not depend on whether, or when, the peer closed; the reuse verdict
  (`Parser.reusable`) further requires that the input has not ended.
- **A certain response that is not complete fails at the end of input** (`finish_certain_incomplete`),
  as a premature close.
- **Completion is final** (`feed_done`): once complete, more bytes cause no event and change nothing
  but `extra`, and so a reusable parser stays reusable only while no byte follows (`reusable_feed`).
- **Completion is decided by a prefix** (`completeCertain_prefix`): if the bytes `a` already complete
  a certain response, then `a ++ b` gives the same head, body and end for every `b`, with `b` only
  noted as extra bytes.
- **A complete certain body is whole** (`completeCertain_body`): it delivered the declared
  `Content-Length`, or nothing for a response without a body.
-/

namespace LeanHttp.Codec

namespace Parser

/--
**Completion is final.**  Feeding a complete parser emits nothing and changes nothing but `extra`,
which records whether any byte arrived.
-/
theorem feed_done (p : Parser) (bytes : ByteArray) (hp : p.phase = .done) :
    p.feed bytes = ({ p with extra := p.extra || decide (0 < bytes.size) }, #[]) := by
  unfold feed
  rw [feedLoop]
  split
  · rename_i h
    simp [hp, h]
  · rename_i h
    have : bytes.size = 0 := by omega
    cases p
    simp [this]

theorem completeCertain_iff (p : Parser) :
    p.completeCertain = true ↔ p.phase = .done ∧ ∃ h, p.head = some h ∧ h.framing.certain = true := by
  unfold completeCertain complete certain
  cases p.head <;> cases hp : p.phase <;> simp_all

/--
The response-side conditions for reusing the connection, spelled out.
-/
theorem reusable_iff (p : Parser) :
    p.reusable = true ↔ p.phase = .done ∧
      (∃ h, p.head = some h ∧ h.framing.certain = true ∧ h.keepAlive = true) ∧
      p.extra = false ∧ p.inputEnded = false := by
  unfold reusable completeCertain complete certain
  cases hh : p.head <;> cases hp : p.phase <;> simp_all <;> grind

/--
**The end of input never completes a certain response.**  Whether a certain response is complete
is the same before and after the end of input.
-/
theorem finish_completeCertain (p : Parser) (hinv : Inv p) :
    p.finish.1.completeCertain = p.completeCertain := by
  have hph := hinv.2
  unfold finish
  split
  · rename_i hp; simp [completeCertain, complete, certain, hp]
  · rename_i e hp; simp [completeCertain, complete, certain, hp]
  · rename_i room hp
    cases hh : p.head with
    | none => simp [hh, hp, PhaseOK] at hph
    | some h =>
      simp only [hh, hp, PhaseOK] at hph
      simp [completeCertain, complete, certain, hh, hp, hph.1, Framing.certain]
  · rename_i hnd _ _
    simp [fail, completeCertain, complete]

/--
**A certain response that is not complete fails at the end of input**, as a premature close.
-/
theorem finish_certain_incomplete (p : Parser) (hinv : Inv p) (hc : p.certain = true)
    (hnd : p.phase ≠ .done) (hnf : ∀ e, p.phase ≠ .failed e) :
    p.finish.1.phase = .failed .closed ∧ p.finish.2 = #[.error .closed] := by
  have hph := hinv.2
  unfold finish
  split
  · contradiction
  · rename_i e hp; exact absurd hp (hnf e)
  · rename_i room hp
    cases hh : p.head with
    | none => simp [hh, hp, PhaseOK] at hph
    | some h =>
      simp only [hh, hp, PhaseOK] at hph
      simp [certain, hh, hph.1, Framing.certain] at hc
  · simp [fail]

/--
**A reusable parser stays reusable only while no byte follows.**
-/
theorem reusable_feed (p : Parser) (bytes : ByteArray) (hr : p.reusable = true) :
    (p.feed bytes).1.reusable = true ↔ bytes.size = 0 := by
  have hp := ((reusable_iff p).1 hr)
  rw [feed_done p bytes hp.1]
  rw [reusable_iff]
  simp only [hp.1, hp.2.2.1, hp.2.2.2, Bool.false_or, decide_eq_false_iff_not, true_and, and_true]
  constructor
  · intro h; omega
  · intro h; exact ⟨hp.2.1, by omega⟩

/--
**A complete certain body is whole**: it delivered the declared `Content-Length`, or nothing for a
response without a body.
-/
theorem completeCertain_body (p : Parser) (hinv : Inv p) (hc : p.completeCertain = true)
    {h : Head} (hh : p.head = some h) :
    (∀ n, h.framing = .length n → p.delivered = n) ∧ (h.framing = .none → p.delivered = 0) := by
  have hph := hinv.2
  have hd := ((completeCertain_iff p).1 hc).1
  rw [hh, hd] at hph
  simp only [PhaseOK, Ended] at hph
  refine ⟨fun n hn => ?_, fun hn => ?_⟩ <;> simp_all

end Parser

/--
**Completion is decided by a prefix.**  If the bytes `a` complete a certain response, then for any
`b`, the bytes `a ++ b` give the same final state but for `extra`, and the same observations: `b`
belongs to whatever follows the response.
-/
theorem completeCertain_prefix (config : Config) (method : Std.Http.Method) (a b : ByteArray)
    (hc : ((Parser.start config method).feed a).1.completeCertain = true) :
    ((Parser.start config method).feed (a ++ b)).1 =
      { ((Parser.start config method).feed a).1 with
        extra := ((Parser.start config method).feed a).1.extra || decide (0 < b.size) } ∧
    obsOf ((Parser.start config method).feed (a ++ b)).2 =
      obsOf ((Parser.start config method).feed a).2 := by
  have hs := Parser.feed_append (Parser.start config method) a b
  have hd := Parser.feed_done _ b ((Parser.completeCertain_iff _).1 hc).1
  rw [hd] at hs
  exact ⟨hs.1, by simpa using hs.2⟩

/--
**Certainty does not depend on the end of input**, for every run: a run's parser is complete and
certain after `finish` exactly when it was before.
-/
theorem reach_finish_completeCertain {config : Config} {method : Std.Http.Method} {p : Parser}
    {obs : List Obs} (hr : Reach config method p obs) :
    p.finish.1.completeCertain = p.completeCertain :=
  Parser.finish_completeCertain p hr.good.inv

end LeanHttp.Codec
