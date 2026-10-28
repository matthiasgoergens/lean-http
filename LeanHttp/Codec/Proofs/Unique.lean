module

public import LeanHttp.Codec.Proofs.ResponseSound

@[expose] public section

/-!
# The specifications are unambiguous

`head_sound` and `response_sound` describe the input by existential decompositions: a head made of a
status line and field lines, a chunked body made of chunks.  Here those descriptions are shown to
read the bytes in one way only:

- a chunked body's payload is determined by its bytes, whatever follows it
  (`chunkedBody_payload_unique`);
- a head's version, status code, reason phrase and fields are determined by its bytes, and so is
  where it ends (`headBytes_unique`).

So the payload and the head that `response_sound` and `head_sound` speak of are functions of the
input.
-/

namespace LeanHttp.Codec

/-! ## Lines end at the first CR -/

theorem first_cr {l l' r r' : List UInt8} (hl : ∀ b ∈ l, b ≠ cr) (hl' : ∀ b ∈ l', b ≠ cr)
    (h : l ++ cr :: r = l' ++ cr :: r') : l = l' ∧ r = r' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => simpa using h
    | cons y ys =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm (hl' y (by simp))
  | cons x xs ih =>
    cases l' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (hl x (by simp))
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih (fun b hb => hl b (by simp [hb])) (fun b hb => hl' b (by simp [hb])) h
      exact ⟨by rw [this.1], this.2⟩

/-- A longest prefix of elements satisfying `p` is determined. -/
theorem prefix_unique {p : UInt8 → Bool} {ds ds' e e' : List UInt8} (hd : ∀ d ∈ ds, p d = true)
    (hd' : ∀ d ∈ ds', p d = true) (he : ∀ x, e.head? = some x → p x = false)
    (he' : ∀ x, e'.head? = some x → p x = false) (h : ds ++ e = ds' ++ e') : ds = ds' ∧ e = e' := by
  induction ds generalizing ds' with
  | nil =>
    cases ds' with
    | nil => simpa using h
    | cons y ys =>
      simp only [List.nil_append, List.cons_append] at h
      subst h
      have := he y (by simp)
      simp [hd' y (by simp)] at this
  | cons x xs ih =>
    cases ds' with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      have := he' x (by simp [← h])
      simp [hd x (by simp)] at this
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih (fun d hd2 => hd d (by simp [hd2])) (fun d hd2 => hd' d (by simp [hd2])) h
      exact ⟨by rw [this.1], this.2⟩

theorem hex_ne_cr {d : UInt8} (h : (hexVal? d).isSome = true) : d ≠ cr := by
  rintro rfl; simp at h

/-! ## Chunked bodies -/

/--
A chunk-size line is determined by the bytes it starts, and so is the size it announces.
-/
theorem sizeLine_unique {n n' : Nat} {line line' r r' : List UInt8} (h : SizeLineOf n line)
    (h' : SizeLineOf n' line') (heq : line ++ r = line' ++ r') : line = line' ∧ n = n' ∧ r = r' := by
  obtain ⟨ds, ext, rfl, hn, hhex, hval, hext, hhead⟩ := h
  obtain ⟨ds', ext', rfl, hn', hhex', hval', hext', hhead'⟩ := h'
  have hl : ∀ b ∈ ds ++ ext, b ≠ cr := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hex_ne_cr (hhex b hb)
    · exact (hext b hb).1
  have hl' : ∀ b ∈ ds' ++ ext', b ≠ cr := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hex_ne_cr (hhex' b hb)
    · exact (hext' b hb).1
  have heq2 : (ds ++ ext) ++ cr :: (lf :: r) = (ds' ++ ext') ++ cr :: (lf :: r') := by
    simpa using heq
  obtain ⟨h1, h2⟩ := first_cr hl hl' heq2
  obtain ⟨hds, hexts⟩ := prefix_unique (p := fun d => (hexVal? d).isSome) hhex hhex' hhead hhead' h1
  subst hds hexts
  simp only [List.cons.injEq, true_and] at h2
  exact ⟨rfl, by rw [← hval, ← hval'], h2⟩

/--
A chunked body read from the front: a last chunk and trailers, or a chunk and the rest.
-/
inductive ChunkedFront : List UInt8 → List UInt8 → Prop where
  /-- The size line announcing 0, and the trailer section. -/
  | last {line trailers : List UInt8} :
      SizeLineOf 0 line → TrailersOf trailers → ChunkedFront (line ++ trailers) []
  /-- A chunk, then the rest of the body. -/
  | chunk {line data rest payload : List UInt8} :
      SizeLineOf data.length line → data ≠ [] → ChunkedFront rest payload →
      ChunkedFront (line ++ data ++ [cr, lf] ++ rest) (data ++ payload)

theorem chunks_front {pre payload : List UInt8} (hc : Chunks pre payload) :
    ∀ {tail tp : List UInt8}, ChunkedFront tail tp → ChunkedFront (pre ++ tail) (payload ++ tp) := by
  induction hc with
  | nil => intro tail tp h; simpa using h
  | snoc _ hsl hne ih =>
    intro tail tp h
    have := ih (ChunkedFront.chunk hsl hne h)
    simpa [List.append_assoc] using this

theorem chunkedBody_front {bytes payload : List UInt8} (h : ChunkedBody bytes payload) :
    ChunkedFront bytes payload := by
  obtain ⟨pre, line, trailers, rfl, hc, hsl, ht⟩ := h
  have := chunks_front hc (ChunkedFront.last hsl ht)
  simpa [List.append_assoc] using this

theorem chunkedFront_payload_unique {b b' p p' e e' : List UInt8} (h : ChunkedFront b p)
    (h' : ChunkedFront b' p') (heq : b ++ e = b' ++ e') : p = p' := by
  induction h generalizing b' p' e e' with
  | last hsl _ =>
    cases h' with
    | last => rfl
    | chunk hsl' hne' _ =>
      have := (sizeLine_unique hsl hsl' (by simpa [List.append_assoc] using heq)).2.1
      exact absurd (List.length_eq_zero_iff.mp this.symm) hne'
  | chunk hsl hne _ ih =>
    cases h' with
    | last hsl' _ =>
      have := (sizeLine_unique hsl hsl' (by simpa [List.append_assoc] using heq)).2.1
      exact absurd (List.length_eq_zero_iff.mp this) hne
    | chunk hsl' _ hrest' =>
      obtain ⟨_, hn, hr⟩ := sizeLine_unique hsl hsl' (by simpa [List.append_assoc] using heq)
      obtain ⟨hd, hr2⟩ := List.append_inj hr hn
      subst hd
      simp only [List.cons.injEq, true_and] at hr2
      rw [ih hrest' hr2]

/--
**A chunked body's payload is determined by its bytes**, whatever follows them: if `b ++ e` and
`b' ++ e'` are the same bytes and `b`, `b'` are chunked bodies, their payloads are equal.
-/
theorem chunkedBody_payload_unique {b b' p p' e e' : List UInt8} (h : ChunkedBody b p)
    (h' : ChunkedBody b' p') (heq : b ++ e = b' ++ e') : p = p' :=
  chunkedFront_payload_unique (chunkedBody_front h) (chunkedBody_front h') heq

/-! ## Heads -/

theorem digit_ne_cr {d : UInt8} {v : Nat} (h : digitVal? d = some v) : d ≠ cr := by
  rintro rfl
  have : ¬ ((48 : UInt8) ≤ cr) := by decide
  simp [digitVal?, this] at h

theorem digits_ne_cr {ds : List UInt8} (h : ∀ d ∈ ds, (digitVal? d).isSome = true) :
    ∀ d ∈ ds, d ≠ cr := by
  intro d hd; rintro rfl; have := h cr hd
  have hn : ¬ ((48 : UInt8) ≤ cr) := by decide
  simp [digitVal?, hn] at this

theorem fieldContent_ne_cr {b : UInt8} (h : isFieldContent b = true) : b ≠ cr := by
  rintro rfl; simp [cr_not_fieldContent] at h

theorem tchar_ne_cr {b : UInt8} (h : isTChar b = true) : b ≠ cr := by
  rintro rfl; revert h; decide

/--
A status line is determined by the bytes it starts, and so are its version, code and reason phrase.
-/
theorem statusLine_unique {a a' : Bool} {c c' : Nat} {r r' line line' x x' : List UInt8}
    (h : StatusLineOf a c r line) (h' : StatusLineOf a' c' r' line') (heq : line ++ x = line' ++ x') :
    line = line' ∧ a = a' ∧ c = c' ∧ r = r' ∧ x = x' := by
  obtain ⟨mj, mn, ds, rfl, hmj, hmn, hds, hdig, hval, hr⟩ := h
  obtain ⟨mj', mn', ds', rfl, hmj', hmn', hds', hdig', hval', hr'⟩ := h'
  have hnc : ∀ (mj mn : UInt8) (ds r : List UInt8), digitVal? mj = some 1 →
      (∃ v, digitVal? mn = some v) → (∀ d ∈ ds, (digitVal? d).isSome = true) →
      (∀ b ∈ r, isFieldContent b = true) →
      ∀ b ∈ httpBytes ++ [mj, 46, mn, 32] ++ ds ++ [32] ++ r, b ≠ cr := by
    intro mj mn ds r hmj ⟨v, hmn⟩ hdig hr b hb
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with (((hb | hb) | hb) | hb) | hb
    · simp [httpBytes] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide
    · rcases hb with rfl | rfl | rfl | rfl
      · exact digit_ne_cr hmj
      · decide
      · exact digit_ne_cr hmn
      · decide
    · exact digits_ne_cr hdig b hb
    · subst hb; decide
    · exact fieldContent_ne_cr (hr b hb)
  have heq2 : (httpBytes ++ [mj, 46, mn, 32] ++ ds ++ [32] ++ r) ++ cr :: (lf :: x) =
      (httpBytes ++ [mj', 46, mn', 32] ++ ds' ++ [32] ++ r') ++ cr :: (lf :: x') := by
    simpa using heq
  obtain ⟨h1, h2⟩ := first_cr (hnc _ _ _ _ hmj ⟨_, hmn⟩ hdig hr) (hnc _ _ _ _ hmj' ⟨_, hmn'⟩ hdig' hr') heq2
  simp only [List.cons.injEq, true_and] at h2
  -- The parts before the reason phrase have the same length.
  have hlen : (httpBytes ++ [mj, 46, mn, 32] ++ ds ++ [32]).length =
      (httpBytes ++ [mj', 46, mn', 32] ++ ds' ++ [32]).length := by
    simp [hds, hds']
  obtain ⟨hp, hrr⟩ := List.append_inj h1 hlen
  have hlen2 : (httpBytes ++ [mj, 46, mn, 32] ++ ds).length =
      (httpBytes ++ [mj', 46, mn', 32] ++ ds').length := by
    simp [hds, hds']
  obtain ⟨hp2, _⟩ := List.append_inj hp hlen2
  have hlen3 : (httpBytes ++ [mj, 46, mn, 32]).length = (httpBytes ++ [mj', 46, mn', 32]).length := by
    simp
  obtain ⟨hp3, hdseq⟩ := List.append_inj hp2 hlen3
  simp only [List.append_cancel_left_eq, List.cons.injEq, and_true, true_and] at hp3
  obtain ⟨rfl, rfl⟩ := hp3
  subst hdseq hrr h2
  refine ⟨rfl, ?_, by rw [← hval, ← hval'], rfl, rfl⟩
  rw [hmn] at hmn'
  cases a <;> cases a' <;> simp_all

/--
A field line is determined by the bytes it starts, and so is its field.
-/
theorem fieldLine_unique {f f' : Field} {line line' x x' : List UInt8} (h : FieldLineOf f line)
    (h' : FieldLineOf f' line') (heq : line ++ x = line' ++ x') : line = line' ∧ f = f' ∧ x = x' := by
  obtain ⟨hne, htc, v, rfl, hv, hval⟩ := h
  obtain ⟨hne', htc', v', rfl, hv', hval'⟩ := h'
  have hnc : ∀ (name v : List UInt8), (∀ b ∈ name, isTChar b = true) →
      (∀ b ∈ v, isFieldContent b = true) → ∀ b ∈ name ++ [58] ++ v, b ≠ cr := by
    intro name v hn hv b hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with (hb | rfl) | hb
    · exact tchar_ne_cr (hn b hb)
    · decide
    · exact fieldContent_ne_cr (hv b hb)
  have heq2 : (f.name ++ [58] ++ v) ++ cr :: (lf :: x) = (f'.name ++ [58] ++ v') ++ cr :: (lf :: x') := by
    simpa using heq
  obtain ⟨h1, h2⟩ := first_cr (hnc _ _ htc hv) (hnc _ _ htc' hv') heq2
  simp only [List.cons.injEq, true_and] at h2
  have h1' : f.name ++ (58 :: v) = f'.name ++ (58 :: v') := by simpa using h1
  obtain ⟨hn, hrest⟩ := prefix_unique (p := isTChar) htc htc' (by intro x hx; simp at hx; subst hx; decide)
    (by intro x hx; simp at hx; subst hx; decide) h1'
  simp only [List.cons.injEq, true_and] at hrest
  subst hrest h2
  have hf : f = f' := by
    cases f; cases f'
    simp only at hn hval hval'
    subst hn
    rw [← hval, ← hval']
  subst hf
  exact ⟨rfl, rfl, rfl⟩

theorem fieldLine_head {f : Field} {line : List UInt8} (h : FieldLineOf f line) :
    ∃ c rest, line = c :: rest ∧ isTChar c = true := by
  obtain ⟨hne, htc, v, rfl, _, _⟩ := h
  cases hn : f.name with
  | nil => exact absurd hn hne
  | cons c cs => exact ⟨c, cs ++ [58] ++ v ++ [cr, lf], by simp, htc c (by rw [hn]; simp)⟩

theorem fieldLines_unique {fs fs' : List Field} {ls ls' : List (List UInt8)} {x x' : List UInt8}
    (h : FieldLines fs ls) (h' : FieldLines fs' ls')
    (heq : ls.flatten ++ cr :: lf :: x = ls'.flatten ++ cr :: lf :: x') :
    fs = fs' ∧ ls = ls' ∧ x = x' := by
  induction h generalizing fs' ls' with
  | nil =>
    cases h' with
    | nil => simpa using heq
    | cons hl _ =>
      obtain ⟨c, rest, rfl, hc⟩ := fieldLine_head hl
      simp only [List.flatten_nil, List.nil_append, List.flatten_cons, List.cons_append,
        List.cons.injEq] at heq
      rw [← heq.1] at hc
      exact absurd hc (by decide)
  | cons hl _ ih =>
    cases h' with
    | nil =>
      obtain ⟨c, rest, rfl, hc⟩ := fieldLine_head hl
      simp only [List.flatten_nil, List.nil_append, List.flatten_cons, List.cons_append,
        List.cons.injEq] at heq
      rw [heq.1] at hc
      exact absurd hc (by decide)
    | cons hl' hls' =>
      simp only [List.flatten_cons, List.append_assoc] at heq
      obtain ⟨rfl, rfl, hrest⟩ := fieldLine_unique hl hl' heq
      obtain ⟨rfl, rfl, rfl⟩ := ih hls' hrest
      exact ⟨rfl, rfl, rfl⟩

/--
A head is determined by the bytes it starts: its version, status code, reason phrase and fields,
and where it ends.
-/
theorem headBytes_unique {a a' : Bool} {c c' : Nat} {r r' : List UInt8} {fs fs' : List Field}
    {hb hb' x x' : List UInt8} (h : HeadBytesOf a c r fs hb) (h' : HeadBytesOf a' c' r' fs' hb')
    (heq : hb ++ x = hb' ++ x') : a = a' ∧ c = c' ∧ r = r' ∧ fs = fs' ∧ hb = hb' ∧ x = x' := by
  obtain ⟨line, lines, rfl, hsl, hfl⟩ := h
  obtain ⟨line', lines', rfl, hsl', hfl'⟩ := h'
  have heq2 : line ++ (lines.flatten ++ cr :: lf :: x) = line' ++ (lines'.flatten ++ cr :: lf :: x') := by
    simpa using heq
  obtain ⟨rfl, rfl, rfl, rfl, hrest⟩ := statusLine_unique hsl hsl' heq2
  obtain ⟨rfl, rfl, rfl⟩ := fieldLines_unique hfl hfl' hrest
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Interim heads read from the front.
-/
inductive InterimFront : List UInt8 → Nat → Prop where
  /-- None. -/
  | nil : InterimFront [] 0
  /-- An interim head, then the rest. -/
  | cons {hb rest : List UInt8} {n : Nat} {a : Bool} {c : Nat} {r : List UInt8} {fs : List Field} :
      100 ≤ c → c < 200 → c ≠ 101 → HeadBytesOf a c r fs hb → InterimFront rest n →
      InterimFront (hb ++ rest) (n + 1)

theorem interim_front {pre : List UInt8} {n : Nat} (h : InterimHeads pre n) :
    ∀ {tail : List UInt8} {m : Nat}, InterimFront tail m → InterimFront (pre ++ tail) (n + m) := by
  induction h with
  | nil => intro tail m ht; simpa using ht
  | snoc _ h1 h2 h3 _ hhb ih =>
    intro tail m ht
    have := ih (InterimFront.cons h1 h2 h3 hhb ht)
    simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using this

theorem interim_unique {pre pre' hb hb' x x' : List UInt8} {n n' : Nat} {a a' : Bool} {c c' : Nat}
    {r r' : List UInt8} {fs fs' : List Field} (h : InterimFront pre n) (h' : InterimFront pre' n')
    (hf : HeadBytesOf a c r fs hb) (hf' : HeadBytesOf a' c' r' fs' hb') (hc : 200 ≤ c) (hc' : 200 ≤ c')
    (heq : pre ++ hb ++ x = pre' ++ hb' ++ x') : pre = pre' ∧ n = n' := by
  induction h generalizing pre' n' with
  | nil =>
    cases h' with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ h2 _ hhb _ =>
      have := (headBytes_unique hf hhb (by simpa [List.append_assoc] using heq)).2.1
      omega
  | cons h1 h2 _ hhb _ ih =>
    cases h' with
    | nil =>
      have := (headBytes_unique hhb hf' (by simpa [List.append_assoc] using heq)).2.1
      omega
    | cons _ _ _ hhb' hrest' =>
      obtain ⟨_, _, _, _, rfl, hrest⟩ := headBytes_unique hhb hhb' (by simpa [List.append_assoc] using heq)
      obtain ⟨rfl, rfl⟩ := ih hrest' (by simpa [List.append_assoc] using hrest)
      exact ⟨rfl, rfl⟩

/--
**The decomposition of `head_sound` is unique.**  If the same bytes are interim heads followed by a
final head (status at least 200) in two ways, the two ways agree: the same interim heads, as many,
and the same final head, with the same version, code, reason phrase and fields.
-/
theorem head_sound_unique {pre pre' hb hb' post post' : List UInt8} {n n' : Nat} {a a' : Bool}
    {c c' : Nat} {r r' : List UInt8} {fs fs' : List Field} (hi : InterimHeads pre n)
    (hi' : InterimHeads pre' n') (hf : HeadBytesOf a c r fs hb) (hf' : HeadBytesOf a' c' r' fs' hb')
    (hc : 200 ≤ c) (hc' : 200 ≤ c') (heq : pre ++ hb ++ post = pre' ++ hb' ++ post') :
    pre = pre' ∧ n = n' ∧ a = a' ∧ c = c' ∧ r = r' ∧ fs = fs' ∧ hb = hb' ∧ post = post' := by
  have hfr := interim_front hi (InterimFront.nil)
  have hfr' := interim_front hi' (InterimFront.nil)
  simp only [List.append_nil, Nat.add_zero] at hfr hfr'
  obtain ⟨rfl, rfl⟩ := interim_unique hfr hfr' hf hf' hc hc' heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := headBytes_unique hf hf' (by simpa [List.append_assoc] using heq)
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanHttp.Codec
