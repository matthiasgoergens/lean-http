module

public import LeanHttp.Codec.Proofs.Body

@[expose] public section

/-!
# The head reported is the head received

If a run observes a final head `h`, then its input starts with the interim responses' heads and then
`h` itself, byte for byte: a status line with `h`'s version, status code and reason phrase, one field
line per field of `h`, in order, and an empty line (`head_sound`).  A field line for a field `f` is
`f.name ":" v CRLF`, where `v` is any field content whose value, without surrounding whitespace, is
`f.value` (`FieldLineOf`).

So the theorems about `Head.fields` (one `Content-Length`, no `Transfer-Encoding`, and so on) are
theorems about the field lines the server sent.
-/

namespace LeanHttp.Codec

/-! ## Field lines -/

/--
`line` is a field line for `f`: its name (a token: one or more `tchar`), a colon, field content whose
value without the surrounding whitespace is `f.value`, and CRLF.  Neither the name nor the field
content can contain CR, LF or (for the name) a colon, so a field line is exactly one line.
-/
def FieldLineOf (f : Field) (line : List UInt8) : Prop :=
  f.name ≠ [] ∧ (∀ b ∈ f.name, isTChar b = true) ∧
  ∃ v, line = f.name ++ [58] ++ v ++ [cr, lf] ∧ (∀ b ∈ v, isFieldContent b = true) ∧
    trimWs v = f.value

/--
A field line read so far: `cur` are its bytes, and the reader's state agrees with them.  After the
colon, the bytes are some whitespace, the value buffer (in reverse) and some more whitespace (only
after a value of the greatest length), and the CR once read.
-/
def FieldRel (fl : FieldLine) (cur : List UInt8) : Prop :=
  fl.bytes = cur.length ∧ fl.nameLen = fl.name.length ∧ fl.valueLen = fl.value.length ∧
  match fl.st with
  | .start => cur = [] ∧ fl.value = [] ∧ fl.name = []
  | .blankLF => cur = [cr]
  | .name => cur = fl.name.reverse ∧ fl.name ≠ [] ∧ fl.value = []
  | .leadOws _ => fl.value = [] ∧ ∃ ws, cur = fl.name.reverse ++ [58] ++ ws ∧ ∀ b ∈ ws, isWs b = true
  | .value | .trailOws _ | .lf =>
    ∃ ws ws2, (∀ b ∈ ws, isWs b = true) ∧ (∀ b ∈ ws2, isWs b = true) ∧
      (∀ b ∈ fl.value, isFieldContent b = true) ∧
      (∀ d, fl.value.getLast? = some d → isWs d = false) ∧
      (fl.st = .value → ws2 = [] ∧ fl.value ≠ []) ∧
      cur = fl.name.reverse ++ [58] ++ ws ++ fl.value.reverse ++ ws2 ++
        (if fl.st = .lf then [cr] else [])

/--
The name read so far is a token, and not empty once the name has begun.
-/
def NameOK (fl : FieldLine) : Prop :=
  (∀ b ∈ fl.name, isTChar b = true) ∧ (fl.st ≠ .start → fl.st ≠ .blankLF → fl.name ≠ [])

theorem nameOK_empty : NameOK {} := by
  simp [NameOK]

theorem isWs_isFieldContent {b : UInt8} (h : isWs b = true) : isFieldContent b = true := by
  simp [isFieldContent, h]

theorem cr_not_fieldContent : isFieldContent cr = false := by decide
theorem cr_not_ws : isWs cr = false := by decide

theorem dropWhile_ws_all (ws : List UInt8) (h : ∀ b ∈ ws, isWs b = true) (rest : List UInt8) :
    (ws ++ rest).dropWhile isWs = rest.dropWhile isWs := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.cons_append]
    rw [List.dropWhile_cons]
    simp only [h w (by simp), ite_true]
    exact ih (fun b hb => h b (by simp [hb]))

theorem dropWhile_ws_head (x : List UInt8) (h : ∀ d, x.head? = some d → isWs d = false) :
    x.dropWhile isWs = x := by
  cases x with
  | nil => rfl
  | cons d ds => simp [h d rfl]

/--
The value of field content: whitespace, then the value buffer (given in reverse, its last element
the first byte of the value, not whitespace), then whitespace, trims to `trimValue`.
-/
theorem trimWs_value (ws val ws2 : List UInt8) (hws : ∀ b ∈ ws, isWs b = true)
    (hws2 : ∀ b ∈ ws2, isWs b = true) (hfirst : ∀ d, val.getLast? = some d → isWs d = false) :
    trimWs (ws ++ val.reverse ++ ws2) = trimValue val := by
  unfold trimWs trimValue
  rw [List.append_assoc, dropWhile_ws_all ws hws]
  cases hv : val with
  | nil =>
    simp only [List.reverse_nil, List.nil_append, List.dropWhile_nil]
    rw [show ws2 = ws2 ++ [] by simp, dropWhile_ws_all ws2 hws2]
    simp
  | cons e es =>
    rw [← hv]
    rw [dropWhile_ws_head (val.reverse ++ ws2)]
    · rw [List.reverse_append, dropWhile_ws_all ws2.reverse (by simpa using hws2), List.reverse_reverse]
    · intro d hd
      have hsome : val.reverse.head? = some (val.getLast (by simp [hv])) := by
        rw [List.head?_reverse, List.getLast?_eq_some_getLast]
      rw [List.head?_append, hsome] at hd
      simp only [Option.some_or, Option.some.injEq] at hd
      subst hd
      exact hfirst _ (List.getLast?_eq_some_getLast _)

/-- The bytes after the colon of a field line, as `FieldRel` describes them for a state `st`. -/
theorem fieldRel_after {fl : FieldLine} {cur : List UInt8}
    (h : fl.st = .value ∨ (∃ k, fl.st = .trailOws k) ∨ fl.st = .lf) (hr : FieldRel fl cur) :
    ∃ ws ws2, (∀ b ∈ ws, isWs b = true) ∧ (∀ b ∈ ws2, isWs b = true) ∧
      (∀ b ∈ fl.value, isFieldContent b = true) ∧
      (∀ d, fl.value.getLast? = some d → isWs d = false) ∧
      (fl.st = .value → ws2 = [] ∧ fl.value ≠ []) ∧
      cur = fl.name.reverse ++ [58] ++ ws ++ fl.value.reverse ++ ws2 ++
        (if fl.st = .lf then [cr] else []) := by
  obtain ⟨_, _, _, hst⟩ := hr
  rcases h with h | ⟨k, h⟩ | h <;> simp only [h] at hst ⊢ <;> exact hst

theorem getLast?_cons_of_ne_nil {x : UInt8} {xs : List UInt8} (h : xs ≠ []) :
    (x :: xs).getLast? = xs.getLast? := by
  cases xs with
  | nil => contradiction
  | cons y ys => simp [List.getLast?_cons_cons]

/--
A byte that continues a field line keeps the reader's state in agreement with the line's bytes.
-/
theorem stepFieldLine_more {cfg : Config} {fl fl' : FieldLine} {b : UInt8} {cur : List UInt8}
    (hr : FieldRel fl cur) (hs : stepFieldLine cfg fl b = .more fl') : FieldRel fl' (cur ++ [b]) := by
  have hr' := hr
  obtain ⟨hbytes, hnl, hvl, hst⟩ := hr
  unfold stepFieldLine at hs
  dsimp only at hs
  split at hs
  · -- start
    rename_i hfs
    simp only [hfs] at hst
    obtain ⟨rfl, hv, hn⟩ := hst
    split at hs
    · rename_i hb
      cases hs
      simp only [beq_iff_eq] at hb
      subst hb
      simp [FieldRel, hbytes, hnl, hvl]
    · split at hs
      · cases hs
        simp [FieldRel, hbytes, hv, hvl]
      · cases hs
  · -- blankLF
    split at hs <;> cases hs
  · -- name
    rename_i hfs
    simp only [hfs] at hst
    obtain ⟨hcur, hne, hv⟩ := hst
    split at hs
    · split at hs
      · cases hs
        simp [FieldRel, hbytes, hnl, hvl, hcur, hv, hfs]
      · cases hs
    · split at hs
      · rename_i hcol
        cases hs
        simp only [beq_iff_eq] at hcol
        subst hcol
        refine ⟨by simp [hbytes], hnl, hvl, ?_⟩
        simp only
        exact ⟨hv, [], by simp [hcur], by simp⟩
      · cases hs
  · -- leadOws
    rename_i k hfs
    simp only [hfs] at hst
    obtain ⟨hv, ws, hcur, hws⟩ := hst
    split at hs
    · rename_i hb
      split at hs
      · cases hs
        refine ⟨by simp [hbytes], hnl, hvl, ?_⟩
        simp only
        refine ⟨hv, ws ++ [b], by simp [hcur], ?_⟩
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hws x hx
        · exact hb
      · cases hs
    · rename_i hb
      unfold valueByte at hs
      split at hs
      · rename_i hcr
        cases hs
        simp only [beq_iff_eq] at hcr
        subst hcr
        refine ⟨by simp [hbytes], hnl, hvl, ?_⟩
        simp only
        exact ⟨ws, [], hws, by simp, by simp [hv], by simp [hv], by simp, by simp [hcur, hv]⟩
      · split at hs
        · split at hs
          · cases hs
            refine ⟨by simp [hbytes], by simp [hnl], by simp [hvl], ?_⟩
            simp only
            refine ⟨ws, [], hws, by simp, ?_, ?_, by simp, ?_⟩
            · simp_all
            · simp [hv]; simpa using hb
            · simp [hcur, hv]
          · split at hs
            · simp_all
            · cases hs
        · cases hs
  · -- value
    rename_i hfs
    obtain ⟨ws, ws2, hws, hws2, hval, hfirst, hvs, hcur⟩ := fieldRel_after (.inl hfs) hr'
    obtain ⟨hws2e, hne⟩ := hvs hfs
    subst hws2e
    simp only [hfs] at hcur
    unfold valueByte at hs
    split at hs
    · rename_i hcr
      cases hs
      simp only [beq_iff_eq] at hcr
      subst hcr
      refine ⟨by simp [hbytes], hnl, hvl, ?_⟩
      simp only
      exact ⟨ws, [], hws, by simp, hval, hfirst, by simp, by simp [hcur]⟩
    · split at hs
      · rename_i hfc
        split at hs
        · cases hs
          refine ⟨by simp [hbytes], by simp [hnl], by simp [hvl], ?_⟩
          simp only
          refine ⟨ws, [], hws, by simp, ?_, ?_, by simp, by simp [hcur]⟩
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hfc
            · exact hval x hx
          · rw [getLast?_cons_of_ne_nil hne]; exact hfirst
        · split at hs
          · rename_i hw
            cases hs
            simp only [Bool.and_eq_true] at hw
            refine ⟨by simp [hbytes], hnl, hvl, ?_⟩
            simp only
            refine ⟨ws, [b], hws, by simpa using hw.1, hval, hfirst, by simp, by simp [hcur]⟩
          · cases hs
      · cases hs
  · -- trailOws
    rename_i k hfs
    obtain ⟨ws, ws2, hws, hws2, hval, hfirst, hvs, hcur⟩ := fieldRel_after (.inr (.inl ⟨k, hfs⟩)) hr'
    simp only [hfs] at hcur
    split at hs
    · rename_i hb
      split at hs
      · cases hs
        refine ⟨by simp [hbytes], hnl, hvl, ?_⟩
        simp only
        refine ⟨ws, ws2 ++ [b], hws, ?_, hval, hfirst, by simp, by simp [hcur]⟩
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hws2 x hx
        · exact hb
      · cases hs
    · split at hs
      · rename_i hcr
        cases hs
        simp only [beq_iff_eq] at hcr
        subst hcr
        refine ⟨by simp [hbytes], hnl, hvl, ?_⟩
        simp only
        exact ⟨ws, ws2, hws, hws2, hval, hfirst, by simp, by simp [hcur]⟩
      · cases hs
  · -- lf
    split at hs <;> cases hs

theorem stepFieldLine_more_name {cfg : Config} {fl fl' : FieldLine} {b : UInt8} (hn : NameOK fl)
    (hs : stepFieldLine cfg fl b = .more fl') : NameOK fl' := by
  obtain ⟨ht, hne⟩ := hn
  unfold stepFieldLine at hs
  dsimp only at hs
  split at hs
  all_goals (try unfold valueByte at hs)
  all_goals (repeat' split at hs)
  all_goals first
    | (cases hs; done)
    | (cases hs
       refine ⟨?_, ?_⟩
       · intro x hx
         simp only [List.mem_cons] at hx
         first
           | exact ht x hx
           | (rcases hx with rfl | hx <;> simp_all)
       · simp_all)

/--
A field line that ends is a field line for the field reported, and its length is the count reported.
-/
theorem stepFieldLine_field {cfg : Config} {fl : FieldLine} {b : UInt8} {cur : List UInt8}
    {name value : List UInt8} {n : Nat} (hr : FieldRel fl cur) (hn : NameOK fl)
    (hs : stepFieldLine cfg fl b = .field name value n) :
    FieldLineOf { name, value } (cur ++ [b]) ∧ n = (cur ++ [b]).length := by
  have hr' := hr
  obtain ⟨hbytes, _, _, _⟩ := hr
  unfold stepFieldLine at hs
  dsimp only at hs
  split at hs
  · split at hs
    · cases hs
    · split at hs <;> cases hs
  · split at hs <;> cases hs
  · split at hs
    · split at hs <;> cases hs
    · split at hs <;> cases hs
  · split at hs
    · split at hs <;> cases hs
    · unfold valueByte at hs
      split at hs
      · cases hs
      · split at hs
        · split at hs
          · cases hs
          · split at hs <;> cases hs
        · cases hs
  · unfold valueByte at hs
    split at hs
    · cases hs
    · split at hs
      · split at hs
        · cases hs
        · split at hs <;> cases hs
      · cases hs
  · split at hs
    · split at hs <;> cases hs
    · split at hs <;> cases hs
  · rename_i hfs
    split at hs
    · rename_i hlf
      cases hs
      simp only [beq_iff_eq] at hlf
      subst hlf
      obtain ⟨ws, ws2, hws, hws2, hval, hfirst, _, hcur⟩ := fieldRel_after (.inr (.inr hfs)) hr'
      simp only [hfs, ite_true] at hcur
      have hne : fl.name ≠ [] := hn.2 (by simp [hfs]) (by simp [hfs])
      refine ⟨⟨by simpa using hne, fun x hx => hn.1 x (by simpa using hx),
        ws ++ fl.value.reverse ++ ws2, by simp [hcur], ?_, ?_⟩, by simp [hbytes]⟩
      · intro x hx
        simp only [List.mem_append, List.mem_reverse] at hx
        rcases hx with (hx | hx) | hx
        · exact isWs_isFieldContent (hws x hx)
        · exact hval x hx
        · exact isWs_isFieldContent (hws2 x hx)
      · exact trimWs_value ws fl.value ws2 hws hws2 hfirst
    · cases hs

/--
The empty line that ends a section is CRLF.
-/
theorem stepFieldLine_blank {cfg : Config} {fl : FieldLine} {b : UInt8} {cur : List UInt8}
    (hr : FieldRel fl cur) (hs : stepFieldLine cfg fl b = .blank) : cur ++ [b] = [cr, lf] := by
  obtain ⟨_, _, _, hst⟩ := hr
  unfold stepFieldLine at hs
  dsimp only at hs
  split at hs
  · split at hs
    · cases hs
    · split at hs <;> cases hs
  · rename_i hfs
    simp only [hfs] at hst
    split at hs
    · rename_i hlf
      simp only [beq_iff_eq] at hlf
      subst hlf
      simp [hst]
    · cases hs
  · split at hs
    · split at hs <;> cases hs
    · split at hs <;> cases hs
  · split at hs
    · split at hs <;> cases hs
    · unfold valueByte at hs
      split at hs
      · cases hs
      · split at hs
        · split at hs
          · cases hs
          · split at hs <;> cases hs
        · cases hs
  · unfold valueByte at hs
    split at hs
    · cases hs
    · split at hs
      · split at hs
        · cases hs
        · split at hs <;> cases hs
      · cases hs
  · split at hs
    · split at hs <;> cases hs
    · split at hs <;> cases hs
  · split at hs <;> cases hs

/-! ## Status lines -/

/-- `HTTP/` -/
def httpBytes : List UInt8 := [72, 84, 84, 80, 47]

/-- The value of decimal digits. -/
def decValue (ds : List UInt8) : Nat :=
  ds.foldl (fun a d => a * 10 + (digitVal? d).getD 0) 0

/--
`line` is a status line: `HTTP/1.0` (if `http10`) or `HTTP/1.1`, three digits whose value is `code`,
the reason phrase (field content), and CRLF.
-/
def StatusLineOf (http10 : Bool) (code : Nat) (reason line : List UInt8) : Prop :=
  ∃ mj mn ds, line = httpBytes ++ [mj, 46, mn, 32] ++ ds ++ [32] ++ reason ++ [cr, lf] ∧
    digitVal? mj = some 1 ∧ digitVal? mn = some (if http10 then 0 else 1) ∧ ds.length = 3 ∧
    (∀ d ∈ ds, (digitVal? d).isSome = true) ∧ decValue ds = code ∧
    ∀ b ∈ reason, isFieldContent b = true

/--
A status line read so far: `rest` are its bytes, and the reader's state agrees with them.
-/
def StatusRel (sl : StatusLine) (rest : List UInt8) : Prop :=
  sl.reasonLen = sl.reason.length ∧ (∀ b ∈ sl.reason, isFieldContent b = true) ∧
  match sl.st with
  | .expect k => k ≤ 4 ∧ rest = httpBytes.take k ∧ sl.reason = [] ∧ sl.code = 0
  | .major => rest = httpBytes ∧ sl.reason = [] ∧ sl.code = 0
  | .dot => ∃ mj, digitVal? mj = some sl.major ∧ rest = httpBytes ++ [mj] ∧ sl.reason = [] ∧
      sl.code = 0
  | .minor => ∃ mj, digitVal? mj = some sl.major ∧ rest = httpBytes ++ [mj, 46] ∧ sl.reason = [] ∧
      sl.code = 0
  | .sp1 => ∃ mj mn, digitVal? mj = some sl.major ∧ digitVal? mn = some sl.minor ∧
      rest = httpBytes ++ [mj, 46, mn] ∧ sl.reason = [] ∧ sl.code = 0
  | .code k => ∃ mj mn ds, digitVal? mj = some sl.major ∧ digitVal? mn = some sl.minor ∧
      rest = httpBytes ++ [mj, 46, mn, 32] ++ ds ∧ ds.length = k ∧ k ≤ 2 ∧
      (∀ d ∈ ds, (digitVal? d).isSome = true) ∧ decValue ds = sl.code ∧ sl.reason = []
  | .sp2 => ∃ mj mn ds, digitVal? mj = some sl.major ∧ digitVal? mn = some sl.minor ∧
      rest = httpBytes ++ [mj, 46, mn, 32] ++ ds ∧ ds.length = 3 ∧
      (∀ d ∈ ds, (digitVal? d).isSome = true) ∧ decValue ds = sl.code ∧ sl.reason = []
  | .reason => ∃ mj mn ds, digitVal? mj = some sl.major ∧ digitVal? mn = some sl.minor ∧
      rest = httpBytes ++ [mj, 46, mn, 32] ++ ds ++ [32] ++ sl.reason.reverse ∧ ds.length = 3 ∧
      (∀ d ∈ ds, (digitVal? d).isSome = true) ∧ decValue ds = sl.code
  | .lf => ∃ mj mn ds, digitVal? mj = some sl.major ∧ digitVal? mn = some sl.minor ∧
      rest = httpBytes ++ [mj, 46, mn, 32] ++ ds ++ [32] ++ sl.reason.reverse ++ [cr] ∧
      ds.length = 3 ∧ (∀ d ∈ ds, (digitVal? d).isSome = true) ∧ decValue ds = sl.code

theorem httpName_eq (k : Nat) (hk : k < 5) : httpName k = httpBytes[k]'(by simp [httpBytes]; omega) := by
  rcases k with _ | _ | _ | _ | _ | k <;> first | rfl | omega

theorem take_httpBytes_succ (k : Nat) (hk : k < 5) :
    httpBytes.take (k + 1) = httpBytes.take k ++ [httpName k] := by
  rw [httpName_eq k hk, List.take_add_one, List.getElem?_eq_getElem]
  rfl

theorem decValue_snoc (ds : List UInt8) (d : UInt8) (v : Nat) (hv : digitVal? d = some v) :
    decValue (ds ++ [d]) = decValue ds * 10 + v := by
  simp [decValue, List.foldl_append, hv]

theorem stepStatusLine_more {cfg : Config} {sl sl' : StatusLine} {b : UInt8} {rest : List UInt8}
    (hr : StatusRel sl rest) (hs : stepStatusLine cfg sl b = .more sl') :
    StatusRel sl' (rest ++ [b]) := by
  obtain ⟨hlen, hrc, hst⟩ := hr
  unfold stepStatusLine at hs
  split at hs
  · rename_i k hk
    simp only [hk] at hst
    obtain ⟨hk4, hrest, hre, hc⟩ := hst
    split at hs
    · rename_i hb
      cases hs
      simp only [beq_iff_eq] at hb
      subst hb
      by_cases hk' : k < 4
      · refine ⟨hlen, hrc, ?_⟩
        simp only [hk', ite_true]
        refine ⟨by omega, ?_, hre, hc⟩
        rw [hrest, take_httpBytes_succ k (by omega)]
      · have : k = 4 := by omega
        subst this
        refine ⟨hlen, hrc, ?_⟩
        simp only [show ¬ (4 < 4) from by omega, ite_false]
        refine ⟨?_, hre, hc⟩
        rw [hrest, ← take_httpBytes_succ 4 (by omega)]
        rfl
    · cases hs
  · rename_i hk
    simp only [hk] at hst
    obtain ⟨hrest, hre, hc⟩ := hst
    split at hs
    · rename_i d hd
      cases hs
      exact ⟨hlen, hrc, b, hd, by simp [hrest], hre, hc⟩
    · cases hs
  · rename_i hk
    simp only [hk] at hst
    obtain ⟨mj, hmj, hrest, hre, hc⟩ := hst
    split at hs
    · rename_i hb
      cases hs
      simp only [beq_iff_eq] at hb
      subst hb
      exact ⟨hlen, hrc, mj, hmj, by simp [hrest], hre, hc⟩
    · cases hs
  · rename_i hk
    simp only [hk] at hst
    obtain ⟨mj, hmj, hrest, hre, hc⟩ := hst
    split at hs
    · rename_i d hd
      cases hs
      exact ⟨hlen, hrc, mj, b, hmj, hd, by simp [hrest], hre, hc⟩
    · cases hs
  · rename_i hk
    simp only [hk] at hst
    obtain ⟨mj, mn, hmj, hmn, hrest, hre, hc⟩ := hst
    split at hs
    · rename_i hb
      cases hs
      simp only [beq_iff_eq] at hb
      subst hb
      exact ⟨hlen, hrc, mj, mn, [], hmj, hmn, by simp [hrest], rfl, by omega, by simp,
        by simp [decValue, hc], hre⟩
    · cases hs
  · rename_i k hk
    simp only [hk] at hst
    obtain ⟨mj, mn, ds, hmj, hmn, hrest, hds, hk2, hdig, hval, hre⟩ := hst
    split at hs
    · rename_i d hd
      cases hs
      refine ⟨hlen, hrc, ?_⟩
      by_cases hk' : k < 2
      · simp only [hk', ite_true]
        refine ⟨mj, mn, ds ++ [b], hmj, hmn, by simp [hrest], by simp [hds], by omega, ?_, ?_, hre⟩
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hdig x hx
          · simp [hd]
        · rw [decValue_snoc ds b d hd, hval]
      · simp only [hk', ite_false]
        refine ⟨mj, mn, ds ++ [b], hmj, hmn, by simp [hrest], by simp [hds]; omega, ?_, ?_, hre⟩
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hdig x hx
          · simp [hd]
        · rw [decValue_snoc ds b d hd, hval]
    · cases hs
  · rename_i hk
    simp only [hk] at hst
    obtain ⟨mj, mn, ds, hmj, hmn, hrest, hds, hdig, hval, hre⟩ := hst
    split at hs
    · rename_i hb
      cases hs
      simp only [beq_iff_eq] at hb
      subst hb
      exact ⟨hlen, hrc, mj, mn, ds, hmj, hmn, by simp [hrest, hre], hds, hdig, hval⟩
    · cases hs
  · rename_i hk
    simp only [hk] at hst
    obtain ⟨mj, mn, ds, hmj, hmn, hrest, hds, hdig, hval⟩ := hst
    split at hs
    · rename_i hb
      cases hs
      simp only [beq_iff_eq] at hb
      subst hb
      exact ⟨hlen, hrc, mj, mn, ds, hmj, hmn, by simp [hrest], hds, hdig, hval⟩
    · split at hs
      · rename_i hb
        cases hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        refine ⟨by simp [hlen], ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hb.1
          · exact hrc x hx
        · simp only [hk]
          exact ⟨mj, mn, ds, hmj, hmn, by simp [hrest], hds, hdig, hval⟩
      · cases hs
  · split at hs <;> cases hs

theorem stepStatusLine_done {cfg : Config} {sl sl' : StatusLine} {b : UInt8} {rest : List UInt8}
    (hr : StatusRel sl rest) (hs : stepStatusLine cfg sl b = .done sl') :
    sl' = sl ∧ ∃ mj mn ds, rest ++ [b] =
        httpBytes ++ [mj, 46, mn, 32] ++ ds ++ [32] ++ sl.reason.reverse ++ [cr, lf] ∧
      digitVal? mj = some sl.major ∧ digitVal? mn = some sl.minor ∧ ds.length = 3 ∧
      (∀ d ∈ ds, (digitVal? d).isSome = true) ∧ decValue ds = sl.code ∧
      ∀ b ∈ sl.reason, isFieldContent b = true := by
  obtain ⟨_, hrc, hst⟩ := hr
  unfold stepStatusLine at hs
  split at hs
  · split at hs <;> cases hs
  · split at hs <;> cases hs
  · split at hs <;> cases hs
  · split at hs <;> cases hs
  · split at hs <;> cases hs
  · split at hs <;> cases hs
  · split at hs <;> cases hs
  · split at hs
    · cases hs
    · split at hs <;> cases hs
  · rename_i hk
    simp only [hk] at hst
    obtain ⟨mj, mn, ds, hmj, hmn, hrest, hds, hdig, hval⟩ := hst
    split at hs
    · rename_i hb
      cases hs
      simp only [beq_iff_eq] at hb
      subst hb
      exact ⟨rfl, mj, mn, ds, by simp [hrest], hmj, hmn, hds, hdig, hval, hrc⟩
    · cases hs

/-! ## Heads -/

/--
`FieldLines fields lines`: each line is a field line for the field at the same position.
-/
inductive FieldLines : List Field → List (List UInt8) → Prop where
  /-- No fields, no lines. -/
  | nil : FieldLines [] []
  /-- One more field and its line, in front. -/
  | cons {f : Field} {line : List UInt8} {fs : List Field} {lines : List (List UInt8)} :
      FieldLineOf f line → FieldLines fs lines → FieldLines (f :: fs) (line :: lines)

theorem FieldLines.snoc {fs : List Field} {lines : List (List UInt8)} {f : Field} {line : List UInt8}
    (h : FieldLines fs lines) (hf : FieldLineOf f line) : FieldLines (fs ++ [f]) (lines ++ [line]) := by
  induction h with
  | nil => exact .cons hf .nil
  | cons hl _ ih => exact .cons hl ih

/--
`bytes` are a head: a status line, a field line for each of `fields` in order, and CRLF.
-/
def HeadBytesOf (http10 : Bool) (code : Nat) (reason : List UInt8) (fields : List Field)
    (bytes : List UInt8) : Prop :=
  ∃ line lines, bytes = line ++ lines.flatten ++ [cr, lf] ∧ StatusLineOf http10 code reason line ∧
    FieldLines fields lines

/--
`bytes` are `n` interim (1xx, not 101) heads, one after another, each with valid framing fields
(which the parser checks even though an interim response has no body).
-/
inductive InterimHeads : List UInt8 → Nat → Prop where
  /-- None. -/
  | nil : InterimHeads [] 0
  /-- One more. -/
  | snoc {pre bytes : List UInt8} {n : Nat} {http10 : Bool} {code : Nat} {reason : List UInt8}
      {fields : List Field} :
      InterimHeads pre n → 100 ≤ code → code < 200 → code ≠ 101 → declared http10 fields ≠ .invalid →
      HeadBytesOf http10 code reason fields bytes → InterimHeads (pre ++ bytes) (n + 1)

/--
The part of a head read so far agrees with its bytes `rest`.
-/
def PartRel : HeadPart → List UInt8 → Prop
  | .status sl, rest => StatusRel sl rest
  | .fields sl fl fields _ _, rest =>
    ∃ line lines cur, rest = line ++ lines.flatten ++ cur ∧
      StatusLineOf (sl.minor == 0) sl.code sl.reason.reverse line ∧
      FieldLines fields.reverse lines ∧ FieldRel fl cur ∧ NameOK fl

/--
The head reader's state agrees with the bytes `zs` read since the start of the response: interim
heads, then the current head so far.
-/
def HeadRel (hs : HeadState) (zs : List UInt8) : Prop :=
  ∃ pre rest, zs = pre ++ rest ∧ InterimHeads pre hs.interim ∧ PartRel hs.part rest

theorem fieldRel_empty : FieldRel {} [] := by
  simp [FieldRel]

theorem statusRel_empty : StatusRel {} [] := by
  simp [StatusRel]

theorem endOfHead_more_info {cfg : Config} {isHead : Bool} {hs hs' : HeadState} {sl : StatusLine}
    {fields : List Field} (he : endOfHead cfg isHead hs sl fields = .more hs') :
    hs'.interim = hs.interim + 1 ∧ hs'.part = .status {} ∧ 100 ≤ sl.code ∧ sl.code < 200 ∧
      sl.code ≠ 101 ∧ declared (sl.minor == 0) fields ≠ .invalid := by
  unfold endOfHead at he
  dsimp only at he
  split at he
  · cases he
  · rename_i framing hfr
    have hdecl : declared (sl.minor == 0) fields ≠ .invalid := by
      intro hd
      unfold framingOf at hfr
      rw [hd] at hfr
      cases hfr
    split at he
    · rename_i h1
      split at he
      · cases he
      · rename_i h101
        split at he
        · cases he
        · cases he
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
          simp only [beq_iff_eq] at h101
          exact ⟨rfl, rfl, h1.1, h1.2, h101, hdecl⟩
    · split at he <;> cases he

theorem endOfHead_final_info {cfg : Config} {isHead : Bool} {hs : HeadState} {sl : StatusLine}
    {fields : List Field} {h : Head} (he : endOfHead cfg isHead hs sl fields = .final h) :
    h.interim = hs.interim ∧ h.code = sl.code ∧ h.http10 = (sl.minor == 0) ∧
      h.reason = sl.reason.reverse ∧ h.fields = fields := by
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
      · cases he; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem statusLineOf_of_done {sl : StatusLine} {mj mn : UInt8} {ds line : List UInt8}
    (hline : line = httpBytes ++ [mj, 46, mn, 32] ++ ds ++ [32] ++ sl.reason.reverse ++ [cr, lf])
    (hmj : digitVal? mj = some sl.major) (hmn : digitVal? mn = some sl.minor) (hds : ds.length = 3)
    (hdig : ∀ d ∈ ds, (digitVal? d).isSome = true) (hval : decValue ds = sl.code)
    (hrc : ∀ b ∈ sl.reason, isFieldContent b = true) (hmaj : sl.major = 1)
    (hmin : sl.minor = 0 ∨ sl.minor = 1) :
    StatusLineOf (sl.minor == 0) sl.code sl.reason.reverse line := by
  refine ⟨mj, mn, ds, hline, by rw [hmj, hmaj], ?_, hds, hdig, hval, ?_⟩
  · rcases hmin with h | h <;> simp [hmn, h]
  · intro b hb; exact hrc b (List.mem_reverse.mp hb)

/--
A byte that continues the heads keeps the head reader's state in agreement with the bytes.
-/
theorem stepHead_more_rel {cfg : Config} {isHead : Bool} {hs hs' : HeadState} {b : UInt8}
    {zs : List UInt8} (hr : HeadRel hs zs) (he : stepHead cfg isHead hs b = .more hs') :
    HeadRel hs' (zs ++ [b]) := by
  obtain ⟨pre, rest, rfl, hpre, hpart⟩ := hr
  unfold stepHead at he
  split at he
  · rename_i sl hp
    rw [hp] at hpart
    simp only [PartRel] at hpart
    split at he
    · rename_i sl' hs2
      cases he
      exact ⟨pre, rest ++ [b], by simp, hpre, stepStatusLine_more hpart hs2⟩
    · cases he
    · rename_i sl' hs2
      obtain ⟨rfl, mj, mn, ds, hline, hmj, hmn, hds, hdig, hval, hrc⟩ := stepStatusLine_done hpart hs2
      split at he
      · cases he
      · split at he
        · rename_i hv
          cases he
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hv
          refine ⟨pre, rest ++ [b], by simp, hpre, ?_⟩
          simp only [PartRel]
          exact ⟨rest ++ [b], [], [], by simp,
            statusLineOf_of_done hline hmj hmn hds hdig hval hrc hv.1 hv.2, .nil, fieldRel_empty, nameOK_empty⟩
        · cases he
  · rename_i sl fl fields count bytes hp
    rw [hp] at hpart
    simp only [PartRel] at hpart
    obtain ⟨line, lines, cur, hrest, hsl, hf2, hfl, hnm⟩ := hpart
    split at he
    · rename_i fl' hs2
      cases he
      refine ⟨pre, rest ++ [b], by simp, hpre, ?_⟩
      simp only [PartRel]
      exact ⟨line, lines, cur ++ [b], by simp [hrest], hsl, hf2, stepFieldLine_more hfl hs2,
        stepFieldLine_more_name hnm hs2⟩
    · cases he
    · rename_i name value n hs2
      obtain ⟨hfo, _⟩ := stepFieldLine_field hfl hnm hs2
      split at he
      · cases he
      · split at he
        · cases he
        · cases he
          refine ⟨pre, rest ++ [b], by simp, hpre, ?_⟩
          simp only [PartRel]
          refine ⟨line, lines ++ [cur ++ [b]], [], by simp [hrest], hsl, ?_, fieldRel_empty, nameOK_empty⟩
          simp only [List.reverse_cons]
          exact FieldLines.snoc hf2 hfo
    · rename_i hs2
      have hblank := stepFieldLine_blank hfl hs2
      obtain ⟨hint, hpart', hc1, hc2, hc3, hdecl⟩ := endOfHead_more_info he
      refine ⟨pre ++ (rest ++ [b]), [], by simp, ?_, ?_⟩
      · rw [hint]
        refine InterimHeads.snoc hpre hc1 hc2 hc3 hdecl ⟨line, lines, ?_, hsl, hf2⟩
        rw [hrest, List.append_assoc, List.append_assoc, hblank]
        simp
      · rw [hpart']
        exact statusRel_empty

/--
A byte that ends the final head: the bytes read so far are interim heads, then that head.
-/
theorem stepHead_final_rel {cfg : Config} {isHead : Bool} {hs : HeadState} {b : UInt8}
    {zs : List UInt8} {h : Head} (hr : HeadRel hs zs) (he : stepHead cfg isHead hs b = .final h) :
    ∃ pre hb, zs ++ [b] = pre ++ hb ∧ InterimHeads pre h.interim ∧
      HeadBytesOf h.http10 h.code h.reason h.fields hb := by
  obtain ⟨pre, rest, rfl, hpre, hpart⟩ := hr
  unfold stepHead at he
  split at he
  · split at he
    · cases he
    · cases he
    · split at he
      · cases he
      · split at he <;> cases he
  · rename_i sl fl fields count bytes hp
    rw [hp] at hpart
    simp only [PartRel] at hpart
    obtain ⟨line, lines, cur, hrest, hsl, hf2, hfl, _⟩ := hpart
    split at he
    · cases he
    · cases he
    · split at he
      · cases he
      · split at he <;> cases he
    · rename_i hs2
      have hblank := stepFieldLine_blank hfl hs2
      obtain ⟨hint, hcode, h10, hreason, hfields⟩ := endOfHead_final_info he
      refine ⟨pre, rest ++ [b], by simp, by rw [hint]; exact hpre, line, lines, ?_, ?_, ?_⟩
      · rw [hrest, List.append_assoc, List.append_assoc, hblank]
        simp
      · rw [h10, hcode, hreason]; exact hsl
      · rw [hfields]; exact hf2

/-! ## Runs -/

/--
What the bytes `zs` read so far say about the parser: while heads are read, the head reader agrees
with them; once the final head arrived, they start with interim heads and that head.
-/
def HeadSound (p : Parser) (zs : List UInt8) : Prop :=
  (∀ hs, p.phase = .head hs → HeadRel hs zs) ∧
  (∀ h, p.head = some h → ∃ pre hb post, zs = pre ++ hb ++ post ∧ InterimHeads pre h.interim ∧
    HeadBytesOf h.http10 h.code h.reason h.fields hb)

namespace Parser

theorem headSound_extend {p : Parser} {zs : List UInt8} (b : UInt8)
    (h : ∀ h, p.head = some h → ∃ pre hb post, zs = pre ++ hb ++ post ∧ InterimHeads pre h.interim ∧
      HeadBytesOf h.http10 h.code h.reason h.fields hb) :
    ∀ h, p.head = some h → ∃ pre hb post, zs ++ [b] = pre ++ hb ++ post ∧
      InterimHeads pre h.interim ∧ HeadBytesOf h.http10 h.code h.reason h.fields hb := by
  intro h' hh
  obtain ⟨pre, hb, post, hz, hi, hhb⟩ := h h' hh
  exact ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb⟩

theorem stepByte_headSound (p : Parser) (zs : List UInt8) (b : UInt8) (hs : HeadSound p zs) :
    HeadSound (p.stepByte b).1 (zs ++ [b]) := by
  obtain ⟨hph, hhd⟩ := hs
  have hext := headSound_extend b hhd
  unfold stepByte
  split
  · rename_i hsh hp
    split
    · rename_i hs' he
      exact ⟨by simpa using stepHead_more_rel (hph hsh hp) he, by simpa using hext⟩
    · exact ⟨by simp [fail], by simpa [fail] using hext⟩
    · rename_i h he
      obtain ⟨pre, hb, hz, hi, hhb⟩ := stepHead_final_rel (hph hsh hp) he
      have hhead : (p.startBody h).1.head = some h := by
        unfold startBody; dsimp only; split <;> (try split) <;> rfl
      refine ⟨?_, ?_⟩
      · unfold startBody; dsimp only; split <;> (try split) <;> simp
      · intro h' hh'
        rw [hhead] at hh'
        cases hh'
        exact ⟨pre, hb, [], by simp [hz], hi, hhb⟩
  all_goals
    first
      | exact ⟨by simp_all, by simpa using hext⟩
      | (split <;> (try split) <;> exact ⟨by simp_all [fail], by simpa [fail] using hext⟩)

theorem run_headSound (p : Parser) (zs xs : List UInt8) (hs : HeadSound p zs) :
    HeadSound (p.run xs).1 (zs ++ xs) := by
  induction xs generalizing p zs with
  | nil => simpa using hs
  | cons b bs ih =>
    have := ih _ _ (stepByte_headSound p zs b hs)
    simpa [run_cons] using this

end Parser

/--
**The head reported is the head received.**  If feeding `bytes` to a parser observes a final head
`h`, then `bytes` start with `h.interim` interim heads and then `h` itself: a status line with `h`'s
version, code and reason phrase, a field line for each of `h.fields` in order, and an empty line.
By split invariance (`feedAll_eq`) the same holds however `bytes` are cut into pieces.
-/
theorem head_sound (config : Config) (method : Std.Http.Method) (bytes : ByteArray) {h : Head}
    (hh : Obs.head h ∈ obsOf ((Parser.start config method).feed bytes).2) :
    ∃ pre hb post, bytes.data.toList = pre ++ hb ++ post ∧ InterimHeads pre h.interim ∧
      HeadBytesOf h.http10 h.code h.reason h.fields hb := by
  have hg := (Reach.feed bytes Reach.start : Reach config method _ _).good
  have hsome := (hg.head h).1 (by simpa using hh)
  have hs0 : HeadSound (Parser.start config method) [] :=
    ⟨by
      intro hs hp
      simp only [Parser.start, Phase.head.injEq] at hp
      subst hp
      exact ⟨[], [], rfl, .nil, show StatusRel {} [] from statusRel_empty⟩,
     by simp [Parser.start]⟩
  have hs := Parser.run_headSound _ [] bytes.data.toList hs0
  rw [← (Parser.feed_eq_run _ bytes).1] at hs
  simpa using hs.2 h hsome

/--
**Content-Length, as received.**  If feeding `bytes` observes a final head with `Content-Length: n`
framing, then the head received has exactly one field line named `Content-Length` (in any case),
whose value reads as `n`, and none named `Transfer-Encoding`; and it answers a request other than
HEAD with a status other than 1xx, 204 and 304.
-/
theorem received_length_declared (config : Config) (method : Std.Http.Method) (bytes : ByteArray)
    {h : Head} {n : Nat} (hh : Obs.head h ∈ obsOf ((Parser.start config method).feed bytes).2)
    (hn : h.framing = .length n) :
    ∃ pre line lines post, bytes.data.toList = pre ++ line ++ lines.flatten ++ [cr, lf] ++ post ∧
      InterimHeads pre h.interim ∧ StatusLineOf h.http10 h.code h.reason line ∧
      FieldLines h.fields lines ∧
      method ≠ .head ∧ noBodyStatus h.code = false ∧
      h.fields.filter (·.isNamed transferEncodingName) = [] ∧
      ∃ cl, h.fields.filter (·.isNamed contentLengthName) = [cl] ∧ parseDecimal cl.value = some n := by
  obtain ⟨pre, hb, post, hbytes, hi, line, lines, hhb, hsl, hf2⟩ := head_sound config method bytes hh
  have hd := reach_length_declared (Reach.feed bytes Reach.start) (by simpa using hh) hn
  exact ⟨pre, line, lines, post, by rw [hbytes, hhb]; simp, hi, hsl, hf2, hd⟩

end LeanHttp.Codec
