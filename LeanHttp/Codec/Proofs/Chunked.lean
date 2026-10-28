module

public import LeanHttp.Codec.Proofs.Body

@[expose] public section

/-!
# Chunked bodies: a round trip

Decoding what `encodeChunked` encodes delivers exactly the concatenation of the chunks, then ends the
response (`feed_encodeChunked`, and `roundtrip_chunked` for a whole response).  By split invariance
the same holds however the encoded bytes are cut into pieces.

The conditions are those the encoder itself needs to be decodable: every chunk shorter than
`16 ^ 16` bytes (at most 16 hex digits), chunk-size lines of 18 bytes allowed, and the body within
`Config.maxBody`.
-/

namespace LeanHttp.Codec

/-! ## Hex digits -/

/--
The value of hex digits read after `acc`, as the chunk-size line reader accumulates it.
-/
def hexValue (acc : Nat) (ds : List UInt8) : Nat :=
  ds.foldl (fun a d => a * 16 + (hexVal? d).getD 0) acc

theorem hexVal_hexChar : ∀ d, d < 16 → hexVal? (hexChar d) = some d := by
  decide

theorem hexDigits_eq (n : Nat) :
    hexDigits n = if n < 16 then [hexChar n] else hexDigits (n / 16) ++ [hexChar (n % 16)] := by
  rw [hexDigits]

theorem hexDigits_hex (n : Nat) : ∀ d ∈ hexDigits n, (hexVal? d).isSome := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [hexDigits_eq]
    split
    · simp [hexVal_hexChar n (by omega)]
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact ih (n / 16) (by omega) d hd
      · subst hd; simp [hexVal_hexChar (n % 16) (Nat.mod_lt _ (by omega))]

theorem hexValue_hexDigits (n : Nat) : hexValue 0 (hexDigits n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [hexDigits_eq]
    split
    · simp [hexValue, hexVal_hexChar n (by omega)]
    · have h := ih (n / 16) (by omega)
      simp only [hexValue, List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
      rw [h, hexVal_hexChar (n % 16) (Nat.mod_lt _ (by omega))]
      simp only [Option.getD_some]
      omega

theorem length_hexDigits_pos (n : Nat) : 0 < (hexDigits n).length := by
  rw [hexDigits_eq]
  split <;> simp

theorem length_hexDigits_le (n k : Nat) (hk : 0 < k) (hn : n < 16 ^ k) : (hexDigits n).length ≤ k := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    rw [hexDigits_eq]
    split
    · simp; omega
    · rcases k with _ | k
      · omega
      · have h16 : n / 16 < 16 ^ k := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          rw [Nat.pow_succ] at hn
          exact hn
        rcases k with _ | k
        · simp at h16; omega
        · have := ih (n / 16) (by omega) (k + 1) (by omega) h16
          simp
          omega

/-! ## Byte facts -/

@[simp] theorem hexVal_cr : hexVal? cr = none := by decide
@[simp] theorem hexVal_lf : hexVal? lf = none := by decide
@[simp] theorem hexVal_zero : hexVal? 48 = some 0 := by decide
@[simp] theorem isWs_cr : isWs cr = false := by decide
@[simp] theorem cr_beq_semi : (cr == 59) = false := by decide
@[simp] theorem cr_beq_cr : (cr == cr) = true := by decide
@[simp] theorem lf_beq_lf : (lf == lf) = true := by decide

namespace Parser

/-! ## Chunk-size lines -/

theorem run_hexDigits (p : Parser) (ds : List UInt8) (j acc : Nat)
    (hp : p.phase = .body (.chunked (.line { st := .size j, size := acc, exts := 0, bytes := j })))
    (hds : ∀ d ∈ ds, (hexVal? d).isSome) (hlen : j + ds.length ≤ 16)
    (hline : j + ds.length ≤ p.config.maxChunkLineLength) :
    (p.run ds).1 = { p with
      phase := .body (.chunked (.line
        { st := .size (j + ds.length), size := hexValue acc ds, exts := 0, bytes := j + ds.length })) } ∧
    obsOf (p.run ds).2 = [] := by
  induction ds generalizing p j acc with
  | nil => cases p; simp_all [hexValue]
  | cons d ds ih =>
    have hj1 : ¬ p.config.maxChunkLineLength ≤ j := by simp only [List.length_cons] at hline; omega
    have hj2 : j < 16 := by simp only [List.length_cons] at hlen; omega
    obtain ⟨v, hv⟩ : ∃ v, hexVal? d = some v := Option.isSome_iff_exists.mp (hds d (by simp))
    have hstep : p.stepByte d = ({ p with
        phase := .body (.chunked (.line
          { st := .size (j + 1), size := acc * 16 + v, exts := 0, bytes := j + 1 })) }, #[]) := by
      simp [stepByte, hp, stepChunk, stepChunkLine, hv, hj1, hj2]
    have h1 := ih { p with
        phase := .body (.chunked (.line
          { st := .size (j + 1), size := acc * 16 + v, exts := 0, bytes := j + 1 })) }
      (j + 1) (acc * 16 + v) rfl (fun d' hd' => hds d' (by simp [hd']))
      (by simp only [List.length_cons] at hlen; omega)
      (by simp only [List.length_cons] at hline; show j + 1 + ds.length ≤ p.config.maxChunkLineLength; omega)
    rw [run_cons, hstep]
    simp only at h1
    refine ⟨?_, ?_⟩
    · rw [h1.1]
      simp only [List.length_cons, hexValue, List.foldl_cons, hv, Option.getD_some]
      rw [show j + 1 + ds.length = j + (ds.length + 1) by omega]
    · simp [h1.2]

/-! ## One chunk -/

theorem run_encodeChunk (p : Parser) (c : List UInt8) (hp : p.phase = .body (.chunked (.line {})))
    (hc : c ≠ []) (hsize : c.length < 16 ^ 16) (hmax : p.delivered + c.length ≤ p.config.maxBody)
    (hline : 18 ≤ p.config.maxChunkLineLength) :
    (p.run (encodeChunk c)).1 = { p with delivered := p.delivered + c.length } ∧
    obsOf (p.run (encodeChunk c)).2 = c.map .byte := by
  have hk := length_hexDigits_le c.length 16 (by omega) hsize
  have hk0 := length_hexDigits_pos c.length
  have hlen : 0 < c.length := List.length_pos_iff.mpr hc
  obtain ⟨k, hkdef⟩ : ∃ k, (hexDigits c.length).length = k := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, c.length = m + 1 := ⟨c.length - 1, by omega⟩
  -- the size digits
  have hd := run_hexDigits p (hexDigits c.length) 0 0 hp (hexDigits_hex _) (by omega) (by omega)
  rw [hexValue_hexDigits, Nat.zero_add, hkdef] at hd
  -- CR, LF
  have hcrlf : ({ p with phase := .body (.chunked (.line
      { st := .size k, size := c.length, exts := 0, bytes := k })) } : Parser).run [cr, lf] =
      ({ p with phase := .body (.chunked (.data (m + 1))) }, #[]) := by
    have hroom : m + 1 ≤ p.config.maxBody - p.delivered := by omega
    simp [run_cons, stepByte, stepChunk, stepChunkLine, afterExt, afterExtNoWs,
      show ¬ p.config.maxChunkLineLength ≤ k by omega,
      show ¬ p.config.maxChunkLineLength ≤ k + 1 by omega, show k ≠ 0 by omega, hm, hroom]
  -- the data
  have hdata := run_chunkData { p with phase := .body (.chunked (.data (m + 1))) } m c rfl (by omega)
  simp only [show c.length = m + 1 from hm, ite_true] at hdata
  -- CR, LF
  have hend : ({ p with phase := .body (.chunked .dataCR), delivered := p.delivered + (m + 1) } :
      Parser).run [cr, lf] = ({ p with delivered := p.delivered + (m + 1) }, #[]) := by
    simp only [run_cons, stepByte, stepChunk]
    simp
    cases p; simp_all
  unfold encodeChunk
  rw [run_append, run_append, run_append, hd.1, hcrlf, hdata.1, hend]
  refine ⟨by rw [hm], ?_⟩
  simp only [obsOf_append, hd.2, obsOf_empty, hdata.2, List.nil_append, List.append_nil]

/-! ## A whole chunked body -/

theorem run_lastChunk (p : Parser) (hp : p.phase = .body (.chunked (.line {})))
    (hline : 18 ≤ p.config.maxChunkLineLength) :
    (p.run [48, cr, lf, cr, lf]).1 = { p with phase := .done } ∧
    obsOf (p.run [48, cr, lf, cr, lf]).2 = [.done] := by
  simp [run_cons, stepByte, hp, stepChunk, stepChunkLine, stepFieldLine, afterExt, afterExtNoWs,
    show ¬ p.config.maxChunkLineLength ≤ 0 by omega,
    show ¬ p.config.maxChunkLineLength ≤ 1 by omega, show ¬ p.config.maxChunkLineLength ≤ 2 by omega]

theorem run_encodeChunkedList (p : Parser) (chunks : List (List UInt8))
    (hp : p.phase = .body (.chunked (.line {})))
    (hsize : ∀ c ∈ chunks, c.length < 16 ^ 16)
    (hmax : p.delivered + (chunks.map List.length).sum ≤ p.config.maxBody)
    (hline : 18 ≤ p.config.maxChunkLineLength) :
    (p.run (encodeChunkedList chunks)).1 =
      { p with phase := .done, delivered := p.delivered + (chunks.map List.length).sum } ∧
    obsOf (p.run (encodeChunkedList chunks)).2 = chunks.flatten.map .byte ++ [.done] := by
  induction chunks generalizing p with
  | nil =>
    have := run_lastChunk p hp hline
    simp only [encodeChunkedList, List.filter_nil, List.flatMap_nil, List.nil_append] at this ⊢
    simpa using this
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons] at hmax
    by_cases hc : c = []
    · subst hc
      have := ih p hp (fun c' hc' => hsize c' (by simp [hc'])) (by simpa using hmax) hline
      simpa [encodeChunkedList] using this
    · have h1 := run_encodeChunk p c hp hc (hsize c (by simp)) (by omega) hline
      have h2 := ih { p with delivered := p.delivered + c.length } (by simpa using hp)
        (fun c' hc' => hsize c' (by simp [hc'])) (by simp; omega) (by simpa using hline)
      have hfilter : encodeChunkedList (c :: cs) = encodeChunk c ++ encodeChunkedList cs := by
        simp [encodeChunkedList, hc]
      rw [hfilter, run_append, h1.1]
      refine ⟨?_, ?_⟩
      · rw [h2.1]
        simp [Nat.add_assoc]
      · rw [obsOf_append, h1.2, h2.2]
        simp

/--
**Chunked round trip.**  From the start of a chunked body, feeding the encoding of `chunks` delivers
exactly their concatenation and ends the response.
-/
theorem feed_encodeChunked (p : Parser) (chunks : List ByteArray)
    (hp : p.phase = .body (.chunked (.line {})))
    (hsize : ∀ c ∈ chunks, c.size < 16 ^ 16)
    (hmax : p.delivered + (chunks.map ByteArray.size).sum ≤ p.config.maxBody)
    (hline : 18 ≤ p.config.maxChunkLineLength) :
    (p.feed (encodeChunked chunks)).1.phase = .done ∧
    obsOf (p.feed (encodeChunked chunks)).2 =
      (chunks.flatMap (·.data.toList)).map .byte ++ [.done] := by
  have he := feed_eq_run p (encodeChunked chunks)
  have hl : (chunks.map (·.data.toList)).map List.length = chunks.map ByteArray.size := by
    simp [Function.comp_def]
  have h := run_encodeChunkedList p (chunks.map (·.data.toList)) hp
    (by intro c hc; simp only [List.mem_map] at hc; obtain ⟨a, ha, rfl⟩ := hc; simpa using hsize a ha)
    (by rw [hl]; exact hmax) hline
  have hdata : (encodeChunked chunks).data.toList = encodeChunkedList (chunks.map (·.data.toList)) := by
    simp [encodeChunked]
  rw [hdata] at he
  refine ⟨by rw [he.1, h.1], ?_⟩
  rw [he.2, h.2]
  congr 1

end Parser

/--
**Chunked round trip, for a whole response.**  If some head bytes leave a parser at the start of a
chunked body, then that head followed by the encoding of `chunks`, cut into pieces in any way, is
observed as what the head alone is observed as, then the concatenation of `chunks`, then the end.
-/
theorem roundtrip_chunked (config : Config) (method : Std.Http.Method) (head : ByteArray)
    (chunks : List ByteArray) (pieces : List ByteArray)
    (hpieces : pieces.foldl (· ++ ·) .empty = head ++ encodeChunked chunks)
    (hhead : ((Parser.start config method).feed head).1.phase = .body (.chunked (.line {})))
    (hsize : ∀ c ∈ chunks, c.size < 16 ^ 16)
    (hmax : ((Parser.start config method).feed head).1.delivered + (chunks.map ByteArray.size).sum ≤
      config.maxBody)
    (hline : 18 ≤ config.maxChunkLineLength) :
    ((Parser.start config method).feedAll pieces).1.phase = .done ∧
    obsOf ((Parser.start config method).feedAll pieces).2 =
      obsOf ((Parser.start config method).feed head).2 ++
        (chunks.flatMap (·.data.toList)).map .byte ++ [.done] := by
  have hall := Parser.feedAll_eq (Parser.start config method) pieces
  rw [hpieces] at hall
  have hs := Parser.feed_append (Parser.start config method) head (encodeChunked chunks)
  have hcfg : ((Parser.start config method).feed head).1.config = config := by
    rw [feed_config]; rfl
  have hr := Parser.feed_encodeChunked _ chunks hhead hsize (by rw [hcfg]; exact hmax)
    (by rw [hcfg]; exact hline)
  refine ⟨by rw [hall.1, hs.1, hr.1], ?_⟩
  rw [hall.2, hs.2, hr.2, List.append_assoc]

end LeanHttp.Codec
