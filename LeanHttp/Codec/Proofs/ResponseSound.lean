module

public import LeanHttp.Codec.Proofs.HeadSound
public import LeanHttp.Codec.Proofs.Chunked
public import LeanHttp.Codec.Proofs.Shape

@[expose] public section

/-!
# The response delivered is the response received

If a run reports a response complete, its input is the interim heads, the final head, a body of the
kind the head's framing declares, and then whatever follows; and the body bytes delivered are that
body's payload (`response_sound`):

- no body: nothing;
- `Content-Length: n`: `n` bytes, delivered as they are;
- chunked: chunks, each a chunk-size line announcing its size (hex digits, then extensions without CR
  or LF, then CRLF), that many bytes of data and CRLF; then a size line announcing 0 and a trailer
  section of field lines ending in an empty line; the payload is the concatenation of the chunks'
  data (`ChunkedBody`);
- delimited by the end of input: everything after the head, delivered as it is.

This holds for every encoding the parser accepts, not only for what `encodeChunked` produces.
-/

namespace LeanHttp.Codec

/-! ## Chunk-size lines -/

/--
Hex digits `ds` with value `n`, followed by extension bytes `ext` that contain no CR or LF and do
not start with a hex digit.
-/
def HexExt (ds ext : List UInt8) (n : Nat) : Prop :=
  ds ≠ [] ∧ (∀ d ∈ ds, (hexVal? d).isSome = true) ∧ hexValue 0 ds = n ∧
    (∀ b ∈ ext, b ≠ cr ∧ b ≠ lf) ∧ ∀ e, ext.head? = some e → (hexVal? e).isSome = false

/--
`line` is a chunk-size line announcing `n` bytes: hex digits with value `n`, extensions without CR
or LF, and CRLF.
-/
def SizeLineOf (n : Nat) (line : List UInt8) : Prop :=
  ∃ ds ext, line = ds ++ ext ++ [cr, lf] ∧ HexExt ds ext n

/--
A chunk-size line read so far agrees with its bytes `cur`.
-/
def LineRel (cl : ChunkLine) (cur : List UInt8) : Prop :=
  cl.bytes = cur.length ∧
  match cl.st with
  | .size k => cur.length = k ∧ (∀ d ∈ cur, (hexVal? d).isSome = true) ∧ hexValue 0 cur = cl.size
  | .lf => ∃ ds ext, cur = ds ++ ext ++ [cr] ∧ HexExt ds ext cl.size
  | _ => ∃ ds ext, cur = ds ++ ext ∧ HexExt ds ext cl.size ∧ ext ≠ []

theorem not_crlf_of_isWs {b : UInt8} (h : isWs b = true) : b ≠ cr ∧ b ≠ lf := by
  refine ⟨?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide

theorem not_crlf_of_isTChar {b : UInt8} (h : isTChar b = true) : b ≠ cr ∧ b ≠ lf := by
  refine ⟨?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide

theorem not_crlf_of_isQdText {b : UInt8} (h : isQdText b = true) : b ≠ cr ∧ b ≠ lf := by
  refine ⟨?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide

theorem not_crlf_of_isQuotedPairChar {b : UInt8} (h : isQuotedPairChar b = true) :
    b ≠ cr ∧ b ≠ lf := by
  refine ⟨?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide

theorem not_crlf_of_beq {b c : UInt8} (h : (b == c) = true) (hc : c ≠ cr ∧ c ≠ lf) :
    b ≠ cr ∧ b ≠ lf := by
  simp only [beq_iff_eq] at h
  subst h
  exact hc

theorem hexVal_none_of_isWs {b : UInt8} (h : isWs b = true) : (hexVal? b).isSome = false := by
  simp only [isWs, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

theorem hexValue_snoc (acc : Nat) (ds : List UInt8) (d : UInt8) (v : Nat) (hv : hexVal? d = some v) :
    hexValue acc (ds ++ [d]) = hexValue acc ds * 16 + v := by
  simp [hexValue, List.foldl_append, hv]

/-- What happens to a chunk-size line in an extension state. -/
def ExtState : ChunkLineSt → Prop
  | .size _ | .lf => False
  | _ => True

theorem lineRel_ext {cl : ChunkLine} {cur : List UInt8} (hr : LineRel cl cur) (he : ExtState cl.st) :
    ∃ ds ext, cur = ds ++ ext ∧ HexExt ds ext cl.size ∧ ext ≠ [] := by
  obtain ⟨_, hst⟩ := hr
  revert he hst
  cases cl.st <;> simp [ExtState] <;> exact id

/--
A byte read in an extension state either ends the extensions with CR, or adds a byte that is
neither CR nor LF and stays in an extension state; the size is unchanged.
-/
theorem stepChunkLine_ext {cfg : Config} {cl cl' : ChunkLine} {b : UInt8} (he : ExtState cl.st)
    (hs : stepChunkLine cfg cl b = .more cl') :
    cl'.size = cl.size ∧ cl'.bytes = cl.bytes + 1 ∧
      ((cl'.st = .lf ∧ b = cr) ∨ (ExtState cl'.st ∧ b ≠ cr ∧ b ≠ lf)) := by
  unfold stepChunkLine at hs
  split at hs
  · cases hs
  · dsimp only at hs
    split at hs
    · rename_i n hst
      rw [hst] at he
      exact he.elim
    rotate_left 9
    · rename_i hst
      rw [hst] at he
      exact he.elim
    all_goals
      repeat (first | (unfold owsMore at hs) | (unfold semicolon at hs) | (unfold afterExt at hs) |
        (unfold afterExtNoWs at hs))
      repeat' (split at hs)
      all_goals
        first
          | (cases hs; done)
          | (cases hs
             refine ⟨rfl, rfl, ?_⟩
             first
               | (left; refine ⟨rfl, ?_⟩; simp_all)
               | (right; refine ⟨trivial, ?_, ?_⟩ <;> rintro rfl <;>
                   simp_all [isWs, isTChar, isQdText, isQuotedPairChar, isVChar, cr, lf]))

theorem lineRel_mk_ext {cl : ChunkLine} {cur : List UInt8} (he : ExtState cl.st)
    (hb : cl.bytes = cur.length)
    (h : ∃ ds ext, cur = ds ++ ext ∧ HexExt ds ext cl.size ∧ ext ≠ []) : LineRel cl cur := by
  refine ⟨hb, ?_⟩
  revert he
  cases cl.st <;> simp [ExtState] <;> exact h

theorem hexExt_snoc {ds ext : List UInt8} {n : Nat} {b : UInt8} (h : HexExt ds ext n)
    (hne : ext ≠ []) (hb : b ≠ cr ∧ b ≠ lf) : HexExt ds (ext ++ [b]) n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h4 x hx
    · exact hb
  · intro e he
    apply h5
    cases ext with
    | nil => contradiction
    | cons x xs => simpa using he

/--
A byte that continues a chunk-size line keeps the reader's state in agreement with the line's bytes.
-/
theorem stepChunkLine_more_rel {cfg : Config} {cl cl' : ChunkLine} {b : UInt8} {cur : List UInt8}
    (hr : LineRel cl cur) (hs : stepChunkLine cfg cl b = .more cl') : LineRel cl' (cur ++ [b]) := by
  by_cases he : ExtState cl.st
  · obtain ⟨hsize, hbytes, hcase⟩ := stepChunkLine_ext he hs
    obtain ⟨ds, ext, hcur, hx, hne⟩ := lineRel_ext hr he
    have hb0 := hr.1
    rcases hcase with ⟨hlf, rfl⟩ | ⟨he', hb⟩
    · refine ⟨by simp [hbytes, hb0], ?_⟩
      rw [hlf]
      exact ⟨ds, ext, by simp [hcur], by rw [hsize]; exact hx⟩
    · exact lineRel_mk_ext he' (by simp [hbytes, hb0])
        ⟨ds, ext ++ [b], by simp [hcur], by rw [hsize]; exact hexExt_snoc hx hne hb, by simp⟩
  · obtain ⟨hb0, hst⟩ := hr
    unfold stepChunkLine at hs
    split at hs
    · cases hs
    · dsimp only at hs
      split at hs
      · rename_i n hsz
        simp only [hsz] at hst
        obtain ⟨hlen, hhex, hval⟩ := hst
        split at hs
        · rename_i d hd
          split at hs
          · cases hs
            refine ⟨by simp [hb0], ?_⟩
            simp only
            refine ⟨by simp [hlen], ?_, ?_⟩
            · intro x hx
              simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | rfl
              · exact hhex x hx
              · simp [hd]
            · rw [hexValue_snoc 0 cur b d hd, hval]
          · cases hs
        · rename_i hd
          split at hs
          · cases hs
          · rename_i hn
            simp only [beq_iff_eq] at hn
            have hne : cur ≠ [] := by intro h; subst h; simp at hlen; omega
            have hx0 : HexExt cur [] cl.size := ⟨hne, hhex, hval, by simp, by simp⟩
            unfold afterExt at hs
            split at hs
            · rename_i hw
              unfold owsMore at hs
              split at hs
              · cases hs
                exact lineRel_mk_ext trivial (by simp [hb0])
                  ⟨cur, [b], by simp, ⟨hne, hhex, hval, by simpa using not_crlf_of_isWs hw,
                    by simp [hd]⟩, by simp⟩
              · cases hs
            · unfold afterExtNoWs at hs
              split at hs
              · rename_i hsemi
                unfold semicolon at hs
                split at hs
                · cases hs
                  exact lineRel_mk_ext trivial (by simp [hb0])
                    ⟨cur, [b], by simp, ⟨hne, hhex, hval,
                      by simpa using not_crlf_of_beq hsemi (by decide), by simp [hd]⟩, by simp⟩
                · cases hs
              · split at hs
                · rename_i hcr
                  cases hs
                  simp only [beq_iff_eq] at hcr
                  subst hcr
                  refine ⟨by simp [hb0], ?_⟩
                  simp only
                  exact ⟨cur, [], by simp, hx0⟩
                · cases hs
      all_goals first
        | (rename_i hst'; rw [hst'] at he; simp [ExtState] at he; done)
        | (split at hs <;> cases hs; done)

/--
A chunk-size line that ends announces the size its bytes say.
-/
theorem stepChunkLine_done_rel {cfg : Config} {cl : ChunkLine} {b : UInt8} {cur : List UInt8}
    {n : Nat} (hr : LineRel cl cur) (hs : stepChunkLine cfg cl b = .done n) :
    SizeLineOf n (cur ++ [b]) := by
  obtain ⟨_, hst⟩ := hr
  unfold stepChunkLine at hs
  split at hs
  · cases hs
  · dsimp only at hs
    split at hs
    · split at hs
      · split at hs <;> cases hs
      · split at hs
        · cases hs
        · unfold afterExt at hs
          split at hs
          · unfold owsMore at hs; split at hs <;> cases hs
          · unfold afterExtNoWs at hs
            split at hs
            · unfold semicolon at hs; split at hs <;> cases hs
            · split at hs <;> cases hs
    rotate_left 9
    · rename_i hlf
      simp only [hlf] at hst
      obtain ⟨ds, ext, hcur, hx⟩ := hst
      split at hs
      · rename_i hb
        cases hs
        simp only [beq_iff_eq] at hb
        subst hb
        exact ⟨ds, ext, by simp [hcur], hx⟩
      · cases hs
    all_goals
      repeat (first | (unfold owsMore at hs) | (unfold semicolon at hs) | (unfold afterExt at hs) |
        (unfold afterExtNoWs at hs))
      repeat' (split at hs)
      all_goals cases hs

/-! ## Chunked bodies -/

/--
`bytes` are complete chunks, each a size line, that many bytes of data and CRLF, whose data joined is
`payload`.
-/
inductive Chunks : List UInt8 → List UInt8 → Prop where
  /-- No chunks. -/
  | nil : Chunks [] []
  /-- One more chunk. -/
  | snoc {pre payload line data : List UInt8} :
      Chunks pre payload → SizeLineOf data.length line → data ≠ [] →
      Chunks (pre ++ line ++ data ++ [cr, lf]) (payload ++ data)

/--
A trailer section: field lines, then an empty line.
-/
def TrailersOf (bytes : List UInt8) : Prop :=
  ∃ fields lines, FieldLines fields lines ∧ bytes = lines.flatten ++ [cr, lf]

/--
`bytes` are a whole chunked body carrying `payload`: chunks, a size line announcing 0, and a trailer
section.
-/
def ChunkedBody (bytes payload : List UInt8) : Prop :=
  ∃ pre line trailers, bytes = pre ++ line ++ trailers ∧ Chunks pre payload ∧ SizeLineOf 0 line ∧
    TrailersOf trailers

/--
A chunked body read so far: `zs` are its bytes, `pl` the data delivered, and the decoder's state
agrees with them.
-/
def ChunkRel (c : ChunkState) (zs pl : List UInt8) : Prop :=
  match c with
  | .line cl => ∃ pre cur, zs = pre ++ cur ∧ Chunks pre pl ∧ LineRel cl cur
  | .data r => ∃ pre pl₀ line d, zs = pre ++ line ++ d ∧ Chunks pre pl₀ ∧ pl = pl₀ ++ d ∧
      SizeLineOf (d.length + r) line ∧ 0 < r
  | .dataCR => ∃ pre pl₀ line d, zs = pre ++ line ++ d ∧ Chunks pre pl₀ ∧ pl = pl₀ ++ d ∧
      SizeLineOf d.length line ∧ d ≠ []
  | .dataLF => ∃ pre pl₀ line d, zs = pre ++ line ++ d ++ [cr] ∧ Chunks pre pl₀ ∧ pl = pl₀ ++ d ∧
      SizeLineOf d.length line ∧ d ≠ []
  | .trailer fl _ => ∃ pre line fields lines cur, zs = pre ++ line ++ lines.flatten ++ cur ∧
      Chunks pre pl ∧ SizeLineOf 0 line ∧ FieldLines fields lines ∧ FieldRel fl cur ∧ NameOK fl

theorem lineRel_empty : LineRel {} [] := by
  simp [LineRel, hexValue]

theorem chunkRel_start : ChunkRel (.line {}) [] [] :=
  ⟨[], [], rfl, .nil, lineRel_empty⟩

theorem stepChunk_more_rel {cfg : Config} {room : Nat} {c c' : ChunkState} {b : UInt8}
    {zs pl : List UInt8} (hr : ChunkRel c zs pl) (hs : stepChunk cfg room c b = .more c') :
    ChunkRel c' (zs ++ [b]) pl := by
  unfold stepChunk at hs
  split at hs
  · rename_i cl
    obtain ⟨pre, cur, rfl, hch, hl⟩ := hr
    split at hs
    · rename_i cl' hs2
      cases hs
      exact ⟨pre, cur ++ [b], by simp, hch, stepChunkLine_more_rel hl hs2⟩
    · cases hs
    · rename_i hs2
      cases hs
      exact ⟨pre, cur ++ [b], [], [], [], by simp, hch, stepChunkLine_done_rel hl hs2, .nil,
        fieldRel_empty, nameOK_empty⟩
    · rename_i n hs2
      split at hs
      · cases hs
        exact ⟨pre, pl, cur ++ [b], [], by simp, hch, by simp, by simpa using stepChunkLine_done_rel hl hs2,
          by omega⟩
      · cases hs
  · cases hs
  · split at hs
    · rename_i hb
      cases hs
      simp only [beq_iff_eq] at hb
      subst hb
      obtain ⟨pre, pl₀, line, d, rfl, hch, hpl, hsl, hne⟩ := hr
      exact ⟨pre, pl₀, line, d, by simp, hch, hpl, hsl, hne⟩
    · cases hs
  · split at hs
    · rename_i hb
      cases hs
      simp only [beq_iff_eq] at hb
      subst hb
      obtain ⟨pre, pl₀, line, d, rfl, hch, rfl, hsl, hne⟩ := hr
      exact ⟨pre ++ line ++ d ++ [cr, lf], [], by simp, .snoc hch hsl hne, lineRel_empty⟩
    · cases hs
  · rename_i fl count
    obtain ⟨pre, line, fields, lines, cur, rfl, hch, hsl, hfl, hcur, hnm⟩ := hr
    split at hs
    · rename_i fl' hs2
      cases hs
      exact ⟨pre, line, fields, lines, cur ++ [b], by simp, hch, hsl, hfl, stepFieldLine_more hcur hs2,
        stepFieldLine_more_name hnm hs2⟩
    · cases hs
    · cases hs
    · rename_i name value n hs2
      split at hs
      · cases hs
      · split at hs
        · cases hs
        · cases hs
          obtain ⟨hfo, _⟩ := stepFieldLine_field hcur hnm hs2
          exact ⟨pre, line, fields ++ [{ name, value }], lines ++ [cur ++ [b]], [], by simp, hch, hsl,
            FieldLines.snoc hfl hfo, fieldRel_empty, nameOK_empty⟩

theorem stepChunk_data_rel {cfg : Config} {room : Nat} {c c' : ChunkState} {b : UInt8}
    {zs pl : List UInt8} (hr : ChunkRel c zs pl) (hs : stepChunk cfg room c b = .data c') :
    ChunkRel c' (zs ++ [b]) (pl ++ [b]) := by
  obtain ⟨r, rfl, rfl⟩ := stepChunk_data hs
  obtain ⟨pre, pl₀, line, d, rfl, hch, rfl, hsl, hr0⟩ := hr
  split
  · rename_i hr1
    have : r = 1 := by omega
    subst this
    exact ⟨pre, pl₀, line, d ++ [b], by simp, hch, by simp, by simpa using hsl, by simp⟩
  · rename_i hr1
    refine ⟨pre, pl₀, line, d ++ [b], by simp, hch, by simp, ?_, by omega⟩
    have : (d ++ [b]).length + (r - 1) = d.length + r := by simp; omega
    rw [this]
    exact hsl

theorem stepChunk_ended_rel {cfg : Config} {room : Nat} {c : ChunkState} {b : UInt8}
    {zs pl : List UInt8} (hr : ChunkRel c zs pl) (hs : stepChunk cfg room c b = .ended) :
    ChunkedBody (zs ++ [b]) pl := by
  unfold stepChunk at hs
  split at hs
  · split at hs
    · cases hs
    · cases hs
    · cases hs
    · split at hs <;> cases hs
  · cases hs
  · split at hs <;> cases hs
  · split at hs <;> cases hs
  · obtain ⟨pre, line, fields, lines, cur, rfl, hch, hsl, hfl, hcur, _⟩ := hr
    split at hs
    · cases hs
    · cases hs
    · rename_i hs2
      have hblank := stepFieldLine_blank hcur hs2
      refine ⟨pre, line, lines.flatten ++ [cr, lf], ?_, hch, hsl, fields, lines, hfl, rfl⟩
      simp only [List.append_assoc]
      rw [hblank]
    · split at hs
      · cases hs
      · split at hs <;> cases hs

/-! ## Responses -/

/--
`body` is a body of the kind `framing` declares, carrying `payload`: none, `n` bytes as they are, a
chunked body, or everything (up to the end of input) as it is.
-/
def BodyOf (framing : Framing) (body payload : List UInt8) : Prop :=
  match framing with
  | .none => body = [] ∧ payload = []
  | .length n => body.length = n ∧ payload = body
  | .chunked => ChunkedBody body payload
  | .untilClose => payload = body

/--
How far a body framed by `framing` has got in `phase`, given the bytes `post` after the head, the
body delivered `pl`, and whether bytes arrived after the end (`xtra`, the parser's `extra`).
-/
def BodyProgress (framing : Framing) (phase : Phase) (post pl : List UInt8) (xtra : Bool) : Prop :=
  match phase with
  | .head _ => False
  | .body (.fixed r) => pl = post ∧ framing = .length (post.length + r)
  | .body (.chunked c) => framing = .chunked ∧ ChunkRel c post pl
  | .body (.untilClose _) => framing = .untilClose ∧ pl = post
  | .done => ∃ body extra, post = body ++ extra ∧ BodyOf framing body pl ∧ (extra = [] ↔ xtra = false)
  | .failed _ => True

/--
The response read so far agrees with the bytes `zs` read, given the body delivered `pl`: while heads
are read, the head reader agrees with them and no body was delivered; once the final head arrived,
they are interim heads, that head, and the body so far.
-/
def RespSound (p : Parser) (zs pl : List UInt8) : Prop :=
  (∀ hs, p.phase = .head hs → HeadRel hs zs) ∧
  (p.head = none → pl = []) ∧
  (∀ h, p.head = some h → ∃ pre hb post, zs = pre ++ hb ++ post ∧ InterimHeads pre h.interim ∧
    HeadBytesOf h.http10 h.code h.reason h.fields hb ∧ BodyProgress h.framing p.phase post pl p.extra) ∧
  (p.phase ≠ .done → p.extra = false)

namespace Parser

theorem startBody_respSound {p : Parser} {h : Head} {zs pre hb : List UInt8} (hz : zs = pre ++ hb)
    (hi : InterimHeads pre h.interim) (hhb : HeadBytesOf h.http10 h.code h.reason h.fields hb)
    (hx : p.extra = false) :
    RespSound (p.startBody h).1 zs (bodyBytes (obsOf (p.startBody h).2)) := by
  have hhead : (p.startBody h).1.head = some h := by
    unfold startBody; dsimp only; split <;> (try split) <;> rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold startBody; dsimp only; split <;> (try split) <;> simp
  · rw [hhead]; simp
  rotate_left
  · unfold startBody; dsimp only; split <;> (try split) <;> simp [hx]
  · intro h' hh'
    rw [hhead] at hh'
    cases hh'
    refine ⟨pre, hb, [], by simp [hz], hi, hhb, ?_⟩
    unfold startBody
    dsimp only
    split
    · rename_i hfr
      exact ⟨[], [], rfl, by simp [BodyOf, hfr], by simp [hx]⟩
    · rename_i hfr
      exact ⟨[], [], rfl, by simp [BodyOf, hfr], by simp [hx]⟩
    · rename_i n hfr
      split
      · trivial
      · simp [BodyProgress, hfr]
    · rename_i hfr
      exact ⟨hfr, by simpa using chunkRel_start⟩
    · rename_i hfr
      simp [BodyProgress, hfr]

/--
Every byte keeps the response read so far in agreement with the bytes and the body delivered.
-/
theorem stepByte_respSound {p : Parser} {obs : List Obs} {zs : List UInt8} (b : UInt8)
    (hg : Good p obs) (hs : RespSound p zs (bodyBytes obs)) :
    RespSound (p.stepByte b).1 (zs ++ [b]) (bodyBytes (obs ++ obsOf (p.stepByte b).2)) := by
  have hphase := hg.inv.2
  obtain ⟨hhs, hnone, hsome, hxf⟩ := hs
  unfold stepByte
  split
  · rename_i hst hp
    have hn : p.head = none := by cases hph : p.head <;> simp_all [PhaseOK]
    have hpl := hnone hn
    have hx : p.extra = false := hxf (by simp [hp])
    split
    · rename_i hs' he
      refine ⟨by simpa using stepHead_more_rel (hhs hst hp) he, by simp [hpl], ?_, by simp [hx]⟩
      intro h hh; simp [hn] at hh
    · refine ⟨by simp [fail], by simp [fail, hpl], ?_, by simp [fail, hx]⟩
      intro h hh; simp [fail, hn] at hh
    · rename_i h he
      obtain ⟨pre, hb, hz, hi, hhb⟩ := stepHead_final_rel (hhs hst hp) he
      have := startBody_respSound (p := p) hz hi hhb hx
      simpa [hpl] using this
  · -- Content-Length
    rename_i r hp
    obtain ⟨h, hh⟩ := head_of_body hphase hp
    simp only [hh, hp, PhaseOK] at hphase
    obtain ⟨hr0, _, _⟩ := hphase
    obtain ⟨pre, hb, post, hz, hi, hhb, hprog⟩ := hsome h hh
    simp only [hp, BodyProgress] at hprog
    obtain ⟨hpl, hfr⟩ := hprog
    have hx : p.extra = false := hxf (by simp [hp])
    split
    · have : r = 1 := by omega
      subst this
      refine ⟨by simp, by simp [hh], ?_, by simp⟩
      intro h' hh'
      simp only [hh, Option.some.injEq] at hh'
      subst hh'
      refine ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, post ++ [b], [], by simp, ?_, by simp [hx]⟩
      simp only [BodyOf, hfr]
      simp [hpl]
    · refine ⟨by simp, by simp [hh], ?_, by simp [hx]⟩
      intro h' hh'
      simp only [hh, Option.some.injEq] at hh'
      subst hh'
      refine ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, by simp [hpl], ?_⟩
      rw [hfr]
      congr 1
      simp
      omega
  · -- until close
    rename_i room hp
    obtain ⟨h, hh⟩ := head_of_body hphase hp
    obtain ⟨pre, hb, post, hz, hi, hhb, hprog⟩ := hsome h hh
    simp only [hp, BodyProgress] at hprog
    obtain ⟨hfr, hpl⟩ := hprog
    have hx : p.extra = false := hxf (by simp [hp])
    split
    · refine ⟨by simp [fail], by simp [fail, hh], ?_, by simp [fail, hx]⟩
      intro h' hh'
      simp only [fail, hh, Option.some.injEq] at hh'
      subst hh'
      exact ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, trivial⟩
    · refine ⟨by simp, by simp [hh], ?_, by simp [hx]⟩
      intro h' hh'
      simp only [hh, Option.some.injEq] at hh'
      subst hh'
      exact ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, hfr, by simp [hpl]⟩
  · -- chunked
    rename_i c hp
    obtain ⟨h, hh⟩ := head_of_body hphase hp
    obtain ⟨pre, hb, post, hz, hi, hhb, hprog⟩ := hsome h hh
    simp only [hp, BodyProgress] at hprog
    obtain ⟨hfr, hrel⟩ := hprog
    have hx : p.extra = false := hxf (by simp [hp])
    split
    · rename_i c' hs2
      refine ⟨by simp, by simp [hh], ?_, by simp [hx]⟩
      intro h' hh'
      simp only [hh, Option.some.injEq] at hh'
      subst hh'
      exact ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, hfr, by simpa using stepChunk_more_rel hrel hs2⟩
    · rename_i c' hs2
      refine ⟨by simp, by simp [hh], ?_, by simp [hx]⟩
      intro h' hh'
      simp only [hh, Option.some.injEq] at hh'
      subst hh'
      exact ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, hfr, by simpa using stepChunk_data_rel hrel hs2⟩
    · rename_i hs2
      refine ⟨by simp, by simp [hh], ?_, by simp⟩
      intro h' hh'
      simp only [hh, Option.some.injEq] at hh'
      subst hh'
      refine ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, post ++ [b], [], by simp, ?_, by simp [hx]⟩
      simp only [BodyOf, hfr]
      simpa using stepChunk_ended_rel hrel hs2
    · refine ⟨by simp [fail], by simp [fail, hh], ?_, by simp [fail, hx]⟩
      intro h' hh'
      simp only [fail, hh, Option.some.injEq] at hh'
      subst hh'
      exact ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, trivial⟩
  · -- after the end
    rename_i hp
    refine ⟨by simp [hp], by simpa using hnone, ?_, by simp [hp]⟩
    intro h hh
    obtain ⟨pre, hb, post, hz, hi, hhb, hprog⟩ := hsome h (by simpa using hh)
    simp only [hp, BodyProgress] at hprog
    obtain ⟨body, extra, hpost, hbody, _⟩ := hprog
    refine ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, ?_⟩
    simp only [hp, BodyProgress]
    exact ⟨body, extra ++ [b], by simp [hpost], by simpa using hbody, by simp⟩
  · -- after an error
    rename_i e hp
    refine ⟨by simp [hp], by simpa using hnone, ?_, by simpa [hp] using hxf⟩
    intro h hh
    obtain ⟨pre, hb, post, hz, hi, hhb, _⟩ := hsome h hh
    refine ⟨pre, hb, post ++ [b], by simp [hz], hi, hhb, ?_⟩
    simp [hp, BodyProgress]

theorem run_respSound {p : Parser} {obs : List Obs} {zs : List UInt8} (xs : List UInt8)
    (hg : Good p obs) (hs : RespSound p zs (bodyBytes obs)) :
    RespSound (p.run xs).1 (zs ++ xs) (bodyBytes (obs ++ obsOf (p.run xs).2)) := by
  induction xs generalizing p obs zs with
  | nil => simpa using hs
  | cons b bs ih =>
    have := ih (stepByte_good b hg) (stepByte_respSound b hg hs)
    simpa [run_cons, List.append_assoc] using this

theorem finish_respSound {p : Parser} {obs : List Obs} {zs : List UInt8} (hg : Good p obs)
    (hs : RespSound p zs (bodyBytes obs)) :
    RespSound p.finish.1 zs (bodyBytes (obs ++ obsOf p.finish.2)) := by
  have hphase := hg.inv.2
  obtain ⟨hhs, hnone, hsome, hxf⟩ := hs
  unfold finish
  split
  · rename_i hp
    refine ⟨by simp [hp], by simpa using hnone, ?_, by simp [hp]⟩
    intro h hh
    simpa [hp] using hsome h (by simpa using hh)
  · rename_i e hp
    refine ⟨by simp [hp], by simpa using hnone, ?_, by simpa [hp] using hxf⟩
    intro h hh
    simpa [hp] using hsome h (by simpa using hh)
  · rename_i room hp
    obtain ⟨h, hh⟩ := head_of_body hphase hp
    obtain ⟨pre, hb, post, hz, hi, hhb, hprog⟩ := hsome h hh
    simp only [hp, BodyProgress] at hprog
    obtain ⟨hfr, hpl⟩ := hprog
    have hx : p.extra = false := hxf (by simp [hp])
    refine ⟨by simp, by simp [hh], ?_, by simp⟩
    intro h' hh'
    simp only [hh, Option.some.injEq] at hh'
    subst hh'
    refine ⟨pre, hb, post, hz, hi, hhb, post, [], by simp, ?_, by simp [hx]⟩
    simp only [BodyOf, hfr]
    simpa using hpl
  · rename_i hnd hnf hnu
    refine ⟨by simp [fail], by simpa [fail] using hnone, ?_, by simpa [fail] using hxf hnd⟩
    intro h hh
    obtain ⟨pre, hb, post, hz, hi, hhb, _⟩ := hsome h (by simpa [fail] using hh)
    exact ⟨pre, hb, post, hz, hi, hhb, by simp [fail, BodyProgress]⟩

end Parser

theorem respSound_start (config : Config) (method : Std.Http.Method) :
    RespSound (Parser.start config method) [] (bodyBytes []) :=
  ⟨by
    intro hs hp
    simp only [Parser.start, Phase.head.injEq] at hp
    subst hp
    exact ⟨[], [], rfl, .nil, show StatusRel {} [] from statusRel_empty⟩,
   by simp,
   by simp [Parser.start],
   by simp [Parser.start]⟩

/--
**While a response is read, what was delivered agrees with what was received.**  After feeding
`bytes` to a parser: while heads are read, the head reader agrees with them and no body was
delivered; once the final head `h` arrived, `bytes` are interim heads, `h` itself, and bytes `post`
whose relation to the body delivered is `BodyProgress`: for a `Content-Length` or close-delimited
body the body delivered is `post`, for a chunked body `post` is chunks so far and the body delivered
their data (`ChunkRel`), and for a complete response `post` is the body and any bytes after it.
-/
theorem feed_respSound (config : Config) (method : Std.Http.Method) (bytes : ByteArray) :
    RespSound ((Parser.start config method).feed bytes).1 bytes.data.toList
      (bodyBytes (obsOf ((Parser.start config method).feed bytes).2)) := by
  have := Parser.run_respSound bytes.data.toList (start_good config method) (respSound_start config method)
  rw [← (Parser.feed_eq_run _ bytes).1, ← (Parser.feed_eq_run _ bytes).2] at this
  simpa using this

/--
A response delimited by the end of input is never complete before the end of input.
-/
def NoUCDone (p : Parser) : Prop :=
  ∀ h, p.head = some h → p.phase = .done → h.framing ≠ .untilClose

theorem Parser.stepByte_noUCDone {p : Parser} {obs : List Obs} (b : UInt8) (hg : Good p obs)
    (hn : NoUCDone p) : NoUCDone (p.stepByte b).1 := by
  have hphase := hg.inv.2
  unfold Parser.stepByte
  split
  · split
    · intro h hh hd; simp at hd
    · intro h hh hd; simp [Parser.fail] at hd
    · rename_i h _
      intro h' hh' hd
      unfold Parser.startBody at hh' hd
      dsimp only at hh' hd
      split at hh' <;> (try split at hh') <;> (rename_i hfr; simp at hh' hd; subst hh') <;> simp_all
  · rename_i r hp
    obtain ⟨h, hh⟩ := Parser.head_of_body hphase hp
    simp only [hh, hp, PhaseOK] at hphase
    intro h' hh' _
    split at hh' <;> (rw [hh] at hh'; cases hh'; simp [hphase.2.1])
  · rename_i room hp
    intro h' hh' hd
    split at hd <;> simp [Parser.fail] at hd
  · rename_i c hp
    obtain ⟨h, hh⟩ := Parser.head_of_body hphase hp
    simp only [hh, hp, PhaseOK] at hphase
    intro h' hh' _
    split at hh' <;> (simp only [Parser.fail] at hh'; rw [hh] at hh'; cases hh'; simp [hphase.1])
  · intro h hh hd; exact hn h (by simpa using hh) (by assumption)
  · exact hn

theorem Parser.run_noUCDone {p : Parser} {obs : List Obs} (xs : List UInt8) (hg : Good p obs)
    (hn : NoUCDone p) : NoUCDone (p.run xs).1 := by
  induction xs generalizing p obs with
  | nil => simpa using hn
  | cons b bs ih =>
    have := ih (Parser.stepByte_good b hg) (Parser.stepByte_noUCDone b hg hn)
    simpa [Parser.run_cons] using this

/--
**The response delivered is the response received.**  If feeding `bytes` to a parser, and then
perhaps the end of input, reports the response complete, then `bytes` are `h.interim` interim heads,
the final head `h` received as it is reported (`head_sound`), a body of the kind `h.framing` declares,
and then `extra` bytes; and the body bytes observed are that body's payload (`BodyOf`).  For a
chunked body this is the concatenation of its chunks' data, whatever extensions, trailers and hex
digits it was sent with.  `extra` is empty exactly when the parser noted no bytes after the end
(`Parser.extra`), and always for a body delimited by the end of input, which is everything after the
head.
-/
theorem response_sound (config : Config) (method : Std.Http.Method) (bytes : ByteArray) (eof : Bool)
    (p : Parser) (obs : List Obs)
    (hp : p = if eof then ((Parser.start config method).feed bytes).1.finish.1
      else ((Parser.start config method).feed bytes).1)
    (hobs : obs = if eof then obsOf ((Parser.start config method).feed bytes).2 ++
        obsOf ((Parser.start config method).feed bytes).1.finish.2
      else obsOf ((Parser.start config method).feed bytes).2)
    (hdone : p.phase = .done) :
    ∃ h pre hb body extra, Obs.head h ∈ obs ∧ bytes.data.toList = pre ++ hb ++ body ++ extra ∧
      InterimHeads pre h.interim ∧ HeadBytesOf h.http10 h.code h.reason h.fields hb ∧
      BodyOf h.framing body (bodyBytes obs) ∧ (extra = [] ↔ p.extra = false) ∧
      (h.framing = .untilClose → extra = []) := by
  have hr1 : Reach config method ((Parser.start config method).feed bytes).1
      ([] ++ obsOf ((Parser.start config method).feed bytes).2) := Reach.feed bytes Reach.start
  have hs1 := feed_respSound config method bytes
  have hn1 : NoUCDone ((Parser.start config method).feed bytes).1 := by
    have := Parser.run_noUCDone bytes.data.toList (start_good config method)
      (p := Parser.start config method) (by intro h hh; simp [Parser.start] at hh)
    rw [← (Parser.feed_eq_run _ bytes).1] at this
    exact this
  have key : ∀ q os, Reach config method q os → RespSound q bytes.data.toList (bodyBytes os) →
      q.phase = .done → (∀ h, q.head = some h → h.framing = .untilClose → q.extra = false) →
      ∃ h pre hb body extra, Obs.head h ∈ os ∧
        bytes.data.toList = pre ++ hb ++ body ++ extra ∧ InterimHeads pre h.interim ∧
        HeadBytesOf h.http10 h.code h.reason h.fields hb ∧ BodyOf h.framing body (bodyBytes os) ∧
        (extra = [] ↔ q.extra = false) ∧ (h.framing = .untilClose → extra = []) := by
    intro q os hr hs hd huc
    have hg := hr.good
    have hph := hg.inv.2
    cases hh : q.head with
    | none => simp_all [PhaseOK]
    | some h =>
      obtain ⟨pre, hb, post, hz, hi, hhb, hprog⟩ := hs.2.2.1 h hh
      simp only [hd, BodyProgress] at hprog
      obtain ⟨body, extra, hpost, hbody, hx⟩ := hprog
      exact ⟨h, pre, hb, body, extra, (hg.head h).2 hh, by simp [hz, hpost], hi, hhb, hbody, hx,
        fun hu => hx.2 (huc h hh hu)⟩
  cases eof
  · simp only [Bool.false_eq_true, ite_false] at hp hobs
    subst hp hobs
    have := key _ _ hr1 (by simpa using hs1) hdone
      (fun h hh hu => absurd hu (hn1 h hh hdone))
    simpa using this
  · simp only [ite_true] at hp hobs
    subst hp hobs
    have hr2 := Reach.finish hr1
    have hs2 := Parser.finish_respSound hr1.good (by simpa using hs1)
    -- Before the end of input a close-delimited response was not complete, so the parser noted
    -- no bytes after an end.
    have huc : ∀ h, ((Parser.start config method).feed bytes).1.finish.1.head = some h →
        h.framing = .untilClose → ((Parser.start config method).feed bytes).1.finish.1.extra = false := by
      intro h hh hu
      have hh0 : ((Parser.start config method).feed bytes).1.head = some h := by
        unfold Parser.finish at hh
        split at hh <;> simpa [Parser.fail] using hh
      have hnd : ((Parser.start config method).feed bytes).1.phase ≠ .done :=
        fun hd0 => hn1 h hh0 hd0 hu
      have hx0 := hs1.2.2.2 hnd
      unfold Parser.finish
      split <;> simp_all [Parser.fail]
    simpa using key _ _ hr2 hs2 hdone huc

end LeanHttp.Codec
