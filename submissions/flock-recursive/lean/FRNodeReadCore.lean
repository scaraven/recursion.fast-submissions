-- G6: this module also holds the former modules `FRNodeRead`, `FRNodeReadW` (one section each, in import order).
import FRFormat
import RecursionFast.Library.Words
import FRVIRCompile

section G6_FRNodeRead

-- New for `flock-recursive` (BLUEPRINT §4.3 `node_sound`, §6.2 step 5, A.5, A.7; stage S-H2,
-- track L-ext, S-H2k).

/-!
# The node witness read off the committed witness: `FR.readSigned`

BLUEPRINT §4.3 states `node_sound` with `p_σ := FR.readSigned σ z` and §6.2 step 5 has the
extractor output `witWords (.node c₁ c₂ p₁ p₂)` read from `f⁽⁰⁾`'s stream and L cells. Here `w`
is the committed witness in A.7's element view (`w e = f[e]`, an `F` element whose 16 bytes are
bits `[128e, 128e + 128)` of `z`): `z = unpack f⁽⁰⁾` and `f⁽⁰⁾ = pack z`, so a reader of `z` is a
reader of `w` (`readSigned σ (pack z)`).

* **The stream of slot `σ ∈ {1, 2}`** (A.7, §1.2): stream element `e` (16 bytes) is message slot
  `4 + e mod 4` of H block `(σ − 1)·chainLen + ⌊e/4⌋`, i.e. cell `streamCell σ e`; slot 1's seed
  payload element `e` is `Node.seedCell 0 e = streamCell 1 (1 + e)` (the A.7 formula). Its words
  (`streamWord`): word `u` is coefficient `c_{u mod 2}` of element `⌊u/2⌋` (A.7: `c₀` = bytes
  `0…7`, `c₁` = bytes `8…15`, little-endian). The stream is `streamBytes = 1,481,344` bytes
  (`stream`), the length of `0x54 ‖ traceBytes tr` for a trace of the item sequence.
* **The trace** (`readTrace`): the item sequence's shape, read at fixed offsets. Item `k` is
  `enc64 |q| ‖ q ‖ a` at stream offset `streamOff k`, with `|q| = items[k].qlen`
  (`FRTranscriptDefs.Item.qlen`): the query is the `qlen` bytes after the length word, the
  answer the next 32. The length word itself is not read: the circuit asserts it is
  `enc64 qlen` (§4.3 (2)), and with it the stream is `0x54 ‖ traceBytes (readTrace w σ)`
  (`readTrace_of_stream`, the positive control).
* **The signature** (`readSig`, A.7's L region): slot `σ`'s 299 `sig` elements at
  `lBase·128 + (σ − 1)·2^14`: `idx` (coefficient `c₀` of element 0), the 133 chain values, then
  the 16 path digests, a digest being two elements (`digestOf`: bytes `0…15`, then `16…31`, as
  `Node.halves`).
* **The child statement** (`readStmt`): slot `σ`'s seed payload elements 2–3 (`c` in
  `"FRSEED0" ‖ vk ‖ c ‖ hdr`, `PubCells`' `cᵢ`).
* **`readSigned σ w := ⟨reassemble tr, tr, readSig w σ⟩`** with `tr := readTrace w σ` (A.5:
  the child's proof is the one its trace carries), and **`readWit w := .node c₁ c₂ p₁ p₂`**.

The constants `lBase = 47,616` (blocks) and `chainLen = 23,146` are `FRNodeLayout.lBase` and
`chainN`; this module does not import `FRNodeLayout` (it pulls in the verifier's compiler), so
the extractor's modules do not depend on it.
-/

namespace FR
namespace Read

open RecursionFast

/-! ## Specification -/

/-- L's base block (A.7, revision 3.12; `FRNodeLayout.lBase`). -/
def lBlk : ℕ := 47616

/-- **The cell of stream element `e` of slot `σ`** (`σ ∈ {1, 2}`): message slot `4 + e mod 4` of
H block `(σ − 1)·chainLen + ⌊e/4⌋` (A.7). -/
def streamCell (σ e : ℕ) : ℕ := ((σ - 1) * chainLen + e / 4) * 128 + 4 + e % 4

/-- The two coefficient words of an `F` element (`c₀`, `c₁`). -/
def elemWords (a : F) : List Word := [a.c₀.val.toBitVec, a.c₁.val.toBitVec]

/-- **Stream word `u` of slot `σ`**: coefficient `c_{u mod 2}` of element `⌊u/2⌋`. -/
def streamWord (w : ℕ → F) (σ u : ℕ) : Word :=
  (elemWords (w (streamCell σ (u / 2)))).getD (u % 2) 0

/-- The words of slot `σ`'s stream (`streamBytes / 8 = 185,168`). -/
def streamWords (w : ℕ → F) (σ : ℕ) : List Word :=
  (List.range (streamBytes / 8)).map (streamWord w σ)

/-- **The bytes of slot `σ`'s stream**, eight little-endian bytes per word. -/
def stream (w : ℕ → F) (σ : ℕ) : List UInt8 := wordsBytes (streamWords w σ)

/-- The trace entry of an item at stream offset `o`: the `qlen` bytes after the length word,
then the 32-byte answer. -/
def entryAt (B : List UInt8) (o : ℕ) (it : Item) : ByteArray × Digest :=
  (⟨((B.drop (o + 8)).take it.qlen).toArray⟩, Vector.ofFn fun i : Fin 32 => B.getD (o + 8 + it.qlen + i) 0)

/-- The entries of the items `its` from stream offset `o` on. -/
def readItems (B : List UInt8) : ℕ → List Item → Trace
  | _, [] => []
  | o, it :: its => entryAt B o it :: readItems B (o + it.slen) its

/-- **Slot `σ`'s trace**: the item sequence read from the stream, item `k` at `streamOff k`. -/
def readTrace (w : ℕ → F) (σ : ℕ) : Trace := readItems (stream w σ) 1 items

/-- The digest whose 32 bytes are those of the words `ws` (four words). -/
def digestW (ws : List Word) : Digest := Vector.ofFn fun i : Fin 32 => (wordsBytes ws).getD i 0

/-- **The digest of two elements** `w e₀ ‖ w e₁` (bytes `0…15`, `16…31`). -/
def digestOf (w : ℕ → F) (e₀ e₁ : ℕ) : Digest := digestW (elemWords (w e₀) ++ elemWords (w e₁))

/-- Element `k` of slot `σ`'s L region (stride `2^14`, A.7). -/
def lCell (σ k : ℕ) : ℕ := lBlk * 128 + (σ - 1) * 2 ^ 14 + k

/-- **Slot `σ`'s signature** (A.7's `sig`: `idx` 1, `ots` 133 × 2, `path` 16 × 2 elements). -/
def readSig (w : ℕ → F) (σ : ℕ) : Sig where
  idx := (w (lCell σ 0)).c₀.val.toNat
  ots := (List.range wotsLen).map fun j => digestOf w (lCell σ (1 + 2 * j)) (lCell σ (2 + 2 * j))
  path := (List.range sigHeight).map fun t =>
    digestOf w (lCell σ (1 + 2 * wotsLen + 2 * t)) (lCell σ (2 + 2 * wotsLen + 2 * t))

/-- **Slot `σ`'s child statement**: seed payload elements 2–3 (stream elements 3–4). -/
def readStmt (w : ℕ → F) (σ : ℕ) : Digest := digestOf w (streamCell σ 3) (streamCell σ 4)

end Read

open Read in
/-- **Slot `σ`'s signed child proof** (§4.3): the proof its trace carries (A.5), the trace, the
signature. -/
def readSigned (σ : ℕ) (w : ℕ → F) : RecursionFast.Signed :=
  ⟨reassemble (readTrace w σ), readTrace w σ, readSig w σ⟩

open Read in
/-- **The node witness** of a committed witness: both children's statements and signed proofs. -/
def readWit (w : ℕ → F) : RecursionFast.Wit :=
  .node (readStmt w 1) (readStmt w 2) (readSigned 1 w) (readSigned 2 w)

namespace Read

open RecursionFast

/-! ## Load-bearing lemmas -/

theorem readItems_length (B : List UInt8) : ∀ (o : ℕ) (its : List Item),
    (readItems B o its).length = its.length
  | _, [] => rfl
  | o, _ :: its => by simp [readItems, readItems_length B _ its]

theorem readTrace_length (w : ℕ → F) (σ : ℕ) : (readTrace w σ).length = 8891 := by
  rw [readTrace, readItems_length, items_length]

theorem streamWords_length (w : ℕ → F) (σ : ℕ) : (streamWords w σ).length = 185168 := by
  simp [streamWords, streamBytes_eq]

theorem stream_length (w : ℕ → F) (σ : ℕ) : (stream w σ).length = streamBytes := by
  rw [stream, wordsBytes_length, streamWords_length, streamBytes_eq]

/-- The entry an item reads off `pre ‖ enc64 |q| ‖ q ‖ a ‖ post` at `|pre|` is `(q, a)`. -/
theorem entryAt_of (pre post : List UInt8) (e : ByteArray × Digest) (it : Item)
    (hq : e.1.size = it.qlen) :
    entryAt (pre ++ (enc64 e.1.size ++ e.1.data.toList ++ e.2.toList) ++ post) pre.length it = e := by
  obtain ⟨q, a⟩ := e
  have hl : q.data.toList.length = it.qlen := by simpa using hq
  have hE : (enc64 q.size).length = 8 := enc64_length _
  simp only at hq ⊢
  have e1 : pre ++ (enc64 q.size ++ q.data.toList ++ a.toList) ++ post =
      (pre ++ enc64 q.size) ++ (q.data.toList ++ (a.toList ++ post)) := by simp
  have e2 : pre ++ (enc64 q.size ++ q.data.toList ++ a.toList) ++ post =
      (pre ++ enc64 q.size ++ q.data.toList) ++ (a.toList ++ post) := by simp
  refine Prod.ext ?_ ?_
  · rw [e1]; simp only [entryAt]
    rw [List.drop_left' (by simp [hE]), List.take_left' hl]
  · rw [e2]; simp only [entryAt]
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_ofFn]
    rw [show pre.length + 8 + it.qlen + i = (pre ++ enc64 q.size ++ q.data.toList).length + i by
      simp [hE, hl]; omega]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simpa using hi)]
    simp [hi]

theorem traceBytes_cons' (e : ByteArray × Digest) (tr : Trace) :
    traceBytes (e :: tr) = (enc64 e.1.size ++ e.1.data.toList ++ e.2.toList) ++ traceBytes tr := by
  simp [traceBytes]

/-- **The trace reader inverts the stream** (the positive control): on `pre ‖ traceBytes tr ‖
post` with `tr` of the items' shape, the reader returns `tr`. -/
theorem readItems_traceBytes : ∀ (its : List Item) (tr : Trace) (pre post : List UInt8),
    tr.map (fun e => e.1.size) = its.map Item.qlen →
    readItems (pre ++ traceBytes tr ++ post) pre.length its = tr
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | it :: its, e :: tr, pre, post, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have he := entryAt_of pre (traceBytes tr ++ post) e it h.1
    have hl : pre.length + it.slen =
        (pre ++ (enc64 e.1.size ++ e.1.data.toList ++ e.2.toList)).length := by
      simp [Item.slen, enc64_length, h.1]; omega
    have ih := readItems_traceBytes its tr (pre ++ (enc64 e.1.size ++ e.1.data.toList ++ e.2.toList))
      post h.2
    rw [traceBytes_cons', readItems, hl]
    simp only [List.append_assoc] at he ih ⊢
    rw [he, ih]

/-- **`readTrace` reads the hashed stream**: when slot `σ`'s stream is `0x54 ‖ traceBytes tr`
for a trace of the item sequence's shape, `readTrace w σ = tr`. -/
theorem readTrace_of_stream (w : ℕ → F) (σ : ℕ) (tr : Trace)
    (hsh : tr.map (fun e => e.1.size) = items.map Item.qlen)
    (hs : stream w σ = tagTrace :: traceBytes tr) : readTrace w σ = tr := by
  rw [readTrace, hs, show tagTrace :: traceBytes tr = [tagTrace] ++ traceBytes tr ++ [] by simp]
  exact readItems_traceBytes items tr [tagTrace] [] hsh

/-- Byte `p` of the stream is byte `p mod 8` of word `⌊p/8⌋`. -/
theorem stream_getD (w : ℕ → F) (σ p : ℕ) (hp : p < streamBytes) :
    (stream w σ).getD p 0 = ((streamWord w σ (p / 8)).toNat / 256 ^ (p % 8)).toUInt8 := by
  have h8 : p / 8 < streamBytes / 8 := by rw [streamBytes_eq] at hp ⊢; omega
  rw [stream, ← wordByte_eq_getD, wordByte, streamWords,
    List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact h8),
    List.getElem_map, List.getElem_range]

/-! ## Controls -/

/-- **The stream cells are A.7's**: slot 1's seed payload element `e` is stream element `1 + e`
(`Node.seedCell 0 e`'s formula), slot 2's starts `chainLen` blocks later. -/
theorem streamCell_seed (e : ℕ) :
    streamCell 1 (1 + e) = (0 * chainLen + (1 + e) / 4) * 128 + 4 + (1 + e) % 4 ∧
    streamCell 2 (1 + e) = (1 * chainLen + (1 + e) / 4) * 128 + 4 + (1 + e) % 4 := by
  simp only [streamCell, Nat.sub_self]; exact ⟨trivial, trivial⟩

/-- The all-zero witness. -/
def w0 : ℕ → F := fun _ => ⟨⟨0⟩, ⟨0⟩⟩

/-- The witness with the element `a` at cell `e` and zeros elsewhere. -/
def w1 (e : ℕ) (a : F) : ℕ → F := fun i => if i = e then a else ⟨⟨0⟩, ⟨0⟩⟩

/-- **`readSig` reads `idx` from `c₀` of slot `σ`'s first L cell** (positive: `idx = 5` from
`c₀ = 5`), **not from `c₁`** and **not from the other slot** (negative). -/
theorem readSig_idx_ctl :
    (readSig (w1 (lCell 1 0) ⟨⟨5⟩, ⟨0⟩⟩) 1).idx = 5 ∧
    (readSig (w1 (lCell 1 0) ⟨⟨0⟩, ⟨5⟩⟩) 1).idx = 0 ∧
    (readSig (w1 (lCell 1 0) ⟨⟨5⟩, ⟨0⟩⟩) 2).idx = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [readSig, w1, lCell, lBlk]

/-- **`readStmt` reads slot `σ`'s seed payload elements 2–3** (positive: byte 0 of `c₁` is
`c₀`'s low byte of stream element 3; negative: element 2, `vk`'s high half, is not read). -/
theorem readStmt_ctl :
    (readStmt (w1 (streamCell 1 3) ⟨⟨7⟩, ⟨0⟩⟩) 1)[0] = 7 ∧
    readStmt (w1 (streamCell 1 2) ⟨⟨7⟩, ⟨0⟩⟩) 1 = readStmt w0 1 := by
  constructor
  · simp [readStmt, digestOf, digestW, w1, elemWords, wordsBytes, wordBytes, enc64]
  · simp only [readStmt, digestOf, w1, w0, streamCell, chainLen_eq]; rfl

end Read
end FR

end G6_FRNodeRead

section G6_FRNodeReadW

-- New for `flock-recursive` (BLUEPRINT A.5, §6.2 step 5, §6.5 `output_spec`; stage S-H2,
-- track L-ext, S-H2k).

/-!
# `reassemble` field by field

`FRFormat.reassemble` walks the phase table with a state of 18 growing fields. For the
extractor's output program the proof's bytes are wanted in the serialised order, field by field.
**`reassemble_eq`**: the bytes of `reassemble tr` are, for `f = 0 … 17` in turn, the
contributions to field `f` of the phases in order (`ctbs`): each phase's contribution `ctb` is
read off its items at the item index the walk has reached (`ix`), with the position answers of
the last `P2` phase (`ans`).
-/

namespace FR.Read

open RecursionFast

/-! ## Specification: a phase's contribution to a field -/

/-- The bytes of a byte array. -/
abbrev bl (b : ByteArray) : List UInt8 := b.data.toList

/-- **Phase `sh`'s bytes for field `f`**, its items starting at item `ix`, with the position
answers `ans` (A.5; `rsPhase` field by field). -/
def ctb (k : Kind) (a : Array (ByteArray × Digest)) (ix : ℕ) (ans : List Digest) :
    Shape → ℕ → List UInt8
  | .seed, f => if f = fHdr then bl (qBytes a ix 71 48) else []
  | .absorb g len, f => if f = g then bl (qBytes a ix 40 len) else []
  | .squeezes _ _, _ => []
  | .uni g, f => if f = g then bl (qBytes a ix 40 uniBytes) else []
  | .rounds g n _ inK _, f =>
    if f = g then (List.range n).flatMap fun j => bl (qBytes a (ix + 2 * j) 40 (roundBytes inK))
    else []
  | .queries i, f =>
    if f = fCols then (List.range (lvlStar i).t).flatMap fun p =>
      bl (qBytes a (ix + (1 + (lvlStar i).sib) * p) 8 (colBytes i))
    else if f = fSibs then (List.range (lvlStar i).t).flatMap fun p =>
      (List.range (lvlStar i).sib).flatMap fun h =>
        bl (sibling k i h (posOf k i ans p)
          ((a.getD (ix + (1 + (lvlStar i).sib) * p + 1 + h) (ByteArray.empty, 0)).1))
    else []

/-- The position answers after phase `sh` (a `P2` phase's squeeze answers, else unchanged). -/
def ansOf (a : Array (ByteArray × Digest)) (ix : ℕ) (ans : List Digest) : Shape → List Digest
  | .squeezes n (.pos _) => (List.range n).map fun j => (a.getD (ix + j) (ByteArray.empty, 0)).2
  | _ => ans

/-- **The phases' bytes for field `f`**, from item `ix` with the answers `ans`. -/
def ctbs (k : Kind) (a : Array (ByteArray × Digest)) : ℕ → List Digest → List Shape → ℕ → List UInt8
  | _, _, [], _ => []
  | ix, ans, sh :: shs, f =>
    ctb k a ix ans sh f ++ ctbs k a (ix + sh.items.length) (ansOf a ix ans sh) shs f

/-- The fields a phase writes are fields of the proof. -/
def FieldsOk : Shape → Prop
  | .absorb g _ => g < nFields
  | .uni g => g < nFields
  | .rounds g _ _ _ _ => g < nFields
  | _ => True

/-! ## Proof helpers: the walk's state -/

/-- Field `f`'s bytes so far. -/
def cont (s : RSt) (f : ℕ) : List UInt8 := bl (s.out.getD f ByteArray.empty)

theorem cont_put (s : RSt) {g : ℕ} (hg : g < s.out.size) (b : ByteArray) (f : ℕ) :
    cont (s.put g b) f = cont s f ++ if f = g then bl b else [] := by
  simp only [cont, RSt.put, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hf : f = g
  · subst hf; simp [hg]
  · simp [Ne.symm hf, hf]

/-- A walk step that appends `C ix ans p f` to every field `f` and keeps the rest. -/
def Appends (body : RSt → ℕ → RSt) (C : ℕ → List Digest → ℕ → ℕ → List UInt8) : Prop :=
  ∀ s p, s.out.size = nFields → (body s p).out.size = nFields ∧ (body s p).ix = s.ix ∧
    (body s p).ans = s.ans ∧ ∀ f, cont (body s p) f = cont s f ++ C s.ix s.ans p f

theorem foldl_appends {body : RSt → ℕ → RSt} {C : ℕ → List Digest → ℕ → ℕ → List UInt8}
    (h : Appends body C) : ∀ (l : List ℕ) (s : RSt), s.out.size = nFields →
    (l.foldl body s).out.size = nFields ∧ (l.foldl body s).ix = s.ix ∧
      (l.foldl body s).ans = s.ans ∧
      ∀ f, cont (l.foldl body s) f = cont s f ++ l.flatMap fun p => C s.ix s.ans p f
  | [], s, hs => ⟨hs, rfl, rfl, fun f => by simp⟩
  | p :: l, s, hs => by
    obtain ⟨h1, h2, h3, h4⟩ := h s p hs
    obtain ⟨g1, g2, g3, g4⟩ := foldl_appends h l (body s p) h1
    refine ⟨g1, g2.trans h2, g3.trans h3, fun f => ?_⟩
    rw [List.foldl_cons, g4, h4, h2, h3, List.flatMap_cons, List.append_assoc]

theorem appends_put (g : ℕ) (hg : g < nFields) (Q : ℕ → List Digest → ℕ → ByteArray) :
    Appends (fun s p => s.put g (Q s.ix s.ans p)) fun ix ans p f => if f = g then bl (Q ix ans p) else [] :=
  fun s p hs => ⟨by simp [RSt.put, hs], rfl, rfl, fun f => cont_put s (hs ▸ hg) _ f⟩

theorem flatMap_ite {α : Type} (l : List α) (c : Prop) [Decidable c] (F : α → List UInt8) :
    (l.flatMap fun x => if c then F x else []) = if c then l.flatMap F else [] := by
  split_ifs <;> simp

/-- **One phase of the walk** appends `ctb` to every field. -/
theorem rsPhase_spec (k : Kind) (a : Array (ByteArray × Digest)) (s : RSt) (sh : Shape)
    (hs : s.out.size = nFields) (hok : FieldsOk sh) :
    (rsPhase k a s sh).out.size = nFields ∧ (rsPhase k a s sh).ix = s.ix + sh.items.length ∧
      (rsPhase k a s sh).ans = ansOf a s.ix s.ans sh ∧
      ∀ f, cont (rsPhase k a s sh) f = cont s f ++ ctb k a s.ix s.ans sh f := by
  have hF : fHdr < s.out.size := by rw [hs]; decide
  cases sh with
  | seed => exact ⟨by simp [rsPhase, RSt.put, hs], by simp [rsPhase, RSt.put, Shape.items],
      rfl, fun f => cont_put s hF _ f⟩
  | absorb g len => exact ⟨by simp [rsPhase, RSt.put, hs], by simp [rsPhase, RSt.put, Shape.items],
      rfl, fun f => cont_put s (hs ▸ hok) _ f⟩
  | squeezes n ch =>
    refine ⟨by cases ch <;> simp [rsPhase, hs], by cases ch <;> simp [rsPhase, Shape.items],
      by cases ch <;> simp [rsPhase, ansOf], fun f => by cases ch <;> simp [rsPhase, cont, ctb]⟩
  | uni g => exact ⟨by simp [rsPhase, RSt.put, hs], by simp [rsPhase, RSt.put, Shape.items],
      rfl, fun f => cont_put s (hs ▸ hok) _ f⟩
  | rounds g n deg inK real =>
    obtain ⟨g1, g2, g3, g4⟩ := foldl_appends (appends_put g hok
      fun ix _ j => qBytes a (ix + 2 * j) 40 (roundBytes inK)) (List.range n) s hs
    refine ⟨g1, by simp [rsPhase, Shape.items]; omega, g3, fun f => ?_⟩
    simp only [rsPhase, cont] at g4 ⊢
    rw [g4, ctb, flatMap_ite]
  | queries i =>
    -- the inner walk over the Merkle-node queries of one position
    have hin : ∀ (j base : ℕ), Appends (fun s h => s.put fSibs (sibling k i h j
        ((a.getD (base + 1 + h) (ByteArray.empty, 0)).1))) fun _ _ h f =>
          if f = fSibs then bl (sibling k i h j ((a.getD (base + 1 + h) (ByteArray.empty, 0)).1))
          else [] := fun j base =>
      appends_put fSibs (by decide) fun _ _ h => sibling k i h j ((a.getD (base + 1 + h) (ByteArray.empty, 0)).1)
    have hout : Appends (fun s p =>
        (List.range (lvlStar i).sib).foldl (fun s' h => s'.put fSibs (sibling k i h
          (posOf k i s.ans p) ((a.getD (s.ix + (1 + (lvlStar i).sib) * p + 1 + h)
            (ByteArray.empty, 0)).1)))
          (s.put fCols (qBytes a (s.ix + (1 + (lvlStar i).sib) * p) 8 (colBytes i))))
        fun ix ans p f =>
          (if f = fCols then bl (qBytes a (ix + (1 + (lvlStar i).sib) * p) 8 (colBytes i)) else []) ++
          (List.range (lvlStar i).sib).flatMap fun h =>
            if f = fSibs then bl (sibling k i h (posOf k i ans p)
              ((a.getD (ix + (1 + (lvlStar i).sib) * p + 1 + h) (ByteArray.empty, 0)).1)) else [] := by
      intro s p hs
      obtain ⟨h1, h2, h3, h4⟩ := appends_put fCols (by decide)
        (fun ix _ p => qBytes a (ix + (1 + (lvlStar i).sib) * p) 8 (colBytes i)) s p hs
      obtain ⟨g1, g2, g3, g4⟩ := foldl_appends (hin (posOf k i s.ans p)
        (s.ix + (1 + (lvlStar i).sib) * p)) (List.range (lvlStar i).sib) _ h1
      refine ⟨g1, g2.trans h2, g3.trans h3, fun f => ?_⟩
      rw [g4, h4, List.append_assoc]
    obtain ⟨g1, g2, g3, g4⟩ := foldl_appends hout (List.range (lvlStar i).t) s hs
    refine ⟨g1, by simp [rsPhase, Shape.items, posItems, Nat.mul_comm]; left; omega, g3, fun f => ?_⟩
    simp only [rsPhase, cont] at g4 ⊢
    rw [g4, ctb]
    congr 1
    by_cases hc : f = fCols
    · subst hc
      have e : ∀ l : List ℕ, l.flatMap (fun _ => ([] : List UInt8)) = [] := fun l => by
        induction l <;> simp_all
      simp [fCols, fSibs, e]
    · by_cases hd : f = fSibs
      · subst hd; simp [fCols, fSibs]
      · simp [hc, hd]

/-- **The walk over shapes** appends `ctbs` to every field. -/
theorem foldl_rsPhase (k : Kind) (a : Array (ByteArray × Digest)) : ∀ (shs : List Shape) (s : RSt),
    s.out.size = nFields → (∀ sh ∈ shs, FieldsOk sh) →
    (shs.foldl (rsPhase k a) s).out.size = nFields ∧
      ∀ f, cont (shs.foldl (rsPhase k a) s) f = cont s f ++ ctbs k a s.ix s.ans shs f
  | [], s, hs, _ => ⟨hs, fun f => by simp [ctbs]⟩
  | sh :: shs, s, hs, hok => by
    obtain ⟨h1, h2, h3, h4⟩ := rsPhase_spec k a s sh hs (hok sh (by simp))
    obtain ⟨g1, g4⟩ := foldl_rsPhase k a shs _ h1 fun x hx => hok x (by simp [hx])
    refine ⟨g1, fun f => ?_⟩
    rw [List.foldl_cons, g4, h4, h2, h3, ctbs, List.append_assoc]

/-- The field a phase names (`0` for the others). -/
def fieldOf : Shape → ℕ
  | .absorb g _ => g
  | .uni g => g
  | .rounds g _ _ _ _ => g
  | _ => 0

theorem phases_fieldsOk : ∀ sh ∈ phases.map Phase.shape, FieldsOk sh := by
  have h : ((phases.map Phase.shape).map fieldOf).all (· < nFields) = true := by decide +kernel
  intro sh hsh
  have := of_decide_eq_true (List.all_eq_true.1 h (fieldOf sh) (List.mem_map_of_mem hsh))
  clear h hsh
  cases sh <;> first | exact this | trivial

theorem flatMap_getD_range (l : List ByteArray) :
    (l.flatMap bl) = (List.range l.length).flatMap fun f => bl (l.getD f ByteArray.empty) := by
  conv_lhs => rw [show l = (List.range l.length).map (fun f => l.getD f ByteArray.empty) from
    List.ext_getElem (by simp) fun i h1 h2 => by simp [List.getElem?_eq_getElem h1]]
  rw [List.flatMap_map]

/-! ## Load-bearing lemma -/

/-- **`reassemble` field by field** (A.5): its bytes are, for each field `f < 18` in order, the
phases' contributions to `f` (`ctbs` from item `0`, no answers yet). -/
theorem reassemble_eq (tr : Trace) :
    bl (reassemble tr) = (List.range nFields).flatMap
      (ctbs (traceKind tr.toArray) tr.toArray 0 [] (phases.map Phase.shape)) := by
  have hs : (⟨Array.replicate nFields ByteArray.empty, 0, []⟩ : RSt).out.size = nFields := by simp
  have e : reassemble tr = serialise ((phases.map Phase.shape).foldl
      (rsPhase (traceKind tr.toArray) tr.toArray) ⟨Array.replicate nFields ByteArray.empty, 0, []⟩).out.toList := by
    rw [List.foldl_map]; rfl
  obtain ⟨g1, g4⟩ := foldl_rsPhase (traceKind tr.toArray) tr.toArray (phases.map Phase.shape) _ hs
    phases_fieldsOk
  rw [e]
  generalize (phases.map Phase.shape).foldl (rsPhase (traceKind tr.toArray) tr.toArray)
    ⟨Array.replicate nFields ByteArray.empty, 0, []⟩ = s at g1 g4
  have hser : bl (serialise s.out.toList) = s.out.toList.flatMap bl := by simp [serialise, bl]
  rw [hser, flatMap_getD_range, Array.length_toList, g1]
  refine List.flatMap_congr fun f hf => ?_
  have h4 := g4 f
  have h0 : cont ⟨Array.replicate nFields ByteArray.empty, 0, []⟩ f = [] := by
    simp only [cont, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split_ifs <;> rfl
  rw [h0, List.nil_append] at h4
  rw [← h4, cont, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-! ## The trace's entries on the stream -/

theorem readItems_getElem (B : List UInt8) : ∀ (its : List Item) (o j : ℕ) (hj : j < its.length),
    (readItems B o its)[j]'(by rw [readItems_length]; exact hj) =
      entryAt B (o + ((its.take j).map Item.slen).sum) its[j]
  | [], _, _, hj => absurd hj (by simp)
  | it :: its, o, 0, _ => by simp [readItems]
  | it :: its, o, j + 1, hj => by
    simp only [readItems, List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
    rw [readItems_getElem B its _ j (by simpa using hj), Nat.add_assoc]

/-- **Entry `j` of slot `σ`'s trace** is item `j` read at its stream offset `streamOff j`. -/
theorem readTrace_getD (w : ℕ → F) (σ j : ℕ) (hj : j < items.length) :
    (readTrace w σ).toArray.getD j (ByteArray.empty, 0) = entryAt (stream w σ) (streamOff j) items[j] := by
  have hl : j < (readTrace w σ).length := by rw [readTrace, readItems_length]; exact hj
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hl,
    Option.getD_some]
  show (readItems (stream w σ) 1 items)[j]'(by rw [readItems_length]; exact hj) = _
  rw [readItems_getElem _ _ _ _ hj]; rfl

/-- **A query slice is a stream slice**: bytes `[off, off + n)` of item `j`'s query are stream
bytes `[streamOff j + 8 + off, … + n)` (inside the query). -/
theorem qBytes_readTrace (w : ℕ → F) (σ j off n : ℕ) (hj : j < items.length)
    (hn : off + n ≤ items[j].qlen) :
    bl (qBytes (readTrace w σ).toArray j off n) = ((stream w σ).drop (streamOff j + 8 + off)).take n := by
  rw [qBytes, readTrace_getD w σ j hj, entryAt, bl, toList_extract]
  simp only [List.toList_toArray, Nat.add_sub_cancel_left, List.drop_take, List.take_take,
    List.drop_drop]
  rw [Nat.min_eq_left (by omega)]

/-! ## Words -/

theorem wordsBytes_drop : ∀ (W : List Word) (u : ℕ), (wordsBytes W).drop (8 * u) = wordsBytes (W.drop u)
  | [], _ => by simp [wordsBytes]
  | _ :: _, 0 => rfl
  | x :: W, u + 1 => by
    rw [show wordsBytes (x :: W) = wordBytes x ++ wordsBytes W from rfl, Nat.mul_succ,
      Nat.add_comm, ← List.drop_drop, List.drop_left' (wordBytes_length x), List.drop_succ_cons,
      wordsBytes_drop W u]

theorem wordsBytes_take : ∀ (W : List Word) (m : ℕ), (wordsBytes W).take (8 * m) = wordsBytes (W.take m)
  | [], _ => by simp [wordsBytes]
  | _ :: _, 0 => by simp [wordsBytes]
  | x :: W, m + 1 => by
    rw [show wordsBytes (x :: W) = wordBytes x ++ wordsBytes W from rfl, Nat.mul_succ,
      Nat.add_comm, List.take_append, wordBytes_length, List.take_of_length_le (by simp [wordBytes_length]),
      Nat.add_sub_cancel_left, wordsBytes_take W m, List.take_succ_cons]
    rfl

/-- **An aligned stream slice is a slice of the stream's words.** -/
theorem stream_slice (w : ℕ → F) (σ u m : ℕ) :
    ((stream w σ).drop (8 * u)).take (8 * m) = wordsBytes (((streamWords w σ).drop u).take m) := by
  rw [stream, wordsBytes_drop, wordsBytes_take]


/-- A trace entry's output words (`logWords`' per-entry part). -/
def entryW (e : ByteArray × Digest) : List Word := bytesWords e.1.data.toList ++ packBytes e.2.toList

/-- **The output words of aligned items** from stream word `u` on: per item its length word,
then its query's and answer's words (`qlen/8 + 4` stream words after the length word). -/
def trW (W : List Word) : ℕ → List Item → List Word
  | _, [] => []
  | u, it :: its => (toWord it.qlen :: (W.drop (u + 1)).take (it.qlen / 8 + 4)) ++
      trW W (u + it.slen / 8) its

theorem digest_toList (B : List UInt8) (o : ℕ) (h : o + 32 ≤ B.length) :
    (Vector.ofFn fun i : Fin 32 => B.getD (o + i) 0).toList = (B.drop o).take 32 := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [Vector.toList_ofFn, List.getElem_ofFn, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

/-- **An aligned item's output words** are its length word and stream words. -/
theorem entryW_aligned (w : ℕ → F) (σ o : ℕ) (it : Item) (ho : o % 8 = 0) (hq : it.qlen % 8 = 0)
    (hb : o + it.slen ≤ streamBytes) :
    entryW (entryAt (stream w σ) o it) =
      toWord it.qlen :: ((streamWords w σ).drop (o / 8 + 1)).take (it.qlen / 8 + 4) := by
  have hB : (stream w σ).length = 1481344 := (stream_length w σ).trans streamBytes_eq
  have hW : (streamWords w σ).length = 185168 := streamWords_length w σ
  rw [streamBytes_eq] at hb
  simp only [Item.slen] at hb
  have e1 : ((stream w σ).drop (o + 8)).take it.qlen =
      wordsBytes (((streamWords w σ).drop (o / 8 + 1)).take (it.qlen / 8)) := by
    rw [← stream_slice, show 8 * (o / 8 + 1) = o + 8 by omega, show 8 * (it.qlen / 8) = it.qlen by omega]
  have e2 : (Vector.ofFn fun i : Fin 32 => (stream w σ).getD (o + 8 + it.qlen + i) 0).toList =
      wordsBytes (((streamWords w σ).drop (o / 8 + 1 + it.qlen / 8)).take 4) := by
    rw [digest_toList _ _ (by omega), ← stream_slice,
      show 8 * (o / 8 + 1 + it.qlen / 8) = o + 8 + it.qlen by omega]
  show bytesWords (List.take it.qlen (List.drop (o + 8) (stream w σ))).toArray.toList ++
    packBytes (Vector.ofFn fun i : Fin 32 => (stream w σ).getD (o + 8 + it.qlen + i) 0).toList = _
  rw [List.toList_toArray, e1, e2, bytesWords, packBytes_wordsBytes, packBytes_wordsBytes,
    wordsBytes_length, List.length_take, List.length_drop, hW, List.cons_append, List.take_add,
    List.drop_drop, Nat.add_comm (o / 8 + 1) (it.qlen / 8),
    show 8 * min (it.qlen / 8) (185168 - (o / 8 + 1)) = it.qlen by omega]

/-- **The trace's words over aligned items.** -/
theorem readItems_words (w : ℕ → F) (σ : ℕ) : ∀ (its : List Item) (o : ℕ), o % 8 = 0 →
    (∀ it ∈ its, it.qlen % 8 = 0) → o + (its.map Item.slen).sum ≤ streamBytes →
    (readItems (stream w σ) o its).flatMap entryW = trW (streamWords w σ) (o / 8) its
  | [], _, _, _, _ => rfl
  | it :: its, o, ho, hq, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    have h8 : it.slen % 8 = 0 := by have := hq it (by simp); simp only [Item.slen]; omega
    rw [readItems, List.flatMap_cons, trW, entryW_aligned w σ o it ho (hq it (by simp)) (by omega),
      readItems_words w σ its (o + it.slen) (by omega) (fun x hx => hq x (by simp [hx])) (by omega),
      show (o + it.slen) / 8 = o / 8 + it.slen / 8 by omega]

/-- The later items fill the stream after the seed's 160 bytes. -/
theorem tail_slen_le : 160 + (items.tail.map Item.slen).sum ≤ streamBytes := by decide +kernel

theorem items_cons : items = .seed :: items.tail := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 qlen_mod.1
  rw [ht, List.tail_cons]

/-- **Slot `σ`'s trace in words** (`logWords`): the count, the seed's entry (at stream offset 1,
not word-aligned), then every later item's length word and stream words from stream word 20. -/
theorem logWords_readTrace (w : ℕ → F) (σ : ℕ) :
    logWords (readTrace w σ) = toWord 8891 :: (entryW (entryAt (stream w σ) 1 .seed) ++
      trW (streamWords w σ) 20 items.tail) := by
  have hq : ∀ it ∈ items.tail, it.qlen % 8 = 0 := fun it h => by have := qlen_mod.2.2 it h; omega
  have hw := readItems_words w σ items.tail 160 rfl hq tail_slen_le
  show toWord (readTrace w σ).length :: (readTrace w σ).flatMap entryW = _
  rw [readTrace_length]
  refine congrArg (toWord 8891 :: ·) ?_
  rw [readTrace]; conv_lhs => rw [items_cons]
  rw [readItems, List.flatMap_cons, show 1 + Item.seed.slen = 160 from rfl, hw]

/-! ## The signature's words -/

theorem digestW_toList {ws : List Word} (h : ws.length = 4) : (digestW ws).toList = wordsBytes ws := by
  refine List.ext_getElem (by simp [wordsBytes_length, h]) fun i h1 h2 => ?_
  simp [digestW, List.getElem?_eq_getElem h2]

theorem packBytes_digestOf (w : ℕ → F) (e₀ e₁ : ℕ) :
    packBytes (digestOf w e₀ e₁).toList = elemWords (w e₀) ++ elemWords (w e₁) := by
  rw [digestOf, digestW_toList (by simp [elemWords]), packBytes_wordsBytes]

/-- **Slot `σ`'s signature words**: `idx`, then two elements' words per chain value and per path
digest, read from L in order. -/
theorem sigWords_readSig (w : ℕ → F) (σ : ℕ) :
    sigWords (readSig w σ) = toWord (w (lCell σ 0)).c₀.val.toNat ::
      ((List.range wotsLen).flatMap fun j =>
        elemWords (w (lCell σ (1 + 2 * j))) ++ elemWords (w (lCell σ (2 + 2 * j)))) ++
      (List.range sigHeight).flatMap fun t => elemWords (w (lCell σ (1 + 2 * wotsLen + 2 * t))) ++
        elemWords (w (lCell σ (2 + 2 * wotsLen + 2 * t))) := by
  simp only [sigWords, readSig, List.flatMap_map, packBytes_digestOf]

end FR.Read

end G6_FRNodeReadW

section G6_FRNodeReadCore

-- New for `flock-recursive` (BLUEPRINT §4.3, A.7; stage RET-4, PATH-review F2): the declarations of
-- `FRNodeSoundA` that the revision 4 certificate reads, moved here verbatim (same names, statements
-- and proofs): `toListLE_eq_ofFn`, `enc64_toListLE`, `wordBytes_ofBytes`, `wordsBytes_elemWords`,
-- `digestOf_halves`, `readItems_qlen`. `FRNodeSoundA` imports this module.

/-!
# Bytes of digests and field elements, and the read items' query lengths

`digestOf_halves`: a digest's two F halves read back as the digest (through `wordsBytes_elemWords`).
`readItems_qlen`: every entry `Read.readItems` reads has a query no longer than its item's `qlen`.
-/

namespace FR.Snd
open RecursionFast Finset Circ

set_option linter.constructorNameAsVariable false

/-! ## From `FRNodeSoundA`: bytes of digests and field elements -/

theorem toListLE_eq_ofFn : ∀ (n x : ℕ),
    CompPoly.Bytes.toListLE n x = List.ofFn fun i : Fin n => (x / 256 ^ i.val).toUInt8
  | 0, _ => rfl
  | n + 1, x => by
    rw [CompPoly.Bytes.toListLE, toListLE_eq_ofFn n (x / 256), List.ofFn_succ]
    congr 1
    · apply UInt8.toNat_inj.mp; simp [Nat.toUInt8]
    · refine congrArg List.ofFn (funext fun i => ?_)
      rw [Fin.val_succ, Nat.div_div_eq_div_mul, pow_succ', Nat.mul_comm]

theorem enc64_toListLE (n : ℕ) : enc64 n = CompPoly.Bytes.toListLE 8 n := by
  rw [toListLE_eq_ofFn, enc64]

/-- A word decoded from eight bytes encodes back to them. -/
theorem wordBytes_ofBytes (v : Vector UInt8 8) : wordBytes (B64.ofBytes v).val.toBitVec = v.toList := by
  have h := congrArg Vector.toList (B64.toBytes_ofBytes v)
  rw [B64.toBytes_toList] at h
  rw [wordBytes, enc64_toListLE]
  exact h

/-- An F element decoded from 16 bytes: its two coefficient words are those bytes. -/
theorem wordsBytes_elemWords (v : Vector UInt8 16) :
    wordsBytes (Read.elemWords (F.ofBytes v)) = v.toList := by
  simp only [Read.elemWords, wordsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    F.ofBytes, wordBytes_ofBytes]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.toList_ofFn, List.getElem_append, List.length_ofFn, List.getElem_ofFn,
    Vector.getElem_toList]
  split_ifs with h
  · rfl
  · congr 1; simp at h1; omega

/-- **A digest's two F halves read back as the digest.** -/
theorem digestOf_halves {w : ℕ → F} {a b : ℕ} {d : Digest} (ha : w a = dlo d) (hb : w b = dhi d) :
    Read.digestOf w a b = d := by
  apply Vector.toList_inj.mp
  rw [Read.digestOf, Read.digestW_toList (by simp [Read.elemWords]), wordsBytes, List.flatMap_append,
    ← wordsBytes, ← wordsBytes, ha, hb, dlo, dhi, wordsBytes_elemWords, wordsBytes_elemWords]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.toList_ofFn, List.getElem_append, List.length_ofFn, List.getElem_ofFn,
    Vector.getElem_toList]
  split_ifs with h
  · rfl
  · congr 1; simp at h1; omega

/-! ## From `FRNodeSoundA`: the read items' query lengths -/

theorem readItems_qlen (B : List UInt8) : ∀ (o : ℕ) (its : List Item), ∀ e ∈ Read.readItems B o its,
    ∃ it ∈ its, e.1.size ≤ it.qlen
  | _, [], e, he => by simp [Read.readItems] at he
  | o, it :: its, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · refine ⟨it, List.mem_cons_self .., ?_⟩
      simp only [Read.entryAt, ByteArray.size, List.size_toArray]
      exact List.length_take_le _ _
    · obtain ⟨it', hit', h⟩ := readItems_qlen B _ its e he
      exact ⟨it', List.mem_cons_of_mem _ hit', h⟩

end FR.Snd

end G6_FRNodeReadCore
