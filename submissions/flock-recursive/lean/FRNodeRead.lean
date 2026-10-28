-- New for `flock-recursive` (BLUEPRINT §4.3 `node_sound`, §6.2 step 5, A.5, A.7; stage S-H2,
-- track L-ext, S-H2k).
import FRFormat
import RecursionFast.Library.Words

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
