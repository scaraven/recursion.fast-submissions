-- New for lvm (WP-13a), after FR's `FRNodeRead*`/`FRXOut` (`readTrace`, `reassemble`, the trace's and
-- the proof's words from the stream; rf-k/submissions/flock-recursive/lean@kk/base): lvm's stream has
-- no tags and its proof is in schedule order, so the definitions are new, the method is FR's.
import LvmXLayout
import RecursionFast.Library.WitnessSending

-- (GOLF2: 13 declarations that `certified` does not use moved verbatim to `LvmXOutSegOff`, outside its import closure.)

/-!
# The node witness read off the child's stream (BLUEPRINT §2.2, §6.2 step 7)

The decoded `C_rec` gives the child's stream `Σ = tagTrace ‖ traceBytes tr'` as lanes `W u`
(`u < T`). The entries have the schedule's lengths (`lensL`, static), at lanes `entL` (the first,
`q₀`, of 7 bytes, straddles lanes 1–2 after the tag byte; from lane 6 on every entry is
`|q|, q, a`, lane-aligned). This module defines, from the lanes:

* **`readTraceL W`**: the trace `tr'` (`q₀`'s bytes 9–15 of the stream, then each entry's query
  and answer at its static lane; the length lanes are not read: the circuit fixes them, `Q_link`);
* **`reassembleL tr`**: the proof a trace of `V_S` spells (BLUEPRINT §2.2): `'S' ‖ 0⁷`, then per entry
  by its length (the length rule, `LvmSchedule.lengthRule`): `q₀` nothing, a node query (64 B) its
  half that is **not** the previous answer (its right half if the left one is), a leaf query (a
  length of `leafLens`, `pX`'s rows) the row, every other query its message (`q` without the 32-byte
  state);
* their output words: **`logWords_readTraceL`** (`trWords`), **`packBytes_reassembleL`** (`pWords`),
  **`size_reassembleL`** (`piSize`).

`reassembleL`'s sibling rule (compare with the previous answer) gives the same bytes as `V_S`'s
position-bit rule whenever the node query holds the previous answer in the half its bit selects
(both halves equal otherwise), and `reassembleL` of `V_S`'s own trace is the proof (WP-11b's
obligation, BLUEPRINT §2.2).
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## Words and bytes -/

/-- `n` lanes from `u`. -/
def wsAt (W : ℕ → Word) (u n : ℕ) : List Word := (List.range n).map fun j => W (u + j)

@[simp] theorem length_wsAt (W : ℕ → Word) (u n : ℕ) : (wsAt W u n).length = n := by simp [wsAt]

theorem wsAt_add (W : ℕ → Word) (u a b : ℕ) : wsAt W u (a + b) = wsAt W u a ++ wsAt W (u + a) b := by
  simp only [wsAt, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => by simp [Function.comp, Nat.add_assoc]

theorem wsAt_drop (W : ℕ → Word) (u a n : ℕ) : (wsAt W u n).drop a = wsAt W (u + a) (n - a) := by
  by_cases h : a ≤ n
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [wsAt_add, List.drop_left' (length_wsAt _ _ _), Nat.add_sub_cancel_left]
  · rw [List.drop_eq_nil_of_le (by simp; omega), show n - a = 0 by omega]; rfl

theorem wsAt_take (W : ℕ → Word) (u a n : ℕ) (h : a ≤ n) : (wsAt W u n).take a = wsAt W u a := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [wsAt_add, List.take_left' (length_wsAt _ _ _)]

theorem wordsBytes_append (a b : List Word) : wordsBytes (a ++ b) = wordsBytes a ++ wordsBytes b :=
  List.flatMap_append

theorem wordsBytes_drop (ws : List Word) (a : ℕ) : (wordsBytes ws).drop (8 * a) = wordsBytes (ws.drop a) := by
  induction ws generalizing a with
  | nil => simp [wordsBytes]
  | cons w ws ih =>
    cases a with
    | zero => rfl
    | succ a =>
      rw [show wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws from rfl,
        show 8 * (a + 1) = 8 + 8 * a by ring, ← List.drop_drop,
        List.drop_left' (wordBytes_length w), ih, List.drop_succ_cons]

theorem wordsBytes_take (ws : List Word) (a : ℕ) : (wordsBytes ws).take (8 * a) = wordsBytes (ws.take a) := by
  induction ws generalizing a with
  | nil => simp [wordsBytes]
  | cons w ws ih =>
    cases a with
    | zero => simp [wordsBytes]
    | succ a =>
      rw [show wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws from rfl,
        show 8 * (a + 1) = 8 + 8 * a by ring, List.take_append, List.take_of_length_le
          (by rw [wordBytes_length]; (clear * -; omega)), wordBytes_length, Nat.add_sub_cancel_left, ih,
        List.take_succ_cons]
      rfl

theorem wordsBytes_inj {a b : List Word} (h : wordsBytes a = wordsBytes b) : a = b := by
  rw [← packBytes_wordsBytes a, h, packBytes_wordsBytes]

/-- A byte list as a byte array. -/
def bArr (l : List UInt8) : ByteArray := ⟨l.toArray⟩

@[simp] theorem bArr_data (l : List UInt8) : (bArr l).data.toList = l := rfl

@[simp] theorem bArr_size (l : List UInt8) : (bArr l).size = l.length := by simp [bArr, ByteArray.size]

/-- **The digest of four words** (their 32 bytes). -/
def digW (ws : List Word) : Digest := Vector.ofFn fun i => (wordsBytes ws).getD i 0

theorem digW_toList {ws : List Word} (h : ws.length = 4) : (digW ws).toList = wordsBytes ws := by
  have hl : (wordsBytes ws).length = 32 := by rw [wordsBytes_length, h]
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  simp [digW, List.getElem?_eq_getElem h2]

theorem packBytes_digW {ws : List Word} (h : ws.length = 4) : packBytes (digW ws).toList = ws := by
  rw [digW_toList h, packBytes_wordsBytes]

/-! ## The trace -/

/-- The entry at lane `u` of a query of `len` bytes (`len ≡ 0 mod 8`): the query's `len / 8`
lanes after the length lane, then the answer's 4 lanes. -/
def entAt (W : ℕ → Word) (u len : ℕ) : ByteArray × Digest :=
  (bArr (wordsBytes (wsAt W (u + 1) (len / 8))), digW (wsAt W (u + 1 + len / 8) 4))

/-- `q₀`'s entry: stream bytes 9–15 (bytes 1–7 of lane 1), the answer at lanes 2–5. -/
def q0Ent (W : ℕ → Word) : ByteArray × Digest := (bArr ((wordBytes (W 1)).drop 1), digW (wsAt W 2 4))

/-- The query lengths of entries `1 … qS − 1` (the seed, then the schedule's queries). -/
def lensL : List ℕ := (blocks pX).flatMap fun b => b.queries.map Prod.snd

/-- Lanes and lengths of a run of entries from lane `u`. -/
def walk : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | u, len :: r => (u, len) :: walk (u + 5 + len / 8) r

/-- **The entries after `q₀`**: lane and length (from lane 6). -/
def entL : List (ℕ × ℕ) := walk 6 lensL

/-- **The child's trace** read off its stream's lanes `W`. -/
def readTraceL (W : ℕ → Word) : Trace := q0Ent W :: entL.map fun x => entAt W x.1 x.2

/-- The words of an entry's contribution, by its length. -/
def pieceLen (len : ℕ) : ℕ := if len = 64 then 4 else if len ∈ leafLens then len / 8 else (len - 32) / 8

/-! The static facts of `lensL` per block: `blocks pX` has about a thousand blocks, `lensL` about
twelve thousand entries, so the kernel checks closed forms over the blocks (`blocks_lens`, with
`LvmXLayout`'s `blocks_tally`) instead of evaluating `lensL`. -/

/-- A block's query lengths are lane-aligned and at least 32 bytes. -/
private def blkLensOk : Blk → Bool
  | .one _ len => len % 8 == 0 && 32 ≤ len
  | .opn _ row _ => row % 8 == 0 && 32 ≤ row

/-- A block's contribution to the proof in words. -/
private def blkPieceLen : Blk → ℕ
  | .one _ len => pieceLen len
  | .opn t row path => t * (pieceLen row + path * pieceLen 64)

private theorem qlens_opn (t row path : ℕ) : (Blk.opn t row path).queries.map Prod.snd =
    (List.replicate t (row :: List.replicate path 64)).flatten := by
  simp [Blk.queries, List.map_flatten, List.map_replicate]

private theorem qlens_length (b : Blk) : (b.queries.map Prod.snd).length = b.count := by
  cases b with
  | one c len => rfl
  | opn t row path =>
    rw [qlens_opn, Blk.count]
    simp [List.length_flatten, List.map_replicate, List.sum_replicate, Nat.mul_comm, Nat.add_comm]

private theorem qlens_all (b : Blk) (h : blkLensOk b = true) :
    (b.queries.map Prod.snd).all (fun l => l % 8 == 0 && 32 ≤ l) = true := by
  cases b with
  | one c len => simpa [Blk.queries, blkLensOk] using h
  | opn t row path =>
    rw [qlens_opn]
    simp only [blkLensOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    simp only [List.all_eq_true, List.mem_flatten, List.mem_replicate, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    rintro x ⟨l, ⟨-, rfl⟩, hx⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h
    · rw [(List.mem_replicate.mp hx).2]; (clear * -; omega)

private theorem qlens_pieces (b : Blk) :
    ((b.queries.map Prod.snd).map pieceLen).sum = blkPieceLen b := by
  cases b with
  | one c len => simp [Blk.queries, blkPieceLen]
  | opn t row path =>
    rw [qlens_opn, blkPieceLen]
    simp [List.map_flatten, List.map_replicate, List.sum_flatten, List.sum_replicate]

/-- The static facts at `pX`, per block (decided with `LvmXLayout`'s other numbers at `P20`,
`layout_all_P20`). -/
private theorem blocks_lens : (blocks pX).all blkLensOk = true ∧
    8 + 8 * ((blocks pX).map blkPieceLen).sum = piSize pX := by
  have e1 : blkLensOk = blkLensOkL := funext fun b => by cases b <;> rfl
  have e2 : blkPieceLen = blkPieceLenL := funext fun b => by cases b <;> rfl
  rw [e1, e2]
  exact layout_all_P20.2.2.2.2.2.2.1

private theorem lens_flatMap_length (bs : List Blk) :
    (bs.flatMap fun b => b.queries.map Prod.snd).length = (bs.map Blk.count).sum := by
  rw [List.length_flatMap]
  simp only [qlens_length]

/-- **The static facts**: `qS − 1` lengths, all lane-aligned, at least 32 bytes. -/
theorem lensL_facts : lensL.length + 1 = qS pX ∧ lensL.all (fun l => l % 8 == 0 && 32 ≤ l) = true := by
  refine ⟨?_, ?_⟩
  · rw [lensL, lens_flatMap_length, Nat.add_comm]
    exact blocks_tally.1
  · rw [lensL, List.all_flatMap, List.all_eq_true]
    exact fun b hb => qlens_all b (List.all_eq_true.mp blocks_lens.1 b hb)

theorem length_walk : ∀ (u : ℕ) (l : List ℕ), (walk u l).length = l.length
  | _, [] => rfl
  | u, _ :: r => by simp [walk, length_walk _ r]

theorem length_readTraceL (W : ℕ → Word) : (readTraceL W).length = qS pX := by
  simp [readTraceL, entL, length_walk, lensL_facts.1.symm]

/-- An entry's output words: its length word, its query's and answer's lanes. -/
def entW (W : ℕ → Word) (u len : ℕ) : List Word := toWord len :: wsAt W (u + 1) (len / 8 + 4)

theorem enc64_drop1 (n : ℕ) : (enc64 n).drop 1 = List.ofFn fun i : Fin 7 => (n / 256 / 256 ^ i.val).toUInt8 := by
  refine List.ext_getElem (by simp [enc64]) fun i h1 h2 => ?_
  simp only [enc64, List.getElem_drop, List.getElem_ofFn, Nat.div_div_eq_div_mul, ← pow_succ']
  congr 3; (clear * -; omega)

/-- Bytes 1–7 of a word (FR `FRXOut.sh8_bytes`). -/
theorem sh8_bytes (x : Word) : toWord (ofLE ((wordBytes x).drop 1)) = x >>> 8 := by
  have hx := x.isLt
  rw [wordBytes, enc64_drop1, ofLE_ofFn]
  apply BitVec.eq_of_toNat_eq
  simp only [toWord, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by (clear * -; omega) : x.toNat / 256 % 256 ^ 7 < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat / 256 < 256 ^ 7)]

theorem entryWords_entAt (W : ℕ → Word) (u len : ℕ) (h : len % 8 = 0) :
    bytesWords (entAt W u len).1.data.toList ++ packBytes (entAt W u len).2.toList = entW W u len := by
  simp only [entAt, bytesWords, bArr_data, wordsBytes_length, length_wsAt, packBytes_wordsBytes,
    packBytes_digW (length_wsAt _ _ _), entW, List.cons_append]
  rw [wsAt_add, show 8 * (len / 8) = len by omega]

theorem entryWords_q0 (W : ℕ → Word) :
    bytesWords (q0Ent W).1.data.toList ++ packBytes (q0Ent W).2.toList =
      toWord 7 :: (W 1 >>> 8) :: wsAt W 2 4 := by
  have hl : ((wordBytes (W 1)).drop 1).length = 7 := by simp [wordBytes_length]
  simp only [q0Ent, bytesWords, bArr_data, hl, packBytes_digW (length_wsAt _ _ _), List.cons_append]
  congr 1
  rw [packBytes, hl]
  simp only [show (7 + 7) / 8 = 1 from rfl, List.range_one, List.map_cons, List.map_nil,
    Nat.mul_zero, List.drop_zero, List.take_of_length_le (by rw [hl]; (clear * -; omega) : _ ≤ 8),
    sh8_bytes, List.singleton_append]

end Lvm.X

namespace Lvm.X

open RecursionFast Lvm

/-! ## The reassembled proof -/

/-- The proof's bytes 0–7: `'S' ‖ 0⁷` (`V_S` rejects anything else, `LvmDriver.parseOk`). -/
def header0 : List UInt8 := [0x53, 0, 0, 0, 0, 0, 0, 0]

/-- An entry's contribution to the proof, after the previous answer `prev` (BLUEPRINT §2.2, by the
query's length: `q₀` nothing, a node its half that is not `prev`, a leaf its row (a length of
`leafLens`), else the message after the 32-byte state). -/
def piece (prev : Digest) (e : ByteArray × Digest) : List UInt8 :=
  if e.1.data.toList.length = 7 then []
  else if e.1.data.toList.length = 64 then
    (if e.1.data.toList.take 32 = prev.toList then e.1.data.toList.drop 32 else e.1.data.toList.take 32)
  else if e.1.data.toList.length ∈ leafLens then e.1.data.toList
  else e.1.data.toList.drop 32

/-- The contributions of a trace's entries, each after the previous entry's answer. -/
def pieces : Digest → Trace → List UInt8
  | _, [] => []
  | prev, e :: tr => piece prev e ++ pieces e.2 tr

/-- **`reassemble`**: the proof a trace of `V_S` spells. -/
def reassembleL (tr : Trace) : ByteArray := bArr (header0 ++ pieces (Vector.replicate 32 0) tr)

/-- A node entry's sibling lanes: its right half if its left half is the previous answer (lanes
`x − 4 … x − 1`), else its left half. -/
def sibWs (W : ℕ → Word) (x : ℕ) : List Word :=
  if wsAt W (x + 1) 4 = wsAt W (x - 4) 4 then wsAt W (x + 5) 4 else wsAt W (x + 1) 4

theorem header0_eq : header0 = wordBytes (toWord 0x53) := by decide

private theorem pieces_flatMap (bs : List Blk) :
    ((bs.flatMap fun b => b.queries.map Prod.snd).map pieceLen).sum = (bs.map blkPieceLen).sum := by
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  simp only [Function.comp_def, qlens_pieces]

theorem lensL_pieces : 8 + 8 * (lensL.map pieceLen).sum = piSize pX := by
  rw [lensL, pieces_flatMap]
  exact blocks_lens.2

end Lvm.X
