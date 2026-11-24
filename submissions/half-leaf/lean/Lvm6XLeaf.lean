-- lvm6 X2 (BLUEPRINT v3 §2.3, §3 step 3; FORMAT6 v2 §2.2, §6.2): the tree inversion. From the decoded tree
-- block (slots 0–7 of the `2^19` heap rows) rebuild the leaf data `xs` (leaf rows' slots 0–3), prove it is the
-- witness under the tree relation (T1's `tree_sound`), and output `Wit.leaf xs` (`2 + 4n` words).
import Lvm6XRead
import Lvm6LeafTree
import Lvm6LeafBlock
import LvmXOut

/-!
# The tree inversion and the leaf witness

The extractor holds the decoded tree block as a table `q : Cols` of words, `q s r` the word of slot `s` at heap
row `r` (BLUEPRINT §2.2: slots 0–7 are the tree inputs, 4 raw words each; rows `0 … 2n − 1`, low bit first, row
`1` the root, leaf rows `n + i`).

* **`xs6 n q`**: the leaf data, block `i` the digest of the four words `q 0 (n + i) … q 3 (n + i)` (`digW`: their
  32 little-endian bytes, the contract's digest-as-four-words); **`witWords_xs6`**: the leaf witness's output
  words are `0, n` and those words in order (`leafWords`).
* **`ColTreeOk n q h`**: the relation (W), (R) of BLUEPRINT §2.3 on the columns, with every row's output digest
  the Keccak-f of its input lanes (`outD6`, (G)); **`colTree_sound`**: at `n = 2^k` it gives
  `dataRoot (xs6 n q) = h` (T1's `tree_sound` and `leafItem_block`, `dataNode_block`).
* **`leafOutIR n colB S`**: the program that outputs `witWords (.leaf xs)` from slot `m`'s words at
  `colB + m·S + r`; **`leafOutIR_sem`**, **`cost_leafOutIR`** (`22 + 28 n` steps on every tape: `7,340,054` at
  `n = 2^18`), `outs_leafOutIR` (`2 + 4n`).
-/

namespace Lvm6.X

open RecursionFast RecursionFast.Keccak Lvm.X

/-! ## The leaf data -/

/-- The decoded tree block: `q s r` is slot `s`'s word at heap row `r`. -/
abbrev Cols := ℕ → ℕ → Word

/-- Block `i`'s four words: slots `0 … 3` of leaf row `n + i`. -/
def blkW (n : ℕ) (q : Cols) (i : ℕ) : List Word := [q 0 (n + i), q 1 (n + i), q 2 (n + i), q 3 (n + i)]

/-- **The leaf data** of the decoded tree block: `n` blocks, block `i` the digest of `blkW n q i`. -/
def xs6 (n : ℕ) (q : Cols) : List Digest := (List.range n).map fun i => digW (blkW n q i)

/-- The output words of the leaf witness: `0`, `n`, then every block's four words. -/
def leafWords (n : ℕ) (q : Cols) : List Word :=
  toWord 0 :: toWord n :: (List.range n).flatMap (blkW n q)

@[simp] theorem xs6_length (n : ℕ) (q : Cols) : (xs6 n q).length = n := by simp [xs6]

/-- **The leaf witness's words** are `leafWords`. -/
theorem witWords_xs6 (n : ℕ) (q : Cols) : witWords (.leaf (xs6 n q)) = leafWords n q := by
  simp only [witWords, leafWords, xs6, List.length_map, List.length_range, List.flatMap_map]
  refine congrArg (fun l => toWord 0 :: toWord n :: l) ?_
  exact List.flatMap_congr fun i _ => packBytes_digW (by simp [blkW])

/-- **The leaf witness is read back** from `leafWords`. -/
theorem decodeWit_leafWords {n : ℕ} (hn : n < 2 ^ 64) (q : Cols) :
    decodeWit (leafWords n q) = some (.leaf (xs6 n q)) := by
  rw [← witWords_xs6]
  exact decodeWit_witWords _ (by simpa [Wit.Fits] using hn)

/-! ## Digests as four words (the bridge to T1's lanes) -/

/-- A machine word as a Keccak lane. -/
def u64 (w : Word) : UInt64 := UInt64.ofBitVec w

theorem byteOf_u64 (w : Word) {k : ℕ} (hk : k < 8) : byteOf (u64 w) k = (w.toNat / 256 ^ k).toUInt8 := by
  refine byte_ext fun r hr => ?_
  rw [byteOf_bit _ hk hr]
  simp only [u64, UInt64.toBitVec_ofBitVec, Nat.toUInt8]
  rw [show (UInt8.ofNat (w.toNat / 256 ^ k)).toBitVec = BitVec.ofNat 8 (w.toNat / 256 ^ k) from rfl,
    BitVec.getLsbD_ofNat, show (256 : ℕ) ^ k = 2 ^ (8 * k) by rw [pow_mul]; norm_num,
    Nat.testBit_div_two_pow, BitVec.getLsbD, show r + 8 * k = 8 * k + r by ring]
  simp [hr]

/-- **Word `j` of the digest of four words is word `j`.** -/
theorem dLane_digW {ws : List Word} (hl : ws.length = 4) {j : ℕ} (hj : j < 4) :
    dLane (digW ws) j = u64 (ws.getD j 0) := by
  refine word_ext fun k hk => ?_
  rw [dLane, byteOf_blockLane _ _ hk, byteOf_u64 _ hk]
  have h32 : 8 * j + k < 32 := by omega
  rw [Array.getD_eq_getD_getElem?, Vector.getElem?_toArray, digW]
  rw [Vector.getElem?_ofFn, dif_pos h32, Option.getD_some, ← wordByte_eq_getD, wordByte,
    show (8 * j + k) / 8 = j by omega, show (8 * j + k) % 8 = k by omega]

theorem itemLanes_congr {w w' : ℕ → UInt64} (h : ∀ j < 4, w j = w' j) : itemLanes w = itemLanes w' := by
  simp only [itemLanes, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

theorem nodeLanes_congr {l l' r r' : ℕ → UInt64} (hl : ∀ j < 4, l j = l' j) (hr : ∀ j < 4, r j = r' j) :
    nodeLanes l r = nodeLanes l' r' := by
  simp only [nodeLanes, hl 0 (by norm_num), hl 1 (by norm_num), hl 2 (by norm_num), hl 3 (by norm_num),
    hr 0 (by norm_num), hr 1 (by norm_num), hr 2 (by norm_num), hr 3 (by norm_num)]

/-! ## The tree relation on the columns -/

/-- **Row `κ`'s input lanes** (BLUEPRINT §2.3): a parent row `κ < n` hashes `0x44 ‖ slots 0–3 ‖ slots 4–7`, a
leaf row `κ ≥ n` hashes `0x48 ‖ slots 0–3` (T1's `nodeLanes`, `itemLanes`). -/
def inLanes6 (n : ℕ) (q : Cols) (κ : ℕ) : State :=
  if κ < n then nodeLanes (fun j => u64 (q j κ)) (fun j => u64 (q (4 + j) κ))
  else itemLanes (fun j => u64 (q j κ))

/-- **Row `κ`'s output digest** `D(κ)`: output lanes 0–3 of Keccak-f of its input lanes ((G)). -/
def outD6 (n : ℕ) (q : Cols) (κ : ℕ) : Digest := outDigest (keccakF (inLanes6 n q κ))

/-- **The tree relation** (W), (R) of BLUEPRINT §2.3 on the decoded columns: a parent row `k ≠ 0` holds its
children's digests in slots 0–3 (left, row `2k`) and 4–7 (right, row `2k + 1`), row 0's slots 4–7 hold `D(1)`,
and row 0's slots 4–7 are the four words of `h`. -/
structure ColTreeOk (n : ℕ) (q : Cols) (h : Digest) : Prop where
  /-- (W), left child, `k ≠ 0`. -/
  wl : ∀ k, 1 ≤ k → k < n → ∀ m < 4, u64 (q m k) = dLane (outD6 n q (2 * k)) m
  /-- (W), right child, every `k` (row 0 included). -/
  wr : ∀ k, k < n → ∀ m < 4, u64 (q (4 + m) k) = dLane (outD6 n q (2 * k + 1)) m
  /-- (R): row 0's slots 4–7 are `h`. -/
  root : ∀ m < 4, u64 (q (4 + m) 0) = dLane h m

/-- **The tree inversion is sound**: on `n = 2^k` leaves, the tree relation on the decoded columns makes the
extracted leaf data a witness of `h`. -/
theorem colTree_sound {k n : ℕ} (hn : n = 2 ^ k) {q : Cols} {h : Digest} (hT : ColTreeOk n q h) :
    dataRoot (xs6 n q) = h := by
  have hn1 : 0 < n := hn ▸ Nat.two_pow_pos k
  have hH : Lvm6.HeapOk (xs6 n q) (outD6 n q) := by
    refine ⟨fun i hi => ?_, fun i h1 h2 => ?_⟩
    · rw [xs6_length] at hi
      rw [show (xs6 n q).length + i = n + i by simp, Lvm6.leafItem_block, outD6, inLanes6, if_neg (by omega)]
      congr 2
      refine itemLanes_congr fun j hj => ?_
      simp only [xs6, List.getElem_map, List.getElem_range]
      rw [dLane_digW (by simp [blkW]) hj]
      interval_cases j <;> rfl
    · rw [xs6_length] at h2
      rw [Lvm6.dataNode_block, outD6, inLanes6, if_pos h2]
      congr 2
      exact nodeLanes_congr (fun j hj => hT.wl i h1 h2 j hj) (fun j hj => hT.wr i h2 j hj)
  have h1 := Lvm6.tree_sound (by rw [xs6_length]; exact hn) hH
  rw [← h1]
  exact (Lvm6.digest_ext_dLane fun j hj => by rw [← hT.wr 0 hn1 j hj, hT.root j hj]).symm

/-! ## The output program -/

/-- The value. -/ def rLV : ℕ := 240
/-- The row pointer (slot 0). -/ def rLP : ℕ := 241
/-- The address. -/ def rLA : ℕ := 242
/-- The column stride. -/ def rLS : ℕ := 243
/-- The block count. -/ def rLN : ℕ := 244
/-- The loop counter. -/ def rLC : ℕ := 245

/-- The next slot's word: `a += S`, output `M[a]`. -/
def lfStep : XIR := .seq (.blk [.op .add rLA rLA rLS]) (.seq (.load rLV rLA) (.out rLV))

/-- One block: the words of slots 0–3 at the row pointer, then `p += 1`. -/
def lfBody : XIR :=
  .seq (.blk [.op .or rLA rLP rLP]) (.seq (.load rLV rLA) (.seq (.out rLV)
    (.seq lfStep (.seq lfStep (.seq lfStep (.blk [.op .add rLP rLP cOne]))))))

/-- **The leaf witness's output**: `0`, `n`, then for `i < n` the words of slots 0–3 of row `n + i`, slot `m`'s
word at row `r` being `M[colB + m·S + r]`. -/
def leafOutIR (n colB S : ℕ) : XIR :=
  .seq (.blk [.const rLV 0]) (.seq (.out rLV) (.seq (.blk [.const rLV (toWord n)]) (.seq (.out rLV)
    (.seq (.blk [.const rLP (toWord (colB + n)), .const rLS (toWord S), .const rLN (toWord n)])
      (.loopK rLC rLN (toWord n) lfBody)))))

theorem wf_leafOutIR (n colB S : ℕ) : WF (leafOutIR n colB S) := by
  simp +decide [leafOutIR, lfBody, lfStep, WF, Writes, Prim.dst, rLV, rLP, rLA, rLS, rLN, rLC, regs, cTmp]

theorem noLoopT_leafOutIR (n colB S : ℕ) : NoLoopT (leafOutIR n colB S) := by
  simp [leafOutIR, lfBody, lfStep, NoLoopT]

theorem sizeIR_leafOutIR (n colB S : ℕ) : sizeIR (leafOutIR n colB S) = 50 := by
  simp [leafOutIR, lfBody, lfStep, sizeIR, blkSteps]

/-- **The exact cost**: `22 + 28 n` steps on every tape (`n < 2^64`). -/
theorem cost_leafOutIR (n colB S t : ℕ) (hn : n < 2 ^ 64) : cost (leafOutIR n colB S) t = 22 + 28 * n := by
  simp [leafOutIR, lfBody, lfStep, cost, blkSteps, toNat_toWord hn]
  ring

theorem outs_leafOutIR (n colB S t : ℕ) (hn : n < 2 ^ 64) : outs (leafOutIR n colB S) t = 2 + 4 * n := by
  simp only [leafOutIR, lfBody, lfStep, outs, toNat_toWord hn]
  omega

/-! ## Its semantics -/

section Sem

variable (I : Array Word)

/-- One block's run: the four words at `p, p + S, p + 2S, p + 3S` are output, `p` advances. -/
theorem lfBody_sem (s : St) (hM : Inv s.M) {p S : ℕ} (hp0 : regs ≤ p) (hP : rd s.M rLP = toWord p)
    (hS : rd s.M rLS = toWord S) (hp : p + 3 * S + 1 < 2 ^ 64) :
    (semXIR I lfBody s).o.toList =
      s.o.toList ++ [rd s.M p, rd s.M (p + S), rd s.M (p + 2 * S), rd s.M (p + 3 * S)] ∧
    rd (semXIR I lfBody s).M rLP = toWord (p + 1) ∧ rd (semXIR I lfBody s).M rLS = toWord S ∧
    (∀ x, regs ≤ x → rd (semXIR I lfBody s).M x = rd s.M x) ∧ Inv (semXIR I lfBody s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hp0
  have wf : WF lfBody := by simp +decide [lfBody, lfStep, WF, Prim.dst, rLV, rLP, rLA]
  refine ⟨?_, ?_, ?_, fun x hx => ?_, inv_sem I wf hM⟩
  · simp only [lfBody, lfStep, semXIR, runPrims, List.foldl, Prim.run, Array.toList_push,
      List.append_assoc, List.cons_append, List.nil_append]
    simp (disch := first | decide | (simp only [Array.size_setIfInBounds, rLV, rLP, rLA, rLS]; omega) | (simp only [rLV, rLP, rLA, rLS]; omega))
      only [rd_set_self, rd_set_ne, hP, hS, XOp.eval, BitVec.or_self, add_toWord, toWord_add,
        toNat_toWord (show p < 2 ^ 64 by omega), toNat_toWord (show p + S < 2 ^ 64 by omega),
        toNat_toWord (show p + S + S < 2 ^ 64 by omega), toNat_toWord (show p + S + S + S < 2 ^ 64 by omega)]
    rw [show p + 2 * S = p + S + S by ring, show p + 3 * S = p + S + S + S by ring]
  · simp only [lfBody, lfStep, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [Array.size_setIfInBounds, rLV, rLP, rLA, rLS]; omega))
      only [rd_set_self, rd_set_ne, hP, h1, XOp.eval]
    exact toWord_add_one p
  · simp only [lfBody, lfStep, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [Array.size_setIfInBounds, rLV, rLP, rLA, rLS]; omega))
      only [rd_set_ne, hS]
  · simp only [regs] at hx
    simp only [lfBody, lfStep, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [rLV, rLP, rLA, rLS]; omega)) only [rd_set_ne]

/-- **The leaf witness's output**: `leafOutIR n colB S` appends `witWords (.leaf (xs6 n q))` for the columns
`q m r = M[colB + m·S + r]` it reads; it writes registers only. -/
theorem leafOutIR_sem (s : St) (hM : Inv s.M) {n colB S : ℕ} (hcol : regs ≤ colB) (hS : colB + 2 * n + 3 * S < 2 ^ 64) :
    (semXIR I (leafOutIR n colB S) s).o.toList =
      s.o.toList ++ witWords (.leaf (xs6 n fun m r => rd s.M (colB + m * S + r))) ∧
    (∀ x, regs ≤ x → rd (semXIR I (leafOutIR n colB S) s).M x = rd s.M x) ∧
    Inv (semXIR I (leafOutIR n colB S) s).M := by
  rw [witWords_xs6]
  have hcol' : 256 ≤ colB := hcol
  have hs := hM.1
  simp only [regs] at hs
  have hn : n < 2 ^ 64 := by omega
  set pre : XIR := .seq (.blk [.const rLV 0]) (.seq (.out rLV) (.seq (.blk [.const rLV (toWord n)])
    (.seq (.out rLV) (.blk [.const rLP (toWord (colB + n)), .const rLS (toWord S), .const rLN (toWord n)]))))
    with hpre
  have e : semXIR I (leafOutIR n colB S) s = semXIR I (.loopK rLC rLN (toWord n) lfBody) (semXIR I pre s) := by
    simp only [leafOutIR, hpre, semXIR_seq]
  have wpre : WF pre := by simp +decide [hpre, WF, Prim.dst, rLV, rLP, rLS, rLN]
  have hM0 := inv_sem I wpre hM
  have hs0 := hM0.1
  simp only [regs] at hs0
  have o0 : (semXIR I pre s).o.toList = s.o.toList ++ [toWord 0, toWord n] := by
    simp only [hpre, semXIR, runPrims, List.foldl, Prim.run, Array.toList_push, List.append_assoc,
      List.cons_append, List.nil_append]
    simp (disch := first | decide | (simp only [Array.size_setIfInBounds]; omega) | omega)
      only [rd_set_self, rLV]
    rfl
  have r0 : rd (semXIR I pre s).M rLP = toWord (colB + n) ∧ rd (semXIR I pre s).M rLS = toWord S ∧
      rd (semXIR I pre s).M rLN = toWord n ∧ ∀ x, regs ≤ x → rd (semXIR I pre s).M x = rd s.M x := by
    simp only [hpre, semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, fun x hx => ?_⟩
    · simp (disch := first | decide | (simp only [Array.size_setIfInBounds]; omega) | omega)
        only [rd_set_self, rd_set_ne, rLV, rLP, rLS, rLN]
    · simp (disch := first | decide | (simp only [Array.size_setIfInBounds]; omega) | omega)
        only [rd_set_self, rd_set_ne, rLV, rLP, rLS, rLN]
    · simp (disch := first | decide | (simp only [Array.size_setIfInBounds]; omega) | omega)
        only [rd_set_self, rd_set_ne, rLV, rLP, rLS, rLN]
    · simp only [regs] at hx
      simp (disch := first | decide | omega) only [rd_set_ne, rLV, rLP, rLS, rLN]
  obtain ⟨p0, s0', n0, k0⟩ := r0
  rw [e]
  generalize semXIR I pre s = s0 at hM0 hs0 o0 p0 s0' n0 k0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ rd s'.M rLP = toWord (colB + n + j) ∧
    rd s'.M rLS = toWord S ∧ (∀ x, regs ≤ x → rd s'.M x = rd s.M x) ∧
    s'.o.toList = s.o.toList ++ [toWord 0, toWord n] ++ (List.range j).flatMap
      (blkW n fun m r => rd s.M (colB + m * S + r))
  have hE : ∀ i, i ≠ rLC → i ≠ cTmp → rd (entryK rLC rLN (toWord n) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK rLC rLN (toWord n) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), ?_, ?_, fun x hx => ?_, ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), p0, Nat.add_zero]
    · rw [hE _ (by decide) (by decide), s0']
    · simp only [regs] at hx
      rw [hE _ (by simp only [rLC]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
    · rw [o0]; simp
  have hstep : ∀ j s', j < n → P j s' → P (j + 1) (decS rLC (semXIR I lfBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    obtain ⟨b1, b2, b3, b4, b5⟩ := lfBody_sem I s' i1 (p := colB + n + j) (S := S) (by simp only [regs]; omega) i2 i3 (by omega)
    have hd : ∀ y, y ≠ rLC → rd (decS rLC (semXIR I lfBody s')).M y = rd (semXIR I lfBody s').M y :=
      fun y hy => rd_decS (Ne.symm hy) _
    have hx : ∀ y, regs ≤ y → y ≠ rLC := fun y hy => by simp only [regs, rLC] at *; omega
    refine ⟨inv_decS b5 (by decide), ?_, ?_, fun x hx' => ?_, ?_⟩
    · rw [hd _ (by decide), b2, Nat.add_assoc]
    · rw [hd _ (by decide), b3]
    · rw [hd _ (hx x hx'), b4 x hx', i4 x hx']
    · rw [show (decS rLC (semXIR I lfBody s')).o = (semXIR I lfBody s').o from rfl]
      have hr : ∀ a, colB ≤ a → rd s'.M a = rd s.M a := fun a ha => i4 a (by simp only [regs]; omega)
      have hb : [rd s'.M (colB + n + j), rd s'.M (colB + n + j + S), rd s'.M (colB + n + j + 2 * S),
          rd s'.M (colB + n + j + 3 * S)] = blkW n (fun m r => rd s.M (colB + m * S + r)) j := by
        have e : ∀ x y : ℕ, x = y → rd s.M x = rd s.M y := fun _ _ h => h ▸ rfl
        rw [hr _ (by omega), hr _ (by omega), hr _ (by omega), hr _ (by omega)]
        simp only [blkW, List.cons.injEq, and_true]
        exact ⟨e _ _ (by ring), e _ _ (by ring), e _ _ (by ring), e _ _ (by ring)⟩
      rw [b1, i5, hb, List.range_succ, List.flatMap_append, List.flatMap_singleton]
      simp only [List.append_assoc]
  have hfin := loopK_run I lfBody P s0 hM0 (c := rLC) (n := rLN) (K := n)
    (by decide) (by decide) (by decide) n0 hn h0 hstep
  obtain ⟨f1, -, -, f4, f5⟩ := hfin
  refine ⟨?_, f4, f1⟩
  rw [f5, leafWords]
  simp

end Sem

end Lvm6.X
