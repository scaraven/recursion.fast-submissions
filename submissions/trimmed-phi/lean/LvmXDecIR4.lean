-- WP-13b: the whole decoder's semantics `decIR_sem` (new composition; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b).
import LvmXNtt3
import LvmXNtt4
import LvmXInterp4
import LvmXCopy
import LvmXDecBr
import LvmXEqT

-- (GOLF2: 15 declarations that `certified` does not use moved verbatim to `LvmXTopOff`, outside its import closure.)

-- ===== merged from `LvmXNtt5` (GOLF module merge: `LvmXNtt5.lean` is now a stub importing `LvmXDecIR4`) =====
section
-- adapted from rf-k/submissions/flock-recursive/lean/FRXFwd.lean@8bff272b (section G6_FRXBfly:
-- bflyIR_decode, as `bflyIR_decode`).
-- New for lvm (WP-13b): the table and the NTTs composed (`wtab_bflyIR_coeffs`,
-- `wtab_fwdIR_enc`) and the link to the pure decoder `LvmXDec.decWord` (`bflyIR_decWord`).

/-!
# The NTT programs composed with the basis table and the decoder

* `wtabIR_nw`: the table program does not touch the row pointer `rA0` or the forward NTT's
  registers.
* **`wtab_bflyIR_coeffs`**, **`wtab_fwdIR_enc`**: `wtabIR tb` then `bflyIR ℓ tb` (resp.
  `fwdIR ℓ tb`) from any state with the row pointer set: the table hypothesis of
  `bflyIR_sem`/`fwdIR_sem` is discharged by `wtabIR_sem`.
* **`bflyIR_decode`**: a row holding `interpF ptK J u` with `u = Enc(c)` on `J` (`|J| = 2^ℓ`)
  decodes to `c` (`Lvm.Nb.decode_row`).
* **`bflyIR_decWord`**: the row of `C_rec`'s decoder (`LvmXDec.decWord`, `ℓ = 13`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

end Lvm.X
end
-- ===== end of `LvmXNtt5` =====

-- ===== merged from `LvmXDecIR` (GOLF module merge: `LvmXDecIR.lean` is now a stub importing `LvmXDecIR4`) =====
section
-- WP-13b: the decoder's phases on the machine (new composition, on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b: `Enc` of the next level by the forward
-- butterflies, the agreement scan, interpolation, the butterflies per row; FR's ladder of levels is one level
-- here).

/-!
# The decoder's phases: `Enc₀(f₁)`, the inverse NTT of the 64 rows

**Workspace** `[dB, dB + 2^21)` (below `memX = 2^25`): basis table `tbB = dB` (225 words), `eq`
table `qB = dB + 256` (192), the flag `okB = dB + 512`, the weights `wbB = dB + 2^13` and the
`E` row `ebB = dB + 2^14` (2^13 each), the agreement list `agB = dB + 2^15` (2^15), `Enc₀(f₁)`'s
coordinates `encB = dB + 2^16` (3·2^15), the interpolated rows `oB = dB + 2^19` (2^19), the
message `mB = dB + 2^20` (2^19). The inputs (word `wB`, `α` at `aB`, `f₁` at `fB`) lie outside.

* `encC c`: `f₁`'s coordinate `c` (`fB + 3v + c`, `v < 2^13`) zero-padded to `2^15`, then the
  forward NTT (`fwdIR 15`): `encC_sem`, `Enc` over `K` of the coordinate at every position.
* `bflyAll`: the inverse NTT (`bflyIR 13`) on each of the 64 rows at `oB` (`bflyAll_sem`).
* `okIR`: the flag `[2^13 ≤ |A|]` in `rOk` and at `okB`.

Registers `251 … 255`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

/-! ## Layout and registers -/

/-- The basis table. -/ def tbB (dB : ℕ) : ℕ := dB
/-- The `eq(α, ·)` table. -/ def qB (dB : ℕ) : ℕ := dB + 256
/-- The success flag. -/ def okB (dB : ℕ) : ℕ := dB + 512
/-- The interpolation weights. -/ def wbB (dB : ℕ) : ℕ := dB + 2 ^ 13
/-- The interpolation's `E` row. -/ def ebB (dB : ℕ) : ℕ := dB + 2 ^ 14
/-- The agreement list. -/ def agB (dB : ℕ) : ℕ := dB + 2 ^ 15
/-- `Enc₀(f₁)`'s coordinates. -/ def encB (dB : ℕ) : ℕ := dB + 2 ^ 16
/-- The interpolated rows (leaf-word order). -/ def oB (dB : ℕ) : ℕ := dB + 2 ^ 19
/-- **The decoded message** (`2^19` words, natural order). -/ def mB (dB : ℕ) : ℕ := dB + 2 ^ 20

/-- The flag. -/ def rOk : ℕ := 251
/-- The row index. -/ def zT : ℕ := 252
/-- Scratch. -/ def zK : ℕ := 253
/-- The row loop's counter. -/ def zC : ℕ := 254
/-- Its count. -/ def zN : ℕ := 255

/-! ## The programs -/

/-- **`Enc₀(f₁)`'s coordinate `c`** at `encB + c·2^15`: copy, zero padding, forward NTT. -/
def encC (dB fB c : ℕ) : XIR :=
  .seq (mcpIR (2 ^ 13) (fB + c) 3 (encB dB + c * 2 ^ 15))
    (.seq (zeroIR (2 ^ 15 - 2 ^ 13) (encB dB + c * 2 ^ 15 + 2 ^ 13))
      (.seq (.blk [.const rA0 (toWord (encB dB + c * 2 ^ 15))]) (fwdIR 15 (tbB dB))))

/-- The three coordinates. -/
def encIR (dB fB : ℕ) : XIR := .seq (encC dB fB 0) (.seq (encC dB fB 1) (encC dB fB 2))

/-- One row `t`: `rA0 := oB + t·2^13`, the inverse NTT, `t += 1`. -/
def bflyRow (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK, .const zK (toWord (oB dB)),
      .op .add rA0 rA0 zK]) (.seq (bflyIR 13 (tbB dB)) (.blk [.op .add zT zT cOne]))

/-- **The inverse NTT of the 64 rows.** -/
def bflyAll (dB : ℕ) : XIR :=
  .seq (.blk [.const zT 0, .const zN 64]) (.loopK zC zN 64 (bflyRow dB))

/-- **The flag** `rOk := [2^13 ≤ cnt]`, stored at `okB`. -/
def okIR (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 13)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (okB dB))]) (.store zK rOk)

/-- **The decoding proper** (on success): interpolation on the first `2^13` listed positions,
the inverse NTT per row, the reorder into the message. -/
def decTail (dB wB : ℕ) : XIR :=
  .seq (baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB))
    (.seq (bflyAll dB) (rowsIR (oB dB) (mB dB)))

/-! ## Costs -/

theorem cost_encC (dB fB c t : ℕ) : cost (encC dB fB c) t = 90522053 := by
  simp only [encC, cost, cost_mcpIR _ _ _ _ _ (show 2 ^ 13 < 2 ^ 64 by norm_num),
    cost_zeroIR _ _ _ (show 2 ^ 15 - 2 ^ 13 < 2 ^ 64 by norm_num), cost_fwdIR_15, blkSteps,
    List.length_cons, List.length_nil]
  norm_num

theorem cost_bflyAll (dB t : ℕ) : cost (bflyAll dB) t = 1250709900 := by
  simp only [bflyAll, bflyRow, cost, cost_bflyIR_13, blkSteps, List.length_cons, List.length_nil]
  norm_num

end Lvm.X
end
-- ===== end of `LvmXDecIR` =====

-- ===== merged from `LvmXDecIR2` (GOLF module merge: `LvmXDecIR2.lean` is now a stub importing `LvmXDecIR4`) =====
section
-- WP-13b: the decoder's phases composed (new; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b, one level here).

/-!
# The decoder after the `eq` table: semantics of the phases and of `decMain`

* `encC_sem`, `encIR_sem`: `Enc₀(f₁)`'s three coordinates at `encB + c·2^15 + q`.
* `bflyAll_sem`: the 64 rows at `oB` become their novel-basis coefficients.
* `decTail_sem`: on a list of `≥ 2^13` agreeing positions at `agB`, the message at `mB`.
* **`decMain_sem`**: `encIR ; agreeIR ; okIR ; (decTail if ok)`: the flag at `okB` is
  `[2^13 ≤ |agreeL|]`, and on success the `2^19` words at `mB` are `decodeRec`'s.

`DecLay dB wB aB fB sz`: the workspace `[dB, dB + 2^21)` inside the memory, the inputs (word at
`wB`, `2^21` words; `α` at `aB`, 18; `f₁` at `fB`, `3·2^13`) outside it, every address below `2^60`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-! ## `Enc₀(f₁)` -/

theorem bflyIR_nw_hi (ℓ tb : ℕ) {r : ℕ} (hr : 187 ≤ r) : ¬ Writes (bflyIR ℓ tb) r := by
  intro hw
  simp only [bflyIR, lvlStep, levelIR, pairBody, pairPs, alphaIR, alphaBody, arithIR, addK, mulK,
    mulKC, redC, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, List.cons_append,
    List.nil_append, exists_eq_or_imp, exists_eq_left, or_false, false_or] at hw
  simp only [rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI,
    rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp] at hw
  omega

end Lvm.X
end
-- ===== end of `LvmXDecIR2` =====

-- ===== merged from `LvmXDecIR3` (GOLF module merge: `LvmXDecIR3.lean` is now a stub importing `LvmXDecIR4`) =====
section
-- WP-13b: the whole decoder program `decIR` and its semantics (new composition; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b).

/-!
# The decoder of `C_rec` on the machine

`decIR dB wB aB fB`: the basis table; `eq(α, ·)` (`eqtIR`); `Enc₀(f₁)` (`encIR`); the agreement
scan (`agreeIR`); the flag (`okIR`); on success the interpolation, the inverse NTT per row and the
reorder (`decTail`).

**`decIR_sem`**: on a memory holding the word `wd` at `wB + 64q + t`, `α_i` at `aB + 3i` and
`f₁(v)` at `fB + 3v` (`rdE`), with the layout `DecLay`:
* the cell `okB dB` holds `[2^13 ≤ |agreeL wd α f₁|]`, i.e. `decodeRec wd α f₁ ≠ none`;
* if `decodeRec wd α f₁ = some out`, the `2^19` cells at `mB dB` hold `out`;
* the heap outside the workspace `[dB, dB + 2^21)` is kept.

With `decodeRec_correct`/`decodeRec_of_ud`, the cells at `mB dB` are `C_rec`'s message.
**`cost_decIR`**: `≈ 2^37.95` steps, all but `2^31.6` in the interpolation.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The decoder program.** -/
def decIR (dB wB aB fB : ℕ) : XIR :=
  .seq (wtabIR (tbB dB)) (.seq (eqtIR 6 aB (qB dB)) (.seq (encIR dB fB)
    (.seq (agreeIR wB (qB dB) (encB dB) (agB dB)) (.seq (okIR dB) (.ite rOk (decTail dB wB) (.blk []))))))

/-! ## Pure helpers -/

theorem coeffsAt_congr {L M : Type*} [Field L] [Field M] [Algebra L M] (pt : ℕ → L) (N : ℕ) :
    ∀ ℓ s (y y' : ℕ → M), (∀ j < 2 ^ ℓ, y j = y' j) →
      ∀ x < 2 ^ ℓ, coeffsAt pt N ℓ s y x = coeffsAt pt N ℓ s y' x
  | 0, _, _, _, h, x, hx => by simp only [coeffsAt]; exact h x hx
  | ℓ + 1, s, y, y', h, x, hx => by
    have hp : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
    have hu := coeffsAt_congr pt N ℓ s y y' (fun j hj => h j (by omega))
    have hw := coeffsAt_congr pt N ℓ (s + 2 ^ ℓ) (fun j => y (2 ^ ℓ + j)) (fun j => y' (2 ^ ℓ + j))
      (fun j hj => h _ (by omega))
    simp only [coeffsAt]
    split_ifs with hx'
    · rw [hu x hx', hw x hx']
    · rw [hu _ (by omega), hw _ (by omega)]

theorem getD_take_lt {L : List ℕ} {n t : ℕ} (ht : t < n) : (L.take n).getD t 0 = L.getD t 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht]

theorem eqA_congr {α α' : ℕ → Ext3} (h : ∀ i < 6, α i = α' i) (l : ℕ) : eqA α l = eqA α' l := by
  simp only [eqA, eqBits, bitSel]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i (mem_range.1 hi)]

/-! ## The decoding proper -/

end Lvm.X
end
-- ===== end of `LvmXDecIR3` =====

/-!
# `decIR_sem`: the decoder program computes `decodeRec`

See `LvmXDecIR3` for the program. On a memory holding the word, `α` and `f₁` outside the workspace:
the flag at `okB dB` is `[2^13 ≤ |agreeL|]`; on `decodeRec … = some out` the message at `mB dB` is
`out`; the heap outside the workspace is kept.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

theorem rdE_congr {M M' : Mem} {a : ℕ} (h : ∀ k < 3, rd M' (a + k) = rd M (a + k)) :
    rdE M' a = rdE M a := by
  simp only [rdE, rdK]
  rw [show a = a + 0 from rfl, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num)]

theorem bW_xor_one (b : Bool) : bW b ^^^ 1 = bW (!b) := by cases b <;> decide

end Lvm.X
