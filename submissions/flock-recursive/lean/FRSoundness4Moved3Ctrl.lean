-- New for `flock-recursive` (`flock-128` stage I5, the 3.x tree's removal): the controls of the
-- dropped 3.x modules whose statements read only definitions that the 4.x path keeps (moved here,
-- re-proved at `flock-128`'s numbers where the numbers moved). Each block names its origin.
import FRNodeStmtR4
import FRSubmission4V
import FRXSpec
import FRNodeReadLayout

/-!
# Controls moved from the dropped 3.x modules

The 3.x tree (`FRSoundnessStepB` and its importers) left the entry at `flock-128` (I4-RESULT §6). Its
controls of definitions that `Solution`'s closure still uses are kept here, one block per origin.
-/

set_option autoImplicit false

/-! ## From `FRNodeSoundA` -/

namespace FR.Snd
open RecursionFast Finset Circ
set_option linter.constructorNameAsVariable false

/-- Control (positive): any digest's two halves, placed in cells `0` and `1`, read back. -/
theorem digestOf_ctl (d : Digest) :
    Read.digestOf (fun e => if e = 0 then dlo d else dhi d) 0 1 = d :=
  digestOf_halves (by simp) (by simp)

end FR.Snd

/-! ## From `FRNodeSoundA` (with its two helpers) -/

namespace FR.Snd
open RecursionFast Finset Circ
set_option linter.constructorNameAsVariable false

/-- The public cells' values (`PubCells`, A.7's order). -/
theorem pubCells_vals {w : Asg} {vk c₁ c₂ : Digest} (h : Node.PubCells w vk c₁ c₂) :
    w (Node.seedCell 0 2) = dlo c₁ ∧ w (Node.seedCell 0 3) = dhi c₁ ∧
      w (Node.seedCell 1 2) = dlo c₂ ∧ w (Node.seedCell 1 3) = dhi c₂ := by
  simp only [Node.PubCells, Node.pubCells, Node.pubVals, Node.halves, List.range_succ,
    List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.append_nil, List.cons.injEq] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

/-- **The children's statements are `PubCells`' digests.** -/
theorem readStmt_of_pubCells {w : Asg} {vk c₁ c₂ : Digest} (h : Node.PubCells w vk c₁ c₂) :
    Read.readStmt w 1 = c₁ ∧ Read.readStmt w 2 = c₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := pubCells_vals h
  exact ⟨by rw [Read.readStmt_cells w 0]; exact digestOf_halves h1 h2,
    by rw [Read.readStmt_cells w 1]; exact digestOf_halves h3 h4⟩

/-- Control (negative): `readStmt_of_pubCells` reads `c₁`'s cells, not `vk`'s: with different
`vk` and `c₁`, slot 1's statement is `c₁`, so it is not `vk`. -/
theorem readStmt_not_vk {w : Asg} {vk c₁ c₂ : Digest} (h : Node.PubCells w vk c₁ c₂)
    (hne : vk ≠ c₁) : Read.readStmt w 1 ≠ vk := by
  rw [(readStmt_of_pubCells h).1]; exact hne.symm

end FR.Snd

/-! ## From `FRSoundnessAccEq` -/

namespace FR.Snd
open RecursionFast Finset
set_option linter.constructorNameAsVariable false

/-- Control (the order): `eqTab [0, 1]` puts its `1` at index `2` (bit 1 set: coordinate 1), not
at index `1`. -/
theorem eqTab_ctl : (eqTab (#[0, 1] : Array ℤ)).getD 2 0 = 1 ∧ (eqTab (#[0, 1] : Array ℤ)).getD 1 0 = 0 := by
  rw [eqTab_getD _ (by decide), eqTab_getD _ (by decide)]
  simp (config := { decide := true }) [eqBits, bitSel, prod_range_succ, Array.getD_eq_getD_getElem?]

end FR.Snd

/-! ## From `FRSoundnessAccEq` -/

namespace FR.Snd
open RecursionFast Finset
set_option linter.constructorNameAsVariable false

/-- Control (the reversed order disagrees): reading coordinate `v` against bit `1 − v` gives a
different value at index `1`. -/
theorem eqTab_rev_ne :
    (eqTab (#[0, 1] : Array ℤ)).getD 1 0 ≠ eqBits (fun v => (#[1, 0] : Array ℤ).getD v 0) 2 1 := by
  rw [eqTab_ctl.2]
  simp (config := { decide := true }) [eqBits, bitSel, prod_range_succ, Array.getD_eq_getD_getElem?]

end FR.Snd

/-! ## From `FRSoundnessAccFin` -/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
set_option linter.constructorNameAsVariable false

/-- Control (value): on the empty chain every round message is zero, so `rSum = rVal = 0`. -/
theorem rSum_nil (b l : ℕ) : rSum b [] l = 0 ∧ rVal b [] l = 0 := by
  simp [rSum, rVal, g2At, readK_nil, peval]

end FR.Snd

/-! ## From `FRSoundnessAccW` -/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
set_option linter.constructorNameAsVariable false

/-- Control (negative): the two ladders' tails differ at level 1. -/
theorem tLen_ne : tLen 32 1 ≠ tLen 30 1 := by decide

end FR.Snd

/-! ## From `FRSoundnessExtLeaf` -/

namespace FR.Snd
open RecursionFast Finset ProductCircuit Blake2sCircuit
set_option linter.constructorNameAsVariable false

/-- Control (positive / negative): the byte order of `testBit_ofListLE` (little-endian, bit 8 is
byte 1's bit 0, not byte 0's). -/
theorem testBit_ofListLE_ctl : (CompPoly.Bytes.ofListLE [1, 0]).testBit 0 = true ∧
    (CompPoly.Bytes.ofListLE [0, 1]).testBit 8 = true ∧
    (CompPoly.Bytes.ofListLE [1, 0]).testBit 8 = false := by decide

end FR.Snd

/-! ## From `FRSoundnessExtLeaf` -/

namespace FR.Snd
open RecursionFast Finset ProductCircuit Blake2sCircuit
set_option linter.constructorNameAsVariable false

/-- Control (negative): `sum_enc64` reads the bytes in little-endian order: `enc64 (2^16)`'s
bytes summed big-endian are not `2^16`. -/
theorem sum_enc64_neg : ((List.range 8).map fun i =>
    ((enc64 (2 ^ 16)).getD (7 - i) 0).toNat * 256 ^ i).sum ≠ 2 ^ 16 := by decide

end FR.Snd

/-! ## From `FRSoundnessFrB` -/

namespace FR.Snd
open RecursionFast Finset
set_option linter.constructorNameAsVariable false

/-- Control (negative): a leaf's public cells never doom (no cells are claimed). -/
theorem pubOK_leaf (L es : Log) : PubOK .P30 L es := fun h => absurd h (by decide)

end FR.Snd

/-! ## From `FRSoundnessFrPend` -/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
set_option linter.constructorNameAsVariable false

/-- Control: a zero L3 message gives `v_β = 0`. -/
theorem vBetaL_zero {es : Log} (h : ∀ i < 8, readF (msgAt es 97) (16 * i) = 0) : vBetaL es = 0 :=
  sum_eq_zero fun i hi => by rw [h i (mem_range.mp hi), mul_zero]

end FR.Snd

/-! ## From `FRSoundnessFrRS0` -/

namespace FR.Snd
open RecursionFast Finset
set_option linter.constructorNameAsVariable false

/-- Control: the E claim's inner weight is the packing basis. -/
theorem cwL_three (κ : Kind) (es : Log) (i : ℕ) : cwL κ es 3 i = bb i := rfl

end FR.Snd

/-! ## From `FRSoundnessFrS` -/

namespace FR.Snd
open RecursionFast Finset FR.Impl FR.NodeT FR.NodeI
set_option linter.constructorNameAsVariable false

/-- Control (positive): the zero table with zero boundary digests satisfies a leaf's S truth. -/
theorem shHoldsL_zero (nb : ℕ) : ShHoldsL nb (fun _ _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end FR.Snd

/-! ## From `FRSoundnessFrS` -/

namespace FR.Snd
open RecursionFast Finset FR.Impl FR.NodeT FR.NodeI
set_option linter.constructorNameAsVariable false

/-- Control (negative): a start digest with bit 0 set breaks the zero table's leaf S truth. -/
theorem not_shHoldsL_start (nb : ℕ) :
    ¬ ShHoldsL nb (fun _ _ => 0) (fun σ => if σ = 0 then 1 else 0) (fun _ => 0) := fun h => by
  have := h.2.1 0 (by norm_num); simp at this

end FR.Snd

/-! ## From `FRSoundnessFrS` -/

namespace FR.Snd
open RecursionFast Finset FR.Impl FR.NodeT FR.NodeI
set_option linter.constructorNameAsVariable false

/-- Control (positive): at a cube point `θ = σ₀` the slot weight picks the slot's position. -/
theorem slotT_cube {b σ₀ : ℕ} (hσ : σ₀ < 256) : slotT (cubeN 10 σ₀) b (b + σ₀) = 1 := by
  unfold slotT
  rw [sum_eq_single σ₀]
  · rw [eqAtR_cubeN (by omega) (by omega)]; simp
  · intro σ hσ' hne
    rw [eqAtR_cubeN (by omega) (by have := mem_range.1 hσ'; omega)]; simp [hne]
  · intro h; exact absurd (mem_range.2 hσ) h

end FR.Snd

/-! ## From `FRSoundnessFrS` -/

namespace FR.Snd
open RecursionFast Finset FR.Impl FR.NodeT FR.NodeI
set_option linter.constructorNameAsVariable false

/-- Control (negative): off the slot (below its base) the weight is `0`. -/
theorem slotT_off (θ : Fin 10 → F) {b q : ℕ} (hq : q < b) : slotT θ b q = 0 :=
  sum_eq_zero fun σ _ => by rw [if_neg (by omega), mul_zero]

end FR.Snd

/-! ## From `FRSoundnessFrW0V` -/

namespace FR.Snd
open RecursionFast Finset FR.Impl
set_option linter.constructorNameAsVariable false

/-- Control (positive): on a leaf, claim 2's weight is the plain one (`β = 1`). -/
theorem kwSL_leaf (q ρ : List K) (hq : q.length = 25) (hρ : ρ.length = 25) :
    kwSL 1 q ρ = eqPts q ρ := kwSL_one q ρ (by rw [hq, hρ]) (by rw [hρ]; norm_num)

end FR.Snd

/-! ## From `FRSoundnessFrZM` -/

namespace FR.Snd
open Layout
open RecursionFast FR.Merkle Finset FR.Impl ProductCircuit
set_option linter.constructorNameAsVariable false

/-- Control (negative): a pinned row of a kind's matrix is zero (`chain` pins `h_in`, row 0). -/
theorem kMat_pinned (C : Block.Pos → Block.Pos → Bool) (k : Fin (2 ^ 14)) :
    kMat C (bkIdx .chain) ⟨0, by norm_num⟩ k = 0 := by
  simp [kMat, bkOf_idx, isZeroRow, zeroRows]

end FR.Snd

/-! ## From `FRSoundnessFrZM` -/

namespace FR.Snd
open Layout
open RecursionFast FR.Merkle Finset FR.Impl ProductCircuit
set_option linter.constructorNameAsVariable false

/-- Control (positive): an unpinned row of a non-`free` kind is the circuit's row (`stream`
pins only slot 8; row 0 is `h_in`'s bit 0). -/
theorem kMat_row (C : Block.Pos → Block.Pos → Bool) (k : Fin (2 ^ 14)) :
    kMat C (bkIdx .stream) ⟨0, by norm_num⟩ k = ProductCircuit.ofBool F (C ⟨0, by norm_num⟩ k) := by
  simp [kMat, bkOf_idx, isZeroRow, zeroRows]

end FR.Snd

/-! ## From `FRSoundnessFrZM` -/

namespace FR.Snd
open Layout
open RecursionFast FR.Merkle Finset FR.Impl ProductCircuit
set_option linter.constructorNameAsVariable false

/-- Control (positive): the `free` kind's matrix is the identity (`(var k, var k)`). -/
theorem kMat_free_id (C : Block.Pos → Block.Pos → Bool) (z : Fin (2 ^ 14) → F) (p : Fin (2 ^ 14)) :
    ∑ k, kMat C (bkIdx .free) p k * z k = z p := kMat_free C z p

end FR.Snd

/-! ## From `FRSoundnessFront` -/

namespace FR.Snd
open FR.Kinds FR.Stream
open RecursionFast FR.Merkle Finset
open scoped NNReal
set_option linter.constructorNameAsVariable false

/-- **Control: E before RS** (revision 3.13, fixing S-G1j defect 1). E4 is phase 21 (its rounds
from position 265, its last challenge `r′₂₂` at 310), E4 end (`f̂(r′) ‖ 0^16`, 32 bytes) phase 22
at 311, RS0 (the `4 × 128` partials, claim 4's `s_{3,i}` included) phase 23 at 312, RS1 (`r″`,
`κ`) from 313: every claim's point is drawn before RS0 absorbs its slices. -/
theorem e4_before_rs0 :
    (piopPhases[21]?.map (·.name)) = some "E4" ∧ (piopPhases[22]?.map (·.name)) = some "E4end" ∧
    (piopPhases[23]?.map (·.name)) = some "RS0" ∧ (piopPhases[24]?.map (·.name)) = some "RS1" ∧
    phStart 21 = 265 ∧ phStart 22 = 311 ∧ phStart 23 = 312 ∧ phStart 24 = 313 ∧
    fsItems[310]? = some .squeeze ∧ fsItems[311]? = some (.absorb 32) ∧
    fsItems[312]? = some (.absorb (4 * 128 * 16)) ∧ fsItems[313]? = some .squeeze := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (rw [phStart, fsStarts_eq]; rfl) | decide +kernel

end FR.Snd

/-! ## From `FRSoundnessFront` -/

namespace FR.Snd
open FR.Kinds FR.Stream
open RecursionFast FR.Merkle Finset
open scoped NNReal
set_option linter.constructorNameAsVariable false

-- helpers of `evalL_short_zero`, moved with it from `FRSoundnessFront`
theorem lRows_cell_ge {r : Circ.Row} (hr : r ∈ Layout.lRows) {t : ℕ × F}
    (ht : t ∈ r.a ++ r.b ++ r.c) : 2 ^ 15 ≤ t.1 ∧ t.1 < 2 ^ 23 := by
  simp only [Layout.lRows, List.mem_map, List.mem_flatMap, List.mem_range, Layout.lBitCells]
    at hr
  obtain ⟨b, ⟨σ, hσ, j, hj, rfl⟩, rfl⟩ := hr
  simp only [Circ.Lin.cell, Circ.Lin.sub, Circ.Lin.smul, List.append_nil, List.mem_append,
    List.mem_cons, List.map_cons, List.map_nil, List.not_mem_nil, or_false] at ht
  simp only [Layout.lBase, Layout.oneCell, Layout.mBase] at ht ⊢
  rcases ht with ((rfl | rfl) | rfl | rfl) | (rfl | rfl) <;> simp <;> omega

/-- `eq` at a point whose coordinates `15 …` are `0` vanishes at every cube point `≥ 2^15`. -/
theorem eq_short_zero {σ : Array F} (hσ : σ.size ≤ 15) (y : Fin (2 ^ 23)) (hy : 2 ^ 15 ≤ y.val) :
    eq (Eval.ptOf 23 σ) (cube y) = 0 := by
  obtain ⟨l, hl, hb⟩ : ∃ l, 15 ≤ l ∧ y.val.testBit l = true := by
    by_contra hc
    push Not at hc
    have := Nat.lt_pow_two_of_testBit y.val fun i hi => by simpa using hc i hi
    omega
  have hl23 : l < 23 := by
    by_contra hc
    have := Nat.testBit_lt_two_pow (show y.val < 2 ^ l from
      lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hb] at this; exact absurd this (by decide)
  refine Finset.prod_eq_zero (i := ⟨l, hl23⟩) (mem_univ _) ?_
  have h0 : Eval.ptOf 23 σ ⟨l, hl23⟩ = 0 := by
    simp only [Eval.ptOf, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_none (by omega)]; rfl
  simp [h0, cube, hb]

/-- **Negative control of `finE`'s `evalL` point** (S-G1j defect 2, fixed by revision 3.13): at a
cell point of at most 15 coordinates, which `evalL` reads as 23 (`ptOf 23`: the last 8 are `0`),
`evalL` is `(0, 0, 0)` at every row point, because every L row reads cells `≥ 2^15` (the L bits
at `lBase·128 + …`, M's `one` cell). Revision 3.12's `finLr` (iv) passed Lr4's 15 challenges and
was vacuous; `finE` passes E4's 23 (`finE_evalL_point`). -/
theorem evalL_short_zero (τ σ : Array F) (hσ : σ.size ≤ 15) :
    Eval.evalLImpl Layout.lRows τ σ = (0, 0, 0) := by
  have key : ∀ sel : Circ.Row → Circ.Lin, (∀ r, ∀ t ∈ sel r, t ∈ r.a ++ r.b ++ r.c) →
      Eval.matMLE (Eval.entriesOf sel Layout.lRows) (Eval.ptOf 15 τ) (Eval.ptOf 23 σ) = 0 := by
    intro sel hsel
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : 2 ^ 15 ≤ y.val
    · rw [eq_short_zero hσ y hy]; ring
    · have : Eval.entry (Eval.entriesOf sel Layout.lRows) x y = 0 := by
        unfold Eval.entry
        rw [List.filter_eq_nil_iff.mpr, List.map_nil, List.sum_nil]
        intro e he hc
        simp only [decide_eq_true_eq] at hc
        simp only [Eval.entriesOf, List.mem_flatMap, List.mem_map] at he
        obtain ⟨q, hq, t, ht, rfl⟩ := he
        have := (lRows_cell_ge (List.fst_mem_of_mem_zipIdx hq) (hsel _ t ht)).1
        simp only at hc; omega
      rw [this, mul_zero]
  rw [Eval.evalL_eq, Eval.evalRowsSpec, key _ (fun r t h => by simp [h]),
    key _ (fun r t h => by simp [h]), key _ (fun r t h => by simp [h])]

end FR.Snd

/-! ## From `FRSoundnessPIOP` -/

namespace FR.Snd
open Circ Eval
open FR.Kinds FR.Stream
open RecursionFast FR.Merkle Finset
set_option linter.constructorNameAsVariable false

/-- Control (negative): a row `1 · 1 = 0` makes the R1CS fail. -/
theorem not_sat_one_row (w : Asg) (hw : w 0 = 1) :
    ¬ Sat (rowMat Row.a [⟨Lin.cell 0, Lin.cell 0, []⟩] 0 1)
      (rowMat Row.b [⟨Lin.cell 0, Lin.cell 0, []⟩] 0 1)
      (rowMat Row.c [⟨Lin.cell 0, Lin.cell 0, []⟩] 0 1) (fun y => w y) := by
  rw [sat_rowMat_iff _ ⟨by simp, by simp [Lin.cell]⟩]
  intro h
  have := h _ List.mem_cons_self
  simp [Row.Holds, hw] at this

end FR.Snd

/-! ## From `FRSoundnessPIOP` -/

namespace FR.Snd
open Circ Eval
open FR.Kinds FR.Stream
open RecursionFast FR.Merkle Finset
set_option linter.constructorNameAsVariable false

/-- Control (positive): the empty row list is satisfied by every assignment. -/
theorem sat_nil (a b : ℕ) (w : Asg) :
    Sat (rowMat Row.a [] a b) (rowMat Row.b [] a b) (rowMat Row.c [] a b) (fun y => w y) :=
  (sat_rowMat_iff [] ⟨by simp, by simp⟩ w).mpr (by simp)

end FR.Snd

/-! ## From `FRSoundnessRows` -/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal
set_option linter.constructorNameAsVariable false

/-- Control (positive): a failing row dooms a kind the unit runs on (`sat_rowMat_iff`). -/
theorem rowsBad_of_row {rows : List Circ.Row} {a nc : ℕ} {on : Kind → Bool} (hf : RowsFit rows a nc)
    {L es : Log} (hon : on (kindOf es) = true) {r : Circ.Row} (hr : r ∈ rows)
    (hn : ¬ r.Holds (fun c => fF (kindOf es) L es c)) : RowsBad rows a nc on L es :=
  ⟨hon, fun h => hn ((sat_rowMat_iff rows hf _).mp h r hr)⟩

end FR.Snd

/-! ## From `FRSoundnessRows` -/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal
set_option linter.constructorNameAsVariable false

/-- Control (negative): a kind the unit does not run on is never doomed by it. -/
theorem not_rowsBad_off {rows : List Circ.Row} {a nc : ℕ} {on : Kind → Bool} {L es : Log}
    (hon : on (kindOf es) = false) : ¬ RowsBad rows a nc on L es := fun h => by
  rw [h.1] at hon; exact Bool.noConfusion hon

end FR.Snd

/-! ## From `FRSoundnessRows` -/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal
set_option linter.constructorNameAsVariable false

/-- Control (negative): before the end absorb no triple is wrong. -/
theorem not_endBad_short {rows : List Circ.Row} {a nc b2 : ℕ} {on : Kind → Bool} {L es : Log}
    (h : es.length ≤ b2 + 2 * a) : ¬ EndBad rows a nc on b2 L es := fun hd => by
  have := hd.2.1; omega

end FR.Snd
