-- lvm6 X1 (BLUEPRINT §3 `FD1`): the registers the decoder programs write. New.
import Lvm6FDSemBase

/-!
# Registers written by `lamIR` and `laneIR`

`nw_lamIR`, `nw_laneIR`: neither program names a register `r` with `208 ≤ r` or
`187 ≤ r < 190` as a destination (`Writes`), so the extractor can keep its own state (loop counters
over rounds and lanes, pointers) there across calls (`Lvm.X.frame`). The programs write the field
scratch `5 … 24`, `cTmp`, season 1's NTT registers `140 … 186` and the decoder's `190 … 207`.

`AllBelow b P`: every destination of `P` (loop counters and `cTmp` included) is below `b`
(`nw_of_allBelow`).
-/

namespace Lvm6.FD

open RecursionFast Lvm.X Lvm.Nb

/-- Every cell `P` names as a destination is below `b`. -/
def AllBelow (b : ℕ) : XIR → Prop
  | .blk ps => ∀ p ∈ ps, p.dst < b
  | .load d _ => d < b
  | .store _ _ => cTmp < b
  | .input d _ => d < b
  | .out _ => True
  | .seq p q => AllBelow b p ∧ AllBelow b q
  | .ite _ p q => AllBelow b p ∧ AllBelow b q
  | .loopK c _ _ body => c < b ∧ cTmp < b ∧ AllBelow b body
  | .loopT c _ _ body => c < b ∧ AllBelow b body

theorem nw_of_allBelow {b r : ℕ} (hr : b ≤ r) : ∀ {P : XIR}, AllBelow b P → ¬ Writes P r
  | .blk _, h, ⟨p, hp, he⟩ => by have := h p hp; omega
  | .load .., h, he => by simp only [AllBelow] at h; simp only [Writes] at he; omega
  | .store .., h, he => by simp only [AllBelow] at h; simp only [Writes] at he; omega
  | .input .., h, he => by simp only [AllBelow] at h; simp only [Writes] at he; omega
  | .out _, _, he => he
  | .seq _ _, h, he => he.elim (nw_of_allBelow hr h.1) (nw_of_allBelow hr h.2)
  | .ite _ _ _, h, he => he.elim (nw_of_allBelow hr h.1) (nw_of_allBelow hr h.2)
  | .loopK .., h, he => by
    rcases he with he | he | he
    · have := h.1; omega
    · have := h.2.1; omega
    · exact nw_of_allBelow hr h.2.2 he
  | .loopT .., h, he => by
    rcases he with he | he
    · have := h.1; omega
    · exact nw_of_allBelow hr h.2 he

theorem allBelow_mono {b b' : ℕ} (hb : b ≤ b') : ∀ {P : XIR}, AllBelow b P → AllBelow b' P
  | .blk _, h => fun p hp => by have := h p hp; omega
  | .load .., h => by simp only [AllBelow] at *; omega
  | .store .., h => by simp only [AllBelow] at *; omega
  | .input .., h => by simp only [AllBelow] at *; omega
  | .out _, _ => trivial
  | .seq _ _, h => ⟨allBelow_mono hb h.1, allBelow_mono hb h.2⟩
  | .ite _ _ _, h => ⟨allBelow_mono hb h.1, allBelow_mono hb h.2⟩
  | .loopK .., h => ⟨by have := h.1; omega, by have := h.2.1; omega, allBelow_mono hb h.2.2⟩
  | .loopT .., h => ⟨by have := h.1; omega, allBelow_mono hb h.2⟩

theorem allBelow_mulK_iff {b d a b' : ℕ} (hb : 9 ≤ b) (hd : d < b) : AllBelow b (mulK d a b') ↔ True :=
  iff_true_intro fun p hp => by rcases mulKC_dst d a b' p hp with h | h <;> omega

theorem allBelow_invK_iff {b d a : ℕ} (hb : 12 ≤ b) (hd : d < b) : AllBelow b (invK d a) ↔ True :=
  iff_true_intro fun p hp => by rcases invKC_dst d a p hp with h | h <;> omega

theorem allBelow_wtabNIR (N tb : ℕ) : AllBelow 187 (wtabNIR N tb) := by
  simp (disch := decide) only [wtabNIR, row0NIR, row0Body, rowNIR, rowNBody, AllBelow,
    allBelow_mulK_iff (show 9 ≤ 187 by decide), allBelow_invK_iff (show 12 ≤ 187 by decide), List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Prim.dst, rTr, rLv, rN3, rC3, uI, rTa, rN2, rC2, fG, fU, fW, fH,
    fAl, fN, uT1, rAH, cTmp]
  decide

theorem allBelow_bflyNIR (N ℓ tb : ℕ) : AllBelow 187 (bflyNIR N ℓ tb) := by
  simp (disch := decide) only [bflyNIR, lvlNStep, levelNIR, pairNBody, pairPs, alphaNIR, alphaBody, arithIR, addK,
    AllBelow, allBelow_mulK_iff (show 9 ≤ 187 by decide), allBelow_invK_iff (show 12 ≤ 187 by decide), List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Prim.dst, rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX, uT2, rBs,
    rAL, rAH, rA0, rBit, uI, rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp]
  decide

theorem allBelow_fwdNIR (N ℓ tb : ℕ) : AllBelow 187 (fwdNIR N ℓ tb) := by
  simp (disch := decide) only [fwdNIR, fStepN, fPreN, flevelNIR, fpairNBody, pairPs, alphaNIR, alphaBody, farithIR,
    addK, AllBelow, allBelow_mulK_iff (show 9 ≤ 187 by decide), allBelow_invK_iff (show 12 ≤ 187 by decide), List.mem_cons, List.mem_nil_iff,
    or_false, forall_eq_or_imp, forall_eq, Prim.dst, rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX,
    uT2, rBs, rAL, rAH, rA0, rBit, uI, rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp, rKf, rTbf]
  decide

theorem allBelow_treeIR (N ℓ B : ℕ) : ∀ h, AllBelow 208 (treeIR N ℓ B h)
  | 0 => fun p hp => by simp at hp
  | h + 1 => by
    refine ⟨allBelow_treeIR N ℓ B h, ?_⟩
    simp (disch := decide) only [tLevelIR, parentBody, copyBody, prodBody, AllBelow,
      allBelow_mulK_iff (show 9 ≤ 208 by decide), allBelow_invK_iff (show 12 ≤ 208 by decide), List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, Prim.dst, zA, zB, zC, zD, zE, zT, zU, zV, zW, zP, zC1, zN1, zC2,
      zN2, rA0, cTmp]
    have b1 := allBelow_mono (show 187 ≤ 208 by decide) (allBelow_bflyNIR N (h + 1) (tbA B))
    have f1 := allBelow_mono (show 187 ≤ 208 by decide) (allBelow_fwdNIR N (h + 2) (tbA B))
    simp only [b1, f1, and_true, true_and]
    decide

theorem allBelow_lamIR (N ℓ m B : ℕ) : AllBelow 208 (lamIR N ℓ m B) := by
  refine ⟨allBelow_mono (by decide) (allBelow_wtabNIR N _), ?_, ?_, allBelow_treeIR N ℓ B ℓ, ?_⟩
  all_goals simp (disch := decide) only [leavesIR, leafBody, dummiesIR, dummyBody, invsIR, invBody, AllBelow,
    allBelow_invK_iff (show 12 ≤ 208 by decide),
    List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Prim.dst, zA, zB, zC,
    zD, zT, zU, zW, zI, zC1, zN1, cTmp]
  all_goals decide

theorem allBelow_laneIR (N ℓ m B : ℕ) : AllBelow 208 (laneIR N ℓ m B) := by
  have b1 := allBelow_mono (show 187 ≤ 208 by decide) (allBelow_bflyNIR N ℓ (tbA B))
  have b2 := allBelow_mono (show 187 ≤ 208 by decide) (allBelow_bflyNIR N (ℓ + 1) (tbA B))
  have f1 := allBelow_mono (show 187 ≤ 208 by decide) (allBelow_fwdNIR N (ℓ + 1) (tbA B))
  simp (disch := decide) only [laneIR, zeroGIR, zeroBodyG, synIR, synBody, corrIR, cosIR, cosBody, AllBelow,
    allBelow_mulK_iff (show 9 ≤ 208 by decide), allBelow_invK_iff (show 12 ≤ 208 by decide), List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Prim.dst, b1, b2, f1, and_true, false_implies, implies_true, true_and, zA, zB, zC, zD, zE,
    zT, zU, zV, zW, zI, zK, zS0, zS1, zC1, zN1, rA0, cTmp]
  decide

/-- **`lamIR` writes no register `≥ 208`.** -/
theorem nw_lamIR (N ℓ m B : ℕ) {r : ℕ} (hr : 208 ≤ r) : ¬ Writes (lamIR N ℓ m B) r :=
  nw_of_allBelow hr (allBelow_lamIR N ℓ m B)

/-- **`laneIR` writes no register `≥ 208`.** -/
theorem nw_laneIR (N ℓ m B : ℕ) {r : ℕ} (hr : 208 ≤ r) : ¬ Writes (laneIR N ℓ m B) r :=
  nw_of_allBelow hr (allBelow_laneIR N ℓ m B)

end Lvm6.FD
