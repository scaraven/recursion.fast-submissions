-- New for `flock-recursive` (R-OPS §5.2, stage R3: `rsWeight`'s replay at the previous-node slot).
import FRVerifierImplOps4

/-!
# `rsWeight` in the replay template's form

The replay template of `rsWeight` (`FRNodeRows4RepRs`) computes `rsWeightF4 ν` from the operands'
cells for **every** claim point in `K` (the template has no branch on data: `rsWeightF4`'s `F` fast
path is a branch on `f₁ = 0`). Claim 2's kind factor (`kwSL4I`) is a sum over the skeleton's blocks
of products over each block's fixed bits; computed afresh at each of the 128 Frobenius stages it
would cost ≈ 2,000 `K` products per stage. The template instead uses that `x ↦ x^(2^k)` is a ring
map (characteristic two):

* per block `p`, once: `W₀(p) = (Σ_{i ∈ p} β^i)·Π_{b fixed} q_b` and `G(p) = Π_{b fixed} ρ_b`
  (`q_b`, `ρ_b`: the coordinate or one minus it, by the fixed bit);
* per stage `k`: the block's term is `W₀(p)^(2^k)·G(p)` (`block_frob`), one squaring chain per block.

This module states the template's arithmetic as a function of values, **`rsRef`**, and proves
**`rsWeightF4_ref`**: `rsWeightF4 ν r ps κ β ρ = rsRef ν r ps κ β ρ` when `|r| = 7`.
-/

namespace FR
namespace RsR
open Finset RecursionFast Rev4 Impl

/-! ## Frobenius -/

theorem sqIter_hom {R : Type*} [CommRing R] [ExpChar R 2] (k : ℕ) (x : R) :
    sqIter k x = iterateFrobenius R 2 k x := by
  rw [sqIter_eq, iterateFrobenius_def]

theorem sqIter_zeroK (k : ℕ) : sqIter k (0 : K) = 0 := by rw [sqIter_eq]; simp

/-! ## The template's values -/

/-- A fixed bit's factor: the coordinate (bit `1`) or one minus it (bit `0`). -/
def selV (x : ℕ → K) (b : ℕ × Bool) : K := if b.2 then x b.1 else 1 - x b.1

/-- A block's stage-0 `F`-side weight: `(Σ_{i ∈ exps} β^i)·Π_{fixed} q_b`. -/
def w0V (β : F) (q : ℕ → K) (p : List (ℕ × Bool) × List ℕ) : K :=
  K.ofF ((p.2.map (β ^ ·)).sum) * (p.1.map (selV q)).prod

/-- A block's `ρ` side: `Π_{fixed} ρ_b` (stage-independent). -/
def gV (ρ : ℕ → K) (p : List (ℕ × Bool) × List ℕ) : K := (p.1.map (selV ρ)).prod

/-- **Claim 2's block factor at stage `k`**, the template's way: Horner over the levels with
`s_l = 1 + q_l^(2^k) + ρ_l`, each level `Σ_p W₀(p)^(2^k)·G(p)`. -/
def kindV (sk : List (List (List (ℕ × Bool) × List ℕ))) (β : F) (q ρ : ℕ → K) (k : ℕ) : K :=
  KW.hornerK (fun l => 1 + sqIter k (q l) + ρ l) 0
    (sk.map fun g => (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum)

/-- Claim `j`'s stage-`k` term. -/
def termV (ν : NodeKind) (β : F) (ρ p : List K) (j k : ℕ) : K :=
  if j = 1 then
    eqPtsC ((p.map (sqIter k)).take 7) (ρ.take 7) *
      kindV (skelAt ν (ρ.length - 7)) β (fun l => (p.drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0) k
  else eqPtsC (p.map (sqIter k)) ρ

/-- **`rsWeight` as the template computes it.** -/
def rsRef (ν : NodeKind) (r : List F) (ps : List (List K)) (κ β : F) (ρ : List K) : K :=
  (ps.zipIdx.map fun p => K.ofF (κ ^ p.2) *
    ((List.range 128).map fun k => K.ofF ((phiTable r).toList.getD k 0) * termV ν β ρ p.1 p.2 k).sum).sum

/-! ## The identities -/

theorem ew_sel (q ρ : ℕ → K) (b : ℕ × Bool) : KW.ew q ρ b.1 b.2 = selV q b * selV ρ b := by
  obtain ⟨l, c⟩ := b; cases c <;> rfl

theorem sqIter_mulK (k : ℕ) (a b : K) : sqIter k (a * b) = sqIter k a * sqIter k b := by
  simp only [sqIter_hom, map_mul]

theorem sqIter_prodK (k : ℕ) (l : List K) : sqIter k l.prod = (l.map (sqIter k)).prod := by
  rw [sqIter_hom, map_list_prod]
  exact congrArg _ (List.map_congr_left fun x _ => (sqIter_hom k x).symm)

theorem sqIter_expSum (k : ℕ) (β : F) (es : List ℕ) :
    sqIter k (es.map (β ^ ·)).sum = (es.map ((sqIter k β) ^ ·)).sum := by
  simp only [sqIter_hom, map_list_sum, List.map_map]
  exact congrArg _ (List.map_congr_left fun i _ => by simp [map_pow])

theorem sqIter_sel (k : ℕ) (q : ℕ → K) (b : ℕ × Bool) :
    sqIter k (selV q b) = selV (fun l => sqIter k (q l)) b := by
  unfold selV; split_ifs <;> simp [sqIter_hom, map_sub, map_one]

/-- **One block at stage `k`**: the kind factor's block term is `W₀^(2^k)·G`. -/
theorem block_frob (k : ℕ) (β : F) (q ρ : ℕ → K) (p : List (ℕ × Bool) × List ℕ) :
    K.ofF ((p.2.map ((sqIter k β) ^ ·)).sum) * (p.1.map fun b => KW.ew (fun l => sqIter k (q l)) ρ b.1 b.2).prod =
      sqIter k (w0V β q p) * gV ρ p := by
  simp only [ew_sel, List.prod_map_mul, w0V, gV, sqIter_mulK, sqIter_ofF, sqIter_expSum, sqIter_prodK,
    List.map_map, Function.comp_def, sqIter_sel]
  ring

theorem ew_s (q ρ : ℕ → K) (l : ℕ) : KW.ew q ρ l false + KW.ew q ρ l true = 1 + q l + ρ l := by
  simp only [KW.ew, Bool.false_eq_true, ite_false, ite_true]
  linear_combination (q l * ρ l - q l - ρ l) * CharTwo.two_eq_zero (R := K)

/-- **`kwSL4I` at the stage-`k` point is the template's value.** -/
theorem kwSL4I_ref (ν : NodeKind) (β : F) (p ρ : List K) (k : ℕ) :
    kwSL4I ν (sqIter k β) (p.map (sqIter k)) ρ =
      eqPtsC ((p.map (sqIter k)).take 7) (ρ.take 7) *
        kindV (skelAt ν (ρ.length - 7)) β (fun l => (p.drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0) k := by
  unfold kwSL4I
  dsimp only
  congr 1
  have hq : ∀ l, ((p.map (sqIter k)).drop 7).toArray.getD l 0 = sqIter k ((p.drop 7).getD l 0) := fun l => by
    rw [toArray_getD_list, ← List.map_drop, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases (p.drop 7)[l]? <;> simp [sqIter_zeroK]
  have hρ : ∀ l, (ρ.drop 7).toArray.getD l 0 = (ρ.drop 7).getD l 0 := fun l => toArray_getD_list _ l
  simp only [hq, hρ, KW4.kwKS, kindV, ew_s]
  congr 1
  refine List.map_congr_left fun g _ => congrArg _ (List.map_congr_left fun b _ => ?_)
  exact block_frob k β _ _ b

theorem arrF_getD (a : Array F) (k : ℕ) : a.getD k 0 = a.toList.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- One claim's stage sum, spec against template. -/
theorem claim_ref (ν : NodeKind) (c : Array F) (β : F) (ρ : Array K) (a : Array K) (j : ℕ) :
    ∑ k ∈ range 128, K.ofF (c.getD k 0) *
      (if j = 1 then kwSL4 ν (sqIter k β) (a.toList.map (sqIter k)) ρ.toList
       else eqPts (a.toList.map (sqIter k)) ρ.toList) =
    ((List.range 128).map fun k => K.ofF (c.toList.getD k 0) * termV ν β ρ.toList a.toList j k).sum := by
  rw [KW.lsum_range]
  refine sum_congr rfl fun k _ => ?_
  rw [arrF_getD]
  congr 1
  unfold termV
  split_ifs with h
  · rw [← kwSL4I_eq, kwSL4I_ref]
  · rw [eqPtsC_eq]

/-- **`rsWeightF4` is the template's value** (`|r| = 7`, any claims and `ρ`). -/
theorem rsWeightF4_ref (ν : NodeKind) (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K)
    (hr : r.size = 7) :
    rsWeightF4 ν r ps κ β ρ = rsRef ν r.toList (ps.map Array.toList) κ β ρ.toList := by
  rw [rsWeightF4_meets ν r ps κ β ρ hr]
  unfold rsWeightS4 rsRef
  rw [List.zipIdx_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  obtain ⟨a, j⟩ := p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [show K.ofF κ ^ j = K.ofF (κ ^ j) from (map_pow K.ofFRingHom κ j).symm, claim_ref]

end RsR
end FR
