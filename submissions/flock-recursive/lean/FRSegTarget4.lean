-- G6: this module also holds the former modules `FRVerifierImplCore` (one section each, in import order).
import FRNodeTargetCore
import FRVIRTplFast

section G6_FRVerifierImplCore

-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 4; stage RET-3): the declarations of
-- the 3.x verifier-shape modules that the revision 4 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRVerifierImpl` (8), `FRNodePlan` (3). Content: the assembled
-- `implC`/`specC`/`Meets` and the node plan pieces revision 4 reads. The 3.x modules import this
-- one.

/-! ## From `FRVerifierImpl` (8 declarations) -/

section

namespace FR

namespace Impl

open Finset RecursionFast RecursionFast.Blake2s

/-- **`implC`**: the computable ops. `fin` fixes the node's M rows (`evalM`, `TEval.planOf`),
`lRows` the L rows (`evalL`, templated by `TEval.planL`, S-E6); `κs₀` is no longer used (`shiftTarget` takes `κ_s`
as an operand since S-0's interface pass). `targetS` and `linkWAll` are selected by `κ.isNode`
(S-CN's `targetSNodeI`, `linkWAllI` on the packed points; a leaf's `linkWAll` is `0^8`); `slotW`
is kind-free (`finSh` selects the In slot map by `keep`, revision 3.14); `shiftMask` is the node's
chain-masked weights (`shiftMaskI`, read by a node only);
`kindFoldWeight` is withdrawn (revision 3.16) and is `0`; `rsWeight` carries claim 2's kind factor. -/
def implCWith (pl : TEval.Plan) (lp : TEval.LPlan) : OpImpl where
  lagrangeS := lagrangeSI
  targetS κ := if κ.isNode then NodeI.targetSNodeI else targetSLeafI
  eqZ := eqZI
  tensorW := tensorWG
  rsWeight := rsWeightF
  phiRS := phiRSF
  walkAB := Eval.walkImpl
  kindInd := Eval.kindIndImpl
  evalM := TEval.evalMT pl
  evalL := TEval.evalLT lp
  shiftTarget := shiftTargetI
  slotW _ := slotWI
  kindFoldWeight _ _ _ := 0
  linkWAll κ tt rr := if κ.isNode then
    NodeI.linkWAllI (tt.extract 0 16) (tt.extract 16 26) (rr.extract 0 16) (rr.extract 16 26)
    else Array.replicate nLinkFam 0
  shiftMask := NodeI.shiftMaskI
  rowW := rowWI
  shiftEq := shiftEqI

/-- **`implC` without plans** (SEG-R1, SEG-R0 §4): `implCWith`'s fields with `evalM` and `evalL`
zero. Every compiled verifier is built on it: the segment's ops (`Rev4.implSeg`) pin both fields to
zero and the node's (`NI4F.implN4F`) set their own, so neither reads the base's. With no plan in it,
no plan is computed at process start (`nodePlan`, `lPlan`, `implCN` below are `noncomputable`:
a compiled nullary constant is initialised at every start, INIT §1). -/
def implC0 : OpImpl where
  lagrangeS := lagrangeSI
  targetS κ := if κ.isNode then NodeI.targetSNodeI else targetSLeafI
  eqZ := eqZI
  tensorW := tensorWG
  rsWeight := rsWeightF
  phiRS := phiRSF
  walkAB := Eval.walkImpl
  kindInd := Eval.kindIndImpl
  evalM _ _ := (0, 0, 0)
  evalL _ _ := (0, 0, 0)
  shiftTarget := shiftTargetI
  slotW _ := slotWI
  kindFoldWeight _ _ _ := 0
  linkWAll κ tt rr := if κ.isNode then
    NodeI.linkWAllI (tt.extract 0 16) (tt.extract 16 26) (rr.extract 0 16) (rr.extract 16 26)
    else Array.replicate nLinkFam 0
  shiftMask := NodeI.shiftMaskI
  rowW := rowWI
  shiftEq := shiftEqI

/-- `implC` at the node's plan (`TEval.planOf fin`: both slots' templated compile, once) and L's
plan (`TEval.planL lRows`, once). -/
def implC (fin : Finals) (lRows : List Circ.Row) (_κs₀ : F) : OpImpl :=
  implCWith (TEval.planOf fin) (TEval.planL lRows)

/-- **`specC`**: the specifications, field by field (the same parameters; `targetS` the leaf
kinds' with `m = 30`, any `m` gives the same function; `linkWAll` the node's `linkWAllS`, a
leaf's `0^8`; `shiftMask` the node's `shiftMaskS`). -/
noncomputable def specCWith (pl : TEval.Plan) (lRows : List Circ.Row) : OpSpec where
  lagrangeS := lagrangeSS
  targetS κ := if κ.isNode then NodeT.targetSNodeS else targetSLeafS 16
  eqZ := eqZS
  tensorW := tensorWS
  rsWeight := rsWeightS
  phiRS := phiRSS
  walkAB rw cw := (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw)
  kindInd := Eval.kindIndSpec
  evalM := TEval.evalMS pl
  evalL := Eval.evalRowsSpec 15 23 lRows
  shiftTarget := shiftTargetS
  slotW _ := slotWS
  kindFoldWeight _ _ _ := 0
  linkWAll κ tt rr := if κ.isNode then NodeT.linkWAllS tt rr else Array.replicate nLinkFam 0
  shiftMask := NodeT.shiftMaskS
  rowW := rowWS
  shiftEq := shiftEqS

noncomputable def specC (fin : Finals) (lRows : List Circ.Row) (_κs₀ : F) : OpSpec :=
  specCWith (TEval.planOf fin) lRows

/-- **`implC ⊨ specC`** (`OpImpl.Meets`, per op under `gen`'s operand lengths). -/
theorem implCWith_meets (pl : TEval.Plan) (lRows : List Circ.Row) :
    (implCWith pl (TEval.planL lRows)).Meets (specCWith pl lRows) := by
  simp only [OpImpl.Meets, implCWith, specCWith]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun v l pe _ => lagrangeS_meets v l pe
  · intro κ r
    split_ifs
    · exact NodeI.targetSNode_meets r
    · exact targetSLeaf_meets 16 r
  · exact eqZ_meets
  · exact fun j r => (tensorWG_eq j r).trans ((tensorWF_eq j r).trans (tensorW_meets j r))
  · exact fun r ps k b p h hp => (rsWeightF_eq r ps k b p).trans (rsWeight_meets r ps k b p h hp)
  · exact fun r a _ => (phiRSF_eq r a).trans (phiRS_meets r a)
  · intro rw cw _ _
    rewrite [← Eval.walkA_eq rw cw, ← Eval.walkB_eq rw cw]
    exact Prod.mk.eta.symm
  · exact TEval.evalMT_eq _
  · intro a b; rw [TEval.evalLT_eq, TEval.planL_rows]
  · exact Eval.kindInd_eq
  · exact fun k a b c _ => shiftTarget_meets k a b c
  · exact fun _ => slotW_meets
  · simp
  · intro κ tt rr
    split_ifs
    · exact NodeI.linkWAll_eqS tt rr
    · rfl
  · exact NodeI.shiftMask_meets
  · exact rowW_meets
  · exact fun a b h => shiftEq_meets a b h

/-- `implC` is the templates' implementation (`ImplT`, the hypothesis of `compileT_sound`). -/
theorem implCWith_implT (pl : TEval.Plan) (lp : TEval.LPlan) : Circ.ImplT (implCWith pl lp) := by
  constructor <;> intros <;> simp only [implCWith]
  · exact funext fun r => funext (phiRSF_eq r)
  exact funext fun j => funext fun r => (tensorWG_eq j r).trans (tensorWF_eq j r)

theorem implC_meets (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    (implC fin lRows κs₀).Meets (specC fin lRows κs₀) := implCWith_meets _ _

/-- The finals with S-G's `finP` and a `finPf` (S-G1d is writing it; a parameter until then). -/
def finC (pf : FinField) : Finals := sfFinals finP pf

end Impl

end FR

end

/-! ## From `FRNodePlan` (3 declarations) -/

section

namespace FR

namespace Impl

/-- **The node's M plan** (`TEval.planOf` of the node's finals). SEG-R1: `noncomputable` (no
initialiser; the compiled verifiers use `implC0`). -/
noncomputable def nodePlan : TEval.Plan := TEval.planOf (finC finPf)

/-- **L's plan** (SEG-R1: `noncomputable`, as `nodePlan`). -/
noncomputable def lPlan : TEval.LPlan := TEval.planL Layout.lRows

/-- **`implC` at the closed plans** (the certificate's base ops; SEG-R1: `noncomputable`). -/
noncomputable def implCN : OpImpl := implCWith nodePlan lPlan

end Impl

end FR

end

end G6_FRVerifierImplCore

section G6_FRSegTarget4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.8 `targetS`/`shiftMask`; stage S-F4).

/-!
# A segment's variable last block: its target and its shift weights (S-C's half of B-12)

A segment proves `1 ≤ n ≤ 2^(m − 14)` chain steps on blocks `0 … n − 1`; the blocks `≥ n` are
**free**, and the honest prover fills them with **zeros** (P2′ §13.3). The program reads
`L = n − 1` from the statement (`FRVIR4.lastOps`: 18 F bits, zero above the kind's `m − 14`) and
passes it to two ops as trailing entries of their operands; every other weight is unchanged.
**What each weight does on the blocks** (on Boolean points, so as multilinear extensions):

* **`targetS`** (Z2's public target, `targetSSegS`): the chain block's target `E_chain` on blocks
  `t ≤ L`, **`0` past `L`** (`targetSSeg_spec`). So a free block meets the homogeneous R1CS
  `(A z)(B z) = z`, which the zero block does. The verifier's form: the leaf target times the range
  factor `Σ_{t ≤ L} eq(r_blk, t)` (`segRangeI`, prefix sums, `segRangeI_eq`; `range_cube`: `[u ≤ L]`).
* **The shift** (`finSh`, `shiftSegS` through `shiftMask`): `w_out`'s `E = eq(τ, r)` unmasked; `w_in`'s
  successor **masked at `L`**: `[y′ = y + 1 ∧ y ≠ L]` (`shiftSeg_cube`), so there is no link from
  block `L` to block `L + 1`; `E₀ = eq(r, 0)`; the target is `eq(τ, L)·h̃ + κ_s·s̃`
  (`shiftTarget`'s `bnd[4 …]` = `L`'s bits). The residual per block `y` is
  `Out(y) + [y ≠ L] In(y + 1) + [y = L] h`: links for `y < L`, `Out(L) = h`; past `L`, `Out(y) =
  In(y + 1)` and the top block's `Out = 0`, which the zero blocks meet. Without the mask the residual
  at `L` would be `Out(L) + In(L + 1) + h`, and a nonzero `In(L + 1)` in a free block would move the
  end (`shift_unmasked_link`: the unmasked weight links `L` to `L + 1`).
* **The lincheck and claim 2 / L3** (`finLc`, `rsWeight`): unchanged. Every block of a segment is a
  chain block (one matrix), `v = [v_chain, 0⁷]`, `β` gated to `1`; the matrix identity holds for any
  `z`, so no mask is needed, and a zero block adds nothing to any sum.
* **RS, Ligerito**: unchanged (`z` is committed whole).

With the zero witness the prover's messages are those of an unmasked prover (the masked entry
multiplies `In(L + 1) = 0`), except Z2's target, which P2′ already scales (`range_eq`).

`implSeg impl₀`: `impl₀` with the segment's `targetS` and `shiftMask`, and `evalM`/`evalL` pinned to
zero (SEG-R1); **`implSeg_meets`**.
-/

namespace FR
namespace Rev4
open Finset Impl

/-! ## The last block -/

/-- The number whose bit `l < 18` is set iff entry `o + l` of `a` is `1`. -/
def lastAt (a : Array F) (o : ℕ) : ℕ := ∑ l ∈ range 18, if a.getD (o + l) 0 = 1 then 2 ^ l else 0

theorem lastAt_lt (a : Array F) (o : ℕ) : lastAt a o < 2 ^ 18 := by
  have key : ∀ n, ∑ l ∈ range n, (if a.getD (o + l) 0 = 1 then 2 ^ l else 0) < 2 ^ n := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, pow_succ]; split_ifs <;> omega
  exact key 18

/-! ## `targetS` -/

/-- The segment point's block coordinates (entries `1 … 18`; Z1's, zero-padded). -/
def blkOf (r : Array F) : Fin 18 → F := fun l => r.getD (1 + l) 0

/-- **The range factor** `Σ_{t ≤ L} eq(r_blk, t)` by prefix sums (`L` from entries `19 … 36`). -/
def segRangeI (r : Array F) : F :=
  prefixP 18 (fun l b => if b then blkOf r l else 1 - blkOf r l) (lastAt r 19 + 1)

/-- Its specification. -/
def segRangeS (r : Array F) : F := ∑ t ∈ range (lastAt r 19 + 1), eqAtR (blkOf r) t

theorem sum_fin_lt {M : Type*} [AddCommMonoid M] (g : ℕ → M) {c N : ℕ} (hc : c ≤ N) :
    ∑ x : Fin N, (if x.val < c then g x else 0) = ∑ t ∈ range c, g t := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x < c then g x else 0) N, ← Finset.sum_filter]
  congr 1; ext x; simp only [mem_filter, mem_range]; omega

theorem segRangeI_eq (r : Array F) : segRangeI r = segRangeS r := by
  rw [segRangeI, prefixP_eq, segRangeS, sum_fin_lt (fun x => ∏ l : Fin 18, if x.testBit l then blkOf r l else 1 - blkOf r l)
    (show lastAt r 19 + 1 ≤ 2 ^ 18 from lastAt_lt r 19)]
  rfl

/-- **`targetS` of a segment** (verifier form): the leaf target times the range factor. -/
def targetSSegI (r : Array F) : Array F := (targetSLeafI r).map (· * segRangeI r)

/-- **Its specification**: `P^e(σ) = Σ_{x′} eq(r, x′) E_L(σ, x′)` over `8 + 18` variables
(`x′ = (hi, t)`), with `E_L(σ, (hi, t)) = E_chain(σ + 64 hi)` on the blocks `t ≤ L` and `0` past. -/
def targetSSegS (r : Array F) : Array F :=
  Array.ofFn (n := 64) fun σ => FR.targetS (ℓ := 8 + 18) (Fin.append (zLo r) (blkOf r))
    (fun σ u => if u.val / 256 ≤ lastAt r 19 then chainE (σ + 64 * (u.val % 256)) else 0) σ

theorem targetSSeg_meets (r : Array F) : targetSSegI r = targetSSegS r := by
  rw [targetSSegI, targetSLeaf_meets 18, segRangeI_eq]
  unfold targetSLeafS targetSSegS
  rw [Array.map_ofFn]
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [Function.comp_apply, FR.targetS, FR.targetS]
  rw [← (joinEquiv 8 18).sum_comp, ← (joinEquiv 8 18).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun hi _ => ?_
  have hj : ∀ t : Fin (2 ^ 18), (join hi t).val % 256 = hi.val ∧ (join hi t).val / 256 = t.val :=
    fun t => by
      show (2 ^ 8 * t.val + hi.val) % 256 = hi.val ∧ (2 ^ 8 * t.val + hi.val) / 256 = t.val
      have := hi.isLt; constructor <;> omega
  have hj1 : ∀ t : Fin (2 ^ 18), (join hi t).val % 256 = hi.val := fun t => (hj t).1
  have hj2 : ∀ t : Fin (2 ^ 18), (join hi t).val / 256 = t.val := fun t => (hj t).2
  simp only [show ∀ t, (joinEquiv 8 18) (hi, t) = join hi t from fun _ => rfl, eq_append_join,
    hj1, hj2]
  generalize eq (zLo r) (cube hi) = e₁
  generalize chainE (σ.val + 64 * hi.val) = C
  have hB : ∑ t : Fin (2 ^ 18), eq (fun l : Fin 18 => r.getD (1 + ↑l) 0) (cube t) = 1 := eq_sum_one _
  have hR : ∑ t : Fin (2 ^ 18), (if t.val ≤ lastAt r 19 then eq (blkOf r) (cube t) else 0) =
      segRangeS r := by
    rw [segRangeS, ← sum_fin_lt (fun t => eqAtR (blkOf r) t)
      (show lastAt r 19 + 1 ≤ 2 ^ 18 from lastAt_lt r 19)]
    exact Finset.sum_congr rfl fun t _ => by simp only [Nat.lt_succ_iff, eq_cube]; rfl
  rw [show ∑ t : Fin (2 ^ 18), e₁ * eq (fun l : Fin 18 => r.getD (1 + ↑l) 0) (cube t) * C =
        e₁ * C * ∑ t : Fin (2 ^ 18), eq (fun l : Fin 18 => r.getD (1 + ↑l) 0) (cube t) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hB,
      show ∑ t : Fin (2 ^ 18), e₁ * eq (blkOf r) (cube t) * (if t.val ≤ lastAt r 19 then C else 0) =
        e₁ * C * ∑ t : Fin (2 ^ 18), (if t.val ≤ lastAt r 19 then eq (blkOf r) (cube t) else 0) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by split_ifs <;> ring,
      hR, mul_one]

/-- **What the segment's target is on the blocks** (B-12): on a Boolean block point `u`, the range
factor is `[u ≤ L]`, so the target is the chain block's on the blocks `≤ L` and `0` past `L`. -/
theorem range_cube (r : Array F) (u : Fin (2 ^ 18)) (hu : blkOf r = cube u) :
    segRangeS r = if u.val ≤ lastAt r 19 then 1 else 0 := by
  rw [segRangeS, hu]
  have : ∀ t ∈ range (lastAt r 19 + 1), eqAtR (cube (R := F) u) t =
      if t = u.val then 1 else 0 := fun t ht => by
    have ht' : t < 2 ^ 18 := lt_of_lt_of_le (mem_range.1 ht) (lastAt_lt r 19)
    rw [show eqAtR (cube (R := F) u) t = eq (cube u) (cube (⟨t, ht'⟩ : Fin (2 ^ 18))) from
      by rw [eq_cube]; rfl, eq_cube_cube]
    simp only [Fin.ext_iff, eq_comm]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  simp only [mem_range, Nat.lt_succ_iff]

/-! ## The shift weights -/

/-- **The segment's `shiftMask`** (operand `τ ‖ L`: entries `0 … 17`, `18 … 35`; `r` the 18 block
coordinates): `eq(τ, r)`; the successor **masked at `L`**, `shift(τ, r) + eq(τ, L)·eq(r, L + 1)`
(characteristic two; no term when `L + 1 = 2^18`); `eq(r, 0)`. -/
def shiftSegI (τL r : Array F) : F × F × F :=
  let τ := Array.ofFn (ptA 18 τL); let ρ := Array.ofFn (ptA 18 r)
  let L := lastAt τL 18
  (eqPoint τ ρ,
   shiftEqI τ ρ + (if L + 1 < 2 ^ 18 then eqAtR (ptA 18 τL) L * eqAtR (ptA 18 r) (L + 1) else 0),
   eqAtR (ptA 18 r) 0)

/-- **Its specification**: `eq`, the successor's extension `shiftMle` with the link at `L` removed,
`eq(r, 0)`. -/
def shiftSegS (τL r : Array F) : F × F × F :=
  let L := lastAt τL 18
  (eq (ptA 18 τL) (ptA 18 r),
   shiftMle 18 (ptA 18 τL) (ptA 18 r) +
     (if L + 1 < 2 ^ 18 then eqAtR (ptA 18 τL) L * eqAtR (ptA 18 r) (L + 1) else 0),
   eqAtR (ptA 18 r) 0)

theorem ptA18_ofFn (a : Array F) : ptA 18 (Array.ofFn (ptA 18 a)) = ptA 18 a := funext fun l => by
  simp [ptA, Array.getD_eq_getD_getElem?, l.isLt]

theorem ptOf_ofFn (f : Fin 18 → F) : ptOf 18 (List.ofFn f) = f := funext fun l => by
  simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_ofFn, l.isLt, dite_true,
    Option.getD_some]

theorem eqPoint_18 (a b : Array F) (ha : a.size = 18) :
    eqPoint a b = eq (ptA 18 a) (ptA 18 b) := by
  rw [eqPoint_eq]; rw [ha]

theorem shiftSeg_meets (τL r : Array F) : shiftSegI τL r = shiftSegS τL r := by
  simp only [shiftSegI, shiftSegS, eqPoint_18 _ _ Array.size_ofFn, ptA18_ofFn, shiftEqI,
    Array.toList_ofFn, shiftPair_eq 18 _ _ (List.length_ofFn) (List.length_ofFn), ptOf_ofFn]

/-- The successor's extension on Boolean points is the successor. -/
theorem shiftMle_cube (y y' : Fin (2 ^ 18)) :
    shiftMle 18 (cube (R := F) y) (cube y') = if y'.val = y.val + 1 then 1 else 0 := by
  rw [← shift_mle]
  simp only [eq_cube_cube, succT, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single y (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

/-- **What the segment's successor weight is on the blocks** (B-12): on Boolean points `y`, `y′`
it is `[y′ = y + 1 ∧ y ≠ L]` (the link from block `L` to `L + 1` is cut). -/
theorem shiftSeg_cube (τL r : Array F) (y y' : Fin (2 ^ 18)) (hτ : ptA 18 τL = cube y)
    (hr : ptA 18 r = cube y') :
    (shiftSegS τL r).2.1 = if y'.val = y.val + 1 ∧ y.val ≠ lastAt τL 18 then 1 else 0 := by
  have hsh := shiftMle_cube y y'
  have hat : ∀ (u : Fin (2 ^ 18)) (t : ℕ) (ht : t < 2 ^ 18), eqAtR (cube (R := F) u) t =
      if t = u.val then 1 else 0 := fun u t ht => by
    rw [show eqAtR (cube (R := F) u) t = eq (cube u) (cube (⟨t, ht⟩ : Fin (2 ^ 18))) from
      by rw [eq_cube]; rfl, eq_cube_cube]
    simp only [Fin.ext_iff, eq_comm]
  simp only [shiftSegS, hτ, hr, hsh]
  set L := lastAt τL 18
  have hcorr : (if L + 1 < 2 ^ 18 then eqAtR (cube (R := F) y) L * eqAtR (cube y') (L + 1) else 0) =
      if y.val = L ∧ y'.val = y.val + 1 then 1 else 0 := by
    split_ifs with h1 h2 h2
    · rw [hat y L (lastAt_lt τL 18), hat y' (L + 1) h1, if_pos h2.1.symm, if_pos (by omega)]; ring
    · rw [hat y L (lastAt_lt τL 18), hat y' (L + 1) h1]
      by_cases hy : L = y.val
      · rw [if_pos hy, if_neg (fun h => h2 ⟨hy.symm, by omega⟩)]; ring
      · rw [if_neg hy]; ring
    · exfalso; have := y'.isLt; omega
    · rfl
  rw [hcorr]
  by_cases hA : y'.val = y.val + 1 <;> by_cases hB : y.val = L <;>
    simp [hA, hB, CharTwo.add_self_eq_zero]

/-- (−) **Without the mask the successor links `L` to `L + 1`** (`L + 1 < 2^18`): on the Boolean
points `L`, `L + 1` the unmasked weight `shiftMle` is `1`, the segment's is `0`. -/
theorem shift_unmasked_link (τL r : Array F) (y y' : Fin (2 ^ 18)) (hτ : ptA 18 τL = cube y)
    (hr : ptA 18 r = cube y') (hy : y.val = lastAt τL 18) (hy' : y'.val = y.val + 1) :
    shiftMle 18 (ptA 18 τL) (ptA 18 r) = 1 ∧ (shiftSegS τL r).2.1 = 0 := by
  constructor
  · rw [hτ, hr, shiftMle_cube]; simp [hy']
  · rw [shiftSeg_cube τL r y y' hτ hr]; simp [hy]

/-! ## The segment's op implementation -/

/-- **`implSeg impl₀`**: `impl₀` with a segment's `targetS` (the leaf kinds; a node's is
`impl₀`'s) and `shiftMask` (read by the segment's `finSh` only). SEG-R1: `evalM` and `evalL` are
**pinned to zero**: in the segment program both feed only an `assertEq` inactive at every kind
(SEG-R §2, SEG-R0 §6), no segment-side theorem reads them (SEG-R0 §5), and the zero is what the
replay's zero rows bind (`FRNodeRows4RepSegK.rtEvZ`). The segment check then evaluates no plan. -/
def implSeg (impl₀ : OpImpl) : OpImpl :=
  { impl₀ with
    targetS := fun κ r => if κ.isNode then impl₀.targetS κ r else targetSSegI r
    shiftMask := shiftSegI
    evalM := fun _ _ => (0, 0, 0)
    evalL := fun _ _ => (0, 0, 0) }

/-- Its specification. -/
def specSeg (spec₀ : OpSpec) : OpSpec :=
  { spec₀ with
    targetS := fun κ r => if κ.isNode then spec₀.targetS κ r else targetSSegS r
    shiftMask := shiftSegS
    evalM := fun _ _ => (0, 0, 0)
    evalL := fun _ _ => (0, 0, 0) }

/-- **`implSeg ⊨ specSeg`** (the `implC_meets` analogue). -/
theorem implSeg_meets {impl₀ : OpImpl} {spec₀ : OpSpec} (h : impl₀.Meets spec₀) :
    (implSeg impl₀).Meets (specSeg spec₀) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -, h10, h11, h12, h13, h14, -, h16, h17⟩ := h
  refine ⟨h1, fun κ r => ?_, h3, h4, h5, h6, h7, fun _ _ => rfl, fun _ _ => rfl, h10, h11, h12, h13, h14,
    shiftSeg_meets, h16, h17⟩
  simp only [implSeg, specSeg]
  split_ifs
  · exact h2 κ r
  · exact targetSSeg_meets r

end Rev4
end FR

end G6_FRSegTarget4
