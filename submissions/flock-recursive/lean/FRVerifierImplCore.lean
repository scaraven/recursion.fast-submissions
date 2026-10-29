-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 4; stage RET-3): the declarations of
-- the 3.x verifier-shape modules that the revision 4 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRVerifierImpl` (8), `FRNodePlan` (3). Content: the assembled
-- `implC`/`specC`/`Meets` and the node plan pieces revision 4 reads. The 3.x modules import this
-- one.
import FRNodeTargetCore
import FRVIRTplFast

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

/-- **The node's M plan** (`TEval.planOf` of the node's finals), built once at process start. -/
def nodePlan : TEval.Plan := TEval.planOf (finC finPf)

/-- **L's plan**, built once at process start. -/
def lPlan : TEval.LPlan := TEval.planL Layout.lRows

/-- **`implC` at the closed plans.** -/
def implCN : OpImpl := implCWith nodePlan lPlan

end Impl

end FR

end
