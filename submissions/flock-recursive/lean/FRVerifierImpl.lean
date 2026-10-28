-- New for `flock-recursive` (BLUEPRINT §3, A.8, A.9; stage S-F2, track L-cert).
import FRVerifierImplOps
import FRVIRTplFast
import FRVIRFinalsSG
import FRVIREval
import FRRSEval
import FRVerifier
import FRBlockChain
import FRPubTarget
import FRVerifierImplNode

/-!
# `implC`, `specC`, `implC_meets`, `V` (with the node's M rows)

The op implementations and specifications are in `FRVerifierImplOps` (split by S-E3); this module
assembles them with the M-row ops (`evalM`, `evalL`; revision 3.12 removed `evalMK`). Since
revision 3.13 both are called once, by `finE`, at E4's 23-coordinate cell point `r′` (`evalL`'s
cell point is no longer Lr4's 15 challenges zero-padded: `FRVIRFinalsSF.finE_evalL_point`).
-/

namespace FR
namespace Impl
open Finset RecursionFast RecursionFast.Blake2s

/-! ## The assembled record, `Meets`, `V` -/

/-- **`implC`**: the computable ops. `fin` fixes the node's M rows (`evalM`, `TEval.planOf`),
`lRows` the L rows (`evalL`, templated by `TEval.planL`, S-E6); `κs₀` is no longer used (`shiftTarget` takes `κ_s`
as an operand since S-0's interface pass). `targetS`, `slotW` and `linkW` receive the kind but are
the leaf kinds' functions except `targetS` at a node kind (S-CN's `targetSNodeI`, S-E6);
`kindFoldWeight` is not used by revision 3.9's `gen` and is `0`. -/
def implCWith (pl : TEval.Plan) (lp : TEval.LPlan) : OpImpl where
  lagrangeS := lagrangeSI
  targetS κ := if κ.isNode then NodeI.targetSNodeI else targetSLeafI
  eqZ := eqZI
  tensorW := tensorWF
  rsWeight := rsWeightI
  phiRS := phiRSI
  walkAB := Eval.walkImpl
  kindInd := Eval.kindIndImpl
  evalM := TEval.evalMT pl
  evalL := TEval.evalLT lp
  shiftTarget := shiftTargetI
  slotW _ := slotWI
  kindFoldWeight _ _ _ := 0
  linkW _ _ _ _ := 0
  rowW := rowWI
  shiftEq := shiftEqI

/-- `implC` at the node's plan (`TEval.planOf fin`: both slots' templated compile, once) and L's
plan (`TEval.planL lRows`, once). -/
def implC (fin : Finals) (lRows : List Circ.Row) (_κs₀ : F) : OpImpl :=
  implCWith (TEval.planOf fin) (TEval.planL lRows)

/-- **`specC`**: the specifications, field by field (the same parameters; `targetS` the leaf
kinds' with `m = 30`, any `m` gives the same function; `linkW` the leaf kinds' `0`). -/
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
  linkW _ _ _ _ := 0
  rowW := rowWS
  shiftEq := shiftEqS

noncomputable def specC (fin : Finals) (lRows : List Circ.Row) (_κs₀ : F) : OpSpec :=
  specCWith (TEval.planOf fin) lRows

/-- **`implC ⊨ specC`** (`OpImpl.Meets`, per op under `gen`'s operand lengths). -/
theorem implCWith_meets (pl : TEval.Plan) (lRows : List Circ.Row) :
    (implCWith pl (TEval.planL lRows)).Meets (specCWith pl lRows) := by
  simp only [OpImpl.Meets, implCWith, specCWith]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun v l pe _ => lagrangeS_meets v l pe
  · intro κ r
    split_ifs
    · exact NodeI.targetSNode_meets r
    · exact targetSLeaf_meets 16 r
  · exact eqZ_meets
  · exact fun j r => (tensorWF_eq j r).trans (tensorW_meets j r)
  · exact fun r ps k p h => rsWeight_meets r ps k p h
  · exact fun r a _ => phiRS_meets r a
  · intro rw cw _ _
    rewrite [← Eval.walkA_eq rw cw, ← Eval.walkB_eq rw cw]
    exact Prod.mk.eta.symm
  · exact TEval.evalMT_eq _
  · intro a b; rw [TEval.evalLT_eq, TEval.planL_rows]
  · exact Eval.kindInd_eq
  · exact fun k a b c _ => shiftTarget_meets k a b c
  · exact fun _ => slotW_meets
  · simp
  · simp
  · exact rowW_meets
  · exact fun a b h => shiftEq_meets a b h

/-- `implC` is the templates' implementation (`ImplT`, the hypothesis of `compileT_sound`). -/
theorem implCWith_implT (pl : TEval.Plan) (lp : TEval.LPlan) : Circ.ImplT (implCWith pl lp) := by
  constructor <;> intros <;> simp only [implCWith]
  exact funext fun j => funext (tensorWF_eq j)

theorem implC_implT (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    Circ.ImplT (implC fin lRows κs₀) := implCWith_implT _ _

theorem implC_meets (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    (implC fin lRows κs₀).Meets (specC fin lRows κs₀) := implCWith_meets _ _

/-- The finals with S-G's `finP` and a `finPf` (S-G1d is writing it; a parameter until then). -/
def finC (pf : FinField) : Finals := sfFinals finP pf

/-- **The verifier** (§3) with the concrete ops: `Vwith implC finC`. Parametric in `finPf`, the
L rows and the stand-in `κs₀` until S-G1d, S-E2 and S-0 supply them. -/
def VC (pf : FinField) (lRows : List Circ.Row) (κs₀ : F) : Digest → Digest → Proof → OProg Bool :=
  Vwith (implC (finC pf) lRows κs₀) (finC pf)

end Impl
end FR
