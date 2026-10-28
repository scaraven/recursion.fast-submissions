-- New for `flock-recursive` (BLUEPRINT §3, A.8, A.9; stage S-F2, track L-cert).
import FRVerifierImplOps
import FRVIRTplFast
import FRVIRFinalsSG
import FRVIREval
import FRRSEval
import FRVerifier
import FRBlockChain
import FRPubTarget

/-!
# `implC`, `specC`, `implC_meets`, `V` (with the node's M rows)

The op implementations and specifications are in `FRVerifierImplOps` (split by S-E3); this module
assembles them with the M-row ops (`evalM`, `evalMK`, `evalL`).
-/

namespace FR
namespace Impl
open Finset RecursionFast RecursionFast.Blake2s

/-! ## The matrix MLEs at a K column point (`evalMK`) -/

/-- The sparse evaluation over `K`: `Σ_entries coef · eq(τ, row) · eq(σ, cell)`, `σ ∈ K^b`. -/
def sparseEvalK {a b : ℕ} (E : Eval.Entries) (τ : Fin a → F) (σ : Fin b → K) : K :=
  (E.map fun e => if e.1 < 2 ^ a ∧ e.2.1 < 2 ^ b then
    K.ofF (e.2.2 * Eval.eqAt τ e.1) * eqAtR σ e.2.1 else 0).sum

/-- A K array read as a point with `n` coordinates. -/
def ptK (n : ℕ) (r : Array K) : Fin n → K := fun l => r.getD l 0

/-- **`evalMK`** (A.9 `finPf`): the node's M matrices at `(τ, σ)`, `σ` a K point; templated
(S-E3: `FRVIRTplEval.evalMKT` over the node's plan). -/
def evalMKI (pl : TEval.Plan) (τ : Array F) (σ : Array K) : K × K × K := TEval.evalMKT pl τ σ

/-- **The matrix MLE over `K`** (`FRVIREval.matMLE` with a K column point):
`Σ_{x,y} eq(τ, x) M[x][y] eq(σ, y)`. -/
def matMLEK {a b : ℕ} (E : Eval.Entries) (τ : Fin a → F) (σ : Fin b → K) : K :=
  ∑ x : Fin (2 ^ a), ∑ y : Fin (2 ^ b), K.ofF (eq τ (cube x) * Eval.entry E x y) * eq σ (cube y)

/-- **`evalMK`'s specification**: the node's M matrices' MLEs at `(τ, σ)`, `σ ∈ K^23`. -/
def evalMKS (pl : TEval.Plan) (τ : Array F) (σ : Array K) : K × K × K :=
  let rows := TEval.nodeIRows pl
  (matMLEK (TEval.entriesI .a rows) (Eval.ptOf 21 τ) (ptK 23 σ),
   matMLEK (TEval.entriesI .b rows) (Eval.ptOf 21 τ) (ptK 23 σ),
   matMLEK (TEval.entriesI .c rows) (Eval.ptOf 21 τ) (ptK 23 σ))

section SparseK

private theorem sum_ite_pair {M : Type*} [AddCommMonoid M] {n m : ℕ} (g : Fin n → Fin m → M)
    (i j : ℕ) : ∑ x : Fin n, ∑ y : Fin m, (if x.val = i ∧ y.val = j then g x y else 0) =
      if h : i < n ∧ j < m then g ⟨i, h.1⟩ ⟨j, h.2⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i, h.1⟩ (fun x _ hx => Finset.sum_eq_zero fun y _ => by
        simp only [show ¬(x.val = i ∧ y.val = j) from fun hc => hx (Fin.ext hc.1), ite_false])
        (by simp),
      Finset.sum_eq_single ⟨j, h.2⟩ (fun y _ hy => by
        simp only [show ¬(y.val = j) from fun hc => hy (Fin.ext hc), and_false, ite_false])
        (by simp)]
    simp
  · exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by
      simp only [show ¬(x.val = i ∧ y.val = j) from fun hc => h ⟨hc.1 ▸ x.isLt, hc.2 ▸ y.isLt⟩,
        ite_false]

private theorem ofF_add (a b : F) : K.ofF (a + b) = K.ofF a + K.ofF b := map_add K.ofFRingHom a b

private theorem ofF_zero : K.ofF 0 = 0 := rfl

private theorem entry_cons (e : ℕ × ℕ × F) (E : Eval.Entries) (x y : ℕ) :
    Eval.entry (e :: E) x y = (if x = e.1 ∧ y = e.2.1 then e.2.2 else 0) + Eval.entry E x y := by
  simp only [Eval.entry, List.filter_cons]
  by_cases h1 : e.1 = x <;> by_cases h2 : e.2.1 = y <;> simp [h1, h2, eq_comm] <;>
    intro h <;> simp_all

/-- **The sparse evaluation over `K` is the matrix MLE** (`FRVIREval.sparse_eq` with a K column
point). -/
theorem sparseK_eq {a b : ℕ} (E : Eval.Entries) (τ : Fin a → F) (σ : Fin b → K) :
    sparseEvalK E τ σ = matMLEK E τ σ := by
  induction E with
  | nil => simp [sparseEvalK, matMLEK, Eval.entry, ofF_zero]
  | cons e E ih =>
    unfold sparseEvalK at ih ⊢
    rw [List.map_cons, List.sum_cons, ih]
    unfold matMLEK
    simp only [entry_cons, mul_add, ofF_add, add_mul, Finset.sum_add_distrib]
    congr 1
    have : ∀ (x : Fin (2 ^ a)) (y : Fin (2 ^ b)),
        K.ofF (eq τ (cube x) * if x.val = e.1 ∧ y.val = e.2.1 then e.2.2 else 0) * eq σ (cube y) =
        if x.val = e.1 ∧ y.val = e.2.1 then K.ofF (eq τ (cube x) * e.2.2) * eq σ (cube y) else 0 :=
      fun x y => by split_ifs <;> simp [ofF_zero]
    simp only [this, sum_ite_pair]
    split_ifs with h
    · rw [eq_cube, eq_cube, mul_comm (e.2.2)]; rfl
    · rfl

/-- **`evalMK` meets its specification.** -/
theorem evalMK_meets (pl : TEval.Plan) (τ : Array F) (σ : Array K) :
    evalMKI pl τ σ = evalMKS pl τ σ := by
  have h : ∀ E : Eval.Entries, sparseEvalK E (Eval.ptOf 21 τ) (ptK 23 σ) =
      (E.map fun e => if e.1 < 2 ^ 21 ∧ e.2.1 < 2 ^ 23 then
        K.ofF (e.2.2 * Eval.eqAt (Eval.ptOf 21 τ) e.1) *
          eqAtR (fun l : Fin 23 => σ.getD l 0) e.2.1 else 0).sum := fun E => rfl
  rw [evalMKI, TEval.evalMKT_eq, ← h, ← h, ← h, sparseK_eq, sparseK_eq, sparseK_eq]; rfl

end SparseK

/-! ## The assembled record, `Meets`, `V` -/

/-- **`implC`**: the computable ops. `fin` fixes the node's M rows (`evalM`, `evalMK`), `lRows`
the L rows (`evalL`; no module fixes them yet); `κs₀` is no longer used (`shiftTarget` takes `κ_s`
as an operand since S-0's interface pass). `targetS`, `slotW` and `linkW` receive the kind but are
still the leaf kinds' functions at every kind (the node's are S-C's);
`kindFoldWeight` is not used by revision 3.9's `gen` and is `0`. -/
def implCWith (pl : TEval.Plan) (lRows : List Circ.Row) : OpImpl where
  lagrangeS := lagrangeSI
  targetS _ := targetSLeafI
  eqZ := eqZI
  tensorW := tensorWI
  rsWeight := rsWeightI
  phiRS := phiRSI
  walkAB := Eval.walkImpl
  kindInd := Eval.kindIndImpl
  evalM := TEval.evalMT pl
  evalL := Eval.evalLImpl lRows
  evalMK := evalMKI pl
  shiftTarget := shiftTargetI
  slotW _ := slotWI
  kindFoldWeight _ _ _ := 0
  linkW _ _ _ _ := 0
  rowW := rowWI
  shiftEq := shiftEqI

/-- `implC` at the node's plan (`TEval.planOf fin`: both slots' templated compile, once). -/
def implC (fin : Finals) (lRows : List Circ.Row) (_κs₀ : F) : OpImpl :=
  implCWith (TEval.planOf fin) lRows

/-- **`specC`**: the specifications, field by field (the same parameters; `targetS` the leaf
kinds' with `m = 30`, any `m` gives the same function; `linkW` the leaf kinds' `0`). -/
noncomputable def specCWith (pl : TEval.Plan) (lRows : List Circ.Row) : OpSpec where
  lagrangeS := lagrangeSS
  targetS _ := targetSLeafS 16
  eqZ := eqZS
  tensorW := tensorWS
  rsWeight := rsWeightS
  phiRS := phiRSS
  walkAB rw cw := (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw)
  kindInd := Eval.kindIndSpec
  evalM := TEval.evalMS pl
  evalL := Eval.evalRowsSpec 15 23 lRows
  evalMK := evalMKS pl
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
    (implCWith pl lRows).Meets (specCWith pl lRows) := by
  simp only [OpImpl.Meets, implCWith, specCWith]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun v l pe _ => lagrangeS_meets v l pe
  · exact fun _ r => targetSLeaf_meets 16 r
  · exact eqZ_meets
  · exact tensorW_meets
  · exact fun r ps k p h => rsWeight_meets r ps k p h
  · exact fun r a _ => phiRS_meets r a
  · intro rw cw _ _
    rewrite [← Eval.walkA_eq rw cw, ← Eval.walkB_eq rw cw]
    exact Prod.mk.eta.symm
  · exact TEval.evalMT_eq _
  · exact Eval.evalL_eq lRows
  · exact evalMK_meets _
  · exact Eval.kindInd_eq
  · exact fun k a b c _ => shiftTarget_meets k a b c
  · exact fun _ => slotW_meets
  · simp
  · simp
  · exact rowW_meets
  · exact fun a b h => shiftEq_meets a b h

/-- `implC` is the templates' implementation (`ImplT`, the hypothesis of `compileT_sound`). -/
theorem implCWith_implT (pl : TEval.Plan) (lRows : List Circ.Row) : Circ.ImplT (implCWith pl lRows) :=
  by constructor <;> intros <;> simp only [implCWith]

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
