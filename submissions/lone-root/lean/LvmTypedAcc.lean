-- New for lvm2 (roll 8 = B1, B1-S0 skeleton; B-DES §1.2 step 3): A23's accumulator at `Φ_Q`. `LvmAccSpec` is
-- generic in `Φ` and is used unchanged: `Φ := PhiQ Q lay`, the fixed claims are the four matrix values, `κ` is
-- the selector point `o`. Reuses `LvmAccSpec`'s `line`, `eqPoly`, `accProg`, `AccHyp`, `accSpecG`.
import LvmTypedLHolds
import LvmAccSpec

/-!
# The accumulator at `Φ_Q`

B-DES §1.2: after the wiring sumcheck at `(r_x, r_y)` the prover sends `v_o = M̃_o(r_x, r_y)`, `o < 4`
(`A`, `B`, `D`, `W`). A23 folds them with the incoming accumulator: `κ ∈ E^2` is the selector point, the line
runs from `acc_in.pt` to `b(κ) = κ ++ r_x ++ r_y` (`o` is `Φ_Q`'s low coordinates), `h` has `44` coefficients.

* `yOwnQ vs κ = Σ_o eq(κ, o)·v_o`, `bOfQ`, `deltaQ` (`δ_o = v_o − M̃_o(r_x, r_y)`), **`accProgQ`**;
* **`lineDeg_sparse`** (proved): an `E`-valued sparse multilinear sum `Σ c_n·eq(·, n)` on a line is a
  polynomial of degree at most the number of variables (`lineDeg_mle` for `E`-valued tables);
* `phiQ_eq_sum` (proved): `Φ_Q` over `E` is that sum; `phiQ_fold` (L-B): the selector split, which gives
  `AccHyp.fold`;
* **`accHypQ`**: `AccHyp` at `Φ_Q` (from `phiQ_fold`); **`accSpecQ`**: `accSpecG` applies unchanged.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakGkr
open Lvm.Acc Polynomial Finset
open scoped ENNReal

/-! ## The line-degree lemma for an `E`-valued multilinear map -/

/-- **The line-degree lemma, `E`-valued**: on the line from `a` to `b`, a sparse sum `Σ_{(n, c)} c·eq(·, n)` is
a polynomial of degree at most `|a|` in `t`. -/
theorem lineDeg_sparse (es : List (ℕ × E)) (a b : List E) :
    ∃ g : E[X], g.natDegree ≤ a.length ∧
      ∀ t, g.eval t = (es.map fun p ↦ p.2 * eqAt (line a b t) p.1).sum := by
  induction es with
  | nil => exact ⟨0, by simp, fun t ↦ by simp⟩
  | cons p es ih =>
    obtain ⟨g, hg, hgv⟩ := ih
    refine ⟨C p.2 * eqPoly a b p.1 + g, ?_, fun t ↦ ?_⟩
    · exact (natDegree_add_le _ _).trans
        (max_le ((natDegree_C_mul_le _ _).trans (natDegree_eqPoly a b p.1)) hg)
    · rw [eval_add, eval_mul, eval_C, eval_eqPoly, hgv, List.map_cons, List.sum_cons]

/-! ## `Φ_Q` as a sum over `E` -/

/-- The native equality weight read over `E` (`LvmAccSpecPhi.toExt3_eqW`, restated here to keep this module off
the bus side's imports). -/
theorem toExt3_eqW' : ∀ (l : List E) (w : ℕ), FE.toExt3 (eqW (l.map FE.ofExt3) w) = eqAt l w
  | [], _ => by simp [eqW]
  | r :: l, w => by
    simp only [List.map_cons, eqW, eqAt_cons, FE.toExt3_mul, toExt3_eqW' l]
    split_ifs
    · simp
    · rw [FE.toExt3_sub, FE.toExt3_one, FE.toExt3_ofExt3, CharTwo.sub_eq_add]

theorem toExt3_phiSum (es : List Ent) (pt : List E) :
    FE.toExt3 (phiSum es (pt.map FE.ofExt3)) = (es.map fun e ↦ FE.toExt3 e.c * eqAt pt e.idx).sum := by
  induction es with
  | nil => simp [phiSum]
  | cons e es ih =>
    simp only [phiSum, List.foldr_cons] at ih ⊢
    rw [FE.toExt3_add, FE.toExt3_mul, toExt3_eqW', ih, List.map_cons, List.sum_cons]

/-- **`Φ_Q` over `E` is the sparse multilinear sum** of the matrices' entries. -/
theorem phiQ_eq_sum (Q : Program) (lay : Lay) (pt : List E) :
    PhiQ Q lay pt = ((ents Q lay).map fun e ↦ FE.toExt3 e.c * eqAt pt e.idx).sum :=
  toExt3_phiSum _ _

/-! ## The instance -/

/-- `y_own(κ) = Σ_o eq(κ, o)·v_o`: the four matrix values against the selector point. -/
def yOwnQ (vs : List E) (κ : List E) : E := Verifier.dot (Verifier.eqKernel κ) vs

/-- The line's far end: the selector point, then `r_x ++ r_y`. -/
def bOfQ (rxy : List E) (κ : List E) : List E := κ ++ rxy

/-- The fixed claims' errors: `δ_o = v_o − M̃_o(r_x, r_y)` for `o < 4`. -/
def deltaQ (Q : Program) (lay : Lay) (vs rxy : List E) (o : ℕ) : E :=
  if o < 4 then vs.getD o 0 - matMle Q lay o rxy else 0

/-- **Phase 3b at `Φ_Q`** (B-DES §1.2 step 3): `κ` (2 samples), `h` (`phiVars + 1 = 44` coefficients), `t`, the
zero scalar; `ok` is the phase's pass check (B1-V). -/
def accProgQ (Q : Program) (lay : Lay) (ok : Bool) (yIn : E) (a rxy vs : List E) : VerifierProgram Unit :=
  accProg 2 phiVars ok yIn a (yOwnQ vs) (bOfQ rxy) (PhiQ Q lay)

/-- A filtered fold of entries, read over `E`, is the sum of the read terms. -/
theorem toExt3_foldr_ents (l : List Ent) (g : Ent → FE) :
    FE.toExt3 (l.foldr (fun e acc ↦ g e + acc) 0) = (l.map fun e ↦ FE.toExt3 (g e)).sum := by
  induction l with
  | nil => simp
  | cons e l ih => rw [List.foldr_cons, FE.toExt3_add, ih, List.map_cons, List.sum_cons]

/-- **Matrix `o`'s extension over `E`** is the sum over its entries (`rxy = r_x ++ r_y`). -/
theorem matMle_eq_sum (Q : Program) (lay : Lay) (o : ℕ) (rxy : List E) :
    matMle Q lay o rxy = (((ents Q lay).filter fun e ↦ e.o == o).map fun e ↦
      FE.toExt3 e.c * eqAt rxy (e.x + 2 ^ xVars * e.y)).sum := by
  unfold matMle matMleF
  rw [toExt3_foldr_ents]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE.toExt3_mul, toExt3_eqW'])

/-- A selector-weighted sum of the per-matrix sums is the weighted sum over all entries (every `o < 4`). -/
theorem sum_sel_filter (g : ℕ → E) (f : Ent → E) :
    ∀ l : List Ent, (∀ e ∈ l, e.o < 4) →
      ∑ w ∈ range (2 ^ 2), g w * ((l.filter fun e ↦ e.o == w).map f).sum = (l.map fun e ↦ g e.o * f e).sum
  | [], _ => by simp
  | e :: l, hl => by
    have ih := sum_sel_filter g f l fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')
    have he : e.o < 2 ^ 2 := hl e (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ← ih]
    rw [Finset.sum_congr rfl fun w _ ↦ show g w * ((((e :: l).filter fun e ↦ e.o == w)).map f).sum =
        (if e.o = w then g e.o * f e else 0) + g w * ((l.filter fun e ↦ e.o == w).map f).sum by
      by_cases h : e.o = w
      · subst h; simp [mul_add]
      · simp [h]]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr he)]

/-- **The selector split** (L-B): at `κ ++ r_x ++ r_y`, `y_own − Φ_Q` is the selector extension of the
matrices' errors. Needs every entry's `o < 4` (`okB`'s `auxOk`; `instEnts` by construction). -/
theorem phiQ_fold (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (rxy vs : List E) (hr : rxy.length = xVars + yVars)
    (hvs : vs.length = 4) (κ : List E) (hκ : κ.length = 2) :
    yOwnQ vs κ - PhiQ Q lay (bOfQ rxy κ) = ∑ w ∈ range (2 ^ 2), eqAt κ w * deltaQ Q lay vs rxy w := by
  have hfit := ents_fit Q lay hlay
  have hk4 : (Verifier.eqKernel κ).length = 2 ^ 2 := by rw [eqKernel_length, hκ]
  have hown : yOwnQ vs κ = ∑ w ∈ range (2 ^ 2), eqAt κ w * vs.getD w 0 := by
    unfold yOwnQ
    rw [LeanVM.Protocol.KeccakGkr.dot_eq _ _ (by rw [hk4, hvs]; rfl), hk4]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [eqKernel_getD, hκ, ite_eq_left (Finset.mem_range.mp hw)]
  have hphi : PhiQ Q lay (bOfQ rxy κ) = ∑ w ∈ range (2 ^ 2), eqAt κ w * matMle Q lay w rxy := by
    simp only [matMle_eq_sum]
    rw [sum_sel_filter (eqAt κ) _ _ fun e he ↦ (hfit e he).1, phiQ_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
    have ho := (hfit e he).1
    unfold bOfQ
    rw [eqAt_append, hκ, eqAt_mod κ, hκ, Ent.idx,
      show (e.o + 4 * (e.x + 2 ^ xVars * e.y)) % 2 ^ 2 = e.o by omega,
      show (e.o + 4 * (e.x + 2 ^ xVars * e.y)) / 2 ^ 2 = e.x + 2 ^ xVars * e.y by omega]
    ring
  rw [hown, hphi, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  rw [deltaQ, ite_eq_left (by simpa using hw), mul_sub]

/-- **`AccHyp` at `Φ_Q`** (B-DES §1.2 step 3: `LvmAccSpec` unchanged): `dk = 2` (the selector), `D = 43`. -/
theorem accHypQ (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (a rxy vs : List E) (ha : a.length = phiVars)
    (hr : rxy.length = xVars + yVars) (hvs : vs.length = 4) :
    AccHyp 2 phiVars a (yOwnQ vs) (bOfQ rxy) (PhiQ Q lay) (deltaQ Q lay vs rxy) where
  line_deg κ _ := by
    obtain ⟨g, hg, hgv⟩ := lineDeg_sparse ((ents Q lay).map fun e ↦ (e.idx, FE.toExt3 e.c)) a (bOfQ rxy κ)
    refine ⟨g, ha ▸ hg, fun t ↦ ?_⟩
    rw [hgv, phiQ_eq_sum, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun e _ ↦ rfl)
  at0 κ hκ := line_zero _ _ (by simp [bOfQ, ha, hr, hκ, phiVars]; omega)
  at1 κ hκ := line_one _ _ (by simp [bOfQ, ha, hr, hκ, phiVars]; omega)
  fold κ hκ := phiQ_fold Q lay hlay rxy vs hr hvs κ hκ

/-- **`accSpecG` at `Φ_Q`**: A23's phase specification applies unchanged (escape `1/|E|` per `κ_j`, `43/|E|` at
`t`). -/
noncomputable def accSpecQ (Q : Program) (lay : Lay) (hlay : lay.Ok Q) {ok : Bool} {yIn : E}
    (a rxy vs : List E) (ha : a.length = phiVars) (hr : rxy.length = xVars + yVars) (hvs : vs.length = 4)
    (M : List Ev → Prop)
    (hM : ∀ h₀ l, (accProgQ Q lay ok yIn a rxy vs).Reach h₀ l → M h₀ → M (h₀ ++ l))
    {εmax T : ℝ≥0∞} (hD : errE phiVars ≤ εmax) (hT : T ≤ εmax) :
    Spec (accProgQ Q lay ok yIn a rxy vs)
      (fun h ↦ ¬ AccGood 2 ok yIn a (PhiQ Q lay) (deltaQ Q lay vs rxy) ∨ M h)
      (fun _ h ↦ M h) εmax (max (2 * errE 1) T) T :=
  accSpecG (accHypQ Q lay hlay a rxy vs ha hr hvs) M hM hD hT

end Lvm.Typed
