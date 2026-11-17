-- New for lvm2 (roll 8 = B1, B1-S0 skeleton; B-DES §1.2 step 3): A23's accumulator at `Φ_Q`. `LvmAccSpec` is
-- generic in `Φ` and is used unchanged: `Φ := PhiQ Q lay`, the fixed claims are the four matrix values, `κ` is
-- the selector point `o`. Reuses `LvmAccSpec`'s `line`, `eqPoly`, `accProg`, `AccHyp`, `accSpecG`.
import LvmTypedLHolds
import LvmAccSpec

-- (GOLF2: 8 declarations that `certified` does not use moved verbatim to `LvmMPMidTOff`, outside its import closure.)

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

/-! ## The instance -/

/-- `y_own(κ) = Σ_o eq(κ, o)·v_o`: the four matrix values against the selector point. -/
def yOwnQ (vs : List E) (κ : List E) : E := Verifier.dot (Verifier.eqKernel κ) vs

/-- The line's far end: the selector point, then `r_x ++ r_y`. -/
def bOfQ (rxy : List E) (κ : List E) : List E := κ ++ rxy

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

end Lvm.Typed
