-- lvm6 (WP M1): taken from season 1's branch lvm2/AC-THM (858ab301), files LvmMcaAff* renamed Lvm6Aff*.
-- Vendored for lvm2 (WP AC-THM) from Verified-zkEVM/CompPoly `CompPoly/ToMathlib/Polynomial/BivariateDegree.lean`
-- @ 572f997 (Apache License 2.0, see `LICENSE-CompPoly`), as imported by ArkLib @ 31ff7dd. Changed: only `degreeX`
-- and `coeff_natDegree_le_degreeX` kept (all that `Lvm6AffPolyResDeg` uses), verbatim; module system stripped;
-- imports cut to the Mathlib modules they need.
/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Mathlib-Facing Bivariate Degree Helpers

This file collects degree- and evaluation-oriented helpers for Mathlib's bivariate
polynomial surface `R[X][Y]` that are useful as a bridge layer between CompPoly and
downstream developments such as ArkLib.
-/

section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type*}

section Semiring

variable [Semiring F]

/-- The `X`-degree of a bivariate polynomial. -/
def degreeX (f : F[X][Y]) : ℕ :=
  f.support.sup (fun n => (f.coeff n).natDegree)

theorem coeff_natDegree_le_degreeX (f : F[X][Y]) (n : ℕ) : (f.coeff n).natDegree ≤ degreeX f := by
  classical
  unfold degreeX
  by_cases hn : n ∈ f.support
  · exact Finset.le_sup (s := f.support) (f := fun m => (f.coeff m).natDegree) hn
  · have hcoeff : f.coeff n = 0 := by
      exact Polynomial.notMem_support_iff.mp hn
    simp [hcoeff]

end Semiring

end
end Polynomial.Bivariate

end
