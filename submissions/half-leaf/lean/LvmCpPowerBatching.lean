-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToCompPoly/PowerBatching.lean` (formal rev 40f877dc) as `LvmCpPowerBatching` for lvm (WP-2).
/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/

/-
  LeanVM.Protocol.ToCompPoly.PowerBatching

  Power batching of weighted claims, with exponents starting at zero.
-/


import LvmCpMultilinear
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

-- (GOLF2: 4 declarations that `certified` does not use moved verbatim to `LvmTypedVEqPhasesXOff`, outside its import closure.)

/-!
# Power batching

A family of `J` values or tables is combined with powers `ρ^j`, starting at zero.
The difference polynomial has degree at most `J - 1`. A false singleton remains false
at every challenge, including zero. The empty family is handled separately.

Candidate for CompPoly: finite power combinations, their multilinear table pairing and
extension, and the finite-field root count. The values are fixed before the challenge is
chosen.

Derived from the zero-based scalar-batching results in Verified-zkEVM/leanth at
23929f8c922cd4461ab22dbfaa6520f3ad23a3b2, by Aristotle (Harmonic), Stefano Rocca and
Elias Judin: `Leanth/ProofSystem/ZeroCheck.lean:670-697`, `scalarBatch_rejection` and
`scalarBatch_eq_zero`. The current API takes separate actual and claimed values, exposes the
difference polynomial, and includes the empty case. `Leanth/ProofSystem/Stacking.lean:779-804`
uses positive powers in `BatchedAccepts` and `batchPoly`; that distinct convention has an
additional automatic root at zero and a `J` bound.

-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

section

variable {R : Type*} [CommRing R] {J μ : ℕ}

/-- A finite power combination, with coefficient zero weighted by one. -/
def powerBatch (a : Fin J → R) (ρ : R) : R := ∑ j : Fin J, a j * ρ ^ j.val

/-- The polynomial whose coefficients are the differences of the individual claims. -/
noncomputable def batchDifference (a v : Fin J → R) : Polynomial R :=
  ∑ j : Fin J, Polynomial.monomial j.val (a j - v j)

/-- The coefficient at index `j` is precisely the difference of claim `j`. -/
theorem coeff_batchDifference (a v : Fin J → R) (j : Fin J) :
    (batchDifference a v).coeff j.val = a j - v j := by
  classical
  simp [batchDifference, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_inj]

/-- A false component makes the difference polynomial nonzero. -/
theorem batchDifference_ne_zero (a v : Fin J → R) (h : ∃ j, a j ≠ v j) :
    batchDifference a v ≠ 0 := by
  obtain ⟨j, hj⟩ := h
  intro hp
  have hc := coeff_batchDifference a v j
  rw [hp, Polynomial.coeff_zero] at hc
  exact hj (sub_eq_zero.mp hc.symm)

/-- Evaluation of the difference polynomial is the difference of the two batches. -/
theorem eval_batchDifference (a v : Fin J → R) (ρ : R) :
    (batchDifference a v).eval ρ = powerBatch a ρ - powerBatch v ρ := by
  simp [batchDifference, powerBatch, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, Finset.sum_sub_distrib]

/-- The zero polynomial convention makes the same natural-degree bound valid when `J = 0`. -/
theorem natDegree_batchDifference_le (a v : Fin J → R) :
    (batchDifference a v).natDegree ≤ J - 1 := by
  unfold batchDifference
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_
  exact (Polynomial.natDegree_monomial_le (a j - v j)).trans (by have := j.isLt; omega)

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- At most `J - 1` challenges make a false family appear true after power batching. -/
theorem card_false_batch_le (a v : Fin J → F) (h : ∃ j, a j ≠ v j) :
    (Finset.univ.filter fun ρ ↦ powerBatch a ρ = powerBatch v ρ).card ≤ J - 1 := by
  have hp := batchDifference_ne_zero a v h
  calc
    _ ≤ (batchDifference a v).roots.toFinset.card := by
      apply Finset.card_le_card
      intro ρ hρ
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
      exact (eval_batchDifference a v ρ).trans
        (sub_eq_zero.mpr (Finset.mem_filter.mp hρ).2)
    _ ≤ (batchDifference a v).roots.card := Multiset.toFinset_card_le _
    _ ≤ (batchDifference a v).natDegree := Polynomial.card_roots' _
    _ ≤ J - 1 := natDegree_batchDifference_le a v

end FiniteField

end
end LeanVM.Protocol
