-- lvm6 (WP M1): taken from season 1's branch lvm2/AC-THM (858ab301), files LvmMcaAff* renamed Lvm6Aff*.
-- Vendored for lvm2 (WP AC-THM) from leanEthereum/leanVM
-- `formal/lean_vm/LeanVM/Protocol/ToArkLib/Whir/AffineCombinerYZDegree.lean` @ f5f3672 (Apache License 2.0, see
-- `LICENSE-leanVM`). Changed: module system stripped (`module`, `public import`, `@[expose] public section`); imports
-- renamed `AffineCombiner*` -> `Lvm6Aff*`; nothing else.
/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerYZDegree

  The `(Y, Z)`-degree of a trivariate polynomial, its additivity over products, and monotonicity
  under divisibility. Candidate for ArkLib.
-/


import Lvm6AffTrivariate
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# The `(Y, Z)`-degree

`yzDeg Q = max_{m ∈ supp Q} (m₁ + m₂)`, the total degree in the variables `1, 2` (`Y`, `Z`) of
`Q ∈ L[X, Y, Z]`. It is the total degree of `yzSplit Q ∈ L[X][Y, Z]` (`X` moved into the
coefficients), so it is additive over products of nonzero polynomials (`yzDeg_mul`) and monotone
under divisibility (`yzDeg_le_of_dvd`).
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Polynomial

section

variable {L : Type*} [Field L]

/-- The exponent `(a, b, c)`. -/
noncomputable def tri (a b c : ℕ) : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![a, b, c]

@[simp] theorem tri_zero (a b c : ℕ) : tri a b c 0 = a := rfl
@[simp] theorem tri_one (a b c : ℕ) : tri a b c 1 = b := rfl
@[simp] theorem tri_two (a b c : ℕ) : tri a b c 2 = c := rfl

theorem tri_eq (m : Fin 3 →₀ ℕ) : tri (m 0) (m 1) (m 2) = m := by
  ext i; fin_cases i <;> rfl

/-- The `(Y, Z)`-degree. -/
noncomputable def yzDeg (Q : MvPolynomial (Fin 3) L) : ℕ := Q.support.sup fun m ↦ m 1 + m 2

theorem le_yzDeg {Q : MvPolynomial (Fin 3) L} {m : Fin 3 →₀ ℕ} (hm : m ∈ Q.support) :
    m 1 + m 2 ≤ yzDeg Q :=
  Finset.le_sup (f := fun m : Fin 3 →₀ ℕ ↦ m 1 + m 2) hm

theorem yzDeg_le_iff {Q : MvPolynomial (Fin 3) L} {D : ℕ} :
    yzDeg Q ≤ D ↔ ∀ m ∈ Q.support, m 1 + m 2 ≤ D := Finset.sup_le_iff

/-- `X` moved into the coefficients: `L[X, Y, Z] → L[X][Y, Z]`. -/
noncomputable def yzSplit : MvPolynomial (Fin 3) L →ₐ[L] MvPolynomial (Fin 2) L[X] :=
  MvPolynomial.aeval ![MvPolynomial.C X, MvPolynomial.X 0, MvPolynomial.X 1]

/-- The exponent `(b, c)`. -/
noncomputable def duo (b c : ℕ) : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![b, c]

theorem coeff_yzSplit (Q : MvPolynomial (Fin 3) L) (n : Fin 2 →₀ ℕ) (k : ℕ) :
    ((yzSplit Q).coeff n).coeff k = Q.coeff (tri k (n 0) (n 1)) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c =>
    have himg : yzSplit (MvPolynomial.monomial m c) =
        MvPolynomial.monomial (duo (m 1) (m 2)) (C c * X ^ m 0) := by
      rw [yzSplit, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
        Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, ← MvPolynomial.C_pow]
      rw [MvPolynomial.monomial_eq, MvPolynomial.C_mul, Finsupp.prod_fintype _ _
        (fun _ ↦ pow_zero _)]
      simp only [MvPolynomial.algebraMap_apply, algebraMap_eq, Fin.isValue, MvPolynomial.C_pow, duo,
          Finsupp.equivFunOnFinite_symm_apply_apply, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring
    rw [himg, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    have hiff : duo (m 1) (m 2) = n ∧ m 0 = k ↔ m = tri k (n 0) (n 1) := by
      constructor
      · rintro ⟨h, rfl⟩
        rw [← tri_eq m]
        congr 1
        · exact congrArg (· 0) h
        · exact congrArg (· 1) h
      · rintro rfl
        refine ⟨?_, rfl⟩
        ext i; fin_cases i <;> rfl
    by_cases hm : m = tri k (n 0) (n 1)
    · have hd : duo (n 0) (n 1) = n := by ext i; fin_cases i <;> rfl
      subst hm
      simp only [Fin.isValue, tri_one, tri_two, hd, ↓reduceIte, tri_zero, coeff_C_mul, coeff_X_pow,
          mul_one]
    · have hn : ¬ (duo (m 1) (m 2) = n ∧ m 0 = k) := mt hiff.mp hm
      by_cases h1 : duo (m 1) (m 2) = n
      · have h0 : m 0 ≠ k := fun h0 ↦ hn ⟨h1, h0⟩
        simp only [Fin.isValue, h1, ↓reduceIte, coeff_C_mul, coeff_X_pow, Ne.symm h0, mul_zero, hm]
      · simp only [Fin.isValue, h1, ↓reduceIte, coeff_zero, hm]
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply,
      coeff_add, hp, Fin.isValue, hq]

theorem yzSplit_ne_zero {Q : MvPolynomial (Fin 3) L} (hQ : Q ≠ 0) : yzSplit Q ≠ 0 := by
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hQ
  intro h
  apply hm
  have := coeff_yzSplit Q (duo (m 1) (m 2)) (m 0)
  rw [h] at this
  simp only [AddMonoidAlgebra.coeff_zero, Fin.isValue, Finsupp.coe_zero, Pi.zero_apply,
      coeff_zero] at this
  rw [← tri_eq m]
  exact this.symm

/-- `yzDeg` is the total degree of the split. -/
theorem totalDegree_yzSplit (Q : MvPolynomial (Fin 3) L) : (yzSplit Q).totalDegree = yzDeg Q := by
  apply le_antisymm
  · refine Finset.sup_le fun n hn ↦ ?_
    obtain ⟨k, hk⟩ : ∃ k, ((yzSplit Q).coeff n).coeff k ≠ 0 := by
      by_contra hc
      push Not at hc
      exact MvPolynomial.mem_support_iff.mp hn (Polynomial.ext fun k ↦ by simp only [hc k,
          coeff_zero])
    rw [coeff_yzSplit] at hk
    have := le_yzDeg (MvPolynomial.mem_support_iff.mpr hk)
    simp only [tri_one, tri_two] at this
    simpa only [implies_true, Finsupp.sum_fintype, Fin.sum_univ_two, Fin.isValue,
        ge_iff_le] using this
  · refine Finset.sup_le fun m hm ↦ ?_
    have hc : ((yzSplit Q).coeff (duo (m 1) (m 2))).coeff (m 0) ≠ 0 := by
      rw [coeff_yzSplit]
      have : tri (m 0) (duo (m 1) (m 2) 0) (duo (m 1) (m 2) 1) = m := tri_eq m
      rw [this]
      exact MvPolynomial.mem_support_iff.mp hm
    have hmem : duo (m 1) (m 2) ∈ (yzSplit Q).support :=
      MvPolynomial.mem_support_iff.mpr (fun h ↦ hc (by rw [h]; simp only [Fin.isValue, coeff_zero]))
    have := MvPolynomial.le_totalDegree hmem
    simpa only [Fin.isValue, ge_iff_le, duo, implies_true, Finsupp.sum_fintype,
        Finsupp.equivFunOnFinite_symm_apply_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] using this

/-- **Additivity of the `(Y, Z)`-degree.** -/
theorem yzDeg_mul {P Q : MvPolynomial (Fin 3) L} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    yzDeg (P * Q) = yzDeg P + yzDeg Q := by
  rw [← totalDegree_yzSplit, ← totalDegree_yzSplit, ← totalDegree_yzSplit, map_mul,
    MvPolynomial.totalDegree_mul_of_isDomain (yzSplit_ne_zero hP) (yzSplit_ne_zero hQ)]

theorem yzDeg_le_of_dvd {P Q : MvPolynomial (Fin 3) L} (h : P ∣ Q) (hQ : Q ≠ 0) :
    yzDeg P ≤ yzDeg Q := by
  obtain ⟨c, rfl⟩ := h
  rw [yzDeg_mul (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)]
  omega

theorem yzDeg_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 3) L)
    (hf : ∀ i ∈ s, f i ≠ 0) : yzDeg (∏ i ∈ s, f i) = ∑ i ∈ s, yzDeg (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [yzDeg, Finset.prod_empty, MvPolynomial.support_one, Fin.isValue,
      Finset.sup_singleton, Finsupp.coe_zero, Pi.zero_apply, add_zero, Finset.sum_empty]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, yzDeg_mul (hf a (by simp only [
        Finset.mem_insert, true_or]))
      (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hf i (by simp only [Finset.mem_insert, hi, or_true])),
      ih fun i hi ↦ hf i (by simp only [Finset.mem_insert, hi, or_true])]

end

end LeanVM.Protocol.Whir.AffineCombiner
