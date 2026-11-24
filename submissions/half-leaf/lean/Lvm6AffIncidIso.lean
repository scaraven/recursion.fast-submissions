-- lvm6 (WP M1): taken from season 1's branch lvm2/AC-THM (858ab301), files LvmMcaAff* renamed Lvm6Aff*.
-- New for lvm2 (WP AC-THM). STATEMENT FROZEN 2026-11-13; proved [AC-THM-INC-B].
-- Not imported by any submission root until the integration roll. Part of the bespoke replacement for
-- ArkLib's incidence count; see `Lvm6AffIncid` and docs/lvm2/stages/AC-THM.md §2.
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # No isolated points on a cylinder curve of `K³` -/

namespace LeanVM.Protocol.Whir.AffineCombiner.Incid

open MvPolynomial Finset

variable {K : Type*} [Field K]

section Jet

variable {σ : Type*} {R : Type*} [CommRing R] [Algebra K R]

/-- If `f ≡ x` modulo `I`, then `aeval f q ≡ q(x)` modulo `I`. -/
theorem aeval_sub_algebraMap_mem (I : Ideal R) (x : σ → K) (f : σ → R)
    (hf : ∀ j, f j - algebraMap K R (x j) ∈ I) (q : MvPolynomial σ K) :
    aeval f q - algebraMap K R (eval x q) ∈ I := by
  induction q using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, eval_C, sub_self, zero_mem]
  | add p q hp hq =>
    have h := add_mem hp hq
    simp only [map_add]
    convert h using 1
    ring
  | mul_X p j hp =>
    have h := add_mem (Ideal.mul_mem_right (f j) _ hp)
      (Ideal.mul_mem_left _ (algebraMap K R (eval x p)) (hf j))
    simp only [map_mul, aeval_X, eval_X]
    convert h using 1
    ring

variable [DecidableEq σ]

/-- First-order Taylor expansion of `aeval` in the direction of the variable `i`. -/
theorem aeval_update_add (p : MvPolynomial σ K) (f : σ → R) (i : σ) (δ : R) :
    ∃ q : R, aeval (Function.update f i (f i + δ)) p =
      aeval f p + δ * aeval f (pderiv i p) + δ ^ 2 * q := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp only [aeval_C, pderiv_C, map_zero]; ring⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by simp only [map_add, ha, hb]; ring⟩
  | mul_X p j hp =>
    obtain ⟨a, ha⟩ := hp
    by_cases hj : j = i
    · subst hj
      refine ⟨aeval f (pderiv j p) + a * f j + a * δ, ?_⟩
      simp only [map_mul, map_add, aeval_X, Function.update_self, pderiv_mul, pderiv_X,
        Pi.single_eq_same, map_one, ha]
      ring
    · refine ⟨a * f j, ?_⟩
      simp only [map_mul, map_add, aeval_X, Function.update_of_ne hj, pderiv_mul, pderiv_X,
        Pi.single_eq_of_ne hj, map_zero, ha]
      ring

/-- **Hensel jet.** A simple root of `p` in the direction `i` lifts to a root of `p` modulo
`I ^ (n + 1)` (linear Newton iteration with the fixed inverse `∂_i p(x)⁻¹`). -/
theorem exists_jet (I : Ideal R) (x : σ → K) (f : σ → R)
    (hf : ∀ j, f j - algebraMap K R (x j) ∈ I) (p : MvPolynomial σ K) (i : σ)
    (hp : eval x p = 0) (hd : eval x (pderiv i p) ≠ 0) (n : ℕ) :
    ∃ ζ, ζ - f i ∈ I ∧ aeval (Function.update f i ζ) p ∈ I ^ (n + 1) := by
  induction n with
  | zero =>
    refine ⟨f i, by simp only [sub_self, zero_mem], ?_⟩
    rw [Function.update_eq_self, zero_add, pow_one]
    simpa only [hp, map_zero, sub_zero] using aeval_sub_algebraMap_mem I x f hf p
  | succ n ih =>
    obtain ⟨ζ, hζ, hρ⟩ := ih
    set f' := Function.update f i ζ with hf'def
    have hf' : ∀ j, f' j - algebraMap K R (x j) ∈ I := by
      intro j
      by_cases hj : j = i
      · subst hj
        have h := add_mem hζ (hf j)
        rw [sub_add_sub_cancel] at h
        simpa only [f', Function.update_self] using h
      · simpa only [f', Function.update_of_ne hj] using hf j
    set ρ := aeval f' p with hρdef
    set c := algebraMap K R (eval x (pderiv i p))⁻¹ with hcdef
    set d := aeval f' (pderiv i p) with hddef
    obtain ⟨q, hq⟩ := aeval_update_add p f' i (-(c * ρ))
    have hρI : ρ ∈ I := Ideal.pow_le_self (Nat.succ_ne_zero n) hρ
    refine ⟨ζ + -(c * ρ), ?_, ?_⟩
    · have h := add_mem hζ (neg_mem (Ideal.mul_mem_left I c hρI))
      convert h using 1
      ring
    · have hupd : Function.update f i (ζ + -(c * ρ)) = Function.update f' i (f' i + -(c * ρ)) := by
        simp only [f', Function.update_idem, Function.update_self]
      rw [hupd, hq]
      have hcd : 1 - c * d ∈ I := by
        have h1 := Ideal.mul_mem_left I (-c) (aeval_sub_algebraMap_mem I x f' hf' (pderiv i p))
        have h2 : c * algebraMap K R (eval x (pderiv i p)) = 1 := by
          rw [hcdef, ← map_mul, inv_mul_cancel₀ hd, map_one]
        convert h1 using 1
        linear_combination -h2
      have h := add_mem (Ideal.mul_mem_mul hρ hcd)
        (Ideal.mul_mem_mul hρ (Ideal.mul_mem_right (c ^ 2 * q) I hρI))
      rw [← pow_succ] at h
      convert h using 1
      ring

end Jet

/-- Peeling `s` off `s^N u ≡ b g (mod s^{N+1})` over a domain, when `g(0) ≠ 0`. -/
theorem coeff_zero_eq_mul_of_X_pow_dvd {D : Type*} [CommRing D] [IsDomain D]
    {u b g : Polynomial D} {N : ℕ} (hg : g.coeff 0 ≠ 0)
    (h : Polynomial.X ^ (N + 1) ∣ Polynomial.X ^ N * u - b * g) :
    ∃ e : D, u.coeff 0 = e * g.coeff 0 := by
  have hc := Polynomial.X_pow_dvd_iff.mp h
  have key : ∀ k ≤ N, Polynomial.X ^ k ∣ b := by
    intro k
    induction k with
    | zero => intro _; rw [pow_zero]; exact one_dvd b
    | succ k ih =>
      intro hk
      obtain ⟨b', hb'⟩ := ih (by omega)
      have hk' := hc k (by omega)
      rw [hb', Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega),
        mul_assoc, Polynomial.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
        Polynomial.mul_coeff_zero, zero_sub, neg_eq_zero] at hk'
      have h0 : b'.coeff 0 = 0 := (mul_eq_zero.mp hk').resolve_right hg
      rw [hb', pow_succ]
      exact mul_dvd_mul_left _ (Polynomial.X_dvd_iff.mpr h0)
  obtain ⟨b', hb'⟩ := key N le_rfl
  have hN := hc N (by omega)
  rw [hb', mul_assoc, ← mul_sub, Polynomial.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
    Polynomial.coeff_sub, Polynomial.mul_coeff_zero, sub_eq_zero] at hN
  exact ⟨b'.coeff 0, hN⟩

/-- `aeval` commutes with a ring hom that is compatible with the scalars. -/
theorem map_aeval_of_algebraMap {σ : Type*} {A B : Type*} [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] (π : A →+* B) (hπ : ∀ a : K, π (algebraMap K A a) = algebraMap K B a)
    (g : σ → A) (q : MvPolynomial σ K) : π (aeval g q) = aeval (fun i ↦ π (g i)) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, hπ]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X]

/-- A polynomial free of the variable `1` does not see coordinate `1`. -/
theorem aeval_eq_of_vfree {A : Type*} [CommRing A] [Algebra K A] {p : MvPolynomial (Fin 3) K}
    (hV : ∀ m ∈ p.support, m 1 = 0) {g g' : Fin 3 → A} (h : ∀ i, i ≠ 1 → g i = g' i) :
    aeval g p = aeval g' p := by
  rw [aeval_eq_eval₂Hom, aeval_eq_eval₂Hom]
  refine eval₂Hom_congr' rfl (fun i hi _ ↦ h i ?_) rfl
  rintro rfl
  obtain ⟨m, hm, him⟩ := (mem_vars_iff_mem_support 1).mp hi
  exact Finsupp.mem_support_iff.mp him (hV m hm)

/-- **No isolated points on a cylinder curve** [AC-THM-INC-B]. Let `r` not involve `V` (coordinate `1`)
and be simple in `Z` at `x`: `r(x) = 0 ≠ ∂_Z r(x)`. If `G(x) = 0` and `H(x) ≠ 0`, then `r = G = 0`
has a second point off `H = 0`. Proof: otherwise, by the Nullstellensatz (Rabinowitsch),
`(Y − x₀)^N H^M` and `(V − x₁)^N H^M` lie in `(r, G)`; substitute the `N`-jet `Z = ζ(Y)` of the branch
of `r = 0` through `x` (Hensel), set `s = Y − x₀`, `t = V − x₁`, and peel `s` off
`s^N H̃^M = B̃ G̃` modulo `s^{N+1}` using `G̃(0, t) ≠ 0` (from the `t`-identity); at `s = t = 0` this
gives `H(x)^M = 0`. -/
theorem exists_ne_of_isolated [IsAlgClosed K] (r G H : MvPolynomial (Fin 3) K)
    (hV : ∀ m ∈ r.support, m 1 = 0) (x : Fin 3 → K) (hr : eval x r = 0)
    (hrZ : eval x (pderiv 2 r) ≠ 0) (hG : eval x G = 0) (hH : eval x H ≠ 0) :
    ∃ y : Fin 3 → K, y ≠ x ∧ eval y r = 0 ∧ eval y G = 0 ∧ eval y H ≠ 0 := by
  by_contra hne
  push Not at hne
  -- Nullstellensatz: `(X j - x j) H` vanishes on `r = G = 0`.
  have hnull : ∀ j : Fin 3, ∃ N : ℕ, ((X j - C (x j)) * H) ^ N ∈ Ideal.span {r, G} := by
    intro j
    have hmem : (X j - C (x j)) * H ∈ vanishingIdeal K (zeroLocus K (Ideal.span {r, G})) := by
      rw [mem_vanishingIdeal_iff]
      intro y hy
      rw [mem_zeroLocus_iff] at hy
      have hyr := hy r (Ideal.subset_span (Set.mem_insert r {G}))
      have hyG := hy G (Ideal.subset_span (Set.mem_insert_of_mem r rfl))
      rw [aeval_eq_eval] at hyr hyG ⊢
      by_cases hyx : y = x
      · subst hyx
        simp only [map_mul, map_sub, eval_X, eval_C, sub_self, zero_mul]
      · simp only [map_mul, hne y hyx hyr hyG, mul_zero]
    rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
    exact Ideal.mem_radical_iff.mp hmem
  obtain ⟨N, hN⟩ := hnull 0
  obtain ⟨N', hN'⟩ := hnull 1
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hN
  obtain ⟨c', d', hcd'⟩ := Ideal.mem_span_pair.mp hN'
  -- The jet `ζ(s)` of `r(x₀ + s, x₁, ζ) = 0` in `K[t][s]`.
  let f : Fin 3 → Polynomial (Polynomial K) :=
    ![Polynomial.C (Polynomial.C (x 0)) + Polynomial.X, Polynomial.C (Polynomial.C (x 1)),
      Polynomial.C (Polynomial.C (x 2))]
  have hf : ∀ j, f j - algebraMap K _ (x j) ∈
      Ideal.span {(Polynomial.X : Polynomial (Polynomial K))} := by
    intro j
    fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Polynomial.algebraMap_apply,
      Polynomial.algebraMap_eq, add_sub_cancel_left, sub_self, Submodule.mem_span_singleton_self,
      zero_mem, f]
  obtain ⟨ζ, hζ, hjet⟩ := exists_jet _ x f hf r 2 hr hrZ N
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hjet
  have hζ0 : ζ.coeff 0 = Polynomial.C (x 2) := by
    have := (Polynomial.X_dvd_iff (R := Polynomial K)).mp (Ideal.mem_span_singleton.mp hζ)
    simpa only [Fin.isValue, Matrix.cons_val, Polynomial.coeff_sub, Polynomial.coeff_C_zero,
      sub_eq_zero, f] using this
  let φ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial (Polynomial K) :=
    aeval ![Polynomial.C (Polynomial.C (x 0)) + Polynomial.X,
      Polynomial.C (Polynomial.C (x 1) + Polynomial.X), ζ]
  let ψ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
    aeval ![Polynomial.C (x 0), Polynomial.C (x 1) + Polynomial.X, Polynomial.C (x 2)]
  have hφψ : ∀ q, (φ q).coeff 0 = ψ q := by
    intro q
    have h := map_aeval_of_algebraMap (K := K) Polynomial.constantCoeff
      (fun a ↦ by simp only [Polynomial.algebraMap_apply, Polynomial.algebraMap_eq,
        Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero])
      (![Polynomial.C (Polynomial.C (x 0)) + Polynomial.X,
        Polynomial.C (Polynomial.C (x 1) + Polynomial.X), ζ] : Fin 3 → Polynomial (Polynomial K)) q
    rw [← Polynomial.constantCoeff_apply]
    refine h.trans (congrArg (aeval · q) ?_)
    funext i
    fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add,
      Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero, Polynomial.coeff_X_zero, add_zero,
      hζ0]
  have hψx : ∀ q, (ψ q).eval 0 = eval x q := by
    intro q
    have h := map_aeval_of_algebraMap (K := K) (Polynomial.evalRingHom 0)
      (fun a ↦ by simp only [Polynomial.algebraMap_eq, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Algebra.algebraMap_self, RingHom.id_apply])
      (![Polynomial.C (x 0), Polynomial.C (x 1) + Polynomial.X,
        Polynomial.C (x 2)] : Fin 3 → Polynomial K) q
    rw [← Polynomial.coe_evalRingHom, h, aeval_eq_eval]
    refine congrArg (fun v ↦ eval v q) (funext fun i ↦ ?_)
    fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Polynomial.coe_evalRingHom,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero]
  have hφr : Polynomial.X ^ (N + 1) ∣ φ r := by
    have h : φ r = aeval (Function.update f 2 ζ) r := by
      refine aeval_eq_of_vfree hV (fun i hi ↦ ?_)
      fin_cases i
      · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, ne_eq, Fin.reduceEq,
          not_false_eq_true, Function.update_of_ne, f]
      · exact absurd rfl hi
      · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, Function.update_self]
    rw [h]
    exact hjet
  have hψr : ψ r = 0 := by
    rw [← hφψ]
    exact Polynomial.X_dvd_iff.mp ((dvd_pow_self _ (Nat.succ_ne_zero N)).trans hφr)
  have hψH : ψ H ≠ 0 := fun h ↦ hH (by rw [← hψx, h, Polynomial.eval_zero])
  -- The `t`-identity: `G(x₀, x₁ + t, x₂) ≠ 0`.
  have hψG : ψ G ≠ 0 := by
    intro h0
    have hX : ψ (X 1 - C (x 1)) = Polynomial.X := by
      simp only [Fin.isValue, map_sub, aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero, algHom_C,
        Polynomial.algebraMap_eq, add_sub_cancel_left, ψ]
    have h := congrArg ψ hcd'
    rw [map_add, map_mul, map_mul, hψr, h0, mul_zero, mul_zero, add_zero, map_pow, map_mul,
      hX] at h
    exact pow_ne_zero N' (mul_ne_zero Polynomial.X_ne_zero hψH) h.symm
  -- The `s`-identity, peeled.
  have hX0 : φ (X 0 - C (x 0)) = Polynomial.X := by
    simp only [Fin.isValue, map_add, map_sub, aeval_X, Matrix.cons_val_zero, algHom_C,
      Polynomial.algebraMap_apply, Polynomial.algebraMap_eq, add_sub_cancel_left, φ]
  have hdiv : Polynomial.X ^ (N + 1) ∣ Polynomial.X ^ N * (φ H) ^ N - φ d * φ G := by
    have h := congrArg φ hcd
    rw [map_add, map_mul, map_mul, map_pow, map_mul, hX0, mul_pow] at h
    rw [← h, add_sub_cancel_right]
    exact dvd_mul_of_dvd_right hφr _
  obtain ⟨e, he⟩ := coeff_zero_eq_mul_of_X_pow_dvd (by rw [hφψ]; exact hψG) hdiv
  rw [← map_pow, hφψ, hφψ] at he
  have h := congrArg (Polynomial.eval 0) he
  rw [hψx, Polynomial.eval_mul, hψx, hG, mul_zero, map_pow] at h
  exact pow_ne_zero N hH h

end LeanVM.Protocol.Whir.AffineCombiner.Incid
