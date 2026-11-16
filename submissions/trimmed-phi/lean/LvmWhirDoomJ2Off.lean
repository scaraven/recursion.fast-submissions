/- `LvmWhirDoomJ2Off` (GOLF2 off-path move, group 15 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmJBClearedJet, LvmWhirParamsJp, LvmWhirDoomJ2,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmJBClearedJet
import LvmWhirParamsJp
import LvmWhirDoomJ2
import LvmWhirSuffixROff
import LvmXDec1UdOff
import LvmJBMutual
import LvmMlListLemmas

-- ===== from `LvmJBClearedJet` =====

section
section
namespace JBAgreement
open Polynomial Finset
variable {K : Type*} [Field K]

/-- **The jet property (§1, conclusion).**

`U^{r+1}` divides `R(Γ_k) - r₀`.  In the intended instantiation `r₀ = R(x₀, T, Z)`
specialises to `0` at every branch point `(z, t_z)`, making the specialised jet a root
of `R(x₀+U, ·, z)` modulo `U^{r+1}`; finite Hensel uniqueness (`Jet.lean`) then
identifies it with the proximate `p_z`. -/
theorem eval_jet_sub_C_dvd (R : K[X][X]) (α₀ : K) (hξ : xi R α₀ ≠ 0) (r : ℕ) :
    (X : K[X]) ^ (r + 1) ∣ R.eval (jet R α₀ r) - C (jetConst R α₀) := by
  rw [X_pow_dvd_iff]
  intro d hd
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · rw [coeff_sub, coeff_zero_eval_jet, coeff_C]
    simp
  · rw [coeff_sub, coeff_eval_jet_eq_zero R α₀ hξ r d hdpos (by (clear * - hd; omega)), coeff_C]
    simp
    (clear * - hdpos; omega)

end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset

theorem ledger_succ_self (t : ℕ) : ledger (t + 1) (t + 1) = 2 * t + 1 := by
  simp only [ledger, if_neg (Nat.succ_ne_zero t), if_pos (le_refl (t + 1))]
  omega

end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
variable (SS : SizeSystem A)
variable (R : K[X][X]) (R₀ : A[X][X]) (α₀ : K) (a₀ : A) (ξ₀ : A)
variable (d mR mα mξ : ℕ)

/-- The uniform size bound for the `U = 0` slices `c_{r,0}`. -/
def sliceBound (mR d mα : ℕ) : ℕ := mR + d * mα

/-- The ledger size constant: `b = m₀ + mξ`. -/
def ledgerConst (mR d mα mξ : ℕ) : ℕ := sliceBound mR d mα + mξ

end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
variable (SS : SizeSystem A)
variable (R : K[X][X]) (R₀ : A[X][X]) (α₀ : K) (a₀ : A) (ξ₀ : A)
variable (d mR mα mξ : ℕ)
section Ledger
variable (hR : R = R₀.map (mapRingHom (algebraMap A K)))
variable (hα : α₀ = algebraMap A K a₀)
variable (hd : R₀.natDegree ≤ d)
variable (hmR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR)
variable (hmα : SS.P a₀ mα)
variable (hmξ : SS.P ξ₀ mξ)
variable (hξint : algebraMap A K ξ₀ = xi R α₀)
variable (hξ0 : xi R α₀ ≠ 0)

include hR hα hd hmR hmα in
/-- **The base computation.**  Every coefficient of `(D^r R)(C α₀)` is integral of size
at most `m₀ = mR + d·mα`: substituting the constant `α₀` costs `mα` per `Y`-power.
This covers both the `t = 0` base of the induction and, via `coeff_zero_eval`, the
`s = 0` column for every `t`. -/
theorem base_integral (r s : ℕ) :
    ∃ g : A, algebraMap A K g = ((hasseDeriv r R).eval (C α₀)).coeff s ∧
      SS.P g (sliceBound mR d mα) := by
  have hRd : R.natDegree ≤ d := natDegree_R_le R R₀ d hR hd
  -- Expand the evaluation over `range (d + 1)`.
  have hdeg : (hasseDeriv r R).natDegree < d + 1 := by
    have h1 := natDegree_hasseDeriv_le R r
    omega
  have hexp : (hasseDeriv r R).eval (C α₀) =
      ∑ j ∈ range (d + 1), (hasseDeriv r R).coeff j * (C α₀) ^ j :=
    eval_eq_sum_range' hdeg _
  refine ⟨∑ j ∈ range (d + 1),
      (j + r).choose r • ((R₀.coeff (j + r)).coeff s) * a₀ ^ j, ?_, ?_⟩
  · -- The map identity.
    rw [hexp, finsetSum_coeff, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hC : ((C α₀ : K[X]) ^ j) = C (α₀ ^ j) := by rw [← C_pow]
    rw [hC, coeff_mul_C, hasseDeriv_coeff]
    rw [← nsmul_eq_mul, coeff_smul]
    rw [map_mul, map_nsmul, map_pow, ← hα]
    have hcoeff : algebraMap A K ((R₀.coeff (j + r)).coeff s) =
        (R.coeff (j + r)).coeff s := by
      simp [hR, coeff_map]
    rw [hcoeff]
  · -- The size bound.
    refine SS.sum _ _ fun j hj => ?_
    have hj' : j ≤ d := by
      have := Finset.mem_range.mp hj
      omega
    refine SS.mono (SS.mul (SS.nsmul (hmR (j + r) s) _) (SS.pow hmα j)) ?_
    have : j * mα ≤ d * mα := Nat.mul_le_mul_right _ hj'
    simp only [sliceBound]
    omega

end Ledger
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
variable (SS : SizeSystem A)
variable (R : K[X][X]) (R₀ : A[X][X]) (α₀ : K) (a₀ : A) (ξ₀ : A)
variable (d mR mα mξ : ℕ)
section Ledger
variable (hR : R = R₀.map (mapRingHom (algebraMap A K)))
variable (hα : α₀ = algebraMap A K a₀)
variable (hd : R₀.natDegree ≤ d)
variable (hmR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR)
variable (hmα : SS.P a₀ mα)
variable (hmξ : SS.P ξ₀ mξ)
variable (hξint : algebraMap A K ξ₀ = xi R α₀)
variable (hξ0 : xi R α₀ ≠ 0)

include hR hd in
/-- Hasse derivatives beyond the degree vanish. -/
theorem hasseDeriv_hasseDeriv_eq_zero {ρ r : ℕ} (h : d < ρ) :
    hasseDeriv ρ (hasseDeriv r R) = 0 := by
  have hRd : R.natDegree ≤ d := natDegree_R_le R R₀ d hR hd
  have h2 := natDegree_hasseDeriv_le R r
  apply Polynomial.ext
  intro n
  rw [hasseDeriv_coeff, coeff_zero, coeff_eq_zero_of_natDegree_lt (by omega)]
  simp

end Ledger
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
variable (SS : SizeSystem A)
variable (R : K[X][X]) (R₀ : A[X][X]) (α₀ : K) (a₀ : A) (ξ₀ : A)
variable (d mR mα mξ : ℕ)
section Ledger
variable (hR : R = R₀.map (mapRingHom (algebraMap A K)))
variable (hα : α₀ = algebraMap A K a₀)
variable (hd : R₀.natDegree ≤ d)
variable (hmR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR)
variable (hmα : SS.P a₀ mα)
variable (hmξ : SS.P ξ₀ mξ)
variable (hξint : algebraMap A K ξ₀ = xi R α₀)
variable (hξ0 : xi R α₀ ≠ 0)

include hR hα hd hmR hmα hmξ hξint hξ0 in
/-- **The ledger invariant.**

Every cleared coefficient `ξ^(ledger t s) · [Uˢ]((D^r R)(Γ_t))` is integral, with size at
most `(m₀ + mξ) · (ledger t s + 1)` — linear in the ledger, hence linear in `s`, and
in particular linear in `t` for the jet coefficients themselves. -/
theorem jet_ledger :
    ∀ t r s, ∃ g : A,
      algebraMap A K g =
        xi R α₀ ^ ledger t s * (((hasseDeriv r R).eval (jet R α₀ t)).coeff s) ∧
      SS.P g (ledgerConst mR d mα mξ * (ledger t s + 1)) := by
  set b := ledgerConst mR d mα mξ with hbdef
  have hm₀b : sliceBound mR d mα ≤ b := by
    rw [hbdef]; unfold ledgerConst; omega
  have hmξb : mξ ≤ b := by
    rw [hbdef]; unfold ledgerConst; omega
  intro t
  induction t with
  | zero =>
      intro r s
      obtain ⟨g, hg, hgs⟩ := base_integral SS R R₀ α₀ a₀ d mR mα hR hα hd hmR hmα r s
      refine ⟨ξ₀ ^ ledger 0 s * g, ?_, ?_⟩
      · rw [map_mul, map_pow, hξint, hg, jet_zero]
      · refine SS.mono (SS.mul (SS.pow hmξ _) hgs) ?_
        have h1 : ledger 0 s * mξ ≤ ledger 0 s * b := Nat.mul_le_mul_left _ hmξb
        have h2 : ledger 0 s * b + b = b * (ledger 0 s + 1) := by ring
        exact le_trans (add_le_add h1 hm₀b) (le_of_eq h2)
  | succ t ih =>
      intro r s
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · -- The `s = 0` column.
        obtain ⟨g, hg, hgs⟩ := base_integral SS R R₀ α₀ a₀ d mR mα hR hα hd hmR hmα r 0
        refine ⟨g, ?_, ?_⟩
        · rw [ledger_zero_right, pow_zero, one_mul,
            coeff_zero_column R α₀ r (t + 1), hg]
        · exact SS.mono hgs (by simp only [ledger_zero_right]; omega)
      · -- The update, `s ≥ 1`.
        choose G hGmap hGsize using ih
        set cJ := (jet R α₀ (t + 1)).coeff (t + 1) with hcJdef
        -- The integral model of the new jet coefficient.
        have hG0 := hGmap 0 (t + 1)
        rw [ledger_self_succ, hasseDeriv_zero'] at hG0
        have hGhat : algebraMap A K (-(G 0 (t + 1))) = xi R α₀ ^ (2 * t + 1) * cJ := by
          rw [map_neg, hG0, hcJdef, jet_coeff_succ_self, pow_succ]
          field_simp
        have hGhatSize : SS.P (-(G 0 (t + 1))) (b * (2 * t + 1)) := by
          have := hGsize 0 (t + 1)
          rw [ledger_self_succ] at this
          exact SS.neg (SS.mono this (by omega))
        -- Assemble the integral sum.
        refine ⟨∑ ρ ∈ range (d + 1),
            if (t + 1) * ρ ≤ s
            then (ρ + r).choose ρ •
              (G (ρ + r) (s - (t + 1) * ρ) * (-(G 0 (t + 1))) ^ ρ *
                ξ₀ ^ (ledger (t + 1) s - ledger t (s - (t + 1) * ρ) - ρ * (2 * t + 1)))
            else 0, ?_, ?_⟩
        · -- The map identity.
          rw [coeff_eval_hasseDeriv_jet_succ R R₀ α₀ d hR hd r s t, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          by_cases hcond : (t + 1) * ρ ≤ s
          · rw [if_pos hcond, if_pos hcond]
            set s' := s - (t + 1) * ρ with hs'def
            -- Exactness of the ledger split.
            have hslack := ledger_slack t s' ρ
            have hsum : s' + (t + 1) * ρ = s := by
              rw [hs'def]
              generalize (t + 1) * ρ = v at hcond ⊢
              omega
            rw [hsum] at hslack
            have hexact : ledger t s' + ρ * (2 * t + 1) +
                (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1)) =
                ledger (t + 1) s := by
              generalize ρ * (2 * t + 1) = w at hslack ⊢
              omega
            rw [map_nsmul, map_mul, map_mul, map_pow, map_pow]
            rw [hGmap (ρ + r) s', hGhat, hξint]
            rw [mul_smul_comm]
            congr 1
            rw [mul_pow]
            rw [← pow_mul]
            calc xi R α₀ ^ ledger t s' *
                  (((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') *
                  (xi R α₀ ^ ((2 * t + 1) * ρ) * cJ ^ ρ) *
                  xi R α₀ ^ (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1))
                = xi R α₀ ^ (ledger t s' + ρ * (2 * t + 1) +
                    (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1))) *
                  ((((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') * cJ ^ ρ) := by
                  rw [pow_add, pow_add]
                  ring
              _ = xi R α₀ ^ ledger (t + 1) s *
                  ((((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') * cJ ^ ρ) := by
                  rw [hexact]
          · rw [if_neg hcond, if_neg hcond]
            simp
        · -- The size bound.
          refine SS.sum _ _ fun ρ _ => ?_
          by_cases hcond : (t + 1) * ρ ≤ s
          · rw [if_pos hcond]
            set s' := s - (t + 1) * ρ with hs'def
            have hslack := ledger_slack t s' ρ
            have hsum : s' + (t + 1) * ρ = s := by
              rw [hs'def]
              generalize (t + 1) * ρ = v at hcond ⊢
              omega
            rw [hsum] at hslack
            set σ := ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1) with hσdef
            have hexact : ledger t s' + ρ * (2 * t + 1) + σ = ledger (t + 1) s := by
              rw [hσdef]
              generalize ρ * (2 * t + 1) = w at hslack ⊢
              omega
            refine SS.mono (SS.nsmul (SS.mul (SS.mul (hGsize (ρ + r) s')
              (SS.pow hGhatSize ρ)) (SS.pow hmξ σ)) _) ?_
            -- Arithmetic: the sizes recombine into `b * (ledger (t+1) s + 1)`.
            have h1 : σ * mξ ≤ σ * b := Nat.mul_le_mul_left _ hmξb
            have h2 : b * (ledger t s' + 1) + ρ * (b * (2 * t + 1)) + σ * b =
                b * (ledger t s' + ρ * (2 * t + 1) + σ + 1) := by ring
            have h3 : ledger t s' + ρ * (2 * t + 1) + σ + 1 = ledger (t + 1) s + 1 := by
              rw [hexact]
            calc b * (ledger t s' + 1) + ρ * (b * (2 * t + 1)) + σ * mξ
                ≤ b * (ledger t s' + 1) + ρ * (b * (2 * t + 1)) + σ * b := by omega
              _ = b * (ledger t s' + ρ * (2 * t + 1) + σ + 1) := h2
              _ = b * (ledger (t + 1) s + 1) := by rw [h3]
          · rw [if_neg hcond]
            exact SS.zero _

end Ledger
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
variable (SS : SizeSystem A)
variable (R : K[X][X]) (R₀ : A[X][X]) (α₀ : K) (a₀ : A) (ξ₀ : A)
variable (d mR mα mξ : ℕ)
section Ledger
variable (hR : R = R₀.map (mapRingHom (algebraMap A K)))
variable (hα : α₀ = algebraMap A K a₀)
variable (hd : R₀.natDegree ≤ d)
variable (hmR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR)
variable (hmα : SS.P a₀ mα)
variable (hmξ : SS.P ξ₀ mξ)
variable (hξint : algebraMap A K ξ₀ = xi R α₀)
variable (hξ0 : xi R α₀ ≠ 0)

include hR hα hd hmR hmα hmξ hξint hξ0 in
/-- **The linear size bound for the jet coefficients** — the load-bearing estimate.

The `(t+1)`-st jet coefficient, cleared by `ξ^(2t+1)`, is integral of size at most
`(mR + d·mα + mξ) · (2t + 1)`.  Linear in `t`: with heights this reads
`ht(γ_{t+1}) ≤ (D + mξ) · (2t + 1) = O(D_Z · t)`, which is what puts a term
linear in the chosen jet order — not `D_X` — into the §3 branch bound. -/
theorem jet_coeff_integral (t : ℕ) :
    ∃ g : A,
      algebraMap A K g = xi R α₀ ^ (2 * t + 1) * ((jet R α₀ (t + 1)).coeff (t + 1)) ∧
      SS.P g (ledgerConst mR d mα mξ * (2 * t + 1)) := by
  obtain ⟨g, hg, hgs⟩ :=
    jet_ledger SS R R₀ α₀ a₀ ξ₀ d mR mα mξ hR hα hd hmR hmα hmξ hξint hξ0 t 0 (t + 1)
  rw [ledger_self_succ, hasseDeriv_zero'] at hg
  rw [ledger_self_succ] at hgs
  refine ⟨-g, ?_, ?_⟩
  · rw [map_neg, hg, jet_coeff_succ_self, pow_succ]
    field_simp
  · exact SS.neg (SS.mono hgs (by omega))

end Ledger
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial

/-- **Uniqueness of a Hensel lift, finite form.**

If `y₁` and `y₂` are both roots of `f`, differ by a nilpotent, and `f'(y₁)` is a unit,
then `y₁ = y₂`.

Applied with the ambient ring `A[U] / (U ^ (r+1))` — in which `U` is nilpotent — this
says the truncated implicit-function recursion determines its solution uniquely.  The
hypothesis `IsUnit (f.derivative.eval y₁)` is the simple-root condition `ξ ≠ 0` of §1. -/
theorem eq_of_sub_isNilpotent_of_isUnit_derivative
    {B : Type*} [CommRing B] (f : B[X]) {y₁ y₂ : B}
    (h₁ : f.eval y₁ = 0) (h₂ : f.eval y₂ = 0)
    (hnil : IsNilpotent (y₂ - y₁))
    (hunit : IsUnit (f.derivative.eval y₁)) :
    y₂ = y₁ := by
  obtain ⟨c, hc⟩ := f.binomExpansion y₁ (y₂ - y₁)
  have hy : y₁ + (y₂ - y₁) = y₂ := by ring
  rw [hy, h₂, h₁] at hc
  -- `hc : 0 = 0 + f'(y₁) * (y₂ - y₁) + c * (y₂ - y₁) ^ 2`
  have hfac : (y₂ - y₁) * (f.derivative.eval y₁ + c * (y₂ - y₁)) = 0 := by
    linear_combination -hc
  have hnil' : IsNilpotent (c * (y₂ - y₁)) :=
    (Commute.all c (y₂ - y₁)).isNilpotent_mul_left hnil
  have hu : IsUnit (f.derivative.eval y₁ + c * (y₂ - y₁)) :=
    hnil'.isUnit_add_left_of_commute hunit (Commute.all _ _)
  have hzero : y₂ - y₁ = 0 := (hu.mul_left_eq_zero).mp hfac
  exact sub_eq_zero.mp hzero

end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial

/-- **One Newton step.**

If `f(a)` lies in an ideal `J` and `f'(a)` is invertible with inverse `u`, then the
Newton update `a - f(a) * u` stays in `a + J` and drives `f` into `J ^ 2`.

Iterating this is what produces the jet `Γ_k`; the quadratic gain `J → J ^ 2` is why
only finitely many steps are needed when `J` is nilpotent. -/
theorem eval_newton_mem_sq {B : Type*} [CommRing B] (f : B[X]) (a : B) (J : Ideal B)
    (hfa : f.eval a ∈ J) (u : B) (hu : f.derivative.eval a * u = 1) :
    f.eval (a - f.eval a * u) ∈ J ^ 2 ∧ (a - f.eval a * u) - a ∈ J := by
  have hdJ : -(f.eval a * u) ∈ J := neg_mem (Ideal.mul_mem_right _ _ hfa)
  have hda : a + -(f.eval a * u) = a - f.eval a * u := by ring
  obtain ⟨c, hc⟩ := f.binomExpansion a (-(f.eval a * u))
  have hcancel : f.derivative.eval a * -(f.eval a * u) = -f.eval a := by
    calc f.derivative.eval a * -(f.eval a * u)
        = -(f.eval a * (f.derivative.eval a * u)) := by ring
      _ = -(f.eval a * 1) := by rw [hu]
      _ = -f.eval a := by ring
  have hfd : f.eval (a - f.eval a * u) = c * (-(f.eval a * u)) ^ 2 := by
    rw [← hda, hc, hcancel]; ring
  refine ⟨?_, ?_⟩
  · rw [hfd]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hdJ 2)
  · have : (a - f.eval a * u) - a = -(f.eval a * u) := by ring
    rw [this]; exact hdJ

/-- **Existence of the jet: Hensel lifting over a nilpotent ideal.**

If `J ^ (2 ^ n) = ⊥`, `f(a) ∈ J`, and `f'(a)` is a unit, then `f` has a genuine root
congruent to `a` modulo `J`.

This is §1's finite recursion.  The proof is `2 ^ n`-fold Newton iteration: each step
squares the ideal, so nilpotency alone terminates it.  No completion, no formal power
series, and no restriction on the characteristic. -/
theorem exists_root_of_pow_eq_bot {B : Type*} [CommRing B] (f : B[X]) :
    ∀ (n : ℕ) (J : Ideal B), J ^ (2 ^ n) = ⊥ → ∀ a : B, f.eval a ∈ J →
      IsUnit (f.derivative.eval a) → ∃ b : B, f.eval b = 0 ∧ b - a ∈ J := by
  intro n
  induction n with
  | zero =>
      intro J hJ a hfa _
      refine ⟨a, ?_, by simp⟩
      have hJb : J = ⊥ := by simpa using hJ
      rw [hJb] at hfa
      simpa using hfa
  | succ n ih =>
      intro J hJ a hfa hunit
      obtain ⟨v, hv⟩ := hunit
      have hu : f.derivative.eval a * (↑v⁻¹ : B) = 1 := by
        rw [← hv]; exact v.mul_inv
      obtain ⟨hstep, hdiff⟩ := eval_newton_mem_sq f a J hfa (↑v⁻¹ : B) hu
      set a₁ := a - f.eval a * (↑v⁻¹ : B) with ha₁
      -- Every element of `J` is nilpotent.
      have hJnil : ∀ x ∈ J, IsNilpotent x := by
        intro x hx
        refine ⟨2 ^ (n + 1), ?_⟩
        have hmem := Ideal.pow_mem_pow hx (2 ^ (n + 1))
        rw [hJ] at hmem
        simpa using hmem
      -- The derivative stays invertible along the iteration.
      have hunit₁ : IsUnit (f.derivative.eval a₁) := by
        obtain ⟨c, hcc⟩ := sub_dvd_eval_sub a₁ a f.derivative
        have hmem : f.derivative.eval a₁ - f.derivative.eval a ∈ J := by
          rw [hcc]; exact Ideal.mul_mem_right _ _ hdiff
        have hnil : IsNilpotent (f.derivative.eval a₁ - f.derivative.eval a) := hJnil _ hmem
        have hres := hnil.isUnit_add_left_of_commute (hv ▸ v.isUnit) (Commute.all _ _)
        have heq : f.derivative.eval a + (f.derivative.eval a₁ - f.derivative.eval a)
            = f.derivative.eval a₁ := by ring
        rwa [heq] at hres
      -- Recurse with the squared ideal.
      have hJ2 : (J ^ 2) ^ (2 ^ n) = ⊥ := by
        rw [← pow_mul]
        have htwo : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
        rw [htwo]; exact hJ
      obtain ⟨b, hb0, hbd⟩ := ih (J ^ 2) hJ2 a₁ hstep hunit₁
      refine ⟨b, hb0, ?_⟩
      have hsplit : b - a = (b - a₁) + (a₁ - a) := by ring
      rw [hsplit]
      exact add_mem (Ideal.pow_le_self (by norm_num) hbd) hdiff

/-- The same statement for an arbitrary nilpotent ideal. -/
theorem exists_root_of_isNilpotent {B : Type*} [CommRing B] (f : B[X]) (J : Ideal B)
    {N : ℕ} (hJ : J ^ N = ⊥) (a : B) (hfa : f.eval a ∈ J)
    (hunit : IsUnit (f.derivative.eval a)) :
    ∃ b : B, f.eval b = 0 ∧ b - a ∈ J := by
  refine exists_root_of_pow_eq_bot f N J ?_ a hfa hunit
  have hle : N ≤ 2 ^ N := Nat.le_of_lt (Nat.lt_two_pow_self)
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ N = N + d := ⟨2 ^ N - N, by omega⟩
  rw [hd, pow_add, hJ]
  simp

end JBAgreement
end
end

section
namespace JBAgreement
open Polynomial Finset

/-- The size bound for the coefficients of the cleared jet: linear in `r`. -/
def clearedBound (mR d mα mξ r : ℕ) : ℕ :=
  (2 * r + 1) * (ledgerConst mR d mα mξ + mξ) + mα

end JBAgreement
end

section
namespace JBAgreement
open Polynomial Finset
section Cleared
variable {A : Type*} [CommRing A] [IsDomain A]

/-- **The cleared jet.**

For a branch `R₀` over `A` with simple-root value `ξ = xi R₀ a₀ ≠ 0`, there is a
polynomial `γ̂ ∈ A[U]` of degree at most `r` such that

* `γ̂(0) = ξ^(2r+1) · a₀` — the constant term is the (cleared) initial value;
* every coefficient has size at most `clearedBound …`, *linear in `r`*, and this
  simultaneously for a whole family of size systems (the `T`-degree and the `Z`-height
  are both needed, of the *same* `γ̂`; the integral model is unique because `A → Frac A`
  is injective, so the bounds can be collected);
* `U^{r+1}` divides `evalH R₀ d (ξ^(2r+1)) γ̂ - C (ξ^((2r+1)d) · H₀)`.

The third item is the jet property in cleared, specialisation-stable form.  All three are
read off from the generic jet over `Frac A` and transported back by injectivity of
`A → Frac A`; `K` never appears in the statement. -/
theorem exists_clearedJet {Idx : Type*} [Nonempty Idx]
    (SS : Idx → SizeSystem A) (R₀ : A[X][X]) (a₀ : A) (d r : ℕ) (mR mα mξ : Idx → ℕ)
    (hd : R₀.natDegree ≤ d)
    (hmR : ∀ o j i, (SS o).P ((R₀.coeff j).coeff i) (mR o))
    (hmα : ∀ o, (SS o).P a₀ (mα o)) (hmξ : ∀ o, (SS o).P (xi R₀ a₀) (mξ o))
    (hξ0 : xi R₀ a₀ ≠ 0) :
    ∃ γ : A[X], γ.natDegree ≤ r ∧
      γ.coeff 0 = xi R₀ a₀ ^ (2 * r + 1) * a₀ ∧
      (∀ o i, (SS o).P (γ.coeff i) (clearedBound (mR o) d (mα o) (mξ o) r)) ∧
      (X : A[X]) ^ (r + 1) ∣
        evalH R₀ d (xi R₀ a₀ ^ (2 * r + 1)) γ
          - C (xi R₀ a₀ ^ ((2 * r + 1) * d) * jetConst R₀ a₀) := by
  classical
  set K := FractionRing A
  set ψ : A →+* K := algebraMap A K with hψ
  have hinj : Function.Injective ψ := IsFractionRing.injective A K
  set ξ₀ : A := xi R₀ a₀ with hξ₀
  set R : K[X][X] := R₀.map (mapRingHom ψ) with hRdef
  set α₀ : K := ψ a₀ with hα₀
  have hξint : ψ ξ₀ = xi R α₀ := (xi_map ψ R₀ a₀).symm
  have hHint : ψ (jetConst R₀ a₀) = jetConst R α₀ := (jetConst_map ψ R₀ a₀).symm
  have hξK : xi R α₀ ≠ 0 := by
    rw [← hξint]
    exact fun h => hξ0 (hinj (by simpa using h))
  have hRd : R.natDegree ≤ d := le_trans natDegree_map_le hd
  set c : A := ξ₀ ^ (2 * r + 1) with hc
  -- Integral models for every coefficient of the cleared jet, with *all* the size
  -- bounds at once: the model is unique, since `ψ` is injective.
  have key : ∀ t : ℕ, ∃ g : A, ψ g = ψ c * (jet R α₀ r).coeff t ∧
      ∀ o, (SS o).P g (clearedBound (mR o) d (mα o) (mξ o) r) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · refine ⟨c * a₀, ?_, fun o => ?_⟩
      · rw [map_mul, jet_coeff_zero]
      · refine (SS o).mono ((SS o).mul ((SS o).pow (hmξ o) _) (hmα o)) ?_
        rw [clearedBound]
        have : (2 * r + 1) * mξ o
            ≤ (2 * r + 1) * (ledgerConst (mR o) d (mα o) (mξ o) + mξ o) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rcases Nat.lt_or_ge t' r with htk | htk
    · -- The model supplied by the ledger, cleared up to the uniform exponent `2r+1`.
      have base : ∀ o, ∃ g : A,
          ψ g = xi R α₀ ^ (2 * t' + 1) * ((jet R α₀ (t' + 1)).coeff (t' + 1)) ∧
            (SS o).P g (ledgerConst (mR o) d (mα o) (mξ o) * (2 * t' + 1)) := fun o =>
        jet_coeff_integral (SS o) R R₀ α₀ a₀ ξ₀ d (mR o) (mα o) (mξ o)
          hRdef hα₀ hd (hmR o) (hmα o) (hmξ o) hξint hξK t'
      obtain ⟨g₀, hg₀, _⟩ := base (Classical.arbitrary Idx)
      refine ⟨ξ₀ ^ (2 * r + 1 - (2 * t' + 1)) * g₀, ?_, fun o => ?_⟩
      · rw [map_mul, map_pow, hg₀, hξint, jet_coeff_stable R α₀ (t' + 1) r (by omega)]
        rw [hc, map_pow, hξint, ← mul_assoc, ← pow_add]
        congr 2
        omega
      · obtain ⟨g, hg, hgs⟩ := base o
        have hgg : g = g₀ := hinj (by rw [hg, hg₀])
        rw [hgg] at hgs
        refine (SS o).mono ((SS o).mul ((SS o).pow (hmξ o) _) hgs) ?_
        rw [clearedBound]
        calc (2 * r + 1 - (2 * t' + 1)) * mξ o
              + ledgerConst (mR o) d (mα o) (mξ o) * (2 * t' + 1)
            ≤ (2 * r + 1) * mξ o + ledgerConst (mR o) d (mα o) (mξ o) * (2 * r + 1) :=
              Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
                (Nat.mul_le_mul_left _ (by omega))
          _ = (2 * r + 1) * (ledgerConst (mR o) d (mα o) (mξ o) + mξ o) := by ring
          _ ≤ (2 * r + 1) * (ledgerConst (mR o) d (mα o) (mξ o) + mξ o) + mα o :=
              Nat.le_add_right _ _
    · refine ⟨0, ?_, fun o => (SS o).zero _⟩
      rw [map_zero, coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_jet_le R α₀ r) (by omega)), mul_zero]
  choose G hGmap hGsize using key
  refine ⟨∑ t ∈ range (r + 1), monomial t (G t), ?_, ?_, ?_, ?_⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun t ht =>
      le_trans (natDegree_monomial_le _) (by simpa using Nat.lt_succ_iff.mp (mem_range.mp ht))
  all_goals
    have hcoeff : ∀ i, (∑ t ∈ range (r + 1), monomial t (G t)).coeff i =
        if i < r + 1 then G i else 0 := by
      intro i
      rw [finsetSum_coeff]
      simp [coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  · rw [hcoeff 0, if_pos (by omega)]
    have := hGmap 0
    rw [jet_coeff_zero] at this
    rw [hα₀] at this
    exact hinj (by rw [this, ← map_mul])
  · intro o i
    rw [hcoeff i]
    split_ifs with h
    · exact hGsize i o
    · exact (SS o).zero _
  · set γ : A[X] := ∑ t ∈ range (r + 1), monomial t (G t) with hγ
    have hmapγ : γ.map ψ = C (ψ c) * jet R α₀ r := by
      apply Polynomial.ext
      intro i
      rw [coeff_map, hcoeff i, coeff_C_mul]
      split_ifs with h
      · exact hGmap i
      · rw [map_zero, coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (natDegree_jet_le R α₀ r) (by omega)), mul_zero]
    have hev : (evalH R₀ d c γ).map ψ = C (ψ c ^ d) * R.eval (jet R α₀ r) := by
      rw [← evalH_map ψ R₀ d c γ, hmapγ, ← hRdef, evalH_C_mul R hRd]
    have hcoeff0 : (evalH R₀ d c γ).coeff 0 = c ^ d * jetConst R₀ a₀ := by
      refine hinj ?_
      have := congrArg (fun p => Polynomial.coeff p 0) hev
      simp only [coeff_map, coeff_C_mul] at this
      rw [this, coeff_zero_eval_jet, ← hHint, ← map_pow, ← map_mul]
    have hcoeffs : ∀ s, 1 ≤ s → s ≤ r → (evalH R₀ d c γ).coeff s = 0 := by
      intro s hs1 hsk
      refine hinj ?_
      have := congrArg (fun p => Polynomial.coeff p s) hev
      simp only [coeff_map, coeff_C_mul] at this
      rw [this, coeff_eval_jet_eq_zero R α₀ hξK r s hs1 hsk, mul_zero, map_zero]
    rw [X_pow_dvd_iff]
    intro i hi
    rw [coeff_sub, coeff_C]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hcoeff0, if_pos rfl, hc, ← pow_mul, sub_self]
    · rw [hcoeffs i hipos (by omega), if_neg (by omega), sub_zero]

end Cleared
end JBAgreement
end

section
namespace JBAgreement
open Polynomial Finset
section Spec
variable {A : Type*} [CommRing A] {F : Type*} [Field F]

/-- Backwards-compatible specialization theorem using the original clearing exponent. -/
theorem clearedJet_spec (R₀ : A[X][X]) (a₀ : A) (d r : ℕ) (hd : R₀.natDegree ≤ d)
    (γ : A[X]) (hγdeg : γ.natDegree ≤ r)
    (hγ0 : γ.coeff 0 = xi R₀ a₀ ^ (2 * r + 1) * a₀)
    (hγjet : (X : A[X]) ^ (r + 1) ∣
      evalH R₀ d (xi R₀ a₀ ^ (2 * r + 1)) γ
        - C (xi R₀ a₀ ^ ((2 * r + 1) * d) * jetConst R₀ a₀))
    (φ : A →+* F) (hφH : φ (jetConst R₀ a₀) = 0) (hφξ : φ (xi R₀ a₀) ≠ 0)
    (π : F[X]) (hπdeg : π.natDegree ≤ r) (hπ0 : π.coeff 0 = φ a₀)
    (hπroot : (R₀.map (mapRingHom φ)).eval π = 0) :
    C (φ (xi R₀ a₀) ^ (2 * r + 1)) * π = γ.map φ :=
  clearedJet_spec_exp R₀ a₀ d r (2 * r + 1) hd γ hγdeg hγ0 hγjet
    φ hφH hφξ π hπdeg hπ0 hπroot

end Spec
end JBAgreement
end

-- ===== from `LvmWhirParamsJp` =====

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd JBAgreement JB.CodingTheory.InterleavedJohnson
set_option exponentiation.threshold 512
section

/-- The codes of `C_main`'s Johnson levels at P8. -/
noncomputable def codesMain23J : ℕ → LevelCode
  | 0 => codeJ17R1
  | 1 => codeJ13R2
  | _ => codeJ9R3

end
end LeanVM.Protocol.Whir.Sound
end
end

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd JBAgreement JB.CodingTheory.InterleavedJohnson
set_option exponentiation.threshold 512
section

/-- `C_main` at P8, Johnson: `(6,1,33) (4,2,17) (4,3,11)`, `g = 4`, OOD; root `0` of `n₀`. -/
def cfgMain23J (n₀ : ℕ) : WhirConfig := ⟨⟨23, [⟨6, 1, 33⟩, ⟨4, 2, 17⟩, ⟨4, 3, 11⟩], 8, 0, n₀, false, 4⟩, true⟩

end
end LeanVM.Protocol.Whir.Sound
end
end

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd JBAgreement JB.CodingTheory.InterleavedJohnson
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_main` at P8, Johnson.** -/
theorem whirEps_main23J (n₀ : ℕ) :
    whirEpsJ codesMain23J (cfgMain23J n₀).grind (cfgMain23J n₀).levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  obtain ⟨f0, f1, f2, -, -, o0, o1, -, q0, q1, q2, -⟩ := eps_P8J
  have a : ∀ {x : ENNReal}, x ≤ (2 : ENNReal)⁻¹ ^ 21 → x ≤ (2 : ENNReal)⁻¹ ^ 20 :=
    fun h ↦ h.trans (inv_two_pow_anti (by norm_num))
  simp only [whirEpsJ, cfgMain23J, levelEpsJ, max_le_iff]
  exact ⟨⟨a f0, a o0⟩, disc_le 4 q0, ⟨a f1, a o1⟩, disc_le 4 q1, a f2, disc_le 4 q2,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

/-- **`εmax` of `C_rec` at P8, Johnson** (J2). -/
theorem whirEps_rec18J :
    whirEpsJ codesRec18J cfgRec18J.grind cfgRec18J.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  obtain ⟨-, -, -, f0, f1, -, -, o0, -, -, q1, q0⟩ := eps_P8J
  have a : ∀ {x : ENNReal}, x ≤ (2 : ENNReal)⁻¹ ^ 21 → x ≤ (2 : ENNReal)⁻¹ ^ 20 :=
    fun h ↦ h.trans (inv_two_pow_anti (by norm_num))
  simp only [whirEpsJ, cfgRec18J, levelEpsJ, max_le_iff]
  exact ⟨⟨a f0, a o0⟩, disc_le 4 q0, a f1, disc_le 4 q1,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

/-- **`εmax` of `C_rec` at P8, unique decoding** (J1). -/
theorem whirEps_rec18U :
    whirEpsUd codesRec18U cfgRec18U.grind cfgRec18U.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  obtain ⟨f0, f1, q0, q1⟩ := eps_rec18U
  have a : ∀ {x : ENNReal}, x ≤ (2 : ENNReal)⁻¹ ^ 21 → x ≤ (2 : ENNReal)⁻¹ ^ 20 :=
    fun h ↦ h.trans (inv_two_pow_anti (by norm_num))
  simp only [whirEpsUd, cfgRec18U, levelEpsUd, max_le_iff]
  exact ⟨⟨a f0, disc_le 4 q0⟩, a f1, disc_le 4 q1, eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

theorem ladderArith_main23J (n₀ : ℕ) :
    LadderArithJ (cfgMain23J n₀).μ (cfgMain23J n₀).per codesMain23J 0 0 (cfgMain23J n₀).levels := by
  obtain ⟨-, -, -, -, -, o0, o1, -, q0, q1, q2, -⟩ := eps_P8J
  have h := inv_two_pow_lt_one (c := 16) (by norm_num)
  have ho := inv_two_pow_lt_one (c := 21) (by norm_num)
  exact ⟨rfl, rfl, o0.trans_lt ho, q0.trans_lt h, by norm_num [cfgMain23J, codesMain23J, codeJ17R1],
    rfl, rfl, o1.trans_lt ho, q1.trans_lt h, by norm_num [cfgMain23J, codesMain23J, codeJ13R2],
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain23J, codesMain23J, codeJ9R3]⟩

end
end LeanVM.Protocol.Whir.Sound
end
end

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd JBAgreement JB.CodingTheory.InterleavedJohnson
set_option exponentiation.threshold 512
section

/-- **`C_main`'s stacked opening at P8, Johnson.** -/
noncomputable def stackedMain23JSpec (n₀ : ℕ) (hn₀ : 0 < n₀) (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine (cfgMain23J n₀).μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ (cfgMain23J n₀) claims)
      (fun h ↦ StackedPreUd (cfgMain23J n₀).toUdConfig (codesMain23J 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesMain23J 0)) T :=
  stackedSpecJ claims hcl rfl rfl rfl (by norm_num [cfgMain23J]) rfl hn₀ (by norm_num [cfgMain23J])
    (by norm_num [cfgMain23J]) (ladderArith_main23J n₀) (whirEps_main23J n₀) T

/-- **`C_rec`'s stacked opening at P8, Johnson** (J2). -/
noncomputable def stackedRec18JSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec18J.μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ cfgRec18J claims)
      (fun h ↦ StackedPreUd cfgRec18J.toUdConfig (codesRec18J 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec18J 0)) T :=
  stackedSpecJ claims hcl rfl rfl rfl (by norm_num [cfgRec18J]) rfl (by norm_num [cfgRec18J])
    (by norm_num [cfgRec18J]) (by norm_num [cfgRec18J]) ladderArith_rec18J whirEps_rec18J T

/-- **`C_rec`'s stacked opening at P8, unique decoding** (J1). -/
noncomputable def stackedRec18USpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec18U.μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ cfgRec18U claims)
      (fun h ↦ StackedPreUd cfgRec18U.toUdConfig (codesRec18U 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec18U 0)) T :=
  (stackedUdSpec (cfg := cfgRec18U.toUdConfig) (codes := codesRec18U) claims hcl rfl rfl
    (by norm_num [cfgRec18U]) rfl (by norm_num [cfgRec18U]) (by norm_num [cfgRec18U])
    (by norm_num [cfgRec18U]) ladderArith_rec18U whirEps_rec18U T).congr
    (verifyStackedJ_ud cfgRec18U rfl claims).symm

/-- `C_main`'s candidates at P8 (Johnson): at most `7824`. -/
theorem candidates_main23J_ncard_le (W : Word) :
    (Candidates 23 1 (codesMain23J 0).thr W).ncard ≤ 7824 :=
  candidates_ncard_le (codesMain23J 0) (by norm_num) rfl rfl W

/-- `C_rec`'s candidates at P8 (Johnson, J2): at most `2536`. -/
theorem candidates_rec18J_ncard_le (W : Word) :
    (Candidates 18 3 (codesRec18J 0).thr W).ncard ≤ 2536 :=
  candidates_ncard_le (codesRec18J 0) (by norm_num) rfl rfl W

end
end LeanVM.Protocol.Whir.Sound
end
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd JBAgreement JB.CodingTheory.InterleavedJohnson
set_option exponentiation.threshold 512
section

/-- **`εmax` of J2′'s `C_rec` at P8.** -/
theorem whirEps_rec18Jp :
    whirEpsJ codesRec18Jp cfgRec18Jp.grind cfgRec18Jp.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  obtain ⟨f0, f1, o0, q0, q1⟩ := eps_rec18Jp
  have a : ∀ {x : ENNReal}, x ≤ (2 : ENNReal)⁻¹ ^ 21 → x ≤ (2 : ENNReal)⁻¹ ^ 20 :=
    fun h ↦ h.trans (inv_two_pow_anti (by norm_num))
  simp only [whirEpsJ, cfgRec18Jp, levelEpsJ, max_le_iff]
  exact ⟨⟨a f0, a o0⟩, disc_le 4 q0, a f1, disc_le 4 q1,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd JBAgreement JB.CodingTheory.InterleavedJohnson
set_option exponentiation.threshold 512
section

/-- **J2′'s `C_rec` opening up to the residual, relativised** (P20), `εmax = 2^-128`; post `PostR`
(`GoodRes ∨ ResC`); the follower's allowance is the final query group's `2^-14·eQueryFinal`. -/
noncomputable def stackedPrefixRec20JpSpec (Good : Column cfgRec20Jp.μ → Prop)
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20Jp.μ c.1) :
    Spec (stackPrefixJ cfgRec20Jp claims)
      (fun h ↦ StackedPreR cfgRec20Jp.toUdConfig (codesRec20Jp 0) Good claims (commits h))
      (fun x h ↦ PostR cfgRec20Jp.μ laneBits
        (fun point ↦ dot (powers x.1 claims.length) (claims.map fun c ↦ c.1 point)) codesRec20Jp
        cfgRec20Jp.c₀ cfgRec20Jp.n₀ 0 0 cfgRec20Jp.levels
        (gdRoot (codesRec20Jp 0) Good (viewC cfgRec20Jp.c₀ cfgRec20Jp.n₀ (commits h))) x.2 h)
      ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesRec20Jp 0))
      ((2 : ENNReal)⁻¹ ^ 14 * eQueryFinal (codesRec20Jp 1) 77) :=
  stackedPrefixSpecR Good claims hcl rfl rfl (by norm_num [cfgRec20Jp]) rfl
    (by norm_num [cfgRec20Jp]) (by norm_num [cfgRec20Jp]) (by norm_num [cfgRec20Jp])
    ladderArith_rec20Jp (le_of_add_margin whirEps_rec20Jp)

/-- **J2′'s `C_rec` after the residual** (P20; final level `(4, 3, 77)`, index `1`, code `codeJ9R3`,
`6` fold challenges before it): from `ResC`, rejection but for `2^-14·eQueryFinal` and `eTail`. -/
noncomputable def finSuffixRec20JpSpec (w : List E → E) (hw : IsMultiaffine 19 w)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ 19 laneBits 8 1 2 14 false w 1 ⟨4, 3, 77⟩ a)
      (fun h ↦ ResC 19 laneBits w 1 codeJ9R3 4 6 a.1 a.2 (viewC 1 2 (commits h)))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) ((2 : ENNReal)⁻¹ ^ 14 * eQueryFinal codeJ9R3 77) 0 :=
  finSuffixSpecR (level := ⟨4, 3, 77⟩) ⟨hw, by norm_num, by norm_num [codeJ9R3], rfl, by norm_num,
      by norm_num, by norm_num [codeJ9R3]⟩ (by norm_num)
    (eps_rec20Jp.2.2.2.2.trans_lt seven_inv_lt_one)
    ((disc7 eps_rec20Jp.2.2.2.2).trans (le_self_add.trans_eq seven_add_one))
    (eTail_le.trans (inv_two_pow_anti (by norm_num))) a

/-- **J2′'s `C_rec` at P8, up to the residual**, `εmax = 2^-20`. -/
noncomputable def stackedPrefixRec18JpSpec (Good : Column cfgRec18Jp.μ → Prop)
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec18Jp.μ c.1) :
    Spec (stackPrefixJ cfgRec18Jp claims)
      (fun h ↦ StackedPreR cfgRec18Jp.toUdConfig (codesRec18Jp 0) Good claims (commits h))
      (fun x h ↦ PostR cfgRec18Jp.μ laneBits
        (fun point ↦ dot (powers x.1 claims.length) (claims.map fun c ↦ c.1 point)) codesRec18Jp
        cfgRec18Jp.c₀ cfgRec18Jp.n₀ 0 0 cfgRec18Jp.levels
        (gdRoot (codesRec18Jp 0) Good (viewC cfgRec18Jp.c₀ cfgRec18Jp.n₀ (commits h))) x.2 h)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec18Jp 0))
      ((2 : ENNReal)⁻¹ ^ 4 * eQueryFinal (codesRec18Jp 1) 11) :=
  stackedPrefixSpecR Good claims hcl rfl rfl (by norm_num [cfgRec18Jp]) rfl
    (by norm_num [cfgRec18Jp]) (by norm_num [cfgRec18Jp]) (by norm_num [cfgRec18Jp])
    ladderArith_rec18Jp whirEps_rec18Jp

/-- **J2′'s `C_rec` at P8 after the residual** (final level `(4, 3, 11)`, code `codeJ8R3`). -/
noncomputable def finSuffixRec18JpSpec (w : List E → E) (hw : IsMultiaffine 18 w)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ 18 laneBits 8 1 2 4 false w 1 ⟨4, 3, 11⟩ a)
      (fun h ↦ ResC 18 laneBits w 1 codeJ8R3 4 6 a.1 a.2 (viewC 1 2 (commits h)))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 20) ((2 : ENNReal)⁻¹ ^ 4 * eQueryFinal codeJ8R3 11) 0 :=
  finSuffixSpecR (level := ⟨4, 3, 11⟩) ⟨hw, by norm_num, by norm_num [codeJ8R3], rfl, by norm_num,
      by norm_num, by norm_num [codeJ8R3]⟩ (by norm_num)
    (eps_rec18Jp.2.2.2.2.trans_lt (inv_two_pow_lt_one (by norm_num)))
    (disc_le 4 eps_rec18Jp.2.2.2.2)
    (eTail_le.trans (inv_two_pow_anti (by norm_num))) a

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd JBAgreement JB.CodingTheory.InterleavedJohnson
set_option exponentiation.threshold 512
section

/-- J2′'s `C_rec` root candidates at P8: at most `1024`. -/
theorem candidates_rec18Jp_ncard_le (W : Word) :
    (Candidates 18 2 (codesRec18Jp 0).thr W).ncard ≤ 1024 :=
  candidates_ncard_le (codesRec18Jp 0) (by norm_num) rfl rfl W

end
end LeanVM.Protocol.Whir.Sound
end

-- ===== from `LvmWhirDoomJ2` =====

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset
section

/-- **The restricted final doom**: the residual `f` is not the fold of any good candidate of `W`. -/
def FinalRDoomJ (μ R A : ℕ) (Good : Column μ → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E) : Prop :=
  ∀ q ∈ Candidates μ R A W, Good q → f ≠ foldMsg α q

/-- **Luck over the list**: some member of the list of `O` has an agreement set that the fold by
`α` enlarges. -/
def FoldAllLuckL {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Submodule E (ι → E)) (A : ℕ)
    {m : ℕ} (α : Fin m → E) (O : (Fin m → Bool) → ι → E) : Prop :=
  ∃ U ∈ iList C A O, FoldAllLuck α O U

/-- The luck over the list contains the luck of every member. -/
theorem foldAllLuck_of_luckL {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Submodule E (ι → E)}
    {A m : ℕ} {α : Fin m → E} {O U : (Fin m → Bool) → ι → E} (hU : U ∈ iList C A O)
    (h : ¬ FoldAllLuckL C A α O) : ¬ FoldAllLuck α O U :=
  fun hl ↦ h ⟨U, hU, hl⟩

open Classical in
/-- **One round's luck over the list**: at most `L·n` challenges `s` make some member's agreement
set grow under the fold (`card_foldLuck_le` for each member). -/
theorem card_foldLuckL_le {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]
    (C : Submodule E (ι → E)) (A L : ℕ) (O : Bool × ρ → ι → E)
    (hL : (iList C A O).card ≤ L) :
    (univ.filter fun s : E ↦ ∃ U ∈ iList C A O,
        ¬ agreeSet (fold s O) (fold s U) ⊆ agreeSet O U).card ≤ L * Fintype.card ι := by
  refine (card_filter_exists_le (iList C A O) _ (N := Fintype.card ι) fun U _ ↦
    card_foldLuck_le O U).trans ?_
  exact Nat.mul_le_mul_right _ hL

/-- **The extractor's facts at the Johnson radius** (the list version of `ud_extract`): if the
residual is the fold of a good candidate (`¬ FinalRDoomJ`), that candidate `q` agrees with the word
on at least `A` columns, and off the luck of its pair the agreement set of the folded word with the
residual's encoding is the word's agreement set with `q`'s encoding. -/
theorem j_extract {μ R A : ℕ} (h64 : μ - laneBits + R ≤ 64)
    (Good : Column μ → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E) (hR : ¬ FinalRDoomJ μ R A Good W α f) :
    ∃ q ∈ Candidates μ R A W, Good q ∧ f = foldMsg α q ∧
      A ≤ (agreeSet (laneRows μ R W) (encRows μ R q)).card ∧
      (¬ FoldAllLuck α (laneRows μ R W) (encRows μ R q) →
        agreeSet (foldAll α (laneRows μ R W)) (fun _ ↦ enc (μ - laneBits) R f) =
          agreeSet (laneRows μ R W) (encRows μ R q)) := by
  classical
  simp only [FinalRDoomJ, not_forall, not_not, exists_prop] at hR
  obtain ⟨q, hq, hgood, hf⟩ := hR
  set C := rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
  have hmem : encRows μ R q ∈ iList C A (laneRows μ R W) := by
    rw [encRows_eq]; exact comp_mem_iList C (bitsEquiv laneBits) (mem_iList_of_candidate h64 hq)
  have heq : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R f) = foldAll α (encRows μ R q) := by
    rw [foldAll_encRows, hf]
  refine ⟨q, hq, hgood, hf, ?_, fun hluck ↦ ?_⟩
  · exact (isClose_iff_le_card_agreeSet A _ _).mp ((mem_iList _ _ _ _).mp hmem).2
  · rw [heq]
    exact agreeSet_foldAll_eq (not_not.mp hluck)

/-- **The restricted doom is never stronger than v1's**: in the unique-decoding range, not doomed
at the commitment and at the final residual (`ud_extract`'s hypotheses) implies `¬ FinalRDoomJ`. -/
theorem not_finalRDoomJ_of_ud {μ R A : ℕ} (hμ : laneBits ≤ μ) (h64 : μ - laneBits + R ≤ 64)
    (hud : 2 ^ (μ - laneBits + R) + 2 ^ (μ - laneBits) ≤ 2 * A)
    (Good : Column μ → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E) (hC : ¬ CommitDoomUd μ R A Good W)
    (hF : ¬ FinalDoomUd μ R A h64 W α f) :
    ¬ FinalRDoomJ μ R A Good W α f := by
  obtain ⟨q, hq, hgood, -, hf, -⟩ := ud_extract hμ h64 hud Good W α f hC hF
  exact fun h ↦ h q hq hgood hf

end
end LeanVM.Protocol.Whir.Sound
end
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset
section

/-- **The extractor's facts at J2′** (the list version of `ud_extract2`): a good candidate `q` of the
root, a member `V` of the level-1 list on `q`'s path after `α₀`, and the residual `f₂` on `q`'s path
after `α₀ ++ α₁` give `ud_extract2`'s relations for `q` and `V`. -/
theorem j_extract2 {μ R A ℓ₁ : ℕ} (h64 : μ - laneBits + R ≤ 64) (P₁ : LevelCode)
    (hκ : μ - laneBits = ℓ₁ + P₁.κ) (Good : Column μ → Prop) (W₀ : Word) (α₀ : Fin laneBits → E)
    (Q' : (Fin ℓ₁ → Bool) → Fin P₁.n → E) (α₁ : Fin ℓ₁ → E) (f₂ : (Fin P₁.κ → Bool) → E)
    (q : Column μ) (hq : q ∈ Candidates μ R A W₀) (hgood : Good q)
    (V : (Fin ℓ₁ → Bool) → Fin P₁.n → E) (hV : V ∈ iList P₁.code P₁.thr Q')
    (hpath : PathAt q (List.ofFn α₀) (decode P₁ V))
    (hf : ∀ x, f₂ x = qMle q (List.ofFn α₀ ++ List.ofFn α₁ ++ bitsL x)) :
    Good q ∧ joinMsg hκ (decode P₁ V) = foldMsg α₀ q ∧
      f₂ = ∑ u, eqW α₁ u • decode P₁ V u ∧
      P₁.thr ≤ (agreeSet Q' V).card ∧
      (¬ FoldAllLuck α₁ Q' V →
        agreeSet (foldAll α₁ Q') (fun _ ↦ enc P₁.κ P₁.R f₂) = agreeSet Q' V) ∧
      A ≤ (agreeSet (laneRows μ R W₀) (encRows μ R q)).card ∧
      (¬ FoldAllLuck α₀ (laneRows μ R W₀) (encRows μ R q) →
        agreeSet (foldAll α₀ (laneRows μ R W₀))
            (fun _ ↦ enc (μ - laneBits) R (foldMsg α₀ q)) =
          agreeSet (laneRows μ R W₀) (encRows μ R q)) := by
  classical
  have hcw : IsInterleavedCodeword P₁.code V := ((mem_iList _ _ _ _).mp hV).1
  have hjoin : joinMsg hκ (decode P₁ V) = foldMsg α₀ q :=
    (pathAt_zero_iff_foldMsg q α₀ _).mp ((pathAt_joinMsg_iff hκ q _ _).mpr hpath)
  have hf₂ : f₂ = ∑ u, eqW α₁ u • decode P₁ V u := by
    funext x
    rw [hf x, sum_eqW_path q _ α₁ _ hpath x]
  set C := rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
  have hmem : encRows μ R q ∈ iList C A (laneRows μ R W₀) := by
    rw [encRows_eq]; exact comp_mem_iList C (bitsEquiv laneBits) (mem_iList_of_candidate h64 hq)
  have hencV : (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R f₂) = foldAll α₁ V := by
    have hV' : foldAll α₁ V = foldAll α₁ (fun u ↦ enc P₁.κ P₁.R (decode P₁ V u)) :=
      congrArg (foldAll α₁) (funext fun u ↦ (enc_decode P₁ hcw u).symm)
    rw [hV', foldAll_enc, hf₂]
  have heq : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R (foldMsg α₀ q)) =
      foldAll α₀ (encRows μ R q) := (foldAll_encRows α₀ q).symm
  refine ⟨hgood, hjoin, hf₂,
    (isClose_iff_le_card_agreeSet _ _ _).mp ((mem_iList _ _ _ _).mp hV).2, fun hluck ↦ ?_,
    (isClose_iff_le_card_agreeSet A _ _).mp ((mem_iList _ _ _ _).mp hmem).2, fun hluck ↦ ?_⟩
  · rw [hencV]
    exact agreeSet_foldAll_eq (not_not.mp hluck)
  · rw [heq]
    exact agreeSet_foldAll_eq (not_not.mp hluck)

/-- **Luck over the list splits by rounds**: lucky for `cons s α` is a first round's luck of some
member, or the rest's luck over the folded list. -/
theorem foldAllLuckL_cons {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Submodule E (ι → E))
    (A : ℕ) {m : ℕ} (s : E) (α : Fin m → E) (O : (Fin (m + 1) → Bool) → ι → E)
    (h : FoldAllLuckL C A (Fin.cons s α : Fin (m + 1) → E) O) :
    (∃ U ∈ iList C A (splitLow O),
        ¬ agreeSet (fold s (splitLow O)) (fold s U) ⊆ agreeSet (splitLow O) U) ∨
      FoldAllLuckL C A α (fold s (splitLow O)) := by
  obtain ⟨U, hU, hl⟩ := h
  have hU' : splitLow U ∈ iList C A (splitLow O) := by
    rw [iList_splitLow]; exact Finset.mem_image_of_mem _ hU
  rcases foldAllLuck_cons s α O U hl with h1 | h2
  · exact Or.inl ⟨splitLow U, hU', h1⟩
  · exact Or.inr ⟨fold s (splitLow U), fold_mem_iList C hU' s, h2⟩

/-- **J2′'s luck in total** (P20): 6 rounds over the root's list (`L₀ = 304`, `n₀ = 2^15`) and 4 over
level 1's (`L₁ = 311`, `n₁ = 2^12`): `≤ 2^-165`. -/
theorem luckL_rec20Jp :
    ((6 * 304 * 2 ^ 15 + 4 * 311 * 2 ^ 12 : ℕ) : ENNReal) / Fintype.card E ≤ (2 : ENNReal)⁻¹ ^ 165 := by
  rw [card_E_ennreal, ← two_pow_cast]
  exact natCast_div_le_inv_pow (by positivity) (by norm_num)

end
end LeanVM.Protocol.Whir.Sound
end
