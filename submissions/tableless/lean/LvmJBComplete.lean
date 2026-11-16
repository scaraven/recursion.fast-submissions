-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBComplete.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import LvmJBClearedJet
import Mathlib.RingTheory.Polynomial.GaussLemma
import LvmJBFactorSelection
import LvmJBMain
import Mathlib.LinearAlgebra.Lagrange
import LvmJBHeight
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LvmJBRecenter
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.Finite.Extension
-- (GOLF2 import pruning: dropped LvmJBMutual: unused by this module.)

-- (GOLF2: 12 declarations that `certified` does not use moved verbatim to `LvmNodeSoundTOff`, outside its import closure.)

-- ===== merged from `LvmJBColumnBound` (GOLF module merge: `LvmJBColumnBound.lean` is now a stub importing `LvmJBComplete`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBColumnBound.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# The coordinate polynomials `ĝ_x` and the column bound

For each coordinate `x` of the evaluation domain the branch argument compares the
cleared jet with the received word:

  `ĝ_x = γ̂(dom x - x₀) - ξ^(2k) · (u₀ x + Z · u₁ x)  ∈  A = F[Z][T]`.

By construction `ĝ_x` vanishes at a branch point `(z, t_z)` exactly when the proximate
`p_z` agrees with the word at `x` (`clearedJet_spec_exp`), so `ĝ_x` converts the
agreement pattern into an algebraic incidence between `H` and `ĝ_x`.

Two things are needed about it, and both are here.

* **Size.**  `size_ghat_exp`: the `T`-degree and `Z`-height of `ĝ_x` are `O(r)` — a direct
  consequence of the ledger estimate.  With `mα = 1, mR = 0` for the `T`-degree and
  `mα = 0, mR = D_Z` for the `Z`-height this reads `O(r·D_Y)` and `O(r·D_Z)`, and it is
  what turns the column bound into `O(r·D_Y·D_Z)` rather than something involving `D_X`.

* **Divisibility.**  `dvd_of_resultant_eq_zero`: for an irreducible primitive branch
  factor `H`, a vanishing resultant forces `H ∣ ĝ_x` outright.  This is what upgrades the
  conclusion of the incidence count — "the resultant vanishes at more than `r`
  coordinates" — into the identity `Γ_k(dom x) = u₀ x + Z u₁ x` needed for interpolation.
  Gauss's lemma moves irreducibility to `F(Z)[T]`, `resultant_eq_zero_iff` produces a
  common factor there, and primality of `H` in the UFD `F[Z][T]` brings the divisibility
  back down without any denominator bookkeeping.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Size calculus -/

namespace SizeSystem

variable {A : Type*} [CommRing A] (SS : SizeSystem A)

theorem sub {g h : A} {m : ℕ} (hg : SS.P g m) (hh : SS.P h m) : SS.P (g - h) m := by
  rw [sub_eq_add_neg]
  exact SS.add hg (SS.neg hh)

/-- Evaluating a polynomial of degree at most `r` costs `r` times the size of the
argument. -/
theorem eval_le {γ : A[X]} {r mγ mw : ℕ} (hdeg : γ.natDegree ≤ r)
    (hc : ∀ i, SS.P (γ.coeff i) mγ) {w : A} (hw : SS.P w mw) :
    SS.P (γ.eval w) (mγ + r * mw) := by
  rw [eval_eq_sum_range' (n := r + 1) (by omega)]
  refine SS.sum _ _ fun i hi => ?_
  have hik : i ≤ r := by have := Finset.mem_range.mp hi; omega
  refine SS.mono (SS.mul (hc i) (SS.pow hw i)) ?_
  have : i * mw ≤ r * mw := Nat.mul_le_mul_right _ hik
  omega

end SizeSystem

/-! ### The coordinate polynomials -/

section Ghat

variable {A : Type*} [CommRing A]

/-- The coordinate polynomial with an explicit clearing exponent: the cleared jet
evaluated at the coordinate, minus the correspondingly cleared received value. -/
def ghatExp (γ : A[X]) (ξ : A) (E : ℕ) (w val : A) : A :=
  γ.eval w - ξ ^ E * val

/-- Size bound for a coordinate polynomial with an arbitrary clearing exponent. -/
theorem size_ghat_exp (SS : SizeSystem A) {γ : A[X]} {ξ w val : A}
    {r E mγ mw mξ mval m : ℕ}
    (hdeg : γ.natDegree ≤ r) (hc : ∀ i, SS.P (γ.coeff i) mγ)
    (hw : SS.P w mw) (hξ : SS.P ξ mξ) (hval : SS.P val mval)
    (h1 : mγ + r * mw ≤ m) (h2 : E * mξ + mval ≤ m) :
    SS.P (ghatExp γ ξ E w val) m := by
  refine SS.sub (SS.mono (SS.eval_le hdeg hc hw) h1)
    (SS.mono (SS.mul (SS.pow hξ _) hval) h2)

end Ghat

/-! ### Sizes of the structural constants -/

section Slice

variable {A : Type*} [CommRing A]

/-- The `U = 0` slice of `P`, evaluated at `a₀`, costs one coefficient size plus `d`
substitutions. -/
theorem size_slice_eval (SS : SizeSystem A) (P : A[X][X]) (a₀ : A) {d mR mα : ℕ}
    (hd : P.natDegree ≤ d) (hP : ∀ j, SS.P ((P.coeff j).coeff 0) mR) (ha : SS.P a₀ mα) :
    SS.P ((P.map (evalRingHom 0)).eval a₀) (mR + d * mα) := by
  have hdeg : (P.map (evalRingHom 0)).natDegree < d + 1 :=
    lt_of_le_of_lt (le_trans natDegree_map_le hd) (by omega)
  rw [eval_eq_sum_range' hdeg]
  refine SS.sum _ _ fun j hj => ?_
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  have hcoeff : (P.map (evalRingHom 0)).coeff j = (P.coeff j).coeff 0 := by
    rw [coeff_map]
    simp [coeff_zero_eq_eval_zero]
  rw [hcoeff]
  refine SS.mono (SS.mul (hP j) (SS.pow ha j)) ?_
  have : j * mα ≤ d * mα := Nat.mul_le_mul_right _ hjd
  omega

/-- Sharp size of the simple-root coefficient: the first Hasse derivative lowers the
`Y`-degree by one, so evaluating it costs only `d-1` powers of the initial root. -/
theorem size_xi_refined (SS : SizeSystem A) (R₀ : A[X][X]) (a₀ : A) {d mR mα : ℕ}
    (hd : R₀.natDegree ≤ d) (hR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR)
    (ha : SS.P a₀ mα) :
    SS.P (xi R₀ a₀) (mR + (d - 1) * mα) := by
  refine size_slice_eval SS (hasseDeriv 1 R₀) a₀ ?_ (fun j => ?_) ha
  · exact le_trans (natDegree_hasseDeriv_le R₀ 1) (Nat.sub_le_sub_right hd 1)
  · have hc : (hasseDeriv 1 R₀).coeff j = (j + 1).choose 1 • R₀.coeff (j + 1) := by
      rw [hasseDeriv_coeff, ← nsmul_eq_mul]
    rw [hc, coeff_smul]
    exact SS.nsmul (hR (j + 1) 0) _

end Slice

/-! ### From a vanishing resultant to divisibility -/

section Divisibility

variable {Rz : Type*} [CommRing Rz] [IsDomain Rz] [UniqueFactorizationMonoid Rz]
  [Nonempty (NormalizedGCDMonoid Rz)]

/-- **A vanishing resultant against an irreducible primitive factor forces divisibility.**

This is the exact converse the incidence count needs.  Over the fraction field a zero
resultant means the two polynomials are not coprime (`resultant_eq_zero_iff`); Gauss's
lemma keeps `H` irreducible there, so `H` divides `g` in `Frac(Rz)[T]`; clearing the
denominator of the cofactor and using that `H` is *prime* in the unique factorisation
domain `Rz[T]` — it cannot divide a nonzero constant, by degree — brings the divisibility
back to `Rz[T]`. -/
theorem dvd_of_resultant_eq_zero (H g : Rz[X]) (hprim : H.IsPrimitive)
    (hirr : Irreducible H) (hdeg : 1 ≤ H.natDegree)
    (hres : resultant H g H.natDegree g.natDegree = 0) :
    H ∣ g := by
  set K := FractionRing Rz
  set φ : Rz →+* K := algebraMap Rz K with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective Rz K
  have hdH : (H.map φ).natDegree = H.natDegree := natDegree_map_eq_of_injective hinj H
  have hdg : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj g
  have h0 : resultant (H.map φ) (g.map φ) = 0 := by
    rw [hdH, hdg, resultant_map_map, hres, map_zero]
  have hirrK : Irreducible (H.map φ) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hdvdK : H.map φ ∣ g.map φ := by
    by_cases hdvd : H.map φ ∣ g.map φ
    · exact hdvd
    · exact ((resultant_eq_zero_iff.mp h0).2 (hirrK.coprime_iff_not_dvd.mpr hdvd)).elim
  obtain ⟨q', hq'⟩ := hdvdK
  -- Clear the denominator of the cofactor.
  obtain ⟨b, hb, hbq⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors Rz) (S := K) q'
  set q := IsLocalization.integerNormalization (nonZeroDivisors Rz) (S := K) q' with hq
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hsmul : b • q' = C (φ b) * q' := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have hmul : (H * q).map φ = (C b * g).map φ := by
    rw [Polynomial.map_mul, Polynomial.map_mul, hbq, hsmul, map_C, hq']
    ring
  have hHq : H * q = C b * g := Polynomial.map_injective φ hinj hmul
  -- `H` is prime, and cannot divide a nonzero constant.
  have hprime : Prime H := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hdvdmul : H ∣ C b * g := ⟨q, hHq.symm⟩
  rcases hprime.dvd_or_dvd hdvdmul with hcb | hg
  · exfalso
    have hCb : (C b : Rz[X]) ≠ 0 := by simpa using hbne
    have := Polynomial.natDegree_le_of_dvd hcb hCb
    simp only [natDegree_C] at this
    omega
  · exact hg

end Divisibility

end JBAgreement
end
-- ===== end of `LvmJBColumnBound` =====

-- ===== merged from `LvmJBSharpClearedJet` (GOLF module merge: `LvmJBSharpClearedJet.lean` is now a stub importing `LvmJBComplete`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBSharpClearedJet.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Sharp cleared Newton jets

This file instantiates the derivative-sensitive ledger and clears the `r`-jet with
the common exponent `2*r`.  If `slope` bounds both the derivative-sensitive base and
the simple-root coefficient, every coefficient of the cleared jet has size at most
`2*r*slope`.  This is the local estimate behind the sharp `4*r` skeleton capacity.
-/

namespace JBAgreement

open Polynomial Finset

section

variable {A : Type*} [CommRing A] [IsDomain A]

/-- A cleared jet with the sharp derivative-sensitive size bound. -/
theorem exists_sharpClearedJet {Idx : Type*} [Nonempty Idx]
    (SS : Idx → SizeSystem A) (R₀ : A[X][X]) (a₀ : A) (d r : ℕ)
    (mR mα mξ slope : Idx → ℕ)
    (hd : R₀.natDegree ≤ d)
    (hmR : ∀ o j i, (SS o).P ((R₀.coeff j).coeff i) (mR o))
    (hmα : ∀ o, (SS o).P a₀ (mα o))
    (hmξ : ∀ o, (SS o).P (xi R₀ a₀) (mξ o))
    (hbase : ∀ o, mR o + d * mα o ≤ slope o)
    (hξSlope : ∀ o, mξ o ≤ slope o)
    (hconst : ∀ o, 2 * r * mξ o + mα o ≤ 2 * r * slope o)
    (hξ0 : xi R₀ a₀ ≠ 0) :
    ∃ γ : A[X], γ.natDegree ≤ r ∧
      γ.coeff 0 = xi R₀ a₀ ^ (2 * r) * a₀ ∧
      (∀ o i, (SS o).P (γ.coeff i) (2 * r * slope o)) ∧
      (X : A[X]) ^ (r + 1) ∣
        evalH R₀ d (xi R₀ a₀ ^ (2 * r)) γ
          - C (xi R₀ a₀ ^ ((2 * r) * d) * jetConst R₀ a₀) := by
  classical
  set K := FractionRing A
  set ψ : A →+* K := algebraMap A K with hψ
  have hinj : Function.Injective ψ := IsFractionRing.injective A K
  set ξ₀ : A := xi R₀ a₀ with hξ₀
  set R : K[X][X] := R₀.map (mapRingHom ψ) with hRdef
  set α₀ : K := ψ a₀ with hα₀
  have hξint : ψ ξ₀ = xi R α₀ := (xi_map ψ R₀ a₀).symm
  have hHint : ψ (jetConst R₀ a₀) = jetConst R α₀ :=
    (jetConst_map ψ R₀ a₀).symm
  have hξK : xi R α₀ ≠ 0 := by
    rw [← hξint]
    exact fun h => hξ0 (hinj (by simpa using h))
  have hRd : R.natDegree ≤ d := le_trans natDegree_map_le hd
  set c : A := ξ₀ ^ (2 * r) with hc
  have key : ∀ t : ℕ, ∃ g : A, ψ g = ψ c * (jet R α₀ r).coeff t ∧
      ∀ o, (SS o).P g (2 * r * slope o) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · refine ⟨c * a₀, ?_, fun o => ?_⟩
      · rw [map_mul, jet_coeff_zero]
      · refine (SS o).mono ((SS o).mul ((SS o).pow (hmξ o) _) (hmα o)) ?_
        simpa [hc] using hconst o
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rcases Nat.lt_or_ge t' r with htk | htk
    · have model : ∀ o, ∃ g : A,
          ψ g = xi R α₀ ^ (2 * t' + 1) *
              ((jet R α₀ (t' + 1)).coeff (t' + 1)) ∧
            (SS o).P g (slope o * (2 * t' + 1)) := by
        intro o
        apply jet_coeff_integral_refined (SS o) R R₀ α₀ ξ₀ d (mξ o)
          hRdef hd (hmξ o) hξint hξK
          (fun r => mR o + (d - r) * mα o) (slope o)
        · intro r s
          exact base_integral_refined (SS o) R R₀ α₀ a₀ d (mR o) (mα o)
            hRdef hα₀ hd (hmR o) (hmα o) r s
        · intro r ρ
          have hsub : d - (ρ + r) ≤ d - r := by omega
          exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hsub) _
        · simpa using hbase o
        · exact hξSlope o
      obtain ⟨g₀, hg₀, _⟩ := model (Classical.arbitrary Idx)
      refine ⟨ξ₀ ^ (2 * r - (2 * t' + 1)) * g₀, ?_, fun o => ?_⟩
      · rw [map_mul, map_pow, hg₀, hξint,
          jet_coeff_stable R α₀ (t' + 1) r (by omega)]
        rw [hc, map_pow, hξint, ← mul_assoc, ← pow_add]
        congr 2
        omega
      · obtain ⟨g, hg, hgs⟩ := model o
        have hgg : g = g₀ := hinj (by rw [hg, hg₀])
        rw [hgg] at hgs
        refine (SS o).mono ((SS o).mul ((SS o).pow (hmξ o) _) hgs) ?_
        have hmul : (2 * r - (2 * t' + 1)) * mξ o ≤
            (2 * r - (2 * t' + 1)) * slope o :=
          Nat.mul_le_mul_left _ (hξSlope o)
        calc
          (2 * r - (2 * t' + 1)) * mξ o + slope o * (2 * t' + 1)
              ≤ (2 * r - (2 * t' + 1)) * slope o + slope o * (2 * t' + 1) :=
                Nat.add_le_add_right hmul _
          _ = 2 * r * slope o := by
            have hu : 2 * t' + 1 ≤ 2 * r := by omega
            calc
              (2 * r - (2 * t' + 1)) * slope o + slope o * (2 * t' + 1) =
                  ((2 * r - (2 * t' + 1)) + (2 * t' + 1)) * slope o := by ring
              _ = 2 * r * slope o := by rw [Nat.sub_add_cancel hu]
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
    have h := hGmap 0
    rw [jet_coeff_zero, hα₀] at h
    exact hinj (by rw [h, ← map_mul])
  · intro o i
    rw [hcoeff i]
    split_ifs
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
      have h := congrArg (fun p => Polynomial.coeff p 0) hev
      simp only [coeff_map, coeff_C_mul] at h
      rw [h, coeff_zero_eval_jet, ← hHint, ← map_pow, ← map_mul]
    have hcoeffs : ∀ s, 1 ≤ s → s ≤ r → (evalH R₀ d c γ).coeff s = 0 := by
      intro s hs₁ hsk
      refine hinj ?_
      have h := congrArg (fun p => Polynomial.coeff p s) hev
      simp only [coeff_map, coeff_C_mul] at h
      rw [h, coeff_eval_jet_eq_zero R α₀ hξK r s hs₁ hsk, mul_zero, map_zero]
    rw [X_pow_dvd_iff]
    intro i hi
    rw [coeff_sub, coeff_C]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hcoeff0, if_pos rfl, hc, ← pow_mul, sub_self]
    · rw [hcoeffs i hipos (by omega), if_neg (by omega), sub_zero]

end

end JBAgreement
end
-- ===== end of `LvmJBSharpClearedJet` =====

-- ===== merged from `LvmJBBranch` (GOLF module merge: `LvmJBBranch.lean` is now a stub importing `LvmJBComplete`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBBranch.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# §3: the branch argument

This file assembles the finite-jet argument for a single branch.  The input is a
separable branch `R₀` (recentered at a good slice `x₀`, over `A = F[Z][T]` with the
free initial root `T`), an irreducible fiber factor `H`, and the proximates it
explains; the output is a set of more than `k` *good coordinates* at which every
proximate simultaneously matches the received word.

Two refinements over the naive assembly make the statement general enough to cover the
inseparable case (§6.6) with no separability hypothesis anywhere:

* **The jet order `κ` and the code dimension `k` are decoupled.**  For an inseparable
  factor the machinery runs on the separable core with proximates `q_z = p_z^{p^f}`;
  `κ = k·p^f` is a conservative truncation order, while the incidence count only needs
  `k` good coordinates because final interpolation happens *after* untwisting each
  coordinate value.  Quantitatively this supports the `η³` bound: the column
  bound is `(2κ+1)·deg_Y(S)·D_Z ≈ 2k·deg_Y(P)·D_Z`, with the `p^f` cancelling.

* **The word value is `w₀ + Z^M·w₁`.**  In the separable case `M = 1`; for the
  inseparable case `M = p^f` and `w_i = u_i^{p^f}`, which is how the affine structure
  survives the Frobenius twist.

* **The fiber factor `H` is an input**, not `R₀`'s own fiber: the fiber of an
  irreducible branch need not be irreducible, so the caller selects (by pigeonhole) an
  irreducible factor of it vanishing on the bucket.  The full fiber is still what the
  cleared-jet specialisation kills, and that is derived from `hroot` internally.

The argument: `exists_sharpClearedJet` (the Newton-skeleton estimate) →
`clearedJet_spec_exp` (the
specialised jet is the proximate) → row bound `n - e` and resultant column bound →
`card_exceptional_ge` → `dvd_of_resultant_eq_zero` at each exceptional coordinate.
-/

namespace JBAgreement

open Polynomial Finset

section Assembly

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two size systems on `A = F[Z][T]` used simultaneously: the `Z`-height and the
`T`-degree.  Indexing them by `Bool` lets one application of `exists_sharpClearedJet` deliver
both bounds for the *same* cleared jet. -/
noncomputable def sizePair (F : Type*) [Field F] : Bool → SizeSystem (F[X][X]) :=
  fun b => cond b (degreeSizeSystem (F[X])) (heightSizeSystem F)

/-- The twisted coordinate value `w₀ x + Z^M · w₁ x`, as an element of `A = F[Z][T]`. -/
noncomputable def wordVal (M : ℕ) (a b : F) : F[X][X] :=
  C (Polynomial.C a + Polynomial.X ^ M * Polynomial.C b)

/-- A scalar of `F`, as an element of `A = F[Z][T]`. -/
noncomputable def scal (a : F) : F[X][X] := C (Polynomial.C a)

@[simp] lemma spec_scal (z t a : F) : spec z t (scal a) = a := by
  simp [spec, scal]

@[simp] lemma spec_wordVal (M : ℕ) (z t a b : F) :
    spec z t (wordVal M a b) = a + z ^ M * b := by
  rw [wordVal, spec_apply, eval₂_C]
  simp
  ring

lemma natDegree_scal_le (a : F) : (scal a).natDegree ≤ 0 := le_of_eq (natDegree_C _)

lemma natDegree_wordVal_le (M : ℕ) (a b : F) : (wordVal M a b).natDegree ≤ 0 :=
  le_of_eq (natDegree_C _)

lemma isHeightLE_scal (a : F) : IsHeightLE (scal a) 0 := by
  intro i
  rw [scal, coeff_C]
  split_ifs <;> simp

lemma isHeightLE_wordVal (M : ℕ) (a b : F) : IsHeightLE (wordVal M a b) M := by
  intro i
  rw [wordVal, coeff_C]
  split_ifs with h
  · refine le_trans (natDegree_add_le _ _) (max_le (by simp) ?_)
    refine le_trans (natDegree_mul_le) ?_
    simp
  · simp

lemma isHeightLE_X : IsHeightLE (X : F[X][X]) 0 := by
  intro i
  rw [coeff_X]
  split_ifs <;> simp

lemma natDegree_X_le_one : (X : F[X][X]).natDegree ≤ 1 := natDegree_X_le

/-- Irreducible polynomials of positive degree over `F[Z]` are primitive. -/
theorem isPrimitive_of_irreducible {H : F[X][X]} (hirr : Irreducible H)
    (hdeg : 1 ≤ H.natDegree) : H.IsPrimitive := by
  intro c hc
  obtain ⟨e, he⟩ := hc
  rcases hirr.isUnit_or_isUnit he with hu | hu
  · exact isUnit_C.mp hu
  · exfalso
    have hH0 : H ≠ 0 := hirr.ne_zero
    have hC0 : (C c : F[X][X]) ≠ 0 := fun h => hH0 (by rw [he, h, zero_mul])
    have he0 : e ≠ 0 := fun h => hH0 (by rw [he, h, mul_zero])
    have : H.natDegree = 0 := by
      rw [he, natDegree_mul hC0 he0, natDegree_C, natDegree_eq_zero_of_isUnit hu]
    omega

/-- The incidence/divisibility endgame, abstracted from the construction of the
coordinate polynomials.  Its capacity is the exact resultant rectangle
`gT * hH + dH * gZ`. -/
theorem exists_goodCoords_of_coordinatePolynomials [Fintype F] [DecidableEq F]
    (dom : ι → F) (w₀ w₁ : ι → F) (k e M E : ℕ)
    (x₀ : F) (S : Finset F) (q : F → F[X])
    (hprox : ∀ z ∈ S,
      (disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))).card ≤ e)
    (ξ₀ : F[X][X])
    (hxi : ∀ z ∈ S, spec z ((q z).eval x₀) ξ₀ ≠ 0)
    (H : F[X][X]) (hH0 : ∀ z ∈ S, spec z ((q z).eval x₀) H = 0)
    (hirrH : Irreducible H) (hHdeg : 1 ≤ H.natDegree)
    (dH hH gT gZ B : ℕ) (hHT : H.natDegree ≤ dH) (hHZ : IsHeightLE H hH)
    (g : ι → F[X][X])
    (hspec : ∀ z ∈ S, ∀ x : ι,
      spec z ((q z).eval x₀) (g x) =
        spec z ((q z).eval x₀) ξ₀ ^ E *
          ((q z).eval (dom x) - (w₀ x + z ^ M * w₁ x)))
    (hgT : ∀ x, (g x).natDegree ≤ gT) (hgZ : ∀ x, IsHeightLE (g x) gZ)
    (hcap : gT * hH + dH * gZ ≤ B)
    (hcount : (Fintype.card ι - k) * B <
      (Fintype.card ι - e - k) * S.card) :
    ∃ I : Finset ι, k < I.card ∧ ∀ x ∈ I, ∀ z ∈ S,
      (q z).eval (dom x) = w₀ x + z ^ M * w₁ x := by
  have hprim : H.IsPrimitive := isPrimitive_of_irreducible hirrH hHdeg
  set P : ι → F → Prop := fun x z => ∃ t : F,
    eval₂ (evalRingHom z) t H = 0 ∧ eval₂ (evalRingHom z) t (g x) = 0 with hP
  have hrow : ∀ z ∈ S, Fintype.card ι - e ≤ (univ.filter fun x => P x z).card := by
    intro z hz
    have hsub : univ \ disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))
        ⊆ univ.filter fun x => P x z := by
      intro x hx
      rw [mem_sdiff, mem_disagree] at hx
      have hagree : (q z).eval (dom x) = w₀ x + z ^ M * w₁ x := by
        have h := not_not.mp hx.2
        simpa [RSeval] using h.symm
      refine mem_filter.mpr ⟨mem_univ _, ⟨(q z).eval x₀, ?_, ?_⟩⟩
      · simpa [spec] using hH0 z hz
      · have h := hspec z hz x
        rw [hagree, sub_self, mul_zero] at h
        simpa [spec] using h
    have hcard : (univ \ disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))).card
        = Fintype.card ι
          - (disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))).card := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ]
    have hle := card_le_card hsub
    have hpx := hprox z hz
    omega
  set I : Finset ι := univ.filter fun x =>
    resultant H (g x) H.natDegree (g x).natDegree = 0 with hI
  have hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B := by
    intro x hx
    have hres : resultant H (g x) H.natDegree (g x).natDegree ≠ 0 := by
      simpa [hI] using hx
    have hbad := card_badSpecializations_le_of_height H (g x) (le_refl _) (le_refl _)
      hHZ (hgZ x) (Or.inl (by omega)) hres
    have hsub : (S.filter fun z => P x z) ⊆ badSpecializations H (g x) := by
      intro z hz
      rw [mem_filter] at hz
      simpa [badSpecializations] using hz.2
    have h1 : (g x).natDegree * hH ≤ gT * hH := Nat.mul_le_mul_right _ (hgT x)
    have h2 : H.natDegree * gZ ≤ dH * gZ := Nat.mul_le_mul_right _ hHT
    exact le_trans (le_trans (card_le_card hsub) hbad)
      (le_trans (Nat.add_le_add h1 h2) hcap)
  have hka : k ≤ Fintype.card ι - e := by
    apply Nat.le_of_not_lt
    intro hcon
    have h0 : Fintype.card ι - e - k = 0 := by omega
    rw [h0, zero_mul] at hcount
    exact absurd hcount (Nat.not_lt_zero _)
  have hIcard : k < I.card :=
    card_exceptional_ge_rect S I P (Fintype.card ι - e) k B
      hka (Nat.sub_le _ _) hrow hcol hcount
  refine ⟨I, hIcard, ?_⟩
  intro x hx z hz
  have hres : resultant H (g x) H.natDegree (g x).natDegree = 0 := by
    simpa [hI] using hx
  obtain ⟨c, hc⟩ := dvd_of_resultant_eq_zero H (g x) hprim hirrH hHdeg hres
  have hzero : spec z ((q z).eval x₀) (g x) = 0 := by
    rw [hc, map_mul, hH0 z hz, zero_mul]
  have h := hspec z hz x
  rw [hzero] at h
  have hne : spec z ((q z).eval x₀) ξ₀ ^ E ≠ 0 := pow_ne_zero _ (hxi z hz)
  have hsub0 := (mul_eq_zero.mp h.symm).resolve_left hne
  exact sub_eq_zero.mp hsub0

/-- **Sharp branch argument.**  The derivative-sensitive Newton ledger permits the
common clearing exponent `2κ`.  Consequently the coordinate polynomial has bidegree
at most `(2κ dY, 2κ dZ + M)`, and the exact resultant rectangle is
`sharpFiberCapacity κ dY dZ M dH hH`. -/
theorem exists_goodCoords_sharp [Fintype F] [DecidableEq F]
    (dom : ι → F) (w₀ w₁ : ι → F) (k κ e M : ℕ) (hκ : 1 ≤ κ)
    (x₀ : F) (R₀ : (F[X][X])[X][X]) (dY dZ : ℕ)
    (hdY : R₀.natDegree ≤ dY) (hdYpos : 1 ≤ dY)
    (hRT : ∀ j i, ((R₀.coeff j).coeff i).natDegree ≤ 0)
    (hRZ : ∀ j i, IsHeightLE ((R₀.coeff j).coeff i) dZ)
    (S : Finset F) (q : F → F[X])
    (hqdeg : ∀ z ∈ S, (q z).natDegree ≤ κ)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))).card ≤ e)
    (hroot : ∀ z ∈ S,
      (R₀.map (mapRingHom (spec z ((q z).eval x₀)))).eval ((q z).comp (X + C x₀)) = 0)
    (hxi : ∀ z ∈ S, spec z ((q z).eval x₀) (xi R₀ (X : F[X][X])) ≠ 0)
    (H : F[X][X]) (hH0 : ∀ z ∈ S, spec z ((q z).eval x₀) H = 0)
    (hirrH : Irreducible H) (hHdeg : 1 ≤ H.natDegree)
    (dH hH : ℕ) (hHT : H.natDegree ≤ dH) (hHZ : IsHeightLE H hH)
    (hcount : (Fintype.card ι - k) *
        sharpFiberCapacity κ dY dZ M dH hH
      < (Fintype.card ι - e - k) * S.card) :
    ∃ I : Finset ι, k < I.card ∧ ∀ x ∈ I, ∀ z ∈ S,
      (q z).eval (dom x) = w₀ x + z ^ M * w₁ x := by
  set a₀ : F[X][X] := X with ha₀
  set ξ₀ : F[X][X] := xi R₀ a₀ with hξ₀
  have hSpos : 0 < S.card := by
    apply Nat.pos_of_ne_zero
    intro h
    simp [h] at hcount
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp hSpos
  have hξ0 : ξ₀ ≠ 0 := by
    intro h
    refine hxi z₀ hz₀ ?_
    show spec z₀ ((q z₀).eval x₀) ξ₀ = 0
    rw [h, map_zero]
  have hξT : ξ₀.natDegree ≤ dY - 1 := by
    have h1 : ξ₀.natDegree ≤ 0 + (dY - 1) * 1 :=
      size_xi_refined (degreeSizeSystem (F[X])) R₀ a₀ hdY hRT natDegree_X_le_one
    omega
  have hξZ : IsHeightLE ξ₀ dZ := by
    have h1 : IsHeightLE ξ₀ (dZ + (dY - 1) * 0) :=
      size_xi_refined (heightSizeSystem F) R₀ a₀ hdY hRZ isHeightLE_X
    exact fun j => (h1 j).trans (by omega)
  have hHzero : ∀ z ∈ S, spec z ((q z).eval x₀) (jetConst R₀ a₀) = 0 := by
    intro z hz
    have hc0 : spec z ((q z).eval x₀) a₀ = ((q z).comp (X + C x₀)).coeff 0 := by
      rw [coeff_zero_eq_eval_zero, eval_comp]
      simp [ha₀]
    have h2 : jetConst (R₀.map (mapRingHom (spec z ((q z).eval x₀))))
        (spec z ((q z).eval x₀) a₀) = 0 := by
      unfold jetConst
      rw [hc0, ← coeff_zero_eval, hroot z hz, coeff_zero]
    rw [← jetConst_map (spec z ((q z).eval x₀)) R₀ a₀]
    exact h2
  obtain ⟨γ, hγdeg, hγ0, hγsize, hγjet⟩ :=
    exists_sharpClearedJet (Idx := Bool) (sizePair F) R₀ a₀ dY κ
      (fun b => cond b 0 dZ) (fun b => cond b 1 0)
      (fun b => cond b (dY - 1) dZ) (fun b => cond b dY dZ) hdY
      (fun b => by cases b <;> [exact hRZ; exact hRT])
      (fun b => by cases b <;> [exact isHeightLE_X; exact natDegree_X_le_one])
      (fun b => by cases b <;> [exact hξZ; exact hξT])
      (fun b => by cases b <;> simp)
      (fun b => by cases b <;> simp)
      (fun b => by
        cases b
        · simp
        · simp only [cond_true]
          calc
            2 * κ * (dY - 1) + 1 ≤ 2 * κ * (dY - 1) + 2 * κ := by omega
            _ = 2 * κ * ((dY - 1) + 1) := by ring
            _ = 2 * κ * dY := by rw [Nat.sub_add_cancel hdYpos])
      hξ0
  have hγZ : ∀ i, IsHeightLE (γ.coeff i) (2 * κ * dZ) := by
    intro i
    have h := hγsize false i
    change IsHeightLE (γ.coeff i) (2 * κ * dZ) at h
    exact h
  have hγT : ∀ i, (γ.coeff i).natDegree ≤ 2 * κ * dY := by
    intro i
    have h := hγsize true i
    change (γ.coeff i).natDegree ≤ 2 * κ * dY at h
    exact h
  set g : ι → F[X][X] := fun x =>
    ghatExp γ ξ₀ (2 * κ) (scal (dom x - x₀)) (wordVal M (w₀ x) (w₁ x)) with hg
  have hgT : ∀ x, (g x).natDegree ≤ 2 * κ * dY := by
    intro x
    refine size_ghat_exp (degreeSizeSystem (F[X])) hγdeg hγT
      (natDegree_scal_le _) hξT (natDegree_wordVal_le _ _ _) ?_ ?_
    · simp
    · have hm : (2 * κ) * (dY - 1) ≤ (2 * κ) * dY :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      simpa using hm
  have hgZ : ∀ x, IsHeightLE (g x) (2 * κ * dZ + M) := by
    intro x
    refine size_ghat_exp (heightSizeSystem F) hγdeg hγZ
      (isHeightLE_scal _) hξZ (isHeightLE_wordVal _ _ _) ?_ ?_
    · simp
    · exact le_rfl
  have hspec : ∀ z ∈ S, ∀ x : ι,
      spec z ((q z).eval x₀) (g x)
        = spec z ((q z).eval x₀) ξ₀ ^ (2 * κ) *
            ((q z).eval (dom x) - (w₀ x + z ^ M * w₁ x)) := by
    intro z hz x
    set φ := spec z ((q z).eval x₀) with hφ
    set π : F[X] := (q z).comp (X + C x₀) with hπ
    have hroot' : (R₀.map (mapRingHom φ)).eval π = 0 := by
      rw [hφ, hπ]
      exact hroot z hz
    have hπ0 : π.coeff 0 = φ a₀ := by
      rw [hπ, coeff_zero_eq_eval_zero, eval_comp]
      simp [ha₀, hφ]
    have hqdeg' : ((X : F[X]) + C x₀).natDegree ≤ 1 :=
      le_trans (natDegree_add_le _ _) (by simp)
    have hπdeg : π.natDegree ≤ κ := by
      rw [hπ]
      refine le_trans natDegree_comp_le ?_
      calc
        (q z).natDegree * ((X : F[X]) + C x₀).natDegree
            ≤ κ * 1 := Nat.mul_le_mul (hqdeg z hz) hqdeg'
        _ = κ := by ring
    have hφH : φ (jetConst R₀ a₀) = 0 := by rw [hφ]; exact hHzero z hz
    have hφξ : φ ξ₀ ≠ 0 := hxi z hz
    have hkey := clearedJet_spec_exp R₀ a₀ dY κ (2 * κ) hdY γ hγdeg hγ0 hγjet
      φ hφH hφξ π hπdeg hπ0 hroot'
    have heval : φ (γ.eval (scal (dom x - x₀))) =
        φ ξ₀ ^ (2 * κ) * (q z).eval (dom x) := by
      have h2 : φ (γ.eval (scal (dom x - x₀)))
          = (γ.map φ).eval (φ (scal (dom x - x₀))) :=
        ((eval_map φ (φ (scal (dom x - x₀)))).trans
          (eval₂_hom φ (scal (dom x - x₀)))).symm
      rw [h2, ← hkey, hφ, spec_scal, ← hφ, eval_mul, eval_C, hπ, eval_comp]
      simp [← hξ₀]
    have hgx : g x = γ.eval (scal (dom x - x₀))
        - ξ₀ ^ (2 * κ) * wordVal M (w₀ x) (w₁ x) := by rfl
    rw [hgx, map_sub, heval, map_mul, map_pow, hφ, spec_wordVal]
    ring
  refine exists_goodCoords_of_coordinatePolynomials dom w₀ w₁ k e M (2 * κ)
    x₀ S q hprox ξ₀ hxi H hH0 hirrH hHdeg dH hH
    (2 * κ * dY) (2 * κ * dZ + M)
    (sharpFiberCapacity κ dY dZ M dH hH) hHT hHZ g hspec hgT hgZ ?_ hcount
  simp [sharpFiberCapacity]

end Assembly

end JBAgreement
end
-- ===== end of `LvmJBBranch` =====

-- ===== merged from `LvmJBSwap` (GOLF module merge: `LvmJBSwap.lean` is now a stub importing `LvmJBComplete`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBSwap.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Variable swaps, and degree bounds for factors

The branch-selection argument (§6.2) factors the Guruswami–Sudan interpolant
`Q ∈ F[Z][X][Y]` and runs the jet machinery on one prime factor.  All the size data of
the factor — its `Y`-degree, its `X`-degree, its `Z`-height — must be inherited from
`Q`.  For the `Y`-degree this is `natDegree_le_of_dvd`; for the other two variables it
is the same statement *after moving the variable to the outside*, which is what the
swap homomorphism of this file does.

`swap : R[X][Y] →+* R[Y][X]` exchanges the two polynomial layers.  It is a ring
homomorphism and an involution, hence injective; therefore divisibility transports
along it, and the inner degree of a factor is bounded by the inner degree of the
multiple.  Composing a `map` of the inner swap with an outer swap bubbles the innermost
variable of a triple tower to the outside (`zOut`).

The degree characterisations `isHeightLE_iff_natDegree_swap_le` and
`natDegree_swap_le_iff` translate between coefficientwise bounds (the form used by the
jet machinery) and outer `natDegree` bounds (the form `natDegree_le_of_dvd` provides).
-/

namespace JBAgreement

open Polynomial

variable {R : Type*} [CommSemiring R]

/-! ### The swap homomorphism -/

/-- Exchange the two variables of `R[X][Y]`. -/
noncomputable def swap (R : Type*) [CommSemiring R] : R[X][X] →+* R[X][X] :=
  eval₂RingHom (eval₂RingHom (C.comp C) X) (C X)

theorem swap_monomial_monomial (n m : ℕ) (a : R) :
    swap R (monomial n (monomial m a)) = monomial m (monomial n a) := by
  unfold swap
  rw [coe_eval₂RingHom, eval₂_monomial, coe_eval₂RingHom, eval₂_monomial]
  rw [RingHom.comp_apply]
  rw [← C_pow]
  calc (C (C a) * X ^ m) * C (X ^ n) = C (C a * X ^ n) * X ^ m := by
        rw [C_mul]; ring
    _ = monomial m (C a * X ^ n) := by rw [C_mul_X_pow_eq_monomial]
    _ = monomial m (monomial n a) := by rw [C_mul_X_pow_eq_monomial]

/-- The coefficient formula: `swap` transposes the coefficient matrix. -/
theorem coeff_coeff_swap (p : R[X][X]) (i j : ℕ) :
    ((swap R p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n q =>
      induction q using Polynomial.induction_on' with
      | add f g hf hg =>
          have : (monomial n (f + g) : R[X][X]) = monomial n f + monomial n g := by
            rw [map_add]
          rw [this, map_add]
          simp only [coeff_add]
          rw [hf, hg]
      | monomial m a =>
          rw [swap_monomial_monomial]
          simp only [coeff_monomial]
          split_ifs with h1 h2 h2 <;>
            simp_all [coeff_monomial, eq_comm]

/-- `swap` is an involution. -/
theorem swap_swap (p : R[X][X]) : swap R (swap R p) = p := by
  apply Polynomial.ext; intro i
  apply Polynomial.ext; intro j
  rw [coeff_coeff_swap, coeff_coeff_swap]

theorem swap_injective : Function.Injective (swap R) := by
  intro p q h
  rw [← swap_swap (R := R) p, h, swap_swap]

@[simp] theorem swap_eq_zero_iff {p : R[X][X]} : swap R p = 0 ↔ p = 0 := by
  constructor
  · intro h
    exact swap_injective (R := R) (a₂ := 0) (by simpa using h)
  · rintro rfl; exact map_zero _

/-! ### Degree characterisations -/

/-- Coefficientwise inner-degree bounds are outer-degree bounds after swapping. -/
theorem natDegree_swap_le_iff {p : R[X][X]} {m : ℕ} :
    (swap R p).natDegree ≤ m ↔ ∀ j, (p.coeff j).natDegree ≤ m := by
  constructor
  · intro h j
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i him
    have : (swap R p).coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h him)
    have h2 := coeff_coeff_swap p i j
    rw [this] at h2
    simpa using h2.symm
  · intro h
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i him
    apply Polynomial.ext; intro j
    rw [coeff_coeff_swap]
    simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h j) him)]

/-- The height predicate of `Height.lean` is the swapped outer degree. -/
theorem isHeightLE_iff_natDegree_swap_le {p : R[X][X]} {m : ℕ} :
    IsHeightLE p m ↔ (swap R p).natDegree ≤ m :=
  ⟨fun h => natDegree_swap_le_iff.mpr h, fun h => natDegree_swap_le_iff.mp h⟩

/-! ### Degree bounds for factors, two variables -/

section TwoVar

variable {F : Type*} [Field F]

/-- The `Z`-height of a factor is at most the `Z`-height of the multiple.  Stated for
`F[Z][T]`; `IsHeightLE` is the coefficientwise `Z`-degree bound. -/
theorem isHeightLE_of_dvd {p q : F[X][X]} {m : ℕ} (hdvd : p ∣ q) (hq : q ≠ 0)
    (hht : IsHeightLE q m) : IsHeightLE p m := by
  rw [isHeightLE_iff_natDegree_swap_le] at hht ⊢
  refine le_trans (natDegree_le_of_dvd ?_ ?_) hht
  · exact map_dvd (swap F) hdvd
  · simpa using hq

end TwoVar

/-! ### Degree bounds for factors, three variables

For `P ∣ Q` in `F[Z][X][Y]`, three bounds are inherited: the `Y`-degree (outer, no swap
needed), the `X`-degree (one outer swap), and the `Z`-height (bubble `Z` to the outside:
an inner swap under `map`, then an outer swap). -/

section ThreeVar

variable {F : Type*} [Field F]

/-- Move the innermost variable of `F[Z][X][Y]` to the outside. -/
noncomputable def zOut (F : Type*) [Field F] : F[X][X][X] →+* F[X][X][X] :=
  (swap (F[X])).comp (mapRingHom (swap F))

theorem zOut_injective : Function.Injective (zOut F) := by
  unfold zOut
  rw [RingHom.coe_comp]
  exact Function.Injective.comp (swap_injective (R := F[X]))
    (map_injective _ (swap_injective (R := F)))

theorem coeff_coeff_coeff_zOut (P : F[X][X][X]) (d j i : ℕ) :
    (((zOut F P).coeff d).coeff j).coeff i = (((P.coeff j).coeff i)).coeff d := by
  unfold zOut
  rw [RingHom.comp_apply]
  rw [coeff_coeff_swap]
  rw [coe_mapRingHom, coeff_map]
  rw [coeff_coeff_swap]

/-- The three-variable height characterisation: coefficientwise `Z`-degree bounds are
outer degree bounds after `zOut`. -/
theorem natDegree_zOut_le_iff {P : F[X][X][X]} {m : ℕ} :
    (zOut F P).natDegree ≤ m ↔ ∀ j i, ((P.coeff j).coeff i).natDegree ≤ m := by
  constructor
  · intro h j i
    rw [natDegree_le_iff_coeff_eq_zero]
    intro d hdm
    have h1 : (zOut F P).coeff d = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hdm)
    have h2 := coeff_coeff_coeff_zOut P d j i
    rw [h1] at h2
    simpa using h2.symm
  · intro h
    rw [natDegree_le_iff_coeff_eq_zero]
    intro d hdm
    apply Polynomial.ext; intro j
    apply Polynomial.ext; intro i
    rw [coeff_coeff_coeff_zOut]
    simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h j i) hdm)]

/-- **`Z`-heights pass to factors** in `F[Z][X][Y]`. -/
theorem heightZ_of_dvd {P Q : F[X][X][X]} {m : ℕ} (hdvd : P ∣ Q) (hQ : Q ≠ 0)
    (h : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ m) :
    ∀ j i, ((P.coeff j).coeff i).natDegree ≤ m := by
  rw [← natDegree_zOut_le_iff] at h ⊢
  refine le_trans (natDegree_le_of_dvd (map_dvd (zOut F) hdvd) ?_) h
  intro h0
  exact hQ (zOut_injective (by simpa using h0))

/-- **`X`-degrees pass to factors** in `F[Z][X][Y]`. -/
theorem degX_of_dvd {P Q : F[X][X][X]} {m : ℕ} (hdvd : P ∣ Q) (hQ : Q ≠ 0)
    (h : ∀ j, (Q.coeff j).natDegree ≤ m) :
    ∀ j, (P.coeff j).natDegree ≤ m := by
  rw [← natDegree_swap_le_iff] at h ⊢
  refine le_trans (natDegree_le_of_dvd (map_dvd (swap (F[X])) hdvd) ?_) h
  simpa using hQ

end ThreeVar

end JBAgreement
end
-- ===== end of `LvmJBSwap` =====

-- ===== merged from `LvmJBFrobenius` (GOLF module merge: `LvmJBFrobenius.lean` is now a stub importing `LvmJBComplete`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBFrobenius.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# §6.6: the inseparable case, by separable extraction and pointwise untwisting

In positive characteristic an irreducible factor `P` of the interpolant can be
inseparable in `Y`: `∂_Y P = 0`, which kills the simple-root value `ξ` and with it the
whole jet recursion.  The classical remedy extracts the separable core,

  `P = S(X, Y^{p^f}, Z)`,   `∂_Y S ≠ 0`,   `S` irreducible,

and this file provides that extraction (`exists_expand_eq`) together with the two facts
that make the extracted data usable downstream:

* **root transfer** — a `Y`-root `π` of a specialisation of `P` becomes the root
  `π^{p^f}` of the same specialisation of `S` (`expand`/`eval` commutation); and

* **pointwise untwisting** — over the *finite* field `F` the map `c ↦ c^{p^f}` is
  injective, so any identity between `p^f`-th powers of field elements descends.

The second point is what keeps the quantitative side intact.  Running the machinery on
`S` uses the conservative jet order `κ = k·p^f` (the proximates become
`q_z = p_z^{p^f}`), but the final interpolation happens *after* untwisting each
coordinate value, so it still uses exactly `k` coordinates; and the column bound is

  `(2κ+1)·deg_Y S·D_Z = (2k·p^f+1)·(deg_Y P/p^f)·D_Z ≈ 2k·deg_Y P·D_Z` —

the factor `p^f` cancels.  The `η³` exponent is therefore unaffected by inseparability;
no separability hypothesis survives into the final theorem.
-/

namespace JBAgreement

open Polynomial

/-! ### Separable extraction -/

section Extract

variable {R : Type*} [CommRing R] [IsDomain R]

/-- `expand` preserves and reflects invertibility. -/
theorem isUnit_expand_iff {n : ℕ} (hn : 0 < n) {f : R[X]} :
    IsUnit (expand R n f) ↔ IsUnit f := by
  constructor
  · intro h
    have hdeg : (expand R n f).natDegree = 0 := natDegree_eq_zero_of_isUnit h
    rw [natDegree_expand] at hdeg
    have hf0 : f.natDegree = 0 := by
      rcases Nat.mul_eq_zero.mp hdeg with h' | h'
      · exact h'
      · omega
    have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hf0
    have : expand R n f = f := by rw [hfC, expand_C]
    rwa [this] at h
  · intro h
    have hdeg : f.natDegree = 0 := natDegree_eq_zero_of_isUnit h
    have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
    rw [hfC, expand_C]
    rwa [hfC] at h

/-- Irreducibility descends along `expand`. -/
theorem irreducible_of_irreducible_expand {n : ℕ} (hn : 0 < n) {f : R[X]}
    (h : Irreducible (expand R n f)) : Irreducible f := by
  constructor
  · exact fun hu => h.not_isUnit ((isUnit_expand_iff hn).mpr hu)
  · intro a b hab
    have hexp : expand R n f = expand R n a * expand R n b := by
      rw [hab, map_mul]
    rcases h.isUnit_or_isUnit hexp with hu | hu
    · exact Or.inl ((isUnit_expand_iff hn).mp hu)
    · exact Or.inr ((isUnit_expand_iff hn).mp hu)

variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- **Separable extraction.**  An irreducible polynomial of positive degree over a
domain of characteristic `p` is `expand (p^f)` of an irreducible *separable* polynomial
(nonzero derivative), of positive degree, with the degrees related by `p^f`. -/
theorem exists_expand_eq :
    ∀ (n : ℕ) (P : R[X]), P.natDegree ≤ n → Irreducible P → 1 ≤ P.natDegree →
    ∃ (f : ℕ) (S : R[X]), P = expand R (p ^ f) S ∧ S.derivative ≠ 0 ∧
      Irreducible S ∧ 1 ≤ S.natDegree ∧ S.natDegree * p ^ f = P.natDegree := by
  intro n
  induction n with
  | zero => intro P hPn _ hPdeg; omega
  | succ n ih =>
      intro P hPn hPirr hPdeg
      rcases eq_or_ne P.derivative 0 with hder | hder
      · -- Inseparable: contract one factor of `p` and recurse.
        set S₀ := contract p P with hS₀
        have hPS₀ : expand R p S₀ = P := expand_contract p hder hp.out.ne_zero
        have hdegS₀ : S₀.natDegree * p = P.natDegree := by
          rw [← hPS₀, natDegree_expand]
        have hS₀deg : 1 ≤ S₀.natDegree := by
          rw [← hdegS₀] at hPdeg
          exact Nat.pos_of_mul_pos_right hPdeg
        have hp2 : 2 ≤ p := hp.out.two_le
        have hS₀lt : S₀.natDegree ≤ n := by nlinarith
        have hS₀irr : Irreducible S₀ :=
          irreducible_of_irreducible_expand hp.out.pos (hPS₀ ▸ hPirr)
        obtain ⟨f, S, hSeq, hSder, hSirr, hSdeg, hSdegeq⟩ :=
          ih S₀ hS₀lt hS₀irr hS₀deg
        refine ⟨f + 1, S, ?_, hSder, hSirr, hSdeg, ?_⟩
        · rw [← hPS₀, hSeq, expand_expand]
          congr 1
          simp [pow_succ, mul_comm]
        · rw [pow_succ, ← mul_assoc, hSdegeq, hdegS₀]
      · -- Already separable.
        exact ⟨0, P, by rw [pow_zero, expand_one], hder, hPirr, hPdeg, by
          rw [pow_zero, mul_one]⟩

end Extract

/-! ### Root transfer -/

section Roots

variable {A B : Type*} [CommRing A] [CommRing B]

/-- A root of a mapped `expand` is a power-root of the mapped base: if
`P = expand N S` and `π` annihilates `P` under the coefficient map `φ`, then `π^N`
annihilates `S` under `φ`. -/
theorem eval_map_expand_eq (φ : A →+* B) (S : A[X]) (N : ℕ) (π : B) :
    ((expand A N S).map φ).eval π = (S.map φ).eval (π ^ N) := by
  rw [map_expand, expand_eval]

end Roots

/-! ### Pointwise untwisting over a field of characteristic `p` -/

section Untwist

variable {F : Type*} [Field F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]

/-- Frobenius powers are injective on a field. -/
theorem pow_char_pow_injective (f : ℕ) :
    Function.Injective (fun c : F => c ^ p ^ f) := by
  intro x y h
  have hsub : (x - y) ^ p ^ f = 0 := by
    rw [sub_pow_char_pow x y f]
    simpa using sub_eq_zero.mpr h
  have := pow_eq_zero_iff (pow_ne_zero f hp.out.ne_zero) |>.mp hsub
  exact sub_eq_zero.mp this

/-- The twisted affine value: `(a + z·b)^{p^f} = a^{p^f} + z^{p^f}·b^{p^f}`. -/
theorem add_mul_pow_char_pow (f : ℕ) (a b z : F) :
    (a + z * b) ^ p ^ f = a ^ p ^ f + z ^ p ^ f * b ^ p ^ f := by
  rw [add_pow_char_pow (a) (z * b) p f, mul_pow]

end Untwist

end JBAgreement
end
-- ===== end of `LvmJBFrobenius` =====

-- ===== merged from `LvmJBSelect` (GOLF module merge: `LvmJBSelect.lean` is now a stub importing `LvmJBComplete`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBSelect.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# §6.2: branch selection from the Guruswami–Sudan interpolant

The only assumption of the end-to-end theorem is Guruswami–Sudan: a nonzero
`Q ∈ F[Z][X][Y]` of controlled degrees with `Q(X, p_z(X), z) = 0` for every parameter
`z ∈ S`.  This file derives, from that data alone, the entire branch package the jet
machinery consumes:

1. **Prime selection.**  Factor `Q` into primes.  For every `z` at which the
   specialisation `Q_z` is nonzero (all but `≤ D_Z` many), the linear factor
   `Y - p_z(X)` is prime, so it divides some prime factor of positive `Y`-degree.

2. **Separable extraction** (§6.6).  Each relevant prime `P` is `expand (p^f)` of an
   irreducible *separable* `S_P`; the proximate of `S_P` at `z` is `p_z^{p^f}`.  No
   separability assumption remains.

3. **The good slice.**  For each `S_P` the resultant `r_P = Res_Y(S_P, ∂_Y S_P)` is a
   *nonzero* polynomial in `(Z, X)` (Gauss's lemma moves irreducibility to the fraction
   field of `F[Z][X]`, where separability gives coprimality).  A slice `x₀` avoiding
   the `≤ 2·D_Y·D_X` roots in `X` of all the `r_P` exists whenever
   `2·D_Y·D_X < |F|`; at such a slice, `ξ(z, t_z) ≠ 0` fails for at most
   `ht(r_P) ≤ 2·D_Y·D_Z` many `z` per branch (`ringHom_resultant_eq_zero_of_common_root`).

4. **Fiber factoring and weighted selection.**  The fiber `S_P(x₀, T, Z)` is nonzero and
   factors into primes of `F[Z][T]`; each surviving `z` kills a positive-degree prime
   factor of its branch's fiber (the degree-zero factors account for `≤ D_Y·D_Z` bad
   `z`).  There are at most `D_Y` labels `(P, H)` altogether, so some label carries a
   enough surviving parameters for its exact sharp capacity — the bucket handed to
   `exists_goodCoords_sharp`.

The output collects every hypothesis of the branch argument, together with the twist
data `N = p^f` used by the Frobenius untwisting in the endgame.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Generic helpers -/

theorem multiset_sum_le_of_le {s t : Multiset ℕ} (h : s ≤ t) : s.sum ≤ t.sum := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp

/-- Sum over the deduplicated support is at most the multiset sum. -/
theorem toFinset_sum_le_multiset_sum {α : Type*} [DecidableEq α] (s : Multiset α)
    (f : α → ℕ) : ∑ a ∈ s.toFinset, f a ≤ (s.map f).sum := by
  have h1 : ∑ a ∈ s.toFinset, f a = (s.dedup.map f).sum := by
    rw [Finset.sum_eq_multiset_sum]
    rfl
  rw [h1]
  exact multiset_sum_le_of_le (Multiset.map_le_map s.dedup_le)

/-- Irreducible polynomials of positive degree over a domain are primitive. -/
theorem isPrimitive_of_irreducible' {R : Type*} [CommRing R] [IsDomain R] {H : R[X]}
    (hirr : Irreducible H) (hdeg : 1 ≤ H.natDegree) : H.IsPrimitive := by
  intro c hc
  obtain ⟨e, he⟩ := hc
  rcases hirr.isUnit_or_isUnit he with hu | hu
  · exact isUnit_C.mp hu
  · exfalso
    have hH0 : H ≠ 0 := hirr.ne_zero
    have hC0 : (C c : R[X]) ≠ 0 := fun h => hH0 (by rw [he, h, zero_mul])
    have he0 : e ≠ 0 := fun h => hH0 (by rw [he, h, mul_zero])
    have : H.natDegree = 0 := by
      rw [he, natDegree_mul hC0 he0, natDegree_C, natDegree_eq_zero_of_isUnit hu]
    omega

/-- The `Z`-height version of the Sylvester bound: if all coefficients of `H` and `g`
(as polynomials over `F[Z][X]`) have `Z`-height at most `a` and `b` respectively, then
the resultant has `Z`-height at most `n·a + m·b`. -/
theorem isHeightLE_resultant {F : Type*} [CommRing F] (H g : (F[X][X])[X]) {a b : ℕ}
    (m n : ℕ) (hH : ∀ i, IsHeightLE (H.coeff i) a) (hg : ∀ i, IsHeightLE (g.coeff i) b) :
    IsHeightLE (resultant H g m n) (n * a + m * b) := by
  rw [resultant, Matrix.det_apply]
  refine IsHeightLE.sum _ _ fun σ _ => ?_
  have hsmul : ∀ (u : ℤˣ) (x : F[X][X]) (c : ℕ), IsHeightLE x c →
      IsHeightLE (u • x) c := by
    intro u x c hx
    rcases Int.units_eq_one_or u with rfl | rfl
    · simpa using hx
    · have h1 : ((-1 : ℤˣ) • x) = -x := by
        rw [Units.smul_def]
        simp
      rw [h1]
      exact hx.neg
  refine hsmul _ _ _ ?_
  have hprod : IsHeightLE (∏ i, sylvester H g m n (σ i) i) (∑ i : Fin (m + n),
      (if (i : ℕ) < m then b else a)) := by
    classical
    induction (Finset.univ : Finset (Fin (m + n))) using Finset.induction with
    | empty =>
        simp only [Finset.prod_empty, Finset.sum_empty]
        intro i
        rw [coeff_one]
        split_ifs <;> simp
    | insert x s hx ih =>
        rw [Finset.prod_insert hx, Finset.sum_insert hx]
        refine IsHeightLE.mul ?_ ih
        rcases lt_or_ge (x : ℕ) m with hxm | hxm
        · rw [if_pos hxm]
          -- a `g`-column
          have : ∃ i : Fin m, Fin.castAdd n i = x := ⟨⟨x, hxm⟩, by simp [Fin.castAdd]⟩
          obtain ⟨i, rfl⟩ := this
          simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
          split_ifs with h
          · exact hg _
          · simp
        · rw [if_neg (not_lt.mpr hxm)]
          have : ∃ i : Fin n, Fin.natAdd m i = x :=
            ⟨⟨(x : ℕ) - m, by (clear * - hxm; omega)⟩, by
              apply Fin.ext
              simp [Fin.natAdd]
              (clear * - hxm; omega)⟩
          obtain ⟨i, rfl⟩ := this
          simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
          split_ifs with h
          · exact hH _
          · simp
  refine hprod.mono ?_
  have hsum : (∑ i : Fin (m + n), (if (i : ℕ) < m then b else a)) = m * b + n * a := by
    rw [Fin.sum_univ_add]
    have h1 : ∀ i : Fin m, (if ((Fin.castAdd n i : Fin (m + n)) : ℕ) < m then b else a) = b := by
      intro i
      rw [if_pos]
      simp
    have h2 : ∀ i : Fin n, (if ((Fin.natAdd m i : Fin (m + n)) : ℕ) < m then b else a) = a := by
      intro i
      rw [if_neg]
      simp [Fin.natAdd]
    simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  (clear * - hsum; omega)

/-- Roots in `F` of a nonzero `F[Z]`-polynomial, as a Finset, number at most its
degree. -/
theorem card_le_natDegree_of_eval_eq_zero {F : Type*} [Field F] [DecidableEq F]
    {c : F[X]} (hc : c ≠ 0) (s : Finset F) (h : ∀ x ∈ s, c.eval x = 0) :
    s.card ≤ c.natDegree := by
  refine le_trans (Finset.card_le_card ?_) (le_trans c.roots.toFinset_card_le
    (card_roots' c))
  intro x hx
  simpa [Multiset.mem_toFinset, mem_roots, hc] using h x hx



/-! ### The selection theorem -/

section Selection

variable {F : Type*} [Field F] [Fintype F]

set_option maxHeartbeats 3200000 in
open scoped Classical in
/-- **§6.2 + §6.6: branch selection.**

From the Guruswami–Sudan data alone — a nonzero interpolant `Q` with degree bounds
`(dX, dY, dZ)` and `Q(X, p_z(X), z) = 0` on `S` — produce a bucket: a subset
`S' ⊆ S` of size `> e + 1`, a separable irreducible branch `Sf` with a Frobenius twist
`N = p^f`, a good slice `x₀`, and an irreducible fiber factor `H`, such that every
`z ∈ S'` lies on the branch (with proximate `p_z^N`), is unramified at the slice, and
kills `H`.

Requires `2·dY·dX < |F|` (room for the slice).  The parameter threshold uses the
sharp total capacity `4k·dYdZ+dY`.  The binder `cols` is the number of columns
charged by the selector, not the evaluation-domain size. -/
theorem exists_bucket_sharp (S : Finset F) (p : F → F[X])
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hfield : 2 * dY * dX < Fintype.card F)
    (k cols e slack : ℕ) (hslack : 1 ≤ slack)
    (hS : dY * (e + 2) + cols * (4 * k * (dY * dZ) + dY) / slack
      + dZ + 3 * (dY * dZ) < S.card) :
    ∃ (S' : Finset F) (N d' : ℕ) (Sf : (F[X][X])[X]) (x₀ : F) (H : F[X][X]),
      S' ⊆ S ∧ e + 1 < S'.card ∧
      (∃ f : ℕ, N = ringChar F ^ f) ∧
      1 ≤ d' ∧ Sf.natDegree ≤ d' ∧ d' * N ≤ dY ∧
      (∀ j, IsHeightLE (Sf.coeff j) dZ) ∧
      Irreducible H ∧ 1 ≤ H.natDegree ∧ H.natDegree ≤ d' ∧ IsHeightLE H dZ ∧
      IsHeightLE H (swap F H).natDegree ∧
      cols * sharpFiberCapacity (k * N) d' dZ N H.natDegree (swap F H).natDegree
        < slack * S'.card ∧
      (∀ z ∈ S',
        (Sf.map (mapRingHom (evalRingHom z))).eval ((p z) ^ N) = 0 ∧
        eval₂ (chi z x₀) (((p z) ^ N).eval x₀) (derivative Sf) ≠ 0 ∧
        spec z (((p z) ^ N).eval x₀) H = 0) := by
  set pc := ringChar F with hpc
  haveI hpcP : Fact pc.Prime := ⟨CharP.char_is_prime F pc⟩
  have hpc1 : 1 ≤ pc := hpcP.out.one_lt.le
  -- ### 1. Factor the interpolant.
  obtain ⟨fs, hfsP, hfsA⟩ := UniqueFactorizationMonoid.exists_prime_factors Q hQ0
  obtain ⟨u, hu⟩ := hfsA
  have hfs0 : (0 : (F[X][X])[X]) ∉ fs := fun h => (hfsP 0 h).ne_zero rfl
  have multiset_prod_ne_zero : ∀ s : Multiset ((F[X][X])[X]),
      (∀ a ∈ s, a ≠ 0) → s.prod ≠ 0 := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
        rw [Multiset.prod_cons]
        apply mul_ne_zero
        · exact hs a (Multiset.mem_cons_self a s)
        · exact ih fun b hb => hs b (Multiset.mem_cons_of_mem hb)
  have hprod0 : fs.prod ≠ 0 := multiset_prod_ne_zero fs fun a ha => (hfsP a ha).ne_zero
  have hdegsum : (fs.map natDegree).sum ≤ dY := by
    have h1 : fs.prod.natDegree = (fs.map natDegree).sum := natDegree_multiset_prod fs hfs0
    have h2 : (fs.prod * ↑u).natDegree = fs.prod.natDegree + (↑u : (F[X][X])[X]).natDegree :=
      natDegree_mul hprod0 u.ne_zero
    have h3 : (↑u : (F[X][X])[X]).natDegree = 0 := natDegree_eq_zero_of_isUnit u.isUnit
    rw [hu] at h2
    omega
  have hPdvdQ : ∀ P ∈ fs, P ∣ Q := fun P hP => dvd_trans (Multiset.dvd_prod hP)
    (Dvd.intro _ hu)
  have hPdeg_le : ∀ P ∈ fs, P.natDegree ≤ dY := by
    intro P hP
    refine le_trans ?_ hdegsum
    exact Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
      (Multiset.mem_map_of_mem natDegree hP)
  -- ### 2. Bad parameters where the specialisation dies.
  obtain ⟨j₀, hj₀⟩ : ∃ j, Q.coeff j ≠ 0 := by
    exact ⟨Q.natDegree, by simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hQ0⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, (Q.coeff j₀).coeff i ≠ 0 := by
    exact ⟨(Q.coeff j₀).natDegree,
      by simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hj₀⟩
  set c₀ : F[X] := (Q.coeff j₀).coeff i₀ with hc₀
  set SbadQ : Finset F := S.filter (fun z => c₀.eval z = 0) with hSbadQ
  have hSbadQcard : SbadQ.card ≤ dZ := by
    refine le_trans (card_le_natDegree_of_eval_eq_zero hi₀ _ ?_) (hQZ j₀ i₀)
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  -- ### 3. Choose a prime factor for every surviving parameter.
  have hQzne : ∀ z : F, c₀.eval z ≠ 0 → Q.map (mapRingHom (evalRingHom z)) ≠ 0 := by
    intro z hcz h0
    apply hcz
    have h1 := congrArg (fun W => ((Polynomial.coeff W j₀).coeff i₀)) h0
    simpa [coeff_map, hc₀] using h1
  have hPzchoice : ∀ z : F, ∃ P : (F[X][X])[X], z ∈ S → c₀.eval z ≠ 0 →
      (P ∈ fs ∧ (X - C (p z)) ∣ P.map (mapRingHom (evalRingHom z))) := by
    intro z
    by_cases hz : z ∈ S ∧ c₀.eval z ≠ 0
    · have hdvdQ : (X - C (p z)) ∣ Q.map (mapRingHom (evalRingHom z)) :=
        dvd_iff_isRoot.mpr (hGS z hz.1)
      have hsplit : Q.map (mapRingHom (evalRingHom z))
          = (fs.map (Polynomial.map (mapRingHom (evalRingHom z)))).prod
            * (↑u : (F[X][X])[X]).map (mapRingHom (evalRingHom z)) := by
        rw [← hu, Polynomial.map_mul]
        congr 1
        exact map_multiset_prod (mapRingHom (mapRingHom (evalRingHom z))) fs
      have hprime : Prime ((X : (F[X])[X]) - C (p z)) := prime_X_sub_C (p z)
      rw [hsplit] at hdvdQ
      rcases hprime.2.2 _ _ hdvdQ with hd | hd
      · obtain ⟨Pm, hPm, hPmdvd⟩ := hprime.exists_mem_multiset_dvd hd
        obtain ⟨P, hPfs, rfl⟩ := Multiset.mem_map.mp hPm
        exact ⟨P, fun _ _ => ⟨hPfs, hPmdvd⟩⟩
      · exfalso
        refine hprime.not_unit (isUnit_of_dvd_unit hd ?_)
        exact u.isUnit.map (mapRingHom (mapRingHom (evalRingHom z)))
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hz⟩
  choose Pz hPz using hPzchoice
  -- ### 4. Separable extraction for every prime.
  have hextc : ∀ P : (F[X][X])[X], ∃ (fe : ℕ) (Sf : (F[X][X])[X]),
      (Prime P → 1 ≤ P.natDegree →
        (P = expand _ (pc ^ fe) Sf ∧ Sf.derivative ≠ 0 ∧ Irreducible Sf ∧
          1 ≤ Sf.natDegree ∧ Sf.natDegree * pc ^ fe = P.natDegree)) := by
    intro P
    by_cases hP : Prime P ∧ 1 ≤ P.natDegree
    · obtain ⟨fe, Sf, h⟩ :=
        exists_expand_eq pc P.natDegree P le_rfl hP.1.irreducible hP.2
      exact ⟨fe, Sf, fun _ _ => h⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hP⟩
  choose fe Sfc hext using hextc
  set PS : Finset ((F[X][X])[X]) := fs.toFinset.filter (fun P => 1 ≤ P.natDegree)
    with hPSdef
  have hPSmem : ∀ P ∈ PS, P ∈ fs ∧ Prime P ∧ 1 ≤ P.natDegree := by
    intro P hP
    rw [hPSdef, Finset.mem_filter, Multiset.mem_toFinset] at hP
    exact ⟨hP.1, hfsP P hP.1, hP.2⟩
  -- Facts about the extracted branches.
  have hSf : ∀ P ∈ PS, P = expand _ (pc ^ fe P) (Sfc P) ∧ (Sfc P).derivative ≠ 0 ∧
      Irreducible (Sfc P) ∧ 1 ≤ (Sfc P).natDegree ∧
      (Sfc P).natDegree * pc ^ fe P = P.natDegree := by
    intro P hP
    obtain ⟨_, hprime, hdeg⟩ := hPSmem P hP
    exact hext P hprime hdeg
  have hSfcoeff : ∀ P ∈ PS, ∀ j, (Sfc P).coeff j = P.coeff (j * pc ^ fe P) := by
    intro P hP j
    obtain ⟨hexp, _, _, _, _⟩ := hSf P hP
    have h1 := coeff_expand_mul (pow_pos hpcP.out.pos (fe P)) (Sfc P) j
    rw [← hexp] at h1
    exact h1.symm
  have hSfX : ∀ P ∈ PS, ∀ j, ((Sfc P).coeff j).natDegree ≤ dX := by
    intro P hP j
    rw [hSfcoeff P hP j]
    exact degX_of_dvd (hPdvdQ P (hPSmem P hP).1) hQ0 hQX _
  have hSfZ : ∀ P ∈ PS, ∀ j, IsHeightLE ((Sfc P).coeff j) dZ := by
    intro P hP j
    rw [hSfcoeff P hP j]
    intro i
    exact heightZ_of_dvd (hPdvdQ P (hPSmem P hP).1) hQ0 hQZ _ i
  have hSfdX : ∀ P ∈ PS, ∀ j, ((derivative (Sfc P)).coeff j).natDegree ≤ dX := by
    intro P hP j
    rw [coeff_derivative]
    refine le_trans (natDegree_mul_le) ?_
    have h1 := hSfX P hP (j + 1)
    have hCj : (C ((j : F[X]) + 1) : F[X][X]) = (j : F[X][X]) + 1 := by
      rw [map_add, map_natCast, map_one]
    have h2 : ((j : F[X][X]) + 1).natDegree = 0 := by
      rw [← hCj, natDegree_C]
    omega
  have hSfdZ : ∀ P ∈ PS, ∀ j, IsHeightLE ((derivative (Sfc P)).coeff j) dZ := by
    intro P hP j
    rw [coeff_derivative]
    have h1 : IsHeightLE ((j : F[X][X]) + 1) 0 := by
      have hCj : (C ((j : F[X]) + 1) : F[X][X]) = (j : F[X][X]) + 1 := by
        rw [map_add, map_natCast, map_one]
      rw [← hCj]
      intro i
      rw [coeff_C]
      split_ifs with h
      · have hCj' : (C ((j : F) + 1) : F[X]) = (j : F[X]) + 1 := by
          rw [map_add, map_natCast, map_one]
        rw [← hCj', natDegree_C]
      · simp
    have := (hSfZ P hP (j + 1)).mul h1
    simpa using this
  -- ### 5. Discriminants are nonzero.
  set rr : (F[X][X])[X] → F[X][X] := fun P =>
    resultant (Sfc P) (derivative (Sfc P)) (Sfc P).natDegree
      (derivative (Sfc P)).natDegree with hrr
  have hrr0 : ∀ P ∈ PS, rr P ≠ 0 := by
    intro P hP h0
    obtain ⟨hexp, hder, hirr, hdeg1, hdegeq⟩ := hSf P hP
    set L := FractionRing (F[X][X])
    set ψ : F[X][X] →+* L := algebraMap _ _ with hψ
    have hinj : Function.Injective ψ := IsFractionRing.injective _ _
    have hprim : (Sfc P).IsPrimitive := isPrimitive_of_irreducible' hirr hdeg1
    have hirrL : Irreducible ((Sfc P).map ψ) :=
      hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
    have hder0 : (derivative (Sfc P)).map ψ ≠ 0 := by
      rw [Ne, Polynomial.map_eq_zero_iff hinj]
      exact hder
    have hdegmap : ((Sfc P).map ψ).natDegree = (Sfc P).natDegree :=
      natDegree_map_eq_of_injective hinj _
    have hdegmapd : ((derivative (Sfc P)).map ψ).natDegree
        = (derivative (Sfc P)).natDegree := natDegree_map_eq_of_injective hinj _
    have hndvd : ¬ ((Sfc P).map ψ ∣ (derivative (Sfc P)).map ψ) := by
      intro hdvd
      have h1 := natDegree_le_of_dvd hdvd hder0
      have h2 : (derivative (Sfc P)).natDegree < (Sfc P).natDegree :=
        natDegree_derivative_lt (by omega)
      omega
    have hcop : IsCoprime ((Sfc P).map ψ) ((derivative (Sfc P)).map ψ) :=
      (hirrL.coprime_iff_not_dvd).mpr hndvd
    have hres0 : resultant ((Sfc P).map ψ) ((derivative (Sfc P)).map ψ) = 0 := by
      rw [hdegmap, hdegmapd, resultant_map_map]
      show ψ (rr P) = 0
      rw [h0, map_zero]
    have := (resultant_eq_zero_iff.mp hres0).2
    exact this hcop
  -- ### 6. The good slice.
  set badX : Finset F := PS.biUnion (fun P =>
    univ.filter (fun x₀ : F => (rr P).eval (C x₀) = 0)) with hbadXdef
  have hbadXP : ∀ P ∈ PS,
      (univ.filter (fun x₀ : F => (rr P).eval (C x₀) = 0)).card
        ≤ 2 * (Sfc P).natDegree * dX := by
    intro P hP
    obtain ⟨_, _, _, hdeg1, _⟩ := hSf P hP
    have hcard : (univ.filter (fun x₀ : F => (rr P).eval (C x₀) = 0)).card
        ≤ (rr P).natDegree := by
      refine le_trans (Finset.card_le_card_of_injOn (fun x₀ => (C x₀ : F[X])) ?_ ?_)
        (le_trans (rr P).roots.toFinset_card_le (card_roots' _))
      · intro x hx
        have hx2 : (rr P).eval (C x) = 0 := by simpa using hx
        simpa [Multiset.mem_toFinset, mem_roots, hrr0 P hP] using hx2
      · exact fun a _ b _ h => C_injective h
    refine le_trans hcard ?_
    have hbound := natDegree_resultant_le (Sfc P) (derivative (Sfc P))
      ((Sfc P).natDegree) ((derivative (Sfc P)).natDegree)
      (hSfX P hP) (hSfdX P hP)
    have hdlt : (derivative (Sfc P)).natDegree ≤ (Sfc P).natDegree :=
      le_of_lt (natDegree_derivative_lt (by omega))
    have h2 : (derivative (Sfc P)).natDegree * dX + (Sfc P).natDegree * dX
        ≤ 2 * (Sfc P).natDegree * dX := by
      rw [two_mul, add_mul]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hdlt) _
    exact le_trans hbound h2
  have hdegSf_sum : ∑ P ∈ PS, (Sfc P).natDegree ≤ dY := by
    refine le_trans ?_ (le_trans (toFinset_sum_le_multiset_sum fs natDegree) hdegsum)
    have hsub : PS ⊆ fs.toFinset := Finset.filter_subset _ _
    refine le_trans (Finset.sum_le_sum fun P hP => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _)
    obtain ⟨_, _, _, hdeg1, hdegeq⟩ := hSf P hP
    calc (Sfc P).natDegree ≤ (Sfc P).natDegree * pc ^ fe P :=
          Nat.le_mul_of_pos_right _ (pow_pos hpcP.out.pos _)
      _ = P.natDegree := hdegeq
  have hbadXcard : badX.card ≤ 2 * dY * dX := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum hbadXP) ?_
    calc ∑ P ∈ PS, 2 * (Sfc P).natDegree * dX
        = ∑ P ∈ PS, 2 * dX * (Sfc P).natDegree :=
          Finset.sum_congr rfl fun P _ => by ring
      _ = 2 * dX * ∑ P ∈ PS, (Sfc P).natDegree := by rw [← Finset.mul_sum]
      _ ≤ 2 * dX * dY := Nat.mul_le_mul_left _ hdegSf_sum
      _ = 2 * dY * dX := by ring
  obtain ⟨x₀, hx₀mem⟩ : (univ \ badX).Nonempty := by
    rw [← Finset.card_pos, card_sdiff_of_subset (subset_univ _), card_univ]
    omega
  have hx₀ : ∀ P ∈ PS, (rr P).eval (C x₀) ≠ 0 := by
    intro P hP h0
    rw [Finset.mem_sdiff] at hx₀mem
    exact hx₀mem.2 (Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h0⟩⟩)
  -- ### 7. Fiber factorisations.
  have hgchoice : ∀ P : (F[X][X])[X], ∃ gs : Multiset (F[X][X]),
      (P ∈ PS → ((∀ g ∈ gs, Prime g) ∧ Associated gs.prod (fiberAt x₀ (Sfc P)))) := by
    intro P
    by_cases hP : P ∈ PS
    · obtain ⟨_, _, hirr, hdeg1, _⟩ := hSf P hP
      have hfib0 : fiberAt x₀ (Sfc P) ≠ 0 := fiberAt_ne_zero x₀ hirr hdeg1
      obtain ⟨gs, h1, h2⟩ := UniqueFactorizationMonoid.exists_prime_factors _ hfib0
      exact ⟨gs, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose gsc hgsc using hgchoice
  have hfibZ : ∀ P ∈ PS, IsHeightLE (fiberAt x₀ (Sfc P)) dZ := by
    intro P hP
    exact fiberAt_isHeightLE x₀ (Sfc P) (hSfZ P hP)
  have hfib0 : ∀ P ∈ PS, fiberAt x₀ (Sfc P) ≠ 0 := by
    intro P hP
    obtain ⟨_, _, hirr, hdeg1, _⟩ := hSf P hP
    exact fiberAt_ne_zero x₀ hirr hdeg1
  have hgs0 : ∀ P ∈ PS, (0 : F[X][X]) ∉ gsc P := by
    intro P hP h
    exact (((hgsc P hP).1) 0 h).ne_zero rfl
  -- The prime factors of the fiber divide it.
  have hgdvd : ∀ P ∈ PS, ∀ g ∈ gsc P, g ∣ fiberAt x₀ (Sfc P) := by
    intro P hP g hg
    obtain ⟨v, hv⟩ := (hgsc P hP).2
    exact dvd_trans (Multiset.dvd_prod hg) (Dvd.intro _ hv)
  -- ### 8. Labels and their count.
  set LBL : Finset ((F[X][X])[X] × F[X][X]) :=
    PS.biUnion (fun P =>
      ((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).image (fun H => (P, H)))
    with hLBLdef
  have hLBLcount : ∀ P ∈ PS,
      (((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).card) ≤ (Sfc P).natDegree := by
    intro P hP
    have h1 : (((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).card)
        ≤ ∑ g ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree), g.natDegree := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun g hg => ?_
      exact (Finset.mem_filter.mp hg).2
    have h2 : ∑ g ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree), g.natDegree
        ≤ ∑ g ∈ (gsc P).toFinset, g.natDegree :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
    have h3 : ∑ g ∈ (gsc P).toFinset, g.natDegree ≤ ((gsc P).map natDegree).sum :=
      toFinset_sum_le_multiset_sum _ _
    have h4 : ((gsc P).map natDegree).sum = (gsc P).prod.natDegree :=
      (natDegree_multiset_prod _ (hgs0 P hP)).symm
    have h5 : (gsc P).prod.natDegree = (fiberAt x₀ (Sfc P)).natDegree := by
      obtain ⟨v, hv⟩ := (hgsc P hP).2
      have hp0 : (gsc P).prod ≠ 0 := Multiset.prod_ne_zero (hgs0 P hP)
      rw [← hv, natDegree_mul hp0 v.ne_zero, natDegree_eq_zero_of_isUnit v.isUnit]
      ring
    have h6 : (fiberAt x₀ (Sfc P)).natDegree ≤ (Sfc P).natDegree :=
      fiberAt_natDegree_le x₀ _ le_rfl
    omega
  have hLBLcard : LBL.card ≤ dY := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum (fun P hP =>
      le_trans (Finset.card_image_le) (hLBLcount P hP))) hdegSf_sum
  -- Exact degree and height sums for the fiber labels.  These are the data needed
  -- for degree-weighted selection; applying `dY` and `dZ` to every label separately
  -- would lose an avoidable factor of `dY`.
  have hPdeg_sum : ∑ P ∈ PS, P.natDegree ≤ dY := by
    have hsub : PS ⊆ fs.toFinset := Finset.filter_subset _ _
    exact le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
      (le_trans (toFinset_sum_le_multiset_sum fs natDegree) hdegsum)
  have hPScard : PS.card ≤ dY := by
    rw [Finset.card_eq_sum_ones]
    exact le_trans (Finset.sum_le_sum fun P hP => (hPSmem P hP).2.2) hPdeg_sum
  have hHdeg_sum : ∀ P ∈ PS,
      ∑ H ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree), H.natDegree
        ≤ (Sfc P).natDegree := by
    intro P hP
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)) ?_
    refine le_trans (toFinset_sum_le_multiset_sum (gsc P) natDegree) ?_
    rw [← natDegree_multiset_prod (gsc P) (hgs0 P hP)]
    obtain ⟨v, hv⟩ := (hgsc P hP).2
    have hp0 : (gsc P).prod ≠ 0 := Multiset.prod_ne_zero (hgs0 P hP)
    have hproddeg : (gsc P).prod.natDegree = (fiberAt x₀ (Sfc P)).natDegree := by
      rw [← hv, natDegree_mul hp0 v.ne_zero, natDegree_eq_zero_of_isUnit v.isUnit]
      ring
    rw [hproddeg]
    exact fiberAt_natDegree_le x₀ _ le_rfl
  have hHheight_sum : ∀ P ∈ PS,
      ∑ H ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree),
        (swap F H).natDegree ≤ dZ := by
    intro P hP
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)) ?_
    refine le_trans (toFinset_sum_le_multiset_sum (gsc P) (fun H => (swap F H).natDegree)) ?_
    have hswap0 : (0 : F[X][X]) ∉ (gsc P).map (swap F) := by
      intro h
      obtain ⟨g, hg, hgg⟩ := Multiset.mem_map.mp h
      exact hgs0 P hP (swap_eq_zero_iff.mp hgg ▸ hg)
    rw [show ((gsc P).map (fun H => (swap F H).natDegree)).sum =
        (((gsc P).map (swap F)).map natDegree).sum by
          simp [Multiset.map_map]]
    rw [← natDegree_multiset_prod ((gsc P).map (swap F)) hswap0,
      ← map_multiset_prod (swap F) (gsc P)]
    obtain ⟨v, hv⟩ := (hgsc P hP).2
    have hp0 : (gsc P).prod ≠ 0 := Multiset.prod_ne_zero (hgs0 P hP)
    have hv0 : (↑v : F[X][X]) ≠ 0 := v.ne_zero
    have hswapdeg : (swap F (gsc P).prod).natDegree =
        (swap F (fiberAt x₀ (Sfc P))).natDegree := by
      rw [← hv, map_mul, natDegree_mul]
      · rw [natDegree_eq_zero_of_isUnit (v.isUnit.map (swap F))]
        ring
      · intro h
        exact hp0 (swap_eq_zero_iff.mp h)
      · intro h
        exact hv0 (swap_eq_zero_iff.mp h)
    rw [hswapdeg]
    exact isHeightLE_iff_natDegree_swap_le.mp (hfibZ P hP)
  have hLBLpairwise : (↑PS : Set ((F[X][X])[X])).PairwiseDisjoint (fun P =>
      ((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).image (fun H => (P, H))) := by
    intro P hP P' hP' hne
    rw [Function.onFun_apply, Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨H, _, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨H', _, hpair⟩ := Finset.mem_image.mp hl'
    exact hne (congrArg Prod.fst hpair.symm)
  let cap (k : ℕ) (l : (F[X][X])[X] × F[X][X]) : ℕ :=
    sharpFiberCapacity (k * pc ^ fe l.1) (Sfc l.1).natDegree dZ (pc ^ fe l.1)
      l.2.natDegree (swap F l.2).natDegree
  have hcapP : ∀ (k : ℕ) P, P ∈ PS →
      ∑ l ∈ ((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).image (fun H => (P, H)),
        cap k l ≤ sharpFactorCapacity k dZ P.natDegree := by
    intro k P hP
    rw [Finset.sum_image]
    · change ∑ H ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree),
        sharpFiberCapacity (k * pc ^ fe P) (Sfc P).natDegree dZ
          (pc ^ fe P) H.natDegree (swap F H).natDegree ≤
            sharpFactorCapacity k dZ P.natDegree
      refine le_trans (sum_sharpFiberCapacity_le _ _ _ (hHdeg_sum P hP)
        (hHheight_sum P hP)) ?_
      exact sharp_extractedCapacity_le (hSf P hP).2.2.2.2
    · intro H hH H' hH' heq
      exact congrArg Prod.snd heq
  have hLBLcapacity : ∀ k : ℕ,
      ∑ l ∈ LBL, cap k l ≤ 4 * k * (dY * dZ) + dY := by
    intro k
    rw [hLBLdef, Finset.sum_biUnion hLBLpairwise]
    refine le_trans (Finset.sum_le_sum (hcapP k)) ?_
    exact sum_sharpFactorCapacity_uniform_height_le PS natDegree hPdeg_sum
  -- ### 9. Bad parameters from degree-zero fiber factors and from ramification.
  set SbadFib : Finset F := PS.biUnion (fun P =>
    ((gsc P).toFinset.filter (fun g => g.natDegree = 0)).biUnion (fun g =>
      univ.filter (fun z : F => (g.coeff 0).eval z = 0))) with hSbadFibdef
  have hSbadFibP : ∀ P ∈ PS,
      (((gsc P).toFinset.filter (fun g => g.natDegree = 0)).biUnion (fun g =>
        univ.filter (fun z : F => (g.coeff 0).eval z = 0))).card ≤ dZ := by
    intro P hP
    refine le_trans (Finset.card_biUnion_le) ?_
    -- Each degree-zero prime factor contributes at most its `Z`-degree, and those
    -- `Z`-degrees sum to at most the fiber height.
    have hterm : ∀ g ∈ (gsc P).toFinset.filter (fun g => g.natDegree = 0),
        (univ.filter (fun z : F => (g.coeff 0).eval z = 0)).card
          ≤ (swap F g).natDegree := by
      intro g hg
      rw [Finset.mem_filter, Multiset.mem_toFinset] at hg
      have hg0 : g ≠ 0 := ((hgsc P hP).1 g hg.1).ne_zero
      have hc0 : g.coeff 0 ≠ 0 := by
        intro h
        apply hg0
        have := eq_C_of_natDegree_eq_zero hg.2
        rw [this, h, map_zero]
      refine le_trans (card_le_natDegree_of_eval_eq_zero hc0 _ ?_) ?_
      · intro z hz
        exact (Finset.mem_filter.mp hz).2
      · exact natDegree_swap_le_iff.mp le_rfl 0
    refine le_trans (Finset.sum_le_sum hterm) ?_
    -- Sum of swapped degrees over the factors is the swapped degree of the fiber.
    have hsum : ∑ g ∈ (gsc P).toFinset.filter (fun g => g.natDegree = 0),
        (swap F g).natDegree ≤ ((gsc P).map (fun g => (swap F g).natDegree)).sum := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)) ?_
      exact toFinset_sum_le_multiset_sum _ _
    refine le_trans hsum ?_
    have hswap0 : (0 : F[X][X]) ∉ (gsc P).map (swap F) := by
      intro h
      obtain ⟨g, hg, hgg⟩ := Multiset.mem_map.mp h
      have hg0 : g = 0 := swap_eq_zero_iff.mp hgg
      rw [hg0] at hg
      exact hgs0 P hP hg
    have h1 : ((gsc P).map (fun g => (swap F g).natDegree)).sum
        = (((gsc P).map (swap F)).map natDegree).sum := by
      rw [Multiset.map_map]
      rfl
    have h2 : (((gsc P).map (swap F)).map natDegree).sum
        = (((gsc P).map (swap F)).prod).natDegree :=
      (natDegree_multiset_prod _ hswap0).symm
    have h3 : ((gsc P).map (swap F)).prod = swap F ((gsc P).prod) :=
      (map_multiset_prod (swap F) (gsc P)).symm
    have h4 : (swap F ((gsc P).prod)).natDegree
        ≤ (swap F (fiberAt x₀ (Sfc P))).natDegree := by
      obtain ⟨v, hv⟩ := (hgsc P hP).2
      have : swap F (fiberAt x₀ (Sfc P)) = swap F ((gsc P).prod) * swap F ↑v := by
        rw [← map_mul, hv]
      rw [this, natDegree_mul, natDegree_eq_zero_of_isUnit (v.isUnit.map _)]
      · omega
      · rw [Ne, swap_eq_zero_iff]
        exact Multiset.prod_ne_zero (hgs0 P hP)
      · rw [Ne, swap_eq_zero_iff]
        exact v.ne_zero
    have h5 : (swap F (fiberAt x₀ (Sfc P))).natDegree ≤ dZ :=
      isHeightLE_iff_natDegree_swap_le.mp (hfibZ P hP)
    rw [h3] at h2
    omega
  have hSbadFibcard : SbadFib.card ≤ dY * dZ := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum hSbadFibP) ?_
    calc ∑ _P ∈ PS, dZ = PS.card * dZ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ dY * dZ := Nat.mul_le_mul_right _ hPScard
  set SbadDisc : Finset F := PS.biUnion (fun P =>
    univ.filter (fun z : F => ((rr P).eval (C x₀)).eval z = 0)) with hSbadDiscdef
  have hSbadDiscP : ∀ P ∈ PS,
      (univ.filter (fun z : F => ((rr P).eval (C x₀)).eval z = 0)).card
        ≤ 2 * (Sfc P).natDegree * dZ := by
    intro P hP
    obtain ⟨_, _, _, hdeg1, _⟩ := hSf P hP
    have hρ0 : (rr P).eval (C x₀) ≠ 0 := hx₀ P hP
    refine le_trans (card_le_natDegree_of_eval_eq_zero hρ0 _
      (fun z hz => (Finset.mem_filter.mp hz).2)) ?_
    have hht : IsHeightLE (rr P) ((derivative (Sfc P)).natDegree * dZ
        + (Sfc P).natDegree * dZ) :=
      isHeightLE_resultant (Sfc P) (derivative (Sfc P)) _ _ (hSfZ P hP) (hSfdZ P hP)
    have h1 : ((rr P).eval (C x₀)).natDegree ≤ (derivative (Sfc P)).natDegree * dZ
        + (Sfc P).natDegree * dZ := natDegree_eval_C_le hht x₀
    have hdlt : (derivative (Sfc P)).natDegree ≤ (Sfc P).natDegree :=
      le_of_lt (natDegree_derivative_lt (by omega))
    refine le_trans h1 ?_
    rw [two_mul, add_mul]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hdlt) _
  have hSbadDisccard : SbadDisc.card ≤ 2 * (dY * dZ) := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum hSbadDiscP) ?_
    calc ∑ P ∈ PS, 2 * (Sfc P).natDegree * dZ
        = ∑ P ∈ PS, 2 * dZ * (Sfc P).natDegree :=
          Finset.sum_congr rfl fun P _ => by ring
      _ = 2 * dZ * ∑ P ∈ PS, (Sfc P).natDegree := by rw [← Finset.mul_sum]
      _ ≤ 2 * dZ * dY := Nat.mul_le_mul_left _ hdegSf_sum
      _ = 2 * (dY * dZ) := by ring
  -- ### 10. The surviving parameters and their labels.
  set S₂ : Finset F := S \ (SbadQ ∪ SbadFib ∪ SbadDisc) with hS₂def
  have hS₂card : dY * (e + 2) + cols * (4 * k * (dY * dZ) + dY) / slack
      < S₂.card := by
    have h1 : (SbadQ ∪ SbadFib ∪ SbadDisc).card
        ≤ dZ + dY * dZ + 2 * (dY * dZ) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have h2 := Finset.card_union_le SbadQ SbadFib
      omega
    have h3 : S.card - (SbadQ ∪ SbadFib ∪ SbadDisc).card ≤ S₂.card := by
      rw [hS₂def]
      have := Finset.le_card_sdiff (SbadQ ∪ SbadFib ∪ SbadDisc) S
      omega
    omega
  -- Basic membership facts for survivors.
  have hS₂S : S₂ ⊆ S := Finset.sdiff_subset
  have hS₂c₀ : ∀ z ∈ S₂, c₀.eval z ≠ 0 := by
    intro z hz h0
    rw [hS₂def, Finset.mem_sdiff] at hz
    exact hz.2 (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hz.1, h0⟩)))
  have hPzmem : ∀ z ∈ S₂, Pz z ∈ PS := by
    intro z hz
    obtain ⟨hPfs, hdvd⟩ := hPz z (hS₂S hz) (hS₂c₀ z hz)
    rw [hPSdef, Finset.mem_filter, Multiset.mem_toFinset]
    refine ⟨hPfs, ?_⟩
    -- The specialisation is nonzero, so the divisibility forces positive degree.
    have hmapne : (Pz z).map (mapRingHom (evalRingHom z)) ≠ 0 := by
      intro h0
      apply hQzne z (hS₂c₀ z hz)
      have hsplit : Q.map (mapRingHom (evalRingHom z))
          = (fs.map (Polynomial.map (mapRingHom (evalRingHom z)))).prod
            * (↑u : (F[X][X])[X]).map (mapRingHom (evalRingHom z)) := by
        rw [← hu, Polynomial.map_mul]
        congr 1
        exact map_multiset_prod (mapRingHom (mapRingHom (evalRingHom z))) fs
      have hzero : (0 : (F[X])[X]) ∈ fs.map (Polynomial.map (mapRingHom (evalRingHom z))) := by
        rw [← h0]
        exact Multiset.mem_map_of_mem _ hPfs
      rw [hsplit, Multiset.prod_eq_zero hzero, zero_mul]
    have h1 : 1 ≤ ((Pz z).map (mapRingHom (evalRingHom z))).natDegree := by
      have h2 := natDegree_le_of_dvd hdvd hmapne
      rw [natDegree_X_sub_C] at h2
      omega
    exact le_trans h1 (natDegree_map_le)
  -- The branch root property for survivors.
  have hSfroot : ∀ z ∈ S₂,
      ((Sfc (Pz z)).map (mapRingHom (evalRingHom z))).eval
        ((p z) ^ (pc ^ fe (Pz z))) = 0 := by
    intro z hz
    obtain ⟨hPfs, hdvd⟩ := hPz z (hS₂S hz) (hS₂c₀ z hz)
    obtain ⟨hexp, _, _, _, _⟩ := hSf (Pz z) (hPzmem z hz)
    have hev : ((Pz z).map (mapRingHom (evalRingHom z))).eval (p z) = 0 := by
      have := dvd_iff_isRoot.mp hdvd
      exact this
    calc ((Sfc (Pz z)).map (mapRingHom (evalRingHom z))).eval ((p z) ^ (pc ^ fe (Pz z)))
        = ((expand _ (pc ^ fe (Pz z)) (Sfc (Pz z))).map
            (mapRingHom (evalRingHom z))).eval (p z) :=
          (eval_map_expand_eq _ _ _ _).symm
      _ = ((Pz z).map (mapRingHom (evalRingHom z))).eval (p z) := by rw [← hexp]
      _ = 0 := hev
  -- The fiber kill for survivors.
  have hfibkill : ∀ z ∈ S₂,
      spec z (((p z) ^ (pc ^ fe (Pz z))).eval x₀) (fiberAt x₀ (Sfc (Pz z))) = 0 := by
    intro z hz
    rw [spec_fiberAt, ← eval_eval_map_eq, hSfroot z hz, eval_zero]
  -- The unramifiedness for survivors.
  have hxine : ∀ z ∈ S₂,
      eval₂ (chi z x₀) (((p z) ^ (pc ^ fe (Pz z))).eval x₀)
        (derivative (Sfc (Pz z))) ≠ 0 := by
    intro z hz h0
    obtain ⟨_, _, _, hdeg1, _⟩ := hSf (Pz z) (hPzmem z hz)
    have hroot : eval₂ (chi z x₀) (((p z) ^ (pc ^ fe (Pz z))).eval x₀) (Sfc (Pz z)) = 0 := by
      rw [← eval_eval_map_eq, hSfroot z hz, eval_zero]
    have hres := ringHom_resultant_eq_zero_of_common_root (chi z x₀)
      (Sfc (Pz z)) (derivative (Sfc (Pz z))) le_rfl le_rfl (Or.inl (by omega))
      _ hroot h0
    have hzS₂ := hz
    rw [hS₂def, Finset.mem_sdiff] at hz
    apply hz.2
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨Pz z, hPzmem z hzS₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩)
    · rw [← chi_apply]
      exact hres
  -- The fiber-factor label for survivors.
  have hlabchoice : ∀ z : F, ∃ Hl : F[X][X], z ∈ S₂ →
      (Hl ∈ gsc (Pz z) ∧ 1 ≤ Hl.natDegree ∧
        spec z (((p z) ^ (pc ^ fe (Pz z))).eval x₀) Hl = 0) := by
    intro z
    by_cases hz : z ∈ S₂
    · set t := ((p z) ^ (pc ^ fe (Pz z))).eval x₀ with ht
      obtain ⟨v, hv⟩ := (hgsc (Pz z) (hPzmem z hz)).2
      have hkill := hfibkill z hz
      rw [← hv, map_mul] at hkill
      have hvne : spec z t (↑v : F[X][X]) ≠ 0 := by
        have := (v.isUnit.map (spec z t)).ne_zero
        exact this
      have hprodzero : spec z t ((gsc (Pz z)).prod) = 0 := by
        rcases mul_eq_zero.mp hkill with h | h
        · exact h
        · exact absurd h hvne
      rw [map_multiset_prod] at hprodzero
      have h0mem : (0 : F) ∈ (gsc (Pz z)).map (spec z t) :=
        Multiset.prod_eq_zero_iff.mp hprodzero
      obtain ⟨g, hg, hg0⟩ := Multiset.mem_map.mp h0mem
      refine ⟨g, fun _ => ⟨hg, ?_, hg0⟩⟩
      -- Positive degree, else `z` would be a bad parameter.
      apply Nat.one_le_iff_ne_zero.mpr
      intro hdeg0
      have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hdeg0
      have heval : (g.coeff 0).eval z = 0 := by
        have : spec z t g = (g.coeff 0).eval z := by
          rw [hgC, spec_apply, eval₂_C]
          simp
        rw [← this, hg0]
      have hzS₂ := hz
      rw [hS₂def, Finset.mem_sdiff] at hz
      apply hz.2
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      refine Finset.mem_biUnion.mpr ⟨Pz z, hPzmem z hzS₂, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨g, ?_, ?_⟩
      · rw [Finset.mem_filter, Multiset.mem_toFinset]
        exact ⟨hg, hdeg0⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heval⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose Hlab hHlab using hlabchoice
  -- ### 11. Degree-weighted factor selection.
  set lab : F → ((F[X][X])[X] × F[X][X]) := fun z => (Pz z, Hlab z) with hlabdef
  have hmapsto : ∀ z ∈ S₂, lab z ∈ LBL := by
    intro z hz
    obtain ⟨hg, hdeg, _⟩ := hHlab z hz
    refine Finset.mem_biUnion.mpr ⟨Pz z, hPzmem z hz, ?_⟩
    refine Finset.mem_image.mpr ⟨Hlab z, ?_, rfl⟩
    rw [Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨hg, hdeg⟩
  have hthresholdSum :
      (∑ l ∈ LBL, incidenceThreshold cols slack e (cap k l)) < S₂.card := by
    refine lt_of_le_of_lt (sum_incidenceThreshold_le LBL (cap k) cols slack e) ?_
    refine lt_of_le_of_lt (Nat.add_le_add
      (Nat.mul_le_mul_right (e + 2) hLBLcard)
      (Nat.div_le_div_right (Nat.mul_le_mul_left cols (hLBLcapacity k)))) hS₂card
  obtain ⟨labSel, hlabmem, hfibercard, hfiberinc⟩ :=
    exists_weighted_incidence_bucket S₂ lab LBL (cap k)
      (fun l => incidenceThreshold cols slack e (cap k l)) hmapsto hslack
      (fun l _ => incidenceThreshold_min cols slack e (cap k l))
      (fun l _ => incidenceThreshold_incidence (show 0 < slack by omega)) hthresholdSum
  set Psel := labSel.1 with hPsel
  set Hsel := labSel.2 with hHsel
  set S' : Finset F := S₂.filter (fun z => lab z = labSel) with hS'def
  have hS'S₂ : S' ⊆ S₂ := Finset.filter_subset _ _
  have hS'P : ∀ z ∈ S', Pz z = Psel ∧ Hlab z = Hsel := by
    intro z hz
    have := (Finset.mem_filter.mp hz).2
    rw [hlabdef] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  -- The selected label's data.
  have hPselPS : Psel ∈ PS := by
    rw [hLBLdef] at hlabmem
    obtain ⟨P, hP, hPl⟩ := Finset.mem_biUnion.mp hlabmem
    obtain ⟨Hf, hHfmem, hHf⟩ := Finset.mem_image.mp hPl
    have h1 : P = Psel := congrArg Prod.fst hHf
    rw [← h1]
    exact hP
  have hHselmem : Hsel ∈ gsc Psel ∧ 1 ≤ Hsel.natDegree := by
    rw [hLBLdef] at hlabmem
    obtain ⟨P, hP, hPl⟩ := Finset.mem_biUnion.mp hlabmem
    obtain ⟨Hf, hHfmem, hHf⟩ := Finset.mem_image.mp hPl
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hHfmem
    have h1 : P = Psel := congrArg Prod.fst hHf
    have h2 : Hf = Hsel := congrArg Prod.snd hHf
    rw [← h1, ← h2]
    exact hHfmem
  obtain ⟨hexpSel, hderSel, hirrSel, hdeg1Sel, hdegeqSel⟩ := hSf Psel hPselPS
  -- ### 12. Package the output.
  refine ⟨S', pc ^ fe Psel, (Sfc Psel).natDegree, Sfc Psel, x₀, Hsel,
    Finset.Subset.trans hS'S₂ hS₂S, ?_, ⟨fe Psel, rfl⟩, hdeg1Sel, le_rfl, ?_, hSfZ Psel hPselPS,
    ((hgsc Psel hPselPS).1 Hsel hHselmem.1).irreducible, hHselmem.2, ?_, ?_, ?_, ?_, ?_⟩
  · -- bucket size
    have : e + 1 < (S₂.filter (fun z => lab z = labSel)).card := hfibercard
    simpa [hS'def] using this
  · -- degree product bound
    rw [hdegeqSel]
    exact hPdeg_le Psel (hPSmem Psel hPselPS).1
  · -- `Hsel` degree bound
    have hdvd := hgdvd Psel hPselPS Hsel hHselmem.1
    refine le_trans (natDegree_le_of_dvd hdvd (hfib0 Psel hPselPS)) ?_
    exact fiberAt_natDegree_le x₀ _ le_rfl
  · -- `Hsel` height bound
    exact isHeightLE_of_dvd (hgdvd Psel hPselPS Hsel hHselmem.1) (hfib0 Psel hPselPS)
      (hfibZ Psel hPselPS)
  · -- exact `Hsel` height
    exact isHeightLE_iff_natDegree_swap_le.mpr le_rfl
  · -- selected label's exact incidence capacity
    simpa [cap, hPsel, hHsel, hS'def] using hfiberinc
  · -- the per-parameter facts
    intro z hz
    obtain ⟨hPzz, hHz⟩ := hS'P z hz
    have hz₂ := hS'S₂ hz
    refine ⟨?_, ?_, ?_⟩
    · have := hSfroot z hz₂
      rwa [hPzz] at this
    · have := hxine z hz₂
      rwa [hPzz] at this
    · have := (hHlab z hz₂).2.2
      rwa [hPzz, hHz] at this

end Selection

end JBAgreement
end
-- ===== end of `LvmJBSelect` =====

-- ===== merged from `LvmJBEndToEnd` (GOLF module merge: `LvmJBEndToEnd.lean` is now a stub importing `LvmJBComplete`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBEndToEnd.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# The end-to-end theorem: correlated agreement from Guruswami–Sudan alone

`correlatedAgreement_of_GS_sharp` is the deliverable: BCIKS correlated agreement in the
Johnson regime, together with Haböck's mutual strengthening, assuming **only** the
Guruswami–Sudan interpolant.  Everything between GS and the conclusion — branch
selection, the inseparable case, the good slice, the finite jet with its ledger, the
resultant counting, the incidence argument, interpolation and the affine endgame — is
proved.

**Assumed** (the hypotheses named `Q`, `hQ0`, `hQY`, `hQX`, `hQZ`, `hGS`): a nonzero
trivariate interpolant of `Y`-degree ≤ `dY`, `X`-degree ≤ `dX`, `Z`-height ≤ `dZ`,
vanishing on the graph of every proximate.  This is exactly the output of
Guruswami–Sudan interpolation applied over `F[Z]` to the line `u₀ + Z·u₁`; `GS.lean`
constructs it for the unconditional theorem.

**Numeric side conditions** (not assumptions, part of the theorem):
* `2·dY·dX < |F|` — room for the good slice; the standard field-size requirement, also
  present in BCIKS (their error term carries a `1/q`).
* the weighted threshold `hS`, whose leading factor capacity is linear in `dY·dZ`
  and therefore has size `O_ρ(n/η³)`.

The flow: `exists_bucket_sharp` (§6.2/§6.6) → `recenter` → `exists_goodCoords_sharp` (§1–§3 via
the ledger) → Frobenius untwisting → Lagrange → §4.  The mutual clause is
`mutual_correlatedAgreement` applied to the produced pair.
-/

namespace JBAgreement

open Polynomial Finset

section EndToEnd

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The total exact factor capacity after summing all fiber factors. -/
def sharpGSBound (k dY dZ : ℕ) : ℕ := 4 * k * (dY * dZ) + dY

/-- **The affine bucket.**  The shared core of the end-to-end theorems: from the GS
data, a pair `(v₀, v₁)` of dimension-`k` polynomials and a sub-bucket `S' ⊆ S` with
`|S'| > e + 1` on which *the chosen proximates are exactly the line*:
`p z = v₀ + z·v₁`.  Everything downstream (plain CA, per-line mutual CA, and the
strong mutual CA of `StrongMutual.lean`) is endgame bookkeeping on this output.

Hypotheses:
* `hpdeg`, `hprox` — for each `z ∈ S` a proximate `p z` with natural degree `< k` within
  distance `e` of the line point `u₀ + z·u₁`;
* `Q, …, hGS` — **the assumed GS interpolant**: nonzero, `Y`-degree ≤ `dY`,
  `X`-degree ≤ `dX`, `Z`-height ≤ `dZ`, with `Q(X, p_z(X), z) = 0` for `z ∈ S`;
* `hfield` — the field is large enough for a good slice;
* `hslack`, `hS` — the weighted threshold, of size `O_ρ(n/η³)`.

Conclusion: a single pair `(v₀, v₁)` of dimension-`k` polynomials with
* **correlated agreement**: `(u₀, u₁)` differs from `(v₀, v₁)` on at most `e`
  coordinates, and
* **mutual correlated agreement** (Haböck): on any parameter set where the line stays
  `e`-close to the line of `(v₀, v₁)`, at most `e` parameters see any agreement beyond
  the correlated agreement set. -/
theorem exists_affine_bucket_of_GS_sharp
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hfield : 2 * dY * dX < Fintype.card F)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * sharpGSBound k dY dZ /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ (v₀ v₁ : F[X]) (S' : Finset F), S' ⊆ S ∧ e + 1 < S'.card ∧
      v₀.natDegree < k ∧ v₁.natDegree < k ∧
      ∀ z ∈ S', p z = v₀ + C z * v₁ := by
  -- ### The bucket.
  obtain ⟨S', N, d', Sf, x₀, H, hS'S, hS'card, ⟨f, hNf⟩, hd'1, hSfd', hd'N, hSfZ,
    hirrH, hHdeg, hHd', hHZ, hHZexact, hcount, hper⟩ :=
    exists_bucket_sharp S p Q hQ0 dX dY dZ hQY hQX hQZ hGS hfield k
      (Fintype.card ι - k) e (Fintype.card ι - e - k) hslack hS
  set pc := ringChar F with hpc
  haveI hpcP : Fact pc.Prime := ⟨CharP.char_is_prime F pc⟩
  have hN1 : 1 ≤ N := by
    rw [hNf]
    exact Nat.one_le_pow _ _ hpcP.out.pos
  -- ### The twisted data.
  set κ := k * N with hκ
  set q : F → F[X] := fun z => (p z) ^ N with hq
  set w₀ : ι → F := fun x => (u₀ x) ^ N with hw₀
  set w₁ : ι → F := fun x => (u₁ x) ^ N with hw₁
  have hFrobinj : Function.Injective (fun c : F => c ^ N) := by
    rw [hNf]
    exact pow_char_pow_injective pc f
  have htwist : ∀ a b z : F, (a + z * b) ^ N = a ^ N + z ^ N * b ^ N := by
    intro a b z
    rw [hNf]
    exact add_mul_pow_char_pow pc f a b z
  -- The twisted proximity: the disagreement sets are literally equal.
  have hproxT : ∀ z ∈ S',
      (disagree (fun x => w₀ x + z ^ N * w₁ x) (RSeval dom (q z))).card ≤ e := by
    intro z hz
    have hset : disagree (fun x => w₀ x + z ^ N * w₁ x) (RSeval dom (q z))
        = disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z)) := by
      ext x
      simp only [mem_disagree, RSeval_apply, hq, hw₀, hw₁, eval_pow]
      rw [← htwist]
      constructor
      · intro hne heq
        exact hne (by rw [heq])
      · intro hne heq
        exact hne (hFrobinj heq)
    rw [hset]
    exact hprox z (hS'S hz)
  -- ### The recentered branch and its inputs.
  set R₀ := recenter x₀ Sf with hR₀
  have hqdeg : ∀ z ∈ S', (q z).natDegree ≤ κ := by
    intro z hz
    rw [hq]
    calc ((p z) ^ N).natDegree ≤ N * (p z).natDegree := natDegree_pow_le
      _ ≤ N * k := Nat.mul_le_mul_left _ (Nat.le_of_lt (hpdeg z (hS'S hz)))
      _ = κ := by rw [hκ]; ring
  have hroot : ∀ z ∈ S',
      (R₀.map (mapRingHom (spec z ((q z).eval x₀)))).eval ((q z).comp (X + C x₀)) = 0 := by
    intro z hz
    exact eval_recenter_spec z x₀ _ Sf (q z) (hper z hz).1
  have hxiB : ∀ z ∈ S', spec z ((q z).eval x₀) (xi R₀ (X : F[X][X])) ≠ 0 := by
    intro z hz
    rw [hR₀, xi_recenter, spec_fiberAt, hasseDeriv_one']
    exact (hper z hz).2.1
  have hH0 : ∀ z ∈ S', spec z ((q z).eval x₀) H = 0 := fun z hz => (hper z hz).2.2
  -- ### The counting hypothesis for the bucket.
  have hcountB : (Fintype.card ι - k) *
      sharpFiberCapacity κ d' dZ N H.natDegree (swap F H).natDegree <
        (Fintype.card ι - e - k) * S'.card := by
    simpa [hκ] using hcount
  -- ### The good coordinates.
  have hκ1 : 1 ≤ κ := by
    rw [hκ]
    exact Nat.mul_pos (by omega) hN1
  obtain ⟨I, hIcard, hgood⟩ :
      ∃ I : Finset ι, k < I.card ∧ ∀ x ∈ I, ∀ z ∈ S',
        (q z).eval (dom x) = w₀ x + z ^ N * w₁ x := by
    apply exists_goodCoords_sharp dom w₀ w₁ k κ e N hκ1 x₀ R₀ d' dZ
      (recenter_natDegree_le x₀ Sf hSfd') hd'1
      (fun j i => recenter_coeff_natDegree x₀ Sf j i)
      (fun j i => recenter_coeff_isHeightLE x₀ Sf hSfZ j i)
      S' q hqdeg hproxT hroot hxiB H hH0 hirrH hHdeg
        H.natDegree (swap F H).natDegree le_rfl hHZexact
    simpa using hcountB
  -- ### Untwist the coordinate values.
  have hgood' : ∀ x ∈ I, ∀ z ∈ S', (p z).eval (dom x) = u₀ x + z * u₁ x := by
    intro x hx z hz
    have h1 := hgood x hx z hz
    rw [hq] at h1
    apply hFrobinj
    show ((p z).eval (dom x)) ^ N = (u₀ x + z * u₁ x) ^ N
    rw [htwist, ← eval_pow]
    exact h1
  -- ### Lagrange interpolation through `k` good coordinates.
  obtain ⟨T, hTI, hTcard⟩ := Finset.exists_subset_card_eq (n := k) (s := I) (by omega)
  set v₀ : F[X] := Lagrange.interpolate T dom u₀ with hv₀
  set v₁ : F[X] := Lagrange.interpolate T dom u₁ with hv₁
  have hinj : Set.InjOn dom ↑T := hdom.injOn
  have hdeg₀ : v₀.natDegree < k := by
    have h := Lagrange.degree_interpolate_lt (r := u₀) hinj
    rw [hTcard] at h
    rcases eq_or_ne v₀ 0 with hv | hv
    · simpa [hv] using (show 0 < k by omega)
    · exact (natDegree_lt_iff_degree_lt hv).mpr h
  have hdeg₁ : v₁.natDegree < k := by
    have h := Lagrange.degree_interpolate_lt (r := u₁) hinj
    rw [hTcard] at h
    rcases eq_or_ne v₁ 0 with hv | hv
    · simpa [hv] using (show 0 < k by omega)
    · exact (natDegree_lt_iff_degree_lt hv).mpr h
  have hpz : ∀ z ∈ S', p z = v₀ + C z * v₁ := by
    intro z hz
    have hdegsum : (v₀ + C z * v₁).natDegree < k := by
      refine (natDegree_add_le _ _).trans_lt (max_lt hdeg₀ ?_)
      exact (natDegree_C_mul_le _ _).trans_lt hdeg₁
    refine eq_of_eval_eq_of_degree_le
      (natDegree_le_iff_degree_le.mp (Nat.le_pred_of_lt (hpdeg z (hS'S hz))))
      (natDegree_le_iff_degree_le.mp (Nat.le_pred_of_lt hdegsum))
      (T.image dom) ?_ ?_
    · rw [Finset.card_image_of_injective _ hdom, hTcard]
      rw [Nat.pred_eq_sub_one, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    · intro y hy
      obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hy
      rw [eval_add, eval_mul, eval_C, hv₀, hv₁,
        Lagrange.eval_interpolate_at_node _ hinj hxT,
        Lagrange.eval_interpolate_at_node _ hinj hxT]
      exact hgood' x (hTI hxT) z hz
  exact ⟨v₀, v₁, S', hS'S, by omega, hdeg₀, hdeg₁, hpz⟩

end EndToEnd

/-! ### The eta-cubed size of the sharp factor capacity -/

end JBAgreement
end
-- ===== end of `LvmJBEndToEnd` =====

-- ===== merged from `LvmJBScalarExtension` (GOLF module merge: `LvmJBScalarExtension.lean` is now a stub importing `LvmJBComplete`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBScalarExtension.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Removing the slice field-size condition by scalar extension

The good slice may be selected after embedding the finite base field into a larger
finite extension.  The branch argument then returns an affine bucket over the
extension.  This file records the essential descent step: two distinct parameters
from the base field force the two affine polynomials to have base-field coefficients.
-/

namespace JBAgreement

open Polynomial Finset

section Descent

variable {F K : Type*} [Field F] [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An affine bucket obtained after scalar extension descends to the base field.

The extension bucket is assumed to use parameters in the image of `φ`.  Since it has
at least two elements, two distinct parameters determine `v₀` and `v₁`; solving the
two affine equations expresses them as maps of polynomials over `F`. -/
theorem descend_affine_bucket [DecidableEq F] [DecidableEq K]
    (φ : F →+* K) (hφ : Function.Injective φ)
    (k e : ℕ) (S : Finset F) (p : F → F[X])
    (SK : Finset K) (hSK : SK ⊆ S.image φ) (hSKcard : e + 1 < SK.card)
    (v₀ v₁ : K[X]) (hv₀ : v₀.natDegree < k) (hv₁ : v₁.natDegree < k)
    (hp : ∀ z ∈ S, φ z ∈ SK → (p z).map φ = v₀ + C (φ z) * v₁) :
    ∃ (w₀ w₁ : F[X]) (S' : Finset F), S' ⊆ S ∧ e + 1 < S'.card ∧
      w₀.natDegree < k ∧ w₁.natDegree < k ∧
      ∀ z ∈ S', p z = w₀ + C z * w₁ := by
  set S' : Finset F := S.filter fun z => φ z ∈ SK with hS'def
  have himage : S'.image φ = SK := by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hz).2
    · intro hy
      obtain ⟨z, hzS, hzφ⟩ := Finset.mem_image.mp (hSK hy)
      refine Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzS, ?_⟩, hzφ⟩
      rwa [hzφ]
  have hcard : S'.card = SK.card := by
    rw [← himage, Finset.card_image_of_injective _ hφ]
  have htwo : 1 < S'.card := by omega
  letI : Fintype ↥S' := Fintype.ofFinite ↥S'
  obtain ⟨z₀, z₁, hz01⟩ := Fintype.exists_pair_of_one_lt_card (α := ↥S') (by simpa using htwo)
  have hz10 : (z₁ : F) ≠ (z₀ : F) := by
    intro h
    exact hz01 (Subtype.ext h.symm)
  have hzφ : φ (z₁ : F) - φ (z₀ : F) ≠ 0 := sub_ne_zero.mpr (hφ.ne hz10)
  set w₁ : F[X] := C ((z₁ : F) - z₀)⁻¹ * (p z₁ - p z₀) with hw₁
  set w₀ : F[X] := p z₀ - C (z₀ : F) * w₁ with hw₀
  have hz₀S : (z₀ : F) ∈ S := (Finset.mem_filter.mp z₀.property).1
  have hz₁S : (z₁ : F) ∈ S := (Finset.mem_filter.mp z₁.property).1
  have hz₀K : φ (z₀ : F) ∈ SK := (Finset.mem_filter.mp z₀.property).2
  have hz₁K : φ (z₁ : F) ∈ SK := (Finset.mem_filter.mp z₁.property).2
  have hp₀ := hp z₀ hz₀S hz₀K
  have hp₁ := hp z₁ hz₁S hz₁K
  have hmapw₁ : w₁.map φ = v₁ := by
    rw [hw₁, Polynomial.map_mul, Polynomial.map_C, map_inv₀, Polynomial.map_sub,
      hp₁, hp₀, map_sub]
    have hinv : (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
        (φ (z₁ : F) - φ (z₀ : F)) = 1 := inv_mul_cancel₀ hzφ
    have hCinv : C (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
        C (φ (z₁ : F) - φ (z₀ : F)) = (1 : K[X]) := by
      rw [← C_mul, hinv, C_1]
    calc
      C (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
          (v₀ + C (φ (z₁ : F)) * v₁ - (v₀ + C (φ (z₀ : F)) * v₁)) =
          C (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
            (C (φ (z₁ : F)) - C (φ (z₀ : F))) * v₁ := by ring
      _ =
          (C (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
            C (φ (z₁ : F) - φ (z₀ : F))) * v₁ := by rw [C_sub]
      _ = v₁ := by rw [hCinv, one_mul]
  have hmapw₀ : w₀.map φ = v₀ := by
    rw [hw₀, Polynomial.map_sub, hp₀, Polynomial.map_mul, Polynomial.map_C, hmapw₁]
    ring
  have hw₀deg : w₀.natDegree < k := by
    rw [← natDegree_map_eq_of_injective hφ, hmapw₀]
    exact hv₀
  have hw₁deg : w₁.natDegree < k := by
    rw [← natDegree_map_eq_of_injective hφ, hmapw₁]
    exact hv₁
  refine ⟨w₀, w₁, S', Finset.filter_subset _ _, by simpa [hcard] using hSKcard,
    hw₀deg, hw₁deg, ?_⟩
  intro z hz
  have hzS := (Finset.mem_filter.mp hz).1
  have hzK := (Finset.mem_filter.mp hz).2
  apply Polynomial.map_injective φ hφ
  rw [hp z hzS hzK, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    hmapw₀, hmapw₁]

end Descent

section Lift

variable {F K : Type*} [Field F] [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extend a polynomial family from `F` to `K`, using `invFun` away from the image.
Only values on the image are used by the scalar-extension argument. -/
noncomputable def extendPolyFamily (φ : F →+* K) (p : F → F[X]) : K → K[X] :=
  fun z => (p (Function.invFun φ z)).map φ

@[simp] theorem extendPolyFamily_apply (φ : F →+* K) (hφ : Function.Injective φ)
    (p : F → F[X]) (z : F) :
    extendPolyFamily φ p (φ z) = (p z).map φ := by
  simp [extendPolyFamily, Function.leftInverse_invFun hφ z]

/-- Specializing a trivariate polynomial commutes with scalar extension. -/
theorem eval_map_trivariate (φ : F →+* K) (Q : (F[X][X])[X]) (p : F[X]) (z : F) :
    (((Q.map (mapRingHom (mapRingHom φ))).map
        (mapRingHom (evalRingHom (φ z)))).eval (p.map φ)) =
      (((Q.map (mapRingHom (evalRingHom z))).eval p).map φ) := by
  have hspec :
      (Q.map (mapRingHom (mapRingHom φ))).map
          (mapRingHom (evalRingHom (φ z))) =
        (Q.map (mapRingHom (evalRingHom z))).map (mapRingHom φ) := by
    apply Polynomial.ext
    intro j
    simp only [coeff_map, coe_mapRingHom]
    apply Polynomial.ext
    intro i
    simp [coeff_map, eval_map_apply]
  rw [hspec]
  exact Polynomial.map_mapRingHom_eval_map φ
    (Q.map (mapRingHom (evalRingHom z))) p

variable [DecidableEq F] [Fintype K] [DecidableEq K]

/-- A sharp affine bucket after passing to any sufficiently large finite scalar
extension and descending it to the base field. -/
theorem exists_affine_bucket_of_GS_sharp_scalarExtension
    (φ : F →+* K) (hφ : Function.Injective φ)
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hfieldK : 2 * dY * dX < Fintype.card K)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ (v₀ v₁ : F[X]) (S' : Finset F), S' ⊆ S ∧ e + 1 < S'.card ∧
      v₀.natDegree < k ∧ v₁.natDegree < k ∧
      ∀ z ∈ S', p z = v₀ + C z * v₁ := by
  classical
  set SK : Finset K := S.image φ with hSK
  set pK : K → K[X] := extendPolyFamily φ p with hpK
  set domK : ι → K := fun x => φ (dom x) with hdomK
  set u₀K : ι → K := fun x => φ (u₀ x) with hu₀K
  set u₁K : ι → K := fun x => φ (u₁ x) with hu₁K
  set QK : (K[X][X])[X] := Q.map (mapRingHom (mapRingHom φ)) with hQK
  have hSKcard : SK.card = S.card := by
    rw [hSK, Finset.card_image_of_injective _ hφ]
  have hpK_apply : ∀ z : F, pK (φ z) = (p z).map φ := by
    intro z
    simp [hpK, extendPolyFamily_apply φ hφ]
  have hpdegK : ∀ z ∈ SK, (pK z).natDegree < k := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp (hSK ▸ hz)
    rw [hpK_apply]
    exact lt_of_le_of_lt natDegree_map_le (hpdeg z₀ hz₀)
  have hproxK : ∀ z ∈ SK,
      (disagree (fun x => u₀K x + z * u₁K x) (RSeval domK (pK z))).card ≤ e := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp (hSK ▸ hz)
    have hset : disagree (fun x => u₀K x + φ z₀ * u₁K x)
        (RSeval domK (pK (φ z₀))) =
          disagree (fun x => u₀ x + z₀ * u₁ x) (RSeval dom (p z₀)) := by
      ext x
      simp only [mem_disagree, RSeval_apply, hu₀K, hu₁K, hdomK, hpK_apply]
      rw [eval_map]
      simp only [eval₂_at_apply]
      rw [← φ.map_mul, ← φ.map_add, hφ.ne_iff]
    rw [hset]
    exact hprox z₀ hz₀
  have hQK0 : QK ≠ 0 := by
    intro h0
    have hφ₁ : Function.Injective (mapRingHom φ) := Polynomial.map_injective φ hφ
    have hφ₂ : Function.Injective (mapRingHom (mapRingHom φ)) :=
      Polynomial.map_injective (mapRingHom φ) hφ₁
    rw [hQK] at h0
    apply hQ0
    apply Polynomial.map_injective (mapRingHom (mapRingHom φ)) hφ₂
    simpa using h0
  have hQKY : QK.natDegree ≤ dY := le_trans natDegree_map_le hQY
  have hQKX : ∀ j, (QK.coeff j).natDegree ≤ dX := by
    intro j
    rw [hQK, coeff_map]
    exact le_trans natDegree_map_le (hQX j)
  have hQKZ : ∀ j i, ((QK.coeff j).coeff i).natDegree ≤ dZ := by
    intro j i
    rw [hQK, coeff_map]
    change (((Q.coeff j).map (mapRingHom φ)).coeff i).natDegree ≤ dZ
    rw [coeff_map]
    exact le_trans natDegree_map_le (hQZ j i)
  have hGSK : ∀ z ∈ SK,
      ((QK.map (mapRingHom (evalRingHom z))).eval (pK z)) = 0 := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp (hSK ▸ hz)
    rw [hpK_apply, hQK, eval_map_trivariate]
    simpa using congrArg (Polynomial.map φ) (hGS z₀ hz₀)
  obtain ⟨v₀K, v₁K, SK', hSK'SK, hSK'card, hv₀K, hv₁K, hpKaff⟩ :=
    exists_affine_bucket_of_GS_sharp domK (hφ.comp hdom) u₀K u₁K k e hk SK pK
      hpdegK hproxK QK hQK0 dX dY dZ hQKY hQKX hQKZ hGSK hfieldK hslack
      (by simpa [sharpGSBound, hSKcard] using hS)
  exact descend_affine_bucket φ hφ k e S p SK'
      (Finset.Subset.trans hSK'SK (by simp [hSK]))
      hSK'card v₀K v₁K hv₀K hv₁K (by
        intro z hzS hzK
        rw [← hpK_apply]
        exact hpKaff (φ z) hzK)

/-- **Sharp correlated agreement with no base-field size assumption.**

The proof passes to the canonical finite extension of degree `2*dY*dX+1`, applies
`exists_affine_bucket_of_GS_sharp_scalarExtension`, and descends the affine bucket.
Thus the former good-slice condition is an internal construction, not a hypothesis. -/
theorem exists_affine_bucket_of_GS_sharp_noFieldSize
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ (v₀ v₁ : F[X]) (S' : Finset F), S' ⊆ S ∧ e + 1 < S'.card ∧
      v₀.natDegree < k ∧ v₁.natDegree < k ∧
      ∀ z ∈ S', p z = v₀ + C z * v₁ := by
  let t : ℕ := 2 * dY * dX
  let n : ℕ := t + 1
  let pc := ringChar F
  letI hpcP : Fact pc.Prime := ⟨CharP.char_is_prime F pc⟩
  letI hn0 : NeZero n := ⟨by simp [n]⟩
  let K := FiniteField.Extension F pc n
  letI : Fintype K := Fintype.ofFinite K
  letI : DecidableEq K := Classical.decEq K
  let φ : F →+* K := algebraMap F K
  have hφ : Function.Injective φ := RingHom.injective φ
  have hcardK : Fintype.card K = Fintype.card F ^ n := by
    rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension]
    exact congrArg (· ^ n) Fintype.card_eq_nat_card.symm
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hpowbase : 2 ^ t ≤ Fintype.card F ^ t := Nat.pow_le_pow_left hq2 t
  have hpowstep : Fintype.card F ^ t ≤ Fintype.card F ^ n := by
    change Fintype.card F ^ t ≤ Fintype.card F ^ (t + 1)
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hfieldK : 2 * dY * dX < Fintype.card K := by
    rw [hcardK]
    exact lt_of_lt_of_le (by simpa [t] using t.lt_two_pow_self)
      (le_trans hpowbase hpowstep)
  exact exists_affine_bucket_of_GS_sharp_scalarExtension φ hφ dom hdom u₀ u₁ k e hk
    S p hpdeg hprox Q hQ0 dX dY dZ hQY hQX hQZ hGS hfieldK hslack hS

end Lift

end JBAgreement
end
-- ===== end of `LvmJBScalarExtension` =====

-- ===== merged from `LvmJBGS` (GOLF module merge: `LvmJBGS.lean` is now a stub importing `LvmJBComplete`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBGS.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Guruswami–Sudan: interpolation with multiplicities, and the root property

This file removes the last assumption of the development: it *proves* the
Guruswami–Sudan input consumed by `correlatedAgreement_of_GS_sharp`.

## Multiplicity via the Taylor shift

`vanishesTo m x₀ y₀ Q` says every coefficient of the shifted polynomial
`Q(X + x₀, Y + y₀)` in bidegree `(i, j)` with `i + j < m` vanishes.  Two facts make
this the right definition here:

* it is preserved by *any* coefficient homomorphism (`vanishesTo_map`), so the
  vanishing conditions imposed over `F[Z]` at the moving point `(dom x, u₀x + Z·u₁x)`
  specialise for free to every `z`; and

* it yields the divisibility that drives the root count: if `p(x₀) = y₀`, then
  `(X - x₀)^m ∣ Q(X, p(X))` (`pow_dvd_eval_of_vanishesTo`) — each monomial of the
  shifted polynomial contributes `(X-x₀)^i · (p - y₀)^j` with `i + j ≥ m`.

## Interpolation without linear algebra

Over the *finite* field `F` the existence of a nonzero interpolant needs no rank
argument: the map sending a coefficient vector to its tuple of constraint values is
additive, so as soon as the constraint space is smaller than the coefficient space it
is not injective, and the difference of two colliding vectors assembles into a nonzero
`Q` with all constraints zero (`exists_interpolant`).

The support is the Guruswami–Sudan triangle `{(a,b) : b ≤ dY, a + w·b ≤ D}` — the
weighted-degree shape is what reaches the Johnson radius (a rectangular support loses
a factor `√2`) — and the coefficients are polynomials in `Z` of degree `≤ dZ`.  The
counting hypothesis is the standard one, `(number of constraints) < (number of coefficients)`, in closed
form.

## The root property

`eval_map_eq_zero_of_agreements` : if `p` has degree at most the interpolation
weight `w` and agrees with the specialised
word on more than `D/m` points, then `Q_z(X, p(X)) = 0` — i.e. `(Y - p) ∣ Q_z`.  The
divisibilities `(X - x₀)^m` at the (distinct) agreement points multiply up by pairwise
coprimality and overwhelm the weighted degree `D` of `Q_z(X, p(X))`.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### The Taylor shift and vanishing to order `m` -/

section Shift

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The `X`-shift `X ↦ X + x₀` on `A[X]`. -/
noncomputable def xShift (x₀ : A) : A[X] →+* A[X] :=
  eval₂RingHom (C : A →+* A[X]) (X + C x₀)

@[simp] lemma xShift_apply (x₀ : A) (p : A[X]) : xShift x₀ p = p.comp (X + C x₀) := rfl

@[simp] lemma xShift_zero (p : A[X]) : xShift (0 : A) p = p := by
  have h : xShift (0 : A) = RingHom.id A[X] := by
    refine ringHom_ext ?_ ?_ <;> simp [xShift]
  rw [h]
  rfl

/-- The bivariate Taylor shift `Q(X, Y) ↦ Q(X + x₀, Y + y₀)` on `A[X][Y]`. -/
noncomputable def shift2 (x₀ y₀ : A) (Q : (A[X])[X]) : (A[X])[X] :=
  ((Q.map (xShift x₀)).comp (X + C (C y₀)))

/-- Vanishing to order `m` at `(x₀, y₀)`: all Taylor coefficients of total degree
`< m` vanish. -/
def vanishesTo (m : ℕ) (x₀ y₀ : A) (Q : (A[X])[X]) : Prop :=
  ∀ i j, i + j < m → ((shift2 x₀ y₀ Q).coeff j).coeff i = 0

/-- The Taylor shift is additive. -/
lemma shift2_sub (x₀ y₀ : A) (Q Q' : (A[X])[X]) :
    shift2 x₀ y₀ (Q - Q') = shift2 x₀ y₀ Q - shift2 x₀ y₀ Q' := by
  unfold shift2
  rw [Polynomial.map_sub, sub_comp]

/-- The Taylor shift commutes with coefficient homomorphisms. -/
lemma shift2_map (φ : A →+* B) (x₀ y₀ : A) (Q : (A[X])[X]) :
    shift2 (φ x₀) (φ y₀) (Q.map (mapRingHom φ))
      = (shift2 x₀ y₀ Q).map (mapRingHom φ) := by
  unfold shift2
  rw [map_comp]
  congr 1
  · rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    refine ringHom_ext ?_ ?_
    · intro a
      simp [xShift]
    · simp [xShift]
  · simp

/-- Vanishing specialises along any coefficient homomorphism. -/
lemma vanishesTo_map (φ : A →+* B) {m : ℕ} {x₀ y₀ : A} {Q : (A[X])[X]}
    (h : vanishesTo m x₀ y₀ Q) :
    vanishesTo m (φ x₀) (φ y₀) (Q.map (mapRingHom φ)) := by
  intro i j hij
  rw [shift2_map, coeff_map, coe_mapRingHom, coeff_map, h i j hij, map_zero]

/-- Un-shifting: mapping the Taylor shift by `X ↦ X - x₀` recovers the `Y`-shift
alone. -/
lemma map_xShift_neg_shift2 (x₀ y₀ : A) (Q : (A[X])[X]) :
    (shift2 x₀ y₀ Q).map (xShift (-x₀)) = Q.comp (X + C (C y₀)) := by
  unfold shift2
  rw [map_comp, Polynomial.map_map]
  have hid : (xShift (-x₀)).comp (xShift x₀) = RingHom.id A[X] := by
    refine ringHom_ext ?_ ?_
    · intro a
      simp [xShift]
    · simp [xShift]
  rw [hid, Polynomial.map_id]
  congr 1
  rw [Polynomial.map_add, map_C, Polynomial.map_X]
  congr 1
  simp [xShift]

/-- **The multiplicity divisibility.**  If `Q` vanishes to order `m` at `(x₀, y₀)` and
`p(x₀) = y₀`, then `(X - x₀)^m` divides `Q(X, p(X))`. -/
theorem pow_dvd_eval_of_vanishesTo {m : ℕ} {x₀ y₀ : A} {Q : (A[X])[X]}
    (hV : vanishesTo m x₀ y₀ Q) {p : A[X]} (hp : p.eval x₀ = y₀) :
    ((X : A[X]) - C x₀) ^ m ∣ Q.eval p := by
  set Qh := shift2 x₀ y₀ Q with hQh
  -- Un-shift: `Q.eval p` in terms of the shifted polynomial.
  have hunshift : Q.eval p = ((Qh.map (xShift (-x₀))).eval (p - C y₀)) := by
    rw [hQh, map_xShift_neg_shift2, eval_comp]
    congr 1
    rw [eval_add, eval_C, eval_X, sub_add_cancel]
  rw [hunshift]
  -- Expand as a sum over `Y`-coefficients and divide each term.
  rw [eval_eq_sum_range]
  refine Finset.dvd_sum fun j _ => ?_
  rw [coeff_map]
  have hpy : ((X : A[X]) - C x₀) ∣ (p - C y₀) := by
    rw [dvd_iff_isRoot]
    simp [IsRoot, hp]
  have hshiftpow : ∀ r : ℕ, xShift (-x₀) ((X : A[X]) ^ r)
      = ((X : A[X]) - C x₀) ^ r := by
    intro r
    rw [map_pow, xShift_apply, X_comp, map_neg, ← sub_eq_add_neg]
  rcases lt_or_ge j m with hj | hj
  · -- Low `Y`-degree: the `X`-order of the coefficient makes up the difference.
    have hcoeff : (X : A[X]) ^ (m - j) ∣ Qh.coeff j := by
      rw [X_pow_dvd_iff]
      intro i hi
      exact hV i j (by (clear * - hj hi; omega))
    have h1 : ((X : A[X]) - C x₀) ^ (m - j) ∣ xShift (-x₀) (Qh.coeff j) := by
      have h2 := map_dvd (xShift (-x₀)) hcoeff
      rwa [hshiftpow] at h2
    have h2 : ((X : A[X]) - C x₀) ^ j ∣ (p - C y₀) ^ j := pow_dvd_pow_of_dvd hpy j
    have h3 := mul_dvd_mul h1 h2
    rwa [← pow_add, Nat.sub_add_cancel (le_of_lt hj)] at h3
  · -- High `Y`-degree: the substituted factor alone suffices.
    have h2 : ((X : A[X]) - C x₀) ^ m ∣ (p - C y₀) ^ j := by
      calc ((X : A[X]) - C x₀) ^ m ∣ (p - C y₀) ^ m := pow_dvd_pow_of_dvd hpy m
        _ ∣ (p - C y₀) ^ j := pow_dvd_pow _ hj
    exact Dvd.dvd.mul_left h2 _

end Shift



/-! ### Heights of the shifted polynomial -/

section Heights

variable {F : Type*} [Field F]

/-- The two-layer height system on `F[Z][X][Y]`: every `(Y,X)`-coefficient has
`Z`-degree at most the size. -/
noncomputable def heightSizeSystem₂ (F : Type*) [CommRing F] :
    SizeSystem ((F[X][X])[X]) where
  P W d := ∀ j, IsHeightLE (W.coeff j) d
  mono := fun h hle j => (h j).mono hle
  zero := fun d j => by simp
  one := fun j => by
    rcases eq_or_ne j 0 with rfl | h
    · intro i
      rw [coeff_one]
      split_ifs with h'
      · rcases eq_or_ne i 0 with rfl | hi
        · simp [coeff_one]
        · simp [coeff_one, hi]
      · simp
    · intro i
      simp [coeff_one, h]
  neg := fun h j => by
    rw [coeff_neg]
    exact (h j).neg
  add := fun h₁ h₂ j => by
    rw [coeff_add]
    exact (h₁ j).add (h₂ j)
  mul := fun {g h m m'} h₁ h₂ j => by
    rw [coeff_mul]
    exact IsHeightLE.sum _ _ fun p _ => (h₁ p.1).mul (h₂ p.2)

/-- The `X`-shift by a scalar preserves two-layer heights. -/
theorem heightLE₂_map_xShift {W : (F[X][X])[X]} {d : ℕ} (v : F)
    (hW : ∀ j, IsHeightLE (W.coeff j) d) :
    ∀ j, IsHeightLE ((W.map (xShift (C v))).coeff j) d := by
  intro j
  rw [coeff_map]
  have hx : xShift (C v) = shiftZ v := rfl
  rw [hx]
  exact isHeightLE_shiftZ v (hW j)

/-- Composition with `Y + y₀` (`y₀` of `Z`-degree ≤ 1) raises two-layer heights by the
`Y`-degree. -/
theorem heightLE₂_comp {W : (F[X][X])[X]} {d dY : ℕ} {y₀ : F[X]}
    (hW : ∀ j, IsHeightLE (W.coeff j) d) (hWdeg : W.natDegree ≤ dY)
    (hy : y₀.natDegree ≤ 1) :
    ∀ j, IsHeightLE ((W.comp (X + C (C y₀))).coeff j) (d + dY) := by
  have hbase : (heightSizeSystem₂ F).P ((X : (F[X][X])[X]) + C (C y₀)) 1 := by
    intro j
    rw [coeff_add, coeff_X, coeff_C]
    split_ifs with h1 h2 h2
    · exfalso; omega
    · intro i
      rw [add_zero, coeff_one]
      split_ifs <;> simp
    · intro i
      rw [zero_add, coeff_C]
      split_ifs with h3
      · exact le_trans hy (by norm_num)
      · simp
    · intro i
      simp
  have hsum : (heightSizeSystem₂ F).P (W.comp (X + C (C y₀))) (d + dY) := by
    rw [comp, eval₂_eq_sum_range]
    refine (heightSizeSystem₂ F).sum _ _ fun j hj => ?_
    have hj' : j ≤ dY := by
      have := Finset.mem_range.mp hj
      omega
    have hC : (heightSizeSystem₂ F).P (C (W.coeff j)) d := by
      intro j'
      rw [coeff_C]
      split_ifs with h
      · exact hW j
      · simp
    have hpow : (heightSizeSystem₂ F).P (((X : (F[X][X])[X]) + C (C y₀)) ^ j) (j * 1) :=
      (heightSizeSystem₂ F).pow hbase j
    refine (heightSizeSystem₂ F).mono ((heightSizeSystem₂ F).mul hC hpow) ?_
    omega
  exact hsum

/-- **Heights of the Taylor shift.**  At a scalar `X`-point and a `Z`-degree-1
`Y`-point, the shifted polynomial's coefficients have `Z`-degree at most `dZ + dY`. -/
theorem heightLE₂_shift2 {Q : (F[X][X])[X]} {dY dZ : ℕ} (v : F) {y₀ : F[X]}
    (hQY : Q.natDegree ≤ dY) (hQZ : ∀ j, IsHeightLE (Q.coeff j) dZ)
    (hy : y₀.natDegree ≤ 1) :
    ∀ j, IsHeightLE ((shift2 (C v) y₀ Q).coeff j) (dZ + dY) := by
  unfold shift2
  refine heightLE₂_comp (heightLE₂_map_xShift v hQZ) ?_ hy
  exact le_trans (natDegree_map_le) hQY

end Heights

/-! ### Interpolation -/

section Interpolation

variable {F : Type*} [Field F]
variable {ι : Type*}

/-- The coefficient index for weighted interpolation: the Guruswami–Sudan
triangle `{(b,a) : a + w·b ≤ D}`
thickened by the `Z`-box. -/
abbrev gsIdx (w D dY dZ : ℕ) : Type :=
  (b : Fin (dY + 1)) × (Fin (D + 1 - w * b) × Fin (dZ + 1))

/-- The constraint index: a point, a Taylor bidegree `(i,j)` with `i + j < m`, and a
`Z`-coefficient slot. -/
abbrev gsCon (ι : Type*) (m dY dZ : ℕ) : Type _ :=
  ι × ((j : Fin m) × Fin (m - j)) × Fin (dZ + dY + 1)

/-- Assembling a coefficient vector into a polynomial. -/
noncomputable def gsAssemble (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F) :
    (F[X][X])[X] :=
  ∑ v : gsIdx w D dY dZ,
    monomial (v.1 : ℕ) (monomial (v.2.1 : ℕ) (monomial (v.2.2 : ℕ) (q v)))

/-- Coefficient extraction: the assembly is coefficientwise. -/
theorem gsAssemble_coeff (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F)
    (v : gsIdx w D dY dZ) :
    (((gsAssemble w D dY dZ q).coeff v.1).coeff v.2.1).coeff v.2.2 = q v := by
  unfold gsAssemble
  rw [finsetSum_coeff]
  simp_rw [finsetSum_coeff]
  rw [Finset.sum_eq_single v]
  · simp
  · intro v' _ hne
    by_cases h1 : (v'.1 : ℕ) = (v.1 : ℕ)
    · have hb : v'.1 = v.1 := Fin.ext h1
      obtain ⟨b, a', c'⟩ := v'
      obtain ⟨b₂, a, c⟩ := v
      cases hb
      by_cases h2 : (a' : ℕ) = (a : ℕ)
      · have ha : a' = a := Fin.ext h2
        cases ha
        by_cases h3 : (c' : ℕ) = (c : ℕ)
        · have hc : c' = c := Fin.ext h3
          cases hc
          exact (hne rfl).elim
        · simp [coeff_monomial, h3]
      · simp [coeff_monomial, h2]
    · simp [coeff_monomial, h1]
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- The assembly is subtractive. -/
theorem gsAssemble_sub (w D dY dZ : ℕ) (q q' : gsIdx w D dY dZ → F) :
    gsAssemble w D dY dZ (q - q')
      = gsAssemble w D dY dZ q - gsAssemble w D dY dZ q' := by
  simp [gsAssemble, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

/-- `Y`-degree of the assembly. -/
theorem gsAssemble_natDegree (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F) :
    (gsAssemble w D dY dZ q).natDegree ≤ dY := by
  refine natDegree_sum_le_of_forall_le _ _ fun v _ => ?_
  refine le_trans (natDegree_monomial_le _) ?_
  have := v.1.isLt
  omega

/-- Weighted `X`-degree of the assembly. -/
theorem gsAssemble_coeff_natDegree (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F) (b : ℕ) :
    ((gsAssemble w D dY dZ q).coeff b).natDegree ≤ D - w * b := by
  unfold gsAssemble
  rw [finsetSum_coeff]
  refine natDegree_sum_le_of_forall_le _ _ fun v _ => ?_
  rw [coeff_monomial]
  split_ifs with h
  · refine le_trans (natDegree_monomial_le _) ?_
    have h2 := v.2.1.isLt
    rw [← h]
    (clear * - h2; omega)
  · simp

/-- `Z`-heights of the assembly. -/
theorem gsAssemble_isHeightLE (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F) (b : ℕ) :
    IsHeightLE ((gsAssemble w D dY dZ q).coeff b) dZ := by
  unfold gsAssemble
  rw [finsetSum_coeff]
  intro a
  rw [finsetSum_coeff]
  refine natDegree_sum_le_of_forall_le _ _ fun v _ => ?_
  rw [coeff_monomial]
  split_ifs with h
  · rw [coeff_monomial]
    split_ifs with h'
    · refine le_trans (natDegree_monomial_le _) ?_
      have := v.2.2.isLt
      (clear * - this; omega)
    · simp
  · simp

/-- The moving word point over `F[Z]`. -/
noncomputable def wordZ (u₀ u₁ : ι → F) (x : ι) : F[X] :=
  C (u₀ x) + X * C (u₁ x)

lemma wordZ_natDegree_le (u₀ u₁ : ι → F) (x : ι) : (wordZ u₀ u₁ x).natDegree ≤ 1 := by
  unfold wordZ
  refine le_trans (natDegree_add_le _ _) (max_le (by simp) ?_)
  refine le_trans (natDegree_mul_le) ?_
  simp

lemma wordZ_eval (u₀ u₁ : ι → F) (x : ι) (z : F) :
    (wordZ u₀ u₁ x).eval z = u₀ x + z * u₁ x := by
  unfold wordZ
  simp
  ring

section Finite

variable [Fintype F] [Fintype ι] [DecidableEq ι]

/-- **Existence of the Guruswami–Sudan interpolant.**

Over the finite field `F`, as soon as the constraint count is smaller than the
coefficient count (hypothesis `hcnt`, stated in doubled closed form), there is a
*nonzero* `Q ∈ F[Z][X][Y]` with `Y`-degree ≤ `dY`, weighted `X`-degrees
(`deg_X Q_b ≤ D - k·b`), `Z`-height ≤ `dZ`, vanishing to order `m` at every point
`(dom x, u₀ x + Z·u₁ x)`.

No rank computation: the constraint map is subtractive, and a counting collision
provides the interpolant. -/
theorem exists_interpolant (dom : ι → F) (u₀ u₁ : ι → F) (w m D dY dZ : ℕ)
    (hwdY : w * dY ≤ D)
    (hcnt : Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - w * (dY * (dY + 1))) * (dZ + 1)) :
    ∃ Q : (F[X][X])[X], Q ≠ 0 ∧ Q.natDegree ≤ dY ∧
      (∀ b, (Q.coeff b).natDegree ≤ D - w * b) ∧
      (∀ b, IsHeightLE (Q.coeff b) dZ) ∧
      ∀ x : ι, vanishesTo m (C (dom x)) (wordZ u₀ u₁ x) Q := by
  set φ : (gsIdx w D dY dZ → F) → (gsCon ι m dY dZ → F) := fun q con =>
    (((shift2 (C (dom con.1)) (wordZ u₀ u₁ con.1) (gsAssemble w D dY dZ q)).coeff
        con.2.1.1).coeff con.2.1.2).coeff con.2.2 with hφ
  have hφsub : ∀ q q', φ (q - q') = φ q - φ q' := by
    intro q q'
    funext con
    simp only [hφ, Pi.sub_apply]
    rw [gsAssemble_sub, shift2_sub, coeff_sub, coeff_sub, coeff_sub]
  -- The two cardinalities, in doubled closed form.
  have hIdx2 : 2 * Fintype.card (gsIdx w D dY dZ)
      = ((dY + 1) * (2 * (D + 1)) - w * (dY * (dY + 1))) * (dZ + 1) := by
    have h1 : Fintype.card (gsIdx w D dY dZ)
        = ∑ b : Fin (dY + 1), (D + 1 - w * b) * (dZ + 1) := by
      rw [Fintype.card_sigma]
      exact Finset.sum_congr rfl fun b _ => by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [h1, Fin.sum_univ_eq_sum_range (fun b => (D + 1 - w * b) * (dZ + 1))]
    rw [← Finset.sum_mul]
    have h2 : (∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b))
        + w * (∑ b ∈ Finset.range (dY + 1), b)
        = (dY + 1) * (D + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      have h3 : ∀ b ∈ Finset.range (dY + 1),
          D + 1 - w * b + w * b = D + 1 := by
        intro b hb
        have hb' : b ≤ dY := by
          have := Finset.mem_range.mp hb
          omega
        have : w * b ≤ w * dY := Nat.mul_le_mul_left _ hb'
        omega
      rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h4 : (∑ b ∈ Finset.range (dY + 1), b) * 2 = (dY + 1) * dY :=
      Finset.sum_range_id_mul_two (dY + 1)
    -- Combine.
    have h5 : 2 * (∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b))
        = (dY + 1) * (2 * (D + 1)) - w * (dY * (dY + 1)) := by
      have e1 : 2 * ((∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b))
          + w * (∑ b ∈ Finset.range (dY + 1), b)) =
            2 * ((dY + 1) * (D + 1)) := by
        rw [h2]
      have e2 : 2 * (w * (∑ b ∈ Finset.range (dY + 1), b)) =
          w * (dY * (dY + 1)) := by
        calc 2 * (w * (∑ b ∈ Finset.range (dY + 1), b))
            = w * ((∑ b ∈ Finset.range (dY + 1), b) * 2) := by ring
          _ = w * ((dY + 1) * dY) := by rw [h4]
          _ = w * (dY * (dY + 1)) := by ring
      have e3 : (dY + 1) * (2 * (D + 1)) = 2 * ((dY + 1) * (D + 1)) := by ring
      omega
    calc 2 * ((∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b)) * (dZ + 1))
        = (2 * (∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b))) *
            (dZ + 1) := by ring
      _ = ((dY + 1) * (2 * (D + 1)) - w * (dY * (dY + 1))) *
            (dZ + 1) := by rw [h5]
  have hCon2 : 2 * Fintype.card (gsCon ι m dY dZ)
      = Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1) := by
    have h1 : Fintype.card ((j : Fin m) × Fin (m - j)) = ∑ j ∈ Finset.range m, (m - j) := by
      rw [Fintype.card_sigma]
      have h0 : ∀ j : Fin m, Fintype.card (Fin (m - j)) = m - (j : ℕ) := fun j =>
        Fintype.card_fin _
      rw [Finset.sum_congr rfl (fun j _ => h0 j)]
      exact Fin.sum_univ_eq_sum_range (fun j => m - j) m
    have h2 : (∑ j ∈ Finset.range m, (m - j)) * 2 = m * (m + 1) := by
      have h3 : (∑ j ∈ Finset.range m, (m - j)) = (∑ j ∈ Finset.range m, j) + m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · rw [← Finset.sum_range_reflect]
          have h4 : ∀ j ∈ Finset.range m, m - (m - 1 - j) = j + 1 := by
            intro j hj
            have := Finset.mem_range.mp hj
            omega
          rw [Finset.sum_congr rfl h4, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_range, smul_eq_mul, mul_one]
      have h5 := Finset.sum_range_id_mul_two m
      calc (∑ j ∈ Finset.range m, (m - j)) * 2
          = (∑ j ∈ Finset.range m, j) * 2 + m * 2 := by rw [h3]; ring
        _ = m * (m - 1) + m * 2 := by rw [h5]
        _ = m * (m + 1) := by
            rcases Nat.eq_zero_or_pos m with rfl | hm
            · simp
            · have : m - 1 + 2 = m + 1 := by omega
              calc m * (m - 1) + m * 2 = m * ((m - 1) + 2) := by ring
                _ = m * (m + 1) := by rw [this]
    rw [Fintype.card_prod, Fintype.card_prod, h1, Fintype.card_fin]
    calc 2 * (Fintype.card ι * ((∑ j ∈ Finset.range m, (m - j)) * (dZ + dY + 1)))
        = Fintype.card ι * ((∑ j ∈ Finset.range m, (m - j)) * 2) * (dZ + dY + 1) := by
          ring
      _ = Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1) := by rw [h2]
  have hcards : Fintype.card (gsCon ι m dY dZ) < Fintype.card (gsIdx w D dY dZ) := by
    omega
  -- Non-injectivity over the finite field.
  have hnoninj : ¬ Function.Injective φ := by
    intro hinj
    have h1 := Fintype.card_le_of_injective φ hinj
    rw [Fintype.card_fun, Fintype.card_fun] at h1
    have hF : 1 < Fintype.card F := Fintype.one_lt_card
    have h2 := Nat.pow_lt_pow_right hF hcards
    omega
  obtain ⟨q₁, q₂, hEq, hne⟩ := Function.not_injective_iff.mp hnoninj
  set q : gsIdx w D dY dZ → F := q₁ - q₂ with hqdef
  have hq0 : q ≠ 0 := sub_ne_zero.mpr hne
  have hφq : φ q = 0 := by
    rw [hqdef, hφsub, hEq, sub_self]
  refine ⟨gsAssemble w D dY dZ q, ?_, gsAssemble_natDegree w D dY dZ q,
    gsAssemble_coeff_natDegree w D dY dZ q, gsAssemble_isHeightLE w D dY dZ q, ?_⟩
  · -- Nonzero: a nonzero entry survives as a coefficient.
    intro h0
    apply hq0
    funext v
    have := gsAssemble_coeff w D dY dZ q v
    rw [h0] at this
    simpa using this.symm
  · -- The vanishing conditions.
    intro x i j hij
    set c : F[X] := ((shift2 (C (dom x)) (wordZ u₀ u₁ x)
      (gsAssemble w D dY dZ q)).coeff j).coeff i with hc
    have hdegc : c.natDegree ≤ dZ + dY := by
      rw [hc]
      exact heightLE₂_shift2 (dom x) (gsAssemble_natDegree w D dY dZ q)
        (gsAssemble_isHeightLE w D dY dZ q) (wordZ_natDegree_le u₀ u₁ x) j i
    have hcoeffs : ∀ ℓ, c.coeff ℓ = 0 := by
      intro ℓ
      rcases le_or_gt ℓ (dZ + dY) with hℓ | hℓ
      · have hj : j < m := by omega
        have hi : i < m - j := by omega
        have := congrFun hφq (⟨x, ⟨⟨⟨j, hj⟩, ⟨i, hi⟩⟩, ⟨ℓ, by omega⟩⟩⟩ : gsCon ι m dY dZ)
        simpa [hφ, hc] using this
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    exact Polynomial.ext hcoeffs

end Finite

/-! ### The root property -/

/-- **The Guruswami–Sudan root property.**  If the specialised interpolant vanishes to
order `m` at `(x₀, p(x₀))` for every `x₀` in a set `T` of size `> D/m`, and the
degree of `p` is at most the interpolation weight `w`, then `Q_z(X, p(X)) = 0`. -/
theorem eval_map_eq_zero_of_agreements
    {Q : (F[X][X])[X]} {w m D dY : ℕ}
    (hQY : Q.natDegree ≤ dY) (hwdY : w * dY ≤ D)
    (hQb : ∀ b, (Q.coeff b).natDegree ≤ D - w * b)
    {z : F} {p : F[X]} (hp : p.natDegree ≤ w)
    {T : Finset F}
    (hvan : ∀ x₀ ∈ T, vanishesTo m x₀ (p.eval x₀) (Q.map (mapRingHom (evalRingHom z))))
    (hDT : D < m * T.card) :
    (Q.map (mapRingHom (evalRingHom z))).eval p = 0 := by
  set Qz := Q.map (mapRingHom (evalRingHom z)) with hQz
  set R : F[X] := Qz.eval p with hR
  rw [← not_ne_iff]
  intro hR0
  -- Each agreement point contributes an `m`-fold factor.
  have hdvd1 : ∀ x₀ ∈ T, ((X : F[X]) - C x₀) ^ m ∣ R := by
    intro x₀ hx₀
    exact pow_dvd_eval_of_vanishesTo (hvan x₀ hx₀) rfl
  have hprod : (∏ x₀ ∈ T, ((X : F[X]) - C x₀) ^ m) ∣ R := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd1
    intro a _ b _ hab
    exact (isCoprime_X_sub_C_of_isUnit_sub
      (by simpa using sub_ne_zero.mpr hab)).pow
  -- Degrees.
  have hdegprod : (∏ x₀ ∈ T, ((X : F[X]) - C x₀) ^ m).natDegree = T.card * m := by
    rw [natDegree_prod]
    · have h1 : ∀ x₀ ∈ T, (((X : F[X]) - C x₀) ^ m).natDegree = m := by
        intro x₀ _
        rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul]
    · intro x₀ _
      exact pow_ne_zero _ (X_sub_C_ne_zero x₀)
  have hdegR : R.natDegree ≤ D := by
    rw [hR, eval_eq_sum_range]
    refine natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
    have hbdY : b ≤ dY := by
      have h1 := Finset.mem_range.mp hb
      have h2 : Qz.natDegree ≤ dY := le_trans (natDegree_map_le) hQY
      omega
    refine le_trans (natDegree_mul_le) ?_
    have h3 : (Qz.coeff b).natDegree ≤ D - w * b := by
      rw [hQz, coeff_map]
      exact le_trans (natDegree_map_le) (hQb b)
    have h4 : (p ^ b).natDegree ≤ w * b := by
      rw [natDegree_pow]
      calc b * p.natDegree ≤ b * w := Nat.mul_le_mul_left _ hp
        _ = w * b := Nat.mul_comm _ _
    have h5 : w * b ≤ D := le_trans (Nat.mul_le_mul_left _ hbdY) hwdY
    omega
  have h6 := natDegree_le_of_dvd hprod hR0
  rw [hdegprod] at h6
  have h7 : m * T.card = T.card * m := by ring
  omega

end Interpolation

end JBAgreement
end
-- ===== end of `LvmJBGS` =====

/-!
# The unconditional theorem

`correlatedAgreement_unconditional_sharp_noFieldSize` constructs the
Guruswami–Sudan interpolant, uses the derivative-sensitive ledger, and selects the
good slice after finite scalar extension.  Its only hypotheses are the words, the
per-parameter proximity, and explicitly checkable numeric conditions on
`(m, D, dY, dZ)`:

* `hkdY`, `hcnt` — interpolation at degree cap `k - 1` is solvable (more
  coefficients than constraints);
* `hroot` — the agreement overwhelms the weighted degree (`D < m·(n-e)`);
* `hslack`, `hS` — positivity of the agreement slack and the weighted threshold.

The proof constructs a large enough extension internally and descends its affine
bucket, so there is no base-field size condition.  No real-valued relaxation is
defined in this module.
-/

namespace JBAgreement

open Polynomial Finset

section Unconditional

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Guruswami–Sudan package, for a given family of proximates.**  Here `k`
is the code dimension, so the interpolant is weighted by the degree cap `k - 1`.
It derives the root property at every parameter of `S` and is shared by the
unconditional correlated agreement theorem and the strong mutual variant. -/
theorem exists_gs_for
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (m D dY dZ : ℕ)
    (hkdY : (k - 1) * dY ≤ D)
    (hcnt : Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - (k - 1) * (dY * (dY + 1))) * (dZ + 1))
    (hroot : D < m * (Fintype.card ι - e)) :
    ∃ Q : (F[X][X])[X], Q ≠ 0 ∧ Q.natDegree ≤ dY ∧
      (∀ j, (Q.coeff j).natDegree ≤ D) ∧
      (∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ) ∧
      ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0 := by
  obtain ⟨Q, hQ0, hQY, hQb, hQZ, hQvan⟩ :=
    exists_interpolant dom u₀ u₁ (k - 1) m D dY dZ hkdY hcnt
  refine ⟨Q, hQ0, hQY, fun j => le_trans (hQb j) (Nat.sub_le _ _),
    fun j => hQZ j, ?_⟩
  intro z hz
  set T : Finset F :=
    (univ \ disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).image dom
    with hT
  have hTcard : Fintype.card ι - e ≤ T.card := by
    rw [hT, Finset.card_image_of_injective _ hdom,
      card_sdiff_of_subset (subset_univ _), card_univ]
    have := hprox z hz
    omega
  refine eval_map_eq_zero_of_agreements (m := m) (T := T) hQY hkdY hQb
    (Nat.le_pred_of_lt (hpdeg z hz)) ?_ ?_
  · intro x₀ hx₀
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx₀
    rw [mem_sdiff, mem_disagree, not_not] at hx
    have hagree : (p z).eval (dom x) = u₀ x + z * u₁ x := by
      simpa [RSeval] using hx.2.symm
    have hV := vanishesTo_map (evalRingHom z) (hQvan x)
    rw [show (evalRingHom z) (C (dom x)) = dom x by simp] at hV
    rw [show (evalRingHom z) (wordZ u₀ u₁ x) = (p z).eval (dom x) by
      show (wordZ u₀ u₁ x).eval z = _
      rw [wordZ_eval, hagree]] at hV
    exact hV
  · calc D < m * (Fintype.card ι - e) := hroot
      _ ≤ m * T.card := Nat.mul_le_mul_left _ hTcard

end Unconditional

/-! ### Johnson-regime feasibility -/

section Johnson

set_option maxHeartbeats 1600000 in
/-- **Feasibility of the Guruswami–Sudan parameters in the Johnson regime.**

Under the (√-free, squared) Johnson condition `k·n ≤ (t - 4ηn)²` with
`t ≥ 4ηn`, `ηn ≥ 1`, `η ≤ 1/4`, the parameters
`m = ⌈t/(2ηn)⌉`, `D = m·t - 1`, `dY = ⌊D/k⌋`, `dZ = (m+1)(dY+1)` satisfy every
numeric hypothesis of the interpolation and root steps, with the `η`-sized bounds
`dY ≤ 3n/(4kη)`, `dZ ≤ n/(kη²)`, `D ≤ 3n/(4η)` — the shape that gives the `η³`
threshold. -/
theorem johnson_params_degreeCap (k n t : ℕ) (η : ℝ)
    (hk1 : 1 ≤ k) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hηn : 1 ≤ η * n)
    (ht4 : 4 * η * n ≤ (t : ℝ)) (htn : t ≤ n)
    (hJ : (k : ℝ) * n ≤ ((t : ℝ) - 4 * η * n) ^ 2) :
    ∃ m D dY dZ : ℕ,
      1 ≤ m ∧ k * dY ≤ D ∧ D < m * t ∧ 1 ≤ dY ∧ dZ = (m + 1) * (dY + 1) ∧
      (n * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - k * (dY * (dY + 1))) * (dZ + 1)) ∧
      (dY : ℝ) ≤ 3 * n / (4 * k * η) ∧
      (dZ : ℝ) ≤ n / (k * η ^ 2) ∧
      (D : ℝ) ≤ 3 * n / (4 * η) ∧
      (m : ℝ) ≤ (t : ℝ) / (2 * η * n) + 1 := by
  have hK1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hK0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le one_pos hK1
  have hηn4 : η * (n : ℝ) ≤ 1 / 4 * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hη4 (Nat.cast_nonneg n)
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by linarith only [hηn4, hηn]
  have hN0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le four_pos hN4
  have hT4 : (4 : ℝ) ≤ (t : ℝ) := by linarith only [ht4, hηn]
  have hT0 : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le four_pos hT4
  have hTN : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast htn
  have hsub0 : (0 : ℝ) ≤ (t : ℝ) - 4 * η * n := sub_nonneg.mpr ht4
  have hsN : (t : ℝ) - 4 * η * n ≤ (n : ℝ) := by linarith only [hTN, hηn]
  have hJ' : (k : ℝ) * n ≤ ((t : ℝ) - 4 * η * n) * ((t : ℝ) - 4 * η * n) :=
    hJ.trans_eq (sq _)
  have hKN : (k : ℝ) ≤ (n : ℝ) := by
    have h3 : ((t : ℝ) - 4 * η * n) * ((t : ℝ) - 4 * η * n) ≤ (n : ℝ) * n :=
      mul_le_mul hsN hsN hsub0 hN0.le
    exact le_of_mul_le_mul_right (hJ'.trans h3) hN0
  have h2ηN : (0 : ℝ) < 2 * η * n := by positivity
  -- The multiplicity.
  obtain ⟨m, hm_lb, hm_ub⟩ : ∃ m : ℕ,
      (t : ℝ) / (2 * η * n) ≤ (m : ℝ) ∧ (m : ℝ) < (t : ℝ) / (2 * η * n) + 1 :=
    ⟨⌈(t : ℝ) / (2 * η * n)⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by
    refine le_trans ?_ hm_lb
    rw [le_div_iff₀ h2ηN]
    linarith only [ht4]
  have hm1 : 1 ≤ m := by exact_mod_cast le_trans (by norm_num : (1:ℝ) ≤ 2) hm2
  have ht1 : 1 ≤ t := by exact_mod_cast le_trans (by norm_num : (1:ℝ) ≤ 4) hT4
  have hmt1 : 1 ≤ m * t := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by (clear * - hm1; omega)) (by (clear * - ht1; omega)))
  -- The weighted degree.
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = m * t - 1 := ⟨_, rfl⟩
  have hDlt : D < m * t := by (clear * - hmt1 hDdef; omega)
  have hD1 : (D : ℝ) = (m : ℝ) * t - 1 := by
    rw [hDdef]
    push_cast [Nat.cast_sub hmt1]
    ring
  -- The `Y`-degree.
  obtain ⟨dY, hdYdef⟩ : ∃ dY : ℕ, dY = D / k := ⟨_, rfl⟩
  have hkdY : k * dY ≤ D := by
    rw [hdYdef, mul_comm]
    exact Nat.div_mul_le_self D k
  have hkdY1 : D + 1 ≤ k * (dY + 1) := by
    have h1 := Nat.div_add_mod D k
    have h2 : D % k < k := Nat.mod_lt _ (by (clear * - hk1; omega))
    have h3 : k * (D / k + 1) = k * (D / k) + k := by ring
    rw [hdYdef, h3]
    (clear * - hDdef h1 h2 h3; omega)
  -- `t ≥ k + 4ηn`, hence `D ≥ k` and `dY ≥ 1`.
  have hTk : (k : ℝ) + 4 * η * n ≤ (t : ℝ) := by
    have h1 : (k : ℝ) ≤ (t : ℝ) - 4 * η * n := by
      by_contra hlt
      push_neg at hlt
      have ha : ((t : ℝ) - 4 * η * n) * ((t : ℝ) - 4 * η * n)
          ≤ ((t : ℝ) - 4 * η * n) * n := mul_le_mul_of_nonneg_left hsN hsub0
      have hb : ((t : ℝ) - 4 * η * n) * n < (k : ℝ) * n := mul_lt_mul_of_pos_right hlt hN0
      exact absurd (hJ'.trans ha) (not_le.mpr hb)
    linarith only [h1]
  have hDk : k ≤ D := by
    have h1 : (k : ℝ) + 1 ≤ (m : ℝ) * t := by
      have h1a : 2 * (t : ℝ) ≤ (m : ℝ) * t :=
        mul_le_mul_of_nonneg_right hm2 (le_of_lt hT0)
      linarith only [h1a, hTk, hηn, hK1]
    have h2 : (k : ℝ) ≤ (D : ℝ) := by rw [hD1]; linarith only [h1]
    exact_mod_cast h2
  have hdY1 : 1 ≤ dY := by
    rw [hdYdef]
    exact (Nat.one_le_div_iff (by (clear * - hk1; omega))).mpr hDk
  -- The `Z`-degree.
  obtain ⟨dZ, hdZdef⟩ : ∃ dZ : ℕ, dZ = (m + 1) * (dY + 1) := ⟨_, rfl⟩
  -- ### The counting inequality.
  have hcnt : n * (m * (m + 1)) * (dZ + dY + 1)
      < ((dY + 1) * (2 * (D + 1)) - k * (dY * (dY + 1))) * (dZ + 1) := by
    have hfac : (dY + 1) * (2 * (D + 1)) - k * (dY * (dY + 1))
        = (dY + 1) * (2 * (D + 1) - k * dY) := by
      have h1 : k * (dY * (dY + 1)) = (dY + 1) * (k * dY) := by ring
      rw [h1, ← Nat.mul_sub]
    have hstep : n * m * (m + 2) < (D + 2) * (dY + 1) := by
      have hcast : (k : ℝ) * ((n : ℝ) * m * ((m : ℝ) + 2))
          < (k : ℝ) * (((D : ℝ) + 2) * ((dY : ℝ) + 1)) := by
        have h4m : 2 * (t : ℝ) ≤ 4 * η * n * m := by
          have h5 := hm_lb
          rw [div_le_iff₀ h2ηN] at h5
          linarith only [h5]
        have hkey : ((m : ℝ) + 1) * ((t : ℝ) - 4 * η * n) ≤ (m : ℝ) * t - t := by
          linarith only [h4m, hηn]
        have hsq : (k : ℝ) * n * ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) * t - t) ^ 2 := by
          have h2 : (0 : ℝ) ≤ ((m : ℝ) + 1) * ((t : ℝ) - 4 * η * n) := by positivity
          calc (k : ℝ) * n * ((m : ℝ) + 1) ^ 2
              = ((m : ℝ) + 1) ^ 2 * ((k : ℝ) * n) := by ring
            _ ≤ ((m : ℝ) + 1) ^ 2 * ((t : ℝ) - 4 * η * n) ^ 2 :=
                mul_le_mul_of_nonneg_left hJ (sq_nonneg _)
            _ = (((m : ℝ) + 1) * ((t : ℝ) - 4 * η * n)) ^ 2 := by ring
            _ ≤ ((m : ℝ) * t - t) ^ 2 := pow_le_pow_left₀ h2 hkey 2
        have hmain : (k : ℝ) * n * ((m : ℝ) * ((m : ℝ) + 2)) < ((m : ℝ) * t) ^ 2 := by
          have e4 : (0 : ℝ) < (2 * (m : ℝ) - 1) * (t : ℝ) ^ 2 :=
            mul_pos (by linarith only [hm2]) (by positivity)
          have e5 : (0 : ℝ) < (k : ℝ) * n := by positivity
          linarith only [hsq, e4, e5]
        have hD1' : ((m : ℝ) * t) = (D : ℝ) + 1 := by rw [hD1]; ring
        have hkdY1' : (D : ℝ) + 1 ≤ (k : ℝ) * ((dY : ℝ) + 1) := by exact_mod_cast hkdY1
        have hDpos : (0 : ℝ) ≤ (D : ℝ) + 1 := by positivity
        calc (k : ℝ) * ((n : ℝ) * m * ((m : ℝ) + 2))
            = (k : ℝ) * n * ((m : ℝ) * ((m : ℝ) + 2)) := by ring
          _ < ((m : ℝ) * t) ^ 2 := hmain
          _ = ((D : ℝ) + 1) * ((D : ℝ) + 1) := by rw [hD1']; ring
          _ ≤ ((D : ℝ) + 1) * ((k : ℝ) * ((dY : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left hkdY1' hDpos
          _ ≤ ((D : ℝ) + 2) * ((k : ℝ) * ((dY : ℝ) + 1)) := by
              refine mul_le_mul_of_nonneg_right (by linarith only []) (by positivity)
          _ = (k : ℝ) * (((D : ℝ) + 2) * ((dY : ℝ) + 1)) := by ring
      have h6 := lt_of_mul_lt_mul_left hcast (le_of_lt hK0)
      exact_mod_cast h6
    have hsplit : dZ + dY + 1 = (m + 2) * (dY + 1) := by rw [hdZdef]; ring
    have hZ1 : (m + 1) * (dY + 1) ≤ dZ + 1 := by
      rw [hdZdef]
      exact Nat.le_succ _
    calc n * (m * (m + 1)) * (dZ + dY + 1)
        = (n * m * (m + 2)) * ((m + 1) * (dY + 1)) := by rw [hsplit]; ring
      _ < ((D + 2) * (dY + 1)) * ((m + 1) * (dY + 1)) := by
          have hpos : 0 < (m + 1) * (dY + 1) := by positivity
          exact mul_lt_mul_of_pos_right hstep hpos
      _ ≤ ((dY + 1) * (2 * (D + 1) - k * dY)) * (dZ + 1) := by
          refine Nat.mul_le_mul ?_ hZ1
          calc (D + 2) * (dY + 1) = (dY + 1) * (D + 2) := by ring
            _ ≤ (dY + 1) * (2 * (D + 1) - k * dY) := by
                refine Nat.mul_le_mul_left _ ?_
                (clear * - hDdef hkdY; omega)
      _ = ((dY + 1) * (2 * (D + 1)) - k * (dY * (dY + 1))) * (dZ + 1) := by
          rw [hfac]
  -- ### The size bounds.
  have hmT : (m : ℝ) * t ≤ (t : ℝ) ^ 2 / (2 * η * n) + t := by
    have h2 : (m : ℝ) * t ≤ ((t : ℝ) / (2 * η * n) + 1) * t :=
      mul_le_mul_of_nonneg_right hm_ub.le hT0.le
    calc (m : ℝ) * t ≤ ((t : ℝ) / (2 * η * n) + 1) * t := h2
      _ = (t : ℝ) * t / (2 * η * n) + t := by ring
      _ = (t : ℝ) ^ 2 / (2 * η * n) + t := by ring
  have hDreal : (D : ℝ) ≤ 3 * n / (4 * η) := by
    have h1 : (t : ℝ) ^ 2 / (2 * η * n) ≤ (n : ℝ) / (2 * η) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hq := mul_le_mul_of_nonneg_right (mul_le_mul hTN hTN (le_of_lt hT0) (le_of_lt hN0))
        (by positivity : (0 : ℝ) ≤ 2 * η)
      linarith only [hq]
    have h2 : (t : ℝ) ≤ (n : ℝ) / (4 * η) := by
      rw [le_div_iff₀ (by positivity)]
      have hq := mul_le_mul hTN (by linarith only [hη4] : 4 * η ≤ (1 : ℝ)) (by positivity)
        hN0.le
      linarith only [hq]
    have h3 : (D : ℝ) ≤ (m : ℝ) * t := by rw [hD1]; linarith only []
    calc (D : ℝ) ≤ (m : ℝ) * t := h3
      _ ≤ (t : ℝ) ^ 2 / (2 * η * n) + t := hmT
      _ ≤ (n : ℝ) / (2 * η) + (n : ℝ) / (4 * η) := add_le_add h1 h2
      _ = 3 * n / (4 * η) := by ring
  have hdYreal : (dY : ℝ) ≤ 3 * n / (4 * k * η) := by
    have h1 : (dY : ℝ) ≤ (D : ℝ) / k := by
      rw [hdYdef]
      exact_mod_cast Nat.cast_div_le
    have h2 : (D : ℝ) / k ≤ (3 * n / (4 * η)) / k := by gcongr
    calc (dY : ℝ) ≤ (D : ℝ) / k := h1
      _ ≤ (3 * n / (4 * η)) / k := h2
      _ = 3 * n / (4 * k * η) := by
          field_simp
  have hdZreal : (dZ : ℝ) ≤ (n : ℝ) / (k * η ^ 2) := by
    have hmub : (m : ℝ) + 1 ≤ 1 / η := by
      have h1 : (t : ℝ) / (2 * η * n) ≤ 1 / (2 * η) := by
        rw [div_le_div_iff₀ h2ηN (by positivity)]
        have hq := mul_le_mul_of_nonneg_left hTN (by positivity : (0:ℝ) ≤ 2 * η)
        linarith only [hq]
      have h2 : (2 : ℝ) ≤ 1 / (2 * η) := by
        rw [le_div_iff₀ (by positivity)]
        linarith only [hη4]
      have h3 : (m : ℝ) + 1 < 1 / (2 * η) + 2 := by linarith only [hm_ub, h1]
      have h4 : 1 / (2 * η) + 2 ≤ 1 / (2 * η) + 1 / (2 * η) := by linarith only [h2]
      have h5 : 1 / (2 * η) + 1 / (2 * η) = 1 / η := by
        field_simp
        ring
      linarith only [h3, h4, h5]
    have hdYub : (dY : ℝ) + 1 ≤ (n : ℝ) / (k * η) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) / (4 * k * η) := by
        rw [le_div_iff₀ (by positivity)]
        have hq := mul_le_mul_of_nonneg_left hη4 (Nat.cast_nonneg (α := ℝ) k)
        linarith only [hq, hKN]
      have h2 : 3 * (n : ℝ) / (4 * k * η) + (n : ℝ) / (4 * k * η) = (n : ℝ) / (k * η) := by
        field_simp
        ring
      linarith only [hdYreal, h1, h2]
    have hcast : (dZ : ℝ) = ((m : ℝ) + 1) * ((dY : ℝ) + 1) := by
      rw [hdZdef]
      push_cast
      ring
    have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have hdY0 : (0 : ℝ) ≤ (dY : ℝ) + 1 := by positivity
    calc (dZ : ℝ) = ((m : ℝ) + 1) * ((dY : ℝ) + 1) := hcast
      _ ≤ (1 / η) * ((n : ℝ) / (k * η)) := by
          refine mul_le_mul hmub hdYub hdY0 (by positivity)
      _ = (n : ℝ) / (k * η ^ 2) := by
          field_simp
  exact ⟨m, D, dY, dZ, hm1, hkdY, hDlt, hdY1, hdZdef, hcnt, hdYreal, hdZreal, hDreal,
    le_of_lt hm_ub⟩

end Johnson

/-- The explicit `|S|`-threshold of the Johnson-regime theorem.  The
interpolation bounds use the degree cap `w = k - 1`, while the weighted selector
and agreement slack use the code dimension `k`.  The incidence term contains
one `dY·dZ` factor, not the old uniform-bucket `dY²·dZ` factor. -/
noncomputable def johnsonThreshold (k n e : ℕ) (η : ℝ) : ℝ :=
  let w := k - 1
  (3 * n / (4 * w * η)) * ((e : ℝ) + 2) +
    (n - k : ℕ) * (4 * k * (3 * n / (4 * w * η) * (n / (w * η ^ 2)))
      + 3 * n / (4 * w * η)) / ((n - e - k : ℕ) : ℝ)
    + n / (w * η ^ 2) + 3 * (3 * n / (4 * w * η) * (n / (w * η ^ 2))) + 1

section Final

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1600000 in
/-- **The Johnson numeric package.**  From the real-parameter Johnson hypotheses and
the threshold bound, all sharp `ℕ`-side conditions (with `n` the domain size and
`cS` the parameter-set size).  Shared by the plain and strong mutual variants. -/
theorem johnson_numeric (k n e cS : ℕ) (η : ℝ)
    (hk2 : 2 ≤ k) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hηn : 1 ≤ η * n)
    (ht4 : 4 * η * n ≤ ((n - e : ℕ) : ℝ))
    (hJ : ((k - 1 : ℕ) : ℝ) * n ≤
      (((n - e : ℕ) : ℝ) - 4 * η * n) ^ 2)
    (hS : johnsonThreshold k n e η ≤ (cS : ℝ)) :
    ∃ m D dY dZ : ℕ,
      (k - 1) * dY ≤ D ∧
      (n * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - (k - 1) * (dY * (dY + 1))) *
          (dZ + 1)) ∧
      D < m * (n - e) ∧ 1 ≤ n - e - k ∧
      dY * (e + 2) + (n - k) * (4 * k * (dY * dZ) + dY) / (n - e - k) +
        dZ + 3 * (dY * dZ) < cS := by
  -- Notation.
  let w := k - 1
  have hw1 : 1 ≤ w := by simp [w]; (clear * - hk2; omega)
  have htn : n - e ≤ n := Nat.sub_le _ _
  -- The Guruswami–Sudan parameters.
  obtain ⟨m, D, dY, dZ, hm1, hkdY, hDlt, hdY1, hdZdef, hcnt, hdYreal, hdZreal, hDreal, -⟩ :=
    johnson_params_degreeCap w n (n - e) η hw1 hη hη4 hηn ht4 htn
      (by simpa [w] using hJ)
  -- Real abbreviations and positivity.
  have hW1 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw1
  have hW0 : (0 : ℝ) < (w : ℝ) := lt_of_lt_of_le one_pos hW1
  have hηn4 : η * (n : ℝ) ≤ 1 / 4 * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hη4 (Nat.cast_nonneg n)
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by linarith only [hηn4, hηn]
  have hN0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le four_pos hN4
  have hT4 : (4 : ℝ) ≤ ((n - e : ℕ) : ℝ) := by linarith only [ht4, hηn]
  -- `n - e ≥ k + 4`, so `s ≥ 4`.
  have hsub0 : (0 : ℝ) ≤ ((n - e : ℕ) : ℝ) - 4 * η * (n) := sub_nonneg.mpr ht4
  have hTN' : ((n - e : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast htn
  have hsN : ((n - e : ℕ) : ℝ) - 4 * η * (n) ≤ (n : ℝ) := by linarith only [hTN', hηn]
  have hJ' : ((w : ℕ) : ℝ) * n ≤
      (((n - e : ℕ) : ℝ) - 4 * η * n) * (((n - e : ℕ) : ℝ) - 4 * η * n) :=
    hJ.trans_eq (sq _)
  have hWN : (w : ℝ) ≤ (n : ℝ) := by
    have h3 : (((n - e : ℕ) : ℝ) - 4 * η * (n)) * (((n - e : ℕ) : ℝ) - 4 * η * (n))
        ≤ (n : ℝ) * n := mul_le_mul hsN hsN hsub0 hN0.le
    exact le_of_mul_le_mul_right (hJ'.trans h3) hN0
  have hTw : (w : ℝ) + 4 * η * n ≤ ((n - e : ℕ) : ℝ) := by
    have h1 : (w : ℝ) ≤ ((n - e : ℕ) : ℝ) - 4 * η * n := by
      by_contra hlt
      push_neg at hlt
      have ha : (((n - e : ℕ) : ℝ) - 4 * η * n) * (((n - e : ℕ) : ℝ) - 4 * η * n)
          ≤ (((n - e : ℕ) : ℝ) - 4 * η * n) * n := mul_le_mul_of_nonneg_left hsN hsub0
      have hb : (((n - e : ℕ) : ℝ) - 4 * η * n) * n < (w : ℝ) * n :=
        mul_lt_mul_of_pos_right hlt hN0
      exact absurd (hJ'.trans ha) (not_le.mpr hb)
    linarith only [h1]
  have hw4 : w + 4 ≤ n - e := by
    have h1 : (w : ℝ) + 4 ≤ ((n - e : ℕ) : ℝ) := by linarith only [hTw, hηn]
    exact_mod_cast h1
  set s : ℕ := n - e - k with hsdef
  have hs1 : 3 ≤ s := by simp [w] at hw4; (clear * - hk2 hw1 hw4; omega)
  have hsR : (s : ℝ) = ((n - e : ℕ) : ℝ) - k := by
    rw [hsdef]
    push_cast [Nat.cast_sub (by (clear * - hw1 hw4 hs1; omega) : k ≤ n - e)]
    ring
  have hs0 : (0 : ℝ) < (s : ℝ) := by
    have : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    linarith only [this]
  -- The real bounds on the weighted threshold.
  have hY0 : (0 : ℝ) ≤ 3 * (n : ℝ) / (4 * w * η) := by positivity
  have hZ0 : (0 : ℝ) ≤ (n : ℝ) / (w * η ^ 2) := by positivity
  have hdY0 : (0 : ℝ) ≤ (dY : ℝ) := Nat.cast_nonneg _
  have hdZ0 : (0 : ℝ) ≤ (dZ : ℝ) := Nat.cast_nonneg _
  have hYZ : (dY : ℝ) * dZ ≤ 3 * (n : ℝ) / (4 * w * η)
        * ((n : ℝ) / (w * η ^ 2)) :=
    mul_le_mul hdYreal hdZreal hdZ0 hY0
  have hCap : ((4 * k * (dY * dZ) + dY : ℕ) : ℝ) ≤
      4 * k * (3 * (n : ℝ) / (4 * w * η)
        * ((n : ℝ) / (w * η ^ 2))) + 3 * (n : ℝ) / (4 * w * η) := by
    push_cast
    have hk : (0 : ℝ) ≤ 4 * k := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left hYZ hk) hdYreal
  -- The real threshold dominates the exact natural weighted threshold.
  have hSnat : dY * (e + 2) + (n - k) * (4 * k * (dY * dZ) + dY) / s +
      dZ + 3 * (dY * dZ) < cS := by
    have hchain : ((dY * (e + 2) + (n - k) * (4 * k * (dY * dZ) + dY) / s +
          dZ + 3 * (dY * dZ) : ℕ) : ℝ) + 1
        ≤ johnsonThreshold k (n) e η := by
      have hbase : (dY : ℝ) * ((e : ℝ) + 2) ≤
          (3 * (n : ℝ) / (4 * w * η)) * ((e : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hdYreal (by positivity)
      have hdiv : ((((n - k) * (4 * k * (dY * dZ) + dY)) / s : ℕ) : ℝ) ≤
          ((n - k : ℕ) : ℝ) * (4 * k * (3 * (n : ℝ) / (4 * w * η)
            * ((n : ℝ) / (w * η ^ 2))) + 3 * (n : ℝ) / (4 * w * η)) /
              (s : ℝ) := by
        calc ((((n - k) * (4 * k * (dY * dZ) + dY)) / s : ℕ) : ℝ)
            ≤ ((((n - k) * (4 * k * (dY * dZ) + dY) : ℕ) : ℝ) / (s : ℝ)) :=
              Nat.cast_div_le
          _ ≤ ((n - k : ℕ) : ℝ) * (4 * k * (3 * (n : ℝ) / (4 * w * η)
              * ((n : ℝ) / (w * η ^ 2))) + 3 * (n : ℝ) / (4 * w * η)) /
                (s : ℝ) := by
            push_cast
            gcongr
      have htail : (dZ : ℝ) + 3 * ((dY : ℝ) * dZ) ≤
          (n : ℝ) / (w * η ^ 2) + 3 * (3 * (n : ℝ) / (4 * w * η)
            * ((n : ℝ) / (w * η ^ 2))) := by linarith only [hdZreal, hYZ]
      rw [johnsonThreshold]
      push_cast
      rw [← hsdef]
      linarith only [hbase, hdiv, htail]
    have h7 : ((dY * (e + 2) + (n - k) * (4 * k * (dY * dZ) + dY) / s +
        dZ + 3 * (dY * dZ) : ℕ) : ℝ) < (cS : ℝ) := by
      linarith only [hchain, hS]
    exact_mod_cast h7
  -- Conclude.
  have hroot : D < m * (n - e) := hDlt
  exact ⟨m, D, dY, dZ, by simpa [w] using hkdY,
    by simpa [w] using hcnt, hroot, by (clear * - hs1; omega), by simpa [hsdef] using hSnat⟩

end Final

end JBAgreement
