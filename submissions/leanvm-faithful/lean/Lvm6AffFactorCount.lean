-- lvm6 (WP M1): taken from season 1's branch lvm2/AC-THM (858ab301), files LvmMcaAff* renamed Lvm6Aff*.
-- Vendored for lvm2 (WP AC-THM) from leanEthereum/leanVM
-- `formal/lean_vm/LeanVM/Protocol/ToArkLib/Whir/AffineCombinerFactorCount.lean` @ f5f3672 (Apache License 2.0, see
-- `LICENSE-leanVM`). Changed: module system stripped (`module`, `public import`, `@[expose] public section`); imports
-- renamed `AffineCombiner*` -> `Lvm6Aff*`; imports `Lvm6AffIncid`; new section `Surface` (`chartA_zero_eq_aeval`,
-- `chartA_zero_one_eq_pderiv`, `chartA_zero_zero_support`); in the proof of `card_factorPairs_le` (statement
-- unchanged) the incidence step uses `Incid.card_le_of_cuts_of_rigid`, with two-point rigidity from
-- `persistent_of_two_points`, instead of ArkLib's `MvPolynomial.card_le_of_agreement_off_excluded_of_hypersurface`
-- and `finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero`; nothing else.
/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFactorCount

  The count of non-persistent pairs on one factor of the interpolant, `[CWYZ26]`,
  Claims 4.8 and 4.9: at most `4 d² e² h³ (n / (A - B))²`. Candidate for ArkLib.
-/


import Lvm6AffFactor
import Lvm6AffIncid

/-!
# Counting the non-persistent pairs of one factor

See `AffineCombinerFactor` for the setting. This file adds:

* `aeval_chartCut_chartPoint`: at the chart point of a counted triple, the cut at `x` is
  `S^(2ed-1) (P(x) - f(x) - (α + β x) g(x))`, so it vanishes exactly at the agreement points.
* `persistent_of_two_points`: if two distinct points off the separant satisfy the same
  `B + 1` cuts, and one of them is the chart point of a counted triple, that triple is
  persistent. The second point gives a nonzero solution over `k` of the linear system of the
  `B + 1` agreement equations in `(a, b, P̂)`, hence one over `L`, whose difference
  `H(x) = (Δa + Δb x) g(x)` is the persistence certificate.
* `card_factorPairs_le`: the count.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial Polynomial.UniversalHenselNumerator

section

section Persist

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {ι : Type*}
  (dom : ι ↪ F) (f g : ι → L) (R : MvPolynomial (Fin 3) L) (e d h : ℕ)
  {k : Type*} [Field k] [Algebra (RatFunc L) k] [Algebra L k] [IsScalarTower L (RatFunc L) k]

/-! ## The cuts at a counted triple -/

/-- **Cuts at a counted triple**: `cut_x(y) = S(y)^(2ed-1) (P(x) - f(x) - (α + β x) g(x))`. -/
theorem aeval_chartCut_chartPoint {p κ : ℕ} [Fact p.Prime] [CharP k p] (he : e = p ^ κ)
    (hR : ∀ m ∈ R.support, m 1 + m 2 ≤ h) (hh : 1 ≤ h) {α β : F} {α' β' : L} {P : L[X]}
    (hP : P.natDegree ≤ d) (hα : α' ^ e = algebraMap F L α) (hβ : β' ^ e = algebraMap F L β)
    (hroot : MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R = 0)
    (hs : MvPolynomial.aeval (chartPoint (k := k) e α' β' P) (chartA R 0 1) ≠ 0) (x : ι) :
    MvPolynomial.aeval (chartPoint (k := k) e α' β' P) (chartCut dom f g R e d h x) =
      MvPolynomial.aeval (chartPoint (k := k) e α' β' P) (chartA R 0 1) ^ (2 * e * d - 1) *
        algebraMap L k (P.eval (pt dom x) - f x - (linL α β).eval (pt dom x) * g x) := by
  have he1 : 1 ≤ e := by
    rw [he]; exact Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  rw [aeval_chartCut dom f g R e d h _ hs he1, hatP_eq R e d h he hR hh hP hroot hs]
  congr 1
  have ha : (chartPoint (k := k) e α' β' P 0 - chartPoint (k := k) e α' β' P 1 *
      algebraMap (RatFunc L) k RatFunc.X) ^ e = algebraMap L k (algebraMap F L α) := by
    have h0 : chartPoint (k := k) e α' β' P 0 - chartPoint (k := k) e α' β' P 1 *
        algebraMap (RatFunc L) k RatFunc.X = algebraMap L k α' := by simp only [chartPoint,
            eval_map_algebraMap, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
            add_sub_cancel_right]
    rw [h0, ← map_pow, hα]
  have hb : chartPoint (k := k) e α' β' P 1 ^ e = algebraMap L k (algebraMap F L β) := by
    rw [show chartPoint (k := k) e α' β' P 1 = algebraMap L k β' by simp only [chartPoint,
        eval_map_algebraMap, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero], ← map_pow,
      hβ]
  rw [ha, hb]
  simp only [eval_map_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval, eval_linL, map_sub,
      map_mul, map_add, Polynomial.eval_map_algebraMap]

/-! ## Persistence on rich components -/

omit [Algebra L k] [IsScalarTower L (RatFunc L) k] in
/-- `P̂_z` has degree at most `d`. -/
theorem natDegree_hatP_le (z : Fin 3 → k) : (hatP R e d h z).natDegree ≤ d := by
  refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
  refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans ?_)
  rw [natDegree_X_sub_C, mul_one]
  exact (mem_Icc.mp hj).2

omit [Algebra L k] [IsScalarTower L (RatFunc L) k] in
/-- `P̂_z(T₀^e) = z₂`. -/
theorem eval_hatP_center (z : Fin 3 → k) :
    (hatP R e d h z).eval (algebraMap (RatFunc L) k RatFunc.X ^ e) = z 2 := by
  rw [hatP, eval_add, eval_C, eval_finsetSum, add_eq_left]
  refine sum_eq_zero fun j hj ↦ ?_
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self]
  rw [zero_pow (by have := (mem_Icc.mp hj).1; omega), mul_zero]

/-- **Persistence from a second point**: if two distinct points off the separant satisfy the same
`B + 1` cuts, and one is the chart point of a counted triple, that triple is persistent
([CWYZ26, Claim 4.8], case `c > B`). -/
theorem persistent_of_two_points [Fintype ι] [DecidableEq ι] {p κ : ℕ} [Fact p.Prime] [CharP k p]
    (he : e = p ^ κ) (hR : ∀ m ∈ R.support, m 1 + m 2 ≤ h) (hh : 1 ≤ h) {B : ℕ} (hdB : d + 1 < B)
    {α β : F} {α' β' : L} {P : L[X]} (hP : P.natDegree ≤ d)
    (hα : α' ^ e = algebraMap F L α) (hβ : β' ^ e = algebraMap F L β)
    (hroot : MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R = 0)
    (hs0 : MvPolynomial.aeval (chartPoint (k := k) e α' β' P) (chartA R 0 1) ≠ 0)
    (z₁ : Fin 3 → k) (hs1 : MvPolynomial.aeval z₁ (chartA R 0 1) ≠ 0)
    (hne : z₁ ≠ chartPoint (k := k) e α' β' P) (Cs : Finset ι) (hC : B + 1 ≤ Cs.card)
    (hcut0 : ∀ x ∈ Cs, MvPolynomial.aeval (chartPoint (k := k) e α' β' P)
      (chartCut dom f g R e d h x) = 0)
    (hcut1 : ∀ x ∈ Cs, MvPolynomial.aeval z₁ (chartCut dom f g R e d h x) = 0) :
    IsPersistent dom f g d B α β P := by
  classical
  set z₀ := chartPoint (k := k) e α' β' P with hz₀
  set T := algebraMap (RatFunc L) k RatFunc.X
  have he1 : 1 ≤ e := by rw [he]; exact Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  -- The agreement equations of `Φ(z) = ((z₀ - z₁ T)^e, z₁^e, P̂_z)` on `Cs`.
  have hΦ : ∀ z : Fin 3 → k, MvPolynomial.aeval z (chartA R 0 1) ≠ 0 →
      (∀ x ∈ Cs, MvPolynomial.aeval z (chartCut dom f g R e d h x) = 0) →
      ∀ x ∈ Cs, (hatP R e d h z).eval (algebraMap L k (pt dom x)) =
        algebraMap L k (f x) + ((z 0 - z 1 * T) ^ e + z 1 ^ e * algebraMap L k (pt dom x)) *
          algebraMap L k (g x) := by
    intro z hz hcut x hx
    have := hcut x hx
    rw [aeval_chartCut dom f g R e d h z hz he1] at this
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hz)
    linear_combination this
  have h0 := hΦ z₀ hs0 hcut0
  have h1 := hΦ z₁ hs1 hcut1
  -- The triple agrees on `Cs`.
  have hagree : Cs ⊆ agreeL dom f g P α β := by
    intro x hx
    have := hcut0 x hx
    rw [aeval_chartCut_chartPoint dom f g R e d h he hR hh hP hα hβ hroot hs0] at this
    have := (map_eq_zero_iff _ (algebraMap L k).injective).mp
      ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hs0))
    rw [mem_agreeL]
    linear_combination this
  -- `Φ(z₁) ≠ Φ(z₀)`.
  have hfrob : ∀ u v : k, u ^ e = v ^ e → u = v := by
    intro u v huv
    have : (u - v) ^ e = 0 := by rw [he, sub_pow_char_pow, ← he, huv, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by omega) |>.mp this)
  set Δa := (z₁ 0 - z₁ 1 * T) ^ e - (z₀ 0 - z₀ 1 * T) ^ e
  set Δb := z₁ 1 ^ e - z₀ 1 ^ e
  set ΔP := hatP R e d h z₁ - hatP R e d h z₀
  have hΔ : ¬ (Δa = 0 ∧ Δb = 0 ∧ ΔP = 0) := by
    rintro ⟨ha, hb, hP'⟩
    apply hne
    have e1 : z₁ 1 = z₀ 1 := hfrob _ _ (sub_eq_zero.mp hb)
    have e0 : z₁ 0 = z₀ 0 := by
      have := hfrob _ _ (sub_eq_zero.mp ha)
      rw [e1] at this
      exact sub_left_injective this
    have e2 : z₁ 2 = z₀ 2 := by
      rw [← eval_hatP_center R e d h z₁, ← eval_hatP_center R e d h z₀, sub_eq_zero.mp hP']
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
  have hΔdeg : ΔP.natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le (natDegree_hatP_le R e d h _) (natDegree_hatP_le R e d h _))
  have hΔeq : ∀ x ∈ Cs, ΔP.eval (algebraMap L k (pt dom x)) =
      (Δa + Δb * algebraMap L k (pt dom x)) * algebraMap L k (g x) := by
    intro x hx
    simp only [ΔP, eval_sub, h0 x hx, h1 x hx, Δa, Δb]
    ring
  -- The linear system over `L`, with a nonzero solution over `k`.
  let M : Matrix Cs (Fin 2 ⊕ Fin (d + 1)) L := Matrix.of fun x ↦
    Sum.elim ![-g x, -(g x * pt dom x)] fun i ↦ pt dom x ^ (i : ℕ)
  let v : Fin 2 ⊕ Fin (d + 1) → k := Sum.elim ![Δa, Δb] fun i ↦ ΔP.coeff i
  have hevalΔ : ∀ y : k, ΔP.eval y = ∑ i : Fin (d + 1), ΔP.coeff i * y ^ (i : ℕ) := by
    intro y
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hΔdeg), Fin.sum_univ_eq_sum_range
      (fun i ↦ ΔP.coeff i * y ^ i)]
  have hMv : (M.map (algebraMap L k)).mulVec v = 0 := by
    funext x
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, M, v, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_neg, map_mul, map_pow, Pi.zero_apply]
    have := hΔeq x x.2
    rw [hevalΔ] at this
    have hsum : ∑ i : Fin (d + 1), algebraMap L k (pt dom x) ^ (i : ℕ) * ΔP.coeff i =
        ∑ i : Fin (d + 1), ΔP.coeff i * algebraMap L k (pt dom x) ^ (i : ℕ) :=
      sum_congr rfl fun i _ ↦ mul_comm _ _
    linear_combination this + hsum
  have hv : v ≠ 0 := by
    intro hv0
    apply hΔ
    have ha : Δa = 0 := by simpa only [Fin.isValue, Sum.elim_inl, Matrix.cons_val_zero,
        Pi.zero_apply, v] using congrFun hv0 (Sum.inl 0)
    have hb : Δb = 0 := by simpa only [Fin.isValue, Sum.elim_inl, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Pi.zero_apply, v] using congrFun hv0 (Sum.inl 1)
    refine ⟨ha, hb, Polynomial.ext fun i ↦ ?_⟩
    rw [coeff_zero]
    by_cases hi : i ≤ d
    · simpa only [Sum.elim_inr, Pi.zero_apply, v] using congrFun hv0 (Sum.inr ⟨i,
        Nat.lt_succ_of_le hi⟩)
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  obtain ⟨w, hw, hMw⟩ := exists_ne_zero_mulVec_of_map M v hv hMv
  -- The persistence certificate.
  set Lp : L[X] := C (w (Sum.inl 0)) + C (w (Sum.inl 1)) * X
  set H : L[X] := ∑ i : Fin (d + 1), C (w (Sum.inr i)) * X ^ (i : ℕ)
  have hHdeg : H.natDegree ≤ d := natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (natDegree_C_mul_le _ _).trans (by simpa only [natDegree_pow, natDegree_X,
        mul_one] using Nat.lt_succ_iff.mp i.2)
  have hLdeg : Lp.natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
  have hHeq : ∀ x ∈ Cs, H.eval (pt dom x) = g x * Lp.eval (pt dom x) := by
    intro x hx
    have := congrFun hMw ⟨x, hx⟩
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, M,
      Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.zero_apply] at this
    simp only [H, Lp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_add]
    have hsum : ∑ i : Fin (d + 1), w (Sum.inr i) * pt dom x ^ (i : ℕ) =
        ∑ i : Fin (d + 1), pt dom x ^ (i : ℕ) * w (Sum.inr i) :=
      sum_congr rfl fun i _ ↦ mul_comm _ _
    linear_combination this + hsum
  have hLp : Lp ≠ 0 := by
    intro hL0
    apply hw
    have hw0 : w (Sum.inl 0) = 0 := by
      simpa only [Fin.isValue, coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, mul_zero,
        add_zero, coeff_zero, Lp] using congrArg (coeff · 0) hL0
    have hw1 : w (Sum.inl 1) = 0 := by
      simpa only [Fin.isValue, coeff_add, coeff_C_succ, coeff_mul_X, coeff_C_zero, zero_add,
        coeff_zero, Lp] using congrArg (coeff · 1) hL0
    have hH0 : H = 0 := by
      by_contra hH
      have := card_le_natDegree_of_eval_eq_zero (pt_injective dom) hH Cs fun x hx ↦ by
        rw [hHeq x hx, hL0, eval_zero, mul_zero]
      omega
    funext c
    rcases c with c | i
    · fin_cases c
      · exact hw0
      · exact hw1
    · have := congrArg (coeff · (i : ℕ)) hH0
      simp only [H, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
      rw [sum_eq_single i (fun j _ hji ↦ by
        simp only [ite_eq_right_iff]
        exact fun h ↦ absurd (Fin.ext h.symm) hji) (by simp)] at this
      simpa only [Pi.zero_apply, ↓reduceIte] using this
  -- `I`: the points of `Cs` off the root of `Lp`.
  refine ⟨Cs.filter fun x ↦ Lp.eval (pt dom x) ≠ 0, H, Lp, (filter_subset _ _).trans hagree, ?_,
    hHdeg, hLp, hLdeg, fun x hx ↦ ?_⟩
  · have hroots := card_le_natDegree_of_eval_eq_zero (pt_injective dom) hLp
      (Cs.filter fun x ↦ Lp.eval (pt dom x) = 0) fun x hx ↦ (mem_filter.mp hx).2
    have hsplit : (Cs.filter fun x ↦ Lp.eval (pt dom x) = 0).card +
        (Cs.filter fun x ↦ Lp.eval (pt dom x) ≠ 0).card = Cs.card :=
      card_filter_add_card_filter_not _
    omega
  · obtain ⟨hxC, hx0⟩ := mem_filter.mp hx
    exact ⟨hx0, hHeq x hxC⟩

end Persist

/-! ## The surface of the chart (lvm2)

Added for lvm2: the facts that `card_factorPairs_le` needs to apply `Incid.card_le_of_cuts_of_rigid`
in place of ArkLib's `card_le_of_agreement_off_excluded_of_hypersurface`. The surface
`A_{0,0} = R(T₀, Y, Z)` does not involve `V`, and the separant is its `Z`-derivative. -/

section Surface

variable {L : Type*} [Field L]

/-- `A_{0,0} = R(T₀, Y, Z)` and `A_{0,1} = ∂_Z R(T₀, Y, Z)`, as polynomials of the chart ring. -/
theorem chartA_zero_eq_aeval (R : MvPolynomial (Fin 3) L) :
    chartA R 0 0 = MvPolynomial.aeval
        ![MvPolynomial.C RatFunc.X, MvPolynomial.X 0, MvPolynomial.X 2] R ∧
      chartA R 0 1 = MvPolynomial.aeval
        ![MvPolynomial.C RatFunc.X, MvPolynomial.X 0, MvPolynomial.X 2] (MvPolynomial.pderiv 2 R) := by
  set c : Fin 3 → ChartRing L :=
    ![MvPolynomial.C RatFunc.X, MvPolynomial.X 0, MvPolynomial.X 2]
  have hW : (chartRs R).map (evalRingHom 0) = MvPolynomial.aeval ![C (c 0), C (c 1), C (c 2) + X] R := by
    rw [chartRs, ← coe_mapRingHom]
    refine map_aeval_eq (S := (ChartRing L)[X][X]) (S' := (ChartRing L)[X])
      (mapRingHom (evalRingHom (0 : ChartRing L))) (fun a ↦ ?_) _ _ (fun i ↦ ?_) R
    · simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_apply,
        RatFunc.algebraMap_eq_C, coe_mapRingHom, map_C, coe_evalRingHom, eval_C]
    · fin_cases i <;> simp only [chartSubst, RingHom.map_add, Fin.isValue, RingHom.map_mul,
        Fin.zero_eta,
        Matrix.cons_val_zero, coe_mapRingHom, map_C, coe_evalRingHom, eval_C,
        eval_X, RingHom.map_zero, add_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one,
        Matrix.cons_val, c, Fin.mk_one, mul_zero, Fin.reduceFinMk, map_X]
  have hcoeff (b : ℕ) : ((chartRs R).map (evalRingHom 0)).coeff b = chartA R 0 b := by
    simp only [coeff_map, coe_evalRingHom, ← coeff_zero_eq_eval_zero, chartA]
  have hc := coeff_aeval_add_X R c
  rw [← hW, hcoeff, hcoeff] at hc
  exact hc

/-- The separant is the `Z`-derivative of the surface: `A_{0,1} = ∂_Z A_{0,0}`. -/
theorem chartA_zero_one_eq_pderiv (R : MvPolynomial (Fin 3) L) :
    chartA R 0 1 = MvPolynomial.pderiv 2 (chartA R 0 0) := by
  rw [(chartA_zero_eq_aeval R).1, (chartA_zero_eq_aeval R).2]
  induction R using MvPolynomial.induction_on with
  | C a => simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, MvPolynomial.derivation_C,
      map_zero, MvPolynomial.algHom_C, MvPolynomial.algebraMap_apply, RatFunc.algebraMap_eq_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.aeval_X, ← hp]
    fin_cases i <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
        MvPolynomial.pderiv_X, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne, map_zero,
        mul_zero, Matrix.cons_val_zero, zero_add, MvPolynomial.derivation_C, Fin.mk_one,
        Matrix.cons_val_one, Fin.reduceFinMk, Pi.single_eq_same, map_one, mul_one, Matrix.cons_val]

/-- The surface `A_{0,0}` does not involve `V` (coordinate `1`). -/
theorem chartA_zero_zero_support (R : MvPolynomial (Fin 3) L) :
    ∀ m ∈ (chartA R 0 0).support, m 1 = 0 := by
  classical
  rw [(chartA_zero_eq_aeval R).1]
  set P : ChartRing L → Prop := fun q ↦ ∀ m ∈ q.support, m 1 = 0
  have hmul : ∀ p q : ChartRing L, P p → P q → P (p * q) := by
    intro p q hp hq m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
    simp only [Fin.isValue, Finsupp.coe_add, Pi.add_apply, hp a ha, hq b hb, add_zero]
  have hX : ∀ j : Fin 3, j ≠ 1 → P (MvPolynomial.X j) := by
    intro j hj m hm
    rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
    simp only [hm, Fin.isValue, ne_eq, hj, not_false_eq_true, Finsupp.single_eq_of_ne']
  have hC : ∀ a, P (MvPolynomial.C a) := by
    intro a m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
    split_ifs at hm with h0
    · rw [← h0, Finsupp.zero_apply]
    · exact absurd rfl hm
  induction R using MvPolynomial.induction_on with
  | C a => simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, MvPolynomial.algHom_C,
      MvPolynomial.algebraMap_apply, RatFunc.algebraMap_eq_C, MvPolynomial.mem_support_iff,
      MvPolynomial.coeff_C, ne_eq, ite_eq_right_iff, map_eq_zero, not_imp, and_imp, forall_eq',
      Finsupp.coe_zero, Pi.zero_apply, implies_true]
  | add p q hp hq =>
    intro m hm
    rw [map_add] at hm
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hp m h
    · exact hq m h
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.aeval_X]
    refine hmul _ _ hp ?_
    fin_cases i
    · exact hC _
    · exact hX 0 (by decide)
    · exact hX 2 (by decide)

end Surface

/-! ## The count -/

section Count

variable {F L : Type*} [Field F] [Fintype F] [Field L] [Algebra F L] {ι : Type*} [Fintype ι]
  [DecidableEq ι] (dom : ι ↪ F) (f g : ι → L) (R : MvPolynomial (Fin 3) L) (e d h : ℕ)

open Classical in
/-- **The pairs counted for one factor `R`**: some `P` of degree at most `d` agrees with
`f + (α + β x) g` on at least `A` points, is not persistent, and `P(X^e)` is a simple root of
`R(X, α' + β' X, Z)` for `e`-th roots `α'`, `β'` of `α`, `β`. -/
noncomputable def factorPairs (A B : ℕ) : Finset (F × F) :=
  univ.filter fun ab ↦ ∃ (P : L[X]) (α' β' : L), P.natDegree ≤ d ∧
    A ≤ (agreeL dom f g P ab.1 ab.2).card ∧ ¬ IsPersistent dom f g d B ab.1 ab.2 P ∧
    α' ^ e = algebraMap F L ab.1 ∧ β' ^ e = algebraMap F L ab.2 ∧
    MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R = 0 ∧
    MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] (MvPolynomial.pderiv 2 R) ≠ 0

/-- **The non-persistent pairs of one factor** ([CWYZ26, Claims 4.8 and 4.9]): for a factor `R`
whose monomials `X^i Y^t Z^j` have `t + j ≤ h` and a Frobenius power `e = p^κ`, at most
`h (n · 2edh / (A - B))² = 4 d² e² h³ (n / (A - B))²` pairs, if `d + 1 < B < A ≤ n`. -/
theorem card_factorPairs_le {A B p κ : ℕ} [Fact p.Prime] [CharP L p] (he : e = p ^ κ)
    (hR : ∀ m ∈ R.support, m 1 + m 2 ≤ h) (hd : 1 ≤ d) (hh : 1 ≤ h) (hdB : d + 1 < B)
    (hBA : B < A) (hAn : A ≤ Fintype.card ι) :
    ((factorPairs dom f g R e d A B).card : ℚ) ≤
      h * (((Fintype.card ι * (2 * e * d * h) : ℕ) : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 := by
  classical
  set K := AlgebraicClosure (RatFunc L)
  have : CharP (RatFunc L) p :=
    charP_of_injective_algebraMap (algebraMap L (RatFunc L)).injective p
  have : CharP K p := charP_of_injective_algebraMap (algebraMap (RatFunc L) K).injective p
  have he1 : 1 ≤ e := by rw [he]; exact Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  set S := factorPairs dom f g R e d A B
  have hex : ∀ ab ∈ S, ∃ (P : L[X]) (α' β' : L), P.natDegree ≤ d ∧
      A ≤ (agreeL dom f g P ab.1 ab.2).card ∧ ¬ IsPersistent dom f g d B ab.1 ab.2 P ∧
      α' ^ e = algebraMap F L ab.1 ∧ β' ^ e = algebraMap F L ab.2 ∧
      MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R = 0 ∧
      MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] (MvPolynomial.pderiv 2 R) ≠ 0 :=
    fun ab hab ↦ (mem_filter.mp hab).2
  choose! P α' β' hPd hPA hPnp hα hβ hroot hsimple using hex
  let pt0 : F × F → (Fin 3 → K) := fun ab ↦ chartPoint (k := K) e (α' ab) (β' ab) (P ab)
  -- Distinct pairs have distinct chart points.
  have hinj : Set.InjOn pt0 S := by
    intro ab hab ab' hab' heq
    have h1 : algebraMap L K (β' ab) = algebraMap L K (β' ab') := by
      exact congrFun heq 1
    have h0 := congrFun heq 0
    simp only [pt0, chartPoint, Matrix.cons_val_zero] at h0
    rw [h1] at h0
    have hβ' := (algebraMap L K).injective h1
    have hα' := (algebraMap L K).injective (add_right_cancel h0)
    have e2 : ab.2 = ab'.2 := (algebraMap F L).injective (by rw [← hβ ab hab, ← hβ ab' hab', hβ'])
    have e1 : ab.1 = ab'.1 := (algebraMap F L).injective (by rw [← hα ab hab, ← hα ab' hab', hα'])
    exact Prod.ext e1 e2
  have hcard : S.card = (S.image pt0).card := (card_image_of_injOn hinj).symm
  rcases S.eq_empty_or_nonempty with hS0 | ⟨ab₀, hab₀⟩
  · rw [hS0, card_empty, Nat.cast_zero]; exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hs00 : MvPolynomial.aeval (pt0 ab₀) (chartA R 0 1) ≠ 0 :=
    aeval_chartA_one_chartPoint_ne_zero R e (hsimple ab₀ hab₀)
  have hsep : chartA R 0 1 ≠ 0 := fun h0 ↦ hs00 (by rw [h0, map_zero])
  have hg0 : chartA R 0 0 ≠ 0 := fun h0 ↦ hsep (chartA_zero_one_eq_zero R h0)
  -- The surface, the separant and the cuts over `K`.
  set ι' := algebraMap (RatFunc L) K
  set gk := MvPolynomial.map ι' (chartA R 0 0)
  set sk := MvPolynomial.map ι' (chartA R 0 1)
  let cutk : ι → MvPolynomial (Fin 3) K := fun x ↦ MvPolynomial.map ι' (chartCut dom f g R e d h x)
  have hmapinj : Function.Injective (MvPolynomial.map (σ := Fin 3) ι') :=
    MvPolynomial.map_injective _ ι'.injective
  have hgk : gk ≠ 0 := fun h0 ↦ hg0 (hmapinj (by rw [map_zero]; exact h0))
  have hdegmap (q : ChartRing L) : (MvPolynomial.map ι' q).totalDegree ≤ q.totalDegree :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hv : gk.totalDegree ≤ h :=
    (hdegmap _).trans (by have := chartA_totalDegree_le R hR 0 0 (Nat.zero_le h); omega)
  have hdeg : ∀ x, (cutk x).totalDegree ≤ 2 * e * d * h := fun x ↦
    (hdegmap _).trans (totalDegree_chartCut_le dom f g e d hR hd he1 hh x)
  have haeval (z : Fin 3 → K) (q : ChartRing L) :
      MvPolynomial.aeval z (MvPolynomial.map ι' q) = MvPolynomial.aeval z q :=
    MvPolynomial.aeval_map_algebraMap K z q
  -- Counted points: on the surface, off the separant, on the cuts of their agreements.
  have hon : ∀ ab ∈ S, MvPolynomial.aeval (pt0 ab) gk = 0 ∧ MvPolynomial.aeval (pt0 ab) sk ≠ 0 := by
    intro ab hab
    rw [haeval, haeval]
    exact ⟨aeval_chartA_zero_chartPoint R e (hroot ab hab),
      aeval_chartA_one_chartPoint_ne_zero R e (hsimple ab hab)⟩
  have hcut0 : ∀ ab ∈ S, ∀ x ∈ agreeL dom f g (P ab) ab.1 ab.2,
      MvPolynomial.aeval (pt0 ab) (cutk x) = 0 := by
    intro ab hab x hx
    simp only [cutk]
    rw [haeval, aeval_chartCut_chartPoint dom f g R e d h he hR hh (hPd ab hab) (hα ab hab)
      (hβ ab hab) (hroot ab hab) (aeval_chartA_one_chartPoint_ne_zero R e (hsimple ab hab))]
    rw [(mem_agreeL dom f g _ _ _ x).mp hx, eval_linL]
    simp only [add_sub_cancel_left, sub_self, map_zero, mul_zero]
  -- The surface does not involve `V`, and its `Z`-derivative is the separant.
  have hV : ∀ m ∈ gk.support, m 1 = 0 := fun m hm ↦
    chartA_zero_zero_support R m (MvPolynomial.support_map_subset _ _ hm)
  have hgs : MvPolynomial.pderiv 2 gk = sk := by
    rw [MvPolynomial.pderiv_map, ← chartA_zero_one_eq_pderiv]
  -- lvm2: the incidence count of `Lvm6AffIncid`, with two-point rigidity from
  -- `persistent_of_two_points` (in place of ArkLib's prime-component hypothesis).
  have key := Incid.card_le_of_cuts_of_rigid (K := K) gk hgk hV cutk (A := A) (B := B) hv hdeg hBA
    (S.image pt0) ?_ ?_
  · rw [hcard]; exact key
  · intro z hz
    obtain ⟨ab, hab, rfl⟩ := mem_image.mp hz
    refine ⟨(hon ab hab).1, hgs ▸ (hon ab hab).2, (hPA ab hab).trans ?_⟩
    exact card_le_card fun x hx ↦ mem_filter.mpr ⟨mem_univ _, hcut0 ab hab x hx⟩
  · -- A second point on `B + 1` common cuts makes the counted triple persistent.
    intro z hz y hne hy hys Cs hCs hcuts
    obtain ⟨ab, hab, rfl⟩ := mem_image.mp hz
    rw [hgs] at hys
    apply hPnp ab hab
    refine persistent_of_two_points dom f g R e d h he hR hh hdB (hPd ab hab) (hα ab hab)
      (hβ ab hab) (hroot ab hab) ?_ y ?_ hne Cs hCs (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · rw [← haeval]; exact (hon ab hab).2
    · rw [← haeval]; exact hys
    · rw [← haeval]; exact (hcuts x hx).1
    · rw [← haeval]; exact (hcuts x hx).2

end Count

end

end LeanVM.Protocol.Whir.AffineCombiner
