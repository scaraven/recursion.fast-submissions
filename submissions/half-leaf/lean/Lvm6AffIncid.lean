-- lvm6 (WP M1): taken from season 1's branch lvm2/AC-THM (858ab301), files LvmMcaAff* renamed Lvm6Aff*.
-- New for lvm2 (WP AC-THM). STATEMENT FROZEN 2026-11-13; proved [AC-THM-INC-B].
-- Not imported by any submission root until the integration roll.
-- Bespoke replacement for ArkLib's `MvPolynomial.card_le_of_agreement_off_excluded_of_hypersurface`
-- (`ArkLib/ToMathlib/RingTheory/Nullstellensatz/AgreementIncidence.lean`), which the vendored
-- `Lvm6AffFactorCount` (from leanEthereum/leanVM `AffineCombinerFactorCount`) used for the incidence
-- count of CWYZ26 Claim 4.8. ArkLib is not importable (AC-G0 §5), and vendoring its Hilbert-polynomial
-- closure costs 7.2 k lines and 50 non-precompiled Mathlib modules. Here the count is proved only in
-- the chart of CWYZ26 Claim 4.9: a surface `g(Y, Z) = 0` in `K³` (coordinates `Y, V, Z` = `0, 1, 2`)
-- that does not involve `V`, and cuts of bounded degree, with affine Hilbert functions instead of
-- Hilbert polynomials (design: docs/lvm2/stages/AC-THM.md §2).
import Lvm6AffIncidSat
import Lvm6AffIncidIso
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Agreement incidences on a cylinder surface in `K³`

`card_le_of_cuts_of_rigid` is the incidence count of CWYZ26 Claim 4.8 for the chart of Claim 4.9:
a finite set `S` of points on `g = 0` off `∂_Z g = 0`, each on at least `A` of the cuts, has at most
`v (n b / (A − B))²` points if no two distinct points of the surface off `∂_Z g = 0`, one of them in
`S`, lie on `B + 1` common cuts (the *rigidity* that non-persistence gives through the injective
chart map). `n` is the number of cuts, `v ≥ deg g`, `b ≥ deg` of every cut.

The proof (AC-THM.md §2):
* **Surface level.** Factor `g = c ∏ r_k^{μ_k}` (all `r_k` free of `V`). A point of `S` lies on exactly
  one `r_k`, simply. At most `B` cuts are divisible by `r_k` (else the vertical shift of the point
  contradicts rigidity), so each point has at least `A − B` cuts `i` with `r_k ∤ cut i`.
* **Curve level.** For such `(k, i)`, a cut `j` is *good* for a point `x` if `x` lies on the
  saturation `(r_k, cut i) : cut j^∞`. At most `B` cuts of `x`'s agreement set are bad
  (`exists_ne_of_isolated`: else `x` is isolated on `r_k = cut i = 0` off `∂_Z g = 0`, but there
  is a second point, contradicting rigidity).
* **Count.** `card_le_of_sat`: the good points on `cut j = 0` number at most `deg r_k · b · b`
  (affine Hilbert function of `(r_k, cut i)`, slope `deg r_k · b`, and the cut is a non-zero-divisor
  modulo the saturation). Two double countings give the bound.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner.Incid

open MvPolynomial Finset

variable {K : Type*} [Field K]

/-- Double counting: if every `a ∈ s` is related to at least `c` elements of `t`, then
`c · |s| ≤ ∑_{b ∈ t} |{a ∈ s | R a b}|`. -/
theorem mul_card_le_sum_card_filter {α β : Type*} (s : Finset α) (t : Finset β) (R : α → β → Prop)
    [∀ a b, Decidable (R a b)] {c : ℕ} (h : ∀ a ∈ s, c ≤ (t.filter (R a)).card) :
    c * s.card ≤ ∑ b ∈ t, (s.filter (R · b)).card := by
  calc c * s.card = ∑ _a ∈ s, c := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ s, (t.filter (R a)).card := sum_le_sum h
    _ = ∑ b ∈ t, (s.filter (R · b)).card := by simp only [card_filter]; exact sum_comm

/-- The total degree of a product of non-zero polynomials is the sum of the total degrees. -/
theorem totalDegree_multiset_prod_eq {σ : Type*} (s : Multiset (MvPolynomial σ K))
    (h : (0 : MvPolynomial σ K) ∉ s) : s.prod.totalDegree = (s.map totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.prod_zero, totalDegree_one, Multiset.map_zero, Multiset.sum_zero]
  | cons a s ih =>
    have ha : a ≠ 0 := fun h0 ↦ h (h0 ▸ Multiset.mem_cons_self 0 s)
    have hs : (0 : MvPolynomial σ K) ∉ s := fun h0 ↦ h (Multiset.mem_cons_of_mem h0)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      totalDegree_mul_of_isDomain ha (Multiset.prod_ne_zero hs), ih hs]

/-- A divisor of a non-zero polynomial free of `V` is free of `V`. -/
theorem vfree_of_dvd {g r : MvPolynomial (Fin 3) K} (hg : g ≠ 0) (hV : ∀ m ∈ g.support, m 1 = 0)
    (h : r ∣ g) : ∀ m ∈ r.support, m 1 = 0 := by
  obtain ⟨q, rfl⟩ := h
  have h0 : degreeOf 1 (r * q) ≤ 0 := degreeOf_le_iff.mpr fun m hm ↦ (hV m hm).le
  rw [degreeOf_mul_eq (left_ne_zero_of_mul hg) (right_ne_zero_of_mul hg)] at h0
  intro m hm
  exact Nat.le_zero.mp (degreeOf_le_iff.mp (by omega : degreeOf 1 r ≤ 0) m hm)

theorem eval_eq_zero_of_dvd {r p : MvPolynomial (Fin 3) K} (h : r ∣ p) {x : Fin 3 → K}
    (hx : eval x r = 0) : eval x p = 0 := by
  obtain ⟨q, rfl⟩ := h
  rw [RingHom.map_mul, hx, zero_mul]

/-- A point of `r = 0` off `∂_Z g = 0`, `r ∣ g`, is off `∂_Z r = 0`. -/
theorem eval_pderiv_ne_zero_of_dvd {g r : MvPolynomial (Fin 3) K} (h : r ∣ g) {x : Fin 3 → K}
    (hx : eval x r = 0) (hg : eval x (pderiv 2 g) ≠ 0) : eval x (pderiv 2 r) ≠ 0 := by
  obtain ⟨q, rfl⟩ := h
  rw [pderiv_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, hx, zero_mul, add_zero] at hg
  exact left_ne_zero_of_mul hg

/-- `x` lies on the saturation `(r, G) : G'^∞`. -/
def OnSat (r G G' : MvPolynomial (Fin 3) K) (x : Fin 3 → K) : Prop :=
  ∀ y : MvPolynomial (Fin 3) K, (∃ N : ℕ, G' ^ N * y ∈ Ideal.span {r, G}) → eval x y = 0

open Classical in
/-- **Agreement incidences on a cylinder surface** (CWYZ26 Claim 4.8, in the chart of Claim 4.9)
[AC-THM-INC-B]. `g ≠ 0` does not involve `V`, `deg g ≤ v`, every cut has degree at most `b`, and
`B < A`. Let every point of `S` lie on `g = 0`, off `∂_Z g = 0`, and on at least `A` cuts, and let no
point `y ≠ x` of `g = 0` off `∂_Z g = 0` share more than `B` cuts with a point `x ∈ S`. Then
`|S| ≤ v (n b / (A − B))²`, `n` the number of cuts. This is the conclusion that
`Lvm6AffFactorCount` drew from ArkLib's `card_le_of_agreement_off_excluded_of_hypersurface` with
`L = B + 1`, `highCuts = []`, `s = ∂_Z g` and two-point rigidity in place of its prime-ideal
hypothesis. -/
theorem card_le_of_cuts_of_rigid [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (g : MvPolynomial (Fin 3) K) (hg : g ≠ 0) (hV : ∀ m ∈ g.support, m 1 = 0)
    (cuts : ι → MvPolynomial (Fin 3) K) {v b A B : ℕ} (hv : g.totalDegree ≤ v)
    (hb : ∀ i, (cuts i).totalDegree ≤ b) (hBA : B < A) (S : Finset (Fin 3 → K))
    (hS : ∀ x ∈ S, eval x g = 0 ∧ eval x (pderiv 2 g) ≠ 0 ∧
      A ≤ (univ.filter fun i ↦ eval x (cuts i) = 0).card)
    (hrig : ∀ x ∈ S, ∀ y : Fin 3 → K, y ≠ x → eval y g = 0 → eval y (pderiv 2 g) ≠ 0 →
      ∀ C : Finset ι, B < C.card → (∀ i ∈ C, eval x (cuts i) = 0 ∧ eval y (cuts i) = 0) → False) :
    (S.card : ℚ) ≤ v * (((Fintype.card ι * b : ℕ) : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 := by
  -- The bound for the points on one irreducible factor `r` of `g`.
  have hfac : ∀ r : MvPolynomial (Fin 3) K, Irreducible r → r ∣ g →
      (A - B) * ((A - B) * (S.filter fun x ↦ eval x r = 0).card) ≤
        Fintype.card ι * (Fintype.card ι * (r.totalDegree * b * b)) := by
    intro r hr hrg
    have hVr := vfree_of_dvd hg hV hrg
    -- Surface level: at least `A − B` cuts through `x` are not divisible by `r`.
    have hsurf : ∀ x ∈ S.filter (fun x ↦ eval x r = 0),
        A - B ≤ (univ.filter fun i ↦ eval x (cuts i) = 0 ∧ ¬ r ∣ cuts i).card := by
      intro x hx
      obtain ⟨hxS, hxr⟩ := mem_filter.mp hx
      obtain ⟨-, hxgZ, hxA⟩ := hS x hxS
      have hrZ := eval_pderiv_ne_zero_of_dvd hrg hxr hxgZ
      have hdiv : (univ.filter fun i ↦ r ∣ cuts i).card ≤ B := by
        by_contra hlt
        obtain ⟨z, hzx, hzr, -, hzH⟩ :=
          exists_ne_of_isolated r 0 (pderiv 2 g) hVr x hxr hrZ (map_zero _) hxgZ
        exact hrig x hxS z hzx (eval_eq_zero_of_dvd hrg hzr) hzH _ (not_le.mp hlt) fun i hi ↦
          ⟨eval_eq_zero_of_dvd (mem_filter.mp hi).2 hxr,
            eval_eq_zero_of_dvd (mem_filter.mp hi).2 hzr⟩
      have hsub : (univ.filter fun i ↦ eval x (cuts i) = 0) ⊆
          (univ.filter fun i ↦ eval x (cuts i) = 0 ∧ ¬ r ∣ cuts i) ∪
            (univ.filter fun i ↦ r ∣ cuts i) := by
        intro i hi
        simp only [mem_union, mem_filter, mem_univ, true_and] at hi ⊢
        by_cases h : r ∣ cuts i
        · exact Or.inr h
        · exact Or.inl ⟨hi, h⟩
      have := (card_le_card hsub).trans (card_union_le _ _)
      omega
    -- Curve level: at least `A − B` cuts `j` through `x` are good for `(r, cut i)`.
    have hcurve : ∀ x ∈ S.filter (fun x ↦ eval x r = 0), ∀ i, eval x (cuts i) = 0 →
        A - B ≤ (univ.filter fun j ↦ eval x (cuts j) = 0 ∧ OnSat r (cuts i) (cuts j) x).card := by
      intro x hx i hxi
      obtain ⟨hxS, hxr⟩ := mem_filter.mp hx
      obtain ⟨-, hxgZ, hxA⟩ := hS x hxS
      have hrZ := eval_pderiv_ne_zero_of_dvd hrg hxr hxgZ
      have hbad : (univ.filter fun j ↦ eval x (cuts j) = 0 ∧ ¬ OnSat r (cuts i) (cuts j) x).card
          ≤ B := by
        by_contra hlt
        have hw : ∀ j ∈ univ.filter (fun j ↦ eval x (cuts j) = 0 ∧ ¬ OnSat r (cuts i) (cuts j) x),
            ∃ y, (∃ N : ℕ, cuts j ^ N * y ∈ Ideal.span {r, cuts i}) ∧ eval x y ≠ 0 := by
          intro j hj
          have h := (mem_filter.mp hj).2.2
          simp only [OnSat, not_forall, exists_prop] at h
          exact h
        choose! w hwN hwx using hw
        obtain ⟨z, hzx, hzr, hzi, hzH⟩ := exists_ne_of_isolated r (cuts i)
          ((∏ j ∈ univ.filter (fun j ↦ eval x (cuts j) = 0 ∧ ¬ OnSat r (cuts i) (cuts j) x), w j) *
            pderiv 2 g) hVr x hxr hrZ hxi
          (by rw [RingHom.map_mul, map_prod]; exact mul_ne_zero (prod_ne_zero_iff.mpr hwx) hxgZ)
        rw [RingHom.map_mul, map_prod] at hzH
        have hzw := prod_ne_zero_iff.mp (left_ne_zero_of_mul hzH)
        refine hrig x hxS z hzx (eval_eq_zero_of_dvd hrg hzr) (right_ne_zero_of_mul hzH) _
          (not_le.mp hlt) fun j hj ↦ ⟨(mem_filter.mp hj).2.1, ?_⟩
        obtain ⟨N, hN⟩ := hwN j hj
        obtain ⟨a, a', ha⟩ := Ideal.mem_span_pair.mp hN
        have h := congrArg (eval z) ha
        rw [RingHom.map_add, RingHom.map_mul, RingHom.map_mul, hzr, hzi, mul_zero, mul_zero,
          add_zero, RingHom.map_mul, RingHom.map_pow] at h
        by_contra hne
        exact mul_ne_zero (pow_ne_zero N hne) (hzw j hj) h.symm
      have hsub : (univ.filter fun j ↦ eval x (cuts j) = 0) ⊆
          (univ.filter fun j ↦ eval x (cuts j) = 0 ∧ OnSat r (cuts i) (cuts j) x) ∪
            (univ.filter fun j ↦ eval x (cuts j) = 0 ∧ ¬ OnSat r (cuts i) (cuts j) x) := by
        intro j hj
        simp only [mem_union, mem_filter, mem_univ, true_and] at hj ⊢
        by_cases h : OnSat r (cuts i) (cuts j) x
        · exact Or.inl ⟨hj, h⟩
        · exact Or.inr ⟨hj, h⟩
      have := (card_le_card hsub).trans (card_union_le _ _)
      omega
    -- Count for one cut `i` with `r ∤ cut i`: `card_le_of_sat` for each `j`, double counting.
    have hi : ∀ i, (A - B) * ((S.filter fun x ↦ eval x r = 0).filter
        fun x ↦ eval x (cuts i) = 0 ∧ ¬ r ∣ cuts i).card ≤
          Fintype.card ι * (r.totalDegree * b * b) := by
      intro i
      by_cases hri : r ∣ cuts i
      · simp only [hri, not_true_eq_false, and_false, filter_false, card_empty, mul_zero,
          zero_le]
      calc (A - B) * ((S.filter fun x ↦ eval x r = 0).filter
            fun x ↦ eval x (cuts i) = 0 ∧ ¬ r ∣ cuts i).card
          ≤ ∑ j, (((S.filter fun x ↦ eval x r = 0).filter
              fun x ↦ eval x (cuts i) = 0 ∧ ¬ r ∣ cuts i).filter
                fun x ↦ eval x (cuts j) = 0 ∧ OnSat r (cuts i) (cuts j) x).card :=
            mul_card_le_sum_card_filter _ _ _ fun x hx ↦
              hcurve x (mem_filter.mp hx).1 i (mem_filter.mp hx).2.1
        _ ≤ ∑ _j : ι, r.totalDegree * b * b := sum_le_sum fun j _ ↦
            card_le_of_sat r (cuts i) (cuts j) hr hri le_rfl (hb i) (hb j) _ fun x hx ↦
              (mem_filter.mp hx).2
        _ = Fintype.card ι * (r.totalDegree * b * b) := by rw [sum_const, card_univ, smul_eq_mul]
    calc (A - B) * ((A - B) * (S.filter fun x ↦ eval x r = 0).card)
        ≤ (A - B) * ∑ i, ((S.filter fun x ↦ eval x r = 0).filter
            fun x ↦ eval x (cuts i) = 0 ∧ ¬ r ∣ cuts i).card :=
          Nat.mul_le_mul_left _ (mul_card_le_sum_card_filter _ _ _ hsurf)
      _ = ∑ i, (A - B) * ((S.filter fun x ↦ eval x r = 0).filter
            fun x ↦ eval x (cuts i) = 0 ∧ ¬ r ∣ cuts i).card := mul_sum _ _ _
      _ ≤ ∑ _i : ι, Fintype.card ι * (r.totalDegree * b * b) := sum_le_sum fun i _ ↦ hi i
      _ = Fintype.card ι * (Fintype.card ι * (r.totalDegree * b * b)) := by
        rw [sum_const, card_univ, smul_eq_mul]
  -- Every point of `S` is on some irreducible factor of `g`.
  have hcover : S ⊆ (UniqueFactorizationMonoid.factors g).toFinset.biUnion
      fun r ↦ S.filter fun x ↦ eval x r = 0 := by
    intro x hx
    rw [mem_biUnion]
    have hprod : eval x (UniqueFactorizationMonoid.factors g).prod = 0 := by
      obtain ⟨w, hw⟩ := (UniqueFactorizationMonoid.factors_prod hg).symm.dvd
      rw [hw, RingHom.map_mul, (hS x hx).1, zero_mul]
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
    obtain ⟨r, hr, hr0⟩ := hprod
    exact ⟨r, Multiset.mem_toFinset.mpr hr, mem_filter.mpr ⟨hx, hr0⟩⟩
  -- The degrees of the distinct factors add up to at most `v`.
  have hdeg : ∑ r ∈ (UniqueFactorizationMonoid.factors g).toFinset, r.totalDegree ≤ v := by
    have hne : (0 : MvPolynomial (Fin 3) K) ∉ UniqueFactorizationMonoid.factors g := fun h ↦
      (UniqueFactorizationMonoid.irreducible_of_factor _ h).ne_zero rfl
    calc ∑ r ∈ (UniqueFactorizationMonoid.factors g).toFinset, r.totalDegree
        ≤ ((UniqueFactorizationMonoid.factors g).map totalDegree).sum := by
          rw [Finset.sum_multiset_map_count]
          exact sum_le_sum fun r hr ↦ by
            rw [smul_eq_mul]
            exact Nat.le_mul_of_pos_left _ (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hr))
      _ = (UniqueFactorizationMonoid.factors g).prod.totalDegree :=
          (totalDegree_multiset_prod_eq _ hne).symm
      _ ≤ g.totalDegree :=
          totalDegree_le_of_dvd_of_isDomain (UniqueFactorizationMonoid.factors_prod hg).dvd hg
      _ ≤ v := hv
  have hmain : S.card * (A - B) ^ 2 ≤ v * (Fintype.card ι * b) ^ 2 := by
    calc S.card * (A - B) ^ 2 = (A - B) * ((A - B) * S.card) := by ring
      _ ≤ (A - B) * ((A - B) * ∑ r ∈ (UniqueFactorizationMonoid.factors g).toFinset,
            (S.filter fun x ↦ eval x r = 0).card) :=
          Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ ((card_le_card hcover).trans card_biUnion_le))
      _ = ∑ r ∈ (UniqueFactorizationMonoid.factors g).toFinset,
            (A - B) * ((A - B) * (S.filter fun x ↦ eval x r = 0).card) := by
          rw [mul_sum, mul_sum]
      _ ≤ ∑ r ∈ (UniqueFactorizationMonoid.factors g).toFinset,
            Fintype.card ι * (Fintype.card ι * (r.totalDegree * b * b)) := sum_le_sum fun r hr ↦
          hfac r (UniqueFactorizationMonoid.irreducible_of_factor _ (Multiset.mem_toFinset.mp hr))
            (UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hr))
      _ = (∑ r ∈ (UniqueFactorizationMonoid.factors g).toFinset, r.totalDegree) *
            (Fintype.card ι * b) ^ 2 := by
          rw [sum_mul]
          exact sum_congr rfl fun r _ ↦ by ring
      _ ≤ v * (Fintype.card ι * b) ^ 2 := Nat.mul_le_mul_right _ hdeg
  have hAB : (0 : ℚ) < ((A - B : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hBA
  rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hAB 2)]
  exact_mod_cast hmain

end LeanVM.Protocol.Whir.AffineCombiner.Incid
