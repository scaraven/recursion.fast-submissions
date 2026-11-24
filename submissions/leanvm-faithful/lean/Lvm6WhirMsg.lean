-- New for lvm6 (WP W1). The messages of the deployed code over any field `F ⊇ K` (deployed: `E2`):
-- the novel-basis message polynomial, its range and injectivity, the low part `lowMsgF` modulo the
-- subspace polynomial `W_κ`, and the out-of-domain functional (the multilinear extension of the
-- message at a point) with its separation by Schwartz–Zippel. Ported from season 1's
-- `LvmNovelBasis` (`msgPoly`, `range_msgPoly`, `msgPoly_injective`; there over season 1's `E`) and
-- leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Tuple.lean` (`vanE`, `lowMsg`,
-- `msgPoly_lowMsg`, `lowMsg_msgPoly_add`) @ fdb317982, with the field a parameter.
import LvmNovelBasis
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Messages, low parts and OOD functionals (W1)

* `novelF j`, `msgPolyF κ g = Σ_u g(u)·X_⟨u⟩` over `F`; `range_msgPolyF`: the polynomials of degree
  `< 2^κ`; `msgPolyF_injective`.
* `vanF κ` (monic, degree `2^κ`), `lowMsgF κ P`: the message of `P mod W_κ` (`F`-linear);
  `msgPolyF_lowMsgF`, `lowMsgF_msgPolyF_add`: the low part of `P_g + W_κ·H` is `g`.
* `mlePoly g`: the multilinear extension of a message on `ν` variables; `mleEval z g`; `mlePoly_ne_zero`,
  `totalDegree_mlePoly_le`; **`card_mle_eq_le`**: two distinct messages agree at at most
  `ν · |F|^(ν−1)` points.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Whir Polynomial Finset

variable {F : Type} [Field F] [Algebra K F]

/-! ## The message polynomial over `F` -/

/-- The novel basis polynomial over `F`. -/
noncomputable abbrev novelF (j : ℕ) : F[X] := (novel j).map (algebraMap K F)

/-- **The message polynomial** `P_g = Σ_u g(u)·X_⟨u⟩` over `F`. -/
noncomputable def msgPolyF (κ : ℕ) : ((Fin κ → Bool) → F) →ₗ[F] F[X] where
  toFun g := ∑ u, g u • novelF (bitsToNat u)
  map_add' g h := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c g := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
    mul_smul]

theorem novelF_mem_degreeLT {κ : ℕ} (hκ : κ ≤ 64) (u : Fin κ → Bool) :
    novelF (F := F) (bitsToNat u) ∈ degreeLT F (2 ^ κ) := by
  have hlt : bitsToNat u < 2 ^ 64 :=
    lt_of_lt_of_le (bitsToNat_lt u) (Nat.pow_le_pow_right (by norm_num) hκ)
  rw [mem_degreeLT]
  refine lt_of_le_of_lt degree_le_natDegree ?_
  rw [natDegree_map, natDegree_novel hlt]
  exact_mod_cast bitsToNat_lt u

theorem msgPolyF_single {κ : ℕ} (u : Fin κ → Bool) :
    msgPolyF (F := F) κ (Pi.single u 1) = novelF (bitsToNat u) := by
  simp only [msgPolyF, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The `X_j`, `j < 2^κ`, span exactly the polynomials of degree `< 2^κ` (for `κ ≤ 64`). -/
theorem range_msgPolyF {κ : ℕ} (hκ : κ ≤ 64) :
    LinearMap.range (msgPolyF (F := F) κ) = degreeLT F (2 ^ κ) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact Submodule.sum_mem _ fun u _ ↦ Submodule.smul_mem _ _ (novelF_mem_degreeLT hκ u)
  · suffices H : ∀ n ≤ 2 ^ κ, degreeLT F n ≤ LinearMap.range (msgPolyF (F := F) κ) from
      H _ le_rfl
    intro n
    induction n with
    | zero =>
      intro _ p hp
      rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp
      have hp0 : p = 0 := Polynomial.ext fun m ↦ by simpa using hp m (Nat.zero_le m)
      rw [hp0]
      exact Submodule.zero_mem _
    | succ n ih =>
      intro hn p hp
      set u := (bitsEquiv κ).symm ⟨n, hn⟩ with hu_def
      have hu : bitsToNat u = n := by rw [← bitsEquiv_val, hu_def, Equiv.apply_symm_apply]
      have hn64 : n < 2 ^ 64 :=
        lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hκ)
      set q : F[X] := novelF n
      have hqdeg : q.natDegree = n := by rw [natDegree_map, natDegree_novel hn64]
      have hq0 : q ≠ 0 := by
        rw [Ne, Polynomial.map_eq_zero_iff (algebraMap K F).injective]
        exact novel_ne_zero n
      have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
      set c := p.coeff n / q.leadingCoeff
      have hp' : p - c • q ∈ degreeLT F n := by
        rw [mem_degreeLT, degree_lt_iff_coeff_zero]
        intro m hm
        rw [coeff_sub, coeff_smul, smul_eq_mul]
        rcases eq_or_lt_of_le hm with hm | hm
        · subst hm
          rw [← hqdeg, coeff_natDegree, hqdeg, div_mul_cancel₀ _ hlc, sub_self]
        · rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp
          rw [hp m (by exact_mod_cast hm), coeff_eq_zero_of_natDegree_lt
            (by (clear * - hn hu hqdeg hm; omega)), mul_zero, sub_zero]
      have hq : q ∈ LinearMap.range (msgPolyF (F := F) κ) :=
        ⟨Pi.single u 1, by rw [msgPolyF_single, hu]⟩
      have := Submodule.add_mem _ (ih (by (clear * - hn hu hqdeg; omega)) hp')
        (Submodule.smul_mem _ c hq)
      rwa [sub_add_cancel] at this

/-- The message polynomial is injective (for `κ ≤ 64`), by dimension count. -/
theorem msgPolyF_injective {κ : ℕ} (hκ : κ ≤ 64) :
    Function.Injective (msgPolyF (F := F) κ) := by
  have hmem : ∀ g, msgPolyF (F := F) κ g ∈ degreeLT F (2 ^ κ) := fun g ↦
    (range_msgPolyF (F := F) hκ) ▸ LinearMap.mem_range_self _ g
  set f := (msgPolyF (F := F) κ).codRestrict (degreeLT F (2 ^ κ)) hmem
  have hrank : Module.finrank F ((Fin κ → Bool) → F) =
      Module.finrank F (degreeLT F (2 ^ κ)) := by
    rw [Module.finrank_fintype_fun_eq_card, (degreeLTEquiv F (2 ^ κ)).finrank_eq,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  have : FiniteDimensional F (degreeLT F (2 ^ κ)) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv F (2 ^ κ)).symm
  have hsurj : Function.Surjective f := by
    rintro ⟨p, hp⟩
    rw [← range_msgPolyF hκ] at hp
    obtain ⟨g, rfl⟩ := hp
    exact ⟨g, rfl⟩
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj
  intro a b hab
  exact hinj (Subtype.ext hab)

/-- The message polynomial has degree below `2^κ`. -/
theorem natDegree_msgPolyF_lt {κ : ℕ} (hκ : κ ≤ 64) (g : (Fin κ → Bool) → F) :
    (msgPolyF κ g).degree < (2 ^ κ : ℕ) := by
  have : msgPolyF κ g ∈ degreeLT F (2 ^ κ) :=
    (range_msgPolyF (F := F) hκ) ▸ LinearMap.mem_range_self _ g
  rwa [mem_degreeLT] at this

/-! ## The low part -/

/-- The subspace polynomial `W_κ` over `F`. -/
noncomputable def vanF (κ : ℕ) : F[X] := (vanishing κ).map (algebraMap K F)

theorem vanF_monic (κ : ℕ) : (vanF (F := F) κ).Monic :=
  Monic.map _ (monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _)

theorem natDegree_vanF (κ : ℕ) : (vanF (F := F) κ).natDegree = 2 ^ κ := by
  rw [vanF, natDegree_map, natDegree_vanishing]

theorem modByMonic_mem_rangeF {κ : ℕ} (hκ : κ ≤ 64) (P : F[X]) :
    P %ₘ vanF κ ∈ LinearMap.range (msgPolyF (F := F) κ) := by
  rw [range_msgPolyF hκ, mem_degreeLT]
  have := degree_modByMonic_lt P (vanF_monic (F := F) κ)
  rwa [degree_eq_natDegree (vanF_monic κ).ne_zero, natDegree_vanF] at this

/-- **The message of the low part**, `F`-linear: `msgPolyF κ (lowMsgF κ P) = P mod W_κ`. -/
noncomputable def lowMsgF (κ : ℕ) : F[X] →ₗ[F] ((Fin κ → Bool) → F) :=
  if hκ : κ ≤ 64 then
    (LinearEquiv.ofInjective (msgPolyF κ) (msgPolyF_injective hκ)).symm.toLinearMap ∘ₗ
      (modByMonicHom (vanF κ)).codRestrict _ (modByMonic_mem_rangeF hκ)
  else 0

theorem msgPolyF_lowMsgF {κ : ℕ} (hκ : κ ≤ 64) (P : F[X]) :
    msgPolyF κ (lowMsgF κ P) = P %ₘ vanF κ := by
  simp only [lowMsgF, hκ, ↓reduceDIte, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply]
  rfl

/-- **The low part of `P_g + W_κ·H` is `g`.** -/
theorem lowMsgF_msgPolyF_add {κ : ℕ} (hκ : κ ≤ 64) (g : (Fin κ → Bool) → F) (H : F[X]) :
    lowMsgF κ (msgPolyF κ g + vanF κ * H) = g := by
  apply msgPolyF_injective hκ
  rw [msgPolyF_lowMsgF hκ]
  have hlt : (msgPolyF κ g).degree < (vanF (F := F) κ).degree := by
    rw [degree_eq_natDegree (vanF_monic κ).ne_zero, natDegree_vanF]
    exact natDegree_msgPolyF_lt hκ g
  have h0 : (vanF κ * H) %ₘ vanF κ = 0 :=
    (modByMonic_eq_zero_iff_dvd (vanF_monic κ)).mpr (dvd_mul_right _ _)
  rw [← modByMonicHom_apply, map_add, modByMonicHom_apply, modByMonicHom_apply, h0, add_zero,
    (modByMonic_eq_self_iff (vanF_monic κ)).mpr hlt]

/-- The low part of `W_κ·H` is zero. -/
theorem lowMsgF_vanF_mul {κ : ℕ} (hκ : κ ≤ 64) (H : F[X]) : lowMsgF κ (vanF κ * H) = 0 := by
  have := lowMsgF_msgPolyF_add hκ (0 : (Fin κ → Bool) → F) H
  rwa [map_zero, zero_add] at this

/-! ## The OOD functional: the multilinear extension -/

/-- The multilinear extension of a message on `ν` variables. -/
noncomputable def mlePoly {ν : ℕ} (g : (Fin ν → Bool) → F) : MvPolynomial (Fin ν) F :=
  ∑ x, MvPolynomial.C (g x) *
    ∏ i, (if x i then MvPolynomial.X i else 1 - MvPolynomial.X i)

/-- The multilinear extension at a point, linear in the message. -/
noncomputable def mleEval {ν : ℕ} (z : Fin ν → F) : ((Fin ν → Bool) → F) →ₗ[F] F where
  toFun g := MvPolynomial.eval z (mlePoly g)
  map_add' g h := by simp [mlePoly, add_mul, Finset.sum_add_distrib]
  map_smul' c g := by simp [mlePoly, Finset.mul_sum, mul_assoc]

omit [Algebra K F] in
theorem mlePoly_sub {ν : ℕ} (g h : (Fin ν → Bool) → F) : mlePoly (g - h) = mlePoly g - mlePoly h := by
  simp [mlePoly, sub_mul, Finset.sum_sub_distrib]

omit [Algebra K F] in
/-- The extension at a cube point is the message's value. -/
theorem eval_mlePoly_bool {ν : ℕ} (g : (Fin ν → Bool) → F) (y : Fin ν → Bool) :
    MvPolynomial.eval (fun i ↦ if y i then (1 : F) else 0) (mlePoly g) = g y := by
  classical
  simp only [mlePoly, map_sum, map_mul, MvPolynomial.eval_C, map_prod]
  rw [Finset.sum_eq_single y]
  · rw [Finset.prod_eq_one, mul_one]
    intro i _
    by_cases h : y i <;> simp [h]
  · intro x _ hxy
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc
      exact hxy (funext fun i ↦ not_not.mp ((not_exists.mp hc) i))
    rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
    cases hx : x i <;> cases hy : y i <;> simp_all
  · simp

omit [Algebra K F] in
theorem mlePoly_ne_zero {ν : ℕ} {g : (Fin ν → Bool) → F} (hg : g ≠ 0) : mlePoly g ≠ 0 := by
  intro h
  apply hg
  funext y
  rw [← eval_mlePoly_bool g y, h, map_zero, Pi.zero_apply]

omit [Algebra K F] in
theorem totalDegree_mlePoly_le {ν : ℕ} (g : (Fin ν → Bool) → F) : (mlePoly g).totalDegree ≤ ν := by
  classical
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun x _ ↦ ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc ∑ i, (if x i then MvPolynomial.X i else 1 - MvPolynomial.X i : MvPolynomial (Fin ν) F).totalDegree
      ≤ ∑ _i : Fin ν, 1 := Finset.sum_le_sum fun i _ ↦ by
        split
        · exact (MvPolynomial.totalDegree_X i).le
        · refine (MvPolynomial.totalDegree_sub _ _).trans
            (max_le (by simp) (MvPolynomial.totalDegree_X i).le)
    _ = ν := by simp

/-- **OOD separation** (Schwartz–Zippel): two distinct messages on `ν = k + 1` variables have equal
extensions at at most `(k + 1) · |F|^k` points. -/
theorem card_mle_eq_le [Fintype F] [DecidableEq F] {k : ℕ} {g h : (Fin (k + 1) → Bool) → F} (hgh : g ≠ h) :
    (univ.filter fun z : Fin (k + 1) → F ↦ mleEval z g = mleEval z h).card ≤
      (k + 1) * Fintype.card F ^ k := by
  have hp : mlePoly (g - h) ≠ 0 := mlePoly_ne_zero (sub_ne_zero.mpr hgh)
  have hz := MvPolynomial.schwartz_zippel_totalDegree hp (univ : Finset F)
  rw [Fintype.piFinset_univ, card_univ] at hz
  have hF : (0 : ℚ≥0) < (Fintype.card F : ℚ≥0) := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) hF] at hz
  have hset : (univ.filter fun z : Fin (k + 1) → F ↦ mleEval z g = mleEval z h) =
      univ.filter fun z ↦ MvPolynomial.eval z (mlePoly (g - h)) = 0 := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [mleEval, mlePoly_sub, sub_eq_zero]
  rw [hset]
  have h1 : ((univ.filter fun z : Fin (k + 1) → F ↦
      MvPolynomial.eval z (mlePoly (g - h)) = 0).card : ℚ≥0) * Fintype.card F ≤
      ((k + 1) * Fintype.card F ^ k : ℕ) * Fintype.card F := by
    calc _ ≤ ((mlePoly (g - h)).totalDegree : ℚ≥0) * (Fintype.card F : ℚ≥0) ^ (k + 1) := hz
      _ ≤ ((k + 1 : ℕ) : ℚ≥0) * (Fintype.card F : ℚ≥0) ^ (k + 1) := by
          gcongr; exact_mod_cast totalDegree_mlePoly_le _
      _ = _ := by push_cast; ring
  exact_mod_cast le_of_mul_le_mul_right h1 hF

end Lvm6.Whir
