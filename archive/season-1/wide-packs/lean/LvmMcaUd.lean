-- WP-6 (UD). Section "One coordinate" is ported from leanVM
-- `formal/lean_vm/LeanVM/Protocol/ToArkLib/Whir/Fold.lean` (leanVM `0b850750`): `fold`, `foldBad`,
-- `McaBad`, `card_foldBad_le_of_mca` and their lemmas, without the ArkLib Johnson and exact-line
-- parts and without `foldMany` (unused downstream). The unique-decoding counts are new; their line
-- bound is `LvmUdBW.lineBad_cover` (after flock-recursive `mca_ud_line`).
import LvmRS
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.ComputeDegree

-- ===== merged from `LvmUdBW` (GOLF module merge: `LvmUdBW.lean` is now a stub importing `LvmMcaUd`) =====
section
-- WP-6 (UD). Ported from flock-recursive `FRProximityFold.lean` sections `G6_FRProximityBW` and
-- `G6_FRProximityLine` (branch kk/base `c52529eb`): `mul_mem_degreeLT`, `poly_eq_zero_of_vanish`,
-- `bw_unique`, `polyOf`, `colPoly`, `rowPoly`, `bwRes`, `bwMap`, `bw_exists`, `bw_E_ne`,
-- `bw_few_zero_cols`, `line_eq_root`, `mca_ud_line_cover`. Changes: positions are any finite type
-- `ι` with an embedding `domain : ι ↪ F` (FR: `Fin n` and an injective `x`); the line is
-- `u₀ + z u₁` (FR: `u₀ + z (u₁ − u₀)`); the threshold is an agreement count `A` (FR: `n − e`).

/-!
# Correlated agreement on lines in the unique-decoding range (Berlekamp–Welch with a variable)

Generic over a field `F`, a finite position type `ι` (`n = |ι|`), `domain : ι ↪ F`, the code
`C = RS[F, domain, k]` and an error bound `e` with `2e + k ≤ n` (`2e < d = n − k + 1`).

For words `u₀ u₁ : ι → F`, `lineBad C e u₀ u₁` is the set of `z` for which `u₀ + z u₁` agrees with
a codeword `w` on at least `n − e` positions but **no** pair `v₀ v₁ ∈ C` has joint agreement with
`(u₀, u₁)` exactly equal to that agreement set. **`lineBad_cover`**: that set is covered by a
finite set of at most `lineMca n k e = k e + n` elements. No threshold on the number of close `z`
is needed; the bound holds in every field.

The proof (Berlekamp–Welch with a variable `Z`, solved by counting rather than by a rank argument
over `F(Z)`; FR's argument):

1. **Interpolation** (`bw_exists`). With `a := n − k − e ≥ e`, there are coefficient arrays
   `E` (`X`-degree `≤ a`, `Z`-degree `≤ e`) and `N` (`X`-degree `< n − e`, `Z`-degree `≤ e + 1`),
   not both zero, with `N(x_j, Z) = E(x_j, Z) · (u₀_j + Z u₁_j)` in `F[Z]` for every `j`:
   `(a+1)(e+1) + (n−e)(e+2)` unknowns against `n (e+2)` linear equations.
2. `E ≠ 0` (else `N` vanishes at `n` points with `X`-degree `< n`), so `E(x_j, Z) = 0` for at
   most `a` positions (`bw_few_zero_cols`); pick `k` positions `J` with `E(x_j, Z) ≠ 0`, and let
   `v₀, v₁ ∈ C` interpolate `u₀, u₁` on `J`.
3. For `z` off the `≤ k e` roots of the `E(x_j, Z)`, `j ∈ J`, and `u₀ + z u₁` close to `w = P(x)`:
   `bw_unique` gives `N(X, z) = E(X, z) P`, so `u₀ + z u₁ = P` on `J`, so `w = v₀ + z v₁`.
4. Off the joint agreement set of `(u₀, u₁)` with `(v₀, v₁)`, `u₀ + z u₁ − (v₀ + z v₁)` is a
   nonzero affine function of `z` at each position: at most `n` further values of `z` add an
   agreement. For every other close `z` the agreement set is exactly the joint one.
-/

namespace LeanVM.Protocol.Whir.Ud

open Polynomial Finset

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-! ## Degree facts and Berlekamp–Welch uniqueness -/

/-- `deg p ≤ a`, `deg q < b` give `deg (p q) < a + b`. -/
theorem mul_mem_degreeLT {a b : ℕ} {p q : F[X]} (hp : p ∈ degreeLT F (a + 1))
    (hq : q ∈ degreeLT F b) : p * q ∈ degreeLT F (a + b) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hq0 : q = 0
  · simp [hq0]
  have h1 := (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp)
  have h2 := (natDegree_lt_iff_degree_lt hq0).2 (mem_degreeLT.1 hq)
  rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt (mul_ne_zero hp0 hq0), natDegree_mul hp0 hq0]
  omega

omit [Fintype ι] in
/-- A polynomial of degree `< m` vanishing at `m` of the points `domain j` is zero. -/
theorem poly_eq_zero_of_vanish (domain : ι ↪ F) {m : ℕ} {p : F[X]}
    (hp : p ∈ degreeLT F m) (S : Finset ι) (hS : m ≤ S.card)
    (h : ∀ j ∈ S, p.eval (domain j) = 0) : p = 0 := by
  have hk : ((m : ℕ) : WithBot ℕ) ≤ (S.card : WithBot ℕ) := by exact_mod_cast hS
  exact Polynomial.eq_of_degrees_lt_of_eval_index_eq S (domain.injective.injOn)
    ((mem_degreeLT.1 hp).trans_le hk) (by simp) fun j hj ↦ by simp [h j hj]

omit [Fintype ι] in
/-- **Berlekamp–Welch uniqueness** (FR `bw_unique`): if `N(x_j) = E(x_j) · u_j` at every
position, `deg E ≤ a`, `deg N < a + k`, `deg P < k`, and `u_j = P(x_j)` on a set `S` of `a + k`
positions, then `N = E · P`. -/
theorem bw_unique (domain : ι ↪ F) {a k : ℕ} {E N P : F[X]}
    (hE : E ∈ degreeLT F (a + 1)) (hN : N ∈ degreeLT F (a + k)) (hP : P ∈ degreeLT F k)
    (u : ι → F) (hEN : ∀ j, N.eval (domain j) = E.eval (domain j) * u j) (S : Finset ι)
    (hS : a + k ≤ S.card) (hagree : ∀ j ∈ S, u j = P.eval (domain j)) : N = E * P := by
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_vanish domain (sub_mem hN (mul_mem_degreeLT hE hP)) S hS fun j hj ↦ ?_
  rw [eval_sub, eval_mul, hEN, hagree j hj, sub_self]

/-! ## Coefficient arrays as polynomials -/

/-- The polynomial `Σ_{a<m} d_a X^a`. -/
noncomputable def polyOf {m : ℕ} (d : Fin m → F) : F[X] := ∑ a : Fin m, C (d a) * X ^ (a : ℕ)

omit [Fintype ι] in
theorem polyOf_mem {m : ℕ} (d : Fin m → F) : polyOf d ∈ degreeLT F m :=
  mem_degreeLT.2 (degree_sum_fin_lt d)

omit [Fintype ι] in
theorem eval_polyOf {m : ℕ} (d : Fin m → F) (y : F) :
    (polyOf d).eval y = ∑ a, d a * y ^ (a : ℕ) := by
  simp [polyOf, eval_finsetSum]

omit [Fintype ι] in
theorem coeff_polyOf {m : ℕ} (d : Fin m → F) (a : Fin m) : (polyOf d).coeff a = d a := by
  simp [polyOf, finsetSum_coeff, coeff_X_pow, Fin.val_inj]

omit [Fintype ι] in
theorem polyOf_add {m : ℕ} (d d' : Fin m → F) : polyOf (d + d') = polyOf d + polyOf d' := by
  simp [polyOf, add_mul, sum_add_distrib]

omit [Fintype ι] in
theorem polyOf_smul {m : ℕ} (c : F) (d : Fin m → F) : polyOf (c • d) = C c * polyOf d := by
  simp [polyOf, mul_sum, mul_assoc]

/-- `B(y, Z) = Σ_a y^a B_a(Z)` for the coefficient array `B a b` of `X^a Z^b`. -/
noncomputable def colPoly {m T : ℕ} (B : Fin m → Fin T → F) (y : F) : F[X] :=
  ∑ a : Fin m, C (y ^ (a : ℕ)) * polyOf (B a)

/-- `B(X, z)`. -/
noncomputable def rowPoly {m T : ℕ} (B : Fin m → Fin T → F) (z : F) : F[X] :=
  polyOf fun a ↦ (polyOf (B a)).eval z

omit [Fintype ι] in
theorem eval_colPoly {m T : ℕ} (B : Fin m → Fin T → F) (y z : F) :
    (colPoly B y).eval z = (rowPoly B z).eval y := by
  simp [colPoly, rowPoly, eval_polyOf, eval_finsetSum, mul_comm]

omit [Fintype ι] in
theorem coeff_colPoly {m T : ℕ} (B : Fin m → Fin T → F) (y : F) (t : Fin T) :
    (colPoly B y).coeff t = (polyOf fun a ↦ B a t).eval y := by
  simp only [colPoly, finsetSum_coeff, coeff_C_mul, coeff_polyOf, eval_polyOf]
  exact sum_congr rfl fun a _ ↦ mul_comm _ _

omit [Fintype ι] in
theorem colPoly_mem {m T : ℕ} (B : Fin m → Fin T → F) (y : F) : colPoly B y ∈ degreeLT F T :=
  sum_mem fun a _ ↦ by rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (polyOf_mem _)

omit [Fintype ι] in
theorem colPoly_add {m T : ℕ} (B B' : Fin m → Fin T → F) (y : F) :
    colPoly (B + B') y = colPoly B y + colPoly B' y := by
  simp [colPoly, polyOf_add, mul_add, sum_add_distrib]

omit [Fintype ι] in
theorem colPoly_smul {m T : ℕ} (c : F) (B : Fin m → Fin T → F) (y : F) :
    colPoly (c • B) y = C c * colPoly B y := by
  simp only [colPoly, Pi.smul_apply, polyOf_smul, mul_sum]
  exact sum_congr rfl fun _ _ ↦ by ring

omit [Fintype ι] in
theorem colPoly_zero {m T : ℕ} (y : F) : colPoly (0 : Fin m → Fin T → F) y = 0 := by
  simpa using colPoly_smul (0 : F) (0 : Fin m → Fin T → F) y

/-! ## The Berlekamp–Welch system with a variable `Z` -/

/-- The residual `N(x_j, Z) − E(x_j, Z) (u₀_j + Z u₁_j)` at position `j`. -/
noncomputable def bwRes {m m' T T' : ℕ} (domain : ι ↪ F) (u₀ u₁ : ι → F)
    (E : Fin m → Fin T → F) (N : Fin m' → Fin T' → F) (j : ι) : F[X] :=
  colPoly N (domain j) - colPoly E (domain j) * (C (u₀ j) + X * C (u₁ j))

/-- The residuals' first `T + 1` coefficients, an `F`-linear map of `(E, N)`. -/
noncomputable def bwMap (domain : ι ↪ F) (u₀ u₁ : ι → F) (m m' T : ℕ) :
    ((Fin m → Fin T → F) × (Fin m' → Fin (T + 1) → F)) →ₗ[F] (ι → Fin (T + 1) → F) where
  toFun p j t := (bwRes domain u₀ u₁ p.1 p.2 j).coeff t
  map_add' p q := by
    funext j t
    simp only [bwRes, Prod.fst_add, Prod.snd_add, colPoly_add, Pi.add_apply]
    rw [← coeff_add]; exact congrArg (coeff · t) (by ring)
  map_smul' c p := by
    funext j t
    simp only [bwRes, Prod.smul_fst, Prod.smul_snd, colPoly_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [← coeff_C_mul]; exact congrArg (coeff · t) (by ring)

omit [Fintype ι] in
theorem bwRes_mem {m m' T : ℕ} (domain : ι ↪ F) (u₀ u₁ : ι → F) (E : Fin m → Fin T → F)
    (N : Fin m' → Fin (T + 1) → F) (j : ι) : bwRes domain u₀ u₁ E N j ∈ degreeLT F (T + 1) := by
  refine sub_mem (colPoly_mem N _) ?_
  rw [mul_comm, Nat.add_comm T 1]
  refine mul_mem_degreeLT ?_ (colPoly_mem E _)
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE]
  compute_degree!

/-- **Step 1** (`bw_exists`): with `2e + k ≤ n` the system has a nonzero solution with
`X`-degrees `≤ n − k − e`, `< n − e` and `Z`-degrees `≤ e`, `≤ e + 1`. -/
theorem bw_exists (domain : ι ↪ F) (u₀ u₁ : ι → F) {k e : ℕ}
    (h : 2 * e + k ≤ Fintype.card ι) :
    ∃ (E : Fin (Fintype.card ι - k - e + 1) → Fin (e + 1) → F)
      (N : Fin (Fintype.card ι - e) → Fin (e + 2) → F),
      (E, N) ≠ 0 ∧ ∀ j, bwRes domain u₀ u₁ E N j = 0 := by
  set n := Fintype.card ι with hn
  have hdim : Module.finrank F (ι → Fin (e + 1 + 1) → F) <
      Module.finrank F ((Fin (n - k - e + 1) → Fin (e + 1) → F) ×
        (Fin (n - e) → Fin (e + 1 + 1) → F)) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
      Fintype.card_fin, mul_one, sum_const, card_univ, smul_eq_mul, ← hn]
    obtain ⟨a, ha⟩ : ∃ a, n - k - e = e + a := ⟨n - k - e - e, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, n = e + b := ⟨n - e, by omega⟩
    rw [ha, hb, Nat.add_sub_cancel_left]
    ring_nf
    omega
  obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1
    (LinearMap.ker_ne_bot_of_finrank_lt (f := bwMap domain u₀ u₁ _ _ _) hdim)
  refine ⟨p.1, p.2, hp0, fun j ↦ ?_⟩
  have hres := bwRes_mem domain u₀ u₁ p.1 p.2 j
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hres
  ext t
  rw [coeff_zero]
  by_cases ht : t < e + 2
  · exact congrFun (congrFun (LinearMap.mem_ker.1 hp) j) ⟨t, ht⟩
  · exact hres t (by omega)

/-- **Step 2a**: a solution with `E = 0` and `m' ≤ n` is zero. -/
theorem bw_E_ne (domain : ι ↪ F) {u₀ u₁ : ι → F} {m m' T T' : ℕ}
    (hm' : m' ≤ Fintype.card ι) {E : Fin m → Fin T → F} {N : Fin m' → Fin T' → F}
    (hne : (E, N) ≠ 0) (hres : ∀ j, bwRes domain u₀ u₁ E N j = 0) : E ≠ 0 := by
  rintro rfl
  apply hne
  ext a t
  · rfl
  have hj : ∀ j, (polyOf fun a ↦ N a t).eval (domain j) = 0 := fun j ↦ by
    have := congrArg (fun p ↦ p.coeff t) (hres j)
    simpa [bwRes, colPoly_zero, coeff_colPoly] using this
  have h0 := poly_eq_zero_of_vanish domain (polyOf_mem _) univ (by simpa using hm')
    fun j _ ↦ hj j
  simpa [coeff_polyOf] using congrArg (fun p ↦ p.coeff a) h0

omit [Fintype ι] in
/-- **Step 2b** (`bw_few_zero_cols`): for `E ≠ 0` of `X`-degree `< m`, `E(x_j, Z) = 0` at fewer
than `m` positions. -/
theorem bw_few_zero_cols (domain : ι ↪ F) {m T : ℕ} {E : Fin m → Fin T → F} (hE : E ≠ 0)
    (S : Finset ι) (hS : ∀ j ∈ S, colPoly E (domain j) = 0) : S.card + 1 ≤ m := by
  classical
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hE
  obtain ⟨b, hb⟩ := Function.ne_iff.1 ha
  set p := polyOf fun a ↦ E a b
  have hp0 : p ≠ 0 := fun h0 ↦ hb (by simpa [p, coeff_polyOf] using congrArg (coeff · a) h0)
  have hsub : (S.image domain).val ⊆ p.roots := by
    intro y hy
    simp only [Finset.mem_val, mem_image] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [mem_roots hp0, IsRoot, ← coeff_colPoly, hS j hj, coeff_zero]
  have h1 := card_le_degree_of_subset_roots hsub
  rw [card_image_of_injective _ domain.injective] at h1
  have := (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 (polyOf_mem fun a ↦ E a b))
  omega

/-! ## The bad set of a line -/

variable [DecidableEq F]

/-- The positions where two single words agree. -/
def wAgree (u w : ι → F) : Finset ι := univ.filter fun j ↦ u j = w j

/-- The positions where `u₀ = v₀` and `u₁ = v₁` (the joint agreement of two pairs of words). -/
def wAgree₂ (u₀ u₁ v₀ v₁ : ι → F) : Finset ι := univ.filter fun j ↦ u₀ j = v₀ j ∧ u₁ j = v₁ j

omit [Field F] in
@[simp] theorem mem_wAgree {u w : ι → F} {j : ι} : j ∈ wAgree u w ↔ u j = w j := by
  simp [wAgree]

omit [Field F] in
@[simp] theorem mem_wAgree₂ {u₀ u₁ v₀ v₁ : ι → F} {j : ι} :
    j ∈ wAgree₂ u₀ u₁ v₀ v₁ ↔ u₀ j = v₀ j ∧ u₁ j = v₁ j := by
  simp [wAgree₂]

/-- The **bad set** of the line `u₀ + z u₁` (FR `lineBad`, direction form): the `z` for which
`u₀ + z u₁` agrees with a codeword `w` on at least `n − e` positions, but no pair of codewords has
joint agreement with `(u₀, u₁)` equal to that agreement set. -/
def lineBad (C : Submodule F (ι → F)) (e : ℕ) (u₀ u₁ : ι → F) : Set F :=
  {z | ∃ w ∈ C, Fintype.card ι - e ≤ (wAgree (u₀ + z • u₁) w).card ∧
    ¬ ∃ v₀ ∈ C, ∃ v₁ ∈ C, wAgree₂ u₀ u₁ v₀ v₁ = wAgree (u₀ + z • u₁) w}

/-- The count the proof gives: `k e + n`. -/
def lineMca (n k e : ℕ) : ℕ := k * e + n

omit [Fintype ι] [DecidableEq F] in
/-- At a position where `(u₀, u₁) ≠ (v₀, v₁)`, `u₀ + z u₁ = v₀ + z v₁` holds only at
`z = (v₀ − u₀) / (u₁ − v₁)`. -/
theorem line_eq_root {a₀ a₁ b₀ b₁ z : F} (hne : ¬ (a₀ = b₀ ∧ a₁ = b₁))
    (h : a₀ + z * a₁ = b₀ + z * b₁) : z = (b₀ - a₀) / (a₁ - b₁) := by
  by_cases hc : a₁ - b₁ = 0
  · exfalso; apply hne
    have h1 : a₁ = b₁ := sub_eq_zero.mp hc
    exact ⟨by rw [h1] at h; linear_combination h, h1⟩
  · field_simp
    linear_combination h

/-- **The line cover** (FR `mca_ud_line_cover`, direction form): for any field `F`, any
`domain : ι ↪ F` and `2e + k ≤ n`, the bad set of every line is contained in a finite set of at
most `k e + n` elements. -/
theorem lineBad_cover [DecidableEq ι] (domain : ι ↪ F) {k e : ℕ}
    (h : 2 * e + k ≤ Fintype.card ι) (u₀ u₁ : ι → F) :
    ∃ B : Finset F, B.card ≤ lineMca (Fintype.card ι) k e ∧
      lineBad (rsCode domain k) e u₀ u₁ ⊆ B := by
  set n := Fintype.card ι with hn
  -- step 1: the interpolating pair
  obtain ⟨E, N, hne, hres⟩ := bw_exists domain u₀ u₁ h
  have hE := bw_E_ne domain (by omega) hne hres
  -- step 2: `k` positions where `E(x_j, Z) ≠ 0`, and the interpolated line
  have hfew := bw_few_zero_cols domain hE (univ.filter fun j ↦ colPoly E (domain j) = 0)
    fun j hj ↦ (mem_filter.1 hj).2
  obtain ⟨J, hJA, hJ⟩ : ∃ J ⊆ univ.filter (fun j ↦ ¬ colPoly E (domain j) = 0), J.card = k := by
    apply exists_subset_card_eq
    have := card_filter_add_card_filter_not (s := (univ : Finset ι))
      fun j ↦ colPoly E (domain j) = 0
    rw [card_univ] at this
    omega
  obtain ⟨v₀, hv₀, hv₀J⟩ := exists_mem_rsCode_eqOn domain J hJ.le u₀
  obtain ⟨v₁, hv₁, hv₁J⟩ := exists_mem_rsCode_eqOn domain J hJ.le u₁
  -- the cover
  let S₁ := J.biUnion fun j ↦ (colPoly E (domain j)).roots.toFinset
  let S₂ := univ.image fun j ↦ (v₀ j - u₀ j) / (u₁ j - v₁ j)
  refine ⟨S₁ ∪ S₂, ?_, ?_⟩
  · have h1 : S₁.card ≤ k * e := by
      refine (card_biUnion_le).trans ((sum_le_card_nsmul _ _ e fun j hj ↦ ?_).trans
        (by rw [hJ, smul_eq_mul]))
      have := (natDegree_lt_iff_degree_lt (mem_filter.1 (hJA hj)).2).2
        (mem_degreeLT.1 (colPoly_mem E (domain j)))
      exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (by omega))
    have h2 : S₂.card ≤ n := card_image_le.trans (by simp [hn])
    exact (card_union_le _ _).trans (by unfold lineMca; omega)
  rintro z ⟨w, hw, hcl, hnot⟩
  by_contra hzB
  obtain ⟨hz1, hz2⟩ := not_or.1 (mt mem_union.2 hzB)
  apply hnot
  refine ⟨v₀, hv₀, v₁, hv₁, ?_⟩
  set uz := u₀ + z • u₁
  have hVz : v₀ + z • v₁ ∈ rsCode domain k := add_mem hv₀ (Submodule.smul_mem _ _ hv₁)
  -- step 3: `w` is the line's codeword at `z`
  have hwV : w = v₀ + z • v₁ := by
    obtain ⟨P, hP, hPw⟩ := mem_rsCode_iff_eval.1 hw
    have hspec : ∀ j, (rowPoly N z).eval (domain j) = (rowPoly E z).eval (domain j) * uz j :=
      fun j ↦ by
        have := congrArg (eval z) (hres j)
        simp only [bwRes, eval_sub, eval_mul, eval_add, eval_C, eval_X, eval_zero,
          eval_colPoly, sub_eq_zero] at this
        simpa [uz, smul_eq_mul, mul_comm z] using this
    have hNE := bw_unique domain (a := n - k - e) (k := k) (polyOf_mem _)
      (by rw [show n - k - e + k = n - e by omega]; exact polyOf_mem _) (mem_degreeLT.2 hP) uz
      hspec (wAgree uz w) (by omega) fun j hj ↦ by rw [hPw]; exact mem_wAgree.1 hj
    refine eq_of_mem_code_of_agreeOn domain hw hVz J hJ.ge fun j hj ↦ ?_
    have hEz : (rowPoly E z).eval (domain j) ≠ 0 := fun h0 ↦ hz1 (mem_biUnion.2 ⟨j, hj,
      Multiset.mem_toFinset.2 ((mem_roots (mem_filter.1 (hJA hj)).2).2 (by rwa [IsRoot.def,
        eval_colPoly]))⟩)
    have h1 := hspec j
    rw [hNE, eval_mul] at h1
    rw [← hPw j, show P.eval (domain j) = uz j from mul_left_cancel₀ hEz h1]
    simp [uz, hv₀J j hj, hv₁J j hj]
  -- step 4: the agreement set is the joint one
  rw [hwV]
  ext j
  simp only [mem_wAgree₂, mem_wAgree, uz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h0, h1⟩; rw [h0, h1]
  · intro hj
    by_contra hnj
    exact hz2 (mem_image.2 ⟨j, mem_univ _, (line_eq_root hnj hj).symm⟩)

end LeanVM.Protocol.Whir.Ud
end
-- ===== end of `LvmUdBW` =====

/-!
# Folding preserves lists in the unique-decoding range (per fold challenge)

leanVM's WHIR round-by-round analysis (`Whir/Sound/Code.lean`, `card_foldStep_bad_le`) folds one
coordinate per sumcheck round, and consumes, per level code, a list bound and a count of the
challenges at which folding creates a list member that is not the fold of one
(`foldBad`, Annex B `lem:fold-list`). This module proves both in the unique-decoding range
`n + k ≤ 2 A` for `RS[F, domain, k]` at agreement threshold `A`:

* `card_mcaBad_le_ud`: the MCA event of a pair of rows has at most `mcaUd n k A = k (n − A) + n`
  challenges (`McaBad ⊆ lineBad`, then `lineBad_cover`);
* `card_foldBad_le_ud`: **the fold-list count**, at most `|ρ| · mcaUd n k A` challenges for a word
  with rows `Bool × ρ` (leanVM's `card_foldBad_le_of_mca`, the row-by-row union);
* `CodeFacts`, `codeFacts_ud`: the per-level hypothesis of the WHIR analysis (uniqueness at `k`,
  `k ≤ thr`, `listMax`, `mcaMax`) and its unique-decoding instance `listMax = 1`,
  `mcaMax = mcaUd n k A`; `udThr`, `codeFacts_udLevel` for `n = 2^(κ+R)`, `k = 2^κ`;
* `card_foldLuck_le`: per fold challenge, at most `n` challenges make a column on which two
  interleaved words differ agree after the fold (the extractor's luck, BLUEPRINT §6.2).
-/

namespace LeanVM.Protocol.Whir

open Finset

variable {F : Type*} [Field F] {ι ρ σ : Type*}

/-! ## One coordinate (leanVM `ToArkLib/Whir/Fold`) -/

/-- **The fold at `s`** of an interleaved word with rows `Bool × ρ`:
`fold s O u = (1 - s) O (false, u) + s O (true, u)`. -/
def fold (s : F) (O : Bool × ρ → ι → F) : ρ → ι → F :=
  fun u x ↦ (1 - s) * O (false, u) x + s * O (true, u) x

/-- The fold on the affine line through `O (false, u)` in direction `O (true, u) - O (false, u)`. -/
theorem fold_apply_eq_line (s : F) (O : Bool × ρ → ι → F) (u : ρ) (x : ι) :
    fold s O u x = O (false, u) x + s * (O (true, u) x - O (false, u) x) := by
  simp only [fold]; ring

/-- A folded row is a linear combination of the two rows. -/
theorem fold_apply_eq_smul (s : F) (O : Bool × ρ → ι → F) (u : ρ) :
    fold s O u = (1 - s) • O (false, u) + s • O (true, u) := by
  funext x; simp [fold]

/-- Folding keeps interleaved codewords of a linear code. -/
theorem isInterleavedCodeword_fold (C : Submodule F (ι → F)) {U : Bool × ρ → ι → F}
    (hU : IsInterleavedCodeword C U) (s : F) : IsInterleavedCodeword C (fold s U) := fun u ↦ by
  rw [fold_apply_eq_smul]
  exact C.add_mem (C.smul_mem _ (hU _)) (C.smul_mem _ (hU _))

/-- Folding keeps agreement on a set. -/
theorem AgreeOn.fold {O U : Bool × ρ → ι → F} {S : Finset ι} (h : AgreeOn O U S) (s : F) :
    AgreeOn (Whir.fold s O) (Whir.fold s U) S := fun u x hx ↦ by
  simp only [Whir.fold, h (false, u) x hx, h (true, u) x hx]

/-- **Folding commutes with decoding** (Annex B, `fact:fold-decode`): for a linear encoder
applied row by row, the fold of the encoded word is the encoding of the folded messages. -/
theorem fold_encoder (enc : (σ → F) →ₗ[F] (ι → F)) (s : F) (g : Bool × ρ → σ → F) :
    fold s (fun r ↦ enc (g r)) = fun u ↦ enc (fold s g u) := by
  funext u
  rw [fold_apply_eq_smul, fold_apply_eq_smul, map_add, map_smul, map_smul]

/-- **The decoded message of a fold.** For an injective linear encoder, a row of the fold of an
encoded word decodes to the fold of the messages. -/
theorem eq_fold_of_encoder (enc : (σ → F) →ₗ[F] (ι → F)) (henc : Function.Injective enc)
    (s : F) (g : Bool × ρ → σ → F) (u : ρ) {m : σ → F}
    (hm : fold s (fun r ↦ enc (g r)) u = enc m) : m = fold s g u :=
  henc (hm.symm.trans (congrFun (fold_encoder enc s g) u))

section List

variable [Fintype F] [Fintype ι] [Fintype ρ]

/-- **The fold of a list member is in the list of the fold.** -/
theorem fold_mem_iList (C : Submodule F (ι → F)) {A : ℕ} {O U : Bool × ρ → ι → F}
    (hU : U ∈ iList C A O) (s : F) : fold s U ∈ iList C A (fold s O) := by
  rw [mem_iList] at hU ⊢
  obtain ⟨hcw, S, hS, hagree⟩ := hU
  exact ⟨isInterleavedCodeword_fold C hcw s, S, hS, hagree.fold s⟩

/-- **The inclusion that always holds** (Annex B, `lem:fold-list`, `⊇`): the fold of the list is
contained in the list of the fold. -/
theorem image_fold_iList_subset [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F))
    (A : ℕ) (O : Bool × ρ → ι → F) (s : F) :
    (iList C A O).image (fold s) ⊆ iList C A (fold s O) := by
  intro V hV
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hV
  exact fold_mem_iList C hU s

/-- The challenges at which folding the list differs from the list of the fold: the bad event of
Annex B, `lem:fold-list`. -/
noncomputable def foldBad [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F)) (A : ℕ)
    (O : Bool × ρ → ι → F) : Finset F :=
  univ.filter fun s ↦ iList C A (fold s O) ≠ (iList C A O).image (fold s)

theorem mem_foldBad [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F)) (A : ℕ)
    (O : Bool × ρ → ι → F) (s : F) :
    s ∈ foldBad C A O ↔ iList C A (fold s O) ≠ (iList C A O).image (fold s) := by
  simp [foldBad]

/-- A challenge is good as soon as every member of the list of the fold is a fold of a member of
the list. -/
theorem not_mem_foldBad_of_subset [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F))
    (A : ℕ) (O : Bool × ρ → ι → F) (s : F)
    (h : ∀ V ∈ iList C A (fold s O), ∃ W ∈ iList C A O, fold s W = V) :
    s ∉ foldBad C A O := by
  rw [mem_foldBad, not_not]
  refine Finset.Subset.antisymm (fun V hV ↦ ?_) (image_fold_iList_subset C A O s)
  obtain ⟨W, hW, rfl⟩ := h V hV
  exact Finset.mem_image_of_mem _ hW

/-- **The MCA event** for the affine line `u₀ + s u₁` at threshold `A` (Annex B, the event of
`thm:mca-udr` and `thm:mca-johnson`): on some set of at least `A` coordinates the combination
agrees with a codeword while the pair does not agree with the interleaved code. -/
def McaBad (C : Submodule F (ι → F)) (A : ℕ) (u₀ u₁ : ι → F) (s : F) : Prop :=
  ∃ S : Finset ι, A ≤ S.card ∧ (∃ c ∈ C, ∀ x ∈ S, u₀ x + s * u₁ x = c x) ∧
    ¬ ∃ c₀ ∈ C, ∃ c₁ ∈ C, ∀ x ∈ S, u₀ x = c₀ x ∧ u₁ x = c₁ x

open Classical in
/-- **The fold-list lemma, the Annex's argument** (Annex B, `lem:fold-list`, count form). For a
linear code in which codewords agreeing on `A` coordinates are equal, if every pair of words has
at most `E` challenges with the MCA event at threshold `A`, then every interleaved word with
rows `Bool × ρ` has at most `|ρ| E` challenges with `Λ(fold s O) ≠ fold s '' Λ(O)`. -/
theorem card_foldBad_le_of_mca [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F))
    {A E : ℕ}
    (huniq : ∀ c ∈ C, ∀ c' ∈ C, ∀ S : Finset ι, A ≤ S.card → (∀ x ∈ S, c x = c' x) → c = c')
    (hmca : ∀ u₀ u₁ : ι → F, (univ.filter fun s ↦ McaBad C A u₀ u₁ s).card ≤ E)
    (O : Bool × ρ → ι → F) :
    (foldBad C A O).card ≤ Fintype.card ρ * E := by
  classical
  let ex : ρ → Finset F := fun u ↦
    univ.filter fun s ↦ McaBad C A (O (false, u)) (fun x ↦ O (true, u) x - O (false, u) x) s
  refine (Finset.card_le_card (t := univ.biUnion ex) fun s hs ↦ ?_).trans
    ((Finset.card_biUnion_le).trans ?_)
  · by_contra hsex
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists, ex,
      Finset.mem_filter] at hsex
    refine not_mem_foldBad_of_subset _ A O s (fun V hV ↦ ?_) hs
    obtain ⟨hVcw, S, hS, hagree⟩ := (mem_iList _ A _ V).mp hV
    have hpair : ∀ u, ∃ c₀ ∈ C, ∃ c₁ ∈ C, ∀ x ∈ S,
        O (false, u) x = c₀ x ∧ O (true, u) x - O (false, u) x = c₁ x := by
      intro u
      by_contra hno
      exact hsex u ⟨S, hS, ⟨V u, hVcw u, fun x hx ↦ by
        rw [← fold_apply_eq_line]; exact hagree u x hx⟩, hno⟩
    choose c₀ hc₀ c₁ hc₁ hc using hpair
    let W : Bool × ρ → ι → F := fun r ↦ if r.1 then c₀ r.2 + c₁ r.2 else c₀ r.2
    have hWcw : IsInterleavedCodeword C W := by
      rintro ⟨b, u⟩
      cases b
      · simpa [W] using hc₀ u
      · simpa [W] using C.add_mem (hc₀ u) (hc₁ u)
    have hWagree : AgreeOn O W S := by
      rintro ⟨b, u⟩ x hx
      cases b
      · simp [W, (hc u x hx).1]
      · simp only [W, ite_true, Pi.add_apply, ← (hc u x hx).1, ← (hc u x hx).2]
        ring
    refine ⟨W, (mem_iList _ A O W).mpr ⟨hWcw, S, hS, hWagree⟩, funext fun u ↦ ?_⟩
    refine huniq _ (isInterleavedCodeword_fold C hWcw s u) _ (hVcw u) S hS fun x hx ↦ ?_
    rw [← hagree u x hx]
    exact ((hWagree.fold s) u x hx).symm
  · simpa using Finset.sum_le_card_nsmul univ (fun u ↦ (ex u).card) E fun u _ ↦ hmca _ _

end List

/-! ## The unique-decoding counts -/

section UniqueDecoding

variable [Fintype ι] [DecidableEq ι] [DecidableEq F]

/-- The MCA count of a pair of rows in the unique-decoding range: `k (n − A) + n`. -/
def mcaUd (n k A : ℕ) : ℕ := k * (n - A) + n

omit [DecidableEq ι] in
/-- The MCA event at threshold `A ≤ n` is inside the exact-agreement bad set of the line at
`e = n − A`. -/
theorem mcaBad_mem_lineBad (C : Submodule F (ι → F)) {A : ℕ} (hAn : A ≤ Fintype.card ι)
    {u₀ u₁ : ι → F} {s : F} (h : McaBad C A u₀ u₁ s) :
    s ∈ Ud.lineBad C (Fintype.card ι - A) u₀ u₁ := by
  obtain ⟨S, hS, ⟨c, hc, hcS⟩, hno⟩ := h
  have hsub : S ⊆ Ud.wAgree (u₀ + s • u₁) c := fun x hx ↦ by
    simpa [Ud.mem_wAgree, smul_eq_mul] using hcS x hx
  refine ⟨c, hc, ?_, ?_⟩
  · rw [show Fintype.card ι - (Fintype.card ι - A) = A by omega]
    exact hS.trans (card_le_card hsub)
  · rintro ⟨v₀, hv₀, v₁, hv₁, heq⟩
    exact hno ⟨v₀, hv₀, v₁, hv₁, fun x hx ↦ Ud.mem_wAgree₂.1 (heq ▸ hsub hx)⟩

open Classical in
/-- **The MCA count of a pair of rows** in the unique-decoding range `n + k ≤ 2 A`: at most
`k (n − A) + n` challenges `s`. -/
theorem card_mcaBad_le_ud [Fintype F] (domain : ι ↪ F) {k A : ℕ}
    (hA : Fintype.card ι + k ≤ 2 * A) (u₀ u₁ : ι → F) :
    (univ.filter fun s ↦ McaBad (rsCode domain k) A u₀ u₁ s).card ≤
      mcaUd (Fintype.card ι) k A := by
  by_cases hAn : A ≤ Fintype.card ι
  · obtain ⟨B, hB, hsub⟩ := Ud.lineBad_cover domain (k := k) (e := Fintype.card ι - A)
      (by omega) u₀ u₁
    refine (card_le_card fun s hs ↦ ?_).trans hB
    exact hsub (mcaBad_mem_lineBad _ hAn (mem_filter.1 hs).2)
  · refine (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun s _ h ↦ ?_)).le.trans (Nat.zero_le _)
    obtain ⟨S, hS, -⟩ := h
    have : S.card ≤ Fintype.card ι := card_le_univ _
    omega

omit [DecidableEq ι] [DecidableEq F] in
/-- Codewords of `RS[F, domain, k]` agreeing on `A` coordinates are equal when `n + k ≤ 2 A`. -/
theorem uniq_of_ud (domain : ι ↪ F) {k A : ℕ} (hA : Fintype.card ι + k ≤ 2 * A) :
    ∀ c ∈ rsCode domain k, ∀ c' ∈ rsCode domain k, ∀ S : Finset ι, A ≤ S.card →
      (∀ x ∈ S, c x = c' x) → c = c' := fun _ hc _ hc' S hS h ↦
  eq_of_mem_code_of_agreeOn domain hc hc' S (le_card_of_ud hA hS) h

/-- **The fold-list count in the unique-decoding range**: for `n + k ≤ 2 A`, every interleaved
word with rows `Bool × ρ` has at most `|ρ| · (k (n − A) + n)` challenges `s` with
`Λ(fold s O) ≠ fold s '' Λ(O)`. -/
theorem card_foldBad_le_ud [Fintype F] [Fintype ρ] (domain : ι ↪ F) {k A : ℕ}
    (hA : Fintype.card ι + k ≤ 2 * A) (O : Bool × ρ → ι → F) :
    (foldBad (rsCode domain k) A O).card ≤ Fintype.card ρ * mcaUd (Fintype.card ι) k A :=
  card_foldBad_le_of_mca _ (uniq_of_ud domain hA) (card_mcaBad_le_ud domain hA) O

end UniqueDecoding

/-! ## The per-level hypothesis of the WHIR analysis -/

section Facts

variable [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- **The code facts a WHIR level needs** (leanVM `Whir/Sound/Code.lean`, `LevelCode`, with its
Johnson-specific parameters replaced by fields): codewords agreeing on `k` coordinates are equal,
the threshold is at least `k`, every list has at most `listMax` members, and every word with rows
`Bool × ρ` has at most `|ρ| · mcaMax` fold-bad challenges. -/
structure CodeFacts (C : Submodule F (ι → F)) (k thr listMax mcaMax : ℕ) : Prop where
  /-- Two codewords agreeing on `k` coordinates are equal. -/
  uniq : ∀ c ∈ C, ∀ c' ∈ C, ∀ S : Finset ι, k ≤ S.card → (∀ x ∈ S, c x = c' x) → c = c'
  /-- The threshold is at least the dimension (`LevelCode.two_pow_le_thr`). -/
  k_le_thr : k ≤ thr
  /-- **The list bound** (`LevelCode.card_iList_le`). -/
  card_iList_le : ∀ (ρ : Type) [Fintype ρ] (O : ρ → ι → F), (iList C thr O).card ≤ listMax
  /-- **The fold-list count** (`LevelCode.card_foldBad_le`). -/
  card_foldBad_le : ∀ (ρ : Type) [Fintype ρ] (O : Bool × ρ → ι → F),
    (foldBad C thr O).card ≤ Fintype.card ρ * mcaMax

/-- **The unique-decoding instance**: for `k ≤ n` and `n + k ≤ 2 A`, `RS[F, domain, k]` at
threshold `A` has `listMax = 1` and `mcaMax = k (n − A) + n`. -/
theorem codeFacts_ud (domain : ι ↪ F) {k A : ℕ} (hk : k ≤ Fintype.card ι)
    (hA : Fintype.card ι + k ≤ 2 * A) :
    CodeFacts (rsCode domain k) k A 1 (mcaUd (Fintype.card ι) k A) where
  uniq _ hc _ hc' S hS h := eq_of_mem_code_of_agreeOn domain hc hc' S hS h
  k_le_thr := by omega
  card_iList_le _ _ O := card_iList_le_one domain hA O
  card_foldBad_le _ _ O := card_foldBad_le_ud domain hA O

/-- The unique-decoding threshold of the level code with `2^κ` messages on `2^(κ+R)` points:
`2^(κ+R−1) + 2^(κ−1)`, the least `A` with `n + k ≤ 2 A`. -/
def udThr (κ R : ℕ) : ℕ := 2 ^ (κ + R - 1) + 2 ^ (κ - 1)

/-- `n + k = 2 · udThr` for `κ ≥ 1`. -/
theorem two_mul_udThr {κ R : ℕ} (hκ : 1 ≤ κ) : 2 * udThr κ R = 2 ^ (κ + R) + 2 ^ κ := by
  obtain ⟨a, rfl⟩ : ∃ a, κ = a + 1 := ⟨κ - 1, by omega⟩
  rw [udThr, show a + 1 + R - 1 = a + R by omega, show a + 1 - 1 = a by omega,
    show a + 1 + R = a + R + 1 by omega, pow_succ, pow_succ]
  ring

/-- The threshold is at most the block length. -/
theorem udThr_le {κ : ℕ} (R : ℕ) (hκ : 1 ≤ κ) : udThr κ R ≤ 2 ^ (κ + R) := by
  have h := two_mul_udThr (R := R) hκ
  have hle : 2 ^ κ ≤ 2 ^ (κ + R) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (κ + R) = X at h hle
  omega

/-- **The query factor**: `(udThr − 1)/n < (1 + 2^-R)/2`, as `2^(R+1) (udThr − 1) < (2^R + 1) n`
(the per-query escape `((thr − 1)/n)^t` of leanVM's `eQuery` against BLUEPRINT §3.1's
`((1 + 2^-R)/2)^t`). -/
theorem udThr_query {κ R : ℕ} (hκ : 1 ≤ κ) :
    2 ^ (R + 1) * (udThr κ R - 1) < (2 ^ R + 1) * 2 ^ (κ + R) := by
  have h := two_mul_udThr (R := R) hκ
  have hpos : 1 ≤ udThr κ R := by
    have h1 : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
    generalize 2 ^ (κ + R) = X at h
    omega
  have hr : 0 < 2 ^ R := Nat.two_pow_pos R
  calc 2 ^ (R + 1) * (udThr κ R - 1) < 2 ^ (R + 1) * udThr κ R :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    _ = 2 ^ R * (2 * udThr κ R) := by rw [pow_succ]; ring
    _ = 2 ^ R * (2 ^ (κ + R) + 2 ^ κ) := by rw [h]
    _ ≤ (2 ^ R + 1) * 2 ^ (κ + R) := by
        rw [add_mul, one_mul, mul_add, show 2 ^ R * 2 ^ κ = 2 ^ (κ + R) by rw [← pow_add, add_comm]]

/-- The MCA count of the level code: `2^κ (2^(κ+R) − udThr) + 2^(κ+R)`. -/
def udMca (κ R : ℕ) : ℕ := mcaUd (2 ^ (κ + R)) (2 ^ κ) (udThr κ R)

/-- **The unique-decoding level code**: `RS[F, domain, 2^κ]` on `2^(κ+R)` points at threshold
`udThr κ R` has `listMax = 1`, `mcaMax = udMca κ R`. -/
theorem codeFacts_udLevel {κ R : ℕ} (hκ : 1 ≤ κ) (domain : Fin (2 ^ (κ + R)) ↪ F) :
    CodeFacts (rsCode domain (2 ^ κ)) (2 ^ κ) (udThr κ R) 1 (udMca κ R) := by
  have hn : Fintype.card (Fin (2 ^ (κ + R))) = 2 ^ (κ + R) := Fintype.card_fin _
  have hk : 2 ^ κ ≤ 2 ^ (κ + R) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := codeFacts_ud domain (k := 2 ^ κ) (A := udThr κ R) (by rw [hn]; exact hk)
    (by rw [hn, two_mul_udThr hκ])
  rwa [hn] at h

end Facts

/-! ## Controls -/

section Controls

/-- **The MCA counts of BLUEPRINT §3.1's levels** (`C_main` levels 0–3, then `C_rec`):
`udMca κ R = 2^κ e + n` with `n = 2^(κ+R)`, `e = n − udThr κ R`. -/
theorem udMca_levels : udMca 20 1 = 2 ^ 39 + 2 ^ 21 ∧ udMca 16 2 = 3 * 2 ^ 31 + 2 ^ 18 ∧
    udMca 12 3 = 7 * 2 ^ 23 + 2 ^ 15 ∧ udMca 8 4 = 15 * 2 ^ 15 + 2 ^ 12 ∧
    udMca 13 2 = 3 * 2 ^ 25 + 2 ^ 15 := by
  simp only [udMca, mcaUd, udThr]
  norm_num

/-- **The fold escape numerators** `2 · listMax + 2^(ℓ−1) · mcaMax` of those levels (leanVM `eFold`
times `|E| = 2^192`, `ℓ = 6, 4, 4, 4` and `6`): below `2^45, 2^36, 2^29, 2^22, 2^32`, so the fold
escapes are at most `2^-147, 2^-156, 2^-163, 2^-170, 2^-160`. -/
theorem eFold_num_levels : 2 * 1 + 2 ^ 5 * udMca 20 1 < 2 ^ 45 ∧
    2 * 1 + 2 ^ 3 * udMca 16 2 < 2 ^ 36 ∧ 2 * 1 + 2 ^ 3 * udMca 12 3 < 2 ^ 29 ∧
    2 * 1 + 2 ^ 3 * udMca 8 4 < 2 ^ 22 ∧ 2 * 1 + 2 ^ 5 * udMca 13 2 < 2 ^ 32 := by
  simp only [udMca, mcaUd, udThr]
  norm_num

/-- **Negative control of `card_iList_le_one`**: without `n + k ≤ 2 A` the list can have two
members. With `n = 2`, `k = 1`, `A = 1` (`n + k = 3 > 2 A`), the word `(0, 1)` is close to both
constant codewords `(0, 0)` and `(1, 1)`. -/
theorem two_le_card_iList_not_ud [Fintype F] (domain : Fin 2 ↪ F) :
    2 ≤ (iList (rsCode domain 1) 1 fun (_ : Unit) ↦ ![(0 : F), 1]).card := by
  have hconst (a : F) : (fun _ : Fin 2 ↦ a) ∈ rsCode domain 1 :=
    mem_rsCode_iff_eval.mpr ⟨Polynomial.C a, (Polynomial.degree_C_le).trans_lt (by norm_num),
      fun _ ↦ Polynomial.eval_C⟩
  refine Finset.one_lt_card.mpr ⟨fun _ _ ↦ 0, ?_, fun _ _ ↦ 1, ?_, fun h ↦ ?_⟩
  · refine (mem_iList _ _ _ _).mpr ⟨fun _ ↦ hconst 0, {0}, by simp, fun _ x hx ↦ ?_⟩
    rw [Finset.mem_singleton.mp hx]; rfl
  · refine (mem_iList _ _ _ _).mpr ⟨fun _ ↦ hconst 1, {1}, by simp, fun _ x hx ↦ ?_⟩
    rw [Finset.mem_singleton.mp hx]; rfl
  · exact zero_ne_one (congrFun (congrFun h ()) 0)

/-- **Positive control of `McaBad`**: the event happens in the unique-decoding range. With `n = 2`,
`k = 1`, `A = 2` (`n + k ≤ 2 A`), the line through `(0, 1)` in direction `(1, 0)` is the constant
codeword `(1, 1)` at `s = 1`, while `(0, 1)` agrees with no constant codeword on both positions. -/
theorem mcaBad_ud_example (domain : Fin 2 ↪ F) :
    McaBad (rsCode domain 1) 2 ![(0 : F), 1] ![(1 : F), 0] 1 := by
  refine ⟨univ, by simp, ⟨fun _ ↦ 1, mem_rsCode_iff_eval.mpr ⟨Polynomial.C 1,
    (Polynomial.degree_C_le).trans_lt (by norm_num), fun _ ↦ Polynomial.eval_C⟩, fun x _ ↦ ?_⟩, ?_⟩
  · fin_cases x <;> simp
  · rintro ⟨c₀, hc₀, _, _, h⟩
    obtain ⟨p, hp, hpc⟩ := mem_rsCode_iff_eval.mp hc₀
    have hp0 : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hp)
    have e0 := (h 0 (mem_univ _)).1
    have e1 := (h 1 (mem_univ _)).1
    rw [← hpc, hp0, Polynomial.eval_C] at e0 e1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    exact zero_ne_one (e0.trans e1.symm)

end Controls

/-! ## The extractor's luck, per fold challenge -/

section Luck

variable [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype ρ]

omit [Fintype F] [DecidableEq ι] in
/-- Folding never shrinks the agreement set. -/
theorem agreeSet_subset_agreeSet_fold (O U : Bool × ρ → ι → F) (s : F) :
    agreeSet O U ⊆ agreeSet (fold s O) (fold s U) :=
  (agreeOn_iff_subset_agreeSet _ _ _).mp
    (((agreeOn_iff_subset_agreeSet O U _).mpr subset_rfl).fold s)

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype ρ] in
/-- A fold `(1 − s) a₀ + s a₁ = (1 − s) b₀ + s b₁` of two differing pairs pins `s`. -/
theorem fold_root {a₀ a₁ b₀ b₁ s : F} (hne : ¬ (a₀ = b₀ ∧ a₁ = b₁))
    (h : (1 - s) * a₀ + s * a₁ = (1 - s) * b₀ + s * b₁) :
    s = (a₀ - b₀) / ((a₀ - b₀) - (a₁ - b₁)) := by
  by_cases hc : (a₀ - b₀) - (a₁ - b₁) = 0
  · exfalso
    have h0 : a₀ - b₀ = 0 := by linear_combination h + s * hc
    have h1 : a₁ - b₁ = 0 := by linear_combination h0 - hc
    exact hne ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩
  · rw [eq_div_iff hc]
    linear_combination (-1 : F) * h

/-- **The luck count**: at most `n` challenges `s` make a column on which `O` and `U` differ agree
after the fold (for each such column some row pair differs, and `(1 − s) D₀ + s D₁ = 0` with
`(D₀, D₁) ≠ 0` has at most one root). -/
theorem card_foldLuck_le (O U : Bool × ρ → ι → F) :
    (univ.filter fun s ↦ ¬ agreeSet (fold s O) (fold s U) ⊆ agreeSet O U).card ≤
      Fintype.card ι := by
  classical
  -- the root of column `x`, read off a row pair `u` that differs at `x`
  let root : ι → F := fun x ↦
    if h : ∃ u, ¬ (O (false, u) x = U (false, u) x ∧ O (true, u) x = U (true, u) x) then
      (O (false, h.choose) x - U (false, h.choose) x) /
        ((O (false, h.choose) x - U (false, h.choose) x) -
          (O (true, h.choose) x - U (true, h.choose) x))
    else 0
  refine (card_le_card (t := univ.image root) fun s hs ↦ ?_).trans
    (card_image_le.trans_eq card_univ)
  obtain ⟨x, hxf, hx⟩ := not_subset.mp (mem_filter.mp hs).2
  have hex : ∃ u, ¬ (O (false, u) x = U (false, u) x ∧ O (true, u) x = U (true, u) x) := by
    by_contra hall
    push Not at hall
    exact hx ((mem_agreeSet O U x).mpr fun ⟨b, u⟩ ↦ by cases b <;> simp [hall u])
  refine mem_image.mpr ⟨x, mem_univ _, ?_⟩
  have hfx := (mem_agreeSet _ _ x).mp hxf hex.choose
  simp only [fold] at hfx
  simp only [root, hex, ↓reduceDIte]
  exact (fold_root hex.choose_spec hfx).symm

omit [Fintype F] [DecidableEq ι] in
/-- Off the luck event the agreement set of the fold is that of the word. -/
theorem agreeSet_fold_eq {O U : Bool × ρ → ι → F} {s : F}
    (hs : agreeSet (fold s O) (fold s U) ⊆ agreeSet O U) :
    agreeSet (fold s O) (fold s U) = agreeSet O U :=
  Finset.Subset.antisymm hs (agreeSet_subset_agreeSet_fold O U s)

end Luck

end LeanVM.Protocol.Whir
