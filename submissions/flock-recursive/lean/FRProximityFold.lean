-- G6: this module also holds the former modules `FRProximityBW`, `FRProximityLine` (one section each, in import order).
import FRRS
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Field.Basic

section G6_FRProximityBW

-- New for `flock-recursive` (BLUEPRINT §5.3 step (1), B-5). Nothing is copied; the univariate
-- Berlekamp–Welch uniqueness is the textbook argument.

/-!
# Unique decoding of the Reed–Solomon code (BLUEPRINT §5.3 (1))

Generic over a field `K` and `n` distinct points `x : Fin n → K`, for `RS[K, x, k]` and an error
bound `e` with `2e + k ≤ n` (that is, `2e < d = n − k + 1`):

* `close_unique`: a word has at most one codeword within agreement `n − e`;
* `bw_unique`: **Berlekamp–Welch uniqueness**: if `N(x_j) = E(x_j) · u_j` at every position,
  `deg E ≤ a`, `deg N < a + k`, and `u` agrees with `P(x_j)` (`deg P < k`) at `a + k` positions,
  then `N = E · P`;
* `mul_mem_degreeLT`, `poly_eq_zero_of_vanish`: the degree facts used here and in
  `FRProximityLine`.
-/

namespace FR

open Polynomial Finset

variable {K : Type*} [Field K] {n : ℕ}

/-- `deg p ≤ a`, `deg q < b` give `deg (p q) < a + b`. -/
theorem mul_mem_degreeLT {a b : ℕ} {p q : K[X]} (hp : p ∈ degreeLT K (a + 1))
    (hq : q ∈ degreeLT K b) : p * q ∈ degreeLT K (a + b) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hq0 : q = 0
  · simp [hq0]
  have h1 := (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp)
  have h2 := (natDegree_lt_iff_degree_lt hq0).2 (mem_degreeLT.1 hq)
  rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt (mul_ne_zero hp0 hq0), natDegree_mul hp0 hq0]
  omega

/-- A polynomial of degree `< m` vanishing at `m` of the distinct points `x j` is zero. -/
theorem poly_eq_zero_of_vanish {x : Fin n → K} (hx : Function.Injective x) {m : ℕ} {p : K[X]}
    (hp : p ∈ degreeLT K m) (S : Finset (Fin n)) (hS : m ≤ S.card)
    (h : ∀ j ∈ S, p.eval (x j) = 0) : p = 0 := by
  classical
  exact poly_eq_of_agree hx (mem_degreeLT.1 hp) (by simp) S hS fun j hj => by simp [h j hj]

variable [DecidableEq K]

/-- **`close_unique`**: if `2e + k ≤ n`, at most one codeword of `RS[K, x, k]` agrees with `u` on
`n − e` positions. -/
theorem close_unique {x : Fin n → K} (hx : Function.Injective x) {k e : ℕ} (h : 2 * e + k ≤ n)
    {u w w' : Fin n → K} (hw : w ∈ rsCode x k) (hw' : w' ∈ rsCode x k)
    (hc : n - e ≤ (agreeSet u w).card) (hc' : n - e ≤ (agreeSet u w').card) : w = w' := by
  refine rs_eq_of_agree hx hw hw' (agreeSet u w ∩ agreeSet u w') ?_ fun j hj => ?_
  · have h1 := card_union_add_card_inter (agreeSet u w) (agreeSet u w')
    have h2 : (agreeSet u w ∪ agreeSet u w').card ≤ n := by
      simpa using card_le_univ (agreeSet u w ∪ agreeSet u w')
    omega
  · obtain ⟨h1, h2⟩ := mem_inter.1 hj
    exact (mem_agreeSet.1 h1).symm.trans (mem_agreeSet.1 h2)

omit [DecidableEq K] in
/-- **`bw_unique`** (Berlekamp–Welch): if `N(x_j) = E(x_j) · u_j` for every `j`, `deg E ≤ a`,
`deg N < a + k`, `deg P < k`, and `u_j = P(x_j)` on a set `S` of `a + k` positions, then
`N = E · P`. -/
theorem bw_unique {x : Fin n → K} (hx : Function.Injective x) {a k : ℕ} {E N P : K[X]}
    (hE : E ∈ degreeLT K (a + 1)) (hN : N ∈ degreeLT K (a + k)) (hP : P ∈ degreeLT K k)
    (u : Fin n → K) (hEN : ∀ j, N.eval (x j) = E.eval (x j) * u j) (S : Finset (Fin n))
    (hS : a + k ≤ S.card) (hagree : ∀ j ∈ S, u j = P.eval (x j)) : N = E * P := by
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_vanish hx (sub_mem hN (mul_mem_degreeLT hE hP)) S hS fun j hj => ?_
  rw [eval_sub, eval_mul, hEN, hagree j hj, sub_self]

end FR

end G6_FRProximityBW

section G6_FRProximityLine

-- New for `flock-recursive` (BLUEPRINT §5.3, B-5, BP-C-M8). The argument is BCIKS20 Thm 4.1's
-- unique-decoding case reorganised (see the module docstring); nothing is copied from ArkLib.

/-!
# Mutual correlated agreement for lines, unique-decoding regime (`mca_ud_line`, BLUEPRINT §5.3)

Generic over **any** field `K`, any `n` distinct points `x : Fin n → K`, the code
`C = RS[K, x, k]` and an error bound `e` with `2e + k ≤ n` (`2e < d = n − k + 1`). For words
`u₀ u₁ : K^n`, `lineBad C e u₀ u₁` is the set of `z` for which `u_z := u₀ + z (u₁ − u₀)` has a
codeword `w` with `n − e` agreements but **no** pair `v₀ v₁ ∈ C` whose joint agreement with
`(u₀, u₁)` is exactly `agreeSet u_z w`. **`mca_ud_line_cover`**: that set is covered by a finite set
of at most `cMca n k e = k e + n` elements; `mca_ud_line` is the cardinality form over a finite
field. No threshold on the number of close `z` is needed.

The proof (Berlekamp–Welch with a variable `Z`, solved by counting rather than by a rank argument
over `K(Z)`):

1. **Interpolation** (`bw_exists`). With `a := n − k − e ≥ e`, there are coefficient arrays
   `E` (`X`-degree `≤ a`, `Z`-degree `≤ e`) and `N` (`X`-degree `< n − e`, `Z`-degree `≤ e + 1`),
   not both zero, with `N(x_j, Z) = E(x_j, Z) · (u₀_j + Z (u₁_j − u₀_j))` in `K[Z]` for every `j`:
   `(a+1)(e+1) + (n−e)(e+2)` unknowns against `n (e+2)` linear equations, and
   `(a+1)(e+1) ≥ (e+1)² > e (e+2)`.
2. `E ≠ 0` (else `N` vanishes at `n` points with `X`-degree `< n`), so `E(x_j, Z) = 0` for at
   most `a` positions (`bw_few_zero_cols`); pick `k` positions `J` with `E(x_j, Z) ≠ 0`, and let
   `v₀, v₁ ∈ C` interpolate `u₀, u₁` on `J`.
3. For `z` off the `≤ k e` roots of the `E(x_j, Z)`, `j ∈ J`, and `u_z` close to `w = P(x)`:
   `bw_unique` gives `N(X, z) = E(X, z) P`, so `u_z = P` on `J`, so `w = v₀ + z (v₁ − v₀)`.
4. Off the agreement set `A` of `(u₀, u₁)` with `(v₀, v₁)`, `u_z − (v₀ + z (v₁ − v₀))` is a nonzero
   affine function of `z` at each position: at most `n` further values of `z` add an agreement.
   For every other close `z` the agreement set is exactly `A`.
-/

namespace FR

open Polynomial Finset

variable {K : Type*} [Field K] {n : ℕ}

/-! ## Coefficient arrays as polynomials -/

/-- The polynomial `Σ_{a<m} d_a X^a`. -/
noncomputable def polyOf {m : ℕ} (d : Fin m → K) : K[X] := ∑ a : Fin m, C (d a) * X ^ (a : ℕ)

theorem polyOf_mem {m : ℕ} (d : Fin m → K) : polyOf d ∈ degreeLT K m :=
  mem_degreeLT.2 (degree_sum_fin_lt d)

theorem eval_polyOf {m : ℕ} (d : Fin m → K) (y : K) :
    (polyOf d).eval y = ∑ a, d a * y ^ (a : ℕ) := by
  simp [polyOf, eval_finsetSum]

theorem coeff_polyOf {m : ℕ} (d : Fin m → K) (a : Fin m) : (polyOf d).coeff a = d a := by
  simp [polyOf, finsetSum_coeff, coeff_X_pow, Fin.val_inj]

theorem polyOf_add {m : ℕ} (d d' : Fin m → K) : polyOf (d + d') = polyOf d + polyOf d' := by
  simp [polyOf, add_mul, sum_add_distrib]

theorem polyOf_smul {m : ℕ} (c : K) (d : Fin m → K) : polyOf (c • d) = C c * polyOf d := by
  simp [polyOf, mul_sum, mul_assoc]

/-- `B(y, Z) = Σ_a y^a B_a(Z)` for the coefficient array `B a b` of `X^a Z^b`. -/
noncomputable def colPoly {m T : ℕ} (B : Fin m → Fin T → K) (y : K) : K[X] :=
  ∑ a : Fin m, C (y ^ (a : ℕ)) * polyOf (B a)

/-- `B(X, z)`. -/
noncomputable def rowPoly {m T : ℕ} (B : Fin m → Fin T → K) (z : K) : K[X] :=
  polyOf fun a => (polyOf (B a)).eval z

theorem eval_colPoly {m T : ℕ} (B : Fin m → Fin T → K) (y z : K) :
    (colPoly B y).eval z = (rowPoly B z).eval y := by
  simp [colPoly, rowPoly, eval_polyOf, eval_finsetSum, mul_comm]

theorem coeff_colPoly {m T : ℕ} (B : Fin m → Fin T → K) (y : K) (t : Fin T) :
    (colPoly B y).coeff t = (polyOf fun a => B a t).eval y := by
  simp only [colPoly, finsetSum_coeff, coeff_C_mul, coeff_polyOf, eval_polyOf]
  exact sum_congr rfl fun a _ => mul_comm _ _

theorem colPoly_mem {m T : ℕ} (B : Fin m → Fin T → K) (y : K) : colPoly B y ∈ degreeLT K T :=
  sum_mem fun a _ => by rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (polyOf_mem _)

theorem colPoly_add {m T : ℕ} (B B' : Fin m → Fin T → K) (y : K) :
    colPoly (B + B') y = colPoly B y + colPoly B' y := by
  simp [colPoly, polyOf_add, mul_add, sum_add_distrib]

theorem colPoly_smul {m T : ℕ} (c : K) (B : Fin m → Fin T → K) (y : K) :
    colPoly (c • B) y = C c * colPoly B y := by
  simp only [colPoly, Pi.smul_apply, polyOf_smul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem colPoly_zero {m T : ℕ} (y : K) : colPoly (0 : Fin m → Fin T → K) y = 0 := by
  simpa using colPoly_smul (0 : K) (0 : Fin m → Fin T → K) y

/-! ## The Berlekamp–Welch system with a variable `Z` -/

/-- The residual `N(x_j, Z) − E(x_j, Z) (u₀_j + Z (u₁_j − u₀_j))` at position `j`. -/
noncomputable def bwRes {m m' T T' : ℕ} (x u₀ u₁ : Fin n → K) (E : Fin m → Fin T → K)
    (N : Fin m' → Fin T' → K) (j : Fin n) : K[X] :=
  colPoly N (x j) - colPoly E (x j) * (C (u₀ j) + X * C (u₁ j - u₀ j))

/-- The residuals' first `T + 1` coefficients, a `K`-linear map of `(E, N)`. -/
noncomputable def bwMap (x u₀ u₁ : Fin n → K) (m m' T : ℕ) :
    ((Fin m → Fin T → K) × (Fin m' → Fin (T + 1) → K)) →ₗ[K] (Fin n → Fin (T + 1) → K) where
  toFun p j t := (bwRes x u₀ u₁ p.1 p.2 j).coeff t
  map_add' p q := by
    funext j t
    simp only [bwRes, Prod.fst_add, Prod.snd_add, colPoly_add, Pi.add_apply]
    rw [← coeff_add]; exact congrArg (coeff · t) (by ring)
  map_smul' c p := by
    funext j t
    simp only [bwRes, Prod.smul_fst, Prod.smul_snd, colPoly_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [← coeff_C_mul]; exact congrArg (coeff · t) (by ring)

theorem bwRes_mem {m m' T : ℕ} (x u₀ u₁ : Fin n → K) (E : Fin m → Fin T → K)
    (N : Fin m' → Fin (T + 1) → K) (j : Fin n) : bwRes x u₀ u₁ E N j ∈ degreeLT K (T + 1) := by
  refine sub_mem (colPoly_mem N _) ?_
  rw [mul_comm, Nat.add_comm T 1]
  refine mul_mem_degreeLT ?_ (colPoly_mem E _)
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE]
  compute_degree!

/-- **Step 1** (`bw_exists`): with `2e + k ≤ n` the system has a nonzero solution with
`X`-degrees `≤ n − k − e`, `< n − e` and `Z`-degrees `≤ e`, `≤ e + 1`. -/
theorem bw_exists (x u₀ u₁ : Fin n → K) {k e : ℕ} (h : 2 * e + k ≤ n) :
    ∃ (E : Fin (n - k - e + 1) → Fin (e + 1) → K) (N : Fin (n - e) → Fin (e + 2) → K),
      (E, N) ≠ 0 ∧ ∀ j, bwRes x u₀ u₁ E N j = 0 := by
  have hdim : Module.finrank K (Fin n → Fin (e + 1 + 1) → K) <
      Module.finrank K ((Fin (n - k - e + 1) → Fin (e + 1) → K) ×
        (Fin (n - e) → Fin (e + 1 + 1) → K)) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
      Fintype.card_fin, mul_one, sum_const, card_univ, smul_eq_mul]
    obtain ⟨a, ha⟩ : ∃ a, n - k - e = e + a := ⟨n - k - e - e, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, n = e + b := ⟨n - e, by omega⟩
    rw [ha, hb, Nat.add_sub_cancel_left]
    ring_nf
    omega
  obtain ⟨p, hp, hp0⟩ :=
    (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := bwMap x u₀ u₁ _ _ _) hdim)
  refine ⟨p.1, p.2, hp0, fun j => ?_⟩
  have hres := bwRes_mem x u₀ u₁ p.1 p.2 j
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hres
  ext t
  rw [coeff_zero]
  by_cases ht : t < e + 2
  · exact congrFun (congrFun (LinearMap.mem_ker.1 hp) j) ⟨t, ht⟩
  · exact hres t (by omega)

/-- **Step 2a**: a solution with `E = 0` and `m' ≤ n` is zero. -/
theorem bw_E_ne {x : Fin n → K} (hx : Function.Injective x) {u₀ u₁ : Fin n → K}
    {m m' T T' : ℕ} (hm' : m' ≤ n) {E : Fin m → Fin T → K} {N : Fin m' → Fin T' → K}
    (hne : (E, N) ≠ 0) (hres : ∀ j, bwRes x u₀ u₁ E N j = 0) : E ≠ 0 := by
  rintro rfl
  apply hne
  ext a t
  · rfl
  have hj : ∀ j, (polyOf fun a => N a t).eval (x j) = 0 := fun j => by
    have := congrArg (fun p => p.coeff t) (hres j)
    simpa [bwRes, colPoly_zero, coeff_colPoly] using this
  have h0 := poly_eq_zero_of_vanish hx (polyOf_mem _) univ (by simpa using hm') fun j _ => hj j
  simpa [coeff_polyOf] using congrArg (fun p => p.coeff a) h0

/-- **Step 2b** (`bw_few_zero_cols`): for `E ≠ 0` of `X`-degree `< m`, `E(x_j, Z) = 0` at fewer
than `m` positions. -/
theorem bw_few_zero_cols {x : Fin n → K} (hx : Function.Injective x) {m T : ℕ}
    {E : Fin m → Fin T → K} (hE : E ≠ 0) (S : Finset (Fin n))
    (hS : ∀ j ∈ S, colPoly E (x j) = 0) : S.card + 1 ≤ m := by
  classical
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hE
  obtain ⟨b, hb⟩ := Function.ne_iff.1 ha
  set p := polyOf fun a => E a b
  have hp0 : p ≠ 0 := fun h0 => hb (by simpa [p, coeff_polyOf] using congrArg (coeff · a) h0)
  have hsub : (S.image x).val ⊆ p.roots := by
    intro y hy
    simp only [Finset.mem_val, mem_image] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [mem_roots hp0, IsRoot, ← coeff_colPoly, hS j hj, coeff_zero]
  have h1 := card_le_degree_of_subset_roots hsub
  rw [card_image_of_injective _ hx] at h1
  have := (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 (polyOf_mem fun a => E a b))
  omega

/-! ## The statement -/

variable [DecidableEq K]

/-- The **bad set** of the line through `u₀`, `u₁` (BLUEPRINT §5.3): the `z` for which
`u₀ + z (u₁ − u₀)` agrees with a codeword `w` on `n − e` positions, but no pair of codewords has
joint agreement with `(u₀, u₁)` equal to that agreement set. -/
def lineBad (C : Submodule K (Fin n → K)) (e : ℕ) (u₀ u₁ : Fin n → K) : Set K :=
  {z | ∃ w ∈ C, n - e ≤ (agreeSet (u₀ + z • (u₁ - u₀)) w).card ∧
    ¬ ∃ v₀ ∈ C, ∃ v₁ ∈ C, agreeSet₂ u₀ u₁ v₀ v₁ = agreeSet (u₀ + z • (u₁ - u₀)) w}

/-- The constant `C_mca(n, k, e) := k e + n` that the proof below gives (BLUEPRINT §5.3 allows any
value `≤ 2^60`). -/
def cMca (n k e : ℕ) : ℕ := k * e + n

/-- At a position where `(u₀, u₁) ≠ (v₀, v₁)`, `u₀ + z (u₁ − u₀) = v₀ + z (v₁ − v₀)` holds only at
`z = −(u₀ − v₀) / ((u₁ − u₀) − (v₁ − v₀))`. -/
theorem line_eq_root {a₀ a₁ b₀ b₁ z : K} (hne : ¬ (a₀ = b₀ ∧ a₁ = b₁))
    (h : a₀ + z * (a₁ - a₀) = b₀ + z * (b₁ - b₀)) :
    z = -(a₀ - b₀) / ((a₁ - a₀) - (b₁ - b₀)) := by
  by_cases hc : (a₁ - a₀) - (b₁ - b₀) = 0
  · exfalso; apply hne
    have h0 : a₀ = b₀ := by linear_combination h - z * hc
    exact ⟨h0, by linear_combination hc + h0⟩
  · field_simp
    linear_combination h

/-- **`mca_ud_line`, cover form**: for any field `K`, distinct points `x`, and `2e + k ≤ n`, the
bad set of every line is contained in a finite set of at most `k e + n` elements. -/
theorem mca_ud_line_cover {x : Fin n → K} (hx : Function.Injective x) {k e : ℕ}
    (h : 2 * e + k ≤ n) (u₀ u₁ : Fin n → K) :
    ∃ B : Finset K, B.card ≤ cMca n k e ∧ lineBad (rsCode x k) e u₀ u₁ ⊆ B := by
  classical
  -- step 1: the interpolating pair
  obtain ⟨E, N, hne, hres⟩ := bw_exists x u₀ u₁ h
  have hE := bw_E_ne hx (by omega) hne hres
  -- step 2: `k` positions where `E(x_j, Z) ≠ 0`, and the interpolated line
  have hfew := bw_few_zero_cols hx hE (univ.filter fun j => colPoly E (x j) = 0)
    fun j hj => (mem_filter.1 hj).2
  obtain ⟨J, hJA, hJ⟩ : ∃ J ⊆ univ.filter (fun j => ¬ colPoly E (x j) = 0), J.card = k := by
    apply exists_subset_card_eq
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      fun j => colPoly E (x j) = 0
    rw [card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨v₀, hv₀, hv₀J⟩ := rs_interp hx J hJ.le u₀
  obtain ⟨v₁, hv₁, hv₁J⟩ := rs_interp hx J hJ.le u₁
  -- the cover
  let S₁ := J.biUnion fun j => (colPoly E (x j)).roots.toFinset
  let S₂ := univ.image fun j => -(u₀ j - v₀ j) / ((u₁ j - u₀ j) - (v₁ j - v₀ j))
  refine ⟨S₁ ∪ S₂, ?_, ?_⟩
  · have h1 : S₁.card ≤ k * e := by
      refine (card_biUnion_le).trans ((sum_le_card_nsmul _ _ e fun j hj => ?_).trans
        (by rw [hJ, smul_eq_mul]))
      have := (natDegree_lt_iff_degree_lt (mem_filter.1 (hJA hj)).2).2
        (mem_degreeLT.1 (colPoly_mem E (x j)))
      exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (by omega))
    have h2 : S₂.card ≤ n := card_image_le.trans (by simp)
    exact (card_union_le _ _).trans (by unfold cMca; omega)
  rintro z ⟨w, hw, hcl, hnot⟩
  by_contra hzB
  obtain ⟨hz1, hz2⟩ := not_or.1 (mt mem_union.2 hzB)
  apply hnot
  refine ⟨v₀, hv₀, v₁, hv₁, ?_⟩
  set uz := u₀ + z • (u₁ - u₀)
  have hVz : v₀ + z • (v₁ - v₀) ∈ rsCode x k :=
    add_mem hv₀ (Submodule.smul_mem _ _ (sub_mem hv₁ hv₀))
  -- step 3: `w` is the line's codeword at `z`
  have hwV : w = v₀ + z • (v₁ - v₀) := by
    obtain ⟨P, hP, rfl⟩ := mem_rsCode.1 hw
    have hspec : ∀ j, (rowPoly N z).eval (x j) = (rowPoly E z).eval (x j) * uz j := fun j => by
      have := congrArg (eval z) (hres j)
      simp only [bwRes, eval_sub, eval_mul, eval_add, eval_C, eval_X, eval_zero,
        eval_colPoly, sub_eq_zero] at this
      simpa [uz, smul_eq_mul] using this
    have hNE := bw_unique hx (a := n - k - e) (k := k) (polyOf_mem _)
      (by rw [show n - k - e + k = n - e by omega]; exact polyOf_mem _) (mem_degreeLT.2 hP) uz
      hspec (agreeSet uz (evalWord x P)) (by omega) fun j hj => mem_agreeSet.1 hj
    refine rs_eq_of_agree hx hw hVz J hJ.ge fun j hj => ?_
    have hEz : (rowPoly E z).eval (x j) ≠ 0 := fun h0 => hz1 (mem_biUnion.2 ⟨j, hj,
      Multiset.mem_toFinset.2 ((mem_roots (mem_filter.1 (hJA hj)).2).2 (by rwa [IsRoot.def,
        eval_colPoly]))⟩)
    have h1 := hspec j
    rw [hNE, eval_mul] at h1
    rw [show evalWord x P j = uz j from mul_left_cancel₀ hEz h1]
    simp [uz, hv₀J j hj, hv₁J j hj]
  -- step 4: the agreement set is the joint one
  rw [hwV]
  ext j
  simp only [mem_agreeSet₂, mem_agreeSet, uz, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  constructor
  · rintro ⟨h0, h1⟩; rw [h0, h1]
  · intro hj
    by_contra hnj
    exact hz2 (mem_image.2 ⟨j, mem_univ _, (line_eq_root hnj hj).symm⟩)

/-- **`mca_ud_line`** (BLUEPRINT §5.3) over a finite field: the bad set of every line has at most
`C_mca(n, k, e) = k e + n` elements. -/
theorem mca_ud_line [Finite K] {x : Fin n → K} (hx : Function.Injective x) {k e : ℕ}
    (h : 2 * e + k ≤ n) (u₀ u₁ : Fin n → K) :
    Nat.card (lineBad (rsCode x k) e u₀ u₁) ≤ cMca n k e := by
  obtain ⟨B, hB, hsub⟩ := mca_ud_line_cover hx h u₀ u₁
  rw [Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard hsub (B.finite_toSet)).trans (by rwa [Set.ncard_coe_finset])

/-! ## The protocol's instance: words over `K`, the code `C_K` on `D` -/

/-- **`mca_ud_line` for the Ligerito levels** (BLUEPRINT §5.3): over `K = GF(2^256)`, the code
`C_K = Enc_k(K^k)` on the domain `D[0…n)` (`n, k ≤ nMax = 2^20`), `2e + k ≤ n`: every line's
bad set has at most `C_mca(n, k, e) = k e + n` elements. -/
theorem mca_ud_line_K {n k e : ℕ} (hn : n ≤ nMax) (hk : k ≤ nMax) (h : 2 * e + k ≤ n)
    (u₀ u₁ : Fin n → FR.K) :
    Nat.card (lineBad (encCode (M := FR.K) D n k) e u₀ u₁) ≤ cMca n k e := by
  rw [encCode_D hk]
  exact mca_ud_line (Dpts_injective hn) h u₀ u₁

/-- The **P1 row**'s count (BLUEPRINT §5.2): a fold round over `m` lines has a bad set (the union
of the lines' bad sets) of at most `m · C_mca(n, k, e)` elements. -/
theorem round_bad_cover {ι : Type*} [Fintype ι] {x : Fin n → K} (hx : Function.Injective x)
    {k e : ℕ} (h : 2 * e + k ≤ n) (U₀ U₁ : ι → Fin n → K) :
    ∃ B : Finset K, B.card ≤ Fintype.card ι * cMca n k e ∧
      ∀ c, lineBad (rsCode x k) e (U₀ c) (U₁ c) ⊆ B := by
  classical
  choose B hB hsub using fun c => mca_ud_line_cover hx h (U₀ c) (U₁ c)
  refine ⟨univ.biUnion B, (card_biUnion_le).trans ?_, fun c => (hsub c).trans ?_⟩
  · simpa using sum_le_card_nsmul univ (fun c => (B c).card) _ fun c _ => hB c
  · intro z hz; simpa using ⟨c, hz⟩

end FR

end G6_FRProximityLine

section G6_FRProximityFold

-- New for `flock-recursive` (BLUEPRINT §5.2 rows P1/P2, §5.3, §5.4 step 2; BP-C-M8).

/-!
# Folding, F-valuedness, positions (BLUEPRINT §5.3, §5.4)

Generic over a field `K`, distinct points `x : Fin n → K`, `C = RS[K, x, k]`, `2e + k ≤ n`:

* `JointClose C e U A`: the rows `U` have codeword rows whose **joint** agreement set is exactly
  `A`, and `|A| ≥ n − e`.
* **`fold_preserves`** (P1): one fold round pairs rows `(U₀ c, U₁ c)` and outputs
  `U₀ c + z (U₁ c − U₀ c)`. If `z` is in no line's bad set (`lineBad`, bounded by
  `round_bad_cover`), the input rows are jointly close with agreement set `A` iff the output
  rows are; `fold_lift` also returns codewords that fold to the given ones. Iterating over a
  level's rounds is the consumer's induction (the row order is the transcript's).
* **`interp_F`**: a codeword over `M ⊇ L` that is `L`-valued on `k` positions is the image of a
  codeword over `L` (`interp_F_D`: in `C_K`, `F`-valued on `k` positions, it is `Enc` of an
  `F`-message).
* **`positions_bad_le`** (P2): the `t`-tuples of positions inside a set of `≤ n − e − 1`
  positions are at most a `(1 − e/n)^t` fraction of all `n^t`.
-/

namespace FR

open Polynomial Finset

section Fold

variable {K : Type*} [Field K] [DecidableEq K] {n : ℕ}

/-- The joint agreement set of a family of rows `U` with a family of words `V`. -/
def jointAgree {ι : Type*} [Fintype ι] (U V : ι → Fin n → K) : Finset (Fin n) :=
  univ.filter fun j => ∀ i, U i j = V i j

omit [Field K] in
@[simp] theorem mem_jointAgree {ι : Type*} [Fintype ι] {U V : ι → Fin n → K} {j : Fin n} :
    j ∈ jointAgree U V ↔ ∀ i, U i j = V i j := by
  simp [jointAgree]

/-- **`JointClose C e U A`**: the rows `U` agree with codeword rows exactly on `A`, `|A| ≥ n − e`
(BLUEPRINT §5.4: "`e`-close to `C^{rows}` with joint agreement `A`"). -/
def JointClose {ι : Type*} [Fintype ι] (C : Submodule K (Fin n → K)) (e : ℕ)
    (U : ι → Fin n → K) (A : Finset (Fin n)) : Prop :=
  n - e ≤ A.card ∧ ∃ V : ι → Fin n → K, (∀ i, V i ∈ C) ∧ jointAgree U V = A

/-- The rows `U₀ c` (`false`) and `U₁ c` (`true`) of one fold round as one family. -/
def pairRows {κ : Type*} (U₀ U₁ : κ → Fin n → K) : Bool × κ → Fin n → K :=
  fun p => if p.1 then U₁ p.2 else U₀ p.2

omit [Field K] [DecidableEq K] in
@[simp] theorem pairRows_false {κ : Type*} (U₀ U₁ : κ → Fin n → K) (c : κ) :
    pairRows U₀ U₁ (false, c) = U₀ c := rfl

omit [Field K] [DecidableEq K] in
@[simp] theorem pairRows_true {κ : Type*} (U₀ U₁ : κ → Fin n → K) (c : κ) :
    pairRows U₀ U₁ (true, c) = U₁ c := rfl

/-- One fold round: `U₀ c + z (U₁ c − U₀ c)`. -/
def foldRows {κ : Type*} (z : K) (U₀ U₁ : κ → Fin n → K) : κ → Fin n → K :=
  fun c => U₀ c + z • (U₁ c - U₀ c)

variable {x : Fin n → K} {k e : ℕ}

/-- A close line point has a pair of codewords whose joint agreement is its agreement set, when
`z` is not bad. -/
theorem good_line (hz : z ∉ lineBad (rsCode x k) e u₀ u₁) {w : Fin n → K}
    (hw : w ∈ rsCode x k) (hcl : n - e ≤ (agreeSet (u₀ + z • (u₁ - u₀)) w).card) :
    ∃ v₀ ∈ rsCode x k, ∃ v₁ ∈ rsCode x k,
      agreeSet₂ u₀ u₁ v₀ v₁ = agreeSet (u₀ + z • (u₁ - u₀)) w := by
  by_contra hne
  exact hz ⟨w, hw, hcl, hne⟩

theorem card_le_of_superset {A B : Finset (Fin n)} (h : A ⊆ B) (hA : n - e ≤ A.card) :
    n - e ≤ B.card := hA.trans (card_le_card h)

/-- **`fold_lift`**: under no bad `z`, codeword rows `W` jointly agreeing with the fold exactly on
`A` (`|A| ≥ n − e`) lift to codeword pairs `(V₀ c, V₁ c)` that fold to `W c` and agree with
`(U₀, U₁)` exactly on `A`. -/
theorem fold_lift (hx : Function.Injective x) (h : 2 * e + k ≤ n) {κ : Type*} [Fintype κ]
    {U₀ U₁ : κ → Fin n → K} {z : K} (hz : ∀ c, z ∉ lineBad (rsCode x k) e (U₀ c) (U₁ c))
    {A : Finset (Fin n)} (hA : n - e ≤ A.card) {W : κ → Fin n → K} (hW : ∀ c, W c ∈ rsCode x k)
    (hWA : jointAgree (foldRows z U₀ U₁) W = A) :
    ∃ V₀ V₁ : κ → Fin n → K, (∀ c, V₀ c ∈ rsCode x k) ∧ (∀ c, V₁ c ∈ rsCode x k) ∧
      (∀ c, W c = V₀ c + z • (V₁ c - V₀ c)) ∧ jointAgree (pairRows U₀ U₁) (pairRows V₀ V₁) = A := by
  have hsup : ∀ c, A ⊆ agreeSet (foldRows z U₀ U₁ c) (W c) := fun c j hj => by
    rw [← hWA, mem_jointAgree] at hj; exact mem_agreeSet.2 (hj c)
  choose V₀ hV₀ V₁ hV₁ hV using fun c => good_line (hz c) (hW c) (card_le_of_superset (hsup c) hA)
  have key : ∀ c j, (U₀ c j = V₀ c j ∧ U₁ c j = V₁ c j) ↔ foldRows z U₀ U₁ c j = W c j :=
    fun c j => mem_agreeSet₂.symm.trans (hV c ▸ mem_agreeSet)
  refine ⟨V₀, V₁, hV₀, hV₁, fun c => ?_, ?_⟩
  · -- both are codewords agreeing with the fold on `A`
    refine rs_eq_of_agree hx (hW c) (add_mem (hV₀ c) (Submodule.smul_mem _ _
      (sub_mem (hV₁ c) (hV₀ c)))) A (by omega) fun j hj => ?_
    obtain ⟨h0, h1⟩ := (key c j).2 (mem_agreeSet.1 (hsup c hj))
    rw [← mem_agreeSet.1 (hsup c hj)]; simp [foldRows, h0, h1]
  · ext j
    rw [← hWA, mem_jointAgree, mem_jointAgree]
    constructor
    · exact fun hj c => (key c j).1 ⟨hj (false, c), hj (true, c)⟩
    · rintro hj ⟨_ | _, c⟩
      exacts [((key c j).2 (hj c)).1, ((key c j).2 (hj c)).2]

/-- **`fold_preserves`** (BLUEPRINT §5.3): if `z` is in no line's bad set, the pair rows
`(U₀, U₁)` are jointly close to `C` with agreement set `A` iff the folded rows are. -/
theorem fold_preserves (hx : Function.Injective x) (h : 2 * e + k ≤ n) {κ : Type*} [Fintype κ]
    {U₀ U₁ : κ → Fin n → K} {z : K} (hz : ∀ c, z ∉ lineBad (rsCode x k) e (U₀ c) (U₁ c))
    (A : Finset (Fin n)) :
    JointClose (rsCode x k) e (pairRows U₀ U₁) A ↔
      JointClose (rsCode x k) e (foldRows z U₀ U₁) A := by
  constructor
  · rintro ⟨hA, V, hV, hVA⟩
    have hU : ∀ c, ∀ i ∈ A, U₀ c i = V (false, c) i ∧ U₁ c i = V (true, c) i := fun c i hi => by
      rw [← hVA, mem_jointAgree] at hi
      exact ⟨hi (false, c), hi (true, c)⟩
    have hF : ∀ c, foldRows z (fun c => V (false, c)) (fun c => V (true, c)) c ∈ rsCode x k :=
      fun c => add_mem (hV _) (Submodule.smul_mem _ _ (sub_mem (hV _) (hV _)))
    have hsup : ∀ c, A ⊆ agreeSet (foldRows z U₀ U₁ c)
        (foldRows z (fun c => V (false, c)) (fun c => V (true, c)) c) := fun c j hj => by
      simp [foldRows, hU c j hj]
    refine ⟨hA, _, hF, ?_⟩
    ext j
    refine ⟨fun hj => ?_, fun hj => mem_jointAgree.2 fun c => mem_agreeSet.1 (hsup c hj)⟩
    rw [← hVA, mem_jointAgree]
    rintro ⟨b, c⟩
    obtain ⟨v₀, hv₀, v₁, hv₁, hv⟩ := good_line (hz c) (hF c) (card_le_of_superset (hsup c) hA)
    have hA₂ : ∀ i ∈ A, U₀ c i = v₀ i ∧ U₁ c i = v₁ i := fun i hi =>
      mem_agreeSet₂.1 (hv ▸ hsup c hi)
    have e0 : v₀ = V (false, c) := rs_eq_of_agree hx hv₀ (hV _) A (by omega) fun i hi =>
      (hA₂ i hi).1.symm.trans (hU c i hi).1
    have e1 : v₁ = V (true, c) := rs_eq_of_agree hx hv₁ (hV _) A (by omega) fun i hi =>
      (hA₂ i hi).2.symm.trans (hU c i hi).2
    have hj' : j ∈ agreeSet₂ (U₀ c) (U₁ c) v₀ v₁ := by
      rw [hv, mem_agreeSet]; exact mem_jointAgree.1 hj c
    rw [mem_agreeSet₂, e0, e1] at hj'
    cases b
    exacts [hj'.1, hj'.2]
  · rintro ⟨hA, W, hW, hWA⟩
    obtain ⟨V₀, V₁, hV₀, hV₁, -, hV⟩ := fold_lift hx h hz hA hW hWA
    exact ⟨hA, pairRows V₀ V₁, fun ⟨b, c⟩ => by cases b <;> simp [hV₀, hV₁], hV⟩

end Fold

/-! ## F-valuedness once per level (`interp_F`) -/

section InterpF

variable {L M : Type*} [Field L] [Field M] [Algebra L M] {n : ℕ}

/-- An `L`-codeword maps to an `M`-codeword of the same code over the image points. -/
theorem rsCode_map {x : Fin n → L} {k : ℕ} {v : Fin n → L} (hv : v ∈ rsCode x k) :
    (fun j => algebraMap L M (v j)) ∈ rsCode (fun j => algebraMap L M (x j)) k := by
  obtain ⟨p, hp, rfl⟩ := mem_rsCode.1 hv
  refine mem_rsCode.2 ⟨p.map (algebraMap L M), ?_, funext fun j => ?_⟩
  · rwa [degree_map]
  · simp [evalWord, eval_map, eval₂_at_apply]

/-- **`interp_F`**: a codeword of `RS[M, x, k]` (points in `L`) that is `L`-valued on `k`
positions is the image of a codeword of `RS[L, x, k]`. -/
theorem interp_F [DecidableEq M] {x : Fin n → L} (hx : Function.Injective x) {k : ℕ}
    {v : Fin n → M} (hv : v ∈ rsCode (fun j => algebraMap L M (x j)) k) (f : Fin n → L)
    (A : Finset (Fin n)) (hA : k ≤ A.card) (hvA : ∀ j ∈ A, v j = algebraMap L M (f j)) :
    ∃ v' ∈ rsCode x k, v = fun j => algebraMap L M (v' j) := by
  obtain ⟨J, hJA, hJ⟩ := exists_subset_card_eq hA
  obtain ⟨v', hv', hv'J⟩ := rs_interp hx J hJ.le f
  refine ⟨v', hv', rs_eq_of_agree ((algebraMap L M).injective.comp hx) hv (rsCode_map hv') J
    hJ.ge fun j hj => ?_⟩
  rw [hvA j (hJA hj), hv'J j hj]

/-- `Enc` commutes with the field embedding: `Enc_M(ι ∘ c) = ι ∘ Enc_L(c)`. -/
theorem enc_algebraMap (pt : ℕ → L) (n k : ℕ) (c : Fin k → L) (j : Fin n) :
    enc (M := M) pt n k (fun x => algebraMap L M (c x)) j = algebraMap L M (enc pt n k c j) := by
  simp [enc, map_sum, map_mul]

end InterpF

/-- **`interp_F` on the protocol's code**: a word of `C_K` (on `D`, `n, k ≤ 2^64`) that is
`F`-valued on `k` positions is `Enc_K` of an `F`-message, i.e. lies in `C_F`. -/
theorem interp_F_D {n k : ℕ} (hn : n ≤ nMax) (hk : k ≤ nMax) {v : Fin n → K}
    (hv : v ∈ encCode (M := K) D n k) (f : Fin n → F) (A : Finset (Fin n)) (hA : k ≤ A.card)
    (hvA : ∀ j ∈ A, v j = algebraMap F K (f j)) :
    ∃ c : Fin k → F, v = enc (M := K) D n k (fun x => algebraMap F K (c x)) := by
  rw [encCode_D hk] at hv
  obtain ⟨v', hv', rfl⟩ := interp_F (Dpts_injective hn) hv f A hA hvA
  rw [← encCode_D (M := F) hk] at hv'
  obtain ⟨c, rfl⟩ := hv'
  exact ⟨c, funext fun j => (enc_algebraMap D n k c j).symm⟩

/-! ## Positions (row P2) -/

section Positions

variable {n : ℕ}

/-- The `t`-tuples of positions all inside `S` are `|S|^t` many. -/
theorem positions_card (S : Finset (Fin n)) (t : ℕ) :
    (univ.filter fun f : Fin t → Fin n => ∀ i, f i ∈ S).card = S.card ^ t := by
  rw [show (univ.filter fun f : Fin t → Fin n => ∀ i, f i ∈ S) = Fintype.piFinset fun _ => S by
    ext f; simp [Fintype.mem_piFinset], Fintype.card_piFinset]
  simp

/-- **`positions_bad_le`** (row P2): if the agreement set `S` has at most `n − e − 1` positions,
the fraction of the `n^t` position tuples that land only in `S` is at most `(1 − e/n)^t`. -/
theorem positions_bad_le (S : Finset (Fin n)) (t e : ℕ) (hS : S.card + e < n) :
    ((univ.filter fun f : Fin t → Fin n => ∀ i, f i ∈ S).card : ℚ) / (n : ℚ) ^ t ≤
      (1 - (e : ℚ) / n) ^ t := by
  have hn : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [positions_card, Nat.cast_pow, ← div_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ t
  rw [div_le_iff₀ hn, sub_mul, one_mul, div_mul_cancel₀ _ hn.ne']
  have : (S.card : ℚ) + e ≤ n := by exact_mod_cast hS.le
  linarith

end Positions

/-! ## Controls (BLUEPRINT §5.6) -/

section Controls

/-- The Ligerito levels `(n, k, e)` of both shapes (BLUEPRINT §2.2: `P30` then `L32`,
`e = ⌊(n − k)/2⌋`). -/
def pcsLevels : List (ℕ × ℕ × ℕ) :=
  [(2 ^ 18, 2 ^ 17), (2 ^ 16, 2 ^ 14), (2 ^ 14, 2 ^ 11), (2 ^ 12, 2 ^ 8), (2 ^ 10, 2 ^ 5),
    (2 ^ 20, 2 ^ 19), (2 ^ 18, 2 ^ 16), (2 ^ 16, 2 ^ 13), (2 ^ 14, 2 ^ 10), (2 ^ 12, 2 ^ 7)].map
    fun p => (p.1, p.2, (p.1 - p.2) / 2)

/-- **Positive control of `mca_ud_line`'s use**: at every level the hypotheses hold
(`2e + k ≤ n ≤ nMax`), `C_mca ≤ 2^60` (the stage requirement) and the P1 row with `2^6` lines,
`(2^6 C_mca + 2)/2^256`, is at most `2^-190` (BLUEPRINT §5.2). -/
theorem pcsLevels_ok : ∀ p ∈ pcsLevels, 2 * p.2.2 + p.2.1 ≤ p.1 ∧ p.1 ≤ nMax ∧
    cMca p.1 p.2.1 p.2.2 ≤ 2 ^ 60 ∧ 2 ^ 6 * cMca p.1 p.2.1 p.2.2 + 2 ≤ 2 ^ 66 := by
  decide

/-- A codeword of `RS[K, x, 1]` is constant. -/
theorem rsCode_one_const {K : Type*} [Field K] {n : ℕ} {x : Fin n → K} {w : Fin n → K}
    (hw : w ∈ rsCode x 1) (i j : Fin n) : w i = w j := by
  obtain ⟨p, hp, rfl⟩ := mem_rsCode.1 hw
  rw [eq_C_of_degree_le_zero (p := p) (Nat.WithBot.lt_one_iff_le_zero.1 (by exact_mod_cast hp))]
  simp [evalWord]

/-- **Positive control of `lineBad`**: a line of codewords has no bad `z`
(`2e + k ≤ n`). -/
theorem lineBad_codewords {K : Type*} [Field K] [DecidableEq K] {n : ℕ} {x : Fin n → K}
    (hx : Function.Injective x) {k e : ℕ} (h : 2 * e + k ≤ n) {u₀ u₁ : Fin n → K}
    (h₀ : u₀ ∈ rsCode x k) (h₁ : u₁ ∈ rsCode x k) : lineBad (rsCode x k) e u₀ u₁ = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨w, hw, hcl, hnot⟩
  have huz : u₀ + z • (u₁ - u₀) ∈ rsCode x k :=
    add_mem h₀ (Submodule.smul_mem _ _ (sub_mem h₁ h₀))
  have hfull : n - e ≤ (agreeSet (u₀ + z • (u₁ - u₀)) (u₀ + z • (u₁ - u₀))).card := by
    simp [agreeSet]
  obtain rfl := close_unique hx h hw huz hcl hfull
  exact hnot ⟨u₀, h₀, u₁, h₁, by ext j; simp⟩

theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] fact_prime_five

/-- **Negative control of `lineBad`**: it is not always empty. Over `GF(5)`, points `0, 1, 2`,
`k = 1`, `e = 1` (`2e + k ≤ n`): the line from `(0, 0, 1)` to `(0, 1, 0)` is bad at `z = 0`
(`(0, 0, 1)` is close to `0` on `{0, 1}`, where `u₁ = (0, 1)` is not constant). -/
theorem lineBad_nonempty :
    (0 : ZMod 5) ∈ lineBad (rsCode ![(0 : ZMod 5), 1, 2] 1) 1 ![0, 0, 1] ![0, 1, 0] := by
  refine ⟨0, zero_mem _, by decide, ?_⟩
  rintro ⟨v₀, -, v₁, hv₁, hagree⟩
  have h0 : (0 : Fin 3) ∈ agreeSet₂ ![(0 : ZMod 5), 0, 1] ![0, 1, 0] v₀ v₁ := by
    rw [hagree]; decide
  have h1 : (1 : Fin 3) ∈ agreeSet₂ ![(0 : ZMod 5), 0, 1] ![0, 1, 0] v₀ v₁ := by
    rw [hagree]; decide
  rw [mem_agreeSet₂] at h0 h1
  have := rsCode_one_const hv₁ 0 1
  rw [← h0.2, ← h1.2] at this
  exact absurd this (by decide)

/-- **Negative control of `fold_preserves`** (S-D-m2): at the bad `z = 0` of
`lineBad_nonempty` the fold is jointly close with `A = {0, 1}`, the pair rows are not. -/
theorem fold_preserves_fails_at_bad :
    JointClose (rsCode ![(0 : ZMod 5), 1, 2] 1) 1
      (foldRows (0 : ZMod 5) (fun _ : Unit => ![(0 : ZMod 5), 0, 1]) (fun _ => ![0, 1, 0]))
        {0, 1} ∧
    ¬ JointClose (rsCode ![(0 : ZMod 5), 1, 2] 1) 1
      (pairRows (fun _ : Unit => ![(0 : ZMod 5), 0, 1]) (fun _ => ![0, 1, 0])) {0, 1} := by
  constructor
  · refine ⟨by decide, fun _ => 0, fun _ => zero_mem _, ?_⟩
    ext j; simp only [mem_jointAgree, foldRows]; fin_cases j <;> decide
  · rintro ⟨-, V, hV, hA⟩
    have h0 : (0 : Fin 3) ∈ jointAgree (pairRows (fun _ : Unit => ![(0 : ZMod 5), 0, 1])
      (fun _ => ![0, 1, 0])) V := by rw [hA]; decide
    have h1 : (1 : Fin 3) ∈ jointAgree (pairRows (fun _ : Unit => ![(0 : ZMod 5), 0, 1])
      (fun _ => ![0, 1, 0])) V := by rw [hA]; decide
    rw [mem_jointAgree] at h0 h1
    have := rsCode_one_const (hV (true, ())) 0 1
    have e0 := h0 (true, ()); have e1 := h1 (true, ())
    simp only [pairRows_true] at e0 e1
    rw [← e0, ← e1] at this
    exact absurd this (by decide)

/-- **Negative control of `close_unique`** (BLUEPRINT §5.6, "`2e = d`"): without `2e + k ≤ n`
two codewords can be equally close. Over `GF(5)`, points `0, 1`, `k = 1`, `e = 1` (`2e = d = 2`):
the word `(0, 1)` agrees with the codewords `0` and `1` on one position each. -/
theorem close_not_unique_at_d :
    ∃ u w w' : Fin 2 → ZMod 5, w ∈ rsCode ![(0 : ZMod 5), 1] 1 ∧ w' ∈ rsCode ![(0 : ZMod 5), 1] 1 ∧
      2 - 1 ≤ (agreeSet u w).card ∧ 2 - 1 ≤ (agreeSet u w').card ∧ w ≠ w' := by
  refine ⟨![0, 1], 0, 1, zero_mem _, mem_rsCode.2 ⟨1, by simp, by ext j; simp [evalWord]⟩,
    by decide, by decide, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **Positive control of `positions_card`** on a toy: `n = 4`, `t = 2`, `S = {0, 1}`:
`4 = 2^2` of the `16` position pairs. -/
theorem positions_card_toy :
    (univ.filter fun f : Fin 2 → Fin 4 => ∀ i, f i ∈ ({0, 1} : Finset (Fin 4))).card = 4 := by
  decide

/-- `D (2^64) = D 0` (the `UInt64` wrap). -/
theorem D_two_pow_64 : D (2 ^ 64) = D 0 := rfl

/-- **Negative control of `D_injOn`**: its bound is sharp, `D` is not injective on
`[0, 2^64 + 1)`. -/
theorem D_not_injOn_succ : ¬ Set.InjOn D (Set.Iio (2 ^ 64 + 1)) := fun h =>
  absurd (h (Set.mem_Iio.2 (by norm_num)) (Set.mem_Iio.2 (by norm_num)) D_two_pow_64)
    (by norm_num)

/-- The `FRRS` lemmas instantiated on `D` (a remark, not a control): `Ŵ_v(D[2^v]) = 1` and
`X_x` has degree `x`
for `x < 2^64` (the hypotheses of the `FRRS` lemmas are discharged by `D_injOn`). -/
theorem novel_D_ok {v x : ℕ} (hv : v < 64) (hx : x < 2 ^ 64) :
    (normW D v).eval (D (2 ^ v)) = 1 ∧ novelX D x ≠ 0 ∧ (novelX D x).natDegree = x :=
  ⟨normW_eval_self D_injOn hv, novelX_natDegree D_injOn hx⟩

/-- **Negative control of block-triangularity**: the vanishing stops at `2^v`: `X_{2^v}` is
`1` at `D[2^v]`, while it vanishes on `D[0 … 2^v)`. -/
theorem novel_D_triangular {v j : ℕ} (hv : v < 64) (hj : j < 2 ^ v) :
    (novelX D (2 ^ v)).eval (D j) = 0 ∧ (novelX D (2 ^ v)).eval (D (2 ^ v)) = 1 := by
  refine ⟨novelX_eval_zero D (Nat.testBit_two_pow_self) hj, ?_⟩
  rw [novelX_eq_bitProd D (show 2 ^ v < 2 ^ (v + 1) from Nat.pow_lt_pow_right (by norm_num)
    (by omega)), show 2 ^ v = 2 ^ v + 0 by rfl, bitProd_succ_hi _ (by positivity)]
  simp [bitProd, bitSel, normW_eval_self D_injOn hv]

/-- **Control of `Enc`** (BLUEPRINT §5.6, "distinct messages differ"): on `D`, distinct messages
give codewords that differ in at least `n − k + 1` positions (`k ≤ n ≤ nMax`); in particular a
codeword has one message (the round trip of `coeffs_of_values`). -/
theorem enc_D_dist {M : Type*} [Field M] [Algebra F M] [DecidableEq M] {n k : ℕ}
    (hn : n ≤ nMax) (hkn : k ≤ n) {c c' : Fin k → M} (h : c ≠ c') :
    n + 1 ≤ k + hammingDist (enc (M := M) D n k c) (enc D n k c') := by
  have hk : k ≤ nMax := hkn.trans hn
  have hmem : ∀ c : Fin k → M, enc (M := M) D n k c ∈ rsCode (Dpts n) k := fun c => by
    rw [← encCode_D hk]; exact LinearMap.mem_range.2 ⟨c, rfl⟩
  exact rs_minDist (Dpts_injective hn) (hmem c) (hmem c')
    (fun e => h (enc_injective D_injOn_nMax hk hn hkn e))

end Controls

end FR

end G6_FRProximityFold
