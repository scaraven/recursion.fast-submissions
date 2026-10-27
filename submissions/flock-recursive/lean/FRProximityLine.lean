-- New for `flock-recursive` (BLUEPRINT §5.3, B-5, BP-C-M8). The argument is BCIKS20 Thm 4.1's
-- unique-decoding case reorganised (see the module docstring); nothing is copied from ArkLib.
import FRProximityBW
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

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
`C_K = Enc_k(K^k)` on the domain `D[0…n)` (`n ≤ 2^64`, `k ≤ 2^64`), `2e + k ≤ n`: every line's
bad set has at most `C_mca(n, k, e) = k e + n` elements. -/
theorem mca_ud_line_K {n k e : ℕ} (hn : n ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) (h : 2 * e + k ≤ n)
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
