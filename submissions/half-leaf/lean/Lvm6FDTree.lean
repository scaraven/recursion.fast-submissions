-- lvm6 X1 (BLUEPRINT §3 `FD1`): the product tree computes `Λ`. New; on season 1's `coeffsAt_spec`,
-- `coeffs_spec`, `bflyRun_eq`, `fwdRun_enc`, `encPoly_mem` (`LvmXDec`).
import Lvm6FDSpec

/-!
# The product tree of `FD1`

* `coeffsAt_congr`, `coeffsAt_zero`: the inverse NTT of a block reads only the block.
* **`extend_eval`**: inverse NTT, zero padding and forward NTT extend the values of a polynomial
  of degree `< 2^ℓ` on `ptK [0, 2^ℓ)` to its values on `ptK [0, 2^(ℓ+1))`.
* `nodePoly S h p`: the product of the leaves of node `p` at height `h`; **`lam_eval`**: the tree
  level `h` holds `nodePoly S h p` on `ptK [0, 2^(h+1))` in block `p`; `lamPoly S ℓ = Λ`.
-/

namespace Lvm6.FD

open Lvm.Nb Lvm.X Finset Polynomial

/-! ## The inverse NTT reads only its block -/

theorem coeffsAt_congr (N : ℕ) : ∀ (ℓ s : ℕ) (y y' : ℕ → BF64), (∀ j < 2 ^ ℓ, y j = y' j) →
    ∀ x < 2 ^ ℓ, coeffsAt ptK N ℓ s y x = coeffsAt ptK N ℓ s y' x
  | 0, _, _, _, h, x, hx => h x hx
  | ℓ + 1, s, y, y', h, x, hx => by
    have hp : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
    have hu := coeffsAt_congr N ℓ s y y' (fun j hj => h j (by omega))
    have hw := coeffsAt_congr N ℓ (s + 2 ^ ℓ) (fun j => y (2 ^ ℓ + j)) (fun j => y' (2 ^ ℓ + j))
      (fun j hj => h _ (by omega))
    simp only [coeffsAt]
    split_ifs with hlt
    · rw [hu x hlt, hw x hlt]
    · rw [hu (x - 2 ^ ℓ) (by omega), hw (x - 2 ^ ℓ) (by omega)]

theorem coeffsAt_zero (N : ℕ) : ∀ (ℓ s : ℕ) (y : ℕ → BF64), (∀ j < 2 ^ ℓ, y j = 0) →
    ∀ x < 2 ^ ℓ, coeffsAt ptK N ℓ s y x = 0
  | 0, _, _, h, x, hx => h x hx
  | ℓ + 1, s, y, h, x, hx => by
    have hp : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
    have hu := coeffsAt_zero N ℓ s y (fun j hj => h j (by omega))
    have hw := coeffsAt_zero N ℓ (s + 2 ^ ℓ) (fun j => y (2 ^ ℓ + j)) (fun j hj => h _ (by omega))
    simp only [coeffsAt]
    split_ifs with hlt
    · rw [hu x hlt, hw x hlt]; ring
    · rw [hu (x - 2 ^ ℓ) (by omega), hw (x - 2 ^ ℓ) (by omega)]; ring

/-! ## Extension of values -/

theorem algebraMap_self_K (a : BF64) : algebraMap BF64 BF64 a = a := rfl

/-- The novel-basis polynomial of `c` evaluates to `encN`. -/
theorem encPoly_eval_K (c : Fin k → BF64) (i : ℕ) : (encPoly ptK c).eval (ptK i) = encN ptK c i :=
  encPoly_eval ptK (i + 1) k c ⟨i, by omega⟩

/-- `ptK` is injective on `range (2^ℓ)` for `ℓ ≤ 64`. -/
theorem ptK_injOn_range {ℓ : ℕ} (h : ℓ ≤ 64) : Set.InjOn ptK (range (2 ^ ℓ) : Set ℕ) :=
  fun _ ha _ hb e => ptK_injOn h (Set.mem_Iio.2 (mem_range.1 ha)) (Set.mem_Iio.2 (mem_range.1 hb)) e

/-- **Extension**: if `A` holds the values of `Q` (degree `< 2^ℓ`) on `ptK [0, 2^ℓ)`, the inverse
NTT, zero padding and the forward NTT of size `2^(ℓ+1)` give `Q` on `ptK [0, 2^(ℓ+1))`. -/
theorem extend_eval {N ℓ : ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (Q : BF64[X])
    (hQ : Q.degree < (2 ^ ℓ : ℕ)) (A : ℕ → BF64) (hA : ∀ x < 2 ^ ℓ, A x = Q.eval (ptK x)) :
    ∀ i < 2 ^ (ℓ + 1), fwdRun ptK N (ℓ + 1)
      (fun i => if i < 2 ^ ℓ then bflyRun ptK N 0 ℓ A i else 0) i = Q.eval (ptK i) := by
  intro i hi
  have hpt := ptK_injOn hN64
  set c : Fin (2 ^ ℓ) → BF64 := coeffsOfValues ptK N ℓ A with hc
  rw [fwdRun_enc ptK_xor hpt (m := ℓ) (n := ℓ + 1) (by omega) hN c _ (fun x => by
      by_cases hx : x < 2 ^ ℓ
      · rw [if_pos hx, dif_pos hx, bflyRun_eq ptK N 0 ℓ A hx]; rfl
      · rw [if_neg hx, dif_neg hx]) hi, ← encPoly_eval_K]
  congr 1
  have hk : 2 ^ ℓ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := range (2 ^ ℓ)) (v := ptK)
    (ptK_injOn_range (by omega)) ?_ ?_ fun j hj => ?_
  · rw [card_range]; exact mem_degreeLT.1 (encPoly_mem hpt hk c)
  · rwa [card_range]
  · rw [encPoly_eval_K, coeffs_spec ptK_xor hpt (by omega) A (mem_range.1 hj), hA j (mem_range.1 hj)]

/-! ## The tree's polynomials -/

/-- The product of the leaves of node `p` at height `h`: `X − ptK j` for the positions
`j ∈ [p·2^h, (p+1)·2^h)` outside `S`. -/
noncomputable def nodePoly (S : List ℕ) (h p : ℕ) : BF64[X] :=
  ∏ j ∈ range (2 ^ h), if p * 2 ^ h + j ∈ S then 1 else X - C (ptK (p * 2 ^ h + j))

/-- **`Λ = Π_{j < 2^ℓ, j ∉ S} (X − ptK j)`.** -/
noncomputable def lamPoly (S : List ℕ) (ℓ : ℕ) : BF64[X] :=
  ∏ j ∈ range (2 ^ ℓ), if j ∈ S then 1 else X - C (ptK j)

theorem lamPoly_eq (S : List ℕ) (ℓ : ℕ) : lamPoly S ℓ = nodePoly S ℓ 0 := by
  simp [lamPoly, nodePoly]

theorem nodePoly_succ (S : List ℕ) (h p : ℕ) :
    nodePoly S (h + 1) p = nodePoly S h (2 * p) * nodePoly S h (2 * p + 1) := by
  rw [nodePoly, pow_succ, mul_two, prod_range_add, nodePoly, nodePoly]
  congr 1
  · refine prod_congr rfl fun j _ => ?_
    rw [show p * (2 ^ h + 2 ^ h) + j = 2 * p * 2 ^ h + j by ring]
  · refine prod_congr rfl fun j _ => ?_
    rw [show p * (2 ^ h + 2 ^ h) + (2 ^ h + j) = (2 * p + 1) * 2 ^ h + j by ring]

theorem natDegree_nodePoly_le (S : List ℕ) (h p : ℕ) : (nodePoly S h p).natDegree ≤ 2 ^ h := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ j ∈ range (2 ^ h), (if p * 2 ^ h + j ∈ S then (1 : BF64[X]) else X - C (ptK (p * 2 ^ h + j))).natDegree
      ≤ ∑ _j ∈ range (2 ^ h), 1 := sum_le_sum fun j _ => by
        split_ifs
        · simp
        · rw [natDegree_X_sub_C]
    _ = 2 ^ h := by simp

theorem degree_nodePoly_lt (S : List ℕ) (h p : ℕ) : (nodePoly S h p).degree < (2 ^ (h + 1) : ℕ) :=
  degree_le_natDegree.trans_lt (by
    have := natDegree_nodePoly_le S h p
    have h2 : 2 ^ h < 2 ^ (h + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact_mod_cast this.trans_lt h2)

/-- **The tree**: after `h` levels, block `p` holds `nodePoly S h p` on `ptK [0, 2^(h+1))`. -/
theorem lam_eval {N : ℕ} (hN64 : N ≤ 64) (S : List ℕ) : ∀ h, h + 1 ≤ N → ∀ p x, x < 2 ^ (h + 1) →
    lam N S h (p * 2 ^ (h + 1) + x) = (nodePoly S h p).eval (ptK x)
  | 0, _, p, x, hx => by
    have hx2 : x < 2 := by simpa using hx
    have e1 : (p * 2 ^ (0 + 1) + x) / 2 = p := by omega
    have e2 : (p * 2 ^ (0 + 1) + x) % 2 = x := by omega
    simp only [lam, leafRow, e1, e2, nodePoly, pow_zero, range_one, prod_singleton, mul_one,
      add_zero]
    split_ifs
    · simp
    · simp only [eval_sub, eval_X, eval_C]
      rw [add_comm, CharTwo.sub_eq_add]
  | h + 1, hh, p, x, hx => by
    have ih := lam_eval hN64 S h (by omega)
    have hp2 : 2 ^ (h + 1 + 1) = 2 ^ (h + 1) + 2 ^ (h + 1) := by rw [pow_succ]; ring
    have e1 : (p * 2 ^ (h + 1 + 1) + x) / 2 ^ (h + 2) = p := by
      rw [show h + 1 + 1 = h + 2 from rfl, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt hx, Nat.zero_add]
    have e2 : (p * 2 ^ (h + 1 + 1) + x) % 2 ^ (h + 2) = x := by
      rw [show h + 1 + 1 = h + 2 from rfl, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
    simp only [lam, treeLevel, e1, e2]
    rw [nodePoly_succ, eval_mul]
    congr 1
    · refine extend_eval (ℓ := h + 1) (by omega) hN64 _ (degree_nodePoly_lt S h (2 * p)) _ (fun j hj => ?_) x hx
      rw [← ih (2 * p) j hj]
      congr 1
      rw [pow_succ]; ring
    · refine extend_eval (ℓ := h + 1) (by omega) hN64 _ (degree_nodePoly_lt S h (2 * p + 1)) _
        (fun j hj => ?_) x hx
      rw [← ih (2 * p + 1) j hj]
      congr 1
      rw [pow_succ]; ring

/-- **The root holds `Λ`** on `ptK [0, 2^(ℓ+1))`. -/
theorem lam_root {N ℓ : ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (S : List ℕ) {i : ℕ}
    (hi : i < 2 ^ (ℓ + 1)) : lam N S ℓ i = (lamPoly S ℓ).eval (ptK i) := by
  have := lam_eval hN64 S ℓ hN 0 i hi
  rwa [Nat.zero_mul, Nat.zero_add, ← lamPoly_eq] at this

end Lvm6.FD
