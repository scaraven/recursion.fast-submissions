import LvmQKeccakSpec
import LvmQSumcheck

-- ===== merged from `LvmQEqKeccakAlg` (GOLF module merge: `LvmQEqKeccakAlg.lean` is now a stub importing `LvmQEqKeccakAlg3`) =====
section

/-!
# QA1: `F`'s materialised Keccak weights = the circuit's structured forms (`Lvm.FE` algebra)

Pure algebra on `Lvm.FE` (no reader, no builder). `F` = `LvmDecideKeccak` (leanVM's verifier on the
fast field types); the structured forms are `LvmQKeccakSpec`'s.

* `lt_getD`: `keccakLinearTranspose` in closed form, `θᵀ` of the weights moved back through `ρπ`
  (adapted from WP-2's `LvmKeccakLinear`, which proves it over `LeanVM.Parameters.E` for the
  ported verifier; here for `F`'s copy over `Lvm.FE`).
* **`lane_dot`**: `Σ_z u(z)·Lᵀ(prodW A B)(64ℓ + z) = laneForm B (rotSum u A) ℓ`; **`weighted_kForm`**:
  `F`'s final-check weight on `Lᵀ(prodW A B)` is `kForm`.
* `eqAt_prod` (product formula of `eqKernel`), `eqAt_split`, **`shift_LH`**: the rotated `eq` sum
  through the guest's two 8-entry tables.
* **`iota_flips`**: `F`'s iota sum on `Lᵀ(prodW A B)` for every round constant is
  `Σ_{i<7} rcBit·flipForm` (round constants use bits `2^i − 1` only).
* First claim (`w1 = lanes ⊗ x^z`): **`weighted_first`** (`(Σ f·lanes)·indexMle b`), **`iota_first`**.
* `keccakOpen`'s fold: `slotWeights_getD`, `foldAll_eq` (adapted from WP-2's
  `LvmKeccakSlotWeights`), **`open_committed`**, **`open_input`**.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Finset

/-! ## Sums and lists (adapted from rf-lvm-QA1 LvmKeccakLinear.lean, WP-2) -/

theorem listSum_range (f : ℕ → FE) (n : ℕ) :
    ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem sumE_range (f : ℕ → FE) (n : ℕ) : sumE ((List.range n).map f) = ∑ y ∈ range n, f y := by
  rw [sumE_eq_sum, listSum_range]

theorem sum_range_mul' (a b : ℕ) (F : ℕ → FE) :
    ∑ p ∈ range (a * b), F p = ∑ i ∈ range a, ∑ k ∈ range b, F (b * i + k) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.mul_comm a b]

theorem array_getD_toArray' (l : List FE) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem setIfInBounds_getD' (a : Array FE) (i p : ℕ) (x : FE) :
    (a.setIfInBounds i x).getD p 0 = if i = p ∧ i < a.size then x else a.getD p 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all
  omega

/-- A row of a grid flattened by rows. -/
theorem flatMap_getD' (F : ℕ → ℕ → FE) (m : ℕ) :
    ∀ (n x z : ℕ), x < n → z < m →
      ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).getD (m * x + z) 0 = F x z
  | 0, _, _, hx, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, x, z, hx, hz => by
    have hlen : ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
      simp [List.length_flatMap, List.sum_replicate]
    rw [List.range_succ, List.flatMap_append]
    by_cases hxn : x < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact flatMap_getD' F m n x z hxn hz
    · have : x = n := by (clear * - hx hxn; omega)
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; nlinarith), hlen]
      simp [Nat.mul_comm, hz, List.getD_eq_getElem?_getD]

theorem flatMap_length' (F : ℕ → ℕ → FE) (m n : ℕ) :
    ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
  simp [List.length_flatMap, List.sum_replicate]

/-! ## `keccakLinearTranspose` in closed form (adapted from WP-2's `LvmKeccakLinear`) -/

/-- A θ column sum: `Σ_y v(x + 5y, z)`. -/
def colLE (v : ℕ → FE) (x z : ℕ) : FE := ∑ y ∈ range 5, v (64 * (x + 5 * y) + z)

/-- The transpose of θ: `g` plus the columns `x + 1` at `z` and `x − 1` at `z + 1`. -/
def thetaTE (g : ℕ → FE) (p : ℕ) : FE :=
  g p + colLE g ((p / 64 % 5 + 1) % 5) (p % 64) + colLE g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64)

/-- Where `ρπ` takes position `p` from: lane `π(ℓ)`, slice `z + ρ_ℓ`. -/
def rhoPiDstE (p : ℕ) : ℕ := 64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64

/-- θ's input weights after ρπ. -/
def gOfE (w : List FE) (p : ℕ) : FE := w.getD (rhoPiDstE p) 0

theorem inner_loopE (W : ℕ → FE) (lane : ℕ) (g : Array FE) :
    ∀ Z, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).size =
        g.size ∧
      ∀ p, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).getD p 0 =
        if 64 * lane ≤ p ∧ p < 64 * lane + Z ∧ p < g.size then W (p - 64 * lane)
        else g.getD p 0
  | 0 => ⟨rfl, fun p ↦ by simp; omega⟩
  | Z + 1 => by
    obtain ⟨hs, hg⟩ := inner_loopE W lane g Z
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [hs], fun p ↦ ?_⟩
    rw [setIfInBounds_getD', hg p, hs]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; (clear hg hs; omega))

theorem outer_loopE (w : List FE) :
    ∀ L, L ≤ 25 →
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).size = 1600 ∧
      ∀ p, ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).getD p 0 = if p < 64 * L then gOfE w p else 0
  | 0, _ => ⟨by simp [keccakBits], fun p ↦ by
      simp [Array.getD_eq_getD_getElem?, keccakBits, Array.getElem?_replicate]
      split_ifs <;> rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, hg⟩ := outer_loopE w L (by omega)
    rw [List.range_succ (n := L), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_loopE
      (fun z ↦ w.toArray.getD (64 * keccakPi L + (z + keccakRho.getD L 0) % 64) 0) L
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)) 64
    refine ⟨hs'.trans hs, fun p ↦ ?_⟩
    rw [hg' p, hg p, hs]
    by_cases h1 : 64 * L ≤ p ∧ p < 64 * L + 64 ∧ p < 1600
    · rw [ite_eq_left h1, ite_eq_left (by (clear * - h1; omega)), array_getD_toArray', gOfE, rhoPiDstE]
      have e1 : p / 64 = L := by (clear * - h1; omega)
      have e2 : p % 64 = p - 64 * L := by (clear * - h1 e1; omega)
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by (clear * - h2; omega))]
      · rw [ite_eq_right h2, ite_eq_right (by (clear * - hL h1 h2; omega))]

theorem columns_getDE (A : Array FE) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
        sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
      (64 * x + z) 0 = colLE (fun p ↦ A.getD p 0) x z := by
  rw [array_getD_toArray', flatMap_getD' (fun x z ↦
    sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)) 64 5 x z hx hz]
  rw [sumE_range]
  rfl

theorem transposeList_getDE (A : Array FE) (g : ℕ → FE) (hA : ∀ p < 1600, A.getD p 0 = g p)
    {p : ℕ} (hp : p < 1600) :
    ((List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
      A.getD (64 * lane + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 1) % 5) + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0).getD p 0 = thetaTE g p := by
  have hp' : p = 64 * (p / 64) + p % 64 := by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
  conv_lhs => rw [hp']
  rw [flatMap_getD' _ 64 25 (p / 64) (p % 64) (by (clear * - hp; omega)) (Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)))]
  rw [columns_getDE _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) (Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))),
    columns_getDE _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) (Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))), ← hp', hA p hp]
  have hcol : ∀ x z, x < 5 → z < 64 → colLE (fun p ↦ A.getD p 0) x z = colLE g x z := by
    intro x z hx hz
    refine Finset.sum_congr rfl fun y hy ↦ ?_
    simp only [Finset.mem_range] at hy
    exact hA _ (by (clear * - hx hz hy; omega))
  rw [hcol _ _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) (Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))), hcol _ _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) (Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)))]
  rfl

/-- **`keccakLinearTranspose` in closed form** (`F`'s copy over `Lvm.FE`). -/
theorem lt_getD (w : List FE) {p : ℕ} (hp : p < 1600) :
    (keccakLinearTranspose w).getD p 0 = thetaTE (gOfE w) p := by
  obtain ⟨-, hg⟩ := outer_loopE w 25 le_rfl
  exact transposeList_getDE _ (gOfE w) (fun q hq ↦ by rw [hg, ite_eq_left (by omega)]) hp

theorem lt_length (w : List FE) : (keccakLinearTranspose w).length = 1600 := by
  unfold keccakLinearTranspose
  simp only []
  rw [flatMap_length']

end Lvm.Q1
end
-- ===== end of `LvmQEqKeccakAlg` =====

-- ===== merged from `LvmQEqKeccakAlg2` (GOLF module merge: `LvmQEqKeccakAlg2.lean` is now a stub importing `LvmQEqKeccakAlg3`) =====
section

/-!
# QA1: Keccak weight algebra, part 2 (lanes, the final-check weight, shifts, iota, first claim, openings)

See `LvmQEqKeccakAlg` for the overview.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Finset

/-! ## Product weights through the transpose: `lane_dot`, `weighted_kForm` -/

theorem keccakPi_lt {i : ℕ} (hi : i < 25) : keccakPi i < 25 := by
  unfold keccakPi; omega

theorem prodW_getD (A : ℕ → FE) (B : List FE) {j : ℕ} (hj : j < 1600) :
    (prodW A B).getD j 0 = A (j % 64) * B.getD (j / 64) 0 := by
  simp [prodW, keccakBits, List.getD_eq_getElem?_getD, hj]

theorem gOf_prodW (A : ℕ → FE) (B : List FE) {p : ℕ} (hp : p < 1600) :
    gOfE (prodW A B) p = A ((p % 64 + rho (p / 64)) % 64) * B.getD (keccakPi (p / 64)) 0 := by
  have hpi := keccakPi_lt (i := p / 64) (by omega)
  rw [gOfE, prodW_getD A B (by unfold rhoPiDstE; (clear * - hpi; omega)), rhoPiDstE]
  have e1 : (64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64) % 64 =
      (p % 64 + keccakRho.getD (p / 64) 0) % 64 := by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
  have e2 : (64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64) / 64 =
      keccakPi (p / 64) := by (clear * - e1; omega)
  rw [e1, e2]
  rfl

/-- A column's dot with `u` at a slice offset `c`. -/
theorem col_dot (A u : ℕ → FE) (B : List FE) {x : ℕ} (hx : x < 5) (c : ℕ) :
    ∑ z ∈ range 64, u z * colLE (gOfE (prodW A B)) x ((z + c) % 64) =
      ∑ y ∈ range 5, B.getD (keccakPi (x + 5 * y)) 0 *
        ∑ z ∈ range 64, u z * A (((z + c) % 64 + rho (x + 5 * y)) % 64) := by
  simp only [colLE, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy ↦ Finset.sum_congr rfl fun z hz ↦ ?_
  simp only [Finset.mem_range] at hy hz
  rw [gOf_prodW A B (by (clear * - hx hy; omega))]
  have e1 : (64 * (x + 5 * y) + (z + c) % 64) % 64 = (z + c) % 64 := by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
  have e2 : (64 * (x + 5 * y) + (z + c) % 64) / 64 = x + 5 * y := by (clear * - e1; omega)
  rw [e1, e2]
  ring

/-- **A lane of the transposed product weights against a slice vector `u`.** -/
theorem lane_dot (A u : ℕ → FE) (B : List FE) {l : ℕ} (hl : l < 25) :
    sumE ((List.range 64).map fun z => u z * (keccakLinearTranspose (prodW A B)).getD (64 * l + z) 0) =
      laneForm B (rotSum u A) l := by
  rw [sumE_range]
  have hz : ∀ z ∈ range 64, u z * (keccakLinearTranspose (prodW A B)).getD (64 * l + z) 0 =
      u z * gOfE (prodW A B) (64 * l + z) +
        u z * colLE (gOfE (prodW A B)) ((l % 5 + 1) % 5) ((z + 0) % 64) +
        u z * colLE (gOfE (prodW A B)) ((l % 5 + 4) % 5) ((z + 1) % 64) := by
    intro z hz
    simp only [Finset.mem_range] at hz
    rw [lt_getD _ (by omega), thetaTE]
    have e1 : (64 * l + z) / 64 % 5 = l % 5 := by (clear * - hz; omega)
    have e2 : (64 * l + z) % 64 = z := by (clear * - hz e1; omega)
    have e3 : (z + 0) % 64 = z := by (clear * - e1 e2; omega)
    rw [e1, e2, e3, mul_add, mul_add]
  rw [Finset.sum_congr rfl hz, Finset.sum_add_distrib, Finset.sum_add_distrib,
    col_dot A u B (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), col_dot A u B (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))]
  have h1 : ∑ z ∈ range 64, u z * gOfE (prodW A B) (64 * l + z) =
      B.getD (keccakPi l) 0 * rotSum u A (rho l) := by
    rw [rotSum, sumE_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    simp only [Finset.mem_range] at hz
    rw [gOf_prodW A B (by omega)]
    have e1 : (64 * l + z) % 64 = z := by (clear * - hz; omega)
    have e2 : (64 * l + z) / 64 = l := by (clear * - e1; omega)
    rw [e1, e2]
    ring
  have h2 : ∀ x, ∑ y ∈ range 5, B.getD (keccakPi (x + 5 * y)) 0 *
        ∑ z ∈ range 64, u z * A (((z + 0) % 64 + rho (x + 5 * y)) % 64) =
      sumE ((List.range 5).map fun y => B.getD (keccakPi (x + 5 * y)) 0 * rotSum u A (rho (x + 5 * y))) := by
    intro x
    rw [sumE_range]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [rotSum, sumE_range]
    simp only [Nat.add_zero, Nat.mod_add_mod]
  have h3 : ∀ x, ∑ y ∈ range 5, B.getD (keccakPi (x + 5 * y)) 0 *
        ∑ z ∈ range 64, u z * A (((z + 1) % 64 + rho (x + 5 * y)) % 64) =
      sumE ((List.range 5).map fun y =>
        B.getD (keccakPi (x + 5 * y)) 0 * rotSum u A ((rho (x + 5 * y) + 1) % 64)) := by
    intro x
    rw [sumE_range]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [rotSum, sumE_range]
    rw [Finset.sum_congr rfl (fun z _ => by
      rw [show ((z + 1) % 64 + rho (x + 5 * y)) % 64 = (z + (rho (x + 5 * y) + 1) % 64) % 64 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)])]
  rw [h1, h2, h3]
  rfl

/-- Regroup `25` lanes by column. -/
theorem regroup25 (f : List FE) (G : ℕ → FE) :
    ∑ l ∈ range 25, f.getD l 0 * G (l % 5) = ∑ x ∈ range 5, (∑ y ∈ range 5, f.getD (x + 5 * y) 0) * G x := by
  rw [show (25 : ℕ) = 5 * 5 from rfl, sum_range_mul', Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  simp only [Finset.mem_range] at hx
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [show (5 * y + x) % 5 = x by omega, Nat.add_comm (5 * y) x]

/-- The column part of a lane's form (a function of `x = ℓ mod 5`). -/
def colForm (B : List FE) (R : ℕ → FE) (x : ℕ) : FE :=
  sumE ((List.range 5).map fun y => B.getD (keccakPi ((x + 1) % 5 + 5 * y)) 0 *
      R (rho ((x + 1) % 5 + 5 * y))) +
    sumE ((List.range 5).map fun y => B.getD (keccakPi ((x + 4) % 5 + 5 * y)) 0 *
      R ((rho ((x + 4) % 5 + 5 * y) + 1) % 64))

theorem laneForm_split (B : List FE) (R : ℕ → FE) (l : ℕ) :
    laneForm B R l = B.getD (keccakPi l) 0 * R (rho l) + colForm B R (l % 5) := by
  simp only [laneForm, colForm, add_assoc]

/-- **`F`'s final-check weight on transposed product weights is `kForm`.** -/
theorem weighted_kForm (A : ℕ → FE) (B f e : List FE) :
    weightedF f e (keccakLinearTranspose (prodW A B)) = kForm B (rotSum (fun z => e.getD z 0) A) f := by
  unfold weightedF
  rw [sumE_range, Finset.sum_congr rfl (fun l hl => by
    rw [lane_dot A (fun z => e.getD z 0) B (Finset.mem_range.mp hl), laneForm_split, mul_add]),
    Finset.sum_add_distrib, regroup25]
  simp only [kForm, sumE_range, colForm]
/-! ## `eqKernel` entries: the product formula, the split, the rotated sum -/

theorem eqKernel_snoc (p : List FE) (r : FE) :
    eqKernel (p ++ [r]) = (eqKernel p).map (· * (1 + r)) ++ (eqKernel p).map (· * r) := by
  simp [eqKernel, List.foldl_append]

theorem eqKernel_length : ∀ (p : List FE), (eqKernel p).length = 2 ^ p.length := by
  intro p
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p r ih =>
    rw [eqKernel_snoc, List.length_append, List.length_map, List.length_map, ih, List.length_append,
      List.length_singleton, pow_succ]; ring

theorem getD_map_mul (l : List FE) (c : FE) (z : ℕ) : (l.map (· * c)).getD z 0 = l.getD z 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[z]? <;> simp

/-- The product formula's factors. -/
def eqProd (p : List FE) (z : ℕ) : FE :=
  ∏ t ∈ range p.length, (if z.testBit t then p.getD t 0 else 1 + p.getD t 0)

/-- **`eq(p, z) = Π_t (bit t of z ? p_t : 1 + p_t)`** below `2^|p|`. -/
theorem eqAt_prod : ∀ (p : List FE) {z : ℕ}, z < 2 ^ p.length → eqAt p z = eqProd p z := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro z hz; simp at hz; subst hz; simp [eqAt, eqKernel, eqProd]
  | append_singleton p r ih =>
    intro z hz
    have hl := eqKernel_length p
    rw [List.length_append, List.length_singleton, pow_succ] at hz
    have hget : ∀ t < p.length, (p ++ [r]).getD t 0 = p.getD t 0 := by
      intro t ht; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left ht]
    have hlast : (p ++ [r]).getD p.length 0 = r := by simp [List.getD_eq_getElem?_getD]
    unfold eqProd
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ, hlast]
    rw [Finset.prod_congr rfl (fun t ht => by rw [hget t (Finset.mem_range.mp ht)])]
    unfold eqAt
    rw [eqKernel_snoc]
    by_cases hz' : z < 2 ^ p.length
    · rw [List.getD_append _ _ _ _ (by simp [hl, hz']), getD_map_mul]
      have := ih hz'
      unfold eqAt eqProd at this
      rw [this, Nat.testBit_lt_two_pow hz']
      simp
    · obtain ⟨z', rfl⟩ : ∃ z', z = 2 ^ p.length + z' := ⟨z - 2 ^ p.length, by (clear * - hl hz'; omega)⟩
      have hz'' : z' < 2 ^ p.length := by (clear * - hz; omega)
      rw [List.getD_append_right _ _ _ _ (by simp [hl]), List.length_map, hl,
        show 2 ^ p.length + z' - 2 ^ p.length = z' by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), getD_map_mul]
      have := ih hz''
      unfold eqAt eqProd at this
      rw [this, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hz'']
      simp only [Bool.not_false, ite_true]
      congr 1
      refine Finset.prod_congr rfl fun t ht => ?_
      rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp ht)]

/-- **`eq` of a 6-point splits** into its low and high three coordinates. -/
theorem eqAt_split {a : List FE} (ha : a.length = 6) {z : ℕ} (hz : z < 64) :
    eqAt a z = eqAt (a.take 3) (z % 8) * eqAt (a.drop 3) (z / 8) := by
  rw [eqAt_prod a (by rw [ha]; omega), eqAt_prod _ (by simp [ha]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)),
    eqAt_prod _ (by simp [ha]; (clear * - hz; omega))]
  unfold eqProd
  rw [ha, show (6 : ℕ) = 3 + 3 from rfl, Finset.prod_range_add]
  simp only [List.length_take, List.length_drop, ha, show min 3 6 = 3 from rfl,
    show 6 - 3 = 3 from rfl]
  congr 1
  · refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    have hb : (z % 8).testBit t = z.testBit t := by
      rw [show (8 : ℕ) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]; simp [ht']
    have hg : (a.take 3).getD t 0 = a.getD t 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_take, ht']
    rw [hb, hg]
  · refine Finset.prod_congr rfl fun t ht => ?_
    have hb : (z / 8).testBit t = z.testBit (3 + t) := by
      rw [show (8 : ℕ) = 2 ^ 3 from rfl, Nat.testBit_div_two_pow, Nat.add_comm]
    have hg : (a.drop 3).getD t 0 = a.getD (3 + t) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hb, hg]

/-- **The rotated `eq` sum through the guest's tables** (`keccak_shifts_eq`). -/
theorem shift_LH {a b : List FE} (ha : a.length = 6) (hb : b.length = 6) {r : ℕ} (hr : r < 64) :
    rotSum (eqAt b) (eqAt a) r = shiftLH a b r := by
  have hterm : ∀ zh < 8, ∀ zl < 8, eqAt b (8 * zh + zl) * eqAt a ((8 * zh + zl + r) % 64) =
      (eqAt (b.take 3) zl * eqAt (a.take 3) ((zl + r % 8) % 8)) *
        (eqAt (b.drop 3) zh * eqAt (a.drop 3) ((zh + (r / 8 + (zl + r % 8) / 8) % 8) % 8)) := by
    intro zh hzh zl hzl
    rw [eqAt_split hb (by (clear * - hzh hzl; omega)), eqAt_split ha (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))]
    have e1 : (8 * zh + zl) % 8 = zl := by (clear * - hzl; omega)
    have e2 : (8 * zh + zl) / 8 = zh := by (clear * - e1; omega)
    have e3 : (8 * zh + zl + r) % 64 % 8 = (zl + r % 8) % 8 := by (clear * - e1; omega)
    have e4 : (8 * zh + zl + r) % 64 / 8 = (zh + (r / 8 + (zl + r % 8) / 8) % 8) % 8 := by (clear * - e1 e3; omega)
    rw [e1, e2, e3, e4]
    ring
  unfold rotSum
  rw [sumE_range, show (64 : ℕ) = 8 * 8 from rfl, sum_range_mul',
    Finset.sum_congr rfl (fun zh hzh => Finset.sum_congr rfl (fun zl hzl =>
      hterm zh (Finset.mem_range.mp hzh) zl (Finset.mem_range.mp hzl))), Finset.sum_comm]
  simp only [← Finset.mul_sum]
  unfold shiftLH lowTab highTab
  simp only [sumE_range, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun zl hzl => ?_
  have hzl' := Finset.mem_range.mp hzl
  rcases (show (zl + r % 8) / 8 = 0 ∨ (zl + r % 8) / 8 = 1 by (clear * - hzl'; omega)) with hc | hc
  · rw [hc, if_pos rfl, if_neg (by decide), zero_mul, Nat.add_zero, add_zero,
      Nat.mod_eq_of_lt (show r / 8 < 8 by (clear * - hr; omega))]
  · rw [hc, if_neg (by decide), if_pos rfl, zero_mul, zero_add]

/-! ## The iota term -/

/-- Round constants use the bits `2^i − 1` only. (Decided as "each constant is a submask of
`Σ_i 2^(2^i − 1)`" plus the 64 bits of that mask, not over the 24 · 64 pairs: 0.6 s → 0.03 s.) -/
theorem rc_bits : ∀ rc ∈ keccakRC, ∀ z < 64, rc.toNat.testBit z = true →
    z ∈ (List.range 7).map iotaPos := by
  have hA : ∀ z < 64, (9223372039002292363 : Nat).testBit z = true → z ∈ (List.range 7).map iotaPos := by
    decide
  have hall : (keccakRC.all fun rc => rc.toNat &&& 9223372039002292363 == rc.toNat) = true := by decide
  intro rc hrc z hz ht
  have h1 := List.all_eq_true.mp hall rc hrc
  rw [beq_iff_eq] at h1
  apply hA z hz
  rw [← h1, Nat.testBit_land] at ht
  exact ((Bool.and_eq_true _ _).mp ht).2

theorem iotaPos_lt {i : ℕ} (hi : i < 7) : iotaPos i < 64 := by
  unfold iotaPos
  interval_cases i <;> decide

theorem sumE_filterMap (P : ℕ → Bool) (g : ℕ → FE) (n : ℕ) :
    sumE ((List.range n).filterMap fun z => if P z then some (g z) else none) =
      ∑ z ∈ range n, if P z then g z else 0 := by
  rw [sumE_eq_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.sum_append, ih, Finset.sum_range_succ]
    by_cases h : P n <;> simp [h]

/-- **`F`'s iota sum for a round constant** reads the weights at `2^i − 1` only. -/
theorem iotaF_reduce {rc : UInt64} (hrc : rc ∈ keccakRC) (W : List FE) :
    iotaF rc W = sumE ((List.range 7).map fun i => rcBit rc i * W.getD (iotaPos i) 0) := by
  unfold iotaF
  rw [sumE_filterMap (fun z => rc.toNat.testBit z) (fun z => W.getD z 0), sumE_range]
  have hsub : (range 7).image iotaPos ⊆ range 64 := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_range.mpr (iotaPos_lt (Finset.mem_range.mp hi))
  rw [← Finset.sum_subset hsub (fun z hz hz' => by
    have hz64 := Finset.mem_range.mp hz
    by_cases hb : rc.toNat.testBit z = true
    · exfalso
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (rc_bits rc hrc z hz64 hb)
      exact hz' (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (List.mem_range.mp hi), rfl⟩)
    · simp [hb])]
  rw [Finset.sum_image (fun i hi j hj hij => by
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    unfold iotaPos at hij
    interval_cases i <;> interval_cases j <;> simp_all)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold rcBit
  by_cases hb : rc.toNat.testBit (iotaPos i) = true <;> simp [hb]

/-- The weight at slice `2^i − 1` of lane `0` of the transposed product weights is `flipForm`. -/
theorem lt_flip (A : ℕ → FE) (B : List FE) {i : ℕ} (hi : i < 7) :
    (keccakLinearTranspose (prodW A B)).getD (iotaPos i) 0 = flipForm B A i := by
  have h := lane_dot A (fun z => if z = iotaPos i then 1 else 0) B (l := 0) (by decide)
  rw [sumE_range] at h
  simp only [Nat.mul_zero, Nat.zero_add, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range, iotaPos_lt hi, if_true] at h
  rw [h]
  unfold flipForm
  congr 1
  funext s
  unfold rotSum
  rw [sumE_range]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, iotaPos_lt hi, if_true]

/-- **The iota term on transposed product weights**, for every round constant. -/
theorem iota_flips {rc : UInt64} (hrc : rc ∈ keccakRC) (A : ℕ → FE) (B : List FE) :
    iotaF rc (keccakLinearTranspose (prodW A B)) =
      sumE ((List.range 7).map fun i => rcBit rc i * flipForm B A i) := by
  rw [iotaF_reduce hrc, List.map_congr_left (fun i hi => by rw [lt_flip A B (List.mem_range.mp hi)])]

end Lvm.Q1
end
-- ===== end of `LvmQEqKeccakAlg2` =====

/-!
# QA1: Keccak weight algebra, part 3 (the first claim, `keccakOpen`'s fold)

See `LvmQEqKeccakAlg` for the overview.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Finset

/-! ## The first claim: weights `lanes ⊗ x^z` -/

/-- `F`'s first-claim weights (`keccakFirstClaim`): lane `ℓ`'s weight times the word `x^z`. -/
def firstW (lanes : List FE) : List FE :=
  (List.range keccakBits).map fun j => lanes.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))

theorem toUInt64_two_pow : ∀ z < 64, (2 ^ z : ℕ).toUInt64 = (1 : UInt64) <<< z.toUInt64 := by
  decide

/-- `x^z` as `F` writes it (`eOfNat (2^z)`), `z < 64`. -/
theorem eOfNat_two_pow {z : ℕ} (hz : z < 64) : eOfNat (2 ^ z) = FE.ofK (FK.x ^ z) := by
  unfold eOfNat
  rw [show z = ((⟨z, hz⟩ : Fin 64) : ℕ) from rfl, FK.x_pow_word ⟨z, hz⟩, toUInt64_two_pow z hz]

theorem ofK_pow (a : FK) (n : ℕ) : FE.ofK (a ^ n) = FE.ofK a ^ n := map_pow FE.ofKRingHom a n

theorem firstW_getD (lanes : List FE) {l z : ℕ} (hl : l < 25) (hz : z < 64) :
    (firstW lanes).getD (64 * l + z) 0 = lanes.getD l 0 * gen ^ z := by
  have h : 64 * l + z < 1600 := by omega
  simp only [firstW, keccakBits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h, Option.map_some, Option.getD_some]
  rw [show (64 * l + z) / 64 = l by (clear * - hz; omega), show (64 * l + z) % 64 = z by (clear * - hz; omega), eOfNat_two_pow hz,
    ofK_pow]
  rfl

/-- `Σ_{z<2^n} eq(β, z)·g^z = Π_t ((1 + β_t) + β_t·g^(2^t))` (product formula). -/
theorem sum_eqProd_pow (β : ℕ → FE) (g : FE) : ∀ n : ℕ,
    ∑ z ∈ range (2 ^ n), (∏ t ∈ range n, (if z.testBit t then β t else 1 + β t)) * g ^ z =
      ∏ t ∈ range n, ((1 + β t) + β t * g ^ (2 ^ t))
  | 0 => by simp
  | n + 1 => by
    have h1 : ∑ z ∈ range (2 ^ n), (∏ t ∈ range (n + 1), (if z.testBit t then β t else 1 + β t)) * g ^ z =
        ∑ z ∈ range (2 ^ n), (∏ t ∈ range n, (if z.testBit t then β t else 1 + β t)) * g ^ z * (1 + β n) := by
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz' := Finset.mem_range.mp hz
      rw [Finset.prod_range_succ, Nat.testBit_lt_two_pow hz']
      simp only [Bool.false_eq_true, ite_false]
      ring
    have h2 : ∑ z ∈ range (2 ^ n),
        (∏ t ∈ range (n + 1), (if (2 ^ n + z).testBit t then β t else 1 + β t)) * g ^ (2 ^ n + z) =
        ∑ z ∈ range (2 ^ n), (∏ t ∈ range n, (if z.testBit t then β t else 1 + β t)) * g ^ z *
          (β n * g ^ (2 ^ n)) := by
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz' := Finset.mem_range.mp hz
      rw [Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hz', pow_add]
      simp only [Bool.not_false, ite_true]
      rw [Finset.prod_congr rfl (fun t ht => by rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp ht)])]
      ring
    rw [pow_succ, show 2 ^ n * 2 = 2 ^ n + 2 ^ n by ring, Finset.sum_range_add, h1, h2,
      Finset.prod_range_succ, ← sum_eqProd_pow β g n, ← Finset.sum_mul, ← Finset.sum_mul, ← mul_add]

theorem indexMleFrom_eq : ∀ (rs : List FE) (gp acc : FE),
    indexMleFrom gp rs acc = acc * ∏ i ∈ range rs.length, (1 + rs.getD i 0 * (1 + gp ^ (2 ^ i)))
  | [], gp, acc => by simp [indexMleFrom]
  | r :: rs, gp, acc => by
    rw [indexMleFrom, indexMleFrom_eq rs, List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, pow_one]
    rw [Finset.prod_congr rfl (fun i _ => by rw [← pow_mul, ← pow_succ']), mul_assoc,
      mul_comm (∏ i ∈ range rs.length, _)]

/-- `Σ_z eq(b, z)·x^z = indexMle b` for a six-point. -/
theorem sum_eq_gen_pow {b : List FE} (hb : b.length = 6) :
    ∑ z ∈ range 64, eqAt b z * gen ^ z = indexMle b := by
  rw [Finset.sum_congr rfl (fun z hz => by
    rw [eqAt_prod b (by rw [hb]; exact Finset.mem_range.mp hz)])]
  unfold eqProd indexMle
  rw [hb, show (64 : ℕ) = 2 ^ 6 from rfl, sum_eqProd_pow (fun t => b.getD t 0) gen 6, indexMleFrom_eq, hb,
    one_mul]
  refine Finset.prod_congr rfl fun t _ => by ring

/-- **The first claim's final-check weight**: `(Σ_ℓ f(ℓ)·lanes(ℓ))·indexMle b`. -/
theorem weighted_first (f lanes b : List FE) (hb : b.length = 6) :
    weightedF f (eqKernel b) (firstW lanes) =
      sumE ((List.range 25).map fun l => f.getD l 0 * lanes.getD l 0) * indexMle b := by
  unfold weightedF
  rw [sumE_range, sumE_range, Finset.sum_mul, ← sum_eq_gen_pow hb]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [sumE_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [firstW_getD lanes (Finset.mem_range.mp hl) (Finset.mem_range.mp hz)]
  unfold eqAt
  ring

/-- **The first claim's iota term**, per bit: `Σ_i rcBit_i · lanes(0)·x^(2^i−1)`. -/
theorem iota_first {rc : UInt64} (hrc : rc ∈ keccakRC) (lanes : List FE) :
    iotaF rc (firstW lanes) =
      sumE ((List.range 7).map fun i => rcBit rc i * (lanes.getD 0 0 * FE.ofK (FK.x ^ iotaPos i))) := by
  rw [iotaF_reduce hrc]
  refine congrArg sumE (List.map_congr_left (fun i hi => ?_))
  have h := firstW_getD lanes (l := 0) (by decide) (iotaPos_lt (List.mem_range.mp hi))
  rw [Nat.mul_zero, Nat.zero_add] at h
  rw [h, show gen = FE.ofK FK.x from rfl, ← ofK_pow]

end Lvm.Q1
