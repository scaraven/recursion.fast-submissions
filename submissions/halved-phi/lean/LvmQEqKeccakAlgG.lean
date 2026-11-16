-- New for lvm2 E2F (E2F-QH4): the Keccak GKR verifier's weight algebra (`LvmQEqKeccakAlg`…`Alg4`) over a field
-- parameter `F`, on `V`'s generic definitions (`LvmE2VBase`, `LvmE2VProg`), for the circuit at `E2` and `E3`.
import LvmE2VKec
import LvmQKeccakSpec

/-!
# The Keccak weight algebra over a field

The circuit never writes a claim's `1600` position weights: it keeps the slice challenges `a` and the lane
weights `B` of the product weights `w(64ℓ + z) = eq(a, z)·B(ℓ)` and evaluates `Lᵀ(w)` (`linearTransposeF`)
through the guest's structured forms (`LvmQKeccakSpec`). Here the forms and their equalities with `V`'s
materialised weights hold over any field `F` (the `E3` statements of `LvmQEqKeccakAlg*` are their instances at
`FE`, the `E2` circuit's at `FE2`):

* forms: `eqAtG`, `prodWG`, `rotSumG`, `laneFormF` (**`lt_posF`**: entry `j` of `Lᵀ(prodW A B)` is a lane form),
  `weightedFG`, `lowTabG`/`highTabG`/`shiftLHG`, `flipFormG`,
  `rcBitG`, `iotaFG`, `firstWG` (`lanes ⊗ g^z`), `indexProdG`;
* **`lane_dotG`**: `Σ_z u(z)·Lᵀ(prodW A B)(64ℓ + z) = laneForm B (rotSum u A) ℓ`;
* `eqAtG_prod`, `eqAtG_split`, **`shift_LHG`** (the rotated `eq` sum through two 8-entry tables);
* **`iota_flipsG`**, **`iota_firstG`** (round constants use bits `2^i − 1`);
* **`weighted_firstG`** (`Σ_ℓ f(ℓ)·lanes(ℓ)·indexProd b`);
* the openings' fold (`slotWeightsF`, `foldRowsF`): **`open_committedG`**, **`open_inputG`**,
  `open_input_ltG`, `open_committed_firstG`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.E2V Finset

/-! ## Constants -/

theorem keccakPi_ltG {i : ℕ} (hi : i < 25) : keccakPi i < 25 := by
  unfold keccakPi; omega

theorem iotaPos_ltG {i : ℕ} (hi : i < 7) : iotaPos i < 64 := by
  unfold iotaPos
  interval_cases i <;> decide

/-- Round constants use the bits `2^i − 1` only (a submask of `Σ_i 2^(2^i − 1)`). -/
theorem rc_bitsG : ∀ rc ∈ keccakRC, ∀ z < 64, rc.toNat.testBit z = true →
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

section

variable {F : Type} [Field F]

/-! ## The forms -/

/-- `eq(a, z)`: entry `z` of `eqKernelF a`. -/
def eqAtG (a : List F) (z : ℕ) : F := (eqKernelF a).getD z 0

/-- The product weights `w(64ℓ + z) = A(z)·B(ℓ)`. -/
def prodWG (A : ℕ → F) (B : List F) : List F :=
  (List.range keccakBits).map fun j => A (j % 64) * B.getD (j / 64) 0

/-- `Σ_{z<64} u(z)·A((z + s) mod 64)`. -/
def rotSumG (u A : ℕ → F) (s : ℕ) : F := sumF ((List.range 64).map fun z => u z * A ((z + s) % 64))

/-- **Lane `ℓ`'s form** from `R = rotSum u A` (`laneForm`). -/
def laneFormF (B : List F) (R : ℕ → F) (l : ℕ) : F :=
  B.getD (keccakPi l) 0 * R (rho l) +
  sumF ((List.range 5).map fun y =>
    B.getD (keccakPi ((l % 5 + 1) % 5 + 5 * y)) 0 * R (rho ((l % 5 + 1) % 5 + 5 * y))) +
  sumF ((List.range 5).map fun y =>
    B.getD (keccakPi ((l % 5 + 4) % 5 + 5 * y)) 0 * R ((rho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64))

/-- `Σ_{ℓ<25} f(ℓ) Σ_{z<64} e(z)·W(64ℓ + z)`. -/
def weightedFG (f e W : List F) : F :=
  sumF ((List.range 25).map fun l => f.getD l 0 * sumF ((List.range 64).map fun z => e.getD z 0 * W.getD (64 * l + z) 0))

/-- `L_c(r_l)` (`lowTab`). -/
def lowTabG (a b : List F) (c rl : ℕ) : F :=
  sumF ((List.range 8).map fun z =>
    if (z + rl) / 8 = c then eqAtG (b.take 3) z * eqAtG (a.take 3) ((z + rl) % 8) else 0)

/-- `H(k)` (`highTab`). -/
def highTabG (a b : List F) (k : ℕ) : F :=
  sumF ((List.range 8).map fun z => eqAtG (b.drop 3) z * eqAtG (a.drop 3) ((z + k) % 8))

/-- `shift(r)` from the tables (`shiftLH`). -/
def shiftLHG (a b : List F) (r : ℕ) : F :=
  lowTabG a b 0 (r % 8) * highTabG a b (r / 8) + lowTabG a b 1 (r % 8) * highTabG a b ((r / 8 + 1) % 8)

/-- `flip_i`, the weight of slice `2^i − 1` of lane `0` as a lane form (`flipForm`). -/
def flipFormG (B : List F) (A : ℕ → F) (i : ℕ) : F :=
  laneFormF B (fun s => A ((iotaPos i + s) % 64)) 0

/-- Bit `2^i − 1` of a round constant (`rcBit`). -/
def rcBitG (rc : UInt64) (i : ℕ) : F := if rc.toNat.testBit (iotaPos i) then 1 else 0

/-- The iota sum on weights `W`: `Σ_{z ∈ bits(rc)} W(z)` (`iotaF`). -/
def iotaFG (rc : UInt64) (W : List F) : F :=
  sumF ((List.range 64).filterMap fun z => if rc.toNat.testBit z then some (W.getD z 0) else none)

/-- The first claim's weights: lane `ℓ`'s weight times `g^z` (`firstW` at `g = x`). -/
def firstWG (g : F) (lanes : List F) : List F :=
  (List.range keccakBits).map fun j => lanes.getD (j / 64) 0 * g ^ (j % 64)

/-- `Π_t (1 + b_t·(1 + g^(2^t)))` (`indexMle` at `g = x`). -/
def indexProdG (g : F) (b : List F) : F := ∏ t ∈ range b.length, (1 + b.getD t 0 * (1 + g ^ (2 ^ t)))

/-! ## Product weights through the transpose: `lane_dotG` -/

theorem prodWG_getD (A : ℕ → F) (B : List F) {j : ℕ} (hj : j < 1600) :
    (prodWG A B).getD j 0 = A (j % 64) * B.getD (j / 64) 0 := by
  simp [prodWG, keccakBits, List.getD_eq_getElem?_getD, hj]

theorem prodWG_length (A : ℕ → F) (B : List F) : (prodWG A B).length = 1600 := by
  simp [prodWG, keccakBits]

theorem gOf_prodWG (A : ℕ → F) (B : List F) {p : ℕ} (hp : p < 1600) :
    gOfF (prodWG A B) p = A ((p % 64 + rho (p / 64)) % 64) * B.getD (keccakPi (p / 64)) 0 := by
  have hpi := keccakPi_ltG (i := p / 64) (by omega)
  have hd : LeanVM.Protocol.KeccakGkr.rhoPiDst p =
      64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64 := by
    unfold LeanVM.Protocol.KeccakGkr.rhoPiDst; rw [keccakPi_eqV, keccakRho_eqV]
  rw [gOfF, hd, prodWG_getD A B (by omega)]
  have e1 : (64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64) % 64 =
      (p % 64 + keccakRho.getD (p / 64) 0) % 64 := by omega
  have e2 : (64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64) / 64 =
      keccakPi (p / 64) := by omega
  rw [e1, e2]
  rfl

theorem col_dotG (A u : ℕ → F) (B : List F) {x : ℕ} (hx : x < 5) (c : ℕ) :
    ∑ z ∈ range 64, u z * colLF (gOfF (prodWG A B)) x ((z + c) % 64) =
      ∑ y ∈ range 5, B.getD (keccakPi (x + 5 * y)) 0 *
        ∑ z ∈ range 64, u z * A (((z + c) % 64 + rho (x + 5 * y)) % 64) := by
  simp only [colLF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy ↦ Finset.sum_congr rfl fun z hz ↦ ?_
  simp only [Finset.mem_range] at hy hz
  rw [gOf_prodWG A B (by omega)]
  have e1 : (64 * (x + 5 * y) + (z + c) % 64) % 64 = (z + c) % 64 := by omega
  have e2 : (64 * (x + 5 * y) + (z + c) % 64) / 64 = x + 5 * y := by omega
  rw [e1, e2]
  ring

/-- **A lane of the transposed product weights against a slice vector `u`.** -/
theorem lane_dotG (A u : ℕ → F) (B : List F) {l : ℕ} (hl : l < 25) :
    sumF ((List.range 64).map fun z => u z * (linearTransposeF (prodWG A B)).getD (64 * l + z) 0) =
      laneFormF B (rotSumG u A) l := by
  rw [sumF_map_range]
  have hz : ∀ z ∈ range 64, u z * (linearTransposeF (prodWG A B)).getD (64 * l + z) 0 =
      u z * gOfF (prodWG A B) (64 * l + z) +
        u z * colLF (gOfF (prodWG A B)) ((l % 5 + 1) % 5) ((z + 0) % 64) +
        u z * colLF (gOfF (prodWG A B)) ((l % 5 + 4) % 5) ((z + 1) % 64) := by
    intro z hz
    simp only [Finset.mem_range] at hz
    rw [linearTransposeF_getD _ (by omega), thetaTF]
    have e1 : (64 * l + z) / 64 % 5 = l % 5 := by omega
    have e2 : (64 * l + z) % 64 = z := by omega
    have e3 : (z + 0) % 64 = z := by omega
    rw [e1, e2, e3, mul_add, mul_add]
  rw [Finset.sum_congr rfl hz, Finset.sum_add_distrib, Finset.sum_add_distrib,
    col_dotG A u B (by omega), col_dotG A u B (by omega)]
  have h1 : ∑ z ∈ range 64, u z * gOfF (prodWG A B) (64 * l + z) =
      B.getD (keccakPi l) 0 * rotSumG u A (rho l) := by
    rw [rotSumG, sumF_map_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    simp only [Finset.mem_range] at hz
    rw [gOf_prodWG A B (by omega)]
    have e1 : (64 * l + z) % 64 = z := by omega
    have e2 : (64 * l + z) / 64 = l := by omega
    rw [e1, e2]
    ring
  have h2 : ∀ x, ∑ y ∈ range 5, B.getD (keccakPi (x + 5 * y)) 0 *
        ∑ z ∈ range 64, u z * A (((z + 0) % 64 + rho (x + 5 * y)) % 64) =
      sumF ((List.range 5).map fun y => B.getD (keccakPi (x + 5 * y)) 0 * rotSumG u A (rho (x + 5 * y))) := by
    intro x
    rw [sumF_map_range]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [rotSumG, sumF_map_range]
    simp only [Nat.add_zero, Nat.mod_add_mod]
  have h3 : ∀ x, ∑ y ∈ range 5, B.getD (keccakPi (x + 5 * y)) 0 *
        ∑ z ∈ range 64, u z * A (((z + 1) % 64 + rho (x + 5 * y)) % 64) =
      sumF ((List.range 5).map fun y =>
        B.getD (keccakPi (x + 5 * y)) 0 * rotSumG u A ((rho (x + 5 * y) + 1) % 64)) := by
    intro x
    rw [sumF_map_range]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [rotSumG, sumF_map_range]
    rw [Finset.sum_congr rfl (fun z _ => by
      rw [show ((z + 1) % 64 + rho (x + 5 * y)) % 64 = (z + (rho (x + 5 * y) + 1) % 64) % 64 by omega])]
  rw [h1, h2, h3]
  rfl

/-- **Entry `j` of the transposed product weights** is a lane form at slice `j mod 64` (`lt_pos` over `F`). -/
theorem lt_posF (A : ℕ → F) (B : List F) {j : ℕ} (hj : j < 1600) :
    (linearTransposeF (prodWG A B)).getD j 0 = laneFormF B (fun s => A ((j % 64 + s) % 64)) (j / 64) := by
  have h := lane_dotG A (fun z => if z = j % 64 then 1 else 0) B (l := j / 64) (by omega)
  rw [sumF_map_range] at h
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    show j % 64 < 64 from Nat.mod_lt _ (by omega), if_true] at h
  rw [show 64 * (j / 64) + j % 64 = j by omega] at h
  rw [h]
  congr 1
  funext s
  unfold rotSumG
  rw [sumF_map_range]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    show j % 64 < 64 from Nat.mod_lt _ (by omega), if_true]

/-! ## `eqKernelF` entries: the product formula, the split, the rotated sum -/

theorem getD_map_mulG (l : List F) (c : F) (z : ℕ) : (l.map (· * c)).getD z 0 = l.getD z 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[z]? <;> simp

/-- The product formula's factors. -/
def eqProdG (p : List F) (z : ℕ) : F :=
  ∏ t ∈ range p.length, (if z.testBit t then p.getD t 0 else 1 + p.getD t 0)

/-- **`eq(p, z) = Π_t (bit t of z ? p_t : 1 + p_t)`** below `2^|p|`. -/
theorem eqAtG_prod : ∀ (p : List F) {z : ℕ}, z < 2 ^ p.length → eqAtG p z = eqProdG p z := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro z hz; simp at hz; subst hz; simp [eqAtG, eqKernelF, eqProdG]
  | append_singleton p r ih =>
    intro z hz
    have hl := eqKernelF_length p
    rw [List.length_append, List.length_singleton, pow_succ] at hz
    have hget : ∀ t < p.length, (p ++ [r]).getD t 0 = p.getD t 0 := by
      intro t ht; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left ht]
    have hlast : (p ++ [r]).getD p.length 0 = r := by simp [List.getD_eq_getElem?_getD]
    unfold eqProdG
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ, hlast]
    rw [Finset.prod_congr rfl (fun t ht => by rw [hget t (Finset.mem_range.mp ht)])]
    unfold eqAtG
    rw [eqKernelF_append]
    by_cases hz' : z < 2 ^ p.length
    · rw [List.getD_append _ _ _ _ (by simp [hl, hz']), getD_map_mulG]
      have := ih hz'
      unfold eqAtG eqProdG at this
      rw [this, Nat.testBit_lt_two_pow hz']
      simp
    · obtain ⟨z', rfl⟩ : ∃ z', z = 2 ^ p.length + z' := ⟨z - 2 ^ p.length, by omega⟩
      have hz'' : z' < 2 ^ p.length := by omega
      rw [List.getD_append_right _ _ _ _ (by simp [hl]), List.length_map, hl,
        show 2 ^ p.length + z' - 2 ^ p.length = z' by omega, getD_map_mulG]
      have := ih hz''
      unfold eqAtG eqProdG at this
      rw [this, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hz'']
      simp only [Bool.not_false, ite_true]
      congr 1
      refine Finset.prod_congr rfl fun t ht => ?_
      rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp ht)]

/-- **`eq` of a 6-point splits** into its low and high three coordinates. -/
theorem eqAtG_split {a : List F} (ha : a.length = 6) {z : ℕ} (hz : z < 64) :
    eqAtG a z = eqAtG (a.take 3) (z % 8) * eqAtG (a.drop 3) (z / 8) := by
  rw [eqAtG_prod a (by rw [ha]; omega), eqAtG_prod _ (by simp [ha]; omega),
    eqAtG_prod _ (by simp [ha]; omega)]
  unfold eqProdG
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
theorem shift_LHG {a b : List F} (ha : a.length = 6) (hb : b.length = 6) {r : ℕ} (hr : r < 64) :
    rotSumG (eqAtG b) (eqAtG a) r = shiftLHG a b r := by
  have hterm : ∀ zh < 8, ∀ zl < 8, eqAtG b (8 * zh + zl) * eqAtG a ((8 * zh + zl + r) % 64) =
      (eqAtG (b.take 3) zl * eqAtG (a.take 3) ((zl + r % 8) % 8)) *
        (eqAtG (b.drop 3) zh * eqAtG (a.drop 3) ((zh + (r / 8 + (zl + r % 8) / 8) % 8) % 8)) := by
    intro zh hzh zl hzl
    rw [eqAtG_split hb (by omega), eqAtG_split ha (by omega)]
    have e1 : (8 * zh + zl) % 8 = zl := by omega
    have e2 : (8 * zh + zl) / 8 = zh := by omega
    have e3 : (8 * zh + zl + r) % 64 % 8 = (zl + r % 8) % 8 := by omega
    have e4 : (8 * zh + zl + r) % 64 / 8 = (zh + (r / 8 + (zl + r % 8) / 8) % 8) % 8 := by omega
    rw [e1, e2, e3, e4]
    ring
  unfold rotSumG
  rw [sumF_map_range, show (64 : ℕ) = 8 * 8 from rfl, sum_range_mulB,
    Finset.sum_congr rfl (fun zh hzh => Finset.sum_congr rfl (fun zl hzl =>
      hterm zh (Finset.mem_range.mp hzh) zl (Finset.mem_range.mp hzl))), Finset.sum_comm]
  simp only [← Finset.mul_sum]
  unfold shiftLHG lowTabG highTabG
  simp only [sumF_map_range, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun zl hzl => ?_
  have hzl' := Finset.mem_range.mp hzl
  rcases (show (zl + r % 8) / 8 = 0 ∨ (zl + r % 8) / 8 = 1 by omega) with hc | hc
  · rw [hc, if_pos rfl, if_neg (by decide), zero_mul, Nat.add_zero, add_zero,
      Nat.mod_eq_of_lt (show r / 8 < 8 by omega)]
  · rw [hc, if_neg (by decide), if_pos rfl, zero_mul, zero_add]

/-! ## The iota term -/

theorem sumF_filterMapG (P : ℕ → Bool) (g : ℕ → F) (n : ℕ) :
    sumF ((List.range n).filterMap fun z => if P z then some (g z) else none) =
      ∑ z ∈ range n, if P z then g z else 0 := by
  rw [sumF_eq_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.sum_append, ih, Finset.sum_range_succ]
    by_cases h : P n <;> simp [h]

/-- **The iota sum for a round constant** reads the weights at `2^i − 1` only. -/
theorem iotaF_reduceG {rc : UInt64} (hrc : rc ∈ keccakRC) (W : List F) :
    iotaFG rc W = sumF ((List.range 7).map fun i => rcBitG rc i * W.getD (iotaPos i) 0) := by
  unfold iotaFG
  rw [sumF_filterMapG (fun z => rc.toNat.testBit z) (fun z => W.getD z 0), sumF_map_range]
  have hsub : (range 7).image iotaPos ⊆ range 64 := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_range.mpr (iotaPos_ltG (Finset.mem_range.mp hi))
  rw [← Finset.sum_subset hsub (fun z hz hz' => by
    have hz64 := Finset.mem_range.mp hz
    by_cases hb : rc.toNat.testBit z = true
    · exfalso
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (rc_bitsG rc hrc z hz64 hb)
      exact hz' (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (List.mem_range.mp hi), rfl⟩)
    · simp [hb])]
  rw [Finset.sum_image (fun i hi j hj hij => by
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    unfold iotaPos at hij
    interval_cases i <;> interval_cases j <;> simp_all)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold rcBitG
  by_cases hb : rc.toNat.testBit (iotaPos i) = true <;> simp [hb]

/-- The weight at slice `2^i − 1` of lane `0` of the transposed product weights is `flipFormG`. -/
theorem lt_flipG (A : ℕ → F) (B : List F) {i : ℕ} (hi : i < 7) :
    (linearTransposeF (prodWG A B)).getD (iotaPos i) 0 = flipFormG B A i := by
  have h := lane_dotG A (fun z => if z = iotaPos i then 1 else 0) B (l := 0) (by decide)
  rw [sumF_map_range] at h
  simp only [Nat.mul_zero, Nat.zero_add, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range, iotaPos_ltG hi, if_true] at h
  rw [h]
  unfold flipFormG
  congr 1
  funext s
  unfold rotSumG
  rw [sumF_map_range]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, iotaPos_ltG hi, if_true]

/-- **The iota term on transposed product weights**, for every round constant. -/
theorem iota_flipsG {rc : UInt64} (hrc : rc ∈ keccakRC) (A : ℕ → F) (B : List F) :
    iotaFG rc (linearTransposeF (prodWG A B)) =
      sumF ((List.range 7).map fun i => rcBitG rc i * flipFormG B A i) := by
  rw [iotaF_reduceG hrc, List.map_congr_left (fun i hi => by rw [lt_flipG A B (List.mem_range.mp hi)])]

/-! ## The first claim: weights `lanes ⊗ g^z` -/

theorem firstWG_getD (g : F) (lanes : List F) {l z : ℕ} (hl : l < 25) (hz : z < 64) :
    (firstWG g lanes).getD (64 * l + z) 0 = lanes.getD l 0 * g ^ z := by
  have h : 64 * l + z < 1600 := by omega
  simp only [firstWG, keccakBits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h, Option.map_some, Option.getD_some]
  rw [show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega]

theorem firstWG_length (g : F) (lanes : List F) : (firstWG g lanes).length = 1600 := by
  simp [firstWG, keccakBits]

/-- `Σ_{z<2^n} eq(β, z)·g^z = Π_t ((1 + β_t) + β_t·g^(2^t))` (product formula). -/
theorem sum_eqProd_powG (β : ℕ → F) (g : F) : ∀ n : ℕ,
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
      Finset.prod_range_succ, ← sum_eqProd_powG β g n, ← Finset.sum_mul, ← Finset.sum_mul, ← mul_add]

/-- `Σ_z eq(b, z)·g^z = indexProd g b` for a six-point. -/
theorem sum_eq_gen_powG (g : F) {b : List F} (hb : b.length = 6) :
    ∑ z ∈ range 64, eqAtG b z * g ^ z = indexProdG g b := by
  rw [Finset.sum_congr rfl (fun z hz => by
    rw [eqAtG_prod b (by rw [hb]; exact Finset.mem_range.mp hz)])]
  unfold eqProdG indexProdG
  rw [hb, show (64 : ℕ) = 2 ^ 6 from rfl, sum_eqProd_powG (fun t => b.getD t 0) g 6]
  refine Finset.prod_congr rfl fun t _ => by ring

/-- **The first claim's final-check weight**: `(Σ_ℓ f(ℓ)·lanes(ℓ))·indexProd g b`. -/
theorem weighted_firstG (g : F) (f lanes b : List F) (hb : b.length = 6) :
    weightedFG f (eqKernelF b) (firstWG g lanes) =
      sumF ((List.range 25).map fun l => f.getD l 0 * lanes.getD l 0) * indexProdG g b := by
  unfold weightedFG
  rw [sumF_map_range, sumF_map_range, Finset.sum_mul, ← sum_eq_gen_powG g hb]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [sumF_map_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [firstWG_getD g lanes (Finset.mem_range.mp hl) (Finset.mem_range.mp hz)]
  unfold eqAtG
  ring

/-- **The first claim's iota term**, per bit: `Σ_i rcBit_i · lanes(0)·g^(2^i−1)`. -/
theorem iota_firstG (g : F) {rc : UInt64} (hrc : rc ∈ keccakRC) (lanes : List F) :
    iotaFG rc (firstWG g lanes) =
      sumF ((List.range 7).map fun i => rcBitG rc i * (lanes.getD 0 0 * g ^ iotaPos i)) := by
  rw [iotaF_reduceG hrc]
  refine congrArg sumF (List.map_congr_left (fun i hi => ?_))
  have h := firstWG_getD g lanes (l := 0) (by decide) (iotaPos_ltG (List.mem_range.mp hi))
  rw [Nat.mul_zero, Nat.zero_add] at h
  rw [h]

/-! ## The openings (`slotWeightsF` folded by `foldRowsF`) -/

/-- The folded slot weights at column `z`. -/
theorem open_fold_getDG (logSteps : ℕ) (claim : KClaim F) (first count : ℕ) (hfc : first + count ≤ 2)
    {slot : List F} (hs : slot.length = 6) {z : ℕ} (hz : z < 64) :
    (foldRowsF slot (slotWeightsF logSteps claim first count)).getD z 0 =
      ∑ o ∈ range 64, eqAtG slot o *
        slotWtF (eqKernelF (claim.point.drop (logSteps - 4))) claim.weights first count o z := by
  obtain ⟨-, -, h3⟩ := foldAllF_eq slot (slotWeightsF logSteps claim first count)
    (by rw [slotWeightsF_length _ _ _ _ hfc, hs]; rfl)
    (fun o ho => slotWeightsF_row_length _ _ _ _ hfc (by rwa [slotWeightsF_length _ _ _ _ hfc] at ho))
  rw [foldRowsF_eq, h3 z hz, hs, show (2 : ℕ) ^ 6 = 64 from rfl]
  refine Finset.sum_congr rfl fun o ho => ?_
  have ho' := Finset.mem_range.mp ho
  rw [slotWeightsF_getD _ _ _ _ hfc ho', eqAtG, eqKernelF_getD, ite_eq_left (by rw [hs]; exact ho')]

theorem fold_lengthG (logSteps : ℕ) (claim : KClaim F) (first count : ℕ) (hfc : first + count ≤ 2)
    {slot : List F} (hs : slot.length = 6) :
    (foldRowsF slot (slotWeightsF logSteps claim first count)).length = 64 :=
  (foldAllF_eq slot (slotWeightsF logSteps claim first count)
    (by rw [slotWeightsF_length _ _ _ _ hfc, hs]; rfl)
    (fun o ho => slotWeightsF_row_length _ _ _ _ hfc (by rwa [slotWeightsF_length _ _ _ _ hfc] at ho))).2.1

/-- **The committed outputs' opening** (`first = 1`, `count = 1`): column `0` of the fold. -/
theorem open_committedG (logSteps : ℕ) (claim : KClaim F) {slot : List F} (hs : slot.length = 6) :
    (foldRowsF slot (slotWeightsF logSteps claim 1 1)).getD 0 0 =
      sumF ((List.range 25).map fun l => eqAtG slot (25 + l) *
        (eqKernelF (claim.point.drop (logSteps - 4))).getD 0 0 * claim.weights.getD (64 * l) 0) := by
  rw [open_fold_getDG _ _ _ _ (by decide) hs (by decide), sumF_map_range,
    show (64 : ℕ) = 25 + (25 + 14) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  have h0 : ∑ o ∈ range 25, eqAtG slot o *
      slotWtF (eqKernelF (claim.point.drop (logSteps - 4))) claim.weights 1 1 o 0 = 0 :=
    Finset.sum_eq_zero fun o ho => by
      rw [slotWtF, if_neg (by have := Finset.mem_range.mp ho; omega), mul_zero]
  have h2 : ∑ k ∈ range 14, eqAtG slot (25 + (25 + k)) *
      slotWtF (eqKernelF (claim.point.drop (logSteps - 4))) claim.weights 1 1 (25 + (25 + k)) 0 = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [slotWtF, if_neg (by omega), mul_zero]
  rw [h0, h2, zero_add, add_zero]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  rw [slotWtF, if_pos (by omega), show (25 + l) / 25 - 1 = 0 by omega, show (25 + l) % 25 = l by omega,
    Nat.add_zero, mul_assoc]

theorem dotF_eq_sumG {l r : List F} (hl : l.length = 64) (hr : r.length = 64) :
    dotF l r = ∑ z ∈ range 64, l.getD z 0 * r.getD z 0 := by
  rw [dotF_eq _ _ (by rw [hl, hr]), hl]

/-- **The inputs' opening** (`first = 0`, `count = 2`): the fold against the 64 slices. -/
theorem open_inputG (logSteps : ℕ) (claim : KClaim F) {slot slices : List F} (hs : slot.length = 6)
    (hsl : slices.length = 64) :
    dotF (foldRowsF slot (slotWeightsF logSteps claim 0 2)) slices =
      sumF ((List.range 2).map fun s => sumF ((List.range 25).map fun l =>
        eqAtG slot (25 * s + l) * (eqKernelF (claim.point.drop (logSteps - 4))).getD s 0 *
          sumF ((List.range 64).map fun z => slices.getD z 0 * claim.weights.getD (64 * l + z) 0))) := by
  rw [dotF_eq_sumG (fold_lengthG _ _ _ _ (by decide) hs) hsl]
  rw [Finset.sum_congr rfl (fun z hz => by
    rw [open_fold_getDG _ _ _ _ (by decide) hs (Finset.mem_range.mp hz), Finset.sum_mul]),
    Finset.sum_comm, show (64 : ℕ) = 2 * 25 + 14 from rfl, Finset.sum_range_add]
  have h2 : ∑ k ∈ range 14, ∑ z ∈ range 64, eqAtG slot (2 * 25 + k) *
      slotWtF (eqKernelF (claim.point.drop (logSteps - 4))) claim.weights 0 2 (2 * 25 + k) z *
        slices.getD z 0 = 0 :=
    Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun z _ => by
      rw [slotWtF, if_neg (by omega), mul_zero, zero_mul]
  rw [h2, add_zero, sum_range_mulB, sumF_map_range]
  refine Finset.sum_congr rfl fun s hs' => ?_
  rw [sumF_map_range]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hs2 := Finset.mem_range.mp hs'
  have hl' := Finset.mem_range.mp hl
  rw [sumF_map_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz' := Finset.mem_range.mp hz
  rw [slotWtF, if_pos (by omega), show (25 * s + l) / 25 - 0 = s by omega,
    show (25 * s + l) % 25 = l by omega]
  ring

/-- The inputs' opening on transposed product weights: lane forms against the slices. -/
theorem open_input_ltG (logSteps : ℕ) (claim : KClaim F) (A : ℕ → F) (B : List F)
    (hw : claim.weights = linearTransposeF (prodWG A B)) {slot slices : List F}
    (hs : slot.length = 6) (hsl : slices.length = 64) :
    dotF (foldRowsF slot (slotWeightsF logSteps claim 0 2)) slices =
      sumF ((List.range 2).map fun s => sumF ((List.range 25).map fun l =>
        eqAtG slot (25 * s + l) * (eqKernelF (claim.point.drop (logSteps - 4))).getD s 0 *
          laneFormF B (rotSumG (fun z => slices.getD z 0) A) l)) := by
  rw [open_inputG logSteps claim hs hsl, hw]
  refine congrArg sumF (List.map_congr_left fun s _ => congrArg sumF (List.map_congr_left fun l hl => ?_))
  rw [lane_dotG A (fun z => slices.getD z 0) B (List.mem_range.mp hl)]

/-- The committed outputs' opening on the first claim's weights (`lanes ⊗ g^z`, slice `0`). -/
theorem open_committed_firstG (g : F) (logSteps : ℕ) (claim : KClaim F) (lanes : List F)
    (hw : claim.weights = firstWG g lanes) {slot : List F} (hs : slot.length = 6) :
    (foldRowsF slot (slotWeightsF logSteps claim 1 1)).getD 0 0 =
      sumF ((List.range 25).map fun l => eqAtG slot (25 + l) *
        (eqKernelF (claim.point.drop (logSteps - 4))).getD 0 0 * lanes.getD l 0) := by
  rw [open_committedG logSteps claim hs, hw]
  refine congrArg sumF (List.map_congr_left fun l hl => ?_)
  have h := firstWG_getD g lanes (List.mem_range.mp hl) (z := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h, pow_zero, mul_one]

end

end Lvm.Q1
