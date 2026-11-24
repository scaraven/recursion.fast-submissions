-- New for lvm6 K1: the input lanes of the tree rows bit by bit (`nodeLanes`, `itemLanes`): input bit `j`
-- is the constant's bit `j` plus slot bit `j − 8` (the tag byte's shift), so a weighted sum of the
-- input bits is `C^t` plus the slot bits weighted by `w_{64o+z+8}` (BLUEPRINT §2.3 step 6, `pw^P`, `pw^L`).
import Lvm6KStmt

/-!
# The tree rows' input bits

* `lanesU nw W c`: the uniform form of `nodeLanes` (`nw = 8`) and `itemLanes` (`nw = 4`): lane `ℓ` is
  `W (ℓ−1) >>> 56 ^^^ W ℓ <<< 8` on the words present, xor the constants `c ℓ`;
* `sbit_lanesU`: input bit `j < 1600` is `c`'s bit `j` xor slot bit `j − 8` (`8 ≤ j < 8 + 64·nw`);
* **`wsum_node`**, **`wsum_item`**: `Σ_j w_j·bit_j(In) = C^t + Σ_{o<nw} Σ_z w_{64o+z+8}·bit_z(W o)`.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics
open LeanVM.Protocol.KeccakGkr (sbit)
open Lvm.E2V
open Finset

/-! ## Words, bit by bit -/

theorem wb_shl8 (a : UInt64) {z : ℕ} (hz : z < 64) :
    (a <<< 8).toBitVec.getLsbD z = (decide (8 ≤ z) && a.toBitVec.getLsbD (z - 8)) := by
  simp only [UInt64.toBitVec_shiftLeft]
  by_cases h : z < 8
  · simp [h, hz, show ¬ 8 ≤ z by omega]
  · simp [h, hz, show 8 ≤ z by omega]
    exact (BitVec.getLsbD_eq_getElem (by omega)).symm

theorem wb_shr56 (a : UInt64) {z : ℕ} (hz : z < 64) :
    (a >>> 56).toBitVec.getLsbD z = (decide (z < 8) && a.toBitVec.getLsbD (z + 56)) := by
  simp only [UInt64.toBitVec_shiftRight]
  by_cases h : z < 8
  · simp [h, Nat.add_comm]
  · simp [h]
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem wb_xor (a b : UInt64) (z : ℕ) :
    (a ^^^ b).toBitVec.getLsbD z = (a.toBitVec.getLsbD z ^^ b.toBitVec.getLsbD z) := by
  rw [UInt64.toBitVec_xor, BitVec.getLsbD_xor]

theorem wb_zero (z : ℕ) : (0 : UInt64).toBitVec.getLsbD z = false := by simp

/-! ## The uniform lanes -/

/-- Lane `ℓ` of a tagged, shifted block of `nw` words with constants `c`. -/
def laneU (nw : ℕ) (W : ℕ → UInt64) (c : ℕ → UInt64) (ℓ : ℕ) : UInt64 :=
  (if 1 ≤ ℓ ∧ ℓ ≤ nw then W (ℓ - 1) >>> 56 else 0) ^^^ (if ℓ < nw then W ℓ <<< 8 else 0) ^^^ c ℓ

/-- The parent constants by lane. -/
def cPl (ℓ : ℕ) : UInt64 :=
  if ℓ = 0 then 0x44 else if ℓ = 8 then 0x100 else if ℓ = 16 then 0x8000000000000000 else 0

/-- The leaf constants by lane. -/
def cLl (ℓ : ℕ) : UInt64 :=
  if ℓ = 0 then 0x48 else if ℓ = 4 then 0x100 else if ℓ = 16 then 0x8000000000000000 else 0

theorem lane_nodeLanes (W : ℕ → UInt64) {ℓ : ℕ} (hℓ : ℓ < 25) :
    Keccak.lane (Lvm6.nodeLanes W (fun m ↦ W (4 + m))) ℓ = laneU 8 W cPl ℓ := by
  interval_cases ℓ <;> simp [Lvm6.nodeLanes, Keccak.lane, laneU, cPl] <;> rw [UInt64.xor_comm]

theorem lane_itemLanes (W : ℕ → UInt64) {ℓ : ℕ} (hℓ : ℓ < 25) :
    Keccak.lane (Lvm6.itemLanes W) ℓ = laneU 4 W cLl ℓ := by
  interval_cases ℓ <;> simp [Lvm6.itemLanes, Keccak.lane, laneU, cLl] <;> rw [UInt64.xor_comm]

/-- Slot bit `i` of the words `W`: bit `i mod 64` of word `i / 64`. -/
def wbit (W : ℕ → UInt64) (i : ℕ) : Bool := (W (i / 64)).toBitVec.getLsbD (i % 64)

/-- **An input bit**: the constant's bit, xor slot bit `j − 8` inside the block. -/
theorem sbit_laneU {nw : ℕ} (W : ℕ → UInt64) (c : ℕ → UInt64) {a : KeccakState}
    (ha : ∀ ℓ < 25, Keccak.lane a ℓ = laneU nw W c ℓ) {j : ℕ} (hj : j < 1600) :
    sbit a j = ((c (j / 64)).toBitVec.getLsbD (j % 64) ^^
      (decide (8 ≤ j ∧ j < 8 + 64 * nw) && wbit W (j - 8))) := by
  have hz : j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [sbit, ha _ (by omega), laneU, wb_xor, wb_xor]
  have hA : (if 1 ≤ j / 64 ∧ j / 64 ≤ nw then W (j / 64 - 1) >>> 56 else 0).toBitVec.getLsbD (j % 64) =
      (decide (j % 64 < 8 ∧ 1 ≤ j / 64 ∧ j / 64 ≤ nw) && wbit W (j - 8)) := by
    split_ifs with h
    · rw [wb_shr56 _ hz]
      by_cases h8 : j % 64 < 8
      · have e1 : (j - 8) / 64 = j / 64 - 1 := by omega
        have e2 : (j - 8) % 64 = j % 64 + 56 := by omega
        simp [h8, h, wbit, e1, e2]
      · simp [h8]
    · simp only [wb_zero]
      by_cases h' : j % 64 < 8 ∧ 1 ≤ j / 64 ∧ j / 64 ≤ nw
      · exact absurd ⟨h'.2.1, h'.2.2⟩ h
      · simp [h']
  have hB : (if j / 64 < nw then W (j / 64) <<< 8 else 0).toBitVec.getLsbD (j % 64) =
      (decide (8 ≤ j % 64 ∧ j / 64 < nw) && wbit W (j - 8)) := by
    split_ifs with h
    · rw [wb_shl8 _ hz]
      by_cases h8 : 8 ≤ j % 64
      · have e1 : (j - 8) / 64 = j / 64 := by omega
        have e2 : (j - 8) % 64 = j % 64 - 8 := by omega
        simp [h8, h, wbit, e1, e2]
      · simp [h8]
    · simp only [wb_zero]
      by_cases h' : 8 ≤ j % 64 ∧ j / 64 < nw
      · exact absurd h'.2 h
      · simp [h']
  rw [hA, hB]
  have hr : (8 ≤ j ∧ j < 8 + 64 * nw) ↔
      ((j % 64 < 8 ∧ 1 ≤ j / 64 ∧ j / 64 ≤ nw) ∨ (8 ≤ j % 64 ∧ j / 64 < nw)) := by omega
  by_cases h1 : j % 64 < 8 ∧ 1 ≤ j / 64 ∧ j / 64 ≤ nw
  · have h2 : ¬ (8 ≤ j % 64 ∧ j / 64 < nw) := by omega
    simp [h1, h2, hr.2 (Or.inl h1), Bool.xor_comm, Bool.xor_assoc]
  · by_cases h2 : 8 ≤ j % 64 ∧ j / 64 < nw
    · simp [h1, h2, hr.2 (Or.inr h2), Bool.xor_comm]
    · have h3 : ¬ (8 ≤ j ∧ j < 8 + 64 * nw) := fun h ↦ (hr.1 h).elim h1 h2
      simp [h1, h2, h3]

/-! ## The constants' bits -/

theorem bit_0x44 {z : ℕ} (hz : z < 64) :
    ((0x44 : UInt64)).toBitVec.getLsbD z = decide (z = 2 ∨ z = 6) := by
  interval_cases z <;> rfl

theorem bit_0x48 {z : ℕ} (hz : z < 64) :
    ((0x48 : UInt64)).toBitVec.getLsbD z = decide (z = 3 ∨ z = 6) := by
  interval_cases z <;> rfl

theorem bit_0x100 {z : ℕ} (hz : z < 64) : ((0x100 : UInt64)).toBitVec.getLsbD z = decide (z = 8) := by
  interval_cases z <;> rfl

theorem bit_0x80 {z : ℕ} (hz : z < 64) :
    ((0x8000000000000000 : UInt64)).toBitVec.getLsbD z = decide (z = 63) := by
  interval_cases z <;> rfl

theorem cPl_bit {j : ℕ} (hj : j < 1600) :
    (cPl (j / 64)).toBitVec.getLsbD (j % 64) = decide (j ∈ cPbits) := by
  have hz : j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  simp only [cPl, cPbits, List.mem_cons, List.not_mem_nil, or_false]
  split_ifs with h0 h8 h16
  · rw [bit_0x44 hz]; congr 1; apply propext; omega
  · rw [bit_0x100 hz]; congr 1; apply propext; omega
  · rw [bit_0x80 hz]; congr 1; apply propext; omega
  · rw [wb_zero]; symm; simp only [decide_eq_false_iff_not]; omega

theorem cLl_bit {j : ℕ} (hj : j < 1600) :
    (cLl (j / 64)).toBitVec.getLsbD (j % 64) = decide (j ∈ cLbits) := by
  have hz : j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  simp only [cLl, cLbits, List.mem_cons, List.not_mem_nil, or_false]
  split_ifs with h0 h8 h16
  · rw [bit_0x48 hz]; congr 1; apply propext; omega
  · rw [bit_0x100 hz]; congr 1; apply propext; omega
  · rw [bit_0x80 hz]; congr 1; apply propext; omega
  · rw [wb_zero]; symm; simp only [decide_eq_false_iff_not]; omega

/-! ## Weighted sums of the input bits -/

variable {F : Type} [Field F] [CharP F 2]

/-- `C^t = Σ_j w_j` over the set bits (`cW` over any field). -/
def cW' (w : List F) (bits : List ℕ) : F := (bits.map fun j ↦ w.getD j 0).sum

theorem cW_eq (w : List E2) (bits : List ℕ) : cW w bits = cW' w bits := rfl

/-- The constants' share: `Σ_j w_j·[j ∈ bits]` over four distinct bits below 1600. -/
theorem wsum_const (w : List F) {a b c d : ℕ} (hd : [a, b, c, d].Nodup) (ha : a < 1600)
    (hb : b < 1600) (hc : c < 1600) (hd' : d < 1600) :
    ∑ j ∈ range 1600, w.getD j 0 * bitF (decide (j ∈ [a, b, c, d])) =
      ([a, b, c, d].map fun j ↦ w.getD j 0).sum := by
  classical
  have e : ∀ j, w.getD j 0 * bitF (decide (j ∈ [a, b, c, d])) =
      if j ∈ [a, b, c, d].toFinset then w.getD j 0 else 0 := by
    intro j
    by_cases h : j ∈ [a, b, c, d]
    · rw [if_pos (List.mem_toFinset.2 h), decide_eq_true h, bitF_true, mul_one]
    · rw [if_neg (fun h' ↦ h (List.mem_toFinset.1 h')), decide_eq_false h, bitF_false, mul_zero]
  rw [Finset.sum_congr rfl fun j _ ↦ e j, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 (fun x hx ↦ by
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [Finset.mem_range]; omega),
    List.sum_toFinset _ hd]

omit [CharP F 2] in
/-- The slot bits' share: `Σ_j w_j·[8 ≤ j < 8 + 64·nw]·bit(j − 8) = Σ_{o<nw} Σ_z w_{64o+z+8}·bit_z(W o)`. -/
theorem wsum_slots (w : List F) {nw : ℕ} (hnw : 8 + 64 * nw ≤ 1600) (W : ℕ → UInt64) :
    ∑ j ∈ range 1600, w.getD j 0 * bitF (decide (8 ≤ j ∧ j < 8 + 64 * nw) && wbit W (j - 8)) =
      ∑ o ∈ range nw, ∑ z ∈ range 64, w.getD (64 * o + z + 8) 0 * bitF ((W o).toBitVec.getLsbD z) := by
  obtain ⟨m, hm⟩ : ∃ m, 1600 = 8 + (64 * nw + m) := ⟨1600 - 8 - 64 * nw, by omega⟩
  rw [hm, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ j ∈ range 8, w.getD j 0 * bitF (decide (8 ≤ j ∧ j < 8 + 64 * nw) && wbit W (j - 8)) = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      have := Finset.mem_range.1 hj
      simp [show ¬ 8 ≤ j by omega]
  have h3 : ∑ j ∈ range m, w.getD (8 + (64 * nw + j)) 0 * bitF (decide (8 ≤ 8 + (64 * nw + j) ∧
      8 + (64 * nw + j) < 8 + 64 * nw) && wbit W (8 + (64 * nw + j) - 8)) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by simp
  rw [h1, h3, zero_add, add_zero, mul_comm 64 nw, sum_range_mulK]
  refine Finset.sum_congr rfl fun o _ ↦ Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  have e1 : (64 * o + z) / 64 = o := by omega
  have e2 : (64 * o + z) % 64 = z := by omega
  have hlt : 64 * o + z < 64 * nw := by
    have := Finset.mem_range.1 ‹o ∈ range nw›; nlinarith
  rw [show 8 + (64 * o + z) = 64 * o + z + 8 by omega]
  simp [wbit, e1, e2, show 64 * o + z + 8 < 8 + nw * 64 by omega]

/-- **The parent rows' input**: `Σ_j w_j·bit_j(nodeLanes) = C^P + Σ_{o<8} Σ_z w_{64o+z+8}·bit_z(W o)`. -/
theorem wsum_node (w : List F) (W : ℕ → UInt64) :
    ∑ j ∈ range 1600, w.getD j 0 * bitF (sbit (Lvm6.nodeLanes W (fun m ↦ W (4 + m))) j) =
      cW' w cPbits + ∑ o ∈ range 8, ∑ z ∈ range 64,
        w.getD (64 * o + z + 8) 0 * bitF ((W o).toBitVec.getLsbD z) := by
  have e : ∀ j ∈ range 1600, w.getD j 0 * bitF (sbit (Lvm6.nodeLanes W (fun m ↦ W (4 + m))) j) =
      w.getD j 0 * bitF (decide (j ∈ cPbits)) +
        w.getD j 0 * bitF (decide (8 ≤ j ∧ j < 8 + 64 * 8) && wbit W (j - 8)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [sbit_laneU W cPl (fun ℓ hℓ ↦ lane_nodeLanes W hℓ) hj', cPl_bit hj', bitF_xor, mul_add]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, wsum_slots w (by norm_num) W, cPbits,
    wsum_const w (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rfl

/-- **The leaf rows' input**: `Σ_j w_j·bit_j(itemLanes) = C^L + Σ_{o<4} Σ_z w_{64o+z+8}·bit_z(W o)`. -/
theorem wsum_item (w : List F) (W : ℕ → UInt64) :
    ∑ j ∈ range 1600, w.getD j 0 * bitF (sbit (Lvm6.itemLanes W) j) =
      cW' w cLbits + ∑ o ∈ range 4, ∑ z ∈ range 64,
        w.getD (64 * o + z + 8) 0 * bitF ((W o).toBitVec.getLsbD z) := by
  have e : ∀ j ∈ range 1600, w.getD j 0 * bitF (sbit (Lvm6.itemLanes W) j) =
      w.getD j 0 * bitF (decide (j ∈ cLbits)) +
        w.getD j 0 * bitF (decide (8 ≤ j ∧ j < 8 + 64 * 4) && wbit W (j - 8)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [sbit_laneU W cLl (fun ℓ hℓ ↦ lane_itemLanes W hℓ) hj', cLl_bit hj', bitF_xor, mul_add]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, wsum_slots w (by norm_num) W, cLbits,
    wsum_const w (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rfl

end Lvm6.K
