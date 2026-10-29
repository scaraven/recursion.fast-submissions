-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRWots.wots_sound`.
import FRNodeRows4WotsP
import FRNodeRead4

/-!
# The WOTS digits, the checksum, and a 4.1 `wots_sound`

* **`mD κ σ w`**: the digest whose 256 bits are signed child `σ`'s message digit bits (the digest
  the digit rows tie to the chain's `h_out`);
* **`msgDigits_mD`**: its 128 base-4 digits are the circuit's digits `digV`;
* **`gW_inj`**: `x` has order above 1023 (`gW ^ 255`, `^ 771`, `^ 641` are not `1`, checked by the
  kernel on 10 squarings; every divisor of `2^128 − 1` below 1024 divides 255, 771 or 641);
* **`wotsDigits_mD`**: with the checksum rows (`R_{i+1} = R_i f_i`), the 133 WOTS digits of `mD` are
  the circuit's digits;
* **`wots_sound4`**: the WOTS rows, the node's Z and S truths, its L rows and `PubCells4` give the
  contract's `SigOk vk (mD κ σ w) (readSig4 κ σ w)`.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit Kinds Stream

/-! ## The digest of the digit bits -/

/-- Half `h` of the digit bits, packed. -/
noncomputable def pkD (κ : NodeKind) (σ : ℕ) (w : Asg) (h : ℕ) : F := (pk (fun q => digC κ σ (128 * h + q)) 128).ev w

/-- **The digest of the message digit bits.** -/
noncomputable def mD (κ : NodeKind) (σ : ℕ) (w : Asg) : Digest :=
  Vector.ofFn fun i : Fin 32 => fb (pkD κ σ w (i / 16)) (i % 16)

theorem byte_digit : ∀ n < 256, ∀ t < 4,
    n / 4 ^ t % 4 = (if n.testBit (2 * t) then 1 else 0) + 2 * (if n.testBit (2 * t + 1) then 1 else 0) := by
  decide +kernel

theorem flatMap4_getD {α : Type} [Inhabited α] (f : α → List ℕ) (hf : ∀ a, (f a).length = 4) :
    ∀ (l : List α) (i : ℕ), i < 4 * l.length → (l.flatMap f).getD i 0 = (f (l.getD (i / 4) default)).getD (i % 4) 0
  | [], i, hi => by simp at hi
  | a :: l, i, hi => by
    rw [List.flatMap_cons]
    by_cases h : i < 4
    · rw [List.getD_append _ _ _ _ (by rw [hf]; exact h)]
      simp [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    · rw [List.getD_append_right _ _ _ _ (by rw [hf]; omega), hf,
        flatMap4_getD f hf l (i - 4) (by simp at hi; omega)]
      simp only [show i / 4 = (i - 4) / 4 + 1 by omega, show i % 4 = (i - 4) % 4 by omega, List.getD_cons_succ]

/-- **The message digits of `mD` are the circuit's.** -/
theorem msgDigits_mD {κ : NodeKind} {w : Asg} {σ : ℕ} (hb : ∀ p < 256, w (digC κ σ p) = 0 ∨ w (digC κ σ p) = 1)
    {i : ℕ} (hi : i < 128) : (msgDigits (mD κ σ w)).getD i 0 = digV κ σ w i := by
  rw [msgDigits, flatMap4_getD _ (fun a => by simp) _ _ (by simp; omega),
    List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [Vector.getElem_toList, mD, Vector.getElem_ofFn]
  have hk : (i / 4) % 16 < 16 := Nat.mod_lt _ (by norm_num)
  rw [byte_digit _ (UInt8.toNat_lt _) _ (Nat.mod_lt _ (by norm_num))]
  have bit : ∀ b < 2, (fb (pkD κ σ w (i / 4 / 16)) (i / 4 % 16)).toNat.testBit (2 * (i % 4) + b) =
      decide (w (digC κ σ (2 * i + b)) = 1) := fun b hb' => by
    rw [← UInt8.toNat_toBitVec, BitVec.testBit_toNat, fb_bit _ hk (by omega), bitN, pkD,
      bitF_pk w _ (by norm_num) (fun q hq => hb _ (by omega))]
    simp only [Nat.mod_eq_of_lt (show 8 * (i / 4 % 16) + (2 * (i % 4) + b) < 128 by omega)]
    rw [show 128 * (i / 4 / 16) + (8 * (i / 4 % 16) + (2 * (i % 4) + b)) = 2 * i + b by omega]
    simp [show 8 * (i / 4 % 16) + (2 * (i % 4) + b) < 128 by omega]
  have b0 := bit 0 (by norm_num)
  simp only [Nat.add_zero] at b0
  rw [b0, bit 1 (by norm_num)]
  simp [digV, bv]

/-! ## The generator's order -/

/-- Square-and-multiply on the bits (low first). -/
def bpowL (a : F) : List Bool → F
  | [] => 1
  | b :: bs => (if b then a else 1) * bpowL (a * a) bs

def bval : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bval bs

theorem bpowL_eq (a : F) (bs : List Bool) : bpowL a bs = a ^ bval bs := by
  induction bs generalizing a with
  | nil => simp [bpowL, bval]
  | cons b bs ih =>
    rw [bpowL, bval, ih, pow_add, pow_mul, sq]
    split_ifs <;> simp

theorem gW_255 : gW ^ 255 ≠ 1 := by
  rw [show 255 = bval [true, true, true, true, true, true, true, true] from rfl, ← bpowL_eq]; decide +kernel
theorem gW_771 : gW ^ 771 ≠ 1 := by
  rw [show 771 = bval [true, true, false, false, false, false, false, false, true, true] from rfl, ← bpowL_eq]
  decide +kernel
theorem gW_641 : gW ^ 641 ≠ 1 := by
  rw [show 641 = bval [true, false, false, false, false, false, false, true, false, true] from rfl, ← bpowL_eq]
  decide +kernel

theorem dvd_small : ∀ d < 1024, (2 ^ 128 - 1) % d = 0 → 255 % d = 0 ∨ 771 % d = 0 ∨ 641 % d = 0 := by
  decide +kernel

theorem gW_ne : gW ≠ 0 := by decide

/-- **`x` has order above 1023.** -/
theorem gW_order : 1023 < orderOf gW := by
  have h1 : gW ^ (2 ^ 128 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one gW gW_ne
    rwa [F.card_F] at this
  have hd := orderOf_dvd_of_pow_eq_one h1
  have hpos : 0 < orderOf gW := Nat.pos_of_dvd_of_pos hd (by norm_num)
  by_contra hle
  rcases dvd_small _ (by omega) (Nat.mod_eq_zero_of_dvd hd) with h | h | h
  · exact gW_255 (orderOf_dvd_iff_pow_eq_one.1 (Nat.dvd_of_mod_eq_zero h))
  · exact gW_771 (orderOf_dvd_iff_pow_eq_one.1 (Nat.dvd_of_mod_eq_zero h))
  · exact gW_641 (orderOf_dvd_iff_pow_eq_one.1 (Nat.dvd_of_mod_eq_zero h))

/-- **`n ↦ x^n` is injective below 1024.** -/
theorem gW_inj {a b : ℕ} (ha : a < 1024) (hb : b < 1024) (h : gW ^ a = gW ^ b) : a = b := by
  have ho := gW_order
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha h.symm (by omega)).symm
  have e : gW ^ (b - a) = 1 := by
    have : gW ^ a * gW ^ (b - a) = gW ^ a * 1 := by rw [← pow_add, Nat.add_sub_cancel' hab, ← h, mul_one]
    exact mul_left_cancel₀ (pow_ne_zero _ gW_ne) this
  have := Nat.eq_zero_of_dvd_of_lt (orderOf_dvd_of_pow_eq_one e) (by omega)
  omega

end W4
end FR
