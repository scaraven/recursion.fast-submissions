-- New for `flock-recursive` (IMPC2 §0, the design's `FRBits128`; track IMPC2): the bits of an `F`
-- element and Boolean decompositions `Σ e_j·b_j`, below the bit generator.
import FRVIRTplCore

/-!
# Bits of `F` and Boolean decompositions

`F` is `GF(2^64)[y]` on two little-endian words and its addition is `xor`, so `Σ_j e_j·b_j` with
Boolean `b_j` and distinct `j < 128` is the element whose bit `j` is `b_j`, and the bits are unique.

* **`eBit j`**: the element with bit `j` alone (`c₀`'s bit `j`, or `c₁`'s bit `j − 64`); **`F.bit`**.
* **`bit_eBit`**, **`bit_bitsLin`**: the bits of `Σ e_j·w(c_j)`; **`decomp_cell`**: a decomposition
  row's Boolean cells are the element's bits.
-/

namespace FR
open Circ


namespace F
/-- Bit `j` of an `F` element (`j < 64`: `c₀`'s, else `c₁`'s bit `j − 64`). -/
def bit (x : F) (j : ℕ) : Bool := if j < 64 then x.c₀.val.toNat.testBit j else x.c₁.val.toNat.testBit (j - 64)

theorem bit_add (a b : F) (j : ℕ) : (a + b).bit j = (a.bit j ^^ b.bit j) := by
  change (F.add a b).bit j = _
  simp only [bit, F.add]
  split <;> simp [HAdd.hAdd, Add.add, B64.add, UInt64.toNat_xor, Nat.testBit_xor]

theorem bit_zero (j : ℕ) : (0 : F).bit j = false := by
  simp only [bit]; split <;> exact Nat.zero_testBit _
end F

/-- **The `F` element with bit `j` alone** (`j < 64`: `c₀`'s bit `j`; else `c₁`'s bit `j − 64`), the
order of `F.toBytes`' little-endian bytes. -/
def eBit (j : ℕ) : F :=
  if j < 64 then ⟨⟨(1 : UInt64) <<< j.toUInt64⟩, ⟨0⟩⟩ else ⟨⟨0⟩, ⟨(1 : UInt64) <<< (j - 64).toUInt64⟩⟩

theorem eBit_shl_toNat {j : ℕ} (hj : j < 64) : ((1 : UInt64) <<< j.toUInt64).toNat = 2 ^ j := by
  rw [UInt64.toNat_shiftLeft]
  have h1 : (j.toUInt64).toNat % 64 = j := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt hj]
  rw [h1, UInt64.toNat_one, Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj)]

theorem bit_eBit {i j : ℕ} (hi : i < 128) (hj : j < 128) : (eBit i).bit j = decide (i = j) := by
  unfold eBit F.bit
  by_cases h1 : i < 64 <;> by_cases h2 : j < 64 <;> simp only [h1, h2, ite_true, ite_false]
  · rw [eBit_shl_toNat h1, Nat.testBit_two_pow]
  · rw [show ((0 : UInt64)).toNat = 0 from rfl, Nat.zero_testBit]; simp; omega
  · rw [show ((0 : UInt64)).toNat = 0 from rfl, Nat.zero_testBit]; simp; omega
  · rw [eBit_shl_toNat (by omega), Nat.testBit_two_pow]; simp; omega

theorem bit_eBit_mul (w : Asg) (i c j : ℕ) (hi : i < 128) (hj : j < 128) (hb : w c = 0 ∨ w c = 1) :
    (eBit i * w c).bit j = (decide (i = j) && decide (w c = 1)) := by
  rcases hb with h | h <;> rw [h]
  · rw [mul_zero, F.bit_zero]; simp [show (0 : F) ≠ 1 by decide]
  · rw [mul_one, bit_eBit hi hj]; simp

/-- **The bits of `Σ e_i·w(c_i)`** over Boolean cells, distinct bit indices below 128. -/
theorem bit_bitsLin (w : Asg) : ∀ (L : List (ℕ × ℕ)), (∀ p ∈ L, w p.2 = 0 ∨ w p.2 = 1) →
    (∀ p ∈ L, p.1 < 128) → (L.map Prod.fst).Nodup → ∀ j < 128,
    (Lin.ev w (L.map fun p => (p.2, eBit p.1))).bit j = decide (∃ p ∈ L, p.1 = j ∧ w p.2 = 1)
  | [], _, _, _, j, _ => by simp [Lin.ev, F.bit_zero]
  | p :: L, hb, hL, hd, j, hj => by
    rw [List.map_cons, Lin.ev_cons, F.bit_add, bit_eBit_mul w p.1 p.2 j (hL p (by simp)) hj (hb p (by simp)),
      bit_bitsLin w L (fun q hq => hb q (by simp [hq])) (fun q hq => hL q (by simp [hq]))
        (List.nodup_cons.1 (by simpa only [List.map_cons] using hd)).2 j hj]
    have hn : p.1 ∉ L.map Prod.fst := (List.nodup_cons.1 (by simpa only [List.map_cons] using hd)).1
    by_cases hpj : p.1 = j
    · have : ¬ ∃ q ∈ L, q.1 = j ∧ w q.2 = 1 := fun ⟨q, hq, hqj, _⟩ =>
        hn (List.mem_map.2 ⟨q, hq, hqj.trans hpj.symm⟩)
      by_cases hw : w p.2 = 1 <;> simp [hpj, hw, this]
    · simp [hpj]

/-- **A Boolean decomposition determines its cells**: if `x = Σ e_i·w(c_i)` then each cell is `x`'s bit. -/
theorem decomp_cell (w : Asg) (L : List (ℕ × ℕ)) (hb : ∀ p ∈ L, w p.2 = 0 ∨ w p.2 = 1)
    (hL : ∀ p ∈ L, p.1 < 128) (hd : (L.map Prod.fst).Nodup) {x : F}
    (hx : x = Lin.ev w (L.map fun p => (p.2, eBit p.1))) {p : ℕ × ℕ} (hp : p ∈ L) :
    w p.2 = if x.bit p.1 then 1 else 0 := by
  rw [hx, bit_bitsLin w L hb hL hd p.1 (hL p hp)]
  have : (∃ q ∈ L, q.1 = p.1 ∧ w q.2 = 1) ↔ w p.2 = 1 := by
    refine ⟨fun ⟨q, hq, hqp, hw⟩ => ?_, fun h => ⟨p, hp, rfl, h⟩⟩
    rwa [List.inj_on_of_nodup_map hd hq hp hqp] at hw
  rcases hb p hp with h | h <;> simp [this, h, show (0 : F) ≠ 1 by decide]

/-- (+) `eBit 3` has bit 3, `eBit 100` bit 100; (−) neither has a neighbouring bit. -/
theorem eBit_ctl : (eBit 3).bit 3 = true ∧ (eBit 3).bit 4 = false ∧ (eBit 100).bit 100 = true ∧
    (eBit 100).bit 99 = false := by
  simp only [bit_eBit (by norm_num : 3 < 128), bit_eBit (by norm_num : 100 < 128), (by norm_num : (4 : ℕ) < 128),
    (by norm_num : (99 : ℕ) < 128)]
  decide

end FR
