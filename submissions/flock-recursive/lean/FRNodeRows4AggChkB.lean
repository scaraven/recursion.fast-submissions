-- New for `flock-recursive` (PACK-4.4.1 §4.3; stage B4, track L-circ): bits, bytes and numbers.
import FRNodeRows4AggChk
import FRNodeRows4WotsB

/-!
# Bits, bytes and numbers for the aggregate's checks

* **Numbers from bits** (`nOfBits`): a byte's value is its bits' (`byte_toNat`), eight bytes'
  little-endian value their 64 bits' (`bytes_bits`).
* **Packed Boolean values at an offset** (`bitF_sumO`, `bitF_pkO`): bit `j` of `Σ_q E_{q+d} v_q`
  is `v_{j−d}` on the range; so equal packs have equal bits (`pkO_bits_eq`), and a zero pack has
  zero bits (`pkO_zero`).
* **Bytes of three elements read as one string** (`catBit`, `catByte`): the views' fields
  `start = catByte x y _ [0, 32)`, `h = catByte x y z [1, 33)` (`dg2`, `sh1`); bytes agree when
  their bits do (`catByte_congr`).
* **The full adder over `GF(2^128)`** (`full_add`): Boolean `a, b, c`, `p = ab`, `c' − p = (a + b)c`
  give a Boolean sum `a + b + c` and carry `c'` with `a + b + c = (a + b + c) + 2c'` in ℕ.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Finset

/-! ## Numbers from bits -/

/-- The value of the bits `f 0, …, f (m − 1)`. -/
def nOfBits (f : ℕ → Bool) (m : ℕ) : ℕ := ∑ t ∈ range m, if f t then 2 ^ t else 0

theorem nat_mod_bits (n : ℕ) : ∀ m, n % 2 ^ m = nOfBits n.testBit m
  | 0 => by simp [nOfBits, Nat.mod_one]
  | m + 1 => by
    rw [Nat.mod_pow_succ, nat_mod_bits n m]
    simp only [nOfBits, sum_range_succ]
    congr 1
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ m) with h | h <;> simp [h]

/-- **A byte is the value of its bits.** -/
theorem byte_toNat (x : UInt8) : x.toNat = nOfBits (fun b => x.toBitVec.getLsbD b) 8 := by
  rw [← Nat.mod_eq_of_lt (show x.toNat < 2 ^ 8 from x.toNat_lt), nat_mod_bits]; rfl

theorem nOfBits_add (f : ℕ → Bool) (a b : ℕ) :
    nOfBits f (a + b) = nOfBits f a + 2 ^ a * nOfBits (fun t => f (a + t)) b := by
  unfold nOfBits
  rw [sum_range_add, mul_sum]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  split_ifs <;> simp [pow_add]

theorem nOfBits_lt (f : ℕ → Bool) : ∀ m, nOfBits f m < 2 ^ m
  | 0 => by simp [nOfBits]
  | m + 1 => by
    have := nOfBits_lt f m
    rw [nOfBits, sum_range_succ, ← nOfBits, pow_succ]
    split_ifs <;> omega

theorem nOfBits_congr {f g : ℕ → Bool} {m : ℕ} (h : ∀ t < m, f t = g t) : nOfBits f m = nOfBits g m :=
  sum_congr rfl fun t ht => by rw [h t (mem_range.1 ht)]

/-- Bits from `m'` on that are clear add nothing. -/
theorem nOfBits_high {f : ℕ → Bool} {m' m : ℕ} (hm : m' ≤ m) (h : ∀ t, m' ≤ t → t < m → f t = false) :
    nOfBits f m = nOfBits f m' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [nOfBits_add]
  have : nOfBits (fun t => f (m' + t)) d = 0 :=
    sum_eq_zero fun t ht => by
      have := h (m' + t) (by omega) (by have := mem_range.1 ht; omega)
      simp [this]
  rw [this, mul_zero, add_zero]

/-- **Little-endian bytes are their bits.** -/
theorem bytes_bits (f : ℕ → Bool) : ∀ m,
    ∑ i ∈ range m, nOfBits (fun b => f (8 * i + b)) 8 * 256 ^ i = nOfBits f (8 * m)
  | 0 => by simp [nOfBits]
  | m + 1 => by
    rw [sum_range_succ, bytes_bits f m, show 8 * (m + 1) = 8 * m + 8 by ring, nOfBits_add,
      show (256 : ℕ) ^ m = 2 ^ (8 * m) by rw [pow_mul]; norm_num]
    ring

/-- Eight bytes `1 … 8` of an element (its view length `n`, `enc64`'s layout). -/
def n8 (z : F) : ℕ := ∑ i ∈ range 8, (fb z (1 + i)).toNat * 256 ^ i

/-- **`n8` is the element's bits `8 … 71`.** -/
theorem n8_bits (z : F) : n8 z = nOfBits (fun t => bitN z (8 + t)) 64 := by
  rw [n8, show 64 = 8 * 8 from rfl, ← bytes_bits]
  refine sum_congr rfl fun i hi => ?_
  have hi : i < 8 := mem_range.1 hi
  rw [byte_toNat]
  congr 1
  refine nOfBits_congr fun b hb => ?_
  rw [fb_bit z (by omega) hb]
  congr 1; ring

/-! ## Packed Boolean values at an offset -/

theorem pkO_ev (w : Asg) (cell : ℕ → ℕ) (d n : ℕ) :
    (pkO cell d n).ev w = ∑ q ∈ range n, E (q + d) * w (cell q) := by
  induction n with
  | zero => simp [pkO]
  | succ n ih =>
    rw [pkO, List.range_succ, List.map_append, ← pkO, Lin.ev_append, ih, sum_range_succ]
    simp [Lin.ev]

/-- **Bit `j` of Boolean values packed at offset `d`.** -/
theorem bitF_sumO {v : ℕ → F} {d : ℕ} : ∀ {n : ℕ}, d + n ≤ 128 → (∀ q < n, v q = 0 ∨ v q = 1) →
    ∀ j : Fin 128, bitF (∑ q ∈ range n, E (q + d) * v q) j = decide (d ≤ j.val ∧ j.val < d + n ∧ v (j.val - d) = 1)
  | 0, _, _, j => by simp only [range_zero, sum_empty, bitF_zero]; symm; simp; omega
  | n + 1, hn, hb, j => by
    rw [sum_range_succ, bitF_add, bitF_sumO (by omega) (fun q hq => hb q (by omega)) j]
    rcases hb n (by omega) with h | h
    · rw [h, mul_zero, bitF_zero, Bool.xor_false]
      refine decide_eq_decide.2 ⟨fun ⟨a, b, c⟩ => ⟨a, by omega, c⟩, fun ⟨a, b, c⟩ => ⟨a, ?_, c⟩⟩
      rcases Nat.lt_or_ge j.val (d + n) with h' | h'
      · exact h'
      · rw [show j.val - d = n by omega, h] at c; exact absurd c zero_ne_one
    · rw [h, mul_one, bitF_E (n + d) (by omega)]
      by_cases hj : j.val = n + d
      · have e1 : ¬ (d ≤ j.val ∧ j.val < d + n ∧ v (j.val - d) = 1) := fun ⟨_, h2, _⟩ => by omega
        have e2 : d ≤ j.val ∧ j.val < d + (n + 1) ∧ v (j.val - d) = 1 :=
          ⟨by omega, by omega, by rw [hj, Nat.add_sub_cancel]; exact h⟩
        rw [decide_eq_false e1, decide_eq_true e2, decide_eq_true hj]; rfl
      · rw [decide_eq_false hj, Bool.xor_false]
        exact decide_eq_decide.2 ⟨fun ⟨a, b, c⟩ => ⟨a, by omega, c⟩, fun ⟨a, b, c⟩ => ⟨a, by omega, c⟩⟩

/-- Boolean cells. -/
def BoolC (w : Asg) (cell : ℕ → ℕ) (n : ℕ) : Prop := ∀ q < n, w (cell q) = 0 ∨ w (cell q) = 1

theorem bitF_pkO (w : Asg) {cell : ℕ → ℕ} {d n : ℕ} (hn : d + n ≤ 128) (hb : BoolC w cell n) (j : Fin 128) :
    bitF ((pkO cell d n).ev w) j = decide (d ≤ j.val ∧ j.val < d + n ∧ w (cell (j.val - d)) = 1) := by
  rw [pkO_ev]; exact bitF_sumO hn hb j

/-- **Equal packs have equal cells.** -/
theorem pkO_bits_eq (w : Asg) {c₁ c₂ : ℕ → ℕ} {d n : ℕ} (hn : d + n ≤ 128) (h₁ : BoolC w c₁ n)
    (h₂ : BoolC w c₂ n) (h : (pkO c₁ d n).ev w = (pkO c₂ d n).ev w) {q : ℕ} (hq : q < n) :
    (w (c₁ q) = 1 ↔ w (c₂ q) = 1) := by
  have := congrArg (fun x => bitF x ⟨q + d, by omega⟩) h
  simp only [bitF_pkO w hn h₁, bitF_pkO w hn h₂, Nat.add_sub_cancel] at this
  simpa [show d ≤ q + d by omega, show q + d < d + n by omega] using this

/-- **A zero pack has zero cells.** -/
theorem pkO_zero (w : Asg) {c : ℕ → ℕ} {d n : ℕ} (hn : d + n ≤ 128) (hb : BoolC w c n)
    (h : (pkO c d n).ev w = 0) {q : ℕ} (hq : q < n) : w (c q) = 0 := by
  have := congrArg (fun x => bitF x ⟨q + d, by omega⟩) h
  simp only [bitF_pkO w hn hb, bitF_zero, Nat.add_sub_cancel] at this
  rcases hb q hq with h' | h'
  · exact h'
  · simp [h', show d ≤ q + d by omega, show q + d < d + n by omega] at this

/-- **A packed element's bits** (a decomposition `x = Σ_q E_q c_q`). -/
theorem bitN_dec (w : Asg) {x : F} {c : ℕ → ℕ} (hb : BoolC w c 128) (h : x = (pkO c 0 128).ev w) {q : ℕ}
    (hq : q < 128) : bitN x q = decide (w (c q) = 1) := by
  rw [bitN, h, bitF_pkO w (by norm_num) hb]
  simp [Nat.mod_eq_of_lt hq, hq]

/-! ## Bytes of three elements as one string -/

/-- Element `e` of three. -/
def pick3 (x y z : F) (e : ℕ) : F := if e = 0 then x else if e = 1 then y else z

/-- Bit `P` of the string `x ‖ y ‖ z`. -/
def catBit (x y z : F) (P : ℕ) : Bool := bitN (pick3 x y z (P / 128)) P

/-- Byte `P` of the string `x ‖ y ‖ z`. -/
def catByte (x y z : F) (P : ℕ) : UInt8 := fb (pick3 x y z (P / 16)) P

/-- Bytes `0 … 31` of `x ‖ y` (a view's start, `hdr.pub`). -/
def dg2 (x y : F) : Digest := Vector.ofFn fun j : Fin 32 => catByte x y 0 j

/-- Bytes `1 … 32` of `x ‖ y ‖ z` (a view's end, `stmt[1 … 33)`; the `hashA` message's `e`). -/
def sh1 (x y z : F) : Digest := Vector.ofFn fun j : Fin 32 => catByte x y z (1 + j)

theorem fb_mod (a : F) (k : ℕ) : fb a (k % 16) = fb a k := by
  unfold fb; simp only [Nat.mod_mod]

theorem catByte_bit (x y z : F) {P b : ℕ} (hb : b < 8) :
    (catByte x y z P).toBitVec.getLsbD b = catBit x y z (8 * P + b) := by
  rw [catByte, ← fb_mod, fb_bit _ (Nat.mod_lt _ (by norm_num)) hb, catBit,
    show (8 * P + b) / 128 = P / 16 by omega]
  unfold bitN
  congr 2; omega

/-- **Bytes agree when their bits do.** -/
theorem catByte_congr {x y z x' y' z' : F} {P P' : ℕ}
    (h : ∀ b < 8, catBit x y z (8 * P + b) = catBit x' y' z' (8 * P' + b)) :
    catByte x y z P = catByte x' y' z' P' :=
  byte_ext fun b hb => by rw [catByte_bit _ _ _ hb, catByte_bit _ _ _ hb, h b hb]

theorem catBit_lt (x y z : F) {P : ℕ} (h : P < 128) : catBit x y z P = bitN x P := by
  simp [catBit, pick3, Nat.div_eq_of_lt h]

theorem bitN_congr (a : F) {n m : ℕ} (h : n % 128 = m % 128) : bitN a n = bitN a m := by
  unfold bitN; congr 1; exact Fin.ext h

theorem bitN_mod (x : F) (Q : ℕ) : bitN x Q = bitN x (Q % 128) := bitN_congr x (Nat.mod_mod _ _).symm

theorem catBit_mid (x y z : F) {P : ℕ} (h1 : 128 ≤ P) (h2 : P < 256) : catBit x y z P = bitN y (P - 128) := by
  rw [catBit, show P / 128 = 1 by omega]
  exact bitN_congr _ (by omega)

theorem catBit_hi (x y z : F) {P : ℕ} (h1 : 256 ≤ P) (h2 : P < 384) : catBit x y z P = bitN z (P - 256) := by
  rw [catBit, show P / 128 = 2 by omega]
  exact bitN_congr _ (by omega)

/-! ## The full adder over `GF(2^128)` -/

/-- A `0`/`1` value as a natural. -/
def nv (x : F) : ℕ := if x = 1 then 1 else 0

theorem nv_zero : nv 0 = 0 := by unfold nv; rw [if_neg zero_ne_one]
theorem nv_one : nv 1 = 1 := by unfold nv; rw [if_pos rfl]

theorem F_two : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1

/-- **One full-adder step**: Boolean `a, b, c`; `p = ab`; `c' − p = (a + b)c`. -/
theorem full_add {a b c p c' : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hp : a * b = p) (hc' : (a + b) * c = c' - p) :
    (a + b + c = 0 ∨ a + b + c = 1) ∧ (c' = 0 ∨ c' = 1) ∧ nv a + nv b + nv c = nv (a + b + c) + 2 * nv c' := by
  have h2 := F_two
  have h10 : (1 : F) ≠ 0 := one_ne_zero
  have hc'' : c' = (a + b) * c + p := by rw [hc']; ring
  subst hp hc''
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp only [h2, add_zero, zero_add, mul_zero, mul_one, one_mul, nv_zero, nv_one, true_or,
      or_true, true_and] <;> norm_num

/-! ## Small facts -/

theorem capE_le (ι : Kind) : capE ι ≤ 18 := by cases ι <;> decide

theorem kinds_mem (ι : Kind) : ι ∈ Circ.kinds := by cases ι <;> simp [Circ.kinds]

theorem nOfBits_zero {f : ℕ → Bool} {m : ℕ} (h : ∀ t < m, f t = false) : nOfBits f m = 0 :=
  sum_eq_zero fun t ht => by simp [h t (mem_range.1 ht)]

theorem nOfBits_ge {f : ℕ → Bool} {m t : ℕ} (ht : t < m) (hf : f t = true) : 2 ^ t ≤ nOfBits f m := by
  unfold nOfBits
  have := single_le_sum (f := fun t => if f t = true then 2 ^ t else 0) (fun _ _ => Nat.zero_le _)
    (mem_range.2 ht)
  simpa [hf] using this

theorem nOfBits_one (f : ℕ → Bool) : nOfBits f 1 = if f 0 then 1 else 0 := by simp [nOfBits]

theorem ev_flatMap_range (w : Asg) (g : ℕ → Lin) : ∀ n, Lin.ev w ((List.range n).flatMap g) = ∑ t ∈ range n, (g t).ev w
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.flatMap_append, Lin.ev_append, ev_flatMap_range w g n, sum_range_succ]; simp

theorem mL_ev (w : Asg) (κ : NodeKind) (σ i t : ℕ) : (mL κ σ i t).ev w = if t < 19 then w (mC κ σ i t) else 0 := by
  unfold mL; split_ifs <;> simp

theorem cL_ev (w : Asg) (κ : NodeKind) (σ i t : ℕ) : (cL κ σ i t).ev w = if t = 0 then 0 else w (cC κ σ i t) := by
  unfold cL; split_ifs <;> simp

theorem accL_succ_ev (w : Asg) (κ : NodeKind) (σ i t : ℕ) : (accL κ σ (i + 1) t).ev w =
    (accL κ σ i t).ev w + (mL κ σ (i + 1) t).ev w + (cL κ σ (i + 1) t).ev w := by
  simp [accL, Lin.ev_append, add_assoc]

/-- `0`/`1` values read as bits. -/
def dv (x : F) : Bool := decide (x = 1)

theorem ite_nv (x : F) (t : ℕ) : (if dv x = true then 2 ^ t else 0) = nv x * 2 ^ t := by
  unfold dv nv; split_ifs <;> simp_all

theorem nOfBits_dv (X : ℕ → F) (T : ℕ) : nOfBits (fun t => dv (X t)) T = ∑ t ∈ range T, nv (X t) * 2 ^ t :=
  sum_congr rfl fun t _ => ite_nv _ _

end W4
end FR
