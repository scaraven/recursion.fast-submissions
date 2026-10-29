-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2, A.6, A.7; stage S-E13b, track L-circ).
import FRNodeRows4Wots
import FRNodeReadCore

/-!
# Bytes of `f`: blocks, elements, digests, and the rows' readings

The WOTS argument moves between three views of the committed witness: H's block bits (what the
BLAKE2s blocks and the link families constrain), F elements (what the rows constrain), and bytes
(what the contract's hashes read). This module ties them:

* **`fb a k`**: byte `k` of the element `a` (`F.toBytes`, `c₀` first, little-endian); its bit `j`
  is `bitF a (8k + j)` (`fb_bit`);
* **a block's bytes are its elements' bytes**: `readByte_hc`, `readDigest_hc` (`h_out` is
  elements 2–3), `msgByte_hc` (the message is elements 4–7);
* **`digestOf`'s bytes** (`digestOf_get`), via `digestOf_halves`;
* **the rows' readings**: `eqR_val`, `boolR_val`, `muxR_val`, `gateR_val`, and the packed bits
  `pk` (`bitF_pk`: bit `j` of `Σ_q E_q c_q` is `c_j` for Boolean `c`).
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit

/-! ## Bytes of an element -/

/-- **Byte `k` (`k < 16`) of `a`.** -/
def fb (a : F) (k : ℕ) : UInt8 := (F.toBytes a)[k % 16]'(Nat.mod_lt _ (by norm_num))

/-- Bit `n mod 128` of `a`. -/
def bitN (a : F) (n : ℕ) : Bool := bitF a ⟨n % 128, Nat.mod_lt _ (by norm_num)⟩

theorem b64_byte_bit (c : B64) {k j : ℕ} (hk : k < 8) (hj : j < 8) :
    ((B64.toBytes c)[k]'hk).toBitVec.getLsbD j = c.val.toBitVec.getLsbD (8 * k + j) := by
  interval_cases k <;> simp [B64.toBytes, hj]

/-- **Bit `j` of byte `k` is bit `8k + j`.** -/
theorem fb_bit (a : F) {k j : ℕ} (hk : k < 16) (hj : j < 8) :
    (fb a k).toBitVec.getLsbD j = bitN a (8 * k + j) := by
  unfold fb bitN bitF
  simp only [Nat.mod_eq_of_lt hk, F.toBytes, Nat.mod_eq_of_lt (show 8 * k + j < 128 by omega)]
  by_cases h8 : k < 8
  · rw [Vector.getElem_append_left (by simpa using h8), b64_byte_bit _ h8 hj, if_pos (by omega)]
  · rw [Vector.getElem_append_right (by simp; omega), b64_byte_bit _ (by omega) hj, if_neg (by omega)]
    · congr 1; omega
    all_goals omega

theorem byte_ext {a b : UInt8} (h : ∀ j < 8, a.toBitVec.getLsbD j = b.toBitVec.getLsbD j) : a = b :=
  UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun j hj => h j hj)

/-- Bytes of two elements agree when their bits do. -/
theorem fb_congr {a b : F} {k k' : ℕ} (hk : k < 16) (hk' : k' < 16)
    (h : ∀ j < 8, bitN a (8 * k + j) = bitN b (8 * k' + j)) : fb a k = fb b k' :=
  byte_ext fun j hj => by rw [fb_bit a hk hj, fb_bit b hk' hj, h j hj]

/-! ## Blocks -/

/-- H's bit `p` of block `blk` is bit `p mod 128` of element `blk·128 + ⌊p/128⌋`. -/
theorem bitsB4_bit (w : Asg) (blk : ℕ) {p : ℕ} (hp : p < 2 ^ 14) :
    bitsB4 w blk (pos p) = bitN (w (blk * 128 + p / 128)) p := by
  have hv : ((pos p : Pos) : ℕ) = p := pos_val hp
  simp only [bitsB4, zB4, zW4, hv, unpack, bitN]
  have e1 : (blk * 2 ^ 14 + p) / 128 = blk * 128 + p / 128 := by omega
  have e2 : (blk * 2 ^ 14 + p) % 128 = p % 128 := by omega
  simp only [e1, e2]
  split_ifs with h <;> simp [h]

/-- `zN4` is the bit as `0`/`1`. -/
theorem zN4_eq (w : Asg) (blk : ℕ) {p : ℕ} (hp : p < 2 ^ 14) :
    zN4 w blk p = if bitN (w (blk * 128 + p / 128)) p then 1 else 0 := by
  have e1 : (blk * 2 ^ 14 + p) / 128 = blk * 128 + p / 128 := by omega
  have e2 : (blk * 2 ^ 14 + p) % 128 = p % 128 := by omega
  simp only [zN4, zW4, unpack, bitN, e1, e2]
  rfl

/-- Equal `zN4` bits are equal element bits. -/
theorem bit_of_zN4 {w : Asg} {blk p blk' p' : ℕ} (hp : p < 2 ^ 14) (hp' : p' < 2 ^ 14)
    (h : zN4 w blk p = zN4 w blk' p') :
    bitN (w (blk * 128 + p / 128)) p = bitN (w (blk' * 128 + p' / 128)) p' := by
  rw [zN4_eq w blk hp, zN4_eq w blk' hp'] at h
  split_ifs at h with h1 h2 h2 <;> simp_all

/-- **A block's byte at a byte offset `p` is its element's byte.** -/
theorem readByte_hc (w : Asg) (blk : ℕ) {p : ℕ} (hp : p < 2048) :
    readByte (bitsB4 w blk) (8 * p) = fb (w (hc blk (p / 16))) (p % 16) := by
  refine byte_ext fun j hj => ?_
  rw [readByte_getLsbD _ _ hj, bitsB4_bit w blk (by omega), fb_bit _ (Nat.mod_lt _ (by norm_num)) hj]
  have e1 : blk * 128 + (8 * p + j) / 128 = hc blk (p / 16) := by unfold hc; omega
  have e2 : (8 * p + j) % 128 = 8 * (p % 16) + j := by omega
  rw [e1]
  unfold bitN
  simp only [e2, Nat.mod_eq_of_lt (show 8 * (p % 16) + j < 128 by omega)]

/-- **`h_out` is elements 2–3.** -/
theorem readDigest_hc (w : Asg) (blk : ℕ) :
    Block.readDigest (bitsB4 w blk) 256 = Vector.ofFn fun i : Fin 32 => fb (w (hc blk (2 + i / 16))) (i % 16) := by
  refine Vector.ext fun i hi => ?_
  simp only [Block.readDigest, Vector.getElem_ofFn]
  rw [show 256 + 8 * i = 8 * (32 + i) by omega, readByte_hc w blk (by omega),
    show (32 + i) / 16 = 2 + i / 16 by omega, show (32 + i) % 16 = i % 16 by omega]

/-- **The message is elements 4–7.** -/
theorem msgByte_hc (w : Asg) (blk : ℕ) {p : ℕ} (hp : p < 64) :
    (msgBytes (bitsB4 w blk)).getD p 0 = fb (w (hc blk (4 + p / 16))) (p % 16) := by
  have hm : msgBase = 512 := rfl
  rw [msgBytes_getD _ hp, show msgBase + 8 * p = 8 * (64 + p) by omega,
    readByte_hc w blk (by omega), show (64 + p) / 16 = 4 + p / 16 by omega,
    show (64 + p) % 16 = p % 16 by omega]

/-! ## Digests of two elements -/

theorem ofFn_fb (a : F) : (Vector.ofFn fun i : Fin 16 => fb a i) = F.toBytes a :=
  Vector.ext fun i hi => by simp [fb, Nat.mod_eq_of_lt hi]

/-- **`digestOf`'s bytes**: byte `i` is byte `i mod 16` of the first element (`i < 16`) or the
second. -/
theorem digestOf_eq (w : Asg) (e₀ e₁ : ℕ) :
    Read.digestOf w e₀ e₁ = Vector.ofFn fun i : Fin 32 => fb (w (if i.1 < 16 then e₀ else e₁)) (i % 16) := by
  refine Snd.digestOf_halves ?_ ?_
  · rw [dlo]
    conv_lhs => rw [← F.ofBytes_toBytes (w e₀), ← ofFn_fb]
    refine congrArg F.ofBytes ?_
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_ofFn]
    rw [if_pos (by omega), Nat.mod_eq_of_lt hi]
  · rw [dhi]
    conv_lhs => rw [← F.ofBytes_toBytes (w e₁), ← ofFn_fb]
    refine congrArg F.ofBytes ?_
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_ofFn]
    rw [if_neg (by omega), show (16 + i) % 16 = i by omega]

/-- **`h_out` is the digest of elements 2–3.** -/
theorem readDigest_digestOf (w : Asg) (blk : ℕ) :
    Block.readDigest (bitsB4 w blk) 256 = Read.digestOf w (hc blk 2) (hc blk 3) := by
  rw [readDigest_hc, digestOf_eq]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_ofFn]
  split_ifs with h
  · rw [Nat.div_eq_of_lt h]
  · rw [show i / 16 = 1 by omega]

/-- Digests of equal elements are equal. -/
theorem digestOf_congr {w : Asg} {a b c d : ℕ} (h₀ : w a = w c) (h₁ : w b = w d) :
    Read.digestOf w a b = Read.digestOf w c d := by
  rw [digestOf_eq, digestOf_eq]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_ofFn]
  split_ifs <;> simp [h₀, h₁]

/-! ## The rows' readings -/

theorem eqR_val {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {x y : Lin} (h : (eqR κ x y).Holds w) :
    x.ev w = y.ev w := by
  simp only [Row.Holds, eqR, one, Lin.ev_cell, hone, one_mul, Lin.ev_sub, Lin.ev_nil] at h
  exact sub_eq_zero.mp h

theorem boolR_val {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {c : ℕ} (h : (boolR κ c).Holds w) :
    w c = 0 ∨ w c = 1 := by
  simp only [Row.Holds, boolR, one, Lin.ev_cell, hone, Lin.ev_sub, Lin.ev_nil, mul_eq_zero] at h
  rcases h with h | h
  · exact .inl h
  · exact .inr (sub_eq_zero.mp h).symm

/-- **The mux row** with a Boolean selector. -/
theorem muxR_val {w : Asg} {s x y m : Lin} (h : (muxR s x y m).Holds w) (hs : s.ev w = 0 ∨ s.ev w = 1) :
    m.ev w = if s.ev w = 1 then x.ev w else y.ev w := by
  simp only [Row.Holds, muxR, Lin.ev_sub] at h
  rcases hs with hs | hs
  · rw [hs, zero_mul] at h; rw [if_neg (by rw [hs]; exact zero_ne_one)]; exact (sub_eq_zero.mp h.symm)
  · rw [hs, one_mul] at h; rw [if_pos hs]; exact (sub_left_inj.mp h).symm

theorem gateR_val {w : Asg} {s x : Lin} (h : (gateR s x).Holds w) (hs : s.ev w = 1) : x.ev w = 0 := by
  simp only [Row.Holds, gateR, hs, one_mul, Lin.ev_nil] at h; exact h

/-! ## Packed bits -/

theorem pk_succ (cell : ℕ → ℕ) (n : ℕ) : pk cell (n + 1) = pk cell n ++ [(cell n, E n)] := by
  simp [pk, List.range_succ]

theorem pk_ev (w : Asg) (cell : ℕ → ℕ) (n : ℕ) :
    (pk cell n).ev w = ∑ q ∈ Finset.range n, E q * w (cell q) := by
  induction n with
  | zero => simp [pk]
  | succ n ih => rw [pk_succ, Lin.ev_append, ih, Finset.sum_range_succ]; simp [Lin.ev]

theorem bitF_E (q : ℕ) (hq : q < 128) (j : Fin 128) : bitF (E q) j = decide (j.val = q) := by
  rw [E, bitF_bitBasis]
  simp only [Fin.ext_iff, Nat.mod_eq_of_lt hq]
  exact decide_eq_decide.2 ⟨fun h => h.symm, fun h => h.symm⟩

/-- **Bit `j` of packed Boolean cells** is cell `j`. -/
theorem bitF_pk (w : Asg) (cell : ℕ → ℕ) {n : ℕ} (hn : n ≤ 128)
    (hb : ∀ q < n, w (cell q) = 0 ∨ w (cell q) = 1) (j : Fin 128) :
    bitF ((pk cell n).ev w) j = decide (j.val < n ∧ w (cell j.val) = 1) := by
  rw [pk_ev]
  induction n with
  | zero => simp [bitF_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, bitF_add, ih (by omega) fun q hq => hb q (by omega)]
    rcases hb n (by omega) with h | h
    · rw [h, mul_zero, bitF_zero, Bool.xor_false]
      refine decide_eq_decide.2 ⟨fun ⟨a, b⟩ => ⟨by omega, b⟩, fun ⟨a, b⟩ => ⟨?_, b⟩⟩
      rcases Nat.lt_or_ge j.val n with h' | h'
      · exact h'
      · have : j.val = n := by omega
        rw [this, h] at b; exact absurd b zero_ne_one
    · rw [h, mul_one, bitF_E n (by omega)]
      by_cases hj : j.val = n
      · simp [hj, h]
      · simp only [hj, decide_false, Bool.xor_false]
        exact decide_eq_decide.2 ⟨fun ⟨a, b⟩ => ⟨by omega, b⟩, fun ⟨a, b⟩ => ⟨by omega, b⟩⟩

end W4
end FR
