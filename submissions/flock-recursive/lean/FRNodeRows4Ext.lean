-- G6: this module also holds the former modules `FRNodeRows4AggChk`, `FRNodeRows4AggChkB`, `FRNodeRows4AggChkS`, `FRNodeRows4AskStmt` (one section each, in import order).
import FRNodeRows4Wots
import FRNodeRows4ArenaPlace
import FRNodeRows4WotsB

section G6_FRNodeRows4AggChk

-- New for `flock-recursive` (PACK-4.4.1 §4.3, §6.1, the B4 row of §7; stage B4, track L-circ).

/-!
# The aggregate's checks in-circuit (`aggChk`): the rows

`V_A` checks, against the aggregate's statement `c_A`, its segments' views: the chaining
`s_{i+1} = h_i`, the lengths `1 ≤ nᵢ ≤ cap κᵢ`, the sum `Σ nᵢ = n` and the end `h_{k−1} = e`
(`FRAgg.aggChecks`). `c_A = leafStmt e n` itself needs no row: it is the `hashA` block `cAB`'s
output (`FRNodeRows4AggChkS`). The rows here bind the rest; they sit with S-E13b's node rows at
slot 1 (`FRNodeRows4Ext.xRowsA`).

**Cells.** Sub-slot `i`'s stream elements (`sE κ σ i e`, A.7's `sCell` at the sub-slot's block
offset `i·sBlk`): `6, 7` are `hdr.pub` (the view's start), `13, 14, 15` hold the `stmt` field's bytes
`0–47` (the view's end `h` is bytes `1–32`, its length `n` bytes `33–40`); `cAB`'s message elements
`4, 5, 6` hold `tagLeaf ‖ e ‖ enc64 n` with the same byte layout. New L cells of signed child `σ`'s
`2^14` stride, from offset `12,288` (S-E13b and R-A′ use up to `11,648`): the bits `bC` of
elements `13–15` of each sub-slot, the bits `aC` of `cAB`'s elements `4` and `6`, the masked
length bits `mC`, the adder's products `pC` and carries `cC`, an inverse `iC` per sub-slot and the
range checks' products `xC`.

**Rows of aggregate `a`** (`aggRowsC`; `S i` sub-slot `i`'s activity, `ind j = [k = j]`):
* `decRowsI`: elements `13–15` of every sub-slot are their 128 packed Boolean bits (`pkO`);
* `rngRowsI`: `Sᵢ`-gated, the length bits `19–63` are zero and `nᵢ ≠ 0` (an inverse); per kind
  selector `s_ι` (exponent `c_ι`: `cap = 2^{c_ι}`) the bits above `c_ι` are zero and bit `c_ι`
  set forces the bits below to zero;
* `mskRowsI`: `mᵢ_t = Sᵢ · nᵢ_t` (`t < 19`);
* `chnRowsI` (`i ≥ 1`): `Sᵢ`-gated, elements `6, 7` of sub-slot `i` are the bytes `1–32` of
  sub-slot `i − 1`'s `13–15` (a byte shift: packed bits at offset `−8`);
* `decRowsA`: `cAB`'s elements `4` and `6` are their packed Boolean bits;
* `endRowsJ j`: `ind j`-gated, sub-slot `j − 1`'s `13/14/15` agree with `cAB`'s `4/5/6` on the
  bytes `1–15`, all, and byte `0`;
* `addRowsI`: the ripple-carry adder over `GF(2^128)`: a sum bit is `a + b + c` (characteristic 2),
  a carry `ab + (a + b)c`; the last carry is zero;
* `sumRow`: the adder's 21 output bits are bits `8–71` of `cAB`'s element `6` (the rest zero).
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c

/-! ## Cells -/

/-- The new cells' first offset in signed child `σ`'s L stride. -/
def aB : ℕ := 12288

/-- Bit `q` of sub-slot `i`'s stream element `13 + u` (`u < 3`). -/
def bC (κ : NodeKind) (σ i u q : ℕ) : ℕ := Lc κ σ (aB + 384 * i + 128 * u + q)
/-- Bit `q` of `cAB`'s element `4 + 2u` (`u < 2`). -/
def aC (κ : NodeKind) (σ u q : ℕ) : ℕ := Lc κ σ (aB + 1536 + 128 * u + q)
/-- The masked length bit `t` of sub-slot `i`. -/
def mC (κ : NodeKind) (σ i t : ℕ) : ℕ := Lc κ σ (aB + 1792 + 32 * i + t)
/-- The adder's product at bit `t` of addition `i`. -/
def pC (κ : NodeKind) (σ i t : ℕ) : ℕ := Lc κ σ (aB + 1920 + 32 * i + t)
/-- The adder's carry into bit `t` (`1 ≤ t ≤ 21`) of addition `i`. -/
def cC (κ : NodeKind) (σ i t : ℕ) : ℕ := Lc κ σ (aB + 2048 + 32 * i + t)
/-- Sub-slot `i`'s inverse of its length. -/
def iC (κ : NodeKind) (σ i : ℕ) : ℕ := Lc κ σ (aB + 2176 + i)
/-- The kinds' index (`FRNodeRows4.selIx`). -/
def kIx : Kind → ℕ | .L32 => 0 | .P30 => 1 | .N30 => 2

/-- Sub-slot `i`'s product `s_ι · bit_{c_ι}`. -/
def xC (κ : NodeKind) (σ i : ℕ) (ι : Kind) : ℕ := Lc κ σ (aB + 2184 + 4 * i + kIx ι)

/-- Sub-slot `i`'s stream element `e` in signed child `σ`'s chain (R-A′: segment `i` is
segment `0` shifted by `i·sBlk` blocks). -/
def sE (κ : NodeKind) (σ i e : ℕ) : ℕ := sCell (chBase κ σ + i * sBlk) e

/-- The selector copy of kind `ι` of slot `v`. -/
def selc (κ : NodeKind) (v : ℕ) (ι : Kind) : ℕ := κ.oneCell + (v * slotM4 + 1 + kIx ι)

/-- **The capacity exponent** of the segment kind selected by `ι` (`cap (segAt ι) = 2^{capE ι}`). -/
def capE : Kind → ℕ | .L32 => 18 | .P30 => 16 | .N30 => 17

/-- Sub-slot `i`'s length bit `t` (bit `8 + t` of element `15`). -/
def nb (κ : NodeKind) (σ i t : ℕ) : ℕ := bC κ σ i 2 (8 + t)

/-- **Packed Boolean cells at an offset**: `Σ_{q<n} E_{q+d} · cell q`. -/
def pkO (cell : ℕ → ℕ) (d n : ℕ) : Lin := (List.range n).map fun q => (cell q, E (q + d))

/-- The bits of sub-slot `i'`'s elements `13–15` that make up element `6` (`u = 0`) or `7`
(`u = 1`) of the next sub-slot: the bytes `1–15` of `13 + u`, then byte `0` of `14 + u`. -/
def shC (κ : NodeKind) (σ i' u q : ℕ) : ℕ := if q < 120 then bC κ σ i' u (q + 8) else bC κ σ i' (u + 1) (q - 120)

/-! ## Rows -/

/-- Sub-slot `i`'s elements `13–15` are their packed Boolean bits. -/
def decRowsI (κ : NodeKind) (σ i : ℕ) : List Row :=
  (List.range 3).flatMap fun u =>
    eqR κ (Lin.cell (sE κ σ i (13 + u))) (pkO (bC κ σ i u) 0 128) ::
      (List.range 128).map fun q => boolR κ (bC κ σ i u q)

/-- Sub-slot `i`'s length range, gated by its activity `S` and its kind selectors. -/
def rngRowsI (κ : NodeKind) (σ v i : ℕ) (S : Lin) : List Row :=
  [gateR S (pkO (fun t => nb κ σ i (19 + t)) 0 45),
   ⟨pkO (nb κ σ i) 0 19, Lin.cell (iC κ σ i), S⟩] ++
  Circ.kinds.flatMap fun ι =>
    [gateR (Lin.cell (selc κ v ι)) (pkO (fun t => nb κ σ i (capE ι + 1 + t)) 0 (18 - capE ι)),
     ⟨Lin.cell (selc κ v ι), Lin.cell (nb κ σ i (capE ι)), Lin.cell (xC κ σ i ι)⟩,
     gateR (Lin.cell (xC κ σ i ι)) (pkO (nb κ σ i) 0 (capE ι))]

/-- Sub-slot `i`'s masked length bits `mᵢ_t = Sᵢ · nᵢ_t`. -/
def mskRowsI (κ : NodeKind) (σ i : ℕ) (S : Lin) : List Row :=
  (List.range 19).map fun t => ⟨S, Lin.cell (nb κ σ i t), Lin.cell (mC κ σ i t)⟩

/-- Sub-slot `i ≥ 1`'s start (elements `6, 7`) is sub-slot `i − 1`'s end, gated by its activity. -/
def chnRowsI (κ : NodeKind) (σ i : ℕ) (S : Lin) : List Row :=
  (List.range 2).map fun u => gateR S ((Lin.cell (sE κ σ i (6 + u))).sub (pkO (shC κ σ (i - 1) u) 0 128))

/-- `cAB`'s elements `4` and `6` are their packed Boolean bits. -/
def decRowsA (κ : NodeKind) (σ a : ℕ) : List Row :=
  (List.range 2).flatMap fun u =>
    eqR κ (Lin.cell (hc (cAB κ a) (4 + 2 * u))) (pkO (aC κ σ u) 0 128) ::
      (List.range 128).map fun q => boolR κ (aC κ σ u q)

/-- **The end**, gated by `[k = j]`: sub-slot `j − 1`'s `13/14/15` agree with `cAB`'s `4/5/6` on
bytes `1–15`, all, byte `0`. -/
def endRowsJ (κ : NodeKind) (σ a : ℕ) (G : Lin) (j : ℕ) : List Row :=
  [gateR G ((pkO (fun q => bC κ σ (j - 1) 0 (q + 8)) 8 120).sub (pkO (fun q => aC κ σ 0 (q + 8)) 8 120)),
   gateR G ((Lin.cell (sE κ σ (j - 1) 14)).sub (Lin.cell (hc (cAB κ a) 5))),
   gateR G ((pkO (bC κ σ (j - 1) 2) 0 8).sub (pkO (aC κ σ 1) 0 8))]

/-- The adder's width (`Σ nᵢ ≤ 4·2^18 < 2^21`). -/
def adW : ℕ := 21

/-- The masked length bit `t` of sub-slot `i` (zero from bit 19). -/
def mL (κ : NodeKind) (σ i t : ℕ) : Lin := if t < 19 then Lin.cell (mC κ σ i t) else []

/-- The carry into bit `t` of addition `i` (zero into bit 0). -/
def cL (κ : NodeKind) (σ i t : ℕ) : Lin := if t = 0 then [] else Lin.cell (cC κ σ i t)

/-- **The running sum's bit `t`** after sub-slot `i`: `acc₀ = m₀`, `acc_{i+1} = acc_i + m_{i+1} + c`. -/
def accL (κ : NodeKind) (σ : ℕ) : ℕ → ℕ → Lin
  | 0, t => mL κ σ 0 t
  | i + 1, t => accL κ σ i t ++ mL κ σ (i + 1) t ++ cL κ σ (i + 1) t

/-- **Addition `i ≥ 1`**: per bit `t < 21`, `p = a·b`, `c_{t+1} − p = (a + b)·c_t`; `c_21 = 0`. -/
def addRowsI (κ : NodeKind) (σ i : ℕ) : List Row :=
  (List.range adW).flatMap (fun t =>
    [⟨accL κ σ (i - 1) t, mL κ σ i t, Lin.cell (pC κ σ i t)⟩,
     ⟨accL κ σ (i - 1) t ++ mL κ σ i t, cL κ σ i t, (Lin.cell (cC κ σ i (t + 1))).sub (Lin.cell (pC κ σ i t))⟩]) ++
  [gateR (one κ) (Lin.cell (cC κ σ i adW))]

/-- The packed sum `Σ_{t<21} E_t · acc_t`. -/
def accP (κ : NodeKind) (σ i : ℕ) : Lin := (List.range adW).flatMap fun t => (accL κ σ i t).smul (E t)

/-- **The sum**: the adder's output is bits `8–71` of `cAB`'s element `6` (its length `n`). -/
def sumRow (κ : NodeKind) (σ : ℕ) : Row :=
  eqR κ (accP κ σ (κ.maxK - 1)) (pkO (fun t => aC κ σ 1 (8 + t)) 0 64)

/-- The rows of sub-slot `i` (`S`: the aggregate's sub-slot activities). -/
def subRows (κ : NodeKind) (a : ℕ) (S : ℕ → Lin) (i : ℕ) : List Row :=
  let σ := aggChild κ a
  decRowsI κ σ i ++ rngRowsI κ σ (N4c.sub κ a i) i (S i) ++ mskRowsI κ σ i (S i) ++
    (if i = 0 then [] else chnRowsI κ σ i (S i))

/-- **Aggregate `a`'s check rows** (`S`: its sub-slots' activities, `FRNodeRows4Ext.actW`). -/
def aggRowsC (κ : NodeKind) (a : ℕ) (S : ℕ → Lin) : List Row :=
  let σ := aggChild κ a
  (List.range κ.maxK).flatMap (subRows κ a S) ++ decRowsA κ σ a ++
    (List.range κ.maxK).flatMap (fun j => endRowsJ κ σ a (ind κ S (j + 1)) (j + 1)) ++
    (List.range (κ.maxK - 1)).flatMap (fun i => addRowsI κ σ (i + 1)) ++ [sumRow κ σ]

/-! ## Counts -/

theorem subRows_length_le (κ : NodeKind) (a : ℕ) (S : ℕ → Lin) (i : ℕ) : (subRows κ a S i).length ≤ 419 := by
  unfold subRows
  split_ifs <;>
    simp [decRowsI, rngRowsI, mskRowsI, chnRowsI, List.length_flatMap, Circ.kinds]

theorem aggRowsC_length_le (κ : NodeKind) (a : ℕ) (S : ℕ → Lin) : (aggRowsC κ a S).length ≤ 2076 := by
  have hm : κ.maxK ≤ 4 := by cases κ <;> decide
  have h1 : ((List.range κ.maxK).flatMap (subRows κ a S)).length ≤ κ.maxK * 419 := by
    rw [List.length_flatMap]
    refine le_trans (List.sum_le_length_nsmul _ 419 fun x hx => ?_) (by simp)
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact subRows_length_le κ a S i
  have h2 : (decRowsA κ (aggChild κ a) a).length = 258 := by simp [decRowsA, List.length_flatMap]
  have h3 : ((List.range κ.maxK).flatMap (fun j => endRowsJ κ (aggChild κ a) a
      (ind κ S (j + 1)) (j + 1))).length = κ.maxK * 3 := by
    simp [endRowsJ, List.length_flatMap]
  have h4 : ((List.range (κ.maxK - 1)).flatMap (fun i => addRowsI κ (aggChild κ a) (i + 1))).length =
      (κ.maxK - 1) * 43 := by
    simp [addRowsI, List.length_flatMap, adW]
  simp only [aggRowsC, List.length_append, List.length_singleton]
  rw [h2, h3, h4]
  have : 2 ≤ κ.maxK := by cases κ <;> decide
  omega

end W4
end FR

end G6_FRNodeRows4AggChk

section G6_FRNodeRows4AggChkB

-- New for `flock-recursive` (PACK-4.4.1 §4.3; stage B4, track L-circ): bits, bytes and numbers.

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

end G6_FRNodeRows4AggChkB

section G6_FRNodeRows4AggChkS

-- New for `flock-recursive` (PACK-4.4.1 §4.3; stage B4, track L-circ): what the check rows give.

/-!
# What aggregate `a`'s check rows give

On `one = 1` and the rows `aggRowsC κ a S` (`S i`: sub-slot `i`'s activity, `0` or `1`, `1` exactly
below the segment count `k`), in terms of the stream's elements (`sE`) and `cAB`'s message:

* **`chain_sub`**: an active sub-slot `i ≥ 1` starts (`dg2` of its elements `6, 7`) at sub-slot
  `i − 1`'s end (`sh1` of its `13, 14, 15`);
* **`end_sub`**: at `[k = j]`, sub-slot `j − 1`'s end is `cAB`'s `e` (`sh1` of its `4, 5, 6`);
* **`rng_sub`**: an active sub-slot of selected kind `ι` has `1 ≤ n ≤ 2^{capE ι}` (`n8` of its
  element `15`);
* **`sum_sub`**: `Σ_{i<k} nᵢ = n8 (cAB's element 6)`.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Finset

section Rows
variable {κ : NodeKind} {a : ℕ} {S : ℕ → Lin} {w : Asg}

/-! ## Membership -/

theorem mem_sub {i : ℕ} (hi : i < κ.maxK) {r : Row} (h : r ∈ subRows κ a S i) : r ∈ aggRowsC κ a S := by
  unfold aggRowsC
  simp only [List.mem_append]
  exact .inl (.inl (.inl (.inl (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, h⟩))))

theorem mem_decA {r : Row} (h : r ∈ decRowsA κ (aggChild κ a) a) : r ∈ aggRowsC κ a S := by
  unfold aggRowsC; simp only [List.mem_append]; exact .inl (.inl (.inl (.inr h)))

theorem mem_end {j : ℕ} (hj : j < κ.maxK) {r : Row}
    (h : r ∈ endRowsJ κ (aggChild κ a) a (ind κ S (j + 1)) (j + 1)) : r ∈ aggRowsC κ a S := by
  unfold aggRowsC; simp only [List.mem_append]
  exact .inl (.inl (.inr (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, h⟩)))

theorem mem_add {i : ℕ} (hi : i + 1 < κ.maxK) {r : Row} (h : r ∈ addRowsI κ (aggChild κ a) (i + 1)) :
    r ∈ aggRowsC κ a S := by
  unfold aggRowsC; simp only [List.mem_append]
  exact .inl (.inr (List.mem_flatMap.2 ⟨i, List.mem_range.2 (by omega), h⟩))

theorem mem_sum : sumRow κ (aggChild κ a) ∈ aggRowsC κ a S := by
  unfold aggRowsC; simp

/-! ## Row values -/

theorem gate_ev {s x : Lin} (h : (gateR s x).Holds w) : s.ev w * x.ev w = 0 := by
  simpa [Row.Holds, gateR] using h

theorem gate_one {s x : Lin} (h : (gateR s x).Holds w) (hs : s.ev w = 1) : x.ev w = 0 := by
  simpa [hs] using gate_ev h

theorem row_ev {x y z : Lin} (h : (⟨x, y, z⟩ : Row).Holds w) : x.ev w * y.ev w = z.ev w := h

variable (hone : w κ.oneCell = 1) (hR : ∀ r ∈ aggRowsC κ a S, r.Holds w)
include hone hR

/-! ## The decompositions -/

/-- **Elements `13 + u` of sub-slot `i` are their Boolean bits.** -/
theorem bits_sub {i u : ℕ} (hi : i < κ.maxK) (hu : u < 3) :
    BoolC w (bC κ (aggChild κ a) i u) 128 ∧
      w (sE κ (aggChild κ a) i (13 + u)) = (pkO (bC κ (aggChild κ a) i u) 0 128).ev w := by
  have hm : ∀ r ∈ decRowsI κ (aggChild κ a) i, r.Holds w := fun r hr =>
    hR r (mem_sub hi (by unfold subRows; simp only [List.mem_append]; exact .inl (.inl (.inl hr))))
  have hu' : ∀ r, r ∈ (eqR κ (Lin.cell (sE κ (aggChild κ a) i (13 + u))) (pkO (bC κ (aggChild κ a) i u) 0 128) ::
      (List.range 128).map fun q => boolR κ (bC κ (aggChild κ a) i u q)) → r.Holds w := fun r hr =>
    hm r (List.mem_flatMap.2 ⟨u, List.mem_range.2 hu, hr⟩)
  refine ⟨fun q hq => boolR_val hone (hu' _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩))), ?_⟩
  simpa using eqR_val hone (hu' _ List.mem_cons_self)

/-- **`cAB`'s elements `4 + 2u` are their Boolean bits.** -/
theorem bits_A {u : ℕ} (hu : u < 2) :
    BoolC w (aC κ (aggChild κ a) u) 128 ∧ w (hc (cAB κ a) (4 + 2 * u)) = (pkO (aC κ (aggChild κ a) u) 0 128).ev w := by
  have hu' : ∀ r, r ∈ (eqR κ (Lin.cell (hc (cAB κ a) (4 + 2 * u))) (pkO (aC κ (aggChild κ a) u) 0 128) ::
      (List.range 128).map fun q => boolR κ (aC κ (aggChild κ a) u q)) → r.Holds w := fun r hr =>
    hR r (mem_decA (List.mem_flatMap.2 ⟨u, List.mem_range.2 hu, hr⟩))
  refine ⟨fun q hq => boolR_val hone (hu' _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩))), ?_⟩
  simpa using eqR_val hone (hu' _ List.mem_cons_self)

/-- **The string `13 ‖ 14 ‖ 15` of sub-slot `i` is its bits.** -/
theorem catBit_sub {i Q : ℕ} (hi : i < κ.maxK) (hQ : Q < 384) :
    catBit (w (sE κ (aggChild κ a) i 13)) (w (sE κ (aggChild κ a) i 14)) (w (sE κ (aggChild κ a) i 15)) Q =
      decide (w (bC κ (aggChild κ a) i (Q / 128) (Q % 128)) = 1) := by
  have hq := Nat.mod_lt Q (show 0 < 128 by norm_num)
  obtain ⟨hb, he⟩ := bits_sub hone hR hi (show Q / 128 < 3 by omega)
  rw [catBit, bitN_mod, ← bitN_dec w hb he hq]
  rcases (by omega : Q / 128 = 0 ∨ Q / 128 = 1 ∨ Q / 128 = 2) with h | h | h <;> rw [h] <;> rfl

/-! ## The chaining -/

/-- **An active later sub-slot starts at its predecessor's end.** -/
theorem chain_sub {i : ℕ} (hi1 : 1 ≤ i) (hi : i < κ.maxK) (hS : (S i).ev w = 1) :
    dg2 (w (sE κ (aggChild κ a) i 6)) (w (sE κ (aggChild κ a) i 7)) =
      sh1 (w (sE κ (aggChild κ a) (i - 1) 13)) (w (sE κ (aggChild κ a) (i - 1) 14))
        (w (sE κ (aggChild κ a) (i - 1) 15)) := by
  set σ := aggChild κ a
  have hc : ∀ u < 2, w (sE κ σ i (6 + u)) = (pkO (shC κ σ (i - 1) u) 0 128).ev w := fun u hu => by
    have hr := hR _ (mem_sub hi (r := gateR (S i) ((Lin.cell (sE κ σ i (6 + u))).sub (pkO (shC κ σ (i - 1) u) 0 128)))
      (by unfold subRows; simp only [List.mem_append, if_neg (show i ≠ 0 by omega)]
          exact .inr (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩)))
    have := gate_one hr hS
    simpa [sub_eq_zero] using this
  have hb : ∀ u < 2, BoolC w (shC κ σ (i - 1) u) 128 := fun u hu q hq => by
    unfold shC; split_ifs
    · exact (bits_sub hone hR (by omega) (by omega : u < 3)).1 _ (by omega)
    · exact (bits_sub hone hR (by omega) (by omega : u + 1 < 3)).1 _ (by omega)
  refine Vector.ext fun j hj => ?_
  simp only [dg2, sh1, Vector.getElem_ofFn]
  refine catByte_congr fun b hb8 => ?_
  rw [catBit_sub hone hR (by omega) (by omega)]
  have hP : 8 * j + b < 256 := by omega
  have hL : catBit (w (sE κ σ i 6)) (w (sE κ σ i 7)) 0 (8 * j + b) =
      decide (w (shC κ σ (i - 1) ((8 * j + b) / 128) ((8 * j + b) % 128)) = 1) := by
    have hm := Nat.mod_lt (8 * j + b) (show 0 < 128 by norm_num)
    rcases (by omega : (8 * j + b) / 128 = 0 ∨ (8 * j + b) / 128 = 1) with h | h
    · rw [catBit, h, bitN_mod]; exact bitN_dec w (hb 0 (by norm_num)) (hc 0 (by norm_num)) hm
    · rw [catBit, h, bitN_mod]; exact bitN_dec w (hb 1 (by norm_num)) (hc 1 (by norm_num)) hm
  rw [hL]
  unfold shC
  split_ifs with h
  · rw [show (8 * (1 + j) + b) / 128 = (8 * j + b) / 128 by omega,
      show (8 * (1 + j) + b) % 128 = (8 * j + b) % 128 + 8 by omega]
  · rw [show (8 * (1 + j) + b) / 128 = (8 * j + b) / 128 + 1 by omega,
      show (8 * (1 + j) + b) % 128 = (8 * j + b) % 128 - 120 by omega]

/-! ## The end -/

/-- **At `[k = j]`, sub-slot `j − 1` ends at `cAB`'s `e`.** -/
theorem end_sub {j : ℕ} (hj : j < κ.maxK) (hind : (ind κ S (j + 1)).ev w = 1) :
    sh1 (w (sE κ (aggChild κ a) j 13)) (w (sE κ (aggChild κ a) j 14)) (w (sE κ (aggChild κ a) j 15)) =
      sh1 (w (hc (cAB κ a) 4)) (w (hc (cAB κ a) 5)) (w (hc (cAB κ a) 6)) := by
  set σ := aggChild κ a
  have hE : ∀ r ∈ endRowsJ κ σ a (ind κ S (j + 1)) (j + 1), r.Holds w := fun r hr => hR r (mem_end hj hr)
  simp only [endRowsJ, Nat.add_sub_cancel, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq] at hE
  obtain ⟨h1, h2, h3⟩ := hE
  have e1 := gate_one h1 hind
  have e2 := gate_one h2 hind
  have e3 := gate_one h3 hind
  simp only [Lin.ev_sub, Lin.ev_cell, sub_eq_zero] at e1 e2 e3
  obtain ⟨b0, d0⟩ := bits_sub hone hR hj (show 0 < 3 by norm_num)
  obtain ⟨b2, d2⟩ := bits_sub hone hR hj (show 2 < 3 by norm_num)
  obtain ⟨a0, da0⟩ := bits_A hone hR (show 0 < 2 by norm_num)
  obtain ⟨a1, da1⟩ := bits_A hone hR (show 1 < 2 by norm_num)
  simp only [Nat.add_zero, Nat.mul_zero, Nat.mul_one] at d0 d2 da0 da1
  refine Vector.ext fun i hi => ?_
  simp only [sh1, Vector.getElem_ofFn]
  refine catByte_congr fun b hb => ?_
  set Q := 8 * (1 + i) + b
  by_cases hQ1 : Q < 128
  · rw [catBit_lt _ _ _ hQ1, catBit_lt _ _ _ hQ1, bitN_dec w b0 d0 hQ1, bitN_dec w a0 da0 hQ1]
    have := pkO_bits_eq w (by norm_num) (fun q hq => b0 _ (by omega)) (fun q hq => a0 _ (by omega)) e1
      (q := Q - 8) (by omega)
    simp only [Nat.sub_add_cancel (show 8 ≤ Q by omega)] at this
    exact decide_eq_decide.2 this
  by_cases hQ2 : Q < 256
  · rw [catBit_mid _ _ _ (by omega) hQ2, catBit_mid _ _ _ (by omega) hQ2, e2]
  · have hQ3 : Q < 264 := by omega
    rw [catBit_hi _ _ _ (by omega) (by omega), catBit_hi _ _ _ (by omega) (by omega),
      bitN_dec w b2 d2 (by omega), bitN_dec w a1 da1 (by omega)]
    exact decide_eq_decide.2 (pkO_bits_eq w (by norm_num) (fun q hq => b2 _ (by omega))
      (fun q hq => a1 _ (by omega)) e3 (by omega))

/-! ## The lengths' range -/

theorem rng_rows {i : ℕ} (hi : i < κ.maxK) :
    ∀ r ∈ rngRowsI κ (aggChild κ a) (N4c.sub κ a i) i (S i), r.Holds w := fun r hr =>
  hR r (mem_sub hi (by unfold subRows; simp only [List.mem_append]; exact .inl (.inl (.inr hr))))

/-- **An active sub-slot's length bits from 19 on are clear.** -/
theorem hi_zero {i : ℕ} (hi : i < κ.maxK) (hS : (S i).ev w = 1) {t : ℕ} (h1 : 19 ≤ t) (h2 : t < 64) :
    w (nb κ (aggChild κ a) i t) = 0 := by
  have hb := (bits_sub hone hR hi (show 2 < 3 by norm_num)).1
  have h := gate_one (rng_rows hone hR hi _ (List.mem_append_left _ (List.mem_cons_self ..))) hS
  have := pkO_zero w (c := fun t => nb κ (aggChild κ a) i (19 + t)) (by norm_num)
    (fun q hq => hb _ (by omega)) h (q := t - 19) (by omega)
  simpa [Nat.add_sub_cancel' h1] using this

/-- **An active sub-slot of selected kind `ι` has `1 ≤ n ≤ 2^{capE ι}`.** -/
theorem rng_sub {i : ℕ} (hi : i < κ.maxK) (hS : (S i).ev w = 1) {ι : Kind}
    (hsel : ∀ ι', w (selc κ (N4c.sub κ a i) ι') = if ι' = ι then 1 else 0) :
    1 ≤ n8 (w (sE κ (aggChild κ a) i 15)) ∧ n8 (w (sE κ (aggChild κ a) i 15)) ≤ 2 ^ capE ι := by
  set σ := aggChild κ a
  obtain ⟨b2, d2⟩ := bits_sub hone hR hi (show 2 < 3 by norm_num)
  have hnb : BoolC w (nb κ σ i) 64 := fun t ht => b2 (8 + t) (by omega)
  set f : ℕ → Bool := fun t => decide (w (nb κ σ i t) = 1) with hf
  have hn : n8 (w (sE κ σ i 15)) = nOfBits f 64 := by
    rw [n8_bits]; exact nOfBits_congr fun t ht => bitN_dec w b2 d2 (by omega)
  have hR' := rng_rows hone hR hi
  have hk : ∀ r ∈ [gateR (Lin.cell (selc κ (N4c.sub κ a i) ι))
      (pkO (fun t => nb κ σ i (capE ι + 1 + t)) 0 (18 - capE ι)),
      ⟨Lin.cell (selc κ (N4c.sub κ a i) ι), Lin.cell (nb κ σ i (capE ι)), Lin.cell (xC κ σ i ι)⟩,
      gateR (Lin.cell (xC κ σ i ι)) (pkO (nb κ σ i) 0 (capE ι))], r.Holds w := fun r hr =>
    hR' r (List.mem_append_right _ (List.mem_flatMap.2 ⟨ι, kinds_mem ι, hr⟩))
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hk
  obtain ⟨k2, k3, k4⟩ := hk
  have hs1 : w (selc κ (N4c.sub κ a i) ι) = 1 := by rw [hsel ι, if_pos rfl]
  have hc := capE_le ι
  set c := capE ι
  -- bits above `c` are clear
  have hz2 := gate_one k2 (by simpa using hs1)
  have hhi : ∀ t, c + 1 ≤ t → t < 64 → f t = false := fun t h1 h2 => by
    simp only [hf, decide_eq_false_iff_not]
    by_cases h19 : t < 19
    · have := pkO_zero w (c := fun t => nb κ σ i (c + 1 + t)) (by omega) (fun q hq => hnb _ (by omega)) hz2
        (q := t - (c + 1)) (by omega)
      simp only [Nat.add_sub_cancel' h1] at this
      rw [this]; exact zero_ne_one
    · rw [hi_zero hone hR hi hS (by omega) h2]; exact zero_ne_one
  have hv : nOfBits f 64 = nOfBits f c + 2 ^ c * (if f c then 1 else 0) := by
    rw [nOfBits_high (m' := c + 1) (by omega) hhi, nOfBits_add, nOfBits_one, Nat.add_zero]
  have hx : w (xC κ σ i ι) = w (nb κ σ i c) := by
    have := row_ev k3; simp only [Lin.ev_cell, hs1, one_mul] at this; exact this.symm
  rw [hn]
  refine ⟨?_, ?_⟩
  · -- `n ≠ 0`: the inverse row
    have h4 := row_ev (hR' _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    simp only [Lin.ev_cell, hS] at h4
    by_contra hlt
    have h0 : nOfBits f 64 = 0 := by omega
    have hall : ∀ t < 19, w (nb κ σ i t) = 0 := fun t ht => by
      rcases hnb t (by omega) with h | h
      · exact h
      · have := nOfBits_ge (f := f) (m := 64) (t := t) (by omega) (by simp [hf, h]); have := Nat.two_pow_pos t; omega
    have : (pkO (nb κ σ i) 0 19).ev w = 0 := by
      rw [pkO_ev]; exact sum_eq_zero fun t ht => by rw [hall t (mem_range.1 ht), mul_zero]
    rw [this, zero_mul] at h4
    exact zero_ne_one h4
  · rw [hv]
    by_cases hfc : f c = true
    · -- bit `c` set: the bits below are clear
      have hw : w (nb κ σ i c) = 1 := by simpa [hf] using hfc
      have hz4 := gate_one k4 (by simpa [hx] using hw)
      have hlo : nOfBits f c = 0 := nOfBits_zero fun t ht => by
        simp only [hf, decide_eq_false_iff_not]
        rw [pkO_zero w (by omega) (fun q hq => hnb _ (by omega)) hz4 ht]; exact zero_ne_one
      rw [hlo, if_pos hfc]; omega
    · rw [if_neg hfc]; have := nOfBits_lt f c; omega

end Rows

section Sum
variable {κ : NodeKind} {a : ℕ} {S : ℕ → Lin} {w : Asg}

/-- **The ripple-carry adder** (bits `t < N`): Boolean `a`, `b`, carries `c` with `c₀ = 0`, the rows of
each bit; the sum bits `a + b + c` are Boolean and `Σ a + Σ b = Σ (a + b + c) + 2^T c_T`. -/
theorem ripple (N : ℕ) (A B C P : ℕ → F) (ha : ∀ t < N, A t = 0 ∨ A t = 1) (hb : ∀ t < N, B t = 0 ∨ B t = 1)
    (hc0 : C 0 = 0) (hp : ∀ t < N, A t * B t = P t) (hc : ∀ t < N, (A t + B t) * C t = C (t + 1) - P t) :
    ∀ T ≤ N, (C T = 0 ∨ C T = 1) ∧ (∀ t < T, A t + B t + C t = 0 ∨ A t + B t + C t = 1) ∧
      nOfBits (fun t => dv (A t)) T + nOfBits (fun t => dv (B t)) T =
        nOfBits (fun t => dv (A t + B t + C t)) T + 2 ^ T * nv (C T)
  | 0, _ => ⟨.inl hc0, fun t ht => absurd ht (Nat.not_lt_zero _), by simp [nOfBits_dv, hc0, nv_zero]⟩
  | T + 1, hT => by
    obtain ⟨hcT, hs, ih⟩ := ripple N A B C P ha hb hc0 hp hc T (by omega)
    obtain ⟨hsT, hcT', e⟩ := full_add (ha T (by omega)) (hb T (by omega)) hcT (hp T (by omega)) (hc T (by omega))
    refine ⟨hcT', fun t ht => ?_, ?_⟩
    · rcases Nat.lt_or_ge t T with h | h
      · exact hs t h
      · rw [show t = T by omega]; exact hsT
    · simp only [nOfBits_dv, sum_range_succ] at ih ⊢
      rw [pow_succ]
      have e' : (nv (A T) + nv (B T)) * 2 ^ T + nv (C T) * 2 ^ T =
          (nv (A T + B T + C T) + 2 * nv (C (T + 1))) * 2 ^ T := by
        rw [← add_mul, e]
      nlinarith [ih, e']

variable (hone : w κ.oneCell = 1) (hR : ∀ r ∈ aggRowsC κ a S, r.Holds w)
include hone hR

/-- **The lengths add up**: `Σ_{i<k} nᵢ` is `cAB`'s `n` (bits `8–71` of its element `6`). -/
theorem sum_sub {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ κ.maxK)
    (hP : ∀ i < κ.maxK, (S i).ev w = if i < k then 1 else 0) :
    ∑ i ∈ range k, n8 (w (sE κ (aggChild κ a) i 15)) = n8 (w (hc (cAB κ a) 6)) := by
  set σ := aggChild κ a
  have hm2 : 2 ≤ κ.maxK := by cases κ <;> decide
  -- the masks
  have hmask : ∀ i < κ.maxK, ∀ t < 19, w (mC κ σ i t) = (S i).ev w * w (nb κ σ i t) := fun i hi t ht => by
    have hr := hR _ (mem_sub hi (r := ⟨S i, Lin.cell (nb κ σ i t), Lin.cell (mC κ σ i t)⟩)
      (by unfold subRows; simp only [List.mem_append]
          exact .inl (.inr (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩))))
    simpa using (row_ev hr).symm
  have hnb : ∀ i < κ.maxK, ∀ t < 64, w (nb κ σ i t) = 0 ∨ w (nb κ σ i t) = 1 := fun i hi t ht =>
    (bits_sub hone hR hi (show 2 < 3 by norm_num)).1 (8 + t) (by omega)
  have hmB : ∀ i < κ.maxK, ∀ t, (mL κ σ i t).ev w = 0 ∨ (mL κ σ i t).ev w = 1 := fun i hi t => by
    rw [mL_ev]
    split_ifs with ht
    · rw [hmask i hi t ht, hP i hi]
      split_ifs
      · rw [one_mul]; exact hnb i hi t (by omega)
      · left; exact zero_mul _
    · exact .inl rfl
  -- each sub-slot's masked value
  have hmval : ∀ i < κ.maxK, nOfBits (fun t => dv ((mL κ σ i t).ev w)) 21 =
      if i < k then n8 (w (sE κ σ i 15)) else 0 := fun i hi => by
    split_ifs with hik
    · have hS : (S i).ev w = 1 := by rw [hP i hi, if_pos hik]
      obtain ⟨b2, d2⟩ := bits_sub hone hR hi (show 2 < 3 by norm_num)
      set f : ℕ → Bool := fun t => decide (w (nb κ σ i t) = 1)
      have h1 : n8 (w (sE κ σ i 15)) = nOfBits f 19 := by
        rw [n8_bits, nOfBits_congr (g := f) fun t ht => bitN_dec w b2 d2 (by omega)]
        exact nOfBits_high (by norm_num) fun t h1 h2 => by
          simp only [f, decide_eq_false_iff_not]; rw [hi_zero hone hR hi hS h1 h2]; exact zero_ne_one
      rw [h1, nOfBits_high (m' := 19) (by norm_num) fun t h1 h2 => by
        simp only [mL_ev, if_neg (show ¬ t < 19 by omega), dv, decide_eq_false_iff_not]; exact zero_ne_one]
      refine nOfBits_congr fun t ht => ?_
      simp only [mL_ev, if_pos ht, hmask i hi t ht, hS, one_mul, dv, f]
    · have hS : (S i).ev w = 0 := by rw [hP i hi, if_neg hik]
      refine nOfBits_zero fun t ht => ?_
      simp only [mL_ev, dv, decide_eq_false_iff_not]
      split_ifs with h
      · rw [hmask i hi t h, hS, zero_mul]; exact zero_ne_one
      · exact zero_ne_one
  -- the adder, addition by addition
  have hacc : ∀ i < κ.maxK, (∀ t < adW, (accL κ σ i t).ev w = 0 ∨ (accL κ σ i t).ev w = 1) ∧
      nOfBits (fun t => dv ((accL κ σ i t).ev w)) adW =
        ∑ i' ∈ range (i + 1), nOfBits (fun t => dv ((mL κ σ i' t).ev w)) 21 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨fun t _ => hmB 0 (by omega) t, by simp [accL, adW]⟩
    | succ i ih =>
      intro hi
      obtain ⟨ihb, ihv⟩ := ih (by omega)
      have hA : ∀ r ∈ addRowsI κ σ (i + 1), r.Holds w := fun r hr => hR r (mem_add hi hr)
      simp only [addRowsI, Nat.add_sub_cancel, List.mem_append, List.mem_flatMap, List.mem_range,
        List.mem_cons, List.mem_nil_iff, or_false, List.mem_singleton] at hA
      have hp : ∀ t < adW, (accL κ σ i t).ev w * (mL κ σ (i + 1) t).ev w = w (pC κ σ (i + 1) t) := fun t ht => by
        simpa using row_ev (hA _ (.inl ⟨t, ht, .inl rfl⟩))
      have hc : ∀ t < adW, ((accL κ σ i t).ev w + (mL κ σ (i + 1) t).ev w) * (cL κ σ (i + 1) t).ev w =
          (cL κ σ (i + 1) (t + 1)).ev w - w (pC κ σ (i + 1) t) := fun t ht => by
        have := row_ev (hA _ (.inl ⟨t, ht, .inr rfl⟩))
        simpa [cL_ev, Lin.ev_append] using this
      have h21 : (cL κ σ (i + 1) adW).ev w = 0 := by
        have := gate_one (hA _ (.inr rfl)) (by simpa [one] using hone)
        simpa [cL_ev, adW] using this
      obtain ⟨-, hsb, e⟩ := ripple adW (fun t => (accL κ σ i t).ev w) (fun t => (mL κ σ (i + 1) t).ev w)
        (fun t => (cL κ σ (i + 1) t).ev w) (fun t => w (pC κ σ (i + 1) t)) ihb
        (fun t _ => hmB (i + 1) hi t) (by simp [cL_ev]) hp hc adW le_rfl
      simp only [h21, nv_zero, mul_zero, add_zero] at e
      refine ⟨fun t ht => by rw [accL_succ_ev]; exact hsb t ht, ?_⟩
      simp only [accL_succ_ev]
      rw [← e, ihv, sum_range_succ _ (i + 1)]; rfl
  -- the sum row
  have hlast := hacc (κ.maxK - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ κ.maxK)] at hlast
  obtain ⟨hlb, hlv⟩ := hlast
  have hs := eqR_val hone (hR _ mem_sum)
  have hP1 : (accP κ σ (κ.maxK - 1)).ev w = ∑ q ∈ range 21, E (q + 0) * (accL κ σ (κ.maxK - 1) q).ev w := by
    simp [accP, ev_flatMap_range, adW]
  rw [hP1, pkO_ev] at hs
  obtain ⟨a1, da1⟩ := bits_A hone hR (show 1 < 2 by norm_num)
  have hbit : ∀ t < 64, decide (w (aC κ σ 1 (8 + t)) = 1) = decide (t < 21 ∧ (accL κ σ (κ.maxK - 1) t).ev w = 1) := by
    intro t ht
    have := congrArg (fun x => bitF x ⟨t, by omega⟩) hs
    rw [bitF_sumO (v := fun q => (accL κ σ (κ.maxK - 1) q).ev w) (d := 0) (n := 21) (by norm_num)
        (fun q hq => hlb q hq),
      bitF_sumO (v := fun q => w (aC κ σ 1 (8 + q))) (d := 0) (n := 64) (by norm_num)
        (fun q hq => a1 _ (by omega))] at this
    simp only [Nat.sub_zero, Nat.zero_le, true_and, Nat.zero_add] at this
    rw [this]; simp [ht]
  rw [n8_bits]
  rw [nOfBits_congr (g := fun t => decide (t < 21 ∧ (accL κ σ (κ.maxK - 1) t).ev w = 1)) fun t ht => by
    rw [bitN_dec w a1 da1 (by omega), hbit t ht]]
  rw [nOfBits_high (m' := 21) (by norm_num) fun t h1 _ => by simp; omega]
  rw [nOfBits_congr (g := fun t => dv ((accL κ σ (κ.maxK - 1) t).ev w)) fun t ht => by simp [dv, ht]]
  rw [show (21 : ℕ) = adW from rfl, hlv, sum_congr rfl fun i hi => hmval i (mem_range.1 hi),
    ← sum_range_add_sum_Ico _ hkm]
  rw [sum_congr rfl fun i hi => if_pos (mem_range.1 hi), sum_eq_zero fun i hi => if_neg (by
    have := (mem_Ico.1 hi).1; omega), add_zero]

end Sum


end W4
end FR

end G6_FRNodeRows4AggChkS

section G6_FRNodeRows4AskStmt

-- New for `flock-recursive` (PACK-4.4 §1.3 `input`/`stmtOk4`, PK-m7; track IMP): the statement
-- blocks' message ties (rows only; their soundness is `FRNodeRows4AskStmtS`).

/-!
# The statement rows (PK-m7)

Every verifier slot `v` has three statement blocks in H: `hashA` at `stmtB κ + 3v`, `hashB1`,
`hashB2` after it (`N4c.stmtIvs`). Their Z truths hash their message cells, but no row ties the
messages to the slot's stream, so the blocks' outputs say nothing about the slot. These rows tie
them (R-A′: the stream's `stmt` field is element-aligned, elements `13 … 20` of the segment, and is
honestly the padded message blocks `tagLeaf ‖ h ‖ enc64 n ‖ 0^23 ‖ 0^64` or
`tagNode ‖ c₁ ‖ c₂ ‖ 0^63`), so whole-element copies suffice:

* **`stmtRowsS`** (segment slots, gated by the sub-slot's activity `act a i`): `hashA`'s message
  elements `4 … 7` are the segment's stream elements `13 … 16`. `hashA`'s output is then
  `leafStmt h n` of the slot's view: the cells of the slot's `input c` (`FRNodeRows4AskStmtS`).
* **`stmtRowsP`** (the previous node, ungated: slot 0 is always active): `hashB1`'s message is
  elements `13 … 16`, `hashB2`'s elements `17 … 20`, `hashB2.h_in = hashB1.h_out`, and
  `hashB2.h_out` is the public `c₁` (`seedC κ 0 2, 3`). Then `nodeStmt` of the `stmt` field is
  `c₁`: the previous node's `stmtOk4`.

`stmtRows κ act` is folded into slot 1's node rows (`W4.xRowsA`), next to B4's check rows.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c

/-- `one·(x − y) = 0`: cell `x` is cell `y` (with `w one = 1`). -/
def eqRow (one x y : ℕ) : Row := ⟨Lin.cell one, (Lin.cell x).sub (Lin.cell y), []⟩

/-- `g·(x − y) = 0`: where `g` is `1`, cell `x` is cell `y`. -/
def eqRowG (g : Lin) (x y : ℕ) : Row := ⟨g, (Lin.cell x).sub (Lin.cell y), []⟩

/-- **The segment slots' statement rows**: sub-slot `i` of aggregate `a` (slot `sub κ a i`), where
active (`act a i`), has `hashA`'s message element `4 + e` equal to its stream element `13 + e`,
`e < 4`. -/
def stmtRowsS (κ : NodeKind) (act : ℕ → ℕ → Lin) : List Row :=
  (List.range (nAgg κ)).flatMap fun a => (List.range κ.maxK).flatMap fun i =>
    (List.range 4).map fun e =>
      eqRowG (act a i) (hc (stmtB κ + 3 * sub κ a i) (4 + e)) (sE κ (aggChild κ a) i (13 + e))

/-- **The previous node's statement rows** (none without one): `hashB1`'s message is stream
elements `13 … 16`, `hashB2`'s `17 … 20`, `hashB2.h_in = hashB1.h_out`, `hashB2.h_out = c₁`'s cells. -/
def stmtRowsP (κ : NodeKind) : List Row :=
  if κ.hasPrev then
    (List.range 4).map (fun e => eqRow κ.oneCell (hc (stmtB κ + 1) (4 + e)) (sE κ 0 0 (13 + e))) ++
    (List.range 4).map (fun e => eqRow κ.oneCell (hc (stmtB κ + 2) (4 + e)) (sE κ 0 0 (17 + e))) ++
    (List.range 2).map (fun h => eqRow κ.oneCell (hc (stmtB κ + 2) h) (hc (stmtB κ + 1) (2 + h))) ++
    (List.range 2).map (fun h => eqRow κ.oneCell (hc (stmtB κ + 2) (2 + h)) (seedC κ 0 (2 + h)))
  else []

/-- **The `input` cells of a slot region** (M-relative): `inOff + 2j + h` holds half `h` of the
slot's `vk` (`j = 0`) or `c` (`j = 1`), between arena₁ (`< 387,752`) and the bits (`≥ 389,120`). The
`input` ask template (`N4s.AT.inp`) ties the compiled `input` registers' cells to them. -/
def inOff : ℕ := 388096

/-- **The `input` rows** (ungated): every slot's `input` cells are its `vk`'s public cells and its
statement cells — a segment slot's `hashA` output, the previous node's public `c₁`. -/
def inpRows (κ : NodeKind) : List Row :=
  ((List.range (nAgg κ)).flatMap fun a => (List.range κ.maxK).flatMap fun i =>
    (List.range 2).flatMap fun h =>
      [eqRow κ.oneCell (κ.oneCell + sub κ a i * slotM4 + inOff + h) (seedC κ (aggChild κ a) h),
       eqRow κ.oneCell (κ.oneCell + sub κ a i * slotM4 + inOff + 2 + h) (hc (stmtB κ + 3 * sub κ a i) (2 + h))]) ++
  if κ.hasPrev then
    (List.range 2).flatMap fun h =>
      [eqRow κ.oneCell (κ.oneCell + inOff + h) (seedC κ 0 h),
       eqRow κ.oneCell (κ.oneCell + inOff + 2 + h) (seedC κ 0 (2 + h))]
  else []

/-- **The statement and `input` rows** (PK-m7, IMP). -/
def stmtRows (κ : NodeKind) (act : ℕ → ℕ → Lin) : List Row := stmtRowsS κ act ++ stmtRowsP κ ++ inpRows κ

theorem stmtRows_length_le (κ : NodeKind) (act : ℕ → ℕ → Lin) : (stmtRows κ act).length ≤ 80 := by
  cases κ <;> simp [stmtRows, stmtRowsS, stmtRowsP, inpRows, List.length_flatMap, nAgg, NodeKind.maxK,
    NodeKind.hasPrev, NodeKind.segSlots]

theorem eqRow_holds {w : Asg} {one x y : ℕ} (hone : w one = 1) (h : (eqRow one x y).Holds w) : w x = w y := by
  simp only [eqRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil, hone, one_mul] at h
  exact sub_eq_zero.1 h

theorem eqRowG_holds {w : Asg} {g : Lin} {x y : ℕ} (hg : g.ev w = 1) (h : (eqRowG g x y).Holds w) :
    w x = w y := by
  simp only [eqRowG, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil, hg, one_mul] at h
  exact sub_eq_zero.1 h

/-- (±) **The rows' controls**: an inactive slot's row holds whatever its cells (`g = 0`); an
active slot's row with differing cells fails; the ungated row with equal cells holds. -/
theorem eqRow_ctl :
    (eqRowG [] 0 1).Holds (fun i => if i = 0 then 1 else 0) ∧
      ¬ (eqRowG (Lin.cell 2) 0 1).Holds (fun i => if i = 1 then 0 else 1) ∧
      (eqRow 2 0 1).Holds (fun _ => 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [eqRowG, eqRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil]

end W4
end FR

end G6_FRNodeRows4AskStmt

section G6_FRNodeRows4Ext

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4; stage S-E13b, track L-circ).

/-!
# The node rows of S-E13b, as one list per slot (`extRows4`)

S-E13a's link region (`FRNodeRows4.linkRows4 = linkRowsB4 ++ packRows4 ++ …`, the last `2^15` rows
of every slot region) takes the node rows after the pack rows. They all sit at **slot 1** (every
kind has one): both signed children's WOTS rows (`W4.wotsRows`) and every aggregate's `aggPad` rows
(`W4.padRows`), with the aggregates' activities read off the sub-slots' selector copies (`actW`,
equal to `Rev4.selSum` of the sub-slot).

* **`extRows4 κ σ`**: the list (`xRowsA`: with B4's aggregate check rows `chkRows` and IMP's statement
  rows `stmtRows`, PK-m7); empty at every
  slot but 1;
* **`xRows_length`**, **`extRows4_length_le`**: `N2` 7,862, `N4` 7,878, `N8` 7,904 rows (R-A′: `aggPad`
  without the element-7 decompositions), inside the link region after the pack rows.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c

/-- **Sub-slot `i` of aggregate `a`'s activity** `S = Σ_ι s′_ι` (its three selector copies;
`Rev4.selSum κ (sub κ a i)`). -/
def actW (κ : NodeKind) (a i : ℕ) : Lin :=
  (List.range 3).map fun x => (κ.oneCell + (N4c.sub κ a i * slotM4 + 1 + x), (1 : F))

/-- **The node rows**: the signed children's WOTS rows, the aggregates' `aggPad` rows. -/
def xRows (κ : NodeKind) : List Row :=
  wotsRows κ 0 (actW κ (aggOf κ 0)) ++ wotsRows κ 1 (actW κ (aggOf κ 1)) ++
    (List.range (nAgg κ)).flatMap fun a => padRows κ a (actW κ a)

/-- **The aggregates' check rows** (B4, `FRNodeRows4AggChk`): every aggregate's, with its sub-slots'
activities. -/
def chkRows (κ : NodeKind) : List Row := (List.range (nAgg κ)).flatMap fun a => aggRowsC κ a (actW κ a)

/-- **The node rows with the aggregates' checks and the statement rows** (B4, IMP): S-E13b's, then
`chkRows`, then `stmtRows` (PK-m7, `FRNodeRows4AskStmt`). -/
def xRowsA (κ : NodeKind) : List Row := xRows κ ++ (chkRows κ ++ stmtRows κ (actW κ))

/-- **Slot `σ`'s node rows** (S-E13b, B4): the node rows at slot 1, none elsewhere. -/
def extRows4 (κ : NodeKind) (σ : ℕ) : List Row := if σ = 1 then xRowsA κ else []

/-- **The node rows' count**: `N2` 7,862, `N4` 7,878, `N8` 7,904 (per child 3,926 for a previous node,
`3,924 + 2·maxK + 2` for an aggregate; `aggPad` `6·(maxK − 1)` per aggregate). -/
theorem xRows_length : (xRows .N2).length = 7862 ∧ (xRows .N4).length = 7878 ∧ (xRows .N8).length = 7904 := by
  simp [xRows, wotsRows, idxRows, selRows, chainRows, chainRowsI, leafRows, pathRows, pathRowsT, rootRows,
    digRows, sumRows, padRows, List.length_flatMap, NodeKind.maxK, N4c.nAgg, NodeKind.hasPrev,
    N4c.isAgg, N4c.aggChild, NodeKind.segSlots, RecursionFast.wotsLen, RecursionFast.sigHeight, N4c.aggOf]

theorem chkRows_length_le (κ : NodeKind) : (chkRows κ).length ≤ 4152 := by
  have hn : nAgg κ ≤ 2 := by cases κ <;> decide
  rw [chkRows, List.length_flatMap]
  refine le_trans (List.sum_le_length_nsmul _ 2076 fun x hx => ?_) (by simp; omega)
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  exact aggRowsC_length_le κ a _

/-- **They fit S-E13a's link region** after its rows (`2^15 − 8 − 8,919 = 23,841`): S-E13b's
at most 7,904, B4's at most 4,152, IMP's statement and `input` rows at most 80. -/
theorem extRows4_length_le (κ : NodeKind) (σ : ℕ) : (extRows4 κ σ).length ≤ 12136 := by
  unfold extRows4
  split_ifs
  · obtain ⟨h2, h4, h8⟩ := xRows_length
    have := chkRows_length_le κ
    have := stmtRows_length_le κ (actW κ)
    rw [xRowsA, List.length_append, List.length_append]
    cases κ <;> omega
  · simp

end W4
end FR

end G6_FRNodeRows4Ext
