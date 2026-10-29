-- New for `flock-recursive` (PACK-4.4.1 §4.3, §6.1, the B4 row of §7; stage B4, track L-circ).
import FRNodeRows4Wots
import FRNodeRows4Pack

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
