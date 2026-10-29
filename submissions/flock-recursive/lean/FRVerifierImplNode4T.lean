-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8 `targetS` on a node; stage S-CN4b). 3.x
-- template: `FRVerifierImplNode` (`pfx`, `twoF`, `sepSum`, `tabs`, `rangeI`, `ctrI`, `clsTab`,
-- `gArr`, `targetSNodeI`, `targetSNode_meets`), ported from base 256 to base 512.
import FRNodeTarget4C
import FRVerifierImplNode4

/-!
# The revision 4.1 node's `targetS`, computed (`targetSNode4I`), and `implN4` with it

* **Base-512 two-level tables.** `eq(r_blk, x) = A[x mod 512] · B[⌊x/512⌋]` (S-CN4's `bt`: `A` the
  `eq` table of the low 9 block coordinates, `B` of the high `nb − 9`), with prefix arrays over 512
  entries (`pfx9`, additions only). A separable weight `R(⌊x/512⌋) · C(x mod 512)` summed over a
  block range costs four products (`twoF9_eq`, `sepSum9_eq`): every range sum of `eq(r_blk, ·)`
  (`rangeI9`). The stream counters (`ctrK`, `ctrArr`): bit `j < 9` of the counter is a mask on
  the columns, bit `j ≥ 9` a mask on the rows split by the column carry; one pass over the columns
  (`col3`) and the range's rows summed directly (`sepD`), the carry classes shared by every `j`.
* **`targetSNode4I ν r`**: `Gc4`'s ten class weights (`clsW` at `eq9`/`rangeI9`), the counter bits
  of the stream bodies (`ctrArr`, `ctrG`) and of the final blocks (`finG`), `w43`'s step fields,
  then `G` at the 1,153 pinned positions (`gArr4`) and `Σ_{hi<19} eq(r_lo, hi) G(σ + 64 hi)`.
  **`targetSNode4_meets`**: it is `targetSNode4S`.
* **`implN4T base ν = implN4 base targetSNode4I ν`** and **`implN4T_meets`**, without the `tS`
  hypothesis.
-/

namespace FR
namespace NI4T
open Finset RecursionFast Rev4 Impl NodeT NT4 NT4C NI4 FR.Stream

/-! ## Base-512 prefix sums -/

/-- The 513 prefix sums of `g` on `0 … 511`. -/
def pfx9 (g : ℕ → F) : Array F := (NodeI.pfxAux g 512).1

theorem pfxAux_getD (g : ℕ → F) (k : ℕ) {i : ℕ} (hi : i ≤ k) :
    (NodeI.pfxAux g k).1.getD i 0 = ∑ l ∈ range i, g l := by
  rw [NodeI.pfxAux_eq, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    dif_pos (Nat.lt_succ_of_le hi), Option.getD_some]

theorem pfx9_getD (g : ℕ → F) {i : ℕ} (hi : i ≤ 512) :
    (pfx9 g).getD i 0 = ∑ l ∈ range i, g l := pfxAux_getD g 512 hi

/-- `Σ_{x<X} R(⌊x/512⌋) C(x mod 512)` from the prefix arrays `PR`, `PC`. -/
def twoF9 (PR : Array F) (R : ℕ → F) (PC : Array F) (X : ℕ) : F :=
  PR.getD (X / 512) 0 * PC.getD 512 0 + R (X / 512) * PC.getD (X % 512) 0

theorem twoF9_eq (R C : ℕ → F) {X : ℕ} (hX : X ≤ 2 ^ 18) :
    twoF9 (pfx9 R) R (pfx9 C) X = ∑ x ∈ range X, R (x / 512) * C (x % 512) := by
  have hh : X / 512 ≤ 512 := by omega
  have hl : X % 512 ≤ 512 := by omega
  unfold twoF9
  rw [pfx9_getD _ hh, pfx9_getD _ le_rfl, pfx9_getD _ hl]
  conv_rhs => rw [← Nat.div_add_mod X 512, Finset.sum_range_add, mul_comm 512, sum_range_mul]
  rw [Finset.sum_mul]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (h * 512 + k) / 512 = h by omega, show (h * 512 + k) % 512 = k by omega]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (X / 512 * 512 + k) / 512 = X / 512 by omega,
      show (X / 512 * 512 + k) % 512 = k by omega]

/-- **A separable weight over a block range**: `Σ_{k<n} R(⌊(lo+k)/512⌋) C((lo+k) mod 512)`. -/
def sepSum9 (PR : Array F) (R : ℕ → F) (PC : Array F) (lo n : ℕ) : F :=
  twoF9 PR R PC (lo + n) - twoF9 PR R PC lo

theorem sepSum9_eq (R C : ℕ → F) {lo n : ℕ} (h : lo + n ≤ 2 ^ 18) :
    sepSum9 (pfx9 R) R (pfx9 C) lo n =
      ∑ k ∈ range n, R ((lo + k) / 512) * C ((lo + k) % 512) := by
  rw [sepSum9, twoF9_eq R C h, twoF9_eq R C (by omega), Finset.sum_range_add, add_sub_cancel_left]

/-! ## The block point's tables -/

/-- The tables of an `n`-coordinate block point (`bt`) and their prefix arrays. -/
def tabs9 (n : ℕ) (a : Array F) : NodeI.Tabs :=
  let T := bt n a
  ⟨T.A, T.B, pfx9 fun l => T.A.getD l 0, pfx9 fun h => T.B.getD h 0⟩

/-- `eq(r_blk, x)` from the tables (one product). -/
def eq9 (T : NodeI.Tabs) (x : ℕ) : F := T.a (x % 512) * T.b (x / 512)

/-- `Σ_{k<n} eq(r_blk, lo + k)` (four products). -/
def rangeI9 (T : NodeI.Tabs) (lo n : ℕ) : F := sepSum9 T.PB T.b T.PA lo n

section TabsLemmas
variable {n : ℕ} (a : Array F)

theorem tabs9_a (l : ℕ) : (tabs9 n a).a l = (bt n a).A.getD l 0 := by simp only [tabs9, NodeI.Tabs.a]
theorem tabs9_b (h : ℕ) : (tabs9 n a).b h = (bt n a).B.getD h 0 := by simp only [tabs9, NodeI.Tabs.b]
theorem tabs9_PA : (tabs9 n a).PA = pfx9 fun l => (tabs9 n a).a l := by
  simp only [tabs9, NodeI.Tabs.a]
theorem tabs9_PB : (tabs9 n a).PB = pfx9 fun h => (tabs9 n a).b h := by
  simp only [tabs9, NodeI.Tabs.b]

variable (hn : 9 ≤ n)
include hn

theorem eq9_eq {x : ℕ} (hx : x < 2 ^ n) : eq9 (tabs9 n a) x = eqAtR (ptA n a) x := by
  rw [eq9, tabs9_a, tabs9_b, ← bt_eq hn a hx, BT.eq]

theorem ba9_eq {x : ℕ} (hx : x < 2 ^ n) :
    (tabs9 n a).b (x / 512) * (tabs9 n a).a (x % 512) = eqAtR (ptA n a) x := by
  rw [← eq9_eq a hn hx, eq9, mul_comm]

theorem rangeI9_eq (hn' : n ≤ 18) {lo m : ℕ} (h : lo + m ≤ 2 ^ n) :
    rangeI9 (tabs9 n a) lo m = ∑ k ∈ range m, eqAtR (ptA n a) (lo + k) := by
  have h18 : 2 ^ n ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn'
  rw [rangeI9, tabs9_PA, tabs9_PB, sepSum9_eq _ _ (by omega)]
  exact Finset.sum_congr rfl fun k hk => ba9_eq a hn (by have := Finset.mem_range.1 hk; omega)

end TabsLemmas

/-! ## The stream counters -/

/-- One pass over the 512 columns, cut at `l₀` and `l₁`:
`(Σ_{l<512} C l, Σ_{l<l₀} C l, Σ_{l<l₁} C l)`. -/
def colT (C : ℕ → F) (l0 l1 : ℕ) : F × F × F :=
  let a := min l0 l1
  let b := max l0 l1
  let s1 := sumTo a C
  let s2 := sumTo (b - a) fun i => C (a + i)
  let s3 := sumTo (512 - b) fun i => C (b + i)
  (s1 + s2 + s3, if l0 ≤ l1 then s1 else s1 + s2, if l0 ≤ l1 then s1 + s2 else s1)

theorem colT_eq (C : ℕ → F) {l0 l1 : ℕ} (h0 : l0 ≤ 512) (h1 : l1 ≤ 512) : colT C l0 l1 =
    (∑ l ∈ range 512, C l, ∑ l ∈ range l0, C l, ∑ l ∈ range l1, C l) := by
  have e1 := Finset.sum_range_add C (min l0 l1) (max l0 l1 - min l0 l1)
  have e2 := Finset.sum_range_add C (max l0 l1) (512 - max l0 l1)
  rw [show min l0 l1 + (max l0 l1 - min l0 l1) = max l0 l1 by omega] at e1
  rw [show max l0 l1 + (512 - max l0 l1) = 512 by omega] at e2
  simp only [colT, sumTo_eq]
  refine Prod.ext (by rw [e2, e1]) (Prod.ext ?_ ?_) <;> dsimp only <;> split_ifs with h
  · rw [show min l0 l1 = l0 by omega]
  · rw [← e1, show max l0 l1 = l0 by omega]
  · rw [← e1, show max l0 l1 = l1 by omega]
  · rw [show min l0 l1 = l1 by omega]

/-- **A separable weight over a block range** from its row weight `R` and the column sums
`t = (Σ_{l<512} C, Σ_{l<lo mod 512} C, Σ_{l<(lo+n) mod 512} C)`: the rows of the range are summed
directly (no prefix array). -/
def sepD (R : ℕ → F) (t : F × F × F) (lo n : ℕ) : F :=
  (sumTo ((lo + n) / 512 - lo / 512) fun i => R (lo / 512 + i)) * t.1 +
    R ((lo + n) / 512) * t.2.2 - R (lo / 512) * t.2.1

theorem twoG_eq (R C : ℕ → F) (X : ℕ) :
    (∑ h ∈ range (X / 512), R h) * (∑ l ∈ range 512, C l) + R (X / 512) * ∑ l ∈ range (X % 512), C l =
      ∑ x ∈ range X, R (x / 512) * C (x % 512) := by
  conv_rhs => rw [← Nat.div_add_mod X 512, Finset.sum_range_add, mul_comm 512, sum_range_mul]
  rw [Finset.sum_mul]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (h * 512 + k) / 512 = h by omega, show (h * 512 + k) % 512 = k by omega]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (X / 512 * 512 + k) / 512 = X / 512 by omega,
      show (X / 512 * 512 + k) % 512 = k by omega]

theorem sepD_eq (R C : ℕ → F) (lo n : ℕ) :
    sepD R (colT C (lo % 512) ((lo + n) % 512)) lo n =
      ∑ k ∈ range n, R ((lo + k) / 512) * C ((lo + k) % 512) := by
  have e := Finset.sum_range_add (fun x => R (x / 512) * C (x % 512)) lo n
  rw [← twoG_eq, ← twoG_eq] at e
  rw [sepD, colT_eq _ (by omega) (by omega), sumTo_eq]
  dsimp only
  have e2 := Finset.sum_range_add R (lo / 512) ((lo + n) / 512 - lo / 512)
  rw [show lo / 512 + ((lo + n) / 512 - lo / 512) = (lo + n) / 512 by
    have : lo / 512 ≤ (lo + n) / 512 := Nat.div_le_div_right (by omega); omega] at e2
  rw [e2] at e
  linear_combination e

/-- The column factor of a body's counter bit `j ≥ 9`: no carry (`b = false`) or a carry out of the
column (`b = true`) for the column offset `d`. -/
def cc (T : NodeI.Tabs) (d : ℕ) (b : Bool) (l : ℕ) : F :=
  if b then (if l + d < 512 then 0 else T.a l) else (if l + d < 512 then T.a l else 0)

/-- The counter's column offset for a body starting at `lo` (`k + 2 = (lo + k) + e − 512 Q`). -/
def eOf (lo : ℕ) : ℕ := 512 * ((lo + 509) / 512) + 2 - lo

/-- **The counter bit `j` of a stream body** `Σ_{k<n} eq(r_blk, lo + k) · bit_j(k + 2)` (3.x's
`ctrI` at base 512): bit `j < 9` is a mask on the columns; bit `j ≥ 9` a mask on the rows, split
by the column carry (`t0`, `t1`: the carry classes' column sums, shared by every `j`); `0` once
`2^j > n + 1`. -/
def ctrK (T : NodeI.Tabs) (lo n : ℕ) (t0 t1 : F × F × F) (j : ℕ) : F :=
  if n + 1 < 2 ^ j then 0 else
  let Q := (lo + 509) / 512
  let e := eOf lo
  if j < 9 then
    sepD T.b (colT (fun l => if ((l + e % 512) % 512).testBit j then T.a l else 0)
      (lo % 512) ((lo + n) % 512)) lo n
  else
    sepD (fun h => if (h + e / 512 - Q).testBit (j - 9) then T.b h else 0) t0 lo n +
      sepD (fun h => if (h + e / 512 + 1 - Q).testBit (j - 9) then T.b h else 0) t1 lo n

/-- **A body's 26 counter bits** (`t_lo`'s bits `6 … 31` of `64 (k + 2)`): a short body
(`n < 512`, a key leaf) directly from its `eq` values; a long one (a chain) by `ctrK`, the carry
classes' column sums computed once. -/
def ctrArr (T : NodeI.Tabs) (lo n : ℕ) : Array F :=
  if n < 512 then
    let E := Array.ofFn (n := n) fun k => eq9 T (lo + k)
    Array.ofFn (n := 26) fun j => sumTo n fun k => if (k + 2).testBit j then E.getD k 0 else 0
  else
    let d := eOf lo % 512
    let t0 := colT (cc T d false) (lo % 512) ((lo + n) % 512)
    let t1 := colT (cc T d true) (lo % 512) ((lo + n) % 512)
    Array.ofFn (n := 26) fun j => ctrK T lo n t0 t1 j

theorem ctrK_eq {nb : ℕ} (hn : 9 ≤ nb) (a : Array F) {lo n : ℕ} (h : lo + n ≤ 2 ^ nb) (j : ℕ) :
    ctrK (tabs9 nb a) lo n (colT (cc (tabs9 nb a) (eOf lo % 512) false) (lo % 512) ((lo + n) % 512))
      (colT (cc (tabs9 nb a) (eOf lo % 512) true) (lo % 512) ((lo + n) % 512)) j =
      ∑ k ∈ range n, eqAtR (ptA nb a) (lo + k) * bF ((k + 2).testBit j) := by
  unfold ctrK eOf
  split_ifs with hj hj9
  · refine (Finset.sum_eq_zero fun k hk => ?_).symm
    have := Finset.mem_range.1 hk
    rw [Nat.testBit_lt_two_pow (by omega)]
    simp [bF]
  · rw [sepD_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hb : (k + 2).testBit j = (((lo + k) % 512 + (512 * ((lo + 509) / 512) + 2 - lo) % 512)
        % 512).testBit j := by
      rw [show ((lo + k) % 512 + (512 * ((lo + 509) / 512) + 2 - lo) % 512) % 512 =
        (k + 2) % 2 ^ 9 by omega, Nat.testBit_mod_two_pow]
      simp [hj9]
    rw [hb, ← ba9_eq a hn (show lo + k < 2 ^ nb by omega)]
    unfold bF
    split_ifs <;> ring
  · dsimp only
    rw [sepD_eq, sepD_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [← ba9_eq a hn (show lo + k < 2 ^ nb by omega)]
    have hb : (k + 2).testBit j = ((k + 2) / 2 ^ 9).testBit (j - 9) := by
      rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]
    unfold cc
    by_cases hc : (lo + k) % 512 + (512 * ((lo + 509) / 512) + 2 - lo) % 512 < 512
    · rw [hb, show (k + 2) / 2 ^ 9 = (lo + k) / 512 + (512 * ((lo + 509) / 512) + 2 - lo) / 512 -
        (lo + 509) / 512 by omega]
      simp only [hc, ite_true, ite_false, mul_zero, add_zero, Bool.false_eq_true]
      unfold bF
      split_ifs <;> ring
    · rw [hb, show (k + 2) / 2 ^ 9 = (lo + k) / 512 + (512 * ((lo + 509) / 512) + 2 - lo) / 512 +
        1 - (lo + 509) / 512 by omega]
      simp only [hc, ite_true, ite_false, mul_zero, zero_add, Bool.false_eq_true]
      unfold bF
      split_ifs <;> ring

theorem ctrArr_eq {nb : ℕ} (hn : 9 ≤ nb) (a : Array F) {lo n : ℕ} (h : lo + n ≤ 2 ^ nb) {j : ℕ}
    (hj : j < 26) : (ctrArr (tabs9 nb a) lo n).getD j 0 =
      ∑ k ∈ range n, eqAtR (ptA nb a) (lo + k) * bF ((k + 2).testBit j) := by
  rw [ctrArr]
  split_ifs with hn5
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hj, Option.getD_some, sumTo_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hk', Option.getD_some,
      eq9_eq a hn (by omega), bF]
    split_ifs <;> simp
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hj, Option.getD_some]
    exact ctrK_eq hn a h j

/-! ## `targetSNode4I` -/

/-- The ten classes' pinned bits at the positions `0 … 1152` (computed once). -/
def clsTab4 : Array (Array Bool) :=
  Array.ofFn (n := 10) fun c => Array.ofFn (n := 1153) fun p =>
    cls4 c (ProductCircuit.pos p) == some true

/-- Class `c`'s bit at `p`. -/
def clsBit4 (c p : ℕ) : Bool := (clsTab4.getD c #[]).getD p false

theorem clsBit4_eq {c p : ℕ} (hc : c < 10) (hp : p < 1153) (x : F) :
    (if clsBit4 c p then x else 0) = x * tgtE (cls4 c) p := by
  have : clsBit4 c p = (cls4 c (ProductCircuit.pos p) == some true) := by
    simp [clsBit4, clsTab4, Array.getD_eq_getD_getElem?, hc, hp]
  rw [this, tgtE, bF]
  split_ifs <;> simp

/-- `G(p)` from the class weights `W`, the bodies' counter bits `CT` (positions `1030 … 1055`),
the final blocks' counter bits `FB` (`1024 … 1055`), `w43`'s `i`, `s` bits. -/
def gAt4 (W CT FB WI WS : Array F) (p : ℕ) : F :=
  (if clsBit4 0 p then W.getD 0 0 else 0) + (if clsBit4 1 p then W.getD 1 0 else 0) +
    (if clsBit4 2 p then W.getD 2 0 else 0) + (if clsBit4 3 p then W.getD 3 0 else 0) +
    (if clsBit4 4 p then W.getD 4 0 else 0) + (if clsBit4 5 p then W.getD 5 0 else 0) +
    (if clsBit4 6 p then W.getD 6 0 else 0) + (if clsBit4 7 p then W.getD 7 0 else 0) +
    (if clsBit4 8 p then W.getD 8 0 else 0) + (if clsBit4 9 p then W.getD 9 0 else 0) +
    (if 1030 ≤ p ∧ p < 1056 then CT.getD (p - 1030) 0 else 0) +
    (if 1024 ≤ p ∧ p < 1056 then FB.getD (p - 1024) 0 else 0) +
    (if 584 ≤ p ∧ p < 592 then WI.getD (p - 584) 0 else 0) +
    (if 592 ≤ p ∧ p < 600 then WS.getD (p - 592) 0 else 0)

/-- **`G` at the 1,153 pinned positions** (the rest is `0`). -/
def gArr4 (ν : NodeKind) (T : NodeI.Tabs) : Array F :=
  let W := Array.ofFn (n := 10) fun c => clsW ν (eq9 T) (rangeI9 T) c
  let KA := ctrArr T (N4c.chBase ν 0 + 1) (N4c.chLen ν 0 - 2)
  let KB := ctrArr T (N4c.chBase ν 1 + 1) (N4c.chLen ν 1 - 2)
  let KC := ctrArr T (N4c.wotsB ν 0 + 400) 65
  let KD := ctrArr T (N4c.wotsB ν 1 + 400) 65
  let CT := Array.ofFn (n := 26) fun j =>
    KA.getD j 0 + KB.getD j 0 + (KC.getD j 0 + KD.getD j 0)
  let FB := Array.ofFn (n := 32) fun j => finG ν (eq9 T) j
  let E0 := Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 0 + o)
  let E1 := Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 1 + o)
  let WI := Array.ofFn (n := 8) fun b => NodeI.w43I E0 (· / 3) b + NodeI.w43I E1 (· / 3) b
  let WS := Array.ofFn (n := 8) fun b => NodeI.w43I E0 (· % 3) b + NodeI.w43I E1 (· % 3) b
  Array.ofFn (n := 1153) fun p => gAt4 W CT FB WI WS p

/-- The block coordinates of `targetS`'s operand as an array (`r[1 … nb]`). -/
def rbArr (ν : NodeKind) (r : Array F) : Array F := Array.ofFn (n := nbN ν) (rbOf4 ν r)

/-- **`targetS` of a revision 4.1 node** (A.8), computed: `Σ_{hi<19} eq(r_lo, hi) G(σ + 64 hi)`. -/
def targetSNode4I (ν : NodeKind) (r : Array F) : Array F :=
  let G := gArr4 ν (tabs9 (nbN ν) (rbArr ν r))
  let H := eqTable (List.ofFn (zLo r))
  Array.ofFn (n := 64) fun σ => sumTo 19 fun hi => H.getD hi 0 * G.getD (σ + 64 * hi) 0

section Meets

theorem ite_getD {n i : ℕ} (c : Prop) [Decidable c] (h : c → i < n) (g : Fin n → F) (v : F)
    (hv : ∀ hi : i < n, g ⟨i, hi⟩ = v) :
    (if c then (Array.ofFn g).getD i 0 else 0) = if c then v else 0 := by
  split_ifs with hc
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos (h hc), Option.getD_some, hv]
  · rfl

private theorem sum_two (g : ℕ → F) : ∑ σ ∈ range 2, g σ = g 0 + g 1 := by
  simp [Finset.sum_range_succ]

/-- `w43`'s step sums from the `e` arrays are `stepG` at `eq9`. -/
theorem w43_eq (ν : NodeKind) (T : NodeI.Tabs) (sel : ℕ → ℕ) (b : ℕ) :
    NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 0 + o)) sel b +
      NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 1 + o)) sel b =
      stepG ν (eq9 T) sel b := by
  have h : ∀ σ, NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν σ + o)) sel b =
      sumTo 399 fun o => eq9 T (N4c.wotsB ν σ + o) * bF ((sel o).testBit b) := fun σ => by
    simp only [NodeI.w43I, sumTo_eq]
    refine Finset.sum_congr rfl fun o ho => ?_
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos (Finset.mem_range.1 ho),
      Option.getD_some, bF]
    split_ifs <;> simp
  rw [h, h, stepG]
  simp only [sumTo_eq, sum_two]

/-- **`G`, computed, is the closed form** at every pinned position. -/
theorem gArr4_eq (ν : NodeKind) (a : Array F) {p : ℕ} (hp : p < 1153) :
    (gArr4 ν (tabs9 (nbN ν) a)).getD p 0 = Gc4 ν (eqAtR (ptA (nbN ν) a)) p := by
  obtain ⟨hn9, hn18⟩ := nbN_bounds ν
  have hE := (lay_bounds ν).2.2.2.2
  have hpt : ∀ x < N4c.hEnd ν, eq9 (tabs9 (nbN ν) a) x = eqAtR (ptA (nbN ν) a) x :=
    fun x hx => eq9_eq a hn9 (by omega)
  have hrng : ∀ lo n, lo + n ≤ N4c.hEnd ν →
      rangeI9 (tabs9 (nbN ν) a) lo n = rngS (eqAtR (ptA (nbN ν) a)) lo n :=
    fun lo n h => rangeI9_eq a hn9 hn18 (by omega)
  have hct : ∀ j < 26, (ctrArr (tabs9 (nbN ν) a) (N4c.chBase ν 0 + 1) (N4c.chLen ν 0 - 2)).getD j 0 +
      (ctrArr (tabs9 (nbN ν) a) (N4c.chBase ν 1 + 1) (N4c.chLen ν 1 - 2)).getD j 0 +
      ((ctrArr (tabs9 (nbN ν) a) (N4c.wotsB ν 0 + 400) 65).getD j 0 +
        (ctrArr (tabs9 (nbN ν) a) (N4c.wotsB ν 1 + 400) 65).getD j 0) =
      ctrG ν (ctrS (eqAtR (ptA (nbN ν) a))) j := fun j hj => by
    obtain ⟨b1, -, b3, -, -⟩ := lay_bounds ν
    have c0 := (chain_facts ν (σ := 0) (by norm_num)).2.1
    have c1 := (chain_facts ν (σ := 1) (by norm_num)).2.1
    have := b1 0 (by norm_num); have := b1 1 (by norm_num)
    have := b3 0 (by norm_num); have := b3 1 (by norm_num)
    rw [ctrArr_eq hn9 a (by omega) hj, ctrArr_eq hn9 a (by omega) hj, ctrArr_eq hn9 a (by omega) hj,
      ctrArr_eq hn9 a (by omega) hj, ctrG, sumTo_eq, sumTo_eq, sum_two, sum_two]
    rfl
  have hW : ∀ c (hc : c < 10), (Array.ofFn (n := 10) fun c =>
      clsW ν (eq9 (tabs9 (nbN ν) a)) (rangeI9 (tabs9 (nbN ν) a)) c).getD c 0 =
      clsW ν (eqAtR (ptA (nbN ν) a)) (rngS (eqAtR (ptA (nbN ν) a))) c := fun c hc => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hc, Option.getD_some]
    exact clsW_congr ν hpt hrng c
  simp only [gArr4]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hp, Option.getD_some]
  unfold gAt4 Gc4
  rw [clsBit4_eq (c := 0) (by norm_num) hp, clsBit4_eq (c := 1) (by norm_num) hp,
    clsBit4_eq (c := 2) (by norm_num) hp, clsBit4_eq (c := 3) (by norm_num) hp,
    clsBit4_eq (c := 4) (by norm_num) hp, clsBit4_eq (c := 5) (by norm_num) hp,
    clsBit4_eq (c := 6) (by norm_num) hp, clsBit4_eq (c := 7) (by norm_num) hp,
    clsBit4_eq (c := 8) (by norm_num) hp, clsBit4_eq (c := 9) (by norm_num) hp,
    hW 0 (by norm_num), hW 1 (by norm_num), hW 2 (by norm_num), hW 3 (by norm_num),
    hW 4 (by norm_num), hW 5 (by norm_num), hW 6 (by norm_num), hW 7 (by norm_num),
    hW 8 (by norm_num), hW 9 (by norm_num),
    ite_getD (1030 ≤ p ∧ p < 1056) (fun _ => by omega)
      (fun j : Fin 26 => (ctrArr (tabs9 (nbN ν) a) (N4c.chBase ν 0 + 1) (N4c.chLen ν 0 - 2)).getD j 0 +
        (ctrArr (tabs9 (nbN ν) a) (N4c.chBase ν 1 + 1) (N4c.chLen ν 1 - 2)).getD j 0 +
        ((ctrArr (tabs9 (nbN ν) a) (N4c.wotsB ν 0 + 400) 65).getD j 0 +
          (ctrArr (tabs9 (nbN ν) a) (N4c.wotsB ν 1 + 400) 65).getD j 0))
      (ctrG ν (ctrS (eqAtR (ptA (nbN ν) a))) (p - 1030)) (fun hi => hct _ hi),
    ite_getD (1024 ≤ p ∧ p < 1056) (fun _ => by omega)
      (fun j : Fin 32 => finG ν (eq9 (tabs9 (nbN ν) a)) j)
      (finG ν (eq9 (tabs9 (nbN ν) a)) (p - 1024)) (fun _ => rfl),
    ite_getD (584 ≤ p ∧ p < 592) (fun _ => by omega)
      (fun b : Fin 8 => NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 (tabs9 (nbN ν) a)
          (N4c.wotsB ν 0 + o)) (· / 3) b +
        NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 (tabs9 (nbN ν) a) (N4c.wotsB ν 1 + o))
          (· / 3) b)
      (stepG ν (eq9 (tabs9 (nbN ν) a)) (· / 3) (p - 584)) (fun _ => w43_eq ν _ _ _),
    ite_getD (592 ≤ p ∧ p < 600) (fun _ => by omega)
      (fun b : Fin 8 => NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 (tabs9 (nbN ν) a)
          (N4c.wotsB ν 0 + o)) (· % 3) b +
        NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 (tabs9 (nbN ν) a) (N4c.wotsB ν 1 + o))
          (· % 3) b)
      (stepG ν (eq9 (tabs9 (nbN ν) a)) (· % 3) (p - 592)) (fun _ => w43_eq ν _ _ _),
    finG_congr ν hpt, stepG_congr ν hpt, stepG_congr ν hpt]

/-- **`targetS` meets the revision 4.1 node's specification.** -/
theorem targetSNode4_meets (ν : NodeKind) (r : Array F) : targetSNode4I ν r = targetSNode4S ν r := by
  rw [targetS_node4_eq]
  unfold targetSNode4I
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  have hσ := σ.isLt
  rw [sumTo_eq]
  refine Finset.sum_congr rfl fun hi hh => ?_
  have hh' := Finset.mem_range.1 hh
  rw [eqTable_ofFn_getD _ (show hi < 2 ^ 8 by omega)]
  refine congrArg (eqAtR (zLo r) hi * ·) ?_
  by_cases hq : σ.val + 64 * hi < 1153
  · rw [gArr4_eq ν _ hq, rbArr, NodeI.ptA_ofFn]
  · rw [Gc4_hi _ _ (by omega) (by omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simp only [gArr4, Array.size_ofFn]; omega)]
    rfl

end Meets

/-! ## The node's op implementation with `targetSNode4I` -/

/-- **`implN4T base ν`**: S-CN4's `implN4` with the computed `targetS`. -/
def implN4T (base : NodeKind → OpImpl) (ν : NodeKind) : OpImpl :=
  implN4 base (fun ν => targetSNode4I ν) ν

/-- **`implN4T ⊨ specN4`**, given the base's ops only. -/
theorem implN4T_meets {base : NodeKind → OpImpl} {spec : NodeKind → OpSpec} (ν : NodeKind)
    (h : (base ν).Meets (spec ν)) : (implN4T base ν).Meets (specN4 spec ν) :=
  implN4_meets ν h fun r => targetSNode4_meets ν r

/-! ## Controls -/

section Controls

/-- At a Boolean block point the block sum reads the block's target: `G(p) = E(b, p)`. -/
theorem blkW4_cube (ν : NodeKind) {b : ℕ} (hb : b < 2 ^ nbN ν) (p : ℕ) :
    blkW4 ν (eqAtR (cubeN (nbN ν) b)) p = nodeE4 ν b p := by
  unfold blkW4
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_range.2 hb) fun x hx hne => by
    rw [eqAtR_cubeN hb (Finset.mem_range.1 hx), if_neg hne, zero_mul]]
  rw [eqAtR_cubeN hb hb, if_pos rfl, one_mul]

/-- (+) **At a Boolean block point `b` the node's `targetS` reads block `b`'s target.** -/
theorem targetSNode4I_blk (ν : NodeKind) (r : Array F) {b : ℕ} (hr : rbOf4 ν r = cubeN (nbN ν) b)
    (hb : b < 2 ^ nbN ν) : targetSNode4I ν r = Array.ofFn (n := 64) fun σ =>
      ∑ hi ∈ range 256, eqAtR (zLo r) hi * nodeE4 ν b (σ + 64 * hi) := by
  rw [targetSNode4_meets, targetSNode4_blk, hr]
  exact congrArg (Array.ofFn (n := 64)) (funext fun σ => Finset.sum_congr rfl fun hi _ => by
    rw [blkW4_cube ν hb])

/-- A block of an interval of the layout reads the interval's target. -/
theorem nodeE4_of_mem {ν : NodeKind} {iv : N4c.TIv} (h : iv ∈ N4c.nodeLayout4 ν) {blk : ℕ}
    (hk : iv.mem blk = true) (p : ℕ) : nodeE4 ν blk p = tF (iv.tgt (blk - iv.lo)) p := by
  rw [nodeE4_tF, N4c.tgt_of_mem h hk]

/-- (−) **At a `free` block point past `hEnd` the node's `targetS` is zero.** -/
theorem targetSNode4I_free (ν : NodeKind) (r : Array F) {b : ℕ} (hr : rbOf4 ν r = cubeN (nbN ν) b)
    (h1 : N4c.hEnd ν ≤ b) (hb : b < 2 ^ nbN ν) :
    targetSNode4I ν r = Array.ofFn (n := 64) fun _ => 0 := by
  have hm : N4c.freeIv (N4c.hEnd ν) ν.blocks ∈ N4c.nodeLayout4 ν := by
    simp only [N4c.nodeLayout4, List.mem_append, List.mem_singleton, or_true]
  have hk : (N4c.freeIv (N4c.hEnd ν) ν.blocks).mem b = true := by
    simp only [N4c.TIv.mem, N4c.freeIv, Bool.and_eq_true]
    exact ⟨decide_eq_true h1, decide_eq_true hb⟩
  rw [targetSNode4I_blk ν r hr hb]
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => Finset.sum_eq_zero fun hi _ => ?_)
  rw [nodeE4_of_mem hm hk]
  show eqAtR (zLo r) hi * tF none _ = 0
  rw [tF, mul_zero]

/-- The target bit of a stream block as a Boolean (`tgtE = bF ∘ ·`). -/
theorem tgtE_bit (t : Block.Target) (p : ℕ) :
    tgtE t p = bF (t (ProductCircuit.pos p) == some true) := rfl

/-- (+/−) **The bits on `N4`**: chain 0's block 1 (counter `128`) reads `t_lo` bit 7 as `1` and
bit 6 as `0`; chain 1's last block (final, `t = aggB 4 = 64 · 96,950`, R-A′'s whole blocks) reads
bit 7 and the final flag as `1` and bit 0 as `0`, its second-to-last block reads the flag as `0`; the tail's candidate `F_{0,1}` (final,
`t = aggB 1 = 0x17AB00`, revision 4.4.2, RSV2) reads the flag and bit 13 as `1`, bit 12 as `0`. -/
theorem nodeE4_ctrl :
    nodeE4 .N4 1 1031 = 1 ∧ nodeE4 .N4 1 1030 = 0 ∧
    nodeE4 .N4 (lastB .N4 1) 1031 = 1 ∧ nodeE4 .N4 (lastB .N4 1) 1024 = 0 ∧
    nodeE4 .N4 (lastB .N4 1) 1088 = 1 ∧
    nodeE4 .N4 (lastB .N4 1 - 1) 1088 = 0 ∧
    nodeE4 .N4 (N4c.finB .N4 0) 1088 = 1 ∧ nodeE4 .N4 (N4c.finB .N4 0) 1037 = 1 ∧
    nodeE4 .N4 (N4c.finB .N4 0) 1036 = 0 := by
  have hc0 : (⟨.stream, N4c.chBase .N4 0 + 1, N4c.chBase .N4 0 + N4c.chLen .N4 0,
      fun o => some (streamTarget (N4c.chBytes .N4 0) (o + 1))⟩ : N4c.TIv) ∈ N4c.nodeLayout4 .N4 := by
    simp only [N4c.nodeLayout4, N4c.chainIvs, List.mem_append, List.mem_cons, true_or, or_true]
  have hc1 : (⟨.stream, N4c.chBase .N4 1 + 1, N4c.chBase .N4 1 + N4c.chLen .N4 1,
      fun o => some (streamTarget (N4c.chBytes .N4 1) (o + 1))⟩ : N4c.TIv) ∈ N4c.nodeLayout4 .N4 := by
    simp only [N4c.nodeLayout4, N4c.chainIvs, List.mem_append, List.mem_cons, true_or, or_true]
  have ht : (⟨.stream, N4c.finB .N4 0 + 0, N4c.finB .N4 0 + 0 + 1,
      fun _ => some (streamTarget (N4c.aggB (0 + 1)) (N4c.aggL (0 + 1) - 1))⟩ : N4c.TIv) ∈
      N4c.nodeLayout4 .N4 := by
    simp only [N4c.nodeLayout4, N4c.tailIvs, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_range, List.mem_singleton]
    exact Or.inl (Or.inr ⟨0, by decide, Or.inl ⟨0, by decide, rfl⟩⟩)
  have m0 : ∀ p, nodeE4 .N4 1 p = tgtE (streamTarget (N4c.chBytes .N4 0) 1) p := fun p => by
    rw [nodeE4_of_mem hc0 (by decide)]; rfl
  have m1 : ∀ x, x < N4c.chLen .N4 1 - 1 → ∀ p, nodeE4 .N4 (N4c.chBase .N4 1 + 1 + x) p =
      tgtE (streamTarget (N4c.chBytes .N4 1) (x + 1)) p := fun x hx p => by
    have := (chain_facts .N4 (σ := 1) (by norm_num)).2.1
    rw [nodeE4_of_mem hc1 (by simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq]; omega),
      show N4c.chBase .N4 1 + 1 + x - (N4c.chBase .N4 1 + 1) = x by omega]
    rfl
  have mt : ∀ p, nodeE4 .N4 (N4c.finB .N4 0) p = tgtE (blockTarget (N4c.aggB 1) true) p := fun p => by
    rw [nodeE4_of_mem ht (by simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq]; omega)]
    simp only [tF, fin_target]
  have hl : lastB .N4 1 = N4c.chBase .N4 1 + 1 + (N4c.chLen .N4 1 - 2) := rfl
  have hl' : lastB .N4 1 - 1 = N4c.chBase .N4 1 + 1 + (N4c.chLen .N4 1 - 3) := by
    have := (chain_facts .N4 (σ := 1) (by norm_num)).2.1
    have : 3 ≤ N4c.chLen .N4 1 := by decide
    rw [hl]; omega
  have hL : 3 ≤ N4c.chLen .N4 1 := by decide
  rw [m0, m0, hl', hl, m1 _ (by omega), m1 _ (by omega), m1 _ (by omega), m1 _ (by omega), mt, mt, mt]
  simp only [tgtE_bit]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [bF] <;> decide

end Controls

end NI4T
end FR
