-- New for `flock-recursive` (BLUEPRINT revision 3.13: A.8 `targetS` and `linkW` node forms; stage-review
-- changes 20, gap 3; track S-CN, the S-F2 part).
import FRNodeTarget

/-!
# The node's `targetS` and `linkW`, computed (`targetSNodeI`, `linkWI`) and `_meets`

The computable forms of `FRNodeTarget`'s specifications on the fast field `F`.

* **Two-level tables.** `eq(r_blk, x) = A[x mod 256] · B[⌊x/256⌋]` (`eqAtR_split`), `A`, `B` the
  `eq` tables of the low and high 8 block coordinates (2 × 255 products). With prefix arrays
  (`pfx`, additions only) a sum of a separable weight `R(⌊x/256⌋) · C(x mod 256)` over a block
  range costs four products (`twoF_eq`, `sepSum_eq`): every range sum of `eq(r_blk, ·)`
  (`rangeI`), and the stream counters (`ctrI`): bit `j < 8` of the counter is a mask on the
  columns, bit `j ≥ 8` a mask on the rows split by the column carry.
* **`targetSNodeI`**: the class weights, counters and the `w43` table sums, the closed form `Gc`
  at the 1,153 pinned positions (`gArr`), then `Σ_{hi<19} eq(r_lo, hi) G(σ + 64 hi)`.
  **`targetSNode_meets`**: it is `targetSNodeS`.
* **`linkWI`**: A.8's sum per family with the two-level tables of `τ` and `r_blk` and the slot
  weights of `θ`, `r_pos` (`slotI`); **`linkW_meets`**: it is `linkWS`.
-/

namespace FR
namespace NodeI
open Finset NodeT Impl

/-! ## Two-level `eq` tables and separable range sums -/

/-- The low `a` coordinates of a point. -/
def loP {a b : ℕ} (r : Fin (a + b) → F) : Fin a → F := fun l => r (Fin.castAdd b l)

/-- The high `b` coordinates of a point. -/
def hiP {a b : ℕ} (r : Fin (a + b) → F) : Fin b → F := fun l => r (Fin.natAdd a l)

theorem eqAtR_split {a b : ℕ} (r : Fin (a + b) → F) (x : ℕ) :
    eqAtR r x = eqAtR (loP r) (x % 2 ^ a) * eqAtR (hiP r) (x / 2 ^ a % 2 ^ b) := by
  unfold eqAtR loP hiP
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun l _ => by simp [Nat.testBit_mod_two_pow, l.isLt]
  · exact Finset.prod_congr rfl fun l _ => by
      simp [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, l.isLt, add_comm]

/-- Prefix sums `0, g 0, g 0 + g 1, …` (`k + 1` entries) and the total. -/
def pfxAux (g : ℕ → F) : ℕ → Array F × F
  | 0 => (#[0], 0)
  | k + 1 => let p := pfxAux g k; (p.1.push (p.2 + g k), p.2 + g k)

/-- The 257 prefix sums of `g` on `0 … 255`. -/
def pfx (g : ℕ → F) : Array F := (pfxAux g 256).1

theorem pfxAux_eq (g : ℕ → F) (k : ℕ) :
    pfxAux g k = (Array.ofFn (n := k + 1) fun i => ∑ l ∈ range i, g l, ∑ l ∈ range k, g l) := by
  induction k with
  | zero =>
    refine Prod.ext ?_ rfl
    rw [Array.ofFn_succ, Array.ofFn_zero]
    rfl
  | succ k ih =>
    rw [pfxAux, ih]
    simp only [Finset.sum_range_succ]
    refine Prod.ext ?_ rfl
    rw [Array.ofFn_succ (n := k + 1)]
    simp [Finset.sum_range_succ]

theorem pfx_getD (g : ℕ → F) {i : ℕ} (hi : i ≤ 256) : (pfx g).getD i 0 = ∑ l ∈ range i, g l := by
  simp [pfx, pfxAux_eq, Array.getD_eq_getD_getElem?, Nat.lt_succ_of_le hi]

/-- `Σ_{x<X} R(⌊x/256⌋) C(x mod 256)` from the prefix arrays `PR`, `PC`. -/
def twoF (PR : Array F) (R : ℕ → F) (PC : Array F) (X : ℕ) : F :=
  PR.getD (X / 256) 0 * PC.getD 256 0 + R (X / 256) * PC.getD (X % 256) 0

theorem twoF_eq (R C : ℕ → F) {X : ℕ} (hX : X ≤ 2 ^ 16) :
    twoF (pfx R) R (pfx C) X = ∑ x ∈ range X, R (x / 256) * C (x % 256) := by
  have hh : X / 256 ≤ 256 := by omega
  have hl : X % 256 ≤ 256 := by omega
  unfold twoF
  rw [pfx_getD _ hh, pfx_getD _ le_rfl, pfx_getD _ hl]
  conv_rhs => rw [← Nat.div_add_mod X 256, Finset.sum_range_add, mul_comm 256, sum_range_mul]
  rw [Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (h * 256 + k) / 256 = h by omega, show (h * 256 + k) % 256 = k by omega]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (X / 256 * 256 + k) / 256 = X / 256 by omega,
      show (X / 256 * 256 + k) % 256 = k by omega]

/-- **A separable weight over a block range**: `Σ_{k<n} R(⌊(lo+k)/256⌋) C((lo+k) mod 256)`. -/
def sepSum (PR : Array F) (R : ℕ → F) (PC : Array F) (lo n : ℕ) : F :=
  twoF PR R PC (lo + n) - twoF PR R PC lo

theorem sepSum_eq (R C : ℕ → F) {lo n : ℕ} (h : lo + n ≤ 2 ^ 16) :
    sepSum (pfx R) R (pfx C) lo n = ∑ k ∈ range n, R ((lo + k) / 256) * C ((lo + k) % 256) := by
  rw [sepSum, twoF_eq R C h, twoF_eq R C (by omega), Finset.sum_range_add, add_sub_cancel_left]

/-! ## The block point's tables -/

/-- The block point's two-level tables `A` (low 8 coordinates), `B` (high 8) and their prefix
arrays. -/
structure Tabs where
  A : Array F
  B : Array F
  PA : Array F
  PB : Array F

/-- `A[l]`. -/
def Tabs.a (T : Tabs) (l : ℕ) : F := T.A.getD l 0
/-- `B[h]`. -/
def Tabs.b (T : Tabs) (h : ℕ) : F := T.B.getD h 0

/-- The low and high 8 block coordinates. -/
def lo8 (rb : Fin 16 → F) : Fin 8 → F := fun l => rb ⟨l, by omega⟩
def hi8 (rb : Fin 16 → F) : Fin 8 → F := fun l => rb ⟨8 + l, by omega⟩

/-- The tables of a 16-coordinate point (510 products). -/
def tabs (rb : Fin 16 → F) : Tabs :=
  let A := eqTable (List.ofFn (lo8 rb))
  let B := eqTable (List.ofFn (hi8 rb))
  ⟨A, B, pfx fun l => A.getD l 0, pfx fun h => B.getD h 0⟩

/-- `eq(r_blk, x)` from the tables (one product). -/
def eqbI (T : Tabs) (x : ℕ) : F := T.a (x % 256) * T.b (x / 256 % 256)

/-- `Σ_{k<n} eq(r_blk, lo + k)` (four products). -/
def rangeI (T : Tabs) (lo n : ℕ) : F := sepSum T.PB T.b T.PA lo n

section TabsLemmas
variable (rb : Fin 16 → F)

theorem tabs_A : (tabs rb).A = eqTable (List.ofFn (lo8 rb)) := by dsimp only [tabs]
theorem tabs_B : (tabs rb).B = eqTable (List.ofFn (hi8 rb)) := by dsimp only [tabs]

theorem tabs_a {l : ℕ} (hl : l < 2 ^ 8) : (tabs rb).a l = eqAtR (lo8 rb) l := by
  rw [Tabs.a, tabs_A]; exact eqTable_ofFn_getD _ hl

theorem tabs_b {h : ℕ} (hh : h < 2 ^ 8) : (tabs rb).b h = eqAtR (hi8 rb) h := by
  rw [Tabs.b, tabs_B]; exact eqTable_ofFn_getD _ hh

theorem eqAtR16 (x : ℕ) : eqAtR rb x = eqAtR (lo8 rb) (x % 256) * eqAtR (hi8 rb) (x / 256 % 256) :=
  eqAtR_split (a := 8) (b := 8) rb x

theorem eqbI_eq (x : ℕ) : eqbI (tabs rb) x = eqAtR rb x := by
  rw [eqbI, tabs_a rb (l := x % 256) (by omega), tabs_b rb (h := x / 256 % 256) (by omega),
    eqAtR16]

theorem ba_eq {x : ℕ} (hx : x < 2 ^ 16) :
    (tabs rb).b (x / 256) * (tabs rb).a (x % 256) = eqAtR rb x := by
  rw [← eqbI_eq, eqbI, Nat.mod_eq_of_lt (show x / 256 < 256 by omega), mul_comm]

theorem tabs_PA : (tabs rb).PA = pfx fun l => (tabs rb).a l := by dsimp only [tabs, Tabs.a]
theorem tabs_PB : (tabs rb).PB = pfx fun h => (tabs rb).b h := by dsimp only [tabs, Tabs.b]

theorem rangeI_eq {lo n : ℕ} (h : lo + n ≤ 2 ^ 16) :
    rangeI (tabs rb) lo n = ∑ k ∈ range n, eqAtR rb (lo + k) := by
  rw [rangeI, tabs_PA, tabs_PB, sepSum_eq _ _ h]
  exact Finset.sum_congr rfl fun k hk => ba_eq rb (by have := Finset.mem_range.1 hk; omega)

end TabsLemmas

/-! ## The stream counters -/

/-- **The counter bits of a stream body** `Σ_{k<n} eq(r_blk, lo + k) · bit_j(k + 2)`: with
`k + 2 = (lo + k) + e − 256 Q`, bit `j < 8` depends on the column `(lo + k) mod 256` only, bit
`j ≥ 8` on the row and the column's carry; `0` once `2^j > n + 1`. -/
def ctrI (T : Tabs) (lo n j : ℕ) : F :=
  if n + 1 < 2 ^ j then 0 else
  let Q := (lo + 253) / 256
  let e := 256 * Q + 2 - lo
  let d := e % 256
  if j < 8 then
    let C := fun l => if ((l + d) % 256).testBit j then T.a l else 0
    sepSum T.PB T.b (pfx C) lo n
  else
    let C0 := fun l => if l + d < 256 then T.a l else 0
    let C1 := fun l => if l + d < 256 then 0 else T.a l
    let R0 := fun h => if (h + e / 256 - Q).testBit (j - 8) then T.b h else 0
    let R1 := fun h => if (h + e / 256 + 1 - Q).testBit (j - 8) then T.b h else 0
    sepSum (pfx R0) R0 (pfx C0) lo n + sepSum (pfx R1) R1 (pfx C1) lo n

theorem ctrI_eq (rb : Fin 16 → F) {lo n : ℕ} (h : lo + n ≤ 2 ^ 16) (j : ℕ) :
    ctrI (tabs rb) lo n j = ∑ k ∈ range n, eqAtR rb (lo + k) * bF ((k + 2).testBit j) := by
  unfold ctrI
  split_ifs with hj hj8
  · refine (Finset.sum_eq_zero fun k hk => ?_).symm
    have := Finset.mem_range.1 hk
    rw [Nat.testBit_lt_two_pow (by omega)]
    simp [bF]
  · rw [tabs_PB, sepSum_eq _ _ h]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hb : (k + 2).testBit j = (((lo + k) % 256 + (256 * ((lo + 253) / 256) + 2 - lo) % 256)
        % 256).testBit j := by
      rw [show ((lo + k) % 256 + (256 * ((lo + 253) / 256) + 2 - lo) % 256) % 256 =
        (k + 2) % 2 ^ 8 by omega, Nat.testBit_mod_two_pow]
      simp [hj8]
    rw [hb, ← ba_eq rb (show lo + k < 2 ^ 16 by omega)]
    unfold bF
    split_ifs <;> ring
  · dsimp only
    rw [sepSum_eq _ _ h, sepSum_eq _ _ h, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [← ba_eq rb (show lo + k < 2 ^ 16 by omega)]
    have hb : (k + 2).testBit j = ((k + 2) / 2 ^ 8).testBit (j - 8) := by
      rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]
    by_cases hc : (lo + k) % 256 + (256 * ((lo + 253) / 256) + 2 - lo) % 256 < 256
    · rw [hb, show (k + 2) / 2 ^ 8 = (lo + k) / 256 + (256 * ((lo + 253) / 256) + 2 - lo) / 256 -
        (lo + 253) / 256 by omega]
      simp only [hc, ite_true, ite_false, mul_zero, add_zero]
      unfold bF
      split_ifs <;> ring
    · rw [hb, show (k + 2) / 2 ^ 8 = (lo + k) / 256 + (256 * ((lo + 253) / 256) + 2 - lo) / 256 +
        1 - (lo + 253) / 256 by omega]
      simp only [hc, ite_true, ite_false, mul_zero, zero_add]
      unfold bF
      split_ifs <;> ring

/-! ## `targetSNodeI` -/

/-- The ten classes' pinned bits at the positions `0 … 1152` (computed once). -/
def clsTab : Array (Array Bool) :=
  Array.ofFn (n := 10) fun c => Array.ofFn (n := 1153) fun p =>
    cls c (ProductCircuit.pos p) == some true

/-- Class `c`'s bit at `p`. -/
def clsBit (c p : ℕ) : Bool := (clsTab.getD c #[]).getD p false

theorem clsBit_eq {c p : ℕ} (hc : c < 10) (hp : p < 1153) (w : F) :
    (if clsBit c p then w else 0) = w * tgtE (cls c) p := by
  have : clsBit c p = (cls c (ProductCircuit.pos p) == some true) := by
    simp [clsBit, clsTab, Array.getD_eq_getD_getElem?, hc, hp]
  rw [this, tgtE, bF]
  split_ifs <;> simp

/-- The ten class weights (A.8: range sums and single blocks of `eq(r_blk, ·)`). -/
structure Wts where
  w0 : F
  w1 : F
  w2 : F
  w3 : F
  w4 : F
  w5 : F
  w6 : F
  w7 : F
  w8 : F
  w9 : F

/-- The class weights from the tables: `streamStart`, the stream bodies (both chains, both key
leaves), the chains' last blocks, `hashA`, `hashB1 tagNode`, `hashB2` (statement and path),
`w43`, `hashB1 tagWotsLeaf`, `streamEnd41`, `hashB1 tagSigNode`. -/
def wts (T : Tabs) : Wts :=
  let N := Layout.chainN
  ⟨sumTo 2 fun σ => eqbI T (σ * N),
   (sumTo 2 fun σ => rangeI T (σ * N + 1) (N - 2)) + sumTo 2 fun σ => rangeI T (wb σ + 400) 65,
   sumTo 2 fun σ => eqbI T (σ * N + (N - 1)),
   sumTo 2 fun σ => eqbI T (Layout.stmtBase + 3 * σ),
   sumTo 2 fun σ => eqbI T (Layout.stmtBase + 3 * σ + 1),
   (sumTo 2 fun σ => eqbI T (Layout.stmtBase + 3 * σ + 2)) +
     sumTo 2 fun σ => sumTo 16 fun t => eqbI T (wb σ + 467 + 2 * t),
   sumTo 2 fun σ => rangeI T (wb σ) 399,
   sumTo 2 fun σ => eqbI T (wb σ + 399),
   sumTo 2 fun σ => eqbI T (wb σ + 465),
   sumTo 2 fun σ => sumTo 16 fun t => eqbI T (wb σ + 466 + 2 * t)⟩

/-- `eq(r_blk, wb σ + o)` for the 399 `w43` blocks (399 products). -/
def e43 (T : Tabs) (σ : ℕ) : Array F := Array.ofFn (n := 399) fun o => eqbI T (wb σ + o)

/-- `Σ_{o<399} eq(r_blk, wb σ + o) · bit_b(sel o)` from `e43` (additions only). -/
def w43I (E : Array F) (sel : ℕ → ℕ) (b : ℕ) : F :=
  sumTo 399 fun o => if (sel o).testBit b then E.getD o 0 else 0

/-- `G(p)` from the class weights, the counter bits `CT`, and `w43`'s `i`, `s` bits. -/
def gAt (W : Wts) (CT WI WS : Array F) (p : ℕ) : F :=
  ((if clsBit 0 p then W.w0 else 0) + (if clsBit 1 p then W.w1 else 0) +
    (if clsBit 2 p then W.w2 else 0) + (if clsBit 3 p then W.w3 else 0) +
    (if clsBit 4 p then W.w4 else 0) + (if clsBit 5 p then W.w5 else 0) +
    (if clsBit 6 p then W.w6 else 0) + (if clsBit 7 p then W.w7 else 0) +
    (if clsBit 8 p then W.w8 else 0) + (if clsBit 9 p then W.w9 else 0)) +
  (if 1030 ≤ p ∧ p < 1056 then CT.getD (p - 1030) 0 else 0) +
  (if 584 ≤ p ∧ p < 592 then WI.getD (p - 584) 0 else 0) +
  (if 592 ≤ p ∧ p < 600 then WS.getD (p - 592) 0 else 0)

/-- **`G` at the 1,153 pinned positions** (the rest is `0`). -/
def gArr (T : Tabs) : Array F :=
  let N := Layout.chainN
  let W := wts T
  let CT := Array.ofFn (n := 26) fun j =>
    (sumTo 2 fun σ => ctrI T (σ * N + 1) (N - 2) j) + sumTo 2 fun σ => ctrI T (wb σ + 400) 65 j
  let E0 := e43 T 0
  let E1 := e43 T 1
  let WI := Array.ofFn (n := 8) fun b => w43I E0 (· / 3) b + w43I E1 (· / 3) b
  let WS := Array.ofFn (n := 8) fun b => w43I E0 (· % 3) b + w43I E1 (· % 3) b
  Array.ofFn (n := 1153) fun p => gAt W CT WI WS p

/-- **`targetS` of a node** (A.8, revision 3.13), computed: `Σ_{hi<19} eq(r_lo, hi) G(σ + 64 hi)`. -/
def targetSNodeI (r : Array F) : Array F :=
  let G := gArr (tabs (rbOf r))
  let H := eqTable (List.ofFn (zLo r))
  Array.ofFn (n := 64) fun σ => sumTo 19 fun hi => H.getD hi 0 * G.getD (σ + 64 * hi) 0

section Meets
variable (rb : Fin 16 → F)

theorem w43I_eq (σ : ℕ) (sel : ℕ → ℕ) (b : ℕ) :
    w43I (e43 (tabs rb) σ) sel b = ∑ o ∈ range 399, eqAtR rb (wb σ + o) * bF ((sel o).testBit b) := by
  rw [w43I, sumTo_eq]
  refine Finset.sum_congr rfl fun o ho => ?_
  have := Finset.mem_range.1 ho
  rw [e43, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos this, Option.getD_some,
    eqbI_eq, bF]
  split_ifs <;> simp

theorem hσ_bounds {σ : ℕ} (hσ : σ < 2) :
    σ * Layout.chainN + 1 + (Layout.chainN - 2) ≤ 2 ^ 16 ∧ wb σ + 400 + 65 ≤ 2 ^ 16 ∧
      wb σ + 399 ≤ 2 ^ 16 := by
  have hN : Layout.chainN = 23146 := rfl
  have hw : wb σ = 46298 + 498 * σ := rfl
  rw [hN, hw]
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> norm_num

private theorem sum_two (g : ℕ → F) : ∑ σ ∈ range 2, g σ = g 0 + g 1 := by
  simp [Finset.sum_range_succ]

private theorem sum_ite_c2 (c : Prop) [Decidable c] (g : ℕ → F) :
    ∑ σ ∈ range 2, (if c then g σ else 0) = if c then ∑ σ ∈ range 2, g σ else 0 := by
  split_ifs <;> simp

theorem gAt_eq {p : ℕ} (hp : p < 1153) :
    (gArr (tabs rb)).getD p 0 = Gc rb p := by
  have hN : Layout.chainN = 23146 := rfl
  have hw : ∀ σ, wb σ = 46298 + 498 * σ := fun _ => rfl
  simp only [gArr]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hp, Option.getD_some]
  unfold gAt
  rw [clsBit_eq (c := 0) (by norm_num) hp, clsBit_eq (c := 1) (by norm_num) hp,
    clsBit_eq (c := 2) (by norm_num) hp, clsBit_eq (c := 3) (by norm_num) hp,
    clsBit_eq (c := 4) (by norm_num) hp, clsBit_eq (c := 5) (by norm_num) hp,
    clsBit_eq (c := 6) (by norm_num) hp, clsBit_eq (c := 7) (by norm_num) hp,
    clsBit_eq (c := 8) (by norm_num) hp, clsBit_eq (c := 9) (by norm_num) hp]
  simp only [wts, sumTo_eq, eqbI_eq, sum_two]
  rw [rangeI_eq rb (lo := 0 * Layout.chainN + 1) (n := Layout.chainN - 2) (by rw [hN]; norm_num),
    rangeI_eq rb (lo := 1 * Layout.chainN + 1) (n := Layout.chainN - 2) (by rw [hN]; norm_num),
    rangeI_eq rb (lo := wb 0 + 400) (n := 65) (by rw [hw]; norm_num),
    rangeI_eq rb (lo := wb 1 + 400) (n := 65) (by rw [hw]; norm_num),
    rangeI_eq rb (lo := wb 0) (n := 399) (by rw [hw]; norm_num),
    rangeI_eq rb (lo := wb 1) (n := 399) (by rw [hw]; norm_num)]
  unfold Gc chainC stmtC wotsC w43C ctrC
  simp only [sum_two]
  by_cases h1 : 1030 ≤ p ∧ p < 1056
  · have h1' : p - 1030 < 26 := by omega
    have h2 : ¬ (584 ≤ p ∧ p < 592) := by omega
    have h3 : ¬ (592 ≤ p ∧ p < 600) := by omega
    simp only [h1, h2, h3, and_self, ite_true, ite_false, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      dif_pos h1', Option.getD_some, add_zero]
    rw [ctrI_eq rb (lo := 0 * Layout.chainN + 1) (n := Layout.chainN - 2) (by rw [hN]; norm_num),
      ctrI_eq rb (lo := 1 * Layout.chainN + 1) (n := Layout.chainN - 2) (by rw [hN]; norm_num),
      ctrI_eq rb (lo := wb 0 + 400) (n := 65) (by rw [hw]; norm_num),
      ctrI_eq rb (lo := wb 1 + 400) (n := 65) (by rw [hw]; norm_num)]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  by_cases h2 : 584 ≤ p ∧ p < 592
  · have h2' : p - 584 < 8 := by omega
    have h3 : ¬ (592 ≤ p ∧ p < 600) := by omega
    simp only [h1, h2, h3, and_self, ite_true, ite_false, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      dif_pos h2', Option.getD_some, add_zero, w43I_eq]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  by_cases h3 : 592 ≤ p ∧ p < 600
  · have h3' : p - 592 < 8 := by omega
    simp only [h1, h2, h3, and_self, ite_true, ite_false, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      dif_pos h3', Option.getD_some, add_zero, w43I_eq]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  simp only [h1, h2, h3, ite_false, add_zero]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- **`targetS` meets the node's specification.** -/
theorem targetSNode_meets (r : Array F) : targetSNodeI r = targetSNodeS r := by
  rw [targetS_node_eq]
  unfold targetSNodeI
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  have hσ := σ.isLt
  rw [sumTo_eq, show (256 : ℕ) = 19 + 237 from rfl, Finset.sum_range_add,
    Finset.sum_eq_zero (s := range 237) fun x hx => by
      rw [Gc_hi _ (by omega) (by have := Finset.mem_range.1 hx; omega), mul_zero], add_zero]
  refine Finset.sum_congr rfl fun hi hh => ?_
  have hh' := Finset.mem_range.1 hh
  rw [eqTable_ofFn_getD _ (show hi < 2 ^ 8 by omega)]
  refine congrArg (eqAtR (zLo r) hi * ·) ?_
  by_cases hq : σ.val + 64 * hi < 1153
  · exact gAt_eq _ hq
  · rw [Gc_hi _ (by omega) (by omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simp only [gArr, Array.size_ofFn]; omega)]
    rfl

end Meets

/-! ## `linkWI` -/

/-- The two `eq` tables of a 16-coordinate point without prefix arrays (`eqbI` only). -/
def tabsE (rb : Fin 16 → F) : Tabs :=
  ⟨eqTable (List.ofFn (lo8 rb)), eqTable (List.ofFn (hi8 rb)), #[], #[]⟩

theorem eqbI_eqE (rb : Fin 16 → F) (x : ℕ) : eqbI (tabsE rb) x = eqAtR rb x := by
  rw [eqbI, Tabs.a, Tabs.b, show (tabsE rb).A = eqTable (List.ofFn (lo8 rb)) by dsimp only [tabsE],
    show (tabsE rb).B = eqTable (List.ofFn (hi8 rb)) by dsimp only [tabsE],
    eqTable_ofFn_getD _ (show x % 256 < 2 ^ 8 by omega),
    eqTable_ofFn_getD _ (show x / 256 % 256 < 2 ^ 8 by omega), eqAtR16]

/-- A 10-coordinate point's two tables (low 8 coordinates, high 2). -/
def tab10 (r : Fin 10 → F) : Array F × Array F :=
  (eqTable (List.ofFn (loP (a := 8) (b := 2) r)), eqTable (List.ofFn (hiP (a := 8) (b := 2) r)))

/-- `eq(r, q)` from the tables (one product). -/
def eq10 (P : Array F × Array F) (q : ℕ) : F := P.1.getD (q % 256) 0 * P.2.getD (q / 256 % 4) 0

theorem eq10_eq (r : Fin 10 → F) (q : ℕ) : eq10 (tab10 r) q = eqAtR r q := by
  rw [eq10, show (tab10 r).1 = eqTable (List.ofFn (loP (a := 8) (b := 2) r)) by dsimp only [tab10],
    show (tab10 r).2 = eqTable (List.ofFn (hiP (a := 8) (b := 2) r)) by dsimp only [tab10],
    eqTable_ofFn_getD _ (show q % 256 < 2 ^ 8 by omega),
    eqTable_ofFn_getD _ (show q / 256 % 4 < 2 ^ 2 by omega)]
  exact (eqAtR_split (a := 8) (b := 2) r q).symm

/-- Family `f`'s weight from the tables: per source `eq(τ, src)·(eq(r_blk, src)·SW −
eq(r_blk, mirBlk)·MS[mir mod 4])`, `SW` the field's slot weight, `MS[c]` the mirror's for the
mirror slot `c` (`MS[c] = eq(r_pos,hi, c) · Σ_s eq(θ, s) eq(r_pos,lo, mbo + s)`). -/
def linkWOne (Tτ Tr : Tabs) (Pr : Array F × Array F) (Eθ : Array F) (f : ℕ) : F :=
  let L := fbits f
  let SW := sumTo L fun s => Eθ.getD s 0 * eq10 Pr (fpos f s)
  let MI := sumTo L fun s => Eθ.getD s 0 * Pr.1.getD ((fam f).mbo + s) 0
  let MS := Array.ofFn (n := 4) fun c => Pr.2.getD c 0 * MI
  sumTo 2 fun σ => sumTo (fam f).n fun t =>
    eqbI Tτ (srcB σ f t) * (eqbI Tr (srcB σ f t) * SW -
      eqbI Tr (mirB σ f t) * MS.getD ((fam f).mir t % 4) 0)

/-- The tables of `linkW`'s four points. -/
def linkTabs (τ θ rb rp : Array F) : Tabs × Tabs × (Array F × Array F) × Array F :=
  let Pθ := tab10 (ptA 10 θ)
  (tabsE (ptA 16 τ), tabsE (ptA 16 rb), tab10 (ptA 10 rp),
    Array.ofFn (n := 256) fun s => eq10 Pθ s)

/-- **`linkW` of a node** (A.8, revision 3.13), family `f`, computed. -/
def linkWI (f : ℕ) (τ θ rb rp : Array F) : F :=
  let T := linkTabs τ θ rb rp
  linkWOne T.1 T.2.1 T.2.2.1 T.2.2.2 f

/-- All eight families at once (the tables shared). -/
def linkWAllI (τ θ rb rp : Array F) : Array F :=
  let T := linkTabs τ θ rb rp
  Array.ofFn (n := nLinkFam) fun f => linkWOne T.1 T.2.1 T.2.2.1 T.2.2.2 f

/-- **`linkW`'s specification on arrays** (`linkWS` at the points the arrays read). -/
def linkWSA (f : ℕ) (τ θ rb rp : Array F) : F :=
  linkWS f (ptA 16 τ) (ptA 10 θ) (ptA 16 rb) (ptA 10 rp)

section LinkMeets

theorem mbo_le (f : ℕ) : (fam f).mbo + fbits f ≤ 256 := by
  unfold fbits
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp [fam]

theorem linkWOne_eq (f : ℕ) (τ rb : Fin 16 → F) (θ' rp' : Fin 10 → F) :
    linkWOne (tabsE τ) (tabsE rb) (tab10 rp')
      (Array.ofFn (n := 256) fun s => eq10 (tab10 θ') s) f = linkWS f τ θ' rb rp' := by
  have hE : ∀ s < fbits f, (Array.ofFn (n := 256) fun s => eq10 (tab10 θ') s).getD s 0 =
      eqAtR θ' s := fun s hs => by
    have : s < 256 := by have := mbo_le f; omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos this, Option.getD_some, eq10_eq]
  have hSW : (sumTo (fbits f) fun s => (Array.ofFn (n := 256) fun s => eq10 (tab10 θ') s).getD s 0 *
      eq10 (tab10 rp') (fpos f s)) = slotWL (fpos f) (fbits f) θ' rp' := by
    rw [sumTo_eq, slotWL]
    exact Finset.sum_congr rfl fun s hs => by rw [hE s (Finset.mem_range.1 hs), eq10_eq]
  have hMS : ∀ t, ((Array.ofFn (n := 4) fun c => (tab10 rp').2.getD c 0 *
      sumTo (fbits f) fun s => (Array.ofFn (n := 256) fun s => eq10 (tab10 θ') s).getD s 0 *
        (tab10 rp').1.getD ((fam f).mbo + s) 0).getD ((fam f).mir t % 4) 0) =
      slotWL (mpos f t) (fbits f) θ' rp' := fun t => by
    have hc : (fam f).mir t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hc, Option.getD_some, sumTo_eq,
      Finset.mul_sum, slotWL]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    have hb := mbo_le f
    rw [hE s hs', mpos, ← eq10_eq rp', eq10,
      show (256 * ((fam f).mir t % 4) + (fam f).mbo + s) % 256 = (fam f).mbo + s by omega,
      show (256 * ((fam f).mir t % 4) + (fam f).mbo + s) / 256 % 4 = (fam f).mir t % 4 by omega,
      Fin.val_mk]
    ring
  unfold linkWOne linkWS
  dsimp only
  rw [hSW]
  simp only [hMS]
  simp only [sumTo_eq, eqbI_eqE]

/-- **`linkW` meets its specification**, every family. -/
theorem linkW_meets (f : ℕ) (τ θ rb rp : Array F) : linkWI f τ θ rb rp = linkWSA f τ θ rb rp := by
  dsimp only [linkWI, linkTabs]
  exact linkWOne_eq f _ _ _ _

/-- The shared form meets it too (`f < 8`). -/
theorem linkWAll_meets {f : ℕ} (hf : f < nLinkFam) (τ θ rb rp : Array F) :
    (linkWAllI τ θ rb rp).getD f 0 = linkWSA f τ θ rb rp := by
  dsimp only [linkWAllI, linkTabs]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hf, Option.getD_some]
  exact linkWOne_eq f _ _ _ _

theorem ptA_extract (a : Array F) {o s n : ℕ} (hs : s = o + n) :
    ptA n (a.extract o s) = fun l : Fin n => a.getD (o + l.1) 0 := by
  funext l
  subst hs
  simp only [ptA, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  by_cases h : o + l.1 < a.size
  · rw [if_pos (by omega)]
  · rw [Array.getElem?_eq_none (by omega)]
    split_ifs <;> simp

/-- **`linkWAll` meets `linkWAllS`** on the packed points (`implC`'s split of `τ ‖ θ`,
`r_blk ‖ r_pos`; `linkWOne_eq`, as `linkWAll_meets` per family). -/
theorem linkWAll_eqS (tt rr : Array F) :
    linkWAllI (tt.extract 0 16) (tt.extract 16 26) (rr.extract 0 16) (rr.extract 16 26) =
      linkWAllS tt rr := by
  unfold linkWAllI linkTabs linkWAllS
  dsimp only
  rw [ptA_extract tt (o := 0) (n := 16) rfl, ptA_extract tt (o := 16) (n := 10) rfl,
    ptA_extract rr (o := 0) (n := 16) rfl, ptA_extract rr (o := 16) (n := 10) rfl]
  congr 1
  funext f
  rw [linkWOne_eq]
  simp only [zero_add]
  rfl

end LinkMeets

/-! ## `shiftMask` (revision 3.14: the node's chain-masked shift weights) -/

/-- **`shiftMask`, computed**: the product tables of `τ` and `r` (`tabs`), the separable range sums
over the two chains' link blocks (`sepSum`); the shifted weight splits at the low byte's carry
(`l < 255`: `C₁`; `l = 255`: `R₂ C₂`, the high byte stepping). -/
def shiftMaskI (τ r : Array F) : F × F × F :=
  let Tt := tabs (ptA 16 τ); let Tr := tabs (ptA 16 r)
  let R : ℕ → F := fun h => Tt.b h * Tr.b h
  let R2 : ℕ → F := fun h => Tt.b h * Tr.b (h + 1)
  let C : ℕ → F := fun l => Tt.a l * Tr.a l
  let C1 : ℕ → F := fun l => Tt.a l * Tr.a (l + 1)
  let C2 : ℕ → F := fun l => if l = 255 then Tt.a 255 * Tr.a 0 else 0
  let PR := pfx R; let PR2 := pfx R2; let PC := pfx C; let PC1 := pfx C1; let PC2 := pfx C2
  let N := Layout.chainN
  (sepSum PR R PC 0 (N - 1) + sepSum PR R PC N (N - 1),
   sepSum PR R PC1 0 (N - 1) + sepSum PR R PC1 N (N - 1) +
     (sepSum PR2 R2 PC2 0 (N - 1) + sepSum PR2 R2 PC2 N (N - 1)),
   eqbI Tr 0 + eqbI Tr N)

section MaskMeets

theorem tabs_a256 (rb : Fin 16 → F) : (tabs rb).a 256 = 0 := by
  rw [Tabs.a, tabs_A, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
    rw [eqTable_size, List.length_ofFn]; norm_num)]
  rfl

theorem mask_eq (τ r : Fin 16 → F) {y : ℕ} (hy : y < 2 ^ 16) :
    eqAtR τ y * eqAtR r y =
      (tabs τ).b (y / 256) * (tabs r).b (y / 256) * ((tabs τ).a (y % 256) * (tabs r).a (y % 256)) := by
  rw [← ba_eq τ hy, ← ba_eq r hy]; ring

theorem mask_succ_eq (τ r : Fin 16 → F) {y : ℕ} (hy : y + 256 < 2 ^ 16) :
    eqAtR τ y * eqAtR r (y + 1) =
      (tabs τ).b (y / 256) * (tabs r).b (y / 256) * ((tabs τ).a (y % 256) * (tabs r).a (y % 256 + 1)) +
      (tabs τ).b (y / 256) * (tabs r).b (y / 256 + 1) *
        (if y % 256 = 255 then (tabs τ).a 255 * (tabs r).a 0 else 0) := by
  rw [← ba_eq τ (by omega), ← ba_eq r (by omega)]
  by_cases hl : y % 256 = 255
  · rw [if_pos hl, hl, tabs_a256, show (y + 1) / 256 = y / 256 + 1 by omega,
      show (y + 1) % 256 = 0 by omega]
    ring
  · rw [if_neg hl, show (y + 1) / 256 = y / 256 by omega, show (y + 1) % 256 = y % 256 + 1 by omega]
    ring

private theorem sum2 (g : ℕ → F) : ∑ c ∈ range 2, g c = g 0 + g 1 := by
  simp [Finset.sum_range_succ]

/-- **`shiftMask` meets its specification.** -/
theorem shiftMask_meets (τ r : Array F) : shiftMaskI τ r = shiftMaskS τ r := by
  have hN : 2 * Layout.chainN + 256 < 2 ^ 16 := by simp only [Layout.chainN]; norm_num
  unfold shiftMaskI shiftMaskS
  generalize Layout.chainN = N at hN ⊢
  have hs : ∀ (lo : ℕ) (R C : ℕ → F), lo ≤ N →
      sepSum (pfx R) R (pfx C) lo (N - 1) =
        ∑ k ∈ range (N - 1), R ((lo + k) / 256) * C ((lo + k) % 256) :=
    fun lo R C h => sepSum_eq R C (by omega)
  have hb : ∀ k ∈ range (N - 1), N + k + 256 < 2 ^ 16 := fun k hk => by
    have := Finset.mem_range.1 hk; omega
  dsimp only
  rw [hs 0 _ _ (Nat.zero_le _), hs 0 _ _ (Nat.zero_le _), hs 0 _ _ (Nat.zero_le _),
    hs _ _ _ le_rfl, hs _ _ _ le_rfl, hs _ _ _ le_rfl, eqbI_eq, eqbI_eq, sum2, sum2]
  simp only [zero_mul, one_mul, zero_add]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · dsimp only
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k hk => ?_) (Finset.sum_congr rfl fun k hk => ?_)
    · exact (mask_eq (ptA 16 τ) (ptA 16 r) (by have := hb k hk; omega)).symm
    · exact (mask_eq (ptA 16 τ) (ptA 16 r) (by have := hb k hk; omega)).symm
  · dsimp only
    rw [add_add_add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k hk => ?_) (Finset.sum_congr rfl fun k hk => ?_)
    · exact (mask_succ_eq (ptA 16 τ) (ptA 16 r) (by have := hb k hk; omega)).symm
    · exact (mask_succ_eq (ptA 16 τ) (ptA 16 r) (hb k hk)).symm

/-- `ptA 16` of a point padded by zeros is the point's (revision 3.15). -/
theorem ptA16_pad (xs : List F) (k : ℕ) (h : xs.length = 16) :
    ptA 16 (xs ++ List.replicate k 0).toArray = ptA 16 xs.toArray := by
  funext l
  simp [ptA, Array.getD_eq_getD_getElem?, List.getElem?_append_left (show l.val < xs.length by omega)]

/-- **`shiftMask`'s specification on 18-coordinate zero-padded block points** (revision 3.15,
ruling (c)): it reads the first 16 coordinates, so it is the 16-coordinate one. -/
theorem shiftMaskS_pad (xs ys : List F) (k : ℕ) (hx : xs.length = 16) (hy : ys.length = 16) :
    shiftMaskS (xs ++ List.replicate k 0).toArray (ys ++ List.replicate k 0).toArray =
      shiftMaskS xs.toArray ys.toArray := by
  simp only [shiftMaskS, ptA16_pad xs k hx, ptA16_pad ys k hy]

end MaskMeets

/-! ## Controls -/

section Controls

theorem ptA_ofFn {n : ℕ} (g : Fin n → F) : ptA n (Array.ofFn g) = g := by
  funext l; simp [ptA, Array.getD_eq_getD_getElem?]

/-- (+) `linkWI`, family `x`: its first source's field bit 0 reads `1`. -/
theorem linkWI_hit : linkWI 0 (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 0))
    (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 600)) = 1 := by
  rw [linkW_meets, linkWSA]
  simp only [ptA_ofFn]
  exact linkW_hit

/-- (−) … one position off reads `0`; the mirror cell reads `−1`. -/
theorem linkWI_off_mir : linkWI 0 (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 0))
      (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 601)) = 0 ∧
    linkWI 0 (Array.ofFn (cubeN 16 (wb 0))) (Array.ofFn (cubeN 10 0))
      (Array.ofFn (cubeN 16 (mirB 0 0 0))) (Array.ofFn (cubeN 10 (mpos 0 0 0))) = -1 := by
  refine ⟨?_, ?_⟩ <;> rw [linkW_meets, linkWSA] <;> simp only [ptA_ofFn]
  · exact linkW_off
  · exact linkW_mir

/-- (−) At a `free` block point (`WM` and beyond) the node's `targetS` is zero. -/
theorem targetSNodeI_free (r : Array F) {b : ℕ} (hr : rbOf r = cubeN 16 b)
    (h1 : Layout.wmBase ≤ b) (h2 : b < 2 ^ 16) :
    targetSNodeI r = Array.ofFn (n := 64) fun _ => 0 := by
  rw [targetSNode_meets, targetSNode_blk, hr]
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => Finset.sum_eq_zero fun hi _ => ?_)
  rw [blkW_cube h2, nodeE_free h1, mul_zero]

/-- (+) At a Boolean block point `b` the node's `targetS` reads block `b`'s target. -/
theorem targetSNodeI_blk (r : Array F) {b : ℕ} (hr : rbOf r = cubeN 16 b) (h2 : b < 2 ^ 16) :
    targetSNodeI r = Array.ofFn (n := 64) fun σ =>
      ∑ hi ∈ range 256, eqAtR (zLo r) hi * nodeE b (σ + 64 * hi) := by
  rw [targetSNode_meets, targetSNode_blk, hr]
  exact congrArg (Array.ofFn (n := 64)) (funext fun σ => Finset.sum_congr rfl fun hi _ => by
    rw [blkW_cube h2])

end Controls

end NodeI
end FR
