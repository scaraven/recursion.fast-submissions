-- New for lvm2 (CR-Q, roll 7 SH2-Z; CR-DES §1.5 circuit side): `V_S`'s small claims (`onStackZB`,
-- `LvmShapeVN`) evaluated at WHIR's terminal point as big-form claims at the rotated point
-- `x^σ = x.tail ‖ x₀`: what the circuit computes with its muxed coordinates. Reuses HAR-WH's product forms
-- (`eqAbove_prod`, `fb`, `selbit`, `LvmQAsmArith2WhirBasis`). lvm2 roll 8 (B1): at `C_main`'s physical
-- `ν = CMain.nu20` (23; roll 7: 24).
import LvmShapeVN
import LvmQAsmArith2WhirBasis
import Mathlib.Tactic.IrreducibleDef

/-!
# The small claims at the rotated point

At a point `x` of `ν = CMain.nu20` coordinates (23 at B1), `x^σ := x.tail ‖ [x₀]` (`rotZ`). Every `C_main` claim
of a small child is a big-form claim at `x^σ`:

* **`onStackZB_reg`**: a block of at most `2^20` words, aligned, in `[4·2^20, (2^(ν−20) − 1)·2^20)` (`7·2^20`
  at ν = 23: tables, `T`, `KS`, `KSY2`, `X`): the same claim on the block moved down by `3·2^20` (`shiftB`);
* **`onStackZB_sum`**: a `sumClaim ν` of such parts (the `KS` link's sums, the typed regions): the parts moved
  down;
* **`onStackZB_dpt`**: a point claim on `D = ⟨22, 0⟩` at `z`: `κ(z) = (1 + z₁₈)(1 + z₁₉)` times the
  point claim on `D` at `z₀…z₁₇ ‖ z₂₀ z₂₁ ‖ 0 0`;
* **`onStackZB_ring`**: the tape's ring claim on `⟨ν, 0⟩` (point `pt` with `pt₂₂ … = 0`, the `ν − 22` block
  bits above `D`): the ring claim at `pt₀…pt₁₇ ‖ pt₂₀ pt₂₁ ‖ 0 0 ‖ 0…` (`ptZ`) with coefficients
  `c_k (1 + pt₁₈^{2^k})(1 + pt₁₉^{2^k})`.
-/

set_option autoImplicit false

namespace Lvm.QShape

open Lvm Lvm.Har Lvm.Shape

/-! ## The rotated point and the shifted block -/

/-- The small shape's terminal point: `x.tail ‖ [x₀]`. -/
def rotZ (x : List FE) : List FE := x.tail ++ [x.headD 0]

/-- `a − 3·2^20`, by cases on `a` (the role `irreducible_def`'s `opaque` wrapper had, which the gate rejects):
computable, and the kernel's whnf stops at a symbolic `a` (a stuck `Nat.casesOn`) instead of unfolding
`Nat.sub` against the literal `3·2^20` three million times. -/
def subHi : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) - 3 * 2 ^ 20

theorem subHi_eq (a : ℕ) : subHi a = a - 3 * 2 ^ 20 := by
  cases a with
  | zero => rfl
  | succ n => rfl

/-- A block moved down by `3·2^20`. -/
def shiftP (b : Placement) : Placement := ⟨b.variableCount, subHi b.index⟩

theorem shiftP_vc (b : Placement) : (shiftP b).variableCount = b.variableCount := by unfold shiftP; rfl
theorem shiftP_index (b : Placement) : (shiftP b).index = b.index - 3 * 2 ^ 20 := by unfold shiftP; exact subHi_eq _

/-- A block claim on the moved block. -/
def shiftB (c : BlockClaim) : BlockClaim := ⟨shiftP c.block, c.weight, c.value⟩

/-- **A regular block**: at most `2^20` words, aligned, in `[4·2^20, (2^(ν−20) − 1)·2^20)`, the big blocks
`4 … 2^(ν−20) − 2` that have a small counterpart (`regions`' `2^20` blocks; `[4·2^20, 7·2^20)` at B1's ν = 23,
V_S's room `TypedV.fitsMiniB`, `TNat.okB`). -/
def RegP (b : Placement) : Prop :=
  b.variableCount ≤ 20 ∧ b.index % 2 ^ b.variableCount = 0 ∧ 4 * 2 ^ 20 ≤ b.index ∧
    b.index < (2 ^ (CMain.nu20 - 20) - 1) * 2 ^ 20

instance (b : Placement) : Decidable (RegP b) := by unfold RegP; infer_instance

/-- The regular blocks' top at B1's ν = 23. -/
theorem regTop : (2 ^ (CMain.nu20 - 20) - 1) * 2 ^ 20 = 7 * 2 ^ 20 := rfl

/-- The number of `2^20` blocks above `D` with a small counterpart at B1's ν = 23. -/
theorem nBlk : 2 ^ (CMain.nu20 - 21) - 1 = 3 := rfl

/-! ## Bits -/

theorem fb_bit {a b : ℕ} (ha : a < 2) (hb : b < 2) : fb (a == 1) (eOfNat b) = if a = b then 1 else 0 := by
  interval_cases a <;> interval_cases b <;> simp [fb, eOfNat_zero, eOfNat_one, CharTwo.add_self_eq_zero]

theorem selbit_eq (blk : Placement) {i : ℕ} (hi : blk.variableCount ≤ i) :
    selbit blk i = ((blk.index >>> i) % 2 == 1) := by
  rw [selbit, ← Nat.shiftRight_add, Nat.add_sub_cancel' hi]

theorem shr_div (a i : ℕ) : a >>> i = a / 2 ^ i := Nat.shiftRight_eq_div_pow a i

/-- The top `ν − 20` factors of a selector against the constant bits of `h`. -/
theorem topK_eq (A h : ℕ) :
    (∏ j ∈ Finset.range (CMain.nu20 - 20), fb ((A >>> (20 + j)) % 2 == 1) (eOfNat ((h >>> j) % 2))) =
      if A / 2 ^ 20 % 2 ^ (CMain.nu20 - 20) = h % 2 ^ (CMain.nu20 - 20) then 1 else 0 := by
  rw [show CMain.nu20 - 20 = 3 from rfl]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [fb_bit (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)),
    fb_bit (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)),
    fb_bit (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]
  simp only [shr_div]
  norm_num
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ## A block claim at a relocated point -/

theorem getD_append_lo {l₁ l₂ : List FE} {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_hi {l₁ l₂ : List FE} (j : ℕ) :
    (l₁ ++ l₂).getD (l₁.length + j) 0 = l₂.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem selectorPoint_getD' {h n j : ℕ} (hj : j < n) : (selectorPoint h n).getD j 0 = eOfNat ((h >>> j) % 2) := by
  simp [selectorPoint, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]

theorem selectorPoint_length' (h n : ℕ) : (selectorPoint h n).length = n := by simp [selectorPoint]

/-- **A block claim on `lo ‖ sel(h, ν − 20)`** (`lo` the 20 low coordinates): the selector factors below
`20`, the top `ν − 20` against `h`'s bits, the weight. -/
theorem onStack_lohi (c : BlockClaim) (hv : c.block.variableCount ≤ 20) (lo : List FE) (hlo : lo.length = 20)
    (h : ℕ) :
    c.onStack.1 (lo ++ selectorPoint h (CMain.nu20 - 20)) =
      (∏ i ∈ Finset.Ico c.block.variableCount 20, fb (selbit c.block i) (lo.getD i 0)) *
        (if c.block.index / 2 ^ 20 % 2 ^ (CMain.nu20 - 20) = h % 2 ^ (CMain.nu20 - 20) then 1 else 0) *
          c.weight (lo.take c.block.variableCount) := by
  have hnu : CMain.nu20 = 23 := rfl
  have hl : (lo ++ selectorPoint h (CMain.nu20 - 20)).length = CMain.nu20 := by
    simp only [List.length_append, hlo, selectorPoint_length']; omega
  simp only [BlockClaim.onStack]
  rw [eqAbove_prod c.block _ (fun i => (lo ++ selectorPoint h (CMain.nu20 - 20)).getD i 0) (by omega)
      (fun _ _ => rfl), hl,
    ← Finset.prod_Ico_consecutive _ hv (by omega : 20 ≤ CMain.nu20), List.take_append_of_le_length (by omega),
    ← topK_eq]
  congr 2
  · exact Finset.prod_congr rfl fun i hi => by rw [getD_append_lo (by rw [hlo]; exact (Finset.mem_Ico.mp hi).2)]
  · rw [Finset.prod_Ico_eq_prod_range]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [selbit_eq _ (by omega), show 20 + j = lo.length + j by omega, getD_append_hi,
      selectorPoint_getD' (by omega)]

/-! ## Regular blocks -/

/-- An aligned block of at most `2^20` words ends inside its `2^20`-region. -/
theorem align_fit (b : Placement) (hv : b.variableCount ≤ 20) (ha : b.index % 2 ^ b.variableCount = 0) :
    b.index % 2 ^ 20 + 2 ^ b.variableCount ≤ 2 ^ 20 := by
  obtain ⟨vc, idx⟩ := b
  simp only at hv ha ⊢
  obtain ⟨e, he⟩ : 2 ^ vc ∣ 2 ^ 20 := Nat.pow_dvd_pow 2 hv
  have h1 : idx % 2 ^ 20 % 2 ^ vc = 0 := by rw [Nat.mod_mod_of_dvd _ ⟨e, he⟩]; exact ha
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h1
  have hlt := Nat.mod_lt idx (by positivity : 0 < 2 ^ 20)
  have hpos : 0 < 2 ^ vc := by positivity
  rw [hq, he] at hlt
  have hqe : q < e := Nat.lt_of_mul_lt_mul_left hlt
  rw [hq, he]
  calc 2 ^ vc * q + 2 ^ vc = 2 ^ vc * (q + 1) := by ring
    _ ≤ 2 ^ vc * e := Nat.mul_le_mul_left _ hqe

/-- **A regular block meets one region**: the `2^20`-region it lies in. -/
theorem filter_reg (b : Placement) (hb : RegP b) :
    regions.filter (meets b) = [(20, b.index / 2 ^ 20 * 2 ^ 20, (b.index / 2 ^ 20 - 3) * 2 ^ 20)] := by
  obtain ⟨hv, ha, h4, h11⟩ := hb
  rw [regTop] at h11
  have hf := align_fit b hv ha
  have hp : 1 ≤ 2 ^ b.variableCount := Nat.one_le_two_pow
  obtain ⟨H, hH⟩ : ∃ H, b.index / 2 ^ 20 = H := ⟨_, rfl⟩
  have hH1 : 4 ≤ H := by omega
  have hH2 : H < 7 := by omega
  rw [hH]
  have hc : ∀ r ∈ regions, meets b r = (r.2.1 / 2 ^ 20 == H) := by
    intro r hr
    simp only [regions, nBlk, List.mem_append, List.mem_map, List.mem_range] at hr
    rcases hr with ⟨l, hl, rfl⟩ | ⟨j, hj, rfl⟩
    · simp only [meets, Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ 20)]
      rw [show (l == H) = false by simp; omega]
      simp only [decide_eq_false_iff_not]
      omega
    · simp only [meets, Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ 20)]
      by_cases e : 4 + j = H
      · rw [show (4 + j == H) = true by simp [e]]; simp only [decide_eq_true_eq]; omega
      · rw [show (4 + j == H) = false by simp [e]]; simp only [decide_eq_false_iff_not]; omega
  rw [List.filter_congr hc]
  interval_cases H <;> rfl

theorem relocF_20 (x0 : FE) (xt : List FE) (hx : xt.length = CMain.nu20 - 1) (H os : ℕ) :
    relocF (x0 :: xt) (20, H * 2 ^ 20, os) = xt.take 20 ++ selectorPoint H (CMain.nu20 - 20) := by
  have hnu : CMain.nu20 = 23 := rfl
  simp only [relocF, List.tail_cons]
  rw [List.take_append_of_le_length (by omega), Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (by positivity)]

theorem getD_take_lt {l : List FE} {i m : ℕ} (hi : i < m) : (l.take m).getD i 0 = l.getD i 0 := getD_take' l 0 hi

/-- The top coordinates of a moved regular block at `x^σ`. -/
theorem top_shift (b : Placement) (hb : RegP b) (x0 : FE) (xt : List FE) (hx : xt.length = CMain.nu20 - 1) :
    ∏ i ∈ Finset.Ico 20 CMain.nu20, fb (selbit (shiftP b) i) ((xt ++ [x0]).getD i 0) =
      (1 - x0) * ∏ i ∈ Finset.Ico 20 (CMain.nu20 - 1),
        fb (selbit ⟨20, (b.index / 2 ^ 20 - 3) * 2 ^ 20⟩ i) (xt.getD i 0) := by
  obtain ⟨hv, -, h4, h11⟩ := hb
  rw [regTop] at h11
  have hxt : xt.length = 22 := hx
  have hv' : (shiftP b).variableCount ≤ 20 := by rw [shiftP_vc]; exact hv
  simp only [Finset.prod_Ico_eq_prod_range, show CMain.nu20 - 20 = 3 from rfl, show CMain.nu20 - 1 - 20 = 2 from rfl,
    Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [selbit_eq _ (by rw [shiftP_vc]; omega), selbit_eq _ (by rw [shiftP_vc]; omega),
    selbit_eq _ (by rw [shiftP_vc]; omega), selbit_eq _ (by simp), selbit_eq _ (by simp)]
  have g2 : (xt ++ [x0]).getD (20 + 2) 0 = x0 := by
    rw [show 20 + 2 = xt.length + 0 by omega, getD_append_hi]; rfl
  rw [getD_append_lo (by omega), getD_append_lo (by omega), g2]
  simp only [shiftP, shr_div, CharTwo.sub_eq_add, subHi_eq]
  have e0 : (b.index - 3 * 2 ^ 20) / 2 ^ (20 + 0) % 2 = ((b.index / 2 ^ 20 - 3) * 2 ^ 20) / 2 ^ (20 + 0) % 2 := by
    norm_num; omega
  have e1 : (b.index - 3 * 2 ^ 20) / 2 ^ (20 + 1) % 2 = ((b.index / 2 ^ 20 - 3) * 2 ^ 20) / 2 ^ (20 + 1) % 2 := by
    norm_num; omega
  have e2 : (b.index - 3 * 2 ^ 20) / 2 ^ (20 + 2) % 2 = 0 := by norm_num; omega
  rw [e0, e1, e2]
  simp only [show ((0 : ℕ) == 1) = false from rfl, fb, Bool.false_eq_true, ite_false]
  ring

/-- **`onStackZB` of a regular block claim** is the moved claim at `x^σ`. -/
theorem onStackZB_reg (c : BlockClaim) (t : FE) (hb : RegP c.block) (x : List FE) (hx : x.length = CMain.nu20) :
    (onStackZB c t).1 x = (shiftB c).onStack.1 (rotZ x) := by
  cases x with
  | nil => simp at hx
  | cons x0 xt =>
  have hnu : CMain.nu20 = 23 := rfl
  have hxt : xt.length = CMain.nu20 - 1 := by simp only [List.length_cons] at hx; omega
  have hv := hb.1
  simp only [onStackZB, filter_reg _ hb, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.headD_cons, List.tail_cons]
  rw [relocF_20 x0 xt hxt, onStack_lohi c hv _ (by simp only [List.length_take]; omega), if_pos rfl, mul_one,
    List.take_take, min_eq_left (by omega)]
  simp only [BlockClaim.onStack, shiftB, rotZ, List.tail_cons, List.headD_cons]
  have hl : (xt ++ [x0]).length = CMain.nu20 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rw [eqAbove_prod (shiftP c.block) (xt ++ [x0]) (fun i => (xt ++ [x0]).getD i 0) (by rw [hl, shiftP_vc]; omega)
      (fun _ _ => rfl),
    eqAbove_prod ⟨20, (c.block.index / 2 ^ 20 - 3) * 2 ^ 20⟩ xt (fun i => xt.getD i 0) (show 20 ≤ xt.length by omega)
      (fun _ _ => rfl), hl, hxt, List.take_append_of_le_length (by rw [shiftP_vc]; omega)]
  have hv' : (shiftP c.block).variableCount = c.block.variableCount := shiftP_vc _
  rw [← Finset.prod_Ico_consecutive _ (by rw [hv']; exact hv) (by omega : 20 ≤ CMain.nu20), top_shift _ hb x0 xt hxt]
  have elo : ∏ i ∈ Finset.Ico (shiftP c.block).variableCount 20, fb (selbit (shiftP c.block) i) ((xt ++ [x0]).getD i 0) =
      ∏ i ∈ Finset.Ico c.block.variableCount 20, fb (selbit c.block i) ((xt.take 20).getD i 0) := by
    rw [hv']
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
    rw [getD_append_lo (by omega), getD_take_lt h2, selbit_eq _ (by rw [hv']; exact h1), selbit_eq _ h1]
    simp only [shiftP, shr_div, subHi_eq]
    have : (c.block.index - 3 * 2 ^ 20) / 2 ^ i % 2 = c.block.index / 2 ^ i % 2 := by
      have h4 := hb.2.2.1
      have hk : 3 * 2 ^ 20 = 2 ^ i * (3 * 2 ^ (20 - i)) := by
        rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (by omega)]
      have hidx : c.block.index = (c.block.index - 3 * 2 ^ 20) + 2 ^ i * (3 * 2 ^ (20 - i)) := by
        rw [← hk]; omega
      have he : 3 * 2 ^ (20 - i) % 2 = 0 := by
        rw [Nat.mul_mod, Nat.two_pow_mod_two_eq_zero.mpr (by omega)]
      conv_rhs => rw [hidx]
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.add_mod, he, add_zero, Nat.mod_mod]
    rw [this]
  rw [elo, shiftP_vc]
  ring

/-! ## Sums of regular parts -/

/-- `onStackZF`'s weight on a weight function (the region sum at `x`). -/
def zW (x : List FE) (w : List FE → FE) : FE :=
  (1 - x.headD 0) * (regions.map fun r ↦ (⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * w (relocF x r)).sum

theorem relocF_length (x : List FE) (hx : x.length = CMain.nu20) (r : ℕ × ℕ × ℕ) (hr : r.1 ≤ CMain.nu20) :
    (relocF x r).length = CMain.nu20 := by
  have hnu : CMain.nu20 = 23 := rfl
  simp only [relocF, List.length_append, List.length_take, List.length_replicate, selectorPoint_length',
    List.length_tail, hx, sLog, CMain.nu20s]
  omega

theorem regions_k (r : ℕ × ℕ × ℕ) (hr : r ∈ regions) : r.1 ≤ CMain.nu20 := by
  simp only [regions, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨l, -, rfl⟩ | ⟨j, -, rfl⟩ <;> simp [CMain.nu20]

theorem zW_congr (x : List FE) (hx : x.length = CMain.nu20) {w w' : List FE → FE}
    (h : ∀ y : List FE, y.length = CMain.nu20 → w y = w' y) : zW x w = zW x w' := by
  unfold zW
  congr 2
  exact List.map_congr_left fun r hr ↦ by rw [h _ (relocF_length x hx r (regions_k r hr))]

theorem zW_add (x : List FE) (f g : List FE → FE) : zW x (fun y ↦ f y + g y) = zW x f + zW x g := by
  simp only [zW, mul_add, List.sum_map_add]

theorem zW_smul (x : List FE) (a : FE) (f : List FE → FE) : zW x (fun y ↦ a * f y) = a * zW x f := by
  simp only [zW]
  rw [List.map_congr_left (fun r _ ↦ (mul_left_comm _ a _ : (⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (a * f (relocF x r)) = _)),
    List.sum_map_mul_left]
  ring

theorem zW_zero (x : List FE) : zW x (fun _ ↦ 0) = 0 := by simp [zW]

theorem zW_sum (x : List FE) {ι : Type} (l : List ι) (c : ι → FE) (g : ι → List FE → FE) :
    zW x (fun y ↦ (l.map fun i ↦ c i * g i y).sum) = (l.map fun i ↦ c i * zW x (g i)).sum := by
  induction l with
  | nil => exact zW_zero x
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [zW_add x (fun y ↦ c i * g i y), zW_smul, ih]

/-- `selectorPoint (4 l) (ν − 18)` is two zeros then `l`'s `ν − 20` bits. -/
theorem sel4 (l : ℕ) :
    selectorPoint ((l * 2 ^ 20) >>> 18) (CMain.nu20 - 18) = [0, 0] ++ selectorPoint l (CMain.nu20 - 20) := by
  have e : (l * 2 ^ 20) >>> 18 = l * 4 := by
    rw [Nat.shiftRight_eq_div_pow, show l * 2 ^ 20 = l * 4 * 2 ^ 18 by ring, Nat.mul_div_cancel _ (by positivity)]
  rw [e, show CMain.nu20 - 18 = 5 from rfl, show CMain.nu20 - 20 = 3 from rfl]
  simp only [selectorPoint, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Nat.shiftRight_eq_div_pow, List.cons.injEq, and_true]
  rw [← eOfNat_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;> omega

/-- The region's relocated point in `lo ‖ sel(h, ν − 20)` form. -/
theorem relocF_lohi (x0 : FE) (xt : List FE) (hx : xt.length = CMain.nu20 - 1) (r : ℕ × ℕ × ℕ) (hr : r ∈ regions) :
    ∃ lo, lo.length = 20 ∧ relocF (x0 :: xt) r = lo ++ selectorPoint (r.2.1 / 2 ^ 20) (CMain.nu20 - 20) := by
  have hnu : CMain.nu20 = 23 := rfl
  simp only [regions, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨l, -, rfl⟩ | ⟨j, -, rfl⟩
  · have hl : (xt.take 18 ++ [(0 : FE), 0]).length = 20 := by
      simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]; omega
    refine ⟨xt.take 18 ++ [0, 0], hl, ?_⟩
    simp only [relocF, List.tail_cons]
    rw [List.take_append_of_le_length (by omega), Nat.mul_div_cancel _ (by positivity), sel4, List.append_assoc]
  · refine ⟨xt.take 20, by simp only [List.length_take]; omega, ?_⟩
    rw [relocF_20 x0 xt hx, Nat.mul_div_cancel _ (by positivity)]

/-- **The regions a regular block misses contribute `0`.** -/
theorem term_miss (c : BlockClaim) (hb : RegP c.block) (x : List FE) (hx : x.length = CMain.nu20) (r : ℕ × ℕ × ℕ)
    (hr : r ∈ regions) (hm : meets c.block r = false) : c.onStack.1 (relocF x r) = 0 := by
  cases x with
  | nil => simp at hx
  | cons x0 xt =>
  have hnu : CMain.nu20 = 23 := rfl
  have hxt : xt.length = CMain.nu20 - 1 := by simp only [List.length_cons] at hx; omega
  obtain ⟨lo, hlo, e⟩ := relocF_lohi x0 xt hxt r hr
  rw [e, onStack_lohi c hb.1 lo hlo, if_neg, mul_zero, zero_mul]
  obtain ⟨hv, ha, h4, h11⟩ := hb
  rw [regTop] at h11
  have hf := align_fit c.block hv ha
  have hp : 1 ≤ 2 ^ c.block.variableCount := Nat.one_le_two_pow
  simp only [regions, nBlk, List.mem_append, List.mem_map, List.mem_range] at hr
  rw [show 2 ^ (CMain.nu20 - 20) = 8 from rfl]
  rcases hr with ⟨l, hl, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ 20)]; omega
  · simp only [meets, decide_eq_false_iff_not] at hm
    simp only [Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ 20)]; omega

theorem sum_filter_of_zero {α : Type} (p : α → Bool) (f : α → FE) :
    ∀ L : List α, (∀ r ∈ L, p r = false → f r = 0) → ((L.filter p).map f).sum = (L.map f).sum
  | [], _ => rfl
  | a :: L, h => by
    have ih := sum_filter_of_zero p f L fun r hr ↦ h r (List.mem_cons_of_mem _ hr)
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
    · rw [List.filter_cons_of_neg ha, List.map_cons, List.sum_cons, ih,
        h a List.mem_cons_self (by simpa using ha), zero_add]

/-- `onStackZB` of a regular block claim is its full region sum. -/
theorem zW_eq_zb (c : BlockClaim) (t : FE) (hb : RegP c.block) (x : List FE) (hx : x.length = CMain.nu20) :
    zW x c.onStack.1 = (onStackZB c t).1 x := by
  unfold zW onStackZB
  dsimp only
  rw [sum_filter_of_zero (meets c.block) _ regions fun r hr hm ↦ by
    rw [term_miss c hb x hx r hr hm, mul_zero]]

/-- A `sumClaim` part as a point claim. -/
def partB (e : FE × Placement × List FE) : BlockClaim := BlockClaim.point e.2.1 e.2.2 0

theorem sumClaim_onStack (parts : List (FE × Placement × List FE)) (v : FE) (y : List FE)
    (hy : y.length = CMain.nu20) :
    (sumClaim CMain.nu20 parts v).onStack.1 y = (parts.map fun e ↦ e.1 * (partB e).onStack.1 y).sum := by
  simp only [BlockClaim.onStack, sumClaim, partB, BlockClaim.point, sumE_eq]
  have h1 : (⟨CMain.nu20, 0⟩ : Placement).eqAbove y = 1 := by
    simp [Placement.eqAbove, hy, selectorPoint, eqEval]
  rw [h1, one_mul, List.take_of_length_le (by omega)]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by ring)

/-- Every region meets `⟨ν, 0⟩`. -/
theorem filter_nu : regions.filter (meets ⟨CMain.nu20, 0⟩) = regions := by
  refine List.filter_eq_self.mpr fun r hr ↦ ?_
  simp only [regions, nBlk, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨l, hl, rfl⟩ | ⟨j, hj, rfl⟩ <;> simp only [meets, decide_eq_true_eq, CMain.nu20] <;> omega

/-- **`onStackZB` of a sum of regular parts** (the `KS` link's sums): the parts moved down, at `x^σ`. -/
theorem onStackZB_sum (parts : List (FE × Placement × List FE)) (v t : FE) (hp : ∀ e ∈ parts, RegP e.2.1)
    (x : List FE) (hx : x.length = CMain.nu20) :
    (onStackZB (sumClaim CMain.nu20 parts v) t).1 x =
      (sumClaim CMain.nu20 (parts.map fun e ↦ (e.1, shiftP e.2.1, e.2.2)) v).onStack.1 (rotZ x) := by
  have hr : (rotZ x).length = CMain.nu20 := by
    cases x with
    | nil => simp at hx
    | cons x0 xt => simp [rotZ]; simpa using hx
  have e1 : (onStackZB (sumClaim CMain.nu20 parts v) t).1 x = zW x (sumClaim CMain.nu20 parts v).onStack.1 := by
    unfold zW onStackZB
    rw [show (sumClaim CMain.nu20 parts v).block = ⟨CMain.nu20, 0⟩ from rfl, filter_nu]
  rw [e1, zW_congr x hx (sumClaim_onStack parts v), zW_sum, sumClaim_onStack _ v _ hr, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
  simp only [Function.comp_apply]
  rw [zW_eq_zb (partB e) 0 (hp e he) x hx, onStackZB_reg (partB e) 0 (hp e he) x hx]
  simp only [shiftB, partB, BlockClaim.point]

/-! ## `D`'s point claims -/

theorem foldl_mul_eq (l : List FE) (a : FE) : l.foldl (· * ·) a = a * l.foldl (· * ·) 1 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp only [List.foldl_cons]; rw [ih (a * b), ih (1 * b)]; ring

theorem eqEval_app (l₁ l₂ r₁ r₂ : List FE) (h : l₁.length = r₁.length) :
    eqEval (l₁ ++ l₂) (r₁ ++ r₂) = eqEval l₁ r₁ * eqEval l₂ r₂ := by
  simp only [eqEval, List.zipWith_append h, List.foldl_append]
  rw [foldl_mul_eq _ (List.foldl _ 1 _)]

theorem split4 (z : List FE) (n : ℕ) (h : z.length = n + 4) :
    ∃ zl a b c d, z = zl ++ [a, b, c, d] ∧ zl.length = n := by
  have hd : (z.drop n).length = 4 := by simp [h]
  obtain ⟨a, b, c, d, hd'⟩ : ∃ a b c d, z.drop n = [a, b, c, d] := by
    rcases hdd : z.drop n with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> rw [hdd] at hd <;>
      simp at hd
    exact ⟨a, b, c, d, rfl⟩
  exact ⟨z.take n, a, b, c, d, by rw [← hd', List.take_append_drop], by simp [h]⟩

theorem split5 (z : List FE) (n : ℕ) (h : z.length = n + 5) :
    ∃ zl a b c d e, z = zl ++ [a, b, c, d, e] ∧ zl.length = n := by
  have hd : (z.drop n).length = 5 := by simp [h]
  obtain ⟨a, b, c, d, e, hd'⟩ : ∃ a b c d e, z.drop n = [a, b, c, d, e] := by
    rcases hdd : z.drop n with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, l⟩⟩⟩⟩⟩⟩ <;> rw [hdd] at hd <;>
      simp at hd
    exact ⟨a, b, c, d, e, rfl⟩
  exact ⟨z.take n, a, b, c, d, e, by rw [← hd', List.take_append_drop], by simp [h]⟩

theorem eqAbove_app (k idx : ℕ) (lo hi : List FE) (hlo : lo.length = k) :
    (⟨k, idx⟩ : Placement).eqAbove (lo ++ hi) = eqEval (selectorPoint (idx >>> k) hi.length) hi := by
  simp only [Placement.eqAbove, List.length_append, hlo, Nat.add_sub_cancel_left]
  rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]

theorem split6 (z : List FE) (n : ℕ) (h : z.length = n + 6) :
    ∃ zl a b c d e f, z = zl ++ [a, b, c, d, e, f] ∧ zl.length = n := by
  have hd : (z.drop n).length = 6 := by simp [h]
  obtain ⟨a, b, c, d, e, f, hd'⟩ : ∃ a b c d e f, z.drop n = [a, b, c, d, e, f] := by
    rcases hdd : z.drop n with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, l⟩⟩⟩⟩⟩⟩⟩ <;>
      rw [hdd] at hd <;> simp at hd
    exact ⟨a, b, c, d, e, f, rfl⟩
  exact ⟨z.take n, a, b, c, d, e, f, by rw [← hd', List.take_append_drop], by simp [h]⟩

/-- The four `D` regions. -/
theorem filter_22 : regions.filter (meets ⟨22, 0⟩) = (List.range 4).map fun l ↦ (18, l * 2 ^ 20, l * 2 ^ 18) := by
  rw [regions, List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.append_nil]
  · intro r hr
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    simp only [meets, decide_eq_true_eq]; omega
  · intro r hr
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨l, hl, rfl⟩ := hr
    simp only [meets, decide_eq_true_eq]; omega

/-- `D`'s scale of a small point claim: `(1 + z₁₈)(1 + z₁₉)`. -/
def kappaD (z : List FE) : FE := (1 + z.getD 18 0) * (1 + z.getD 19 0)

/-- `D`'s small point: `z₀…z₁₇ ‖ z₂₀ z₂₁ ‖ 0 0`. -/
def dzD (z : List FE) : List FE := z.take 18 ++ [z.getD 20 0, z.getD 21 0, 0, 0]

/-- `Σ_{l < 4}` of `D`'s relocated factors (char 2). -/
theorem dsum (a b z0 z1 : FE) :
    (1 + 0 + a) * (1 + 0 + b) * ((1 + z0 + 0) * (1 + z1 + 0)) +
        (1 + 1 + a) * (1 + 0 + b) * ((1 + z0 + 1) * (1 + z1 + 0)) +
        (1 + 0 + a) * (1 + 1 + b) * ((1 + z0 + 0) * (1 + z1 + 1)) +
        (1 + 1 + a) * (1 + 1 + b) * ((1 + z0 + 1) * (1 + z1 + 1)) =
      (1 + z0 + a) * (1 + z1 + b) := by
  linear_combination ((2 + a + z0 + a * z0) * (1 + b + z1) + (2 + b + z1 + b * z1) * (1 + a + z0) +
    2 * (2 + a + z0 + a * z0) * (2 + b + z1 + b * z1)) * (CharTwo.two_eq_zero : (2 : FE) = 0)

/-- **`onStackZB` of a `D` point claim**: `κ(z)` times the point claim on `D` at `dzD z`, at `x^σ`. -/
theorem onStackZB_dpt (z : List FE) (hz : z.length = 22) (v t : FE) (x : List FE) (hx : x.length = CMain.nu20) :
    (onStackZB (BlockClaim.point ⟨22, 0⟩ z v) t).1 x =
      kappaD z * (BlockClaim.point ⟨22, 0⟩ (dzD z) v).onStack.1 (rotZ x) := by
  obtain ⟨zl, z18, z19, z20, z21, rfl, hzl⟩ := split4 z 18 (by omega)
  cases x with
  | nil => simp at hx
  | cons x0 xt =>
  have hnu : CMain.nu20 = 23 := rfl
  obtain ⟨lo, a, b, c, d, rfl, hlo⟩ := split4 xt 18 (by simp only [List.length_cons] at hx; omega)
  have k1 : kappaD (zl ++ [z18, z19, z20, z21]) = (1 + z18) * (1 + z19) := by
    simp [kappaD, List.getD_eq_getElem?_getD, List.getElem?_append_right, hzl]
  have k2 : dzD (zl ++ [z18, z19, z20, z21]) = zl ++ [z20, z21, 0, 0] := by
    simp [dzD, List.getD_eq_getElem?_getD, List.getElem?_append_right, hzl, List.take_append_of_le_length]
  rw [k1, k2]
  simp only [onStackZB, BlockClaim.point, filter_22, rotZ, List.tail_cons, List.headD_cons, BlockClaim.onStack,
    List.map_map]
  have hr : ∀ l, relocF (x0 :: (lo ++ [a, b, c, d])) (18, l * 2 ^ 20, l * 2 ^ 18) =
      lo ++ ([0, 0] ++ selectorPoint l (CMain.nu20 - 20)) := by
    intro l
    simp only [relocF, List.tail_cons, List.append_assoc]
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega), sel4]
  simp only [Function.comp_def, hr, eqAbove_app 18 _ lo _ hlo]
  have h1 : ∀ hi : List FE, hi.length = 5 → (⟨22, 0⟩ : Placement).eqAbove (lo ++ hi) = eqEval [0] (hi.drop 4) := by
    intro hi hhi
    rw [show lo ++ hi = (lo ++ hi.take 4) ++ hi.drop 4 by simp, eqAbove_app 22 0 _ _ (by simp [hlo, hhi])]
    simp [hhi, selectorPoint, List.range_succ, eOfNat_zero]
  have h2 : ∀ hi : List FE, hi.length = 5 → List.take 22 (lo ++ hi) = lo ++ hi.take 4 := by
    intro hi hhi
    rw [show 22 = lo.length + 4 by omega, List.take_append]
    simp
  rw [List.append_assoc, h1 _ (by simp), h2 _ (by simp)]
  simp only [show CMain.nu20 - 20 = 3 from rfl]
  simp (disch := simp [selectorPoint]) only [h1, h2]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append, List.sum_cons,
    List.sum_nil, add_zero]
  simp only [eqEval_app _ _ _ _ (by rw [hzl, hlo] : zl.length = lo.length)]
  simp only [show CMain.nu20 - 20 = 3 from rfl, CharTwo.sub_eq_add, selectorPoint, Nat.reducePow, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, Nat.shiftRight_zero, List.map_nil, Nat.zero_shiftRight, Nat.zero_mod, eOfNat_zero,
    Nat.reduceShiftRight, Nat.mod_succ, eOfNat_one, Nat.reduceMul, Nat.mod_self, Nat.reduceMod, List.drop_succ_cons,
    List.drop_zero, List.take_succ_cons, List.take_zero]
  generalize eqEval zl lo = A
  simp only [eqEval, List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil, one_mul, add_zero,
    mul_one, List.sum_cons, List.sum_nil]
  generalize 1 + x0 = X0
  generalize 1 + c = C1
  generalize 1 + d = D1
  generalize 1 + z18 = Z18
  generalize 1 + z19 = Z19
  linear_combination X0 * C1 * D1 * A * Z18 * Z19 * dsum a b z20 z21

/-! ## The tape's ring claim -/

/-- The 20-regions miss `D`: `⟨22, 0⟩`'s weight vanishes there. -/
theorem dpt_full (z : List FE) (v : FE) (x : List FE) (hx : x.length = CMain.nu20) :
    zW x (BlockClaim.point ⟨22, 0⟩ z v).onStack.1 = (onStackZB (BlockClaim.point ⟨22, 0⟩ z v) 0).1 x := by
  unfold zW onStackZB
  dsimp only
  rw [show (BlockClaim.point ⟨22, 0⟩ z v).block = ⟨22, 0⟩ from rfl, filter_22, regions, List.map_append,
    List.sum_append, nBlk]
  cases x with
  | nil => simp at hx
  | cons x0 xt =>
  have hnu : CMain.nu20 = 23 := rfl
  have hxt : xt.length = CMain.nu20 - 1 := by simp only [List.length_cons] at hx; omega
  have h0 : ∀ j < 3, (BlockClaim.point ⟨22, 0⟩ z v).onStack.1
      (relocF (x0 :: xt) (20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20)) = 0 := by
    intro j hj
    rw [relocF_20 x0 xt hxt, show CMain.nu20 - 20 = 3 from rfl]
    simp only [BlockClaim.onStack, BlockClaim.point]
    have e : xt.take 20 ++ selectorPoint (4 + j) 3 =
        (xt.take 20 ++ (selectorPoint (4 + j) 3).take 2) ++ (selectorPoint (4 + j) 3).drop 2 := by
      rw [List.append_assoc, List.take_append_drop]
    rw [e, eqAbove_app 22 0 _ _ (by simp only [List.length_append, List.length_take, selectorPoint_length']; omega)]
    interval_cases j <;> simp [selectorPoint, List.range_succ, eqEval, eOfNat_zero, eOfNat_one, CharTwo.add_self_eq_zero]
  rw [List.map_congr_left (l := (List.range 3).map _) (g := fun _ ↦ 0) fun r hr ↦ by
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    simp only; rw [h0 j hj, mul_zero]]
  simp [Function.comp_def]

/-- `F`'s ring weight as a sum of `eq`'s at the Frobenius powers of the point. -/
theorem ringWeight_eqE (r y cs : List FE) (hl : r.length = y.length) :
    ringWeight r y cs = ∑ i ∈ Finset.range cs.length, cs.getD i 0 * eqEval (r.map (· ^ 2 ^ i)) y := by
  rw [Lvm.Loop.QRing.ringWeight_sum r y cs hl]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Lvm.Loop.Build.eqEval_prod _ _ (by simp [hl]), List.length_map]
  congr 1
  refine Finset.prod_congr rfl fun n hn ↦ ?_
  have hn' := Finset.mem_range.mp hn
  simp [Lvm.Loop.QRing.wf, List.getD_eq_getElem?_getD, List.getElem?_map, hn']

theorem zW_fsum (x : List FE) (n : ℕ) (c : ℕ → FE) (g : ℕ → List FE → FE) :
    zW x (fun y ↦ ∑ i ∈ Finset.range n, c i * g i y) = ∑ i ∈ Finset.range n, c i * zW x (g i) := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact zW_zero x
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [zW_add x (fun y ↦ ∑ i ∈ Finset.range n, c i * g i y), zW_smul, ih]

/-- The small ring's coefficients: `c_k (1 + pt₁₈^{2^k})(1 + pt₁₉^{2^k})`. -/
def csZ (pt cs : List FE) : List FE :=
  (List.range cs.length).map fun k ↦ cs.getD k 0 * kappaD (pt.map (· ^ 2 ^ k))

/-- The small ring's point: `pt₀…pt₁₇ ‖ pt₂₀ pt₂₁ ‖ 0 0 ‖ 0^(ν − 22)` (`D`'s small point, then the block bits). -/
def ptZ (pt : List FE) : List FE := dzD pt ++ List.replicate (CMain.nu20 - 22) 0

theorem selectorPoint_zero (n : ℕ) : selectorPoint 0 n = List.replicate n 0 := by
  refine List.ext_getElem (by simp [selectorPoint]) fun i h1 h2 ↦ ?_
  simp [selectorPoint, eOfNat_zero]

/-- A point on the stack that is `0` above `D` is the point claim on `D`. -/
theorem eqEval_dpt (ρ y : List FE) (hρ : ρ.length = CMain.nu20) (hy : y.length = CMain.nu20)
    (h0 : ρ.drop 22 = List.replicate (CMain.nu20 - 22) 0) (v : FE) :
    eqEval ρ y = (BlockClaim.point ⟨22, 0⟩ (ρ.take 22) v).onStack.1 y := by
  have hnu : CMain.nu20 = 23 := rfl
  simp only [BlockClaim.point, BlockClaim.onStack, Placement.eqAbove, Nat.zero_shiftRight, selectorPoint_zero, hy]
  conv_lhs => rw [← List.take_append_drop 22 ρ, ← List.take_append_drop 22 y]
  have hl : (ρ.take 22).length = (y.take 22).length := by simp only [List.length_take]; omega
  rw [eqEval_app _ _ _ _ hl, h0]
  ring

/-- **`onStackZB` of the tape's ring claim** (`pt` zero above `D`): the ring claim at `ptZ pt` with the
coefficients `csZ pt cs`, at `x^σ`. -/
theorem onStackZB_ring (pt cs : List FE) (hpt : pt.length = CMain.nu20)
    (h0 : pt.drop 22 = List.replicate (CMain.nu20 - 22) 0) (v t : FE) (x : List FE) (hx : x.length = CMain.nu20) :
    (onStackZB ⟨⟨CMain.nu20, 0⟩, fun y ↦ ringWeight pt y cs, v⟩ t).1 x =
      (⟨⟨CMain.nu20, 0⟩, fun y ↦ ringWeight (ptZ pt) y (csZ pt cs), v⟩ : BlockClaim).onStack.1 (rotZ x) := by
  have hnu : CMain.nu20 = 23 := rfl
  have hr : (rotZ x).length = CMain.nu20 := by
    cases x with
    | nil => simp at hx
    | cons x0 xt => simp [rotZ]; simpa using hx
  have hN : ∀ y : List FE, y.length = CMain.nu20 → (⟨CMain.nu20, 0⟩ : Placement).eqAbove y = 1 := fun y hy ↦ by
    simp [Placement.eqAbove, hy, selectorPoint, eqEval]
  have hpow : ∀ i, (0 : FE) ^ 2 ^ i = 0 := fun i ↦ zero_pow (by positivity)
  set ρ : ℕ → List FE := fun k ↦ pt.map (· ^ 2 ^ k) with hρdef
  have hρl : ∀ k, (ρ k).length = CMain.nu20 := fun k ↦ by simp [hρdef, hpt]
  have g0 : ∀ k, (ρ k).drop 22 = List.replicate (CMain.nu20 - 22) 0 := fun k ↦ by
    simp only [hρdef, ← List.map_drop, h0, List.map_replicate, hpow]
  have e1 : (onStackZB ⟨⟨CMain.nu20, 0⟩, fun y ↦ ringWeight pt y cs, v⟩ t).1 x =
      zW x (⟨⟨CMain.nu20, 0⟩, fun y ↦ ringWeight pt y cs, v⟩ : BlockClaim).onStack.1 := by
    unfold zW onStackZB; dsimp only; rw [filter_nu]
  rw [e1, zW_congr x hx (w' := fun y ↦ ∑ i ∈ Finset.range cs.length,
      cs.getD i 0 * (BlockClaim.point ⟨22, 0⟩ ((ρ i).take 22) 0).onStack.1 y) fun y hy ↦ by
    simp only [BlockClaim.onStack]
    rw [hN y hy, one_mul, List.take_of_length_le (by omega), ringWeight_eqE _ y cs (by rw [hpt, hy])]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [eqEval_dpt _ y (hρl i) hy (g0 i) 0]; rfl]
  rw [zW_fsum]
  have hpzl : (ptZ pt).length = CMain.nu20 := by
    simp only [ptZ, dzD, List.length_append, List.length_take, List.length_cons, List.length_nil,
      List.length_replicate]; omega
  have hcz : (csZ pt cs).length = cs.length := by simp [csZ]
  have eR : (⟨⟨CMain.nu20, 0⟩, fun y ↦ ringWeight (ptZ pt) y (csZ pt cs), v⟩ : BlockClaim).onStack.1 (rotZ x) =
      ∑ i ∈ Finset.range cs.length, (csZ pt cs).getD i 0 * eqEval ((ptZ pt).map (· ^ 2 ^ i)) (rotZ x) := by
    simp only [BlockClaim.onStack]
    rw [hN _ hr, one_mul, List.take_of_length_le (by omega), ringWeight_eqE _ _ _ (by rw [hpzl, hr]), hcz]
  rw [eR]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  have hl22 : ((ρ i).take 22).length = 22 := by simp only [List.length_take, hρl]; omega
  rw [dpt_full _ 0 x hx, onStackZB_dpt _ hl22 0 0 x hx]
  have ec : (csZ pt cs).getD i 0 = cs.getD i 0 * kappaD (ρ i) := by
    simp [csZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi', hρdef]
  have ek : kappaD ((ρ i).take 22) = kappaD (ρ i) := by
    simp [kappaD, List.getD_eq_getElem?_getD, List.getElem?_take]
  have hzl : ((ptZ pt).map (· ^ 2 ^ i)).length = CMain.nu20 := by rw [List.length_map, hpzl]
  have hdz : (dzD pt).length = 22 := by
    simp only [dzD, List.length_append, List.length_take, List.length_cons, List.length_nil]; omega
  have hz0 : ((ptZ pt).map (· ^ 2 ^ i)).drop 22 = List.replicate (CMain.nu20 - 22) 0 := by
    rw [← List.map_drop, ptZ, List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append]
    simp only [List.map_replicate, hpow]
  have hd : ((ptZ pt).map (· ^ 2 ^ i)).take 22 = dzD ((ρ i).take 22) := by
    have h18 : ((pt.take 18).map (· ^ 2 ^ i)).length = 18 := by
      simp only [List.length_map, List.length_take]; omega
    have g : ∀ j, j < 22 → ((ρ i).take 22).getD j 0 = (pt.getD j 0) ^ 2 ^ i := by
      intro j h2
      rw [getD_take_lt h2]
      simp [hρdef, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (show j < pt.length by omega)]
    have ht : ((ρ i).take 22).take 18 = (pt.take 18).map (· ^ 2 ^ i) := by
      rw [List.take_take, min_eq_left (by norm_num), hρdef, List.map_take]
    rw [dzD, ht, g 20 (by norm_num), g 21 (by norm_num), ptZ, dzD]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate, hpow]
    rw [List.take_append_of_le_length (by rw [List.length_append, h18]; simp),
      List.take_of_length_le (by rw [List.length_append, h18]; simp)]
  rw [ec, ek, eqEval_dpt _ _ hzl hr hz0 0, hd]
  ring

end Lvm.QShape
