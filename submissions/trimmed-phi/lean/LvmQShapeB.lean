-- New for lvm2 (CR-Q, roll 7 SH2-Z; CR-DES §1.5 circuit side): the batched basis of `C_main`'s opening in
-- both shapes. The regular claims' terms come in pairs (the big key, the moved key, one leaf); the trie is cut
-- at depth 20: the subtries below are built once per top pair, the top four levels twice (big and moved keys)
-- and muxed. Adapted from HAR-WH's `basisG`/`claimTerms` (`LvmQAsmArith2WhirBasis`).
import LvmShapeVN
import LvmQAsmArith2WhirBasis
import Mathlib.Tactic.IrreducibleDef

-- ===== merged from `LvmQShapeF` (GOLF module merge: `LvmQShapeF.lean` is now a stub importing `LvmQShapeB`) =====
section
-- New for lvm2 (CR-Q, roll 7 SH2-Z; CR-DES §1.5 circuit side): `V_S`'s small claims (`onStackZB`,
-- `LvmShapeVN`) evaluated at WHIR's terminal point as big-form claims at the rotated point
-- `x^σ = x.tail ‖ x₀`: what the circuit computes with its muxed coordinates. Reuses HAR-WH's product forms
-- (`eqAbove_prod`, `fb`, `selbit`, `LvmQAsmArith2WhirBasis`). lvm2 roll 8 (B1): at `C_main`'s physical
-- `ν = CMain.nu20` (23; roll 7: 24).

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
  rw [eqAbove_prod c.block _ (fun i => (lo ++ selectorPoint h (CMain.nu20 - 20)).getD i 0) (by (clear * - hv hnu hl; omega))
      (fun _ _ => rfl), hl,
    ← Finset.prod_Ico_consecutive _ hv (by (clear * - hnu; omega) : 20 ≤ CMain.nu20), List.take_append_of_le_length (by (clear * - hv hlo; omega)),
    ← topK_eq]
  congr 2
  · exact Finset.prod_congr rfl fun i hi => by rw [getD_append_lo (by rw [hlo]; exact (Finset.mem_Ico.mp hi).2)]
  · rw [Finset.prod_Ico_eq_prod_range]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [selbit_eq _ (by (clear * - hv; omega)), show 20 + j = lo.length + j by (clear * - hlo; omega), getD_append_hi,
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
  have hH1 : 4 ≤ H := by (clear * - h4 h11 hH; omega)
  have hH2 : H < 7 := by (clear * - h4 h11 hH; omega)
  rw [hH]
  have hc : ∀ r ∈ regions, meets b r = (r.2.1 / 2 ^ 20 == H) := by
    intro r hr
    simp only [regions, nBlk, List.mem_append, List.mem_map, List.mem_range] at hr
    rcases hr with ⟨l, hl, rfl⟩ | ⟨j, hj, rfl⟩
    · simp only [meets, Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ 20)]
      rw [show (l == H) = false by simp; (clear * - hH1 hH2 hl; omega)]
      simp only [decide_eq_false_iff_not]
      (clear * - h4 h11 hl; omega)
    · simp only [meets, Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ 20)]
      by_cases e : 4 + j = H
      · rw [show (4 + j == H) = true by simp [e]]; simp only [decide_eq_true_eq]; (clear * - ha hH e; omega)
      · rw [show (4 + j == H) = false by simp [e]]; simp only [decide_eq_false_iff_not]; (clear * - hf hH e; omega)
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
  rw [selbit_eq _ (by rw [shiftP_vc]; omega), selbit_eq _ (by rw [shiftP_vc]; (clear * - hv; omega)),
    selbit_eq _ (by rw [shiftP_vc]; (clear * - hv; omega)), selbit_eq _ (by simp), selbit_eq _ (by simp)]
  have g2 : (xt ++ [x0]).getD (20 + 2) 0 = x0 := by
    rw [show 20 + 2 = xt.length + 0 by (clear * - hx hxt; omega), getD_append_hi]; rfl
  rw [getD_append_lo (by (clear * - hx hxt; omega)), getD_append_lo (by (clear * - hx hxt; omega)), g2]
  simp only [shiftP, shr_div, CharTwo.sub_eq_add, subHi_eq]
  have e0 : (b.index - 3 * 2 ^ 20) / 2 ^ (20 + 0) % 2 = ((b.index / 2 ^ 20 - 3) * 2 ^ 20) / 2 ^ (20 + 0) % 2 := by
    norm_num; (clear * - h4 h11; omega)
  have e1 : (b.index - 3 * 2 ^ 20) / 2 ^ (20 + 1) % 2 = ((b.index / 2 ^ 20 - 3) * 2 ^ 20) / 2 ^ (20 + 1) % 2 := by
    norm_num; (clear * - h4 h11; omega)
  have e2 : (b.index - 3 * 2 ^ 20) / 2 ^ (20 + 2) % 2 = 0 := by norm_num; (clear * - h4 h11; omega)
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
  have hxt : xt.length = CMain.nu20 - 1 := by simp only [List.length_cons] at hx; (clear * - hx hnu; omega)
  have hv := hb.1
  simp only [onStackZB, filter_reg _ hb, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.headD_cons, List.tail_cons]
  rw [relocF_20 x0 xt hxt, onStack_lohi c hv _ (by simp only [List.length_take]; (clear * - hnu hxt; omega)), if_pos rfl, mul_one,
    List.take_take, min_eq_left (by omega)]
  simp only [BlockClaim.onStack, shiftB, rotZ, List.tail_cons, List.headD_cons]
  have hl : (xt ++ [x0]).length = CMain.nu20 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rw [eqAbove_prod (shiftP c.block) (xt ++ [x0]) (fun i => (xt ++ [x0]).getD i 0) (by rw [hl, shiftP_vc]; (clear * - hnu hv; omega))
      (fun _ _ => rfl),
    eqAbove_prod ⟨20, (c.block.index / 2 ^ 20 - 3) * 2 ^ 20⟩ xt (fun i => xt.getD i 0) (show 20 ≤ xt.length by (clear * - hnu hxt; omega))
      (fun _ _ => rfl), hl, hxt, List.take_append_of_le_length (by rw [shiftP_vc]; (clear * - hnu hxt hv; omega))]
  have hv' : (shiftP c.block).variableCount = c.block.variableCount := shiftP_vc _
  rw [← Finset.prod_Ico_consecutive _ (by rw [hv']; exact hv) (by (clear * - hnu; omega) : 20 ≤ CMain.nu20), top_shift _ hb x0 xt hxt]
  have elo : ∏ i ∈ Finset.Ico (shiftP c.block).variableCount 20, fb (selbit (shiftP c.block) i) ((xt ++ [x0]).getD i 0) =
      ∏ i ∈ Finset.Ico c.block.variableCount 20, fb (selbit c.block i) ((xt.take 20).getD i 0) := by
    rw [hv']
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
    rw [getD_append_lo (by (clear * - hnu hxt h2; omega)), getD_take_lt h2, selbit_eq _ (by rw [hv']; exact h1), selbit_eq _ h1]
    simp only [shiftP, shr_div, subHi_eq]
    have : (c.block.index - 3 * 2 ^ 20) / 2 ^ i % 2 = c.block.index / 2 ^ i % 2 := by
      have h4 := hb.2.2.1
      have hk : 3 * 2 ^ 20 = 2 ^ i * (3 * 2 ^ (20 - i)) := by
        rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (by (clear * - h2; omega))]
      have hidx : c.block.index = (c.block.index - 3 * 2 ^ 20) + 2 ^ i * (3 * 2 ^ (20 - i)) := by
        rw [← hk]; (clear * - h4; omega)
      have he : 3 * 2 ^ (20 - i) % 2 = 0 := by
        rw [Nat.mul_mod, Nat.two_pow_mod_two_eq_zero.mpr (by (clear * - h2; omega))]
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
  (clear * - hr hnu; omega)

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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;> (clear * -; omega)

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
    rw [List.take_append_of_le_length (by (clear * - hx hnu; omega)), Nat.mul_div_cancel _ (by positivity), sel4, List.append_assoc]
  · refine ⟨xt.take 20, by simp only [List.length_take]; omega, ?_⟩
    rw [relocF_20 x0 xt hx, Nat.mul_div_cancel _ (by positivity)]

/-- **The regions a regular block misses contribute `0`.** -/
theorem term_miss (c : BlockClaim) (hb : RegP c.block) (x : List FE) (hx : x.length = CMain.nu20) (r : ℕ × ℕ × ℕ)
    (hr : r ∈ regions) (hm : meets c.block r = false) : c.onStack.1 (relocF x r) = 0 := by
  cases x with
  | nil => simp at hx
  | cons x0 xt =>
  have hnu : CMain.nu20 = 23 := rfl
  have hxt : xt.length = CMain.nu20 - 1 := by simp only [List.length_cons] at hx; (clear * - hx hnu; omega)
  obtain ⟨lo, hlo, e⟩ := relocF_lohi x0 xt hxt r hr
  rw [e, onStack_lohi c hb.1 lo hlo, if_neg, mul_zero, zero_mul]
  obtain ⟨hv, ha, h4, h11⟩ := hb
  rw [regTop] at h11
  have hf := align_fit c.block hv ha
  have hp : 1 ≤ 2 ^ c.block.variableCount := Nat.one_le_two_pow
  simp only [regions, nBlk, List.mem_append, List.mem_map, List.mem_range] at hr
  rw [show 2 ^ (CMain.nu20 - 20) = 8 from rfl]
  rcases hr with ⟨l, hl, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ 20)]; (clear * - h4 h11 hl; omega)
  · simp only [meets, decide_eq_false_iff_not] at hm
    simp only [Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ 20)]; (clear * - ha h4 h11 hj hm; omega)

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
  rw [h1, one_mul, List.take_of_length_le (by (clear * - hy; omega))]
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
    simp only [meets, decide_eq_true_eq]; (clear * -; omega)
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

private theorem foldl_mulF (a : FE) (l : List FE) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, mul_assoc]

/-- `eqEval` one coordinate at a time, for `onStackZB_dpt` (unfolding `eqEval` there by `simp only` cost the
kernel 1.1 s). -/
private theorem eqEval_consF (x0 y0 : FE) (x y : List FE) :
    eqEval (x0 :: x) (y0 :: y) = (1 + x0 + y0) * eqEval x y := by
  unfold eqEval
  rw [List.zipWith_cons_cons, List.foldl_cons, foldl_mulF, foldl_mulF]
  ring

private theorem eqEval_nilF (y : List FE) : eqEval [] y = 1 := by simp [eqEval]

/-- **`onStackZB` of a `D` point claim**: `κ(z)` times the point claim on `D` at `dzD z`, at `x^σ`. -/
theorem onStackZB_dpt (z : List FE) (hz : z.length = 22) (v t : FE) (x : List FE) (hx : x.length = CMain.nu20) :
    (onStackZB (BlockClaim.point ⟨22, 0⟩ z v) t).1 x =
      kappaD z * (BlockClaim.point ⟨22, 0⟩ (dzD z) v).onStack.1 (rotZ x) := by
  obtain ⟨zl, z18, z19, z20, z21, rfl, hzl⟩ := split4 z 18 (by omega)
  cases x with
  | nil => simp at hx
  | cons x0 xt =>
  have hnu : CMain.nu20 = 23 := rfl
  obtain ⟨lo, a, b, c, d, rfl, hlo⟩ := split4 xt 18 (by simp only [List.length_cons] at hx; (clear * - hx hnu; omega))
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
    rw [List.take_append_of_le_length (by (clear * - hlo; omega)), List.take_of_length_le (by (clear * - hlo; omega)), sel4]
  simp only [Function.comp_def, hr, eqAbove_app 18 _ lo _ hlo]
  have h1 : ∀ hi : List FE, hi.length = 5 → (⟨22, 0⟩ : Placement).eqAbove (lo ++ hi) = eqEval [0] (hi.drop 4) := by
    intro hi hhi
    rw [show lo ++ hi = (lo ++ hi.take 4) ++ hi.drop 4 by simp, eqAbove_app 22 0 _ _ (by simp [hlo, hhi])]
    simp [hhi, selectorPoint, List.range_succ, eOfNat_zero]
  have h2 : ∀ hi : List FE, hi.length = 5 → List.take 22 (lo ++ hi) = lo ++ hi.take 4 := by
    intro hi hhi
    rw [show 22 = lo.length + 4 by (clear * - hlo; omega), List.take_append]
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
  simp only [eqEval_consF, eqEval_nilF, one_mul, add_zero, mul_one, List.sum_cons, List.sum_nil]
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
    rw [e, eqAbove_app 22 0 _ _ (by simp only [List.length_append, List.length_take, selectorPoint_length']; (clear * - hnu hxt; omega))]
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
  have hl : (ρ.take 22).length = (y.take 22).length := by simp only [List.length_take]; (clear * - hρ hy hnu; omega)
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
    rw [hN y hy, one_mul, List.take_of_length_le (by (clear * - hx hnu hy; omega)), ringWeight_eqE _ y cs (by rw [hpt, hy])]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [eqEval_dpt _ y (hρl i) hy (g0 i) 0]; rfl]
  rw [zW_fsum]
  have hpzl : (ptZ pt).length = CMain.nu20 := by
    simp only [ptZ, dzD, List.length_append, List.length_take, List.length_cons, List.length_nil,
      List.length_replicate]; (clear * - hpt hx hnu; omega)
  have hcz : (csZ pt cs).length = cs.length := by simp [csZ]
  have eR : (⟨⟨CMain.nu20, 0⟩, fun y ↦ ringWeight (ptZ pt) y (csZ pt cs), v⟩ : BlockClaim).onStack.1 (rotZ x) =
      ∑ i ∈ Finset.range cs.length, (csZ pt cs).getD i 0 * eqEval ((ptZ pt).map (· ^ 2 ^ i)) (rotZ x) := by
    simp only [BlockClaim.onStack]
    rw [hN _ hr, one_mul, List.take_of_length_le (by (clear * - hx hnu hr; omega)), ringWeight_eqE _ _ _ (by rw [hpzl, hr]), hcz]
  rw [eR]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  have hl22 : ((ρ i).take 22).length = 22 := by simp only [List.length_take, hρl]; (clear * - hx hnu; omega)
  rw [dpt_full _ 0 x hx, onStackZB_dpt _ hl22 0 0 x hx]
  have ec : (csZ pt cs).getD i 0 = cs.getD i 0 * kappaD (ρ i) := by
    simp [csZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi', hρdef]
  have ek : kappaD ((ρ i).take 22) = kappaD (ρ i) := by
    simp [kappaD, List.getD_eq_getElem?_getD, List.getElem?_take]
  have hzl : ((ptZ pt).map (· ^ 2 ^ i)).length = CMain.nu20 := by rw [List.length_map, hpzl]
  have hdz : (dzD pt).length = 22 := by
    simp only [dzD, List.length_append, List.length_take, List.length_cons, List.length_nil]; (clear * - hpt hx hnu; omega)
  have hz0 : ((ptZ pt).map (· ^ 2 ^ i)).drop 22 = List.replicate (CMain.nu20 - 22) 0 := by
    rw [← List.map_drop, ptZ, List.drop_append_of_le_length (by (clear * - hdz; omega)), List.drop_of_length_le (by (clear * - hdz; omega)),
      List.nil_append]
    simp only [List.map_replicate, hpow]
  have hd : ((ptZ pt).map (· ^ 2 ^ i)).take 22 = dzD ((ρ i).take 22) := by
    have h18 : ((pt.take 18).map (· ^ 2 ^ i)).length = 18 := by
      simp only [List.length_map, List.length_take]; (clear * - hpt hx hnu; omega)
    have g : ∀ j, j < 22 → ((ρ i).take 22).getD j 0 = (pt.getD j 0) ^ 2 ^ i := by
      intro j h2
      rw [getD_take_lt h2]
      simp [hρdef, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (show j < pt.length by (clear * - hpt hx hnu h2; omega))]
    have ht : ((ρ i).take 22).take 18 = (pt.take 18).map (· ^ 2 ^ i) := by
      rw [List.take_take, min_eq_left (by norm_num), hρdef, List.map_take]
    rw [dzD, ht, g 20 (by norm_num), g 21 (by norm_num), ptZ, dzD]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate, hpow]
    rw [List.take_append_of_le_length (by rw [List.length_append, h18]; simp),
      List.take_of_length_le (by rw [List.length_append, h18]; simp)]
  rw [ec, ek, eqEval_dpt _ _ hzl hr hz0 0, hd]
  ring

end Lvm.QShape
end
-- ===== end of `LvmQShapeF` =====

-- ===== merged from `LvmQShapeC` (GOLF module merge: `LvmQShapeC.lean` is now a stub importing `LvmQShapeB`) =====
section
-- New for lvm2 (CR-Q, roll 7 SH2-Z; CR-DES §1.5 circuit side): Q_arith's gadgets for the child's shape:
-- the shape cell `σ'`, muxes, `D`'s and the ring's small claims with their tails, and the regular claims'
-- term pairs (big and moved keys sharing their leaf). Built on HAR-WH's batching (`LvmQAsmArith2WhirBasis*`:
-- `chainG`, `ringLeaf`, `partW_eq`, `kprod_keyOf`, `trieG`).

/-!
# The child's shape in Q_arith: gadgets

* **`muxG s a b`**: `s (a + b) + a` (two rows): `a` when `s = 0`, `b` when `s = 1`.
* **`zsumG a b`**: `Σ_l eq((a, b), l) · z*_l` (four rows; `zF`), the `D` tail's lane factor.
* **`dClaimG`**: a `D` point claim `⟨22, 0⟩` at `z` as the muxed claim `sum ν [(κ_m, ⟨22, 0⟩, z_m)]` (`ν = CMain.nu20`)
  (`κ_m = 1`, `z_m = z` when `s = 0`; `κ`, `dzD z` when `s = 1`), its value `v + s · t`,
  `t = (1 + κ) · zF(z₂₀, z₂₁)` (`tailD`).
* **`ringClaimG`**: the tape's ring claim on `⟨ν, 0⟩` as the muxed ring claim (`ptZ`, `csZ` when `s = 1`), its value
  `v + s · t`, `t = Σ_k c_k (1 + κ(pt^{2^k})) · zF(pt₂₀^{2^k}, pt₂₁^{2^k})` (`tailR`).
* **`zClaimG`**: per claim: `D`'s and the ring's muxed, every other claim kept and flagged regular.
-/

set_option autoImplicit false

namespace Lvm.QShape

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Shape

variable {c : Ctx} {M : Mem}

/-! ## Muxes -/

/-- `s (a + b) + a`. -/
def mux (s a b : FE) : FE := s * (a + b) + a

theorem mux_zero (a b : FE) : mux 0 a b = a := by simp [mux]
theorem mux_one (a b : FE) : mux 1 a b = b := by
  simp only [mux, one_mul]; rw [add_comm a b, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **The mux**: `a` when `s = 0`, `b` when `s = 1`. -/
def muxG (s a b : Cell) : BM Cell := do
  let u ← lin .E 1 0 a b
  mulAdd .E s u a

theorem muxG_spec (s a b : Cell) : Hs c M (muxG s a b) (fun r ↦ r.val M = mux (s.val M) (a.val M) (b.val M)) :=
  hs_bind (hs_lin _ _ _ _ _) fun u hu ↦ hs_mono (hs_mulAdd _ _ _ _) fun r hr ↦ by
    rw [hr, hu, ofK_one, ofK_zero, one_mul, add_zero, mux]

/-- `1 + a`. -/
def onePlusG (a : Cell) : BM Cell := lin .E 0 1 a a

theorem onePlusG_spec (a : Cell) : Hs c M (onePlusG a) (fun r ↦ r.val M = 1 + a.val M) :=
  hs_mono (hs_lin _ _ _ _ _) fun r hr ↦ by rw [hr, ofK_zero, ofK_one, zero_mul, add_zero, add_comm]

/-! ## `z*` as constants -/

/-- `z*_l` as a base-field constant. -/
def zK (l : ℕ) : FK := ⟨(LeanVM.Semantics.keccakF1600 (Vector.replicate 25 0)).toArray.getD l 0⟩

theorem ofK_zK (l : ℕ) : FE.ofK (zK l) = zStarF l := by
  unfold zK zStarF zStarsF
  simp [Array.getD]
  split <;> rfl

/-- The lane factor of a `D` tail: `Σ_l eq((a, b), l) · z*_l`. -/
def zF (a b : FE) : FE := ((List.range 4).map fun l ↦ eqEval [a, b] (selectorPoint l 2) * zStarF l).sum

/-- **`zF` in four rows** (`z` holds `0`). -/
def zsumG (a b z : Cell) : BM Cell := do
  let ab ← mulAdd .E a b z
  let u1 ← lin .E (zK 0 + zK 1) (zK 0) z a
  let u2 ← lin .E (zK 0 + zK 2) 0 u1 b
  lin .E (zK 0 + zK 1 + zK 2 + zK 3) 0 u2 ab

theorem zF_eq (a b : FE) : zF a b = zStarF 0 + (zStarF 0 + zStarF 1) * a + (zStarF 0 + zStarF 2) * b +
    (zStarF 0 + zStarF 1 + zStarF 2 + zStarF 3) * (a * b) := by
  -- the four selector points and `eqEval` on two coordinates by `rfl`/`simp only`, then the identity on variables
  -- (GOLF3: `norm_num` on the unfolded `eqEval`s cost the kernel 2 M heartbeats)
  have e : ∀ u v : FE, eqEval [a, b] [u, v] = (1 + a + u) * (1 + b + v) := fun u v => by
    simp only [eqEval, List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil, one_mul]
  have s0 : selectorPoint 0 2 = [0, 0] := by
    rw [show selectorPoint 0 2 = [eOfNat 0, eOfNat 0] from rfl, eOfNat_zero]
  have s1 : selectorPoint 1 2 = [1, 0] := by
    rw [show selectorPoint 1 2 = [eOfNat 1, eOfNat 0] from rfl, eOfNat_zero, eOfNat_one]
  have s2 : selectorPoint 2 2 = [0, 1] := by
    rw [show selectorPoint 2 2 = [eOfNat 0, eOfNat 1] from rfl, eOfNat_zero, eOfNat_one]
  have s3 : selectorPoint 3 2 = [1, 1] := by
    rw [show selectorPoint 3 2 = [eOfNat 1, eOfNat 1] from rfl, eOfNat_one]
  rw [zF, show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s0, s1, s2, s3, e]
  generalize zStarF 0 = z0
  generalize zStarF 1 = z1
  generalize zStarF 2 = z2
  generalize zStarF 3 = z3
  linear_combination (z1 * (1 + b) + z2 * (1 + a) + z3 * (a + b) + 2 * z3) * (CharTwo.two_eq_zero : (2 : FE) = 0)

theorem zsumG_spec {a b z : Cell} (hz : z.val M = 0) :
    Hs c M (zsumG a b z) (fun r ↦ r.val M = zF (a.val M) (b.val M)) :=
  hs_bind (hs_mulAdd _ _ _ _) fun ab hab ↦ hs_bind (hs_lin _ _ _ _ _) fun u1 hu1 ↦
    hs_bind (hs_lin _ _ _ _ _) fun u2 hu2 ↦ hs_mono (hs_lin _ _ _ _ _) fun r hr ↦ by
      rw [hr, hu2, hu1, hab, hz, zF_eq]
      simp only [ofK_add, ofK_zero, ofK_zK]
      ring

/-! ## `D`'s point claims -/

/-- `D`'s tail in closed form: `(1 + κ(z)) · zF(z₂₀, z₂₁)`. -/
def tailD (z : List FE) : FE := (1 + kappaD z) * zF (z.getD 20 0) (z.getD 21 0)

/-- **A `D` point claim, muxed** (`zl` the 22 point cells, `s` the shape cell). -/
def dClaimG (s z o : Cell) (cc : CClaim) (zl : List Cell) : BM CClaim := do
  let a ← onePlusG (zl.getD 18 default)
  let b ← onePlusG (zl.getD 19 default)
  let κ ← mulAdd .E a b z
  let κm ← muxG s o κ
  let m18 ← muxG s (zl.getD 18 default) (zl.getD 20 default)
  let m19 ← muxG s (zl.getD 19 default) (zl.getD 21 default)
  let m20 ← muxG s (zl.getD 20 default) z
  let m21 ← muxG s (zl.getD 21 default) z
  let zv ← zsumG (zl.getD 20 default) (zl.getD 21 default) z
  let u ← onePlusG κ
  let t ← mulAdd .E u zv z
  let v' ← mulAdd .E s t cc.value
  pure ⟨cc.com, .sum CMain.nu20 [(κm, ⟨22, 0⟩, zl.take 18 ++ [m18, m19, m20, m21])], v'⟩

/-- What `dClaimG`'s output is: the muxed scale and point cells' values, the value cell's. -/
structure DOut (M : Mem) (s z : Cell) (cc : CClaim) (zl : List Cell) (r : CClaim) : Prop where
  com : r.com = cc.com
  form : ∃ κm m18 m19 m20 m21 : Cell, r.cw = .sum CMain.nu20 [(κm, ⟨22, 0⟩, zl.take 18 ++ [m18, m19, m20, m21])] ∧
    κm.val M = mux (s.val M) 1 (kappaD (vs M zl)) ∧
    m18.val M = mux (s.val M) ((vs M zl).getD 18 0) ((vs M zl).getD 20 0) ∧
    m19.val M = mux (s.val M) ((vs M zl).getD 19 0) ((vs M zl).getD 21 0) ∧
    m20.val M = mux (s.val M) ((vs M zl).getD 20 0) 0 ∧
    m21.val M = mux (s.val M) ((vs M zl).getD 21 0) 0
  value : r.value.val M = cc.value.val M + s.val M * tailD (vs M zl)

theorem vs_getD' (l : List Cell) (i : ℕ) (hi : i < l.length) : (l.getD i default).val M = (vs M l).getD i 0 := by
  simp [vs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem dClaimG_spec {s z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (cc : CClaim) (zl : List Cell)
    (hzl : zl.length = 22) : Hs c M (dClaimG s z o cc zl) (DOut M s z cc zl) := by
  have g : ∀ i < 22, (zl.getD i default).val M = (vs M zl).getD i 0 := fun i hi ↦ vs_getD' zl i (by omega)
  unfold dClaimG
  refine hs_bind (onePlusG_spec _) fun a ha ↦ hs_bind (onePlusG_spec _) fun b hb ↦
    hs_bind (hs_mulAdd _ _ _ _) fun κ hκ ↦ hs_bind (muxG_spec _ _ _) fun κm hκm ↦
    hs_bind (muxG_spec _ _ _) fun m18 h18 ↦ hs_bind (muxG_spec _ _ _) fun m19 h19 ↦
    hs_bind (muxG_spec _ _ _) fun m20 h20 ↦ hs_bind (muxG_spec _ _ _) fun m21 h21 ↦
    hs_bind (zsumG_spec hz) fun zv hzv ↦ hs_bind (onePlusG_spec _) fun u hu ↦
    hs_bind (hs_mulAdd _ _ _ _) fun t ht ↦ hs_bind (hs_mulAdd _ _ _ _) fun v' hv' ↦ hs_pure ⟨rfl, ?_, ?_⟩
  · have hk : κ.val M = kappaD (vs M zl) := by
      rw [hκ, ha, hb, hz, add_zero, kappaD, g 18 (by norm_num), g 19 (by norm_num)]
    refine ⟨κm, m18, m19, m20, m21, rfl, by rw [hκm, ho, hk], ?_, ?_, ?_, ?_⟩
    · rw [h18, g 18 (by norm_num), g 20 (by norm_num)]
    · rw [h19, g 19 (by norm_num), g 21 (by norm_num)]
    · rw [h20, g 20 (by norm_num), hz]
    · rw [h21, g 21 (by norm_num), hz]
  · show v'.val M = _
    rw [hv', ht, hu, hzv, hκ, ha, hb, hz, add_zero, add_zero, tailD, kappaD, g 18 (by norm_num),
      g 19 (by norm_num), g 20 (by norm_num), g 21 (by norm_num)]
    ring

/-! ## The tape's ring claim -/

/-- The ring's tail in closed form: `Σ_k c_k (1 + κ(pt^{2^k})) · zF(pt₂₀^{2^k}, pt₂₁^{2^k})`. -/
def tailR (pt cs : List FE) : FE :=
  ∑ k ∈ Finset.range cs.length, cs.getD k 0 * ((1 + kappaD (pt.map (· ^ 2 ^ k))) *
    zF ((pt.getD 20 0) ^ 2 ^ k) ((pt.getD 21 0) ^ 2 ^ k))

/-- One coefficient per step: `c'_k = mux(s, c_k, c_k κ_k)`, the tail's running sum, the squares. -/
def ringStepG (s z : Cell) : List Cell → Cell → Cell → Cell → Cell → Cell → BM (List Cell × Cell)
  | [], _, _, _, _, acc => pure ([], acc)
  | c :: cs, r18, r19, r20, r21, acc => do
    let a ← onePlusG r18
    let b ← onePlusG r19
    let m ← mulAdd .E a b z
    let c' ← mulAdd .E c m z
    let cm ← muxG s c c'
    let zv ← zsumG r20 r21 z
    let u ← onePlusG m
    let w ← mulAdd .E u zv z
    let acc' ← mulAdd .E c w acc
    let q18 ← mulAdd .E r18 r18 z
    let q19 ← mulAdd .E r19 r19 z
    let q20 ← mulAdd .E r20 r20 z
    let q21 ← mulAdd .E r21 r21 z
    let rest ← ringStepG s z cs q18 q19 q20 q21 acc'
    pure (cm :: rest.1, rest.2)

theorem ringStepG_spec {s z : Cell} (hz : z.val M = 0) (P : List FE) :
    ∀ (cs : List Cell) (k : ℕ) (r18 r19 r20 r21 acc : Cell),
      r18.val M = (P.getD 18 0) ^ 2 ^ k → r19.val M = (P.getD 19 0) ^ 2 ^ k →
      r20.val M = (P.getD 20 0) ^ 2 ^ k → r21.val M = (P.getD 21 0) ^ 2 ^ k →
      Hs c M (ringStepG s z cs r18 r19 r20 r21 acc) (fun r ↦ r.1.length = cs.length ∧
        (∀ j < cs.length, (r.1.getD j default).val M = mux (s.val M) ((vs M cs).getD j 0)
          ((vs M cs).getD j 0 * ((1 + (P.getD 18 0) ^ 2 ^ (k + j)) * (1 + (P.getD 19 0) ^ 2 ^ (k + j))))) ∧
        r.2.val M = acc.val M + ∑ j ∈ Finset.range cs.length, (vs M cs).getD j 0 *
          ((1 + (1 + (P.getD 18 0) ^ 2 ^ (k + j)) * (1 + (P.getD 19 0) ^ 2 ^ (k + j))) *
            zF ((P.getD 20 0) ^ 2 ^ (k + j)) ((P.getD 21 0) ^ 2 ^ (k + j))))
  | [], _, _, _, _, _, acc, _, _, _, _ => hs_pure ⟨rfl, fun j hj ↦ absurd hj (by simp), by simp⟩
  | cc :: cs, k, r18, r19, r20, r21, acc, h18, h19, h20, h21 => by
    unfold ringStepG
    have sq : ∀ (x : FE) (k : ℕ), (x ^ 2 ^ k) * (x ^ 2 ^ k) = x ^ 2 ^ (k + 1) := fun x k ↦ by
      rw [← pow_add, pow_succ]; ring_nf
    refine hs_bind (onePlusG_spec _) fun a ha ↦ hs_bind (onePlusG_spec _) fun b hb ↦
      hs_bind (hs_mulAdd _ _ _ _) fun m hm ↦ hs_bind (hs_mulAdd _ _ _ _) fun c' hc' ↦
      hs_bind (muxG_spec _ _ _) fun cm hcm ↦ hs_bind (zsumG_spec hz) fun zv hzv ↦
      hs_bind (onePlusG_spec _) fun u hu ↦ hs_bind (hs_mulAdd _ _ _ _) fun w hw ↦
      hs_bind (hs_mulAdd _ _ _ _) fun acc' hacc ↦ hs_bind (hs_mulAdd _ _ _ _) fun q18 hq18 ↦
      hs_bind (hs_mulAdd _ _ _ _) fun q19 hq19 ↦ hs_bind (hs_mulAdd _ _ _ _) fun q20 hq20 ↦
      hs_bind (hs_mulAdd _ _ _ _) fun q21 hq21 ↦ hs_bind (ringStepG_spec hz P cs (k + 1) q18 q19 q20 q21 acc'
        (by rw [hq18, h18, hz, add_zero, sq]) (by rw [hq19, h19, hz, add_zero, sq])
        (by rw [hq20, h20, hz, add_zero, sq]) (by rw [hq21, h21, hz, add_zero, sq])) fun rest ⟨hl, hv, ht⟩ ↦
      hs_pure ⟨by simp [hl], fun j hj ↦ ?_, ?_⟩
    · rcases j with _ | j
      · simp only [List.getD_cons_zero, vs, List.map_cons, Nat.add_zero]
        rw [hcm, hc', hm, ha, hb, hz, add_zero, add_zero, h18, h19]
      · simp only [List.getD_cons_succ, vs, List.map_cons, List.length_cons] at hj ⊢
        rw [hv j (by omega), show k + (j + 1) = k + 1 + j by omega]
        rfl
    · rw [ht, hacc, hw, hu, hm, ha, hb, hzv, hz, add_zero, add_zero, h18, h19, h20, h21, List.length_cons,
        Finset.sum_range_succ', add_assoc]
      have e : ∀ j, k + (j + 1) = k + 1 + j := fun j ↦ by omega
      simp only [Nat.add_assoc, Nat.add_comm 1] at ht ⊢
      simp only [vs, List.map_cons, List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
      ring

/-- **The tape's ring claim, muxed** (`pt` `ν` point cells with `pt₂₂ … = z`, the block bits above `D`, `cs` 64
coefficients). -/
def ringClaimG (s z : Cell) (cc : CClaim) (pt cs : List Cell) : BM CClaim := do
  let r ← ringStepG s z cs (pt.getD 18 default) (pt.getD 19 default) (pt.getD 20 default) (pt.getD 21 default) z
  let m18 ← muxG s (pt.getD 18 default) (pt.getD 20 default)
  let m19 ← muxG s (pt.getD 19 default) (pt.getD 21 default)
  let m20 ← muxG s (pt.getD 20 default) z
  let m21 ← muxG s (pt.getD 21 default) z
  let v' ← mulAdd .E s r.2 cc.value
  pure ⟨cc.com, .ring ⟨CMain.nu20, 0⟩ (pt.take 18 ++ [m18, m19, m20, m21] ++ pt.drop 22) r.1, v'⟩

theorem kappaD_map (P : List FE) (k : ℕ) (hP : P.length = CMain.nu20) :
    kappaD (P.map (· ^ 2 ^ k)) = (1 + (P.getD 18 0) ^ 2 ^ k) * (1 + (P.getD 19 0) ^ 2 ^ k) := by
  have h18 : 18 < P.length := by rw [hP]; decide
  have h19 : 19 < P.length := by rw [hP]; decide
  simp [kappaD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h18,
    List.getElem?_eq_getElem h19]

/-- What `ringClaimG`'s output is. -/
structure ROut (M : Mem) (s z : Cell) (cc : CClaim) (pt cs : List Cell) (r : CClaim) : Prop where
  com : r.com = cc.com
  form : ∃ m18 m19 m20 m21 : Cell, ∃ csm : List Cell,
    r.cw = .ring ⟨CMain.nu20, 0⟩ (pt.take 18 ++ [m18, m19, m20, m21] ++ pt.drop 22) csm ∧
    m18.val M = mux (s.val M) ((vs M pt).getD 18 0) ((vs M pt).getD 20 0) ∧
    m19.val M = mux (s.val M) ((vs M pt).getD 19 0) ((vs M pt).getD 21 0) ∧
    m20.val M = mux (s.val M) ((vs M pt).getD 20 0) 0 ∧
    m21.val M = mux (s.val M) ((vs M pt).getD 21 0) 0 ∧
    csm.length = cs.length ∧
    ∀ j < cs.length, (csm.getD j default).val M =
      mux (s.val M) ((vs M cs).getD j 0) ((csZ (vs M pt) (vs M cs)).getD j 0)
  value : r.value.val M = cc.value.val M + s.val M * tailR (vs M pt) (vs M cs)

theorem ringClaimG_spec {s z : Cell} (hz : z.val M = 0) (cc : CClaim) (pt cs : List Cell)
    (hpt : pt.length = CMain.nu20) :
    Hs c M (ringClaimG s z cc pt cs) (ROut M s z cc pt cs) := by
  have g : ∀ i < CMain.nu20, (pt.getD i default).val M = (vs M pt).getD i 0 := fun i hi ↦ vs_getD' pt i (by omega)
  have hP : (vs M pt).length = CMain.nu20 := by simp [vs, hpt]
  unfold ringClaimG
  refine hs_bind (ringStepG_spec hz (vs M pt) cs 0 _ _ _ _ z (by rw [g 18 (by norm_num)]; simp)
      (by rw [g 19 (by norm_num)]; simp) (by rw [g 20 (by norm_num)]; simp) (by rw [g 21 (by norm_num)]; simp))
    fun r ⟨hl, hv, ht⟩ ↦ hs_bind (muxG_spec _ _ _) fun m18 h18 ↦ hs_bind (muxG_spec _ _ _) fun m19 h19 ↦
    hs_bind (muxG_spec _ _ _) fun m20 h20 ↦ hs_bind (muxG_spec _ _ _) fun m21 h21 ↦
    hs_bind (hs_mulAdd _ _ _ _) fun v' hv' ↦ hs_pure ⟨rfl, ⟨m18, m19, m20, m21, r.1, rfl, ?_, ?_, ?_, ?_, hl, ?_⟩, ?_⟩
  · rw [h18, g 18 (by norm_num), g 20 (by norm_num)]
  · rw [h19, g 19 (by norm_num), g 21 (by norm_num)]
  · rw [h20, g 20 (by norm_num), hz]
  · rw [h21, g 21 (by norm_num), hz]
  · intro j hj
    rw [hv j hj, Nat.zero_add]
    congr 1
    have hj' : j < (vs M cs).length := by simp [vs]; exact hj
    simp [csZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj', kappaD_map _ _ hP]
  · show v'.val M = _
    rw [hv', ht, hz, zero_add, tailR]
    have hcl : (vs M cs).length = cs.length := by simp [vs]
    rw [hcl]
    simp only [Nat.zero_add, kappaD_map _ _ hP]
    ring

/-! ## Claims in both shapes -/

/-- **The static form of `C_main`'s claims** (decided on the record; `ν = CMain.nu20`): a `D` point claim
(`⟨22, 0⟩`, 22 cells), the tape's ring claim (`⟨ν, 0⟩`, `ν` point cells ending in `ν − 22` zero cells, the block
bits above `D`, 64 coefficients), or a regular claim (point/ring on a regular block, `sum ν` of regular parts). -/
def ZWF (z : Cell) (cc : CClaim) : Bool :=
  match cc.cw with
  | .point blk zl => if blk = ⟨22, 0⟩ then decide (zl.length = 22) else decide (RegP blk)
  | .ring blk pt cs => if blk = ⟨CMain.nu20, 0⟩ then decide (pt.length = CMain.nu20) &&
      (pt.drop 22).all (· == z) && decide (cs.length = 64) else decide (RegP blk)
  | .sum nu parts => decide (nu = CMain.nu20) && parts.all fun e ↦ decide (RegP e.2.1)

/-- **One claim in both shapes**: `D`'s and the ring's muxed (flag `false`), every other kept (flag `true`:
its small form is the moved claim, built as moved keys over the same leaves). -/
def zClaimG (s z o : Cell) (cc : CClaim) : BM (CClaim × Bool) :=
  match cc.cw with
  | .point blk zl => if blk = ⟨22, 0⟩ then do let r ← dClaimG s z o cc zl; pure (r, false) else pure (cc, true)
  | .ring blk pt cs => if blk = ⟨CMain.nu20, 0⟩ then do let r ← ringClaimG s z cc pt cs; pure (r, false)
      else pure (cc, true)
  | .sum _ _ => pure (cc, true)

/-- The claims in both shapes. -/
def zClaimsG (s z o : Cell) : List CClaim → BM (List (CClaim × Bool))
  | [] => pure []
  | cc :: cl => do
    let r ← zClaimG s z o cc
    let rs ← zClaimsG s z o cl
    pure (r :: rs)

/-- The tail value of a claim (the cells' closed form): `tailD` for `D`, `tailR` for the ring, `0` else. -/
def tailC (M : Mem) (cc : CClaim) : FE :=
  match cc.cw with
  | .point blk zl => if blk = ⟨22, 0⟩ then tailD (vs M zl) else 0
  | .ring blk pt cs => if blk = ⟨CMain.nu20, 0⟩ then tailR (vs M pt) (vs M cs) else 0
  | .sum _ _ => 0

/-- A regular claim: its blocks (every part's) regular. -/
def RegC (cc : CClaim) : Prop :=
  match cc.cw with
  | .point blk _ => RegP blk
  | .ring blk _ _ => RegP blk
  | .sum nu parts => nu = CMain.nu20 ∧ ∀ e ∈ parts, RegP e.2.1

/-- The small form of a regular claim: its blocks moved down. -/
def smallW (M : Mem) (cc : CClaim) : List FE → FE :=
  match cc.cw with
  | .point blk zl => (BlockClaim.point (shiftP blk) (vs M zl) 0).onStack.1
  | .ring blk pt cs => (⟨shiftP blk, fun y ↦ ringWeight (vs M pt) y (vs M cs), 0⟩ : BlockClaim).onStack.1
  | .sum nu parts => (sumClaim nu (parts.map fun e ↦ (e.1.val M, shiftP e.2.1, vs M e.2.2)) 0).onStack.1

/-! ## One claim in both shapes: the relation -/

theorem list_ext_getD (l l' : List FE) (h : l.length = l'.length) (hg : ∀ j < l.length, l.getD j 0 = l'.getD j 0) :
    l = l' :=
  List.ext_getElem h fun j h1 h2 ↦ by
    have := hg j h1
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem onStack_val_irrel (b : Placement) (w : List FE → FE) (v v' : FE) :
    (⟨b, w, v⟩ : BlockClaim).onStack.1 = (⟨b, w, v'⟩ : BlockClaim).onStack.1 := rfl

theorem take_getD4 (l : List FE) (hl : l.length = 22) :
    l.take 18 ++ [l.getD 18 0, l.getD 19 0, l.getD 20 0, l.getD 21 0] = l := by
  obtain ⟨zl, a, b, c, d, rfl, h⟩ := split4 l 18 (by omega)
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h, List.take_append_of_le_length]

theorem take_getD_nu (l : List FE) (hl : l.length = CMain.nu20) :
    l.take 18 ++ [l.getD 18 0, l.getD 19 0, l.getD 20 0, l.getD 21 0] ++ l.drop 22 = l := by
  have h := take_getD4 (l.take 22) (by simp only [List.length_take, hl]; decide)
  rw [List.take_take, min_eq_left (by norm_num), getD_take' _ _ (by norm_num : 18 < 22),
    getD_take' _ _ (by norm_num : 19 < 22), getD_take' _ _ (by norm_num : 20 < 22),
    getD_take' _ _ (by norm_num : 21 < 22)] at h
  conv_rhs => rw [← List.take_append_drop 22 l, ← h]

/-- The two values a shape cell can hold. -/
def IsBit (a : FE) : Prop := a = 0 ∨ a = 1

/-- **What `zClaimG` gives** for a claim `cc` of the static form (`ZWF`), at any point `x` of `ν` coordinates:
the same commitment; the value `v + s · tail`; the big form when `s = 0`; when `s = 1`, the small form at `x^σ`
is `V_S`'s small claim `onStackZB` at `x` (a regular claim's small form is `smallW`, its blocks moved). -/
structure ZRel (M : Mem) (s : Cell) (cc : CClaim) (r : CClaim × Bool) : Prop where
  com : r.1.com = cc.com
  value : r.1.value.val M = cc.value.val M + s.val M * tailC M cc
  reg : r.2 = true → r.1 = cc
  regC : r.2 = true → RegC cc
  big : r.2 = false → s.val M = 0 → ∀ x : List FE, x.length = CMain.nu20 →
    (r.1.val M).2.onStack.1 x = (cc.val M).2.onStack.1 x
  small : s.val M = 1 → ∀ x : List FE, x.length = CMain.nu20 →
    (if r.2 then smallW M cc (rotZ x) else (r.1.val M).2.onStack.1 (rotZ x)) =
      (onStackZB (cc.val M).2 (tailC M cc)).1 x
  wf : WF1 CMain.nu20 cc = true → WF1 CMain.nu20 r.1 = true

theorem rotZ_length (x : List FE) (hx : x.length = CMain.nu20) : (rotZ x).length = CMain.nu20 := by
  cases x with
  | nil => simp at hx
  | cons x0 xt => simp [rotZ]; simpa using hx

theorem zClaimG_spec {s z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (cc : CClaim) (hw : ZWF z cc = true) :
    Hs c M (zClaimG s z o cc) (ZRel M s cc) := by
  rcases cc with ⟨com, cw, v⟩
  cases cw with
  | point blk zl =>
    by_cases hb : blk = ⟨22, 0⟩
    · subst hb
      have hzl : zl.length = 22 := by simpa [ZWF] using hw
      simp only [zClaimG, if_pos rfl]
      refine hs_bind (dClaimG_spec hz ho _ zl hzl) fun r hr ↦ hs_pure ?_
      obtain ⟨hcom, ⟨κm, m18, m19, m20, m21, hcw, hκ, h18, h19, h20, h21⟩, hval⟩ := hr
      have hvl : (vs M zl).length = 22 := by simp [vs, hzl]
      have e : ∀ x : List FE, x.length = CMain.nu20 → (r.val M).2.onStack.1 x = κm.val M * (BlockClaim.point ⟨22, 0⟩
          ((vs M zl).take 18 ++ [m18.val M, m19.val M, m20.val M, m21.val M]) 0).onStack.1 x := by
        intro x hx
        rcases r with ⟨rc, rw, rv⟩
        simp only at hcw
        subst hcw
        simp only [CClaim.val]
        rw [sumClaim_onStack _ _ _ hx]
        simp [vs, List.map_take, partB, BlockClaim.point, BlockClaim.onStack]
      have tc : tailC M ⟨com, .point ⟨22, 0⟩ zl, v⟩ = tailD (vs M zl) := by simp [tailC]
      refine ⟨hcom, by rw [hval, tc], fun h ↦ absurd h (by simp), fun h ↦ absurd h (by simp), fun _ hs x hx ↦ ?_, fun hs x hx ↦ ?_, fun _ ↦ ?_⟩
      · rw [e x hx, hκ, h18, h19, h20, h21, hs, mux_zero, mux_zero, mux_zero, mux_zero, mux_zero, one_mul,
          take_getD4 _ hvl]
        rfl
      · simp only [Bool.false_eq_true, if_false]
        rw [e _ (rotZ_length x hx), hκ, h18, h19, h20, h21, hs, mux_one, mux_one, mux_one, mux_one, mux_one, tc]
        exact (onStackZB_dpt (vs M zl) hvl (v.val M) _ x hx).symm
      · rcases r with ⟨rc, rw, rv⟩
        simp only at hcw
        subst hcw
        simp [WF1, hzl, CMain.nu20]
    · have hr : RegP blk := by simpa [ZWF, hb] using hw
      have tc : tailC M ⟨com, .point blk zl, v⟩ = 0 := by simp [tailC, hb]
      simp only [zClaimG, if_neg hb]
      refine hs_pure ⟨rfl, by rw [tc, mul_zero, add_zero], fun _ ↦ rfl, fun _ ↦ hr, fun h ↦ absurd h (by simp),
        fun _ x hx ↦ ?_, fun h ↦ h⟩
      simp only [if_true, tc]
      rw [onStackZB_reg _ 0 hr x hx]
      rfl
  | ring blk pt cs =>
    by_cases hb : blk = ⟨CMain.nu20, 0⟩
    · subst hb
      have hw' : pt.length = CMain.nu20 ∧ (∀ x ∈ pt.drop 22, x = z) ∧ cs.length = 64 := by
        simpa [ZWF, and_assoc] using hw
      obtain ⟨hpt, h22, hcs⟩ := hw'
      simp only [zClaimG, if_pos rfl]
      refine hs_bind (ringClaimG_spec hz _ pt cs hpt) fun r hr ↦ hs_pure ?_
      obtain ⟨hcom, ⟨m18, m19, m20, m21, csm, hcw, h18', h19', h20', h21', hcl, hcv⟩, hval⟩ := hr
      have hP : (vs M pt).length = CMain.nu20 := by simp [vs, hpt]
      have hP0 : (vs M pt).drop 22 = List.replicate (CMain.nu20 - 22) 0 := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp [vs, hpt], fun b hb ↦ ?_⟩
        rw [vs, ← List.map_drop] at hb
        obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hb
        rw [h22 x' hx', hz]
      have epm : vs M (pt.take 18 ++ [m18, m19, m20, m21] ++ pt.drop 22) =
          (vs M pt).take 18 ++ [m18.val M, m19.val M, m20.val M, m21.val M] ++ (vs M pt).drop 22 := by
        simp [vs, List.map_take, List.map_drop]
      have e : ∀ x : List FE, (r.val M).2.onStack.1 x =
          (⟨⟨CMain.nu20, 0⟩, fun y ↦ ringWeight ((vs M pt).take 18 ++ [m18.val M, m19.val M, m20.val M, m21.val M] ++
            (vs M pt).drop 22) y (vs M csm), 0⟩ : BlockClaim).onStack.1 x := by
        intro x
        rcases r with ⟨rc, rw, rv⟩
        simp only at hcw
        subst hcw
        simp only [CClaim.val, epm]
        rfl
      have tc : tailC M ⟨com, .ring ⟨CMain.nu20, 0⟩ pt cs, v⟩ = tailR (vs M pt) (vs M cs) := by simp [tailC]
      have hcsl : (vs M csm).length = (vs M cs).length := by simp [vs, hcl]
      refine ⟨hcom, by rw [hval, tc], fun h ↦ absurd h (by simp), fun h ↦ absurd h (by simp), fun _ hs x hx ↦ ?_, fun hs x hx ↦ ?_, fun hwf ↦ ?_⟩
      · rw [e x, h18', h19', h20', h21', hs, mux_zero, mux_zero, mux_zero, mux_zero, take_getD_nu _ hP]
        have ec : vs M csm = vs M cs := list_ext_getD _ _ hcsl fun j hj ↦ by
          rw [← vs_getD' csm j (by simpa [vs] using hj), hcv j (by simpa [vs, hcl] using hj), hs, mux_zero]
        rw [ec]
        rfl
      · simp only [Bool.false_eq_true, if_false]
        rw [e _, h18', h19', h20', h21', hs, mux_one, mux_one, mux_one, mux_one, tc]
        have ep : (vs M pt).take 18 ++ [(vs M pt).getD 20 0, (vs M pt).getD 21 0, 0, 0] ++ (vs M pt).drop 22 =
            ptZ (vs M pt) := by
          rw [hP0]; rfl
        have ec : vs M csm = csZ (vs M pt) (vs M cs) := list_ext_getD _ _ (by rw [hcsl]; simp [csZ, vs]) fun j hj ↦ by
          rw [← vs_getD' csm j (by simpa [vs] using hj), hcv j (by simpa [vs, hcl] using hj), hs, mux_one]
        rw [ep, ec]
        exact (onStackZB_ring (vs M pt) (vs M cs) hP hP0 (v.val M) _ x hx).symm
      · rcases r with ⟨rc, rw, rv⟩
        simp only at hcw
        subst hcw
        simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf ⊢
        refine ⟨⟨⟨hwf.1.1.1, by simp [hpt, CMain.nu20]⟩, by rw [hcl]; exact hwf.1.2⟩, hwf.2⟩
    · have hr : RegP blk := by simpa [ZWF, hb] using hw
      have tc : tailC M ⟨com, .ring blk pt cs, v⟩ = 0 := by simp [tailC, hb]
      simp only [zClaimG, if_neg hb]
      refine hs_pure ⟨rfl, by rw [tc, mul_zero, add_zero], fun _ ↦ rfl, fun _ ↦ hr, fun h ↦ absurd h (by simp),
        fun _ x hx ↦ ?_, fun h ↦ h⟩
      simp only [if_true, tc]
      rw [onStackZB_reg _ 0 hr x hx]
      rfl
  | sum nu parts =>
    have hw' : nu = CMain.nu20 ∧ ∀ e ∈ parts, RegP e.2.1 := by simpa [ZWF] using hw
    obtain ⟨rfl, hp⟩ := hw'
    have tc : tailC M ⟨com, .sum CMain.nu20 parts, v⟩ = 0 := by simp [tailC]
    refine hs_pure ⟨rfl, by rw [tc, mul_zero, add_zero], fun _ ↦ rfl, fun _ ↦ ⟨rfl, hp⟩, fun h ↦ absurd h (by simp),
      fun _ x hx ↦ ?_, fun h ↦ h⟩
    simp only [if_true, tc]
    simp only [CClaim.val]
    rw [onStackZB_sum _ _ 0 (fun e he ↦ by
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      exact hp e' he') x hx]
    simp only [smallW, List.map_map]
    rfl

end Lvm.QShape
end
-- ===== end of `LvmQShapeC` =====

/-!
# The basis in both shapes

* **`ZT`**: a term pair: scale, leaf, big top key `pb`, moved top key `ps` (`ν − 20` bits each, `ν = CMain.nu20`;
  three at B1's ν = 23), the common rest.
  `ptPair`, `rgPair`, `partsPairs`, `regPairs`: the pairs of a regular claim (one leaf, two keys);
  `ptPair_spec` … `regPairs_spec`: the big keys give the claim's weight, the moved keys `smallW`.
* **`zTerms`**: the pairs of the regular claims and the plain terms of the muxed ones (`oneClaim`).
* **`lowsG`**: the subtries below depth 20, one per top pair (`keysOf`); `sum_groups`: regrouping.
* **`basisZ`**: the two tops (big and moved keys over the shared subtries, plus the muxed claims' terms) and
  their mux. `basisZ_spec`: `mux(s, Σ s^i W_i(X), Σ s^i W^σ_i(X))`.
-/

set_option autoImplicit false

namespace Lvm.QShape

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Har Lvm.Shape

variable {c : Ctx} {M : Mem}

/-! ## Keys -/

/-- The top `ν − 20` bits of a key (coordinates `ν − 1` … 20; 22 … 20 at B1's ν = 23). -/
def topK (bit : ℕ → Bool) : List Bool := keyOf bit CMain.nu20 20

theorem keyOf_app (bit : ℕ → Bool) {k m : ℕ} (hk : k ≤ m) :
    ∀ n, m ≤ n → keyOf bit n k = keyOf bit n m ++ keyOf bit m k
  | 0, h => by
    obtain rfl : m = 0 := by (clear * - h; omega)
    obtain rfl : k = 0 := by (clear * - hk; omega)
    rfl
  | n + 1, h => by
    by_cases e : m = n + 1
    · subst e
      rw [show keyOf bit (n + 1) (n + 1) = [] by rw [keyOf.eq_2]; simp, List.nil_append]
    · rw [keyOf.eq_2, if_neg (by omega), keyOf.eq_2, if_neg (by (clear * - h e; omega)), keyOf_app bit hk n (by (clear * - h e; omega)),
        List.cons_append]

theorem keyOf_length (bit : ℕ → Bool) (k : ℕ) : ∀ n, (keyOf bit n k).length = n - k
  | 0 => by simp [keyOf]
  | n + 1 => by
    rw [keyOf.eq_2]
    split_ifs with h
    · simp; omega
    · rw [List.length_cons, keyOf_length bit k n]; omega

theorem topK_length (bit : ℕ → Bool) : (topK bit).length = CMain.nu20 - 20 := keyOf_length bit 20 _

theorem keyOf_top (bit : ℕ → Bool) {k : ℕ} (hk : k ≤ 20) : keyOf bit CMain.nu20 k = topK bit ++ keyOf bit 20 k :=
  keyOf_app bit hk CMain.nu20 (by decide)

theorem keyOf_congr (b b' : ℕ → Bool) (k : ℕ) : ∀ n, (∀ i, k ≤ i → i < n → b i = b' i) →
    keyOf b n k = keyOf b' n k
  | 0, _ => rfl
  | n + 1, h => by
    rw [keyOf.eq_2, keyOf.eq_2]
    split_ifs with hn
    · rfl
    · rw [h n (by (clear * - hn; omega)) (by (clear * -; omega)), keyOf_congr b b' k n fun i h1 h2 ↦ h i h1 (by (clear * - h2; omega))]

theorem shr_sub (a i : ℕ) (hi : i < 20) (h : 3 * 2 ^ 20 ≤ a) : (a - 3 * 2 ^ 20) / 2 ^ i % 2 = a / 2 ^ i % 2 := by
  have hk : 3 * 2 ^ 20 = 2 ^ i * (3 * 2 ^ (20 - i)) := by
    rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (by (clear * - hi; omega))]
  have ha : a = (a - 3 * 2 ^ 20) + 2 ^ i * (3 * 2 ^ (20 - i)) := by rw [← hk]; (clear * - h; omega)
  have he : 3 * 2 ^ (20 - i) % 2 = 0 := by
    rw [Nat.mul_mod, Nat.two_pow_mod_two_eq_zero.mpr (by (clear * - hi; omega))]
  conv_rhs => rw [ha]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.add_mod, he, add_zero, Nat.mod_mod]

theorem selbit_shift_lo (blk : Placement) (hr : RegP blk) {i : ℕ} (h1 : blk.variableCount ≤ i) (h2 : i < 20) :
    selbit (shiftP blk) i = selbit blk i := by
  rw [selbit_eq _ (by rw [shiftP_vc]; exact h1), selbit_eq _ h1, shiftP_index, shr_div, shr_div,
    shr_sub _ _ h2 (by have := hr.2.2.1; (clear * - this; omega))]

theorem bitP_shift_lo (z o : Cell) (blk : Placement) (zl : List Cell) (hr : RegP blk) {i : ℕ} (h2 : i < 20) :
    bitP z o CMain.nu20 (shiftP blk) zl i = bitP z o CMain.nu20 blk zl i := by
  unfold bitP
  rw [shiftP_vc]
  split_ifs with h1 h3
  · rfl
  · exact selbit_shift_lo blk hr h3 h2
  · rfl

/-! ## Term pairs -/

/-- A term pair: scale, leaf, the big and the moved top keys, the common rest of the key. -/
structure ZT where
  sc : Cell
  lf : Cell
  pb : List Bool
  ps : List Bool
  rest : List Bool

/-- The big term. -/
def ZT.big (t : ZT) : TC := ⟨t.sc, t.pb ++ t.rest, t.lf⟩
/-- The moved term. -/
def ZT.sml (t : ZT) : TC := ⟨t.sc, t.ps ++ t.rest, t.lf⟩
/-- The term below depth 20. -/
def ZT.low (t : ZT) : TC := ⟨t.sc, t.rest, t.lf⟩

/-- The pair of a point part on a regular block (`nu = ν`). -/
def ptPair (xb : ℕ) (z o sc : Cell) (blk : Placement) (zl : List Cell) (memo : Memo) : BM (Memo × ZT) := do
  let r ← chainG xb z o zl (ncPre z o zl) memo
  pure (r.1, ⟨sc, r.2, topK (bitP z o CMain.nu20 blk zl), topK (bitP z o CMain.nu20 (shiftP blk) zl),
    keyOf (bitP z o CMain.nu20 blk zl) 20 (ncPre z o zl)⟩)

theorem e0f_nu (xb : ℕ) : e0f M CMain.nu20 xb CMain.nu20 = 1 := by simp [e0f]

theorem ptPair_spec {xb : ℕ} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) {sc : Cell} {blk : Placement}
    {zl : List Cell} {memo : Memo} (hm : MemoOk M (fun i ↦ M.e (xb + i)) memo) (hzl : zl.length = blk.variableCount)
    (hr : RegP blk) :
    Hs c M (ptPair xb z o sc blk zl memo) (fun r ↦ MemoOk M (fun i ↦ M.e (xb + i)) r.1 ∧
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 r.2.big = sc.val M * partW M CMain.nu20 xb CMain.nu20 blk zl ∧
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 r.2.sml =
        sc.val M * partW M CMain.nu20 xb CMain.nu20 (shiftP blk) zl ∧
      r.2.pb.length = CMain.nu20 - 20 ∧ r.2.ps.length = CMain.nu20 - 20) := by
  have hnu : CMain.nu20 = 23 := rfl
  have hk : ncPre z o zl ≤ 20 := (ncPre_le z o zl).trans (hzl ▸ hr.1)
  refine hs_bind (chainG_spec hz ho _ memo (ncPre_le z o zl) hm) fun r ⟨hm', hv⟩ ↦
    hs_pure ⟨hm', ?_, ?_, topK_length _, topK_length _⟩
  · simp only [ZT.big]
    rw [← keyOf_top _ hk, tval, kprod_keyOf, hv, mul_assoc,
      partW_eq hz ho hzl (by have := hr.1; (clear * - hzl hnu this; omega)) le_rfl, e0f_nu, one_mul]
  · simp only [ZT.sml]
    rw [keyOf_congr (bitP z o CMain.nu20 blk zl) (bitP z o CMain.nu20 (shiftP blk) zl) _ 20
        (fun i _ hi ↦ (bitP_shift_lo z o blk zl hr hi).symm),
      ← keyOf_top _ hk, tval, kprod_keyOf, hv, mul_assoc,
      partW_eq hz ho (by rw [shiftP_vc]; exact hzl) (by rw [shiftP_vc]; have := hr.1; (clear * - hzl hnu this; omega)) le_rfl, e0f_nu,
      one_mul]

/-- The pair of a ring claim on a regular block. -/
def rgPair (xb : ℕ) (z sc : Cell) (blk : Placement) (pt cs : List Cell) : BM ZT := do
  let lf ← ringLeaf blk.variableCount pt cs xb z.n
  pure ⟨sc, lf, topK (selbit blk), topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩

theorem rgPair_spec {xb : ℕ} {z : Cell} (hz : z.val M = 0) (hzE : z.ty = .E) {sc : Cell} {blk : Placement}
    {pt cs : List Cell} (hr : RegP blk) (hpt : pt.length = blk.variableCount) (hcs : cs.length = 64)
    (hbs : sz (binDec 64 blk.variableCount 0) = blk.variableCount) :
    Hs c M (rgPair xb z sc blk pt cs) (fun t ↦
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big = sc.val M * (blk.eqAbove (xsOf M CMain.nu20 xb) *
        ringWeight (vs M pt) ((xsOf M CMain.nu20 xb).take blk.variableCount) (vs M cs)) ∧
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml = sc.val M * ((shiftP blk).eqAbove (xsOf M CMain.nu20 xb) *
        ringWeight (vs M pt) ((xsOf M CMain.nu20 xb).take blk.variableCount) (vs M cs)) ∧
      t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20) := by
  have hnu : CMain.nu20 = 23 := rfl
  have hv := hr.1
  refine hs_bind (ringLeaf_spec (zval_e hz hzE) hpt hcs hbs ((xsOf M CMain.nu20 xb).take blk.variableCount)
    (by rw [List.length_take, xs_length]; (clear * - hpt hbs hnu hv; omega))
    (fun n hn ↦ by rw [getD_take' _ _ hn, xs_getD (by (clear * - hpt hbs hnu hv hn; omega))])) fun lf hlf ↦
      hs_pure ⟨?_, ?_, topK_length _, topK_length _⟩
  · simp only [ZT.big]
    rw [← keyOf_top _ hv, tval, kprod_keyOf, hlf, eqAbove_prod blk _ (fun i ↦ M.e (xb + i))
      (by rw [xs_length]; (clear * - hpt hbs hnu hv; omega)) (fun i hi ↦ xs_getD (by rwa [xs_length] at hi)), xs_length]
    ring
  · simp only [ZT.sml]
    rw [keyOf_congr (selbit blk) (selbit (shiftP blk)) _ 20 (fun i h1 h2 ↦ (selbit_shift_lo blk hr h1 h2).symm),
      ← keyOf_top _ hv, tval, kprod_keyOf, hlf, eqAbove_prod (shiftP blk) _ (fun i ↦ M.e (xb + i))
      (by rw [xs_length, shiftP_vc]; (clear * - hpt hbs hnu hv; omega)) (fun i hi ↦ xs_getD (by rwa [xs_length] at hi)), xs_length, shiftP_vc]
    ring

/-- The pairs of a sum's parts (scale `sc · c_j`). -/
def partsPairs (xb : ℕ) (z o sc : Cell) : List (Cell × Placement × List Cell) → Memo → BM (Memo × List ZT)
  | [], memo => pure (memo, [])
  | x :: ps, memo => do
    let sc' ← mulAdd .E sc x.1 z
    let r ← ptPair xb z o sc' x.2.1 x.2.2 memo
    let r' ← partsPairs xb z o sc ps r.1
    pure (r'.1, r.2 :: r'.2)

theorem partsPairs_spec {xb : ℕ} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) {sc : Cell} :
    ∀ (ps : List (Cell × Placement × List Cell)) (memo : Memo),
      (ps.all fun x ↦ decide (x.2.1.variableCount ≤ CMain.nu20) && decide (x.2.2.length = x.2.1.variableCount)) =
        true →
      (∀ x ∈ ps, RegP x.2.1) → MemoOk M (fun i ↦ M.e (xb + i)) memo →
      Hs c M (partsPairs xb z o sc ps memo) (fun r ↦ MemoOk M (fun i ↦ M.e (xb + i)) r.1 ∧
        (r.2.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big).sum =
          sc.val M * (ps.map fun x ↦ x.1.val M * partW M CMain.nu20 xb CMain.nu20 x.2.1 x.2.2).sum ∧
        (r.2.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml).sum =
          sc.val M * (ps.map fun x ↦ x.1.val M * partW M CMain.nu20 xb CMain.nu20 (shiftP x.2.1) x.2.2).sum ∧
        ∀ t ∈ r.2, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20)
  | [], memo, _, _, hm => hs_pure ⟨hm, by simp, by simp, by simp⟩
  | x :: ps, memo, hwf, hr, hm => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨-, h2⟩, hrest⟩ := hwf
    unfold partsPairs
    refine hs_bind (hs_mulAdd _ _ _ _) fun sc' hsc ↦ hs_bind (ptPair_spec hz ho hm h2 (hr x List.mem_cons_self))
      fun r ⟨hm', hb, hs, hl1, hl2⟩ ↦ hs_bind (partsPairs_spec hz ho ps r.1 hrest
        (fun y hy ↦ hr y (List.mem_cons_of_mem _ hy)) hm') fun r' ⟨hm'', hb', hs', hl'⟩ ↦
      hs_pure ⟨hm'', ?_, ?_, ?_⟩
    · rw [List.map_cons, List.sum_cons, hb, hb', hsc, hz, List.map_cons, List.sum_cons]; ring
    · rw [List.map_cons, List.sum_cons, hs, hs', hsc, hz, List.map_cons, List.sum_cons]; ring
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hl1, hl2⟩
      · exact hl' t ht

/-- The pairs of a regular claim (scale cell `sc`). -/
def regPairs (xb : ℕ) (z o sc : Cell) (cc : CClaim) (memo : Memo) : BM (Memo × List ZT) :=
  match cc.cw with
  | .point blk zl => do
    let r ← ptPair xb z o sc blk zl memo
    pure (r.1, [r.2])
  | .ring blk pt cs => do
    let t ← rgPair xb z sc blk pt cs
    pure (memo, [t])
  | .sum _ parts => partsPairs xb z o sc parts memo

theorem take_nu (xb : ℕ) : (xsOf M CMain.nu20 xb).take CMain.nu20 = xsOf M CMain.nu20 xb :=
  List.take_of_length_le (by rw [xs_length])

theorem eqAbove_nu (y : List FE) (hy : y.length = CMain.nu20) : (⟨CMain.nu20, 0⟩ : Placement).eqAbove y = 1 := by
  simp [Placement.eqAbove, hy, selectorPoint, eqEval]

theorem regPairs_spec {xb : ℕ} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) {sc : Cell}
    {cc : CClaim} {memo : Memo} (hwf : WF1 CMain.nu20 cc = true) (hr : RegC cc)
    (hm : MemoOk M (fun i ↦ M.e (xb + i)) memo) :
    Hs c M (regPairs xb z o sc cc memo) (fun r ↦ MemoOk M (fun i ↦ M.e (xb + i)) r.1 ∧
      (r.2.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big).sum =
        sc.val M * (cc.val M).2.onStack.1 (xsOf M CMain.nu20 xb) ∧
      (r.2.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml).sum =
        sc.val M * smallW M cc (xsOf M CMain.nu20 xb) ∧
      ∀ t ∈ r.2, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20) := by
  rcases cc with ⟨com, cw, v⟩
  cases cw with
  | point blk zl =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [RegC] at hr
    unfold regPairs
    refine hs_bind (ptPair_spec hz ho hm hwf.2 hr) fun r ⟨hm', hb, hs, hl1, hl2⟩ ↦ hs_pure ⟨hm', ?_, ?_, ?_⟩
    · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hb, partW, take_nu]; rfl
    · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hs, partW, take_nu]; rfl
    · intro t ht; rcases List.mem_singleton.mp ht with rfl; exact ⟨hl1, hl2⟩
  | ring blk pt cs =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := hwf
    simp only [RegC] at hr
    unfold regPairs
    refine hs_bind (rgPair_spec hz hzE hr h2 h3 h4) fun t ⟨hb, hs, hl1, hl2⟩ ↦ hs_pure ⟨hm, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hb]; rfl
    · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hs]; rfl
    · intro t' ht; rcases List.mem_singleton.mp ht with rfl; exact ⟨hl1, hl2⟩
  | sum nu parts =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [RegC] at hr
    obtain ⟨rfl, hp⟩ := hr
    show Hs c M (partsPairs xb z o sc parts memo) _
    refine hs_mono (partsPairs_spec hz ho parts memo hwf.2 hp hm) fun r ⟨hm', hb, hs, hl⟩ ↦ ⟨hm', ?_, ?_, hl⟩
    · rw [hb]
      show _ = sc.val M * (sumClaim CMain.nu20 (parts.map fun e ↦ (e.1.val M, e.2.1, vs M e.2.2)) (v.val M)).onStack.1
        (xsOf M CMain.nu20 xb)
      rw [sumClaim_onStack _ _ _ (xs_length CMain.nu20 xb), List.map_map]
      refine congrArg (sc.val M * ·) (congrArg List.sum (List.map_congr_left fun x _ ↦ ?_))
      simp only [Function.comp_apply, partW, take_nu, partB, BlockClaim.point, BlockClaim.onStack]
    · rw [hs]
      show _ = sc.val M * (sumClaim CMain.nu20 (parts.map fun e ↦ (e.1.val M, shiftP e.2.1, vs M e.2.2)) 0).onStack.1
        (xsOf M CMain.nu20 xb)
      rw [sumClaim_onStack _ _ _ (xs_length CMain.nu20 xb), List.map_map]
      refine congrArg (sc.val M * ·) (congrArg List.sum (List.map_congr_left fun x _ ↦ ?_))
      simp only [Function.comp_apply, partW, take_nu, partB, BlockClaim.point, BlockClaim.onStack]

theorem hs_and {α : Type} {m : BM α} {P Q : α → Prop} (hP : Hs c M m P) (hQ : Hs c M m Q) :
    Hs c M m (fun a ↦ P a ∧ Q a) := fun p h ↦ ⟨hP p h, hQ p h⟩

/-! ## The claims' terms -/

/-- The term pairs of the regular claims and the terms of the muxed ones (scale cells `sp + i`). -/
def zTerms (xb : ℕ) (z o : Cell) (sp : ℕ) : ℕ → List (CClaim × Bool) → Memo → BM (Memo × List ZT × List TC)
  | _, [], memo => pure (memo, [], [])
  | i, e :: cl, memo =>
    if e.2 then do
      let r ← regPairs xb z o (ec (sp + i)) e.1 memo
      let r' ← zTerms xb z o sp (i + 1) cl r.1
      pure (r'.1, r.2 ++ r'.2.1, r'.2.2)
    else do
      let r ← oneClaim CMain.nu20 xb z o (ec (sp + i)) e.1 memo
      let r' ← zTerms xb z o sp (i + 1) cl r.1
      pure (r'.1, r'.2.1, r.2 ++ r'.2.2)

/-- The big weight of a claim at `xs`. -/
def wBig (M : Mem) (xs : List FE) (e : CClaim × Bool) : FE := (e.1.val M).2.onStack.1 xs

/-- The small weight of a claim at `xs` (regular: moved blocks; muxed: its own form). -/
def wSml (M : Mem) (xs : List FE) (e : CClaim × Bool) : FE :=
  if e.2 then smallW M e.1 xs else (e.1.val M).2.onStack.1 xs

theorem zTerms_spec {xb : ℕ} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) {sp N : ℕ}
    {s : FE} (hs : ∀ j < N, M.e (sp + j) = s ^ j) :
    ∀ (cl : List (CClaim × Bool)) (i : ℕ) (memo : Memo),
      (∀ e ∈ cl, WF1 CMain.nu20 e.1 = true ∧ (e.2 = true → RegC e.1)) →
      MemoOk M (fun i ↦ M.e (xb + i)) memo → i + cl.length ≤ N →
      Hs c M (zTerms xb z o sp i cl memo) (fun r ↦ MemoOk M (fun i ↦ M.e (xb + i)) r.1 ∧
        (r.2.1.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big).sum +
          (r.2.2.map (tval M (fun i ↦ M.e (xb + i)) CMain.nu20)).sum =
            bsum s i (cl.map (wBig M (xsOf M CMain.nu20 xb))) ∧
        (r.2.1.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml).sum +
          (r.2.2.map (tval M (fun i ↦ M.e (xb + i)) CMain.nu20)).sum =
            bsum s i (cl.map (wSml M (xsOf M CMain.nu20 xb))) ∧
        ∀ t ∈ r.2.1, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20)
  | [], _, memo, _, hm, _ => hs_pure ⟨hm, by simp [bsum], by simp [bsum], by simp⟩
  | e :: cl, i, memo, hw, hm, hN => by
    simp only [List.length_cons] at hN
    obtain ⟨hwf, hreg⟩ := hw e List.mem_cons_self
    have hw' : ∀ e' ∈ cl, WF1 CMain.nu20 e'.1 = true ∧ (e'.2 = true → RegC e'.1) :=
      fun e' he' ↦ hw e' (List.mem_cons_of_mem _ he')
    have hsi : (ec (sp + i)).val M = s ^ i := by rw [Cell.val_E, hs i (by (clear * - hN; omega))]
    unfold zTerms
    by_cases he : e.2 = true
    · rw [if_pos he]
      refine hs_bind (regPairs_spec hz ho hzE hwf (hreg he) hm) fun r ⟨hm', hb, hsm, hl⟩ ↦
        hs_bind (zTerms_spec hz ho hzE hs cl (i + 1) r.1 hw' hm' (by (clear * - hN; omega))) fun r' ⟨hm'', hb', hs', hl'⟩ ↦
          hs_pure ⟨hm'', ?_, ?_, ?_⟩
      · rw [List.map_append, List.sum_append, add_assoc, hb', hb, hsi, List.map_cons, bsum]; rfl
      · rw [List.map_append, List.sum_append, add_assoc, hs', hsm, hsi, List.map_cons, bsum, wSml, if_pos he]
      · intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hl t ht
        · exact hl' t ht
    · rw [if_neg he]
      refine hs_bind (oneClaim_spec hz ho hzE hwf hm) fun r ⟨hm', hv⟩ ↦
        hs_bind (zTerms_spec hz ho hzE hs cl (i + 1) r.1 hw' hm' (by (clear * - hN; omega))) fun r' ⟨hm'', hb', hs', hl'⟩ ↦
          hs_pure ⟨hm'', ?_, ?_, hl'⟩
      · dsimp only
        rw [List.map_append, List.sum_append, List.map_cons, bsum, ← hb', wBig, ← hsi, ← hv]
        ring
      · dsimp only
        rw [List.map_append, List.sum_append, List.map_cons, bsum, ← hs', wSml, if_neg he, ← hsi, ← hv]
        ring

/-! ## The cut at depth 20 -/

/-- A pair's two top keys. -/
abbrev ZK : Type := List Bool × List Bool

/-- The top keys of a pair. -/
def zkey (t : ZT) : ZK := (t.pb, t.ps)

/-- The distinct top-key pairs. -/
def keysOf (ts : List ZT) : List ZK := (ts.map zkey).dedup

/-- The terms below depth 20 of the pairs with top keys `k`. -/
def grp (ts : List ZT) (k : ZK) : List TC := (ts.filter fun t ↦ zkey t == k).map ZT.low

/-- **The subtries below depth 20**, one per top-key pair. -/
def lowsG (xb : ℕ) (z : Cell) (ts : List ZT) : List ZK → BM (List (ZK × Cell))
  | [] => pure []
  | k :: ks => do
    let v ← trieG xb z 20 (grp ts k)
    let r ← lowsG xb z ts ks
    pure ((k, v) :: r)

theorem lowsG_spec {xb : ℕ} {z : Cell} (hz : z.val M = 0) (ts : List ZT) (F : ZK → FE) :
    ∀ ks : List ZK, Hs c M (lowsG xb z ts ks) (fun r ↦ (r.map fun e ↦ F e.1 * e.2.val M).sum =
      (ks.map fun k ↦ F k * ((grp ts k).map (tval M (fun i ↦ M.e (xb + i)) 20)).sum).sum)
  | [] => hs_pure (by simp)
  | k :: ks => by
    unfold lowsG
    exact hs_bind (trieG_spec hz 20 _) fun v hv ↦ hs_bind (lowsG_spec hz ts F ks) fun r hr ↦
      hs_pure (by rw [List.map_cons, List.sum_cons, hr, hv, List.map_cons, List.sum_cons])

theorem sum_ite_mem {K : Type} [DecidableEq K] (a : FE) (k₀ : K) :
    ∀ L : List K, L.Nodup → k₀ ∈ L → (L.map fun k ↦ if k₀ = k then a else 0).sum = a
  | [], _, h => absurd h (by simp)
  | k :: L, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.sum_cons]
    by_cases e : k₀ = k
    · subst e
      rw [if_pos rfl, List.map_congr_left (g := fun _ ↦ (0 : FE)) fun k' hk' ↦ if_neg fun (h : k₀ = k') ↦ hn.1 (h ▸ hk')]
      simp
    · rw [if_neg e, zero_add, sum_ite_mem a k₀ L hn.2 ((List.mem_cons.mp h).resolve_left e)]

/-- **Regrouping by top keys.** -/
theorem sum_groups (f : ZT → FE) (ts : List ZT) : ∀ L : List ZK, L.Nodup → (∀ t ∈ ts, zkey t ∈ L) →
    (ts.map f).sum = (L.map fun k ↦ ((ts.filter fun t ↦ zkey t == k).map f).sum).sum := by
  induction ts with
  | nil => intro L _ _; simp
  | cons t ts ih =>
    intro L hn hm
    rw [List.map_cons, List.sum_cons, ih L hn fun t' ht' ↦ hm t' (List.mem_cons_of_mem _ ht')]
    have e2 : ∀ k, (((t :: ts).filter fun t ↦ zkey t == k).map f).sum =
        (if zkey t = k then f t else 0) + ((ts.filter fun t ↦ zkey t == k).map f).sum := fun k ↦ by
      by_cases h : zkey t = k <;> simp [List.filter_cons, h]
    rw [List.map_congr_left (fun k _ ↦ e2 k), List.sum_map_add,
      sum_ite_mem (f t) (zkey t) L hn (hm t List.mem_cons_self)]

theorem kprod_app (X : ℕ → FE) (m : ℕ) (r : List Bool) :
    ∀ p : List Bool, kprod X (m + p.length) (p ++ r) = kprod X (m + p.length) p * kprod X m r
  | [] => by simp [kprod]
  | b :: p => by
    have ih := kprod_app X m r p
    show fb b (X (m + p.length)) * kprod X (m + p.length) (p ++ r) =
      fb b (X (m + p.length)) * kprod X (m + p.length) p * kprod X m r
    rw [ih]; ring

theorem kprod_split (X : ℕ → FE) (p r : List Bool) (hp : p.length = CMain.nu20 - 20) :
    kprod X CMain.nu20 (p ++ r) = kprod X CMain.nu20 p * kprod X 20 r := by
  have e : CMain.nu20 = 20 + p.length := by rw [hp]; rfl
  rw [e]; exact kprod_app X 20 r p

/-- **A top over the subtries**: the top keys `sel` (`ν − 20` bits, a function `selk` of the key pair) over the
shared rests give the terms with those keys. -/
theorem top_val (X : ℕ → FE) (ts : List ZT) (sel : ZT → List Bool) (selk : ZK → List Bool)
    (hl : ∀ t ∈ ts, (sel t).length = CMain.nu20 - 20) (hk : ∀ t, sel t = selk (zkey t)) :
    ((keysOf ts).map fun k ↦ kprod X CMain.nu20 (selk k) * ((grp ts k).map (tval M X 20)).sum).sum =
      (ts.map fun t ↦ tval M X CMain.nu20 ⟨t.sc, sel t ++ t.rest, t.lf⟩).sum := by
  have e1 : (ts.map fun t ↦ tval M X CMain.nu20 ⟨t.sc, sel t ++ t.rest, t.lf⟩) =
      ts.map fun t ↦ kprod X CMain.nu20 (sel t) * tval M X 20 t.low := List.map_congr_left fun t ht ↦ by
    simp only [tval, ZT.low, kprod_split X _ _ (hl t ht)]; ring
  rw [e1, sum_groups _ ts (keysOf ts) (List.nodup_dedup _) fun t ht ↦ by
    rw [keysOf, List.mem_dedup]; exact List.mem_map_of_mem ht]
  refine congrArg List.sum (List.map_congr_left fun k _ ↦ ?_)
  rw [grp, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun t ht ↦ ?_)
  have hz : zkey t = k := by simpa using (List.mem_filter.mp ht).2
  simp only [Function.comp_apply, hk t, hz]

/-! ## The basis -/

/-- **The batched weight in both shapes** at the point in the `E` cells `xb + i` (`x^σ`'s copies): the term pairs
and the muxed claims' terms (`zTerms`), the subtries below depth 20 (`lowsG`), the two tops, their mux. -/
def basisZ (cl : List (CClaim × Bool)) (sp xb : ℕ) (z o s : Cell) : BM Cell := do
  let r ← zTerms xb z o sp 0 cl []
  let lows ← lowsG xb z r.2.1 (keysOf r.2.1)
  let tb ← trieG xb z CMain.nu20 (lows.map (fun e ↦ (⟨o, e.1.1, e.2⟩ : TC)) ++ r.2.2)
  let ts ← trieG xb z CMain.nu20 (lows.map (fun e ↦ (⟨o, e.1.2, e.2⟩ : TC)) ++ r.2.2)
  muxG s tb ts

theorem basisZ_spec {cl : List (CClaim × Bool)} {sp xb : ℕ} {z o s : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hzE : z.ty = .E) (hw : ∀ e ∈ cl, WF1 CMain.nu20 e.1 = true ∧ (e.2 = true → RegC e.1)) (σ : FE)
    (hs : ∀ j < cl.length, M.e (sp + j) = σ ^ j) :
    Hs c M (basisZ cl sp xb z o s) (fun r ↦ r.val M = mux (s.val M)
      (bsum σ 0 (cl.map (wBig M (xsOf M CMain.nu20 xb)))) (bsum σ 0 (cl.map (wSml M (xsOf M CMain.nu20 xb))))) := by
  unfold basisZ
  refine hs_bind (zTerms_spec (N := cl.length) hz ho hzE hs cl 0 [] hw (fun _ h ↦ by simp at h) (by (clear * -; omega)))
    fun r ⟨_, hb, hsm, hl⟩ ↦ ?_
  set X : ℕ → FE := fun i ↦ M.e (xb + i)
  refine hs_bind (hs_and (lowsG_spec hz r.2.1 (fun k ↦ kprod X CMain.nu20 k.1) _)
    (lowsG_spec hz r.2.1 (fun k ↦ kprod X CMain.nu20 k.2) _)) fun lows ⟨hl1, hl2⟩ ↦
    hs_bind (trieG_spec hz CMain.nu20 _) fun tb htb ↦ hs_bind (trieG_spec hz CMain.nu20 _) fun ts hts ↦
      hs_mono (muxG_spec _ _ _) fun w hw ↦ ?_
  have t1 : ((lows.map fun e ↦ (⟨o, e.1.1, e.2⟩ : TC)).map (tval M X CMain.nu20)).sum =
      (r.2.1.map fun t ↦ tval M X CMain.nu20 t.big).sum := by
    rw [List.map_map]
    have : (lows.map ((tval M X CMain.nu20) ∘ fun e ↦ (⟨o, e.1.1, e.2⟩ : TC))) =
        lows.map fun e ↦ kprod X CMain.nu20 e.1.1 * e.2.val M :=
      List.map_congr_left fun e _ ↦ by simp only [Function.comp_apply, tval, ho, one_mul]
    rw [this, hl1, top_val X r.2.1 ZT.pb Prod.fst (fun t ht ↦ (hl t ht).1) fun _ ↦ rfl]
    rfl
  have t2 : ((lows.map fun e ↦ (⟨o, e.1.2, e.2⟩ : TC)).map (tval M X CMain.nu20)).sum =
      (r.2.1.map fun t ↦ tval M X CMain.nu20 t.sml).sum := by
    rw [List.map_map]
    have : (lows.map ((tval M X CMain.nu20) ∘ fun e ↦ (⟨o, e.1.2, e.2⟩ : TC))) =
        lows.map fun e ↦ kprod X CMain.nu20 e.1.2 * e.2.val M :=
      List.map_congr_left fun e _ ↦ by simp only [Function.comp_apply, tval, ho, one_mul]
    rw [this, hl2, top_val X r.2.1 ZT.ps Prod.snd (fun t ht ↦ (hl t ht).2) fun _ ↦ rfl]
    rfl
  rw [hw, htb, hts, List.map_append, List.sum_append, List.map_append, List.sum_append, t1, t2, hb, hsm]

/-! ## The shape cell, the muxed point, the claims -/

/-- **The child's shape cell** `σ' = (1 + d₁₈)(1 + d₁₉)` from `n' − 1`'s bits (the borrow chain's cells). -/
def sigmaG (mb : List Cell) (zc : Cell) : BM Cell := do
  let a ← onePlusG (mb.getD 18 default)
  let b ← onePlusG (mb.getD 19 default)
  mulAdd .E a b zc

theorem sigmaG_spec {mb : List Cell} {zc : Cell} (hz : zc.val M = 0) :
    Hs c M (sigmaG mb zc) (fun r ↦ r.val M = (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M)) :=
  hs_bind (onePlusG_spec _) fun a ha ↦ hs_bind (onePlusG_spec _) fun b hb ↦
    hs_mono (hs_mulAdd _ _ _ _) fun r hr ↦ by rw [hr, ha, hb, hz, add_zero]

theorem muxG_ty (s a b : Cell) (p : Ptr) : (muxG s a b p).1.ty = .E := rfl

/-- **The muxed terminal point** `x^σ_i = mux(σ, x_i, x_{(i+1) mod ν})` (the point in `E` cells `xb + i`). -/
def muxPtG (s : Cell) (xb : ℕ) : List ℕ → BM (List Cell)
  | [] => pure []
  | i :: is => do
    let m ← muxG s (ec (xb + i)) (ec (xb + (i + 1) % CMain.nu20))
    let r ← muxPtG s xb is
    pure (m :: r)

theorem muxPtG_spec (s : Cell) (xb : ℕ) : ∀ is : List ℕ, Hs c M (muxPtG s xb is) (fun r ↦ r.length = is.length ∧
    (∀ x ∈ r, x.ty = .E) ∧ ∀ j < is.length, (r.getD j default).val M =
      mux (s.val M) (M.e (xb + is.getD j 0)) (M.e (xb + (is.getD j 0 + 1) % CMain.nu20)))
  | [] => hs_pure ⟨rfl, by simp, by simp⟩
  | i :: is => by
    unfold muxPtG
    refine hs_bind (hs_and (muxG_spec _ _ _) (show Hs c M (muxG s (ec (xb + i)) (ec (xb + (i + 1) % CMain.nu20)))
        (fun r ↦ r.ty = .E) from fun p _ ↦ muxG_ty _ _ _ p))
      fun m ⟨hm, hmE⟩ ↦ hs_bind (muxPtG_spec s xb is) fun r ⟨hl, hE, hv⟩ ↦ hs_pure ⟨by simp [hl], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hmE
      · exact hE x hx
    · intro j hj
      rcases j with _ | j
      · simpa using hm
      · simpa using hv j (by simpa using hj)

/-- The claims in both shapes, related one by one (`ZRel`). -/
theorem zClaimsG_spec {s z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ cl : List CClaim, (∀ cc ∈ cl, ZWF z cc = true) →
      Hs c M (zClaimsG s z o cl) (fun r ↦ List.Forall₂ (ZRel M s) cl r)
  | [], _ => hs_pure List.Forall₂.nil
  | cc :: cl, h => by
    unfold zClaimsG
    exact hs_bind (zClaimG_spec hz ho cc (h cc List.mem_cons_self)) fun r hr ↦
      hs_bind (zClaimsG_spec hz ho cl fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')) fun rs hrs ↦
        hs_pure (List.Forall₂.cons hr hrs)

end Lvm.QShape
