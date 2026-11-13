-- New for lvm2 (CR-V): auxiliary lemmas for `LvmShape`'s closed-form tail values.
import LvmShapeVN
import LvmFieldCorrect
import LvmQRingWeight

/-!
# Tail values over `FE` in closed form (aux)

* **`eqEval`** as a product (`eqEval_prod`, `eqEval_append`, `eqEval_split`), cube points
  (`cubePt_split`, `cubePt_eq`: the cube point is `selectorPoint`);
* **cube sums**: `sum_eqEval_cube` (the full cube sums to `1`, characteristic two),
  `sum_eqEval_low` (the sub-cube with the top bits zero);
* **`tailSum_eqEval`**: the tail mass of an `eqEval` weight at a `ν`-point `ρ` (`ν = CMain.nu20`) is `tailPtF ρ`;
* `point_onStack`: a point claim's stack weight on a `ν`-list is one `eqEval`;
  `eqAbove_tail`: a block from word `2^22` has `eqAbove = 0` on every point below `2^22`;
* `ringWeight_eqEval`, `ringTailF_sum`, `ringTailN_fold`: the ring claim's pieces.
-/

set_option autoImplicit false

namespace Lvm.Shape

open Lvm

/-! ## `eqEval` -/

theorem eqEval_eq_prod (l r : List FE) : eqEval l r = (List.zipWith (fun x z ↦ 1 + x + z) l r).prod := by
  unfold eqEval; rw [List.prod_eq_foldl]

@[simp] theorem eqEval_nil_left (r : List FE) : eqEval [] r = 1 := by simp [eqEval_eq_prod]

@[simp] theorem eqEval_nil_right (l : List FE) : eqEval l [] = 1 := by simp [eqEval_eq_prod]

theorem eqEval_cons (x z : FE) (l r : List FE) : eqEval (x :: l) (z :: r) = (1 + x + z) * eqEval l r := by
  simp [eqEval_eq_prod]

theorem eqEval_append {l₁ l₂ r₁ r₂ : List FE} (h : l₁.length = r₁.length) :
    eqEval (l₁ ++ l₂) (r₁ ++ r₂) = eqEval l₁ r₁ * eqEval l₂ r₂ := by
  simp only [eqEval_eq_prod, List.zipWith_append h, List.prod_append]

/-- Splitting the second argument. -/
theorem eqEval_split (σ r₁ r₂ : List FE) (h : r₁.length ≤ σ.length) :
    eqEval σ (r₁ ++ r₂) = eqEval (σ.take r₁.length) r₁ * eqEval (σ.drop r₁.length) r₂ := by
  conv_lhs => rw [← List.take_append_drop r₁.length σ]
  exact eqEval_append (by simp [h])

/-- `eqEval` as a `Finset` product. -/
theorem eqEval_prod : ∀ (l r : List FE), l.length = r.length →
    eqEval l r = ∏ n ∈ Finset.range l.length, (1 + l.getD n 0 + r.getD n 0)
  | [], [], _ => by simp
  | x :: l, z :: r, h => by
    rw [eqEval_cons, eqEval_prod l r (by simpa using h), List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## Cube points -/

/-- The cube point of index `a` (`LvmShape`'s `boolPointF`, which is defined below this module). -/
def cubePt (μ a : ℕ) : List FE := (List.range μ).map fun i ↦ if a.testBit i then 1 else 0

@[simp] theorem cubePt_length (n a : ℕ) : (cubePt n a).length = n := by simp [cubePt]

theorem cubePt_split (p q m i : ℕ) (hi : i < 2 ^ p) :
    cubePt (p + q) (2 ^ p * m + i) = cubePt p i ++ cubePt q m := by
  unfold cubePt
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun j hj ↦ ?_
    simp only [Nat.testBit_two_pow_mul_add m hi, List.mem_range.1 hj, ite_true]
  · refine List.map_congr_left fun j _ ↦ ?_
    simp only [Function.comp, Nat.testBit_two_pow_mul_add m hi, show ¬ (p + j < p) by omega,
      ite_false, Nat.add_sub_cancel_left]

@[simp] theorem eOfNat_zero : eOfNat 0 = 0 := rfl

@[simp] theorem eOfNat_one : eOfNat 1 = 1 := rfl

/-- The cube point is `selectorPoint`. -/
theorem cubePt_eq (n a : ℕ) : cubePt n a = selectorPoint a n := by
  unfold cubePt selectorPoint
  refine List.map_congr_left fun i _ ↦ ?_
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ i) with h | h <;> simp [h]

theorem two_FE : (2 : FE) = 0 := CharTwo.two_eq_zero

/-! ## Cube sums -/

theorem sum_range_mul_split {M : Type*} [AddCommMonoid M] (N K : ℕ) (g : ℕ → M) :
    ∑ a ∈ Finset.range (N * K), g a = ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range N, g (N * k + i) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- **The full cube sums to `1`** (characteristic two: `eq(x, 0) + eq(x, 1) = 1`). -/
theorem sum_eqEval_cube (n : ℕ) (σ : List FE) (hσ : σ.length = n) :
    ∑ i ∈ Finset.range (2 ^ n), eqEval σ (cubePt n i) = 1 := by
  induction n generalizing σ with
  | zero => simp [cubePt]
  | succ n ih =>
    rw [pow_succ, sum_range_mul_split]
    have e : ∀ k ∈ Finset.range 2, ∑ i ∈ Finset.range (2 ^ n), eqEval σ (cubePt (n + 1) (2 ^ n * k + i)) =
        (∑ i ∈ Finset.range (2 ^ n), eqEval (σ.take n) (cubePt n i)) *
          eqEval (σ.drop n) (cubePt 1 k) := by
      intro k _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [cubePt_split n 1 k i (Finset.mem_range.1 hi), eqEval_split _ _ _ (by simp [hσ]),
        cubePt_length]
    rw [Finset.sum_congr rfl e, ih _ (by simp [hσ])]
    obtain ⟨x, hx⟩ : ∃ x, σ.drop n = [x] := List.length_eq_one_iff.1 (by simp [hσ])
    simp only [one_mul, hx, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cubePt,
      List.range_one, List.map_cons, List.map_nil, Nat.testBit_zero, eqEval_cons, eqEval_nil_left]
    norm_num
    linear_combination (1 + x) * two_FE

/-- **The sub-cube with the top `q` bits zero.** -/
theorem sum_eqEval_low (p q : ℕ) (σ : List FE) (hσ : σ.length = p + q) :
    ∑ i ∈ Finset.range (2 ^ p), eqEval σ (cubePt (p + q) i) = eqEval (σ.drop p) (cubePt q 0) := by
  have e : ∀ i ∈ Finset.range (2 ^ p), eqEval σ (cubePt (p + q) i) =
      eqEval (σ.take p) (cubePt p i) * eqEval (σ.drop p) (cubePt q 0) := by
    intro i hi
    have := cubePt_split p q 0 i (Finset.mem_range.1 hi)
    rw [Nat.mul_zero, Nat.zero_add] at this
    rw [this, eqEval_split _ _ _ (by simp [hσ]), cubePt_length]
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul, sum_eqEval_cube p _ (by simp [hσ]), one_mul]

/-! ## The tail mass of an `eqEval` weight -/

theorem getD_eq_take_drop (ρ : List FE) (k j : ℕ) (hj : j < 2) :
    ρ.getD (k + j) 0 = ((ρ.drop k).take 2).getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]

/-- **The tail mass of `eqEval ρ`** (`ρ` of `ν = CMain.nu20` coordinates): rows `0 … 17` sum to `1`, rows 18–19
give `1 − (1 − ρ₁₈)(1 − ρ₁₉)`, lanes 20–21 `Σ_l eq(ρ₂₀,₂₁; l) z*_l`, the block bit 22 `eq(ρ₂₂; 0)` (ν = 23). -/
theorem tailSum_eqEval (ρ : List FE) (hρ : ρ.length = CMain.nu20) :
    ∑ a ∈ (Finset.range (2 ^ 22)).filter (fun a ↦ 2 ^ 18 ≤ a % 2 ^ 20),
      eqEval ρ (cubePt CMain.nu20 a) * zStarF (a / 2 ^ 20) = tailPtF ρ := by
  rw [Finset.sum_filter, show 2 ^ 22 = 2 ^ 20 * 4 by norm_num, sum_range_mul_split]
  have e : ∀ k ∈ Finset.range 4, ∑ i ∈ Finset.range (2 ^ 20),
      (if 2 ^ 18 ≤ (2 ^ 20 * k + i) % 2 ^ 20 then
        eqEval ρ (cubePt CMain.nu20 (2 ^ 20 * k + i)) * zStarF ((2 ^ 20 * k + i) / 2 ^ 20) else 0) =
      (∑ i ∈ Finset.range (2 ^ 20), if 2 ^ 18 ≤ i then eqEval (ρ.take 20) (cubePt 20 i) else 0) *
        (eqEval (ρ.drop 20) (cubePt 3 k) * zStarF k) := by
    intro k _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    have hm : (2 ^ 20 * k + i) % 2 ^ 20 = i := by omega
    have hd : (2 ^ 20 * k + i) / 2 ^ 20 = k := by omega
    rw [hm, hd, show CMain.nu20 = 20 + 3 from rfl, cubePt_split 20 3 k i hi',
      eqEval_split _ _ _ (by simp [hρ, CMain.nu20]), cubePt_length]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have h1 : (∑ i ∈ Finset.range (2 ^ 20), if 2 ^ 18 ≤ i then eqEval (ρ.take 20) (cubePt 20 i) else 0) =
      1 - eqEval ((ρ.drop 18).take 2) (cubePt 2 0) := by
    have hs := sum_eqEval_cube 20 (ρ.take 20) (by simp [hρ, CMain.nu20])
    have hl : ∑ i ∈ Finset.range (2 ^ 18), eqEval (ρ.take 20) (cubePt 20 i) =
        eqEval ((ρ.take 20).drop 18) (cubePt 2 0) := sum_eqEval_low 18 2 _ (by simp [hρ, CMain.nu20])
    rw [List.drop_take] at hl
    rw [show 2 ^ 20 = 2 ^ 18 + 3 * 2 ^ 18 by norm_num, Finset.sum_range_add] at hs ⊢
    rw [Finset.sum_eq_zero (fun i hi ↦ ite_eq_right_iff.2 fun h ↦ absurd h (by simpa using hi))]
    simp only [Nat.le_add_right, ite_true, zero_add]
    linear_combination hs - hl
  have h2 : ∀ k ∈ Finset.range 4, eqEval (ρ.drop 20) (cubePt 3 k) * zStarF k =
      eqEval ((ρ.drop 20).take 2) (selectorPoint k 2) * zStarF k *
        eqEval (ρ.drop 22) (selectorPoint 0 (CMain.nu20 - 22)) := by
    intro k hk
    have := cubePt_split 2 1 0 k (by simpa using hk)
    rw [Nat.mul_zero, Nat.zero_add] at this
    rw [show (3 : ℕ) = 2 + 1 from rfl, this, eqEval_split _ _ _ (by simp [CMain.nu20] at hρ ⊢; omega), cubePt_length,
      List.drop_drop, cubePt_eq, cubePt_eq]
    rw [show CMain.nu20 - 22 = 1 from rfl]; ring
  rw [h1, Finset.sum_congr rfl h2]
  obtain ⟨u, w, hu⟩ : ∃ u w, (ρ.drop 18).take 2 = [u, w] := List.length_eq_two.1 (by simp [CMain.nu20] at hρ ⊢; omega)
  have g18 := getD_eq_take_drop ρ 18 0 (by norm_num)
  have g19 := getD_eq_take_drop ρ 18 1 (by norm_num)
  rw [hu] at g18 g19
  simp only [Nat.add_zero, show 18 + 1 = 19 from rfl, List.getD_cons_zero, List.getD_cons_succ] at g18 g19
  unfold tailPtF
  rw [g18, g19, hu]
  simp only [cubePt, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    Nat.zero_testBit, Bool.false_eq_true, ite_false, eqEval_cons, eqEval_nil_left,
    Finset.sum_range_succ, Finset.sum_range_zero, List.sum_cons, List.sum_nil,
    List.cons_append, CharTwo.sub_eq_add, add_zero]
  ring
/-! ## The tail sum of a weight -/

/-- `LvmShape`'s `tailValueF` (stated here on `cubePt`). -/
def tailSum (w : List FE → FE) : FE :=
  ∑ a ∈ (Finset.range (2 ^ 22)).filter (fun a ↦ 2 ^ 18 ≤ a % 2 ^ 20),
    w (cubePt CMain.nu20 a) * zStarF (a / 2 ^ 20)

theorem tailSum_congr {w w' : List FE → FE} (h : ∀ a < 2 ^ 22, w (cubePt CMain.nu20 a) = w' (cubePt CMain.nu20 a)) :
    tailSum w = tailSum w' := by
  unfold tailSum
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [h a (Finset.mem_range.1 (Finset.mem_filter.1 ha).1)]

theorem tailSum_zero {w : List FE → FE} (h : ∀ a < 2 ^ 22, w (cubePt CMain.nu20 a) = 0) : tailSum w = 0 := by
  unfold tailSum
  refine Finset.sum_eq_zero fun a ha ↦ ?_
  rw [h a (Finset.mem_range.1 (Finset.mem_filter.1 ha).1), zero_mul]

theorem tailSum_eqEval' (ρ : List FE) (hρ : ρ.length = CMain.nu20) : tailSum (eqEval ρ) = tailPtF ρ :=
  tailSum_eqEval ρ hρ

/-! ## Per claim kind -/

/-- A point claim's stack weight on a `ν`-list is one `eqEval`. -/
theorem point_onStack (k idx : ℕ) (z x : List FE) (hz : z.length = k) (hx : x.length = CMain.nu20)
    (hk : k ≤ CMain.nu20) (v : FE) :
    (BlockClaim.point ⟨k, idx⟩ z v).onStack.1 x = eqEval (z ++ selectorPoint (idx >>> k) (CMain.nu20 - k)) x := by
  conv_rhs => rw [← List.take_append_drop k x]
  rw [eqEval_append (by simp [hz, hx, hk])]
  simp only [BlockClaim.onStack, BlockClaim.point, Placement.eqAbove, hx]
  ring

theorem tailSum_point (k idx : ℕ) (z : List FE) (hz : z.length = k) (hk : k ≤ CMain.nu20) (v : FE) :
    tailSum (BlockClaim.point ⟨k, idx⟩ z v).onStack.1 = tailPtF (z ++ selectorPoint (idx >>> k) (CMain.nu20 - k)) := by
  rw [tailSum_congr (w' := eqEval (z ++ selectorPoint (idx >>> k) (CMain.nu20 - k)))
    (fun a _ ↦ point_onStack k idx z _ hz (by simp) hk v)]
  exact tailSum_eqEval _ (by simp [selectorPoint, hz]; omega)

theorem one_add_one_FE : (1 : FE) + 1 = 0 := CharTwo.add_self_eq_zero 1

/-- **A `D` point claim's tail.** -/
theorem tailPtF_D (r : List FE) (hr : r.length = 20) (l : ℕ) (hl : l < 4) :
    tailPtF (r ++ selectorPoint l 2 ++ selectorPoint 0 (CMain.nu20 - 22)) = tailDF r l := by
  have hs : ∀ m, (selectorPoint m 2).length = 2 := fun m ↦ by simp [selectorPoint]
  have g18 : (r ++ selectorPoint l 2 ++ selectorPoint 0 (CMain.nu20 - 22)).getD 18 0 = r.getD 18 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hr]
  have g19 : (r ++ selectorPoint l 2 ++ selectorPoint 0 (CMain.nu20 - 22)).getD 19 0 = r.getD 19 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hr]
  have d20 : (r ++ selectorPoint l 2 ++ selectorPoint 0 (CMain.nu20 - 22)).drop 20 =
      selectorPoint l 2 ++ selectorPoint 0 (CMain.nu20 - 22) := by
    rw [List.append_assoc, List.drop_left' hr]
  have d22 : (r ++ selectorPoint l 2 ++ selectorPoint 0 (CMain.nu20 - 22)).drop 22 =
      selectorPoint 0 (CMain.nu20 - 22) := by
    rw [show 22 = 20 + 2 from rfl, ← List.drop_drop, d20, List.drop_left' (hs l)]
  unfold tailPtF tailDF
  rw [g18, g19, d20, d22, List.take_left' (hs l)]
  interval_cases l <;>
    simp [selectorPoint, List.range_succ, eqEval_cons, one_add_one_FE, CMain.nu20]
/-- **A boundary claim's tail** (`m < 2^18`: bits 18, 19 are `0`). -/
theorem tailPtF_bnd (m : ℕ) (hm : m < 2 ^ 18) (l : ℕ) :
    tailPtF (selectorPoint m 20 ++ selectorPoint l 2 ++ selectorPoint 0 (CMain.nu20 - 22)) = 0 := by
  have g : ∀ j, 18 ≤ j → j < 20 →
      (selectorPoint m 20 ++ selectorPoint l 2 ++ selectorPoint 0 (CMain.nu20 - 22)).getD j 0 = 0 := by
    intro j h1 h2
    have hb : (m >>> j) % 2 = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) h1))]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, selectorPoint, h2, hb]
  unfold tailPtF
  rw [g 18 le_rfl (by norm_num), g 19 (by norm_num) (by norm_num)]
  simp

/-- **A block from word `2^22` misses every tail point**: its selector bit 22 is `1` (ν = 23). -/
theorem eqAbove_tail (b : Placement) (hb : 2 ^ 22 ≤ b.index) (hv : b.variableCount ≤ 22)
    (hlt : b.index < 2 ^ CMain.nu20) (a : ℕ) (ha : a < 2 ^ 22) : b.eqAbove (cubePt CMain.nu20 a) = 0 := by
  obtain ⟨j, hj22, hjν, hjb⟩ : ∃ j, 22 ≤ j ∧ j < CMain.nu20 ∧ b.index / 2 ^ j % 2 = 1 := by
    refine ⟨22, le_rfl, by norm_num, ?_⟩
    have h1 : b.index / 2 ^ 22 = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by simp only [CMain.nu20] at hlt; omega)
    rw [h1]
  have haj : a.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hj22))
  unfold Placement.eqAbove
  rw [eqEval_eq_prod]
  apply List.prod_eq_zero
  rw [List.mem_iff_getElem]
  refine ⟨j - b.variableCount, by simp [selectorPoint, cubePt]; omega, ?_⟩
  have hd : b.index / 2 ^ b.variableCount / 2 ^ (j - b.variableCount) = b.index / 2 ^ j := by
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' (le_trans hv hj22)]
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getElem_drop, selectorPoint,
    cubePt, Nat.add_sub_cancel' (le_trans hv hj22), haj, Nat.shiftRight_eq_div_pow, hd, hjb, eOfNat_one,
    Bool.false_eq_true, ite_false, add_zero]
  exact one_add_one_FE
theorem tailSum_off (c : BlockClaim) (hb : 2 ^ 22 ≤ c.block.index) (hv : c.block.variableCount ≤ 22)
    (hlt : c.block.index < 2 ^ CMain.nu20) : tailSum c.onStack.1 = 0 :=
  tailSum_zero fun a ha ↦ by
    simp only [BlockClaim.onStack, eqAbove_tail c.block hb hv hlt a ha, zero_mul]

theorem sumE_eq_zero (l : List FE) (h : ∀ x ∈ l, x = 0) : sumE l = 0 := by
  unfold sumE
  rw [← List.sum_eq_foldl]
  exact List.sum_eq_zero h

theorem tailSum_sum (parts : List (FE × Placement × List FE)) (v : FE)
    (hp : ∀ p ∈ parts, 2 ^ 22 ≤ p.2.1.index ∧ p.2.1.variableCount ≤ 22 ∧ p.2.1.index < 2 ^ CMain.nu20) :
    tailSum (sumClaim CMain.nu20 parts v).onStack.1 = 0 :=
  tailSum_zero fun a ha ↦ by
    have hx : (cubePt CMain.nu20 a).take CMain.nu20 = cubePt CMain.nu20 a := List.take_of_length_le (by simp)
    simp only [BlockClaim.onStack, sumClaim, hx]
    rw [sumE_eq_zero, mul_zero]
    intro x hx'
    obtain ⟨⟨c, blk, z⟩, hm, rfl⟩ := List.mem_map.1 hx'
    obtain ⟨h1, h2, h3⟩ := hp _ hm
    simp only [eqAbove_tail blk h1 h2 h3 a ha, mul_zero, zero_mul]

/-! ## The ring claim -/

theorem ringWeight_eqEval (pt y cs : List FE) (h : pt.length = y.length) :
    ringWeight pt y cs = ∑ i ∈ Finset.range cs.length, cs.getD i 0 * eqEval (pt.map (· ^ 2 ^ i)) y := by
  rw [Lvm.Loop.QRing.ringWeight_sum pt y cs h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eqEval_prod _ _ (by simp [h]), List.length_map]
  congr 1
  refine Finset.prod_congr rfl fun n hn ↦ ?_
  have hn' := Finset.mem_range.1 hn
  simp [Lvm.Loop.QRing.wf, List.getD_eq_getElem?_getD, hn']

theorem zipIdx_sum (f : FE × ℕ → FE) : ∀ (l : List FE) (k : ℕ),
    ((l.zipIdx k).map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i 0, k + i)
  | [], k => by simp
  | x :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum f l (k + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Nat.add_assoc, Nat.add_comm 1 i]

theorem ringTailF_sum (pt cs : List FE) :
    ringTailF pt cs = ∑ i ∈ Finset.range cs.length, cs.getD i 0 * tailPtF (pt.map (· ^ 2 ^ i)) := by
  unfold ringTailF
  rw [zipIdx_sum (fun e ↦ e.1 * tailPtF (pt.map (· ^ 2 ^ e.2))) cs 0]
  simp only [Nat.zero_add]

theorem tailSum_finsum (s : Finset ℕ) (f : ℕ → FE) (g : ℕ → List FE → FE) :
    tailSum (fun y ↦ ∑ i ∈ s, f i * g i y) = ∑ i ∈ s, f i * tailSum (g i) := by
  unfold tailSum
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by ring

theorem tailSum_ring (pt cs : List FE) (hpt : pt.length = CMain.nu20) (v : FE) :
    tailSum (⟨⟨CMain.nu20, 0⟩, fun y ↦ ringWeight pt y cs, v⟩ : BlockClaim).onStack.1 = ringTailF pt cs := by
  rw [tailSum_congr (w' := fun y ↦ ∑ i ∈ Finset.range cs.length, cs.getD i 0 * eqEval (pt.map (· ^ 2 ^ i)) y)
    fun a _ ↦ ?_]
  · rw [tailSum_finsum, ringTailF_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [tailSum_eqEval' _ (by simp [hpt])]
  · have hx : (cubePt CMain.nu20 a).take CMain.nu20 = cubePt CMain.nu20 a := List.take_of_length_le (by simp)
    simp only [BlockClaim.onStack, Placement.eqAbove, hx, cubePt_length, Nat.sub_self, Nat.zero_shiftRight,
      List.drop_of_length_le (le_of_eq (cubePt_length CMain.nu20 a))]
    rw [ringWeight_eqEval _ _ _ (by simp [hpt])]
    simp [selectorPoint]
/-! ## V_S's ring tail -/

theorem tailPtF_congr {ρ ρ' : List FE} (h : ρ.drop 18 = ρ'.drop 18) : tailPtF ρ = tailPtF ρ' := by
  have e : ∀ σ : List FE, tailPtF σ = (1 - (1 - (σ.drop 18).getD 0 0) * (1 - (σ.drop 18).getD 1 0)) *
      ((List.range 4).map fun l ↦ eqEval (((σ.drop 18).drop 2).take 2) (selectorPoint l 2) * zStarF l).sum *
      eqEval ((σ.drop 18).drop 4) (selectorPoint 0 (CMain.nu20 - 22)) := by
    intro σ
    simp only [tailPtF, List.drop_drop, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [e, e ρ', h]
theorem ringTailN_fold (pt : List FE) : ∀ (cs : List FE) (a : FE) (k : ℕ),
    (cs.foldl (fun (acc : FE × List FE) c ↦
      (acc.1 + c * tailPtF (List.replicate 18 0 ++ acc.2), acc.2.map FE.sq))
        (a, (pt.drop 18).map (· ^ 2 ^ k))).1 =
      a + ∑ i ∈ Finset.range cs.length, cs.getD i 0 * tailPtF (pt.map (· ^ 2 ^ (k + i)))
  | [], a, k => by simp
  | c :: cs, a, k => by
    rw [List.foldl_cons]
    have hm : ((pt.drop 18).map (· ^ 2 ^ k)).map FE.sq = (pt.drop 18).map (· ^ 2 ^ (k + 1)) := by
      rw [List.map_map]
      refine List.map_congr_left fun x _ ↦ ?_
      simp only [Function.comp, FE.sq_eq_mul, pow_succ, pow_mul]
      ring
    have ht : tailPtF (List.replicate 18 0 ++ (pt.drop 18).map (· ^ 2 ^ k)) = tailPtF (pt.map (· ^ 2 ^ k)) :=
      tailPtF_congr (by rw [List.drop_left' (by simp), List.map_drop])
    simp only
    rw [hm, ringTailN_fold pt cs _ (k + 1), ht, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have e2 : ∀ i ∈ Finset.range cs.length, cs.getD i 0 * tailPtF (pt.map (· ^ 2 ^ (k + 1 + i))) =
        cs.getD i 0 * tailPtF (pt.map (· ^ 2 ^ (k + (i + 1)))) :=
      fun i _ ↦ by rw [show k + 1 + i = k + (i + 1) by omega]
    rw [Finset.sum_congr rfl e2]
    ring

/-- **V_S's ring tail is `ringTailF`.** -/
theorem ringTailN_eq' (pt cs : List FE) : ringTailN pt cs = ringTailF pt cs := by
  have := ringTailN_fold pt cs 0 0
  simp only [pow_zero, pow_one, List.map_id', zero_add] at this
  rw [ringTailN, this, ringTailF_sum]

end Lvm.Shape
