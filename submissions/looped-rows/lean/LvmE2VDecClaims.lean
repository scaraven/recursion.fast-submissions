-- New for lvm2 E2-FT (E2F-V2-REF): piece (a) of `refinesF20` — V_S's claim list at S2GF (after the pin) against
-- the specification's: the front's split `E2` claims (`frontClaimsD`) against `assembleSF`'s through the twins,
-- `M`'s halves relocated onto the stream block, the small shape's tails of the split claims (`tailDE2`,
-- `rowTailE2`, `0`), and the whole list against `ordM` of `assembleF₂`'s relocated pair.
import LvmE2VEqCaller
import LvmE2VBaseLemmas
import LvmVEqTop
import LvmCertM20
import LvmTypedVEqPhasesX

/-!
# V_S's claim list at S2GF

* **Tails over `E2`** (`tailSumF`, a field of characteristic two): the mass of `eq(r ‖ s, ·)` on `D`'s tail rows
  `2^18 … 2^20 − 1` against a lane function is `(1 − (1 − r₁₈)(1 − r₁₉))·Σ_m eq(s, m) g(m)`.
* **Tails of V_S's split claims** (spec side, `tailValue`): `D`'s halves (`tailDE2`), the row claim
  (`rowTailE2`, bit by bit through `rowWord_bit`), `0` for parts off `D` (`tailValue_split_off`).
* `relocS_split`: `M`'s halves on `C_main`'s stream block are the `C_rec` halves relocated (`relocS_sum` at `E2`).
* `front_rel`: `frontClaimsD` against the spec's front list `frontW` (`VRel`); **`claimsF_rel`**: the whole
  list (typed claims, the mini-bus's, the front's) against `ordM` of `assembleF₂`'s relocated pair.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.TypedV Lvm.Typed
open LeanVM.Protocol.EndToEnd (boolPoint)

/-! ## Tail sums over a field of characteristic two -/

section TailF

variable {F : Type} [Field F]

theorem eqAtF_append_pow : ∀ (r s : List F) (m u : ℕ), u < 2 ^ r.length →
    E2V.eqAtF (r ++ s) (2 ^ r.length * m + u) = E2V.eqAtF r u * E2V.eqAtF s m
  | [], s, m, u, hu => by
    obtain rfl : u = 0 := by simpa using hu
    simp [E2V.eqAtF]
  | x :: r, s, m, u, hu => by
    rw [List.length_cons, pow_succ] at hu ⊢
    have ih := eqAtF_append_pow r s m (u / 2) (by generalize 2 ^ r.length = P at hu; omega)
    have e : 2 ^ r.length * 2 * m + u = 2 * (2 ^ r.length * m) + u := by ring
    rw [List.cons_append, E2V.eqAtF_cons, E2V.eqAtF_cons, e]
    generalize hA : 2 ^ r.length * m = A at ih ⊢
    rw [show (2 * A + u) % 2 = u % 2 by omega, show (2 * A + u) / 2 = A + u / 2 by omega, ih, mul_assoc]

variable [CharP F 2]

theorem sum_eqAtF_one : ∀ r : List F, ∑ u ∈ range (2 ^ r.length), E2V.eqAtF r u = 1
  | [] => by simp [E2V.eqAtF]
  | x :: r => by
    rw [List.length_cons, E2V.sum_range_pow_succ]
    simp only [E2V.eqAtF_two_mul, E2V.eqAtF_two_mul_add_one, ← add_mul, ← mul_sum, sum_eqAtF_one r]
    rw [mul_one, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem sum_eqAtF_low (r : List F) (p : ℕ) (hp : p ≤ r.length) :
    ∑ u ∈ range (2 ^ p), E2V.eqAtF r u = E2V.eqAtF (r.drop p) 0 := by
  have ht : (r.take p).length = p := List.length_take_of_le hp
  have e : ∀ u ∈ range (2 ^ p), E2V.eqAtF r u = E2V.eqAtF (r.take p) u * E2V.eqAtF (r.drop p) 0 := by
    intro u hu
    have := eqAtF_append_pow (r.take p) (r.drop p) 0 u (by rw [ht]; exact mem_range.1 hu)
    rwa [List.take_append_drop, Nat.mul_zero, Nat.zero_add] at this
  have h1 := sum_eqAtF_one (r.take p)
  rw [ht] at h1
  rw [sum_congr rfl e, ← sum_mul, h1, one_mul]

/-- `D`'s tail rows: `a < 2^22` with `2^18 ≤ a mod 2^20`. -/
abbrev tailRows : Finset ℕ := (range (2 ^ 22)).filter fun a ↦ 2 ^ 18 ≤ a % 2 ^ 20

theorem getD_drop_two {α : Type} [Zero α] (r : List α) (k : ℕ) {u w : α} (h : r.drop k = [u, w]) :
    r.getD k 0 = u ∧ r.getD (k + 1) 0 = w := by
  have h0 : (r.drop k).getD 0 0 = u := by rw [h]; rfl
  have h1 : (r.drop k).getD 1 0 = w := by rw [h]; rfl
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at h0 h1
  exact ⟨by simpa using h0, h1⟩

/-- **The tail mass at `E2`** (a field of characteristic two): `eq(r ‖ s, ·)` against a lane function `g` on `D`'s
tail rows is `(1 − (1 − r₁₈)(1 − r₁₉))·Σ_m eq(s, m)·g(m)`. -/
theorem tailSumF (r s : List F) (hr : r.length = 20) (g : ℕ → F) :
    ∑ a ∈ tailRows, E2V.eqAtF (r ++ s) a * g (a / 2 ^ 20) =
      (1 - (1 - r.getD 18 0) * (1 - r.getD 19 0)) * ∑ m ∈ range 4, E2V.eqAtF s m * g m := by
  rw [Finset.sum_filter, show 2 ^ 22 = 2 ^ 20 * 4 by norm_num, Shape.sum_range_mul_split]
  have e : ∀ k ∈ range 4, ∑ i ∈ range (2 ^ 20), (if 2 ^ 18 ≤ (2 ^ 20 * k + i) % 2 ^ 20 then
      E2V.eqAtF (r ++ s) (2 ^ 20 * k + i) * g ((2 ^ 20 * k + i) / 2 ^ 20) else 0) =
      (∑ i ∈ range (2 ^ 20), if 2 ^ 18 ≤ i then E2V.eqAtF r i else 0) * (E2V.eqAtF s k * g k) := by
    intro k _
    rw [sum_mul]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.1 hi
    have := eqAtF_append_pow r s k i (by rw [hr]; exact hi')
    rw [hr] at this
    rw [show (2 ^ 20 * k + i) % 2 ^ 20 = i by omega, show (2 ^ 20 * k + i) / 2 ^ 20 = k by omega, this]
    split_ifs <;> ring
  rw [sum_congr rfl e, ← mul_sum]
  have h1 : (∑ i ∈ range (2 ^ 20), if 2 ^ 18 ≤ i then E2V.eqAtF r i else 0) =
      1 - E2V.eqAtF (r.drop 18) 0 := by
    have hs := sum_eqAtF_one r
    rw [hr] at hs
    have hl := sum_eqAtF_low r 18 (by omega)
    rw [show 2 ^ 20 = 2 ^ 18 + 3 * 2 ^ 18 by norm_num, sum_range_add] at hs ⊢
    rw [sum_eq_zero (fun i hi ↦ ite_eq_right_iff.2 fun h ↦ absurd h (by simpa using hi))]
    simp only [Nat.le_add_right, ite_true, zero_add]
    linear_combination hs - hl
  obtain ⟨u, w, hu⟩ : ∃ u w, r.drop 18 = [u, w] := List.length_eq_two.1 (by simp [hr])
  obtain ⟨g18, g19⟩ := getD_drop_two r 18 hu
  rw [h1, hu, g18, g19]
  simp only [Nat.zero_mod, Nat.zero_div, zero_ne_one, ite_false, E2V.eqAtF, mul_one, CharTwo.sub_eq_add]

end TailF

/-! ## Facts at `P20F` -/

theorem layout0_P20F : layout0 P20F = layout0 P20 := rfl

theorem dBlock_P20F : dBlock P20F = ⟨22, 0⟩ := by
  rw [show dBlock P20F = dBlock P20 from rfl, dBlock, layout0_P20]; rfl

theorem nuMain_P20F : P20F.nuMain = 23 := rfl

theorem logN_P20F : P20F.logN = 20 := rfl

theorem ksLog_P20F : P20F.ksLog = 13 := rfl

theorem dSel_P20F : dSel P20F = 0 := by
  rw [show dSel P20F = dSel P20 from rfl, dSel, layout0_P20]; rfl

theorem dSelBits_P20F : dSelBits P20F = 1 := rfl

theorem ksXLog_P20F : ksXLog P20F = 9 := by decide +kernel

/-! ## Spec-side tails -/

/-- A spec claim's tail from the native one's. -/
theorem tail_of_rel {c : Lvm.StackClaim} {c' : VStackClaim} (h : SCRel c c') {t : FE}
    (ht : FE.toExt3 t = Shape.tailValue c'.1) : t = Shape.tailValueF c.1 :=
  FE.toExt3_injective (ht.trans (Shape.tailValue_rel h))

theorem tailValue_eq (w : List E → E) :
    Shape.tailValue w = ∑ a ∈ tailRows, w (boolPoint CMain.nu20 a) * ofK (Shape.zStar (a / 2 ^ 20)) := rfl

/-- The whole-stack placement is `1` on a cube point of `23` coordinates. -/
theorem eqAbove_full_bp (a : ℕ) : (⟨23, 0⟩ : VPlacement).eqAbove (boolPoint 23 a) = 1 := by
  rw [eqAbove_eqAt, List.drop_eq_nil_of_le (by simp)]; rfl

theorem take_bp_23 (a : ℕ) : (boolPoint 23 a).take 23 = boolPoint 23 a :=
  List.take_of_length_le (by simp)

/-- A placement of the low `2^22` words is `1` on a cube point of a low row. -/
theorem eqAbove_low_bp (a : ℕ) (ha : a < 2 ^ 22) : (⟨22, 0⟩ : VPlacement).eqAbove (boolPoint 23 a) = 1 := by
  rw [eqAbove_eqAt, LeanVM.Protocol.EndToEnd.Front.drop_boolPoint]
  show LeanVM.Protocol.KeccakGkr.eqAt (boolPoint 1 (a / 2 ^ 22)) 0 = 1
  rw [Nat.div_eq_of_lt ha]
  exact (E2V.eqAt_boolPoint 1 0 0 (by norm_num) (by norm_num)).trans (ite_eq_left rfl)

/-- `e2ToE6` of a constant. -/
theorem e2ToE6_C (k : K) : e2ToE6 (Quad.C k) = Quad.C (ofK k) :=
  QuadraticAlgebra.ext rfl (map_zero _)

/-- A whole-stack weight `x ↦ (W x)_re` on `D`'s tail (spec side). -/
theorem tailValue_re (W : List E → E6) (v : E) :
    Shape.tailValue (BClaim.onStack ⟨⟨23, 0⟩, fun x ↦ (W x).re, v⟩).1 =
      (∑ a ∈ tailRows, W (boolPoint 23 a) * Quad.C (ofK (Shape.zStar (a / 2 ^ 20)))).re := by
  rw [tailValue_eq, ← QuadraticAlgebra.reₗ_apply (R := E), map_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  simp only [BClaim.onStack]
  rw [QuadraticAlgebra.reₗ_apply, Quad.re_mul_C, eqAbove_full_bp, take_bp_23, one_mul]

/-- A whole-stack weight `x ↦ (W x)_im` on `D`'s tail (spec side). -/
theorem tailValue_im (W : List E → E6) (v : E) :
    Shape.tailValue (BClaim.onStack ⟨⟨23, 0⟩, fun x ↦ (W x).im, v⟩).1 =
      (∑ a ∈ tailRows, W (boolPoint 23 a) * Quad.C (ofK (Shape.zStar (a / 2 ^ 20)))).im := by
  rw [tailValue_eq, ← QuadraticAlgebra.imₗ_apply (R := E), map_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  simp only [BClaim.onStack]
  rw [QuadraticAlgebra.imₗ_apply, Quad.im_mul_C, eqAbove_full_bp, take_bp_23, one_mul]

/-- `D`'s word weight on a low cube point. -/
theorem sumW6_D_bp (z : List E2) (hz : z.length = 22) (a : ℕ) (ha : a < 2 ^ 22) :
    E2V.sumW6 [(1, ⟨22, 0⟩, z)] (boolPoint 23 a) = e2ToE6 (E2V.eqAtF z a) := by
  simp only [E2V.sumW6, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, map_one, one_mul]
  rw [eqAbove_low_bp a ha, Quad.C_eq_algebraMap, map_one, one_mul,
    LeanVM.Protocol.EndToEnd.Front.take_boolPoint 23 22 a (by norm_num), ← hz, E2V.wordW_boolPoint]

/-- The lane sum against `eq(sel(l), ·)` picks lane `l`. -/
theorem sum_eqAtF_selPt {F : Type} [Field F] [CharP F 2] (l : ℕ) (hl : l < 4) (g : ℕ → F) :
    ∑ m ∈ range 4, E2V.eqAtF (E2V.selPtF l 2) m * g m = g l := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  interval_cases l
  · rw [show E2V.selPtF 0 2 = ([0, 0] : List F) from rfl]
    simp [Finset.sum_range_succ, E2V.eqAtF]
  · rw [show E2V.selPtF 1 2 = ([1, 0] : List F) from rfl]
    simp [Finset.sum_range_succ, E2V.eqAtF, h2]
  · rw [show E2V.selPtF 2 2 = ([0, 1] : List F) from rfl]
    simp [Finset.sum_range_succ, E2V.eqAtF, h2]
  · rw [show E2V.selPtF 3 2 = ([1, 1] : List F) from rfl]
    simp [Finset.sum_range_succ, E2V.eqAtF, h2]

/-- **`D`'s word claim's tail** (spec side): `mass(r)·z*_l` in `E6`. -/
theorem tailSum_D (r : List E2) (hr : r.length = 20) (l : ℕ) (hl : l < 4) :
    ∑ a ∈ tailRows, E2V.sumW6 [(1, ⟨22, 0⟩, r ++ E2V.selPtF l 2)] (boolPoint 23 a) *
        Quad.C (ofK (Shape.zStar (a / 2 ^ 20))) =
      e2ToE6 ((1 - (1 - r.getD 18 0) * (1 - r.getD 19 0)) * Quad.C (Shape.zStar l)) := by
  have hz : (r ++ E2V.selPtF l 2).length = 22 := by simp [hr, E2V.selPtF]
  have e : ∀ a ∈ tailRows, E2V.sumW6 [(1, ⟨22, 0⟩, r ++ E2V.selPtF l 2)] (boolPoint 23 a) *
      Quad.C (ofK (Shape.zStar (a / 2 ^ 20))) =
      e2ToE6 (E2V.eqAtF (r ++ E2V.selPtF l 2) a * Quad.C (Shape.zStar (a / 2 ^ 20))) := fun a ha ↦ by
    rw [sumW6_D_bp _ hz a (mem_range.1 (mem_filter.1 ha).1), map_mul, e2ToE6_C]
  rw [sum_congr rfl e, ← map_sum, tailSumF r _ hr (fun m ↦ Quad.C (Shape.zStar m)), sum_eqAtF_selPt l hl]

/-- `toE2` of the tail mass. -/
theorem toE2_tailMassE2 (r : List FE2) :
    toE2 (tailMassE2 r) = 1 - (1 - (r.map toE2).getD 18 0) * (1 - (r.map toE2).getD 19 0) := by
  simp only [tailMassE2, Lvm.FE2.toE2_sub, Lvm.FE2.fe2_mul_eq, Lvm.FE2.toE2_one, toE2_getD]

theorem toE2_zStarE2 (l : ℕ) : toE2 (zStarE2 l) = Quad.C (Shape.zStar l) := by
  rw [zStarE2, Lvm.FE2.toE2_ofK, Shape.zStarF_eq]; rfl

/-- Twins put on the stack relate. -/
theorem screl_of_twin {c : BlockClaim} {d : BClaim} (h : E2V.BlockTwin c d) : SCRel c.onStack d.onStack :=
  ⟨(E2V.BlockTwin.onStack h).2.symm, fun xs ↦ ((E2V.BlockTwin.onStack h).1 xs).symm⟩

/-- **The tails of `D`'s split word claim** (`tailDE2`). -/
theorem tails_D (r : List FE2) (hr : r.length = 20) (l : ℕ) (hl : l < 4) (v : FE2) :
    List.Forall₂ (fun (c : BlockClaim) (t : FE) ↦ t = Shape.tailValueF c.onStack.1)
      (splitD 23 [(1, ⟨22, 0⟩, r ++ E2V.selPtF l 2)] v) (tailDE2 r l) := by
  have htw := E2V.splitD_twin 23 [(1, ⟨22, 0⟩, r ++ E2V.selPtF l 2)] v
  have hp : [((1 : FE2), (⟨22, 0⟩ : Placement), r ++ E2V.selPtF l 2)].map E2V.partE =
      [((1 : E2), (⟨22, 0⟩ : VPlacement), r.map toE2 ++ E2V.selPtF l 2)] := by
    simp only [List.map_cons, List.map_nil, E2V.partE, Lvm.FE2.toE2_one, List.map_append, E2V.map_toE2_selPtF]
    rfl
  rw [hp] at htw
  have hT := tailSum_D (r.map toE2) (by simp [hr]) l hl
  obtain ⟨h1, h2⟩ : E2V.BlockTwin _ _ ∧ E2V.BlockTwin _ _ := by simpa [splitD, E2V.splitE2] using htw
  have hy : ∀ y : FE2, FE.toExt3 (FE.ofK y.re) = ofK (toE2 y).re := fun y ↦ M3.toExt3_ofK' _
  have hy' : ∀ y : FE2, FE.toExt3 (FE.ofK y.im) = ofK (toE2 y).im := fun y ↦ M3.toExt3_ofK' _
  refine .cons (tail_of_rel (screl_of_twin h1) ?_) (.cons (tail_of_rel (screl_of_twin h2) ?_) .nil)
  · rw [hy, tailValue_re, hT, E2V.e2ToE6_re, Lvm.FE2.fe2_mul_eq, toE2_tailMassE2, toE2_zStarE2]
  · rw [hy', tailValue_im, hT, E2V.e2ToE6_im, Lvm.FE2.fe2_mul_eq, toE2_tailMassE2, toE2_zStarE2]

/-! ### Parts off `D` -/

/-- A spec placement from word `2^22` is `0` on a low cube point. -/
theorem eqAbove_off_bp (b : VPlacement) (hb : 2 ^ 22 ≤ b.index) (hv : b.variableCount ≤ 22)
    (hlt : b.index < 2 ^ CMain.nu20) (a : ℕ) (ha : a < 2 ^ 22) : b.eqAbove (boolPoint 23 a) = 0 := by
  have e := toExt3_eqAbove ⟨b.variableCount, b.index⟩ (Shape.cubePt CMain.nu20 a)
  rw [Shape.eqAbove_tail ⟨b.variableCount, b.index⟩ hb hv hlt a ha, FE.toExt3_zero] at e
  rw [← Shape.map_boolPointF]
  exact e.symm

theorem sumW6_off_bp (parts : List (E2 × VPlacement × List E2))
    (hp : ∀ q ∈ parts, 2 ^ 22 ≤ q.2.1.index ∧ q.2.1.variableCount ≤ 22 ∧ q.2.1.index < 2 ^ CMain.nu20)
    (a : ℕ) (ha : a < 2 ^ 22) : E2V.sumW6 parts (boolPoint 23 a) = 0 := by
  unfold E2V.sumW6
  refine List.sum_eq_zero fun y hy ↦ ?_
  obtain ⟨⟨c, blk, z⟩, hq, rfl⟩ := List.mem_map.1 hy
  obtain ⟨h1, h2, h3⟩ := hp _ hq
  simp only [eqAbove_off_bp blk h1 h2 h3 a ha, Quad.C_eq_algebraMap, map_zero, mul_zero, zero_mul]

/-- A split claim whose parts lie off `D` has no tail (spec side). -/
theorem tailSum_off (parts : List (E2 × VPlacement × List E2))
    (hp : ∀ q ∈ parts, 2 ^ 22 ≤ q.2.1.index ∧ q.2.1.variableCount ≤ 22 ∧ q.2.1.index < 2 ^ CMain.nu20) :
    ∑ a ∈ tailRows, E2V.sumW6 parts (boolPoint 23 a) * Quad.C (ofK (Shape.zStar (a / 2 ^ 20))) = 0 :=
  sum_eq_zero fun a ha ↦ by rw [sumW6_off_bp parts hp a (mem_range.1 (mem_filter.1 ha).1), zero_mul]

/-- The spec block conditions of V_S's parts from `OffOK`. -/
theorem partE_off (parts : List (FE2 × Placement × List FE2)) (hp : ∀ q ∈ parts, Shape.OffOK q.2.1) :
    ∀ q ∈ parts.map E2V.partE, 2 ^ 22 ≤ q.2.1.index ∧ q.2.1.variableCount ≤ 22 ∧ q.2.1.index < 2 ^ CMain.nu20 := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
  obtain ⟨h1, h2, h3, -⟩ := hp q' hq'
  exact ⟨h1, h2, h3⟩

/-- **The tails of a split claim off `D`** are `0`. -/
theorem tails_off (parts : List (FE2 × Placement × List FE2)) (hp : ∀ q ∈ parts, Shape.OffOK q.2.1)
    (v : FE2) : ∀ c ∈ splitD 23 parts v, Shape.tailValueF c.onStack.1 = 0 := by
  have htw := E2V.splitD_twin 23 parts v
  obtain ⟨h1, h2⟩ : E2V.BlockTwin _ _ ∧ E2V.BlockTwin _ _ := by simpa [splitD, E2V.splitE2] using htw
  have hT := tailSum_off _ (partE_off parts hp)
  intro c hc
  simp only [splitD, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact (tail_of_rel (screl_of_twin h1) (by rw [FE.toExt3_zero, tailValue_re, hT]; rfl)).symm
  · exact (tail_of_rel (screl_of_twin h2) (by rw [FE.toExt3_zero, tailValue_im, hT]; rfl)).symm

/-! ### The row claim -/

/-- V_S's switched weight (`rowSwitchD`'s closure). -/
def rowWD (z : List FE2) (eqR : List FE) (r : List FE) : FE :=
  sumE ((List.range 128).map fun j ↦ eqR.getD j 0 * (tensorWD z r).getD j 0)

/-- Its spec twin. -/
def rowWE (z : List E2) (eqR : List E) (X : List E) : E :=
  ∑ j ∈ range 128, eqR.getD j 0 * (E2V.tensorW z X).getD j 0

theorem toExt3_rowWD (z : List FE2) (eqR r : List FE) :
    FE.toExt3 (rowWD z eqR r) = rowWE (z.map toE2) (eqR.map FE.toExt3) (r.map FE.toExt3) := by
  rw [rowWD, toExt3_sumE_range']
  refine sum_congr rfl fun j _ ↦ ?_
  rw [FE.toExt3_mul, E2V.tensorWD_getD, getD_map_toExt3]

theorem list_sum_map_range' {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ j ∈ range n, f j
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_map_range' f n, sum_range_succ]; simp

theorem getD_map_range' {α : Type} [Zero α] (f : ℕ → α) {N k : ℕ} (hk : k < N) :
    ((List.range N).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hk]

/-- The tensor coordinates on the cube: coordinate `j` of `eq(z, n)`. -/
theorem tensorW_bp (z : List E2) {n : ℕ} (hn : n < 2 ^ z.length) {j : ℕ} (hj : j < 128) :
    (E2V.tensorW z (boolPoint z.length n)).getD j 0 = E2V.bitE (E2V.bitE2 (E2V.eqAtF z n) j) := by
  rw [E2V.tensorW_eq z _ (by simp) hj,
    sum_congr rfl fun n' hn' ↦ by rw [E2V.eqAt_boolPoint _ _ _ hn (mem_range.1 hn')]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq', ite_eq_left (mem_range.2 hn)]

/-- **A switched row of the tail**: `Σ_a ε_j(a)·z*(a)` is row `j` of slices `s_i = Σ_a [bit i of z*(a)]·eq(z, a)`. -/
theorem sum_bit_row (z sv : List E2) (hsv : ∀ i < 64, sv.getD i 0 =
      ∑ a ∈ tailRows, if (Shape.zStar (a / 2 ^ 20)).toBitVec.getLsbD i then E2V.eqAtF z a else 0) (j : ℕ) :
    ∑ a ∈ tailRows, E2V.bitE (E2V.bitE2 (E2V.eqAtF z a) j) * ofK (Shape.zStar (a / 2 ^ 20)) =
      ofK (E2V.rowWord sv j) := by
  have e : ∑ a ∈ tailRows, E2V.bitE (E2V.bitE2 (E2V.eqAtF z a) j) * ofK (Shape.zStar (a / 2 ^ 20)) =
      algebraMap K E (∑ a ∈ tailRows, if E2V.bitE2 (E2V.eqAtF z a) j then Shape.zStar (a / 2 ^ 20) else 0) := by
    rw [map_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    by_cases hb : E2V.bitE2 (E2V.eqAtF z a) j
    · rw [ite_eq_left hb, hb, show E2V.bitE true = 1 from rfl, one_mul]; rfl
    · rw [ite_eq_right hb, Bool.eq_false_iff.2 hb, show E2V.bitE false = 0 from rfl, zero_mul, map_zero]
  rw [e]
  refine congrArg (algebraMap K E)
    (BF64.toBitVec_injective (BitVec.eq_of_getLsbD_eq fun i hi ↦ E2V.bitE_injective ?_))
  rw [E2V.rowWord_bit sv hi j, hsv i hi, E2V.bitE_bitE2_sum, E2V.bitE_getLsbD_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  by_cases hb : E2V.bitE2 (E2V.eqAtF z a) j <;> by_cases hc : (Shape.zStar (a / 2 ^ 20)).toBitVec.getLsbD i <;>
    (simp only [hb, hc, ↓reduceIte, Bool.false_eq_true, E2V.bitE2_zero, E2V.toBitVec_zero_K]) <;> simp

theorem testBit_zStarF (l i : ℕ) :
    (Shape.zStarF l).c₀.val.toNat.testBit i = (Shape.zStar l).toBitVec.getLsbD i := by
  rw [Shape.zStarF_eq]; rfl

theorem getD_take_lt {α : Type} [Zero α] (l : List α) {n k : ℕ} (hk : k < n) :
    (l.take n).getD k 0 = l.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- **V_S's tail slices** are the slices of the tail rows. -/
theorem toE2_tailSlicesE2 (z : List FE2) (hz : z.length = 23) {i : ℕ} (hi : i < 64) :
    toE2 ((tailSlicesE2 z).getD i 0) = ∑ a ∈ tailRows,
      if (Shape.zStar (a / 2 ^ 20)).toBitVec.getLsbD i then E2V.eqAtF (z.map toE2) a else 0 := by
  have hl' : (z.map toE2).length = 23 := by simp [hz]
  obtain ⟨w, hw⟩ : ∃ w, (z.map toE2).drop 22 = [w] := List.length_eq_one_iff.1 (by simp [hl'])
  have h22 : (z.map toE2).take 22 = (z.map toE2).take 20 ++ ((z.map toE2).drop 20).take 2 := by
    rw [← List.take_add]
  let g : ℕ → E2 := fun m ↦ if (Shape.zStar m).toBitVec.getLsbD i then 1 else 0
  have e : ∀ a ∈ tailRows,
      (if (Shape.zStar (a / 2 ^ 20)).toBitVec.getLsbD i then E2V.eqAtF (z.map toE2) a else 0) =
      E2V.eqAtF ((z.map toE2).take 20 ++ ((z.map toE2).drop 20).take 2) a * g (a / 2 ^ 20) * (1 + w) := by
    intro a ha
    have := eqAtF_append_pow ((z.map toE2).take 22) ((z.map toE2).drop 22) 0 a
      (by simpa [hl'] using mem_range.1 (mem_filter.1 ha).1)
    rw [List.take_append_drop, Nat.mul_zero, Nat.zero_add, hw, h22] at this
    rw [this]
    simp only [g, Nat.zero_mod, zero_ne_one, ite_false, E2V.eqAtF, mul_one]
    split_ifs <;> ring
  rw [sum_congr rfl e, ← sum_mul, tailSumF _ _ (by simp [hl']) g,
    getD_take_lt _ (by norm_num : 18 < 20), getD_take_lt _ (by norm_num : 19 < 20)]
  unfold tailSlicesE2
  dsimp only
  rw [getD_map_range' _ hi, Lvm.FE2.fe2_mul_eq, Lvm.FE2.fe2_mul_eq, toE2_tailMassE2, E2V.toE2_eqEvalF,
    E2V.map_toE2_selPtF, E2V.toE2_sumF, E2V.sumF_eq_sum, List.map_map, list_sum_map_range', List.map_drop, hw]
  have hL : ∀ l ∈ range 4, (toE2 ∘ fun l ↦ if (Shape.zStarF l).c₀.val.toNat.testBit i then
      (E2V.eqKernelF ((z.drop 20).take 2)).getD l 0 else 0) l =
      E2V.eqAtF (((z.map toE2).drop 20).take 2) l * g l := by
    intro l hl
    simp only [Function.comp_apply, testBit_zStarF, g]
    split_ifs
    · rw [toE2_getD, E2V.map_toE2_eqKernelF, E2V.eqKernelF_getD, ite_eq_left, mul_one, List.map_take, List.map_drop]
      have := mem_range.1 hl
      simp [hz]
      omega
    · rw [Lvm.FE2.toE2_zero, mul_zero]
  have hb : E2V.eqEvalF [w] (E2V.selPtF 0 (CMain.nu20 - 22) : List E2) = 1 + w := by
    rw [show CMain.nu20 - 22 = 1 from rfl, show (E2V.selPtF 0 1 : List E2) = [0] from rfl]
    simp [E2V.eqEvalF]
  rw [sum_congr rfl hL, hb]
  ring

/-- **The row claim's tail** (`rowTailE2`): the switched target of the tail slices. -/
theorem tail_row (z : List FE2) (hz : z.length = 23) (eqR : List FE) (tgt : FE) :
    rowTailE2 eqR z = Shape.tailValueF (⟨⟨23, 0⟩, rowWD z eqR, tgt⟩ : BlockClaim).onStack.1 := by
  have hrel : SCRel (⟨⟨23, 0⟩, rowWD z eqR, tgt⟩ : BlockClaim).onStack
      (⟨⟨23, 0⟩, rowWE (z.map toE2) (eqR.map FE.toExt3), FE.toExt3 tgt⟩ : BClaim).onStack :=
    onStack_rel ⟨rfl, rfl, fun xs ↦ (toExt3_rowWD z eqR xs).symm⟩
  refine tail_of_rel hrel ?_
  have hl' : (z.map toE2).length = 23 := by simp [hz]
  have e : ∀ a ∈ tailRows,
      (⟨⟨23, 0⟩, rowWE (z.map toE2) (eqR.map FE.toExt3), FE.toExt3 tgt⟩ : BClaim).onStack.1
        (boolPoint CMain.nu20 a) * ofK (Shape.zStar (a / 2 ^ 20)) =
      ∑ j ∈ range 128, FE.toExt3 (eqR.getD j 0) *
        (E2V.bitE (E2V.bitE2 (E2V.eqAtF (z.map toE2) a) j) * ofK (Shape.zStar (a / 2 ^ 20))) := by
    intro a ha
    have ha' : a < 2 ^ (z.map toE2).length := by
      rw [hl']; exact lt_trans (mem_range.1 (mem_filter.1 ha).1) (by norm_num)
    simp only [BClaim.onStack]
    rw [eqAbove_full_bp, take_bp_23, one_mul, rowWE, sum_mul]
    refine sum_congr rfl fun j hj ↦ ?_
    have := tensorW_bp (z.map toE2) ha' (mem_range.1 hj)
    rw [hl'] at this
    rw [this, getD_map_toExt3, mul_assoc]
  rw [tailValue_eq, sum_congr rfl e, sum_comm]
  unfold rowTailE2
  dsimp only
  rw [toExt3_sumE_range']
  refine sum_congr rfl fun j _ ↦ ?_
  rw [FE.toExt3_mul, ← mul_sum, M3.toExt3_ofK', E2V.toBF64_rowWordD,
    sum_bit_row (z.map toE2) ((tailSlicesE2 z).map toE2) (fun i hi ↦ by
      rw [← toE2_getD]; exact toE2_tailSlicesE2 z hz hi) j]
  rfl

/-! ## `M` on the stream block -/

/-- An `E2` part moved by `S`. -/
def shiftS2 (q : E2 × VPlacement × List E2) : E2 × VPlacement × List E2 :=
  (q.1, ⟨q.2.1.variableCount, CMain.sOff20 + q.2.1.index⟩, q.2.2)

/-- `relocS_sum`'s conditions on a part. -/
def RelocOK (q : E2 × VPlacement × List E2) : Prop :=
  q.2.1.variableCount ≤ 19 ∧
    (CMain.sOff20 + q.2.1.index) >>> q.2.1.variableCount >>> (23 - q.2.1.variableCount) = 0 ∧
    ((CMain.sOff20 + q.2.1.index) >>> q.2.1.variableCount) % 2 ^ (19 - q.2.1.variableCount) =
      (q.2.1.index >>> q.2.1.variableCount) % 2 ^ (19 - q.2.1.variableCount) ∧
    (CMain.sOff20 + q.2.1.index) >>> q.2.1.variableCount >>> (19 - q.2.1.variableCount) = CMain.sOff20 >>> 19

theorem sumW6_reloc (parts : List (E2 × VPlacement × List E2)) (hp : ∀ q ∈ parts, RelocOK q) (x : List E) :
    Quad.C ((⟨23, 0⟩ : VPlacement).eqAbove x) * E2V.sumW6 (parts.map shiftS2) (x.take 23) =
      Quad.C ((⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x) * E2V.sumW6 parts (x.take 19) := by
  unfold E2V.sumW6
  rw [List.map_map, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun q hq ↦ ?_)
  obtain ⟨c, ⟨k, o⟩, z⟩ := q
  obtain ⟨hk, h1, h2, h3⟩ := hp _ hq
  dsimp only [Function.comp, shiftS2] at h1 h2 h3 hk ⊢
  have e := eqAbove_reloc x k (CMain.sOff20 + o) o hk h1 h2 h3
  rw [eqAbove_take_self 19 0 x rfl, one_mul] at e
  rw [List.take_take, List.take_take, min_eq_left (by omega : k ≤ 23), min_eq_left hk]
  simp only [Quad.C_eq_algebraMap]
  calc algebraMap E E6 ((⟨23, 0⟩ : VPlacement).eqAbove x) * (e2ToE6 c *
        algebraMap E E6 ((⟨k, CMain.sOff20 + o⟩ : VPlacement).eqAbove (x.take 23)) * E2V.wordW z (x.take k))
      _ = algebraMap E E6 ((⟨23, 0⟩ : VPlacement).eqAbove x *
          (⟨k, CMain.sOff20 + o⟩ : VPlacement).eqAbove (x.take 23)) * (e2ToE6 c * E2V.wordW z (x.take k)) := by
        rw [map_mul]; ring
      _ = _ := by rw [e, map_mul]; ring

theorem re_C_mul (a : E) (w : E6) : (Quad.C a * w).re = a * w.re := by rw [mul_comm, Quad.re_mul_C, mul_comm]

theorem im_C_mul (a : E) (w : E6) : (Quad.C a * w).im = a * w.im := by rw [mul_comm, Quad.im_mul_C, mul_comm]

/-- **`M`'s halves on `S`** are the `C_rec` halves relocated (`relocS_sum` at `E2`). -/
theorem relocS_split (parts : List (E2 × VPlacement × List E2)) (hp : ∀ q ∈ parts, RelocOK q) (v : E2) :
    List.Forall₂ (fun a b : BClaim ↦ a.onStack = relocS b.onStack)
      (E2V.splitE2 23 ⟨parts.map shiftS2, v⟩) (E2V.splitE2 19 ⟨parts, v⟩) := by
  have key := sumW6_reloc parts hp
  refine .cons (Prod.ext (funext fun x ↦ ?_) rfl) (.cons (Prod.ext (funext fun x ↦ ?_) rfl) .nil)
  · show (⟨23, 0⟩ : VPlacement).eqAbove x * (E2V.sumW6 (parts.map shiftS2) (x.take 23)).re =
      (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x * ((⟨19, 0⟩ : VPlacement).eqAbove (x.take 19) *
        (E2V.sumW6 parts ((x.take 19).take 19)).re)
    rw [eqAbove_take_self 19 0 x rfl, one_mul, List.take_take, min_self, ← re_C_mul, ← re_C_mul, key]
  · show (⟨23, 0⟩ : VPlacement).eqAbove x * (E2V.sumW6 (parts.map shiftS2) (x.take 23)).im =
      (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x * ((⟨19, 0⟩ : VPlacement).eqAbove (x.take 19) *
        (E2V.sumW6 parts ((x.take 19).take 19)).im)
    rw [eqAbove_take_self 19 0 x rfl, one_mul, List.take_take, min_self, ← im_C_mul, ← im_C_mul, key]


/-! ## Shapes of V_S's front values -/

/-- A width-aware refinement with a fact on the native value. -/
theorem RefAtW.retD {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}
    {α β : Type} {i j : ℕ} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop} {Q : β → Prop}
    (h : RefAtW cap occ shp rw sig i d P R j) (hq : RetD Q d) :
    RefAtW cap occ shp rw sig i d P (fun b a ↦ R b a ∧ Q b) j := fun s hok ↦ by
  obtain ⟨a, h1, h2, h3, h4, h5⟩ := h s hok
  exact ⟨a, h1, h2, h3, h4, h5, hq sig s⟩

theorem retD_samplesG (g : ℕ) : ∀ n, RetD (fun xs : List FE2 ↦ xs.length = n) (samplesG g n)
  | 0 => RetD.pure rfl
  | n + 1 => RetD.bind_true fun _ ↦ (retD_samplesG g n).bind fun _ h ↦ RetD.pure (by simp [h])

theorem retD_sumcheckD (g count : ℕ) : ∀ (modes : List (Option FE2)) (claim : FE2),
    RetD (fun r : List FE2 × FE2 ↦ r.1.length = modes.length) (sumcheckD g claim count modes)
  | [], _ => RetD.pure rfl
  | _ :: modes, _ => RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
      (retD_sumcheckD g count modes _).bind fun ⟨_, _⟩ h ↦ RetD.pure (by simp [h])

theorem retD_rowSwitchD (z sv : List FE2) :
    RetD (fun row : (FE × (List FE → FE)) × List FE ↦ row.1.2 = rowWD z row.2) (rowSwitchD z sv) := by
  unfold rowSwitchD
  refine RetD.bind_true fun rr ↦ ?_
  dsimp only
  exact RetD.pure (Q := fun row : (FE × (List FE → FE)) × List FE ↦ row.1.2 = rowWD z row.2) (by
    show (fun r ↦ _) = _
    funext r
    dsimp only [rowWD])

theorem retD_slotD (b sb blk : ℕ) (W : ℕ → ℕ → FE2) (pt : List FE2) (v : FE2) :
    RetD (fun d : (List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE) ↦
      d.1.1.length = b ∧ d.2.2.1.2 = rowWD (pt ++ d.1.1 ++ E2V.selPtF blk sb) d.2.2.2)
      (slotD b sb blk W pt v) :=
  (retD_sumcheckD _ _ _ _).bind fun _ hsl ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_rowSwitchD _ _).bind fun _ hrow ↦ RetD.pure ⟨by simpa using hsl, hrow⟩

theorem retD_wireD (w sb dsel : ℕ) (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) :
    RetD (fun wo : (List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 ×
        ((FE × (List FE → FE)) × List FE)) ↦
      wo.1.1.length = w ∧ wo.2.2.1.1.length = 2 ∧
        wo.2.2.2.2.1.2 = rowWD (wo.1.1 ++ wo.2.2.1.1 ++ E2V.selPtF dsel sb) wo.2.2.2.2.2)
      (wireD w sb dsel s n claim) :=
  (retD_sumcheckD _ _ _ _).bind fun _ hsc ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_slotD _ _ _ _ _ _).bind fun _ hd ↦ RetD.pure ⟨by simpa using hsc, hd.1, hd.2⟩

/-- V_S's tape caller value. -/
abbrev TapeV : Type := List FE2 × List FE2 × E2V.KClaim FE2 ×
  ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE)))

/-- **The shape of the tape caller's value**: the lengths of `r`, the wiring point and the slot point, and the
row switch's weight. -/
def TapeShape (w sb dsel : ℕ) (tp : TapeV) : Prop :=
  tp.1.length = w ∧ tp.2.2.2.1.1.length = w ∧ tp.2.2.2.2.2.1.1.length = 2 ∧
    tp.2.2.2.2.2.2.2.1.2 = rowWD (tp.2.2.2.1.1 ++ tp.2.2.2.2.2.1.1 ++ E2V.selPtF dsel sb) tp.2.2.2.2.2.2.2.2

theorem retD_tapeD (w sb dsel : ℕ) (s : List FK) (n : ℕ) : RetD (TapeShape w sb dsel) (tapeD w sb dsel s n) :=
  RetD.bind_true fun _ ↦ (retD_samplesG _ _).bind fun _ hr ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    RetD.bind_true fun _ ↦ (retD_wireD _ _ _ _ _ _).bind fun _ hwo ↦ RetD.pure ⟨hr, hwo⟩

/-! ## Claim relations -/

theorem inStack_full : Shape.InStack ⟨23, 0⟩ := ⟨le_rfl, rfl, by norm_num⟩

theorem forall₂_flatMap_same {α β γ : Type} {R : β → γ → Prop} {f : α → List β} {g : α → List γ} :
    ∀ (l : List α), (∀ a ∈ l, List.Forall₂ R (f a) (g a)) → List.Forall₂ R (l.flatMap f) (l.flatMap g)
  | [], _ => .nil
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact Lk.forall₂_append (h a (by simp)) (forall₂_flatMap_same l fun b hb ↦ h b (by simp [hb]))

/-- **A split claim with its tails** against the spec's halves. -/
theorem vrel_splitD {s : Bool} (parts : List (FE2 × Placement × List FE2)) (v : FE2) (ts : List FE)
    (hts : ts.length = 2)
    (ht : s = true → List.Forall₂ (fun (c : BlockClaim) (t : FE) ↦ t = Shape.tailValueF c.onStack.1)
      (splitD 23 parts v) ts) (c' : E2V.SumE2) (hc : (⟨parts.map E2V.partE, toE2 v⟩ : E2V.SumE2) = c') :
    List.Forall₂ (VRel s) (((splitD 23 parts v).zip ts).map fun e ↦ (Com.main, e.1, e.2))
      ((E2V.splitE2 23 c').map BClaim.onStack) := by
  subst hc
  obtain ⟨t1, t2, rfl⟩ := List.length_eq_two.1 hts
  obtain ⟨h1, h2⟩ : E2V.BlockTwin _ _ ∧ E2V.BlockTwin _ _ := by
    simpa [splitD, E2V.splitE2] using E2V.splitD_twin 23 parts v
  refine .cons (vrel_of (screl_of_twin h1) fun hs ↦ ⟨inStack_full, ?_⟩)
    (.cons (vrel_of (screl_of_twin h2) fun hs ↦ ⟨inStack_full, ?_⟩) .nil)
  · have := ht hs; simp only [splitD, List.forall₂_cons] at this; exact this.1
  · have := ht hs; simp only [splitD, List.forall₂_cons] at this; exact this.2.1

/-- **A split claim off `D`** (zero tails) against the spec's halves. -/
theorem vrel_splitZ {s : Bool} (parts : List (FE2 × Placement × List FE2)) (hp : ∀ q ∈ parts, Shape.OffOK q.2.1)
    (v : FE2) (c' : E2V.SumE2) (hc : (⟨parts.map E2V.partE, toE2 v⟩ : E2V.SumE2) = c') :
    List.Forall₂ (VRel s) (splitZ 23 parts v) ((E2V.splitE2 23 c').map BClaim.onStack) := by
  subst hc
  obtain ⟨h1, h2⟩ : E2V.BlockTwin _ _ ∧ E2V.BlockTwin _ _ := by
    simpa [splitD, E2V.splitE2] using E2V.splitD_twin 23 parts v
  have ht := tails_off parts hp v
  simp only [splitD, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ht
  exact .cons (vrel_of (screl_of_twin h1) fun _ ↦ ⟨inStack_full, ht.1.symm⟩)
    (.cons (vrel_of (screl_of_twin h2) fun _ ↦ ⟨inStack_full, ht.2.symm⟩) .nil)

/-- **`M`'s split claim on `S`** against the spec's `C_rec` halves relocated. -/
theorem vrel_splitM {s : Bool} (parts : List (FE2 × Placement × List FE2)) (hp : ∀ q ∈ parts, Shape.OffOK q.2.1)
    (v : FE2) (mparts : List (E2 × VPlacement × List E2)) (hm : parts.map E2V.partE = mparts.map shiftS2)
    (hr : ∀ q ∈ mparts, RelocOK q) (v' : E2) (hv : toE2 v = v') :
    List.Forall₂ (VRel s) (splitZ 23 parts v) ((E2V.splitE2 19 ⟨mparts, v'⟩).map fun c ↦ relocS c.onStack) := by
  subst hv
  have hz := vrel_splitZ (s := s) parts hp v _ rfl
  have h := relocS_split mparts hr (toE2 v)
  simp only [E2V.splitE2, List.forall₂_cons, List.Forall₂.nil, and_true] at h
  rw [hm] at hz
  simpa only [E2V.splitE2, List.map_cons, List.map_nil, h.1, h.2] using hz


/-! ## The front's claims -/

/-- The `KS` link's sum claims (`ksLinkClaimsF`'s `yC`, `inC`, `mC`, `xC`). -/
def yCF (lo : List E2 × (List E2 × E2) × List E2) : E2V.SumE2 :=
  ⟨(List.range 25).map fun l ↦ ((E2V.eqKernelF (lo.1.drop 13)).getD l 0, (E2V.ksYPartF l lo.2.1.1).1,
    (E2V.ksYPartF l lo.2.1.1).2), lo.2.2.getD 0 0⟩

def inCF (lo : List E2 × (List E2 × E2) × List E2) : E2V.SumE2 :=
  ⟨(List.range 25).map fun l ↦ ((E2V.eqKernelF (lo.1.drop 13)).getD l 0, ksBlk, lo.2.1.1 ++ E2V.selPtF l slotLog),
    lo.2.2.getD 1 0⟩

def mCF (lo : List E2 × (List E2 × E2) × List E2) : E2V.SumE2 :=
  ⟨(List.range 17).map (fun l ↦ ((E2V.eqKernelF (lo.1.drop 13)).getD l 0, (⟨13, l * 2 ^ 14⟩ : VPlacement), lo.2.1.1)) ++
    (List.range 17).map (fun l ↦ ((E2V.eqKernelF (lo.1.drop 13)).getD l 0 * E2V.selXF 9 lo.2.1.1,
      (⟨9, l * 2 ^ 14 + ksSplit P20⟩ : VPlacement), lo.2.1.1.take 9)), lo.2.2.getD 2 0⟩

def xCF (lo : List E2 × (List E2 × E2) × List E2) : E2V.SumE2 :=
  ⟨(List.range 17).map fun l ↦ ((E2V.eqKernelF (lo.1.drop 13)).getD l 0, (⟨9, xOff + l * 2 ^ 14⟩ : VPlacement),
    lo.2.1.1.take 9), lo.2.2.getD 3 0⟩

theorem ksLinkClaimsF_eq (lo : List E2 × (List E2 × E2) × List E2) :
    E2V.ksLinkClaimsF lo.1 lo.2.1 lo.2.2 =
      (E2V.splitE2 nuMainE (yCF lo)).map (Com.main, ·) ++ (E2V.splitE2 nuMainE (inCF lo)).map (Com.main, ·) ++
        (E2V.splitE2 19 (mCF lo)).map (Com.crec, ·) ++ (E2V.splitE2 nuMainE (xCF lo)).map (Com.main, ·) := rfl

/-- **The spec's front list in V_S's order**: the tape's, `KS`'s and the output lanes' claims on the stack, then
the `KS` link's `Y, in, X_re, M (relocated onto S), X_im`. -/
def linkW (lo : List E2 × (List E2 × E2) × List E2) : List VStackClaim :=
  (E2V.splitE2 nuMainE (yCF lo)).map BClaim.onStack ++ (E2V.splitE2 nuMainE (inCF lo)).map BClaim.onStack ++
    ((E2V.splitE2 nuMainE (xCF lo)).map BClaim.onStack).take 1 ++
    (E2V.splitE2 19 (mCF lo)).map (fun c ↦ relocS c.onStack) ++
    ((E2V.splitE2 nuMainE (xCF lo)).map BClaim.onStack).drop 1

def frontW (x : List UInt8) (k : E2V.KgOutF) : List VStackClaim :=
  (E2V.tapeClaimsF k.1 (pubX x) ++ E2V.keccakClaimsF ksBlk k.2.1 ++ E2V.ksOutputClaimsF k.2.1.1 k.2.1.2.1).map
    BClaim.onStack ++ linkW k.2.2

/-- What the `KS` link's two sides relate (`refW_ksLinkD`). -/
def LinkRelW (lo : List FE2 × (List FE2 × FE2) × List FE2) (lo' : List E2 × (List E2 × E2) × List E2) : Prop :=
  lo'.1 = lo.1.map toE2 ∧ lo'.2.1.1 = lo.2.1.1.map toE2 ∧ lo'.2.1.2 = toE2 lo.2.1.2 ∧ lo'.2.2 = lo.2.2.map toE2

/-- `KS`'s `Y` lane `l` of `P20F` at `E2`. -/
theorem ksYPartD_rel (l : ℕ) (pt : List FE2) :
    plE (ksYPartD P20F (layout0 P20F) l pt).1 = (E2V.ksYPartF l (pt.map toE2)).1 ∧
      (ksYPartD P20F (layout0 P20F) l pt).2.map toE2 = (E2V.ksYPartF l (pt.map toE2)).2 := by
  unfold ksYPartD E2V.ksYPartF
  rw [layout0_P20F, layout0_P20]
  by_cases hl : l < 14
  · rw [ite_eq_left hl, ite_eq_left hl, List.map_append, E2V.map_toE2_selPtF]; exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hl, ite_eq_right hl]; exact ⟨rfl, rfl⟩

theorem offOK_ksYD (l : ℕ) (hl : l < 25) (pt : List FE2) : Shape.OffOK (ksYPartD P20F (layout0 P20F) l pt).1 := by
  have := Shape.offOK_ksY l hl []
  unfold ksYPartD
  unfold Lvm.ksYPart at this
  split_ifs at this ⊢ <;> exact this

theorem offOK_ksV : Shape.OffOK ⟨P20F.ksLog + slotLog, (layout0 P20F).ks⟩ := Shape.offOK_ks

theorem plE_ksV : plE ⟨P20F.ksLog + slotLog, (layout0 P20F).ks⟩ = ksBlk := by
  rw [layout0_P20F, layout0_P20]; rfl

theorem nuMainE_eq : nuMainE = 23 := rfl

theorem dBlkE_eq : dBlkE = ⟨22, 0⟩ := rfl


/-- What V_S's front and the spec's `kgProgF` relate (`refW_tapeD`, `refW_callerD`, `refW_ksLinkD`). -/
def FrontRel (tp : TapeV)
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE))
    (lo : List FE2 × (List FE2 × FE2) × List FE2) (k : E2V.KgOutF) : Prop :=
  TapeRelW tp k.1 ∧ CallerRel co k.2.1 ∧ LinkRelW lo k.2.2

/-- **The front's claims at S2GF** (`frontClaimsD`, with their tails) against the spec's (`frontW`). -/
theorem front_rel {s : Bool} (x : List UInt8) (tp : TapeV)
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE))
    (lo : List FE2 × (List FE2 × FE2) × List FE2) (k : E2V.KgOutF) (hk : FrontRel tp co lo k)
    (hsh : TapeShape 20 1 0 tp) (hn : s = true → (pubX x).n ≤ 2 ^ 18) (hh : (pubX x).h.length ≤ 4) :
    List.Forall₂ (VRel s) (frontClaimsD P20F (pubXF x) tp co lo) (frontW x k) := by
  obtain ⟨⟨hr1, hr2, -, hsc1, -, -, hsl1, -, -, hrow⟩, ⟨hc1, hc2, hvk, hkrow⟩, ⟨hl1, hl2, -, hl4⟩⟩ := hk
  obtain ⟨hlr, hlsc, hlsl, hwfn⟩ := hsh
  unfold frontClaimsD frontW E2V.tapeClaimsF E2V.keccakClaimsF E2V.ksOutputClaimsF
  dsimp only
  simp only [List.map_append]
  refine Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append
    (Lk.forall₂_append ?_ ?_) ?_) (Lk.forall₂_append ?_ ?_)) ?_) ?_
  · -- `D`'s split word claims
    rw [List.map_flatMap, show dLanes = 4 from rfl]
    refine forall₂_flatMap_same _ fun l hl ↦ ?_
    rw [show P20F.nuMain = 23 from rfl, dBlock_P20F, nuMainE_eq]
    refine vrel_splitD _ _ _ rfl (fun _ ↦ tails_D tp.1 hlr l (mem_range.1 hl) _) _ ?_
    rw [hr1, hr2, dBlkE_eq, toE2_getD]
    simp only [E2V.pointE2, List.map_cons, List.map_nil, E2V.partE, Lvm.FE2.toE2_one, List.map_append,
      E2V.map_toE2_selPtF]
    rfl
  · -- the row claim
    refine .cons (vrel_of (onStack_rel ⟨rfl, hrow.1, hrow.2⟩) fun _ ↦ ⟨inStack_full, ?_⟩) .nil
    rw [hwfn, dSel_P20F, dSelBits_P20F, show P20F.nuMain = 23 from rfl]
    dsimp only
    exact tail_row _ (by simp [hlsc, hlsl, E2V.selPtF]) _ _
  · -- the boundary claims
    rw [List.map_map]
    refine Lk.forall₂_map_map _ fun wl hwl ↦ ?_
    obtain ⟨w, l⟩ := wl
    have hh' : (pubXF x).h.length ≤ 4 := hh
    have hl : l < 4 := lt_of_lt_of_le (List.mem_zipIdx hwl).2.1 (by simpa using hh')
    refine vrel_of (onStack_rel (Lk.point_rel _ _ _ ?_ ?_ ?_)) fun hs ↦ ⟨?_, ?_⟩
    · rw [dBlock_P20F]; rfl
    · rw [List.map_append, map_selectorPoint, map_selectorPoint]; rfl
    · exact (M3.tE_ofK w).symm
    · rw [dBlock_P20F]; exact (by decide : Shape.InStack ⟨22, 0⟩)
    · exact (Shape.tailValueF_bnd ((pubX x).n - 1) (by have := hn hs; omega) l hl (FE.ofK w)).symm
  · -- `KS`'s output word claims
    rw [hvk.1, List.flatMap_map, List.map_flatMap]
    refine forall₂_flatMap_same _ fun c _ ↦ ?_
    rw [show P20F.nuMain = 23 from rfl, nuMainE_eq]
    refine vrel_splitZ _ (by simpa using offOK_ksV) _ _ ?_
    simp only [E2V.pointE2, List.map_cons, List.map_nil, E2V.partE, Lvm.FE2.toE2_one,
      plE_ksV]
  · -- `KS`'s row claim
    refine .cons (vrel_of (onStack_rel ⟨plE_ksV.symm, hkrow.1, hkrow.2⟩) fun _ ↦
      ⟨offOK_ksV.inStack, (Shape.OffOK.tail offOK_ksV).symm⟩) .nil
  · -- the output lanes
    rw [List.map_flatMap]
    refine forall₂_flatMap_same _ fun l hl ↦ ?_
    rw [show P20F.nuMain = 23 from rfl, nuMainE_eq]
    refine vrel_splitZ _ (by simpa using offOK_ksYD l (mem_range.1 hl) co.1) _ _ ?_
    rw [hc1, hc2, ← (ksYPartD_rel l co.1).1, ← (ksYPartD_rel l co.1).2, toE2_getD]
    simp only [E2V.pointE2, List.map_cons, List.map_nil, E2V.partE, Lvm.FE2.toE2_one]
  · -- the `KS` link
    unfold linkW
    rw [show P20F.nuMain = 23 from rfl, nuMainE_eq]
    have hom : ∀ l, toE2 ((E2V.eqKernelF (lo.1.drop P20F.ksLog)).getD l 0) =
        (E2V.eqKernelF (k.2.2.1.drop 13)).getD l 0 := fun l ↦ by
      rw [toE2_getD, E2V.map_toE2_eqKernelF, List.map_drop, hl1]; rfl
    have hsel : toE2 (E2V.selXF 9 lo.2.1.1) = E2V.selXF 9 k.2.2.2.1.1 := by
      rw [E2V.toE2_selXF, hl2]
    have hL : (layout0 P20F) = ⟨CMain.dOff20, CMain.ksOff20, CMain.ksY2Off20, CMain.xOff20, CMain.freeLo20,
        CMain.tOff20, CMain.sOff20⟩ := by rw [layout0_P20F, layout0_P20]
    have hX := vrel_splitZ (s := s) ((List.range 17).map fun l ↦ ((E2V.eqKernelF (lo.1.drop P20F.ksLog)).getD l 0,
        (⟨ksXLog P20F, (layout0 P20F).x + l * 2 ^ P20F.recRowsLog⟩ : Placement), lo.2.1.1.take (ksXLog P20F)))
      (by
        intro q hq
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hq
        exact Shape.offOK_xs l (List.mem_range.1 hl))
      (lo.2.2.getD 3 0) (xCF k.2.2) (by
        rw [xCF, hl2, hl4, toE2_getD, List.map_map]
        congr 1
        refine List.map_congr_left fun l _ ↦ ?_
        simp only [Function.comp_apply, E2V.partE, hom, hL, ksXLog_P20F, List.map_take]
        rfl)
    refine Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append ?_ ?_)
      (List.forall₂_take 1 hX)) ?_) (List.forall₂_drop 1 hX)
    · refine vrel_splitZ _ (by
        intro q hq
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hq
        exact offOK_ksYD l (List.mem_range.1 hl) _) _ _ ?_
      rw [yCF, hl4, toE2_getD, List.map_map]
      congr 1
      refine List.map_congr_left fun l _ ↦ ?_
      simp only [Function.comp_apply, E2V.partE, hom, (ksYPartD_rel l lo.2.1.1).1,
        (ksYPartD_rel l lo.2.1.1).2, hl2]
    · refine vrel_splitZ _ (by
        intro q hq
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hq
        exact offOK_ksV) _ _ ?_
      rw [inCF, hl2, hl4, toE2_getD, List.map_map]
      congr 1
      refine List.map_congr_left fun l _ ↦ ?_
      simp only [Function.comp_apply, E2V.partE, hom, plE_ksV, List.map_append, E2V.map_toE2_selPtF]
    · refine vrel_splitM _ ?_ _ (mCF k.2.2).parts ?_ ?_ (mCF k.2.2).value
        (by show _ = k.2.2.2.2.getD 2 0; rw [hl4, toE2_getD])
      · intro q hq
        rcases List.mem_append.1 hq with hq | hq <;> obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hq
        · exact Shape.offOK_m l (List.mem_range.1 hl)
        · exact Shape.offOK_mx l (List.mem_range.1 hl)
      · rw [mCF, hl2, List.map_append, List.map_append, List.map_map, List.map_map, List.map_map, List.map_map]
        congr 1 <;> refine List.map_congr_left fun l _ ↦ ?_
        · simp only [Function.comp_apply, E2V.partE, hom, shiftS2, hL]
          rfl
        · simp only [Function.comp_apply, E2V.partE, hom, shiftS2, hL, Lvm.FE2.fe2_mul_eq,
            ksXLog_P20F, List.map_take, hsel, hl2, plE, Nat.add_assoc]
          rfl
      · intro q hq
        simp only [mCF, List.mem_append, List.mem_map, List.mem_range] at hq
        rcases hq with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
        · refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> dsimp only <;>
            simp only [Nat.shiftRight_eq_div_pow, CMain.sOff20] <;> omega
        · refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> dsimp only <;>
            simp only [Nat.shiftRight_eq_div_pow, CMain.sOff20, ksSplit_P20] <;> omega


/-! ## The whole list -/

/-- `ordM` on two stream claims and more, `C_main`'s list ending in two claims. -/
theorem ordM_split {α : Type} (a b : α) (R L : List α) (x y : α) :
    Lvm.ASM.ordM (a :: b :: R) (L ++ [x, y]) = a :: b :: (L ++ x :: (R ++ [y])) := by
  have h : L ++ [x, y] = (L ++ [x]) ++ [y] := by simp
  rw [Lvm.ASM.ordM, h, List.dropLast_concat, List.getLast?_concat]
  simp

/-- `ordM` at S2GF: the relayout's and `σ′`'s claims, `C_main`'s up to `X_re`, `M`'s halves, `X_im`. -/
theorem ordM_front {α : Type} (a b r1 r2 c d y1 y2 i1 i2 x1 x2 : α) (A B : List α) :
    Lvm.ASM.ordM [a, b, r1, r2] (c :: d :: (A ++ (B ++ [y1, y2, i1, i2, x1, x2]))) =
      a :: b :: c :: d :: (A ++ (B ++ [y1, y2, i1, i2, x1, r1, r2, x2])) := by
  rw [show c :: d :: (A ++ (B ++ [y1, y2, i1, i2, x1, x2])) =
    (c :: d :: (A ++ (B ++ [y1, y2, i1, i2]))) ++ [x1, x2] by simp, ordM_split]
  simp

/-- `assembleSF` in V_S's terms: `M`'s halves on `C_rec`; the tape's, `KS`'s, the output lanes' and the link's
`Y`, `in`, `X` halves on `C_main`. -/
theorem assembleSF_eq (pub : Pub) (k : E2V.KgOutF) :
    E2V.assembleSF pub k = ((E2V.splitE2 19 (mCF k.2.2)).map BClaim.onStack,
      (E2V.tapeClaimsF k.1 pub ++ E2V.keccakClaimsF ksBlk k.2.1 ++ E2V.ksOutputClaimsF k.2.1.1 k.2.1.2.1).map
        BClaim.onStack ++ (E2V.splitE2 nuMainE (yCF k.2.2)).map BClaim.onStack ++
        (E2V.splitE2 nuMainE (inCF k.2.2)).map BClaim.onStack ++
        (E2V.splitE2 nuMainE (xCF k.2.2)).map BClaim.onStack) := by
  unfold E2V.assembleSF
  dsimp only
  rw [ksLinkClaimsF_eq]
  have hmc : (Com.main == Com.crec) = false := rfl
  have hcc : (Com.crec == Com.main) = false := rfl
  simp [List.filter_append, List.filter_map, Function.comp_def, hmc, hcc]

/-- **V_S's claim list at S2GF (after the pin) against `ordM` of `assembleF₂`'s relocated pair** (both shapes):
where V_S's `require` held (every claim on `C_main`), the typed claims (`TRelT`), the mini-bus's and the front's
(`front_rel`), on the statement's shape's stack, are the spec's in V_S's order, the stream claims (the relayout's
point claim, `σ′`'s, `M`'s halves) relocated onto `S`. -/
theorem claimsF_rel (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypX N Q lay) (hσ : SigInS N)
    (x : List UInt8) (t : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE))
    (a : Lvm.ASM.OpenClaims) (hT : TRelT N Q lay t a) (tp : TapeV)
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE))
    (lo : List FE2 × (List FE2 × FE2) × List FE2) (k : E2V.KgOutF) (hk : FrontRel tp co lo k)
    (hsh : TapeShape 20 1 0 tp)
    (hall : (t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsD P20F (pubXF x) tp co lo).all
      (·.1 == .main) = true) :
    List.Forall₂ SCRel (Shape.onStackZsF (Shape.small x)
        (((t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsD P20F (pubXF x) tp co lo).filter
          (·.1 == .main)).map (·.2)))
      (Lvm.ASM.ordM ((E2V.assembleF₂ x a k).1.map (Lvm.CT.reloc20 x)) (E2V.assembleF₂ x a k).2) := by
  obtain ⟨ry, rv, rr, vR, ht1, hry, hrr, rfl, -, hcl⟩ := hT
  obtain ⟨-, -, -, hfc, hfh⟩ := H.toT.fits
  have hall' : ∀ e ∈ t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++
      frontClaimsD P20F (pubXF x) tp co lo, e.1 = .main := fun e he ↦ by
    simpa using List.all_eq_true.1 hall e he
  rw [List.filter_eq_self.2 fun e he ↦ by simp [hall' e he]]
  have hok := H.ok
  rw [nuMain_P20] at hok
  -- the typed claims (roll 11's `typedClaimsM_rel`)
  have hrelay : SCRel (BlockClaim.point ⟨P20.nuRec, (layout0 P20).s⟩ rr vR).onStack
      (relocS (BClaim.point ⟨relayRounds, 0⟩ (rr.map FE.toExt3) (FE.toExt3 vR)).onStack) := by
    rw [← relocS_point]
    exact onStack_rel (Lk.point_rel _ _ _ (by rw [nuRec_P20, layout0_s]; rfl) rfl rfl)
  have hsg : SCRel (⟨⟨23, 0⟩, affW N .sigma ry, rv.getD 2 0⟩ : BlockClaim).onStack
      (relocS (regClaim (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map FE.toExt3)
        ((rv.map FE.toExt3).getD 2 0))) := by
    rw [← regClaim_relocS N Q lay 23 P20.nuRec hok H.hlay hσ, getD_map_toExt3]
    exact regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .sigma 23 (regsOf_dst hok .sigma (.inr (.inr rfl))) ry hry _
  have hcom := regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .com 23
    (regsOf_dst hok .com (.inl rfl)) ry hry (rv.getD 0 0)
  have hks := regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .ks 23
    (regsOf_dst hok .ks (.inr (.inl rfl))) ry hry (rv.getD 3 0)
  have hTV : List.Forall₂ (VRel (Shape.small x)) t.2.1
      [relocS (BClaim.point ⟨relayRounds, 0⟩ (rr.map FE.toExt3) (FE.toExt3 vR)).onStack,
        relocS (regClaim (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map FE.toExt3)
          ((rv.map FE.toExt3).getD 2 0)),
        regClaim (N.inst Q lay) .com N.off (ry.map FE.toExt3) (FE.toExt3 (rv.getD 0 0)),
        regClaim (N.inst Q lay) .ks N.off (ry.map FE.toExt3) (FE.toExt3 (rv.getD 3 0))] := by
    rw [ht1]
    unfold typedClaimsN
    rw [nuMain_P20]
    refine .cons (vrel_of hrelay fun _ ↦ ⟨offOK_relay.inStack, (Shape.OffOK.tail offOK_relay).symm⟩)
      (.cons (vrel_of hsg fun _ ↦ ⟨inStack_full, (tail_affW N P20.nuRec hok .sigma (.inr (.inr rfl)) _ _).symm⟩)
        (.cons (vrel_of hcom fun _ ↦ ⟨inStack_full, (tail_affW N P20.nuRec hok .com (.inl rfl) _ _).symm⟩)
          (.cons (vrel_of hks fun _ ↦ ⟨inStack_full, (tail_affW N P20.nuRec hok .ks (.inr (.inl rfl)) _ _).symm⟩)
            .nil)))
  -- the mini-bus's claims
  have hZrel : List.Forall₂ CRelM ((Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2)).map fun e ↦ (e.1, e.2.1))
      (tableClaimsE N.mbT (M3.claimsOfEvs N.mbT t.2.2)) := by
    rw [Shape.zeroTails, List.map_map]
    simpa [Function.comp_def] using hcl.imp fun _ _ h ↦ CRel.crelM h
  have hZm : ∀ e ∈ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2), e.1 = .main := fun e he ↦
    hall' e (List.mem_append_left _ (List.mem_append_right _ he))
  have hZt : Shape.small x = true → ∀ e ∈ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2), e.1 = .main →
      Shape.InStack e.2.1.block ∧ e.2.2 = Shape.tailValueF e.2.1.onStack.1 := by
    intro _ e he hm
    rw [Shape.zeroTails] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    have h := Shape.table_tails N.mbT N.mbT (fun _ h ↦ h) t.2.2 hfc hfh e' he' hm
    exact ⟨h.inStack, h.tail.symm⟩
  have hZV := forall₂_crelM (s := Shape.small x) hZrel hZm hZt
  -- the front
  have hFV := front_rel (s := Shape.small x) x tp co lo k hk hsh (fun hs ↦ of_decide_eq_true hs)
    (by simp [pubX, pubOf])
  have hV := forall₂_onStackZsF (Lk.forall₂_append (Lk.forall₂_append hTV hZV) hFV)
  -- the spec's list in V_S's order
  have hmbE := main_of_crel hcl fun e he ↦ by
    have := hZm (e.1, e.2, 0) (List.mem_map.2 ⟨e, he, rfl⟩)
    exact this
  convert hV using 1
  have hmb : (N.inst Q lay).mbT = N.mbT := rfl
  set G : VStackClaim → VStackClaim := fun w ↦ if Shape.small x then Shape.onStackZ w else w with hG
  have hρ : ∀ l : List VStackClaim, l.map (Lvm.CT.reloc20 x) = (l.map relocS).map G := fun l ↦ by
    rw [List.map_map]; rfl
  unfold E2V.assembleF₂ typedClaims miniClaims
  rw [hmb, filter_main_self hmbE, filter_crec_nil hmbE, assembleSF_eq]
  dsimp only
  rw [onStackZs_eq_map, hρ, ordM_map]
  congr 1
  rw [inplM_main hmbE]
  simp only [frontW, linkW, E2V.splitE2, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
  rw [ordM_front]
  simp only [getD_map_toExt3]
  rfl

end Lvm.VEq
