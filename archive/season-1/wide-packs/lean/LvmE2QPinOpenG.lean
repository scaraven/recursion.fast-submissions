-- New for lvm2 E2-FT (E2F-QH5): the small shape's `D` claims with the point in a commutative `E3`-algebra `R`
-- (`Quad Ext3` for the `E2` word halves; a CRT component of the row switch for the tape's row claim): `V_S`'s region
-- sum (`onStackZF`'s, `LvmQShapeF.zW`) of `eqEval`'s product `Π (1 + z_l + y_l)` with `z_l ∈ R` is the product at
-- the small point `dzD`, times `κ = (1 + z₁₈)(1 + z₁₉)`, at the rotated point (`LvmQShapeF.onStackZB_dpt` over `R`).
import LvmQShapeB
-- (GOLF2 import pruning: dropped LvmQShapeC: unused by this module.)

-- (GOLF2: 3 declarations that `certified` does not use moved verbatim to `LvmE2QPinOpenGOff`, outside its import closure.)

/-!
# `D`'s claims over an `E3`-algebra

* `fR`, `pR`: `eqEval`'s factor `1 + a + y` and fold with `a ∈ R`, `y ∈ E3` (`pR_append`, `pR_cons`);
* `zWR`: `zW` with values in `R` (`zW_lin`: an `E3`-linear `L` takes `zWR` to `zW`);
* **`zWR_D`**: for `z` of 22 coordinates, the region sum of `eqAbove_D(y)·pR z y` at `x` is
  `eqAbove_D(x^σ)·κ(z)·pR (dzR z) x^σ` (`x^σ = rotZ x`);
* `interp2`: `Σ_{l<4} eq(sel(l), (a, b))·pR [z₀, z₁] sel(l) = pR [z₀, z₁] [a, b]` (the bilinear interpolation).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Har Lvm.Shape Lvm.QShape

section Gen

variable {R : Type} [CommRing R] [Algebra FE R]

/-- `eqEval`'s factor `1 + a + y` with `a ∈ R`. -/
def fR (a : R) (y : FE) : R := 1 + a + algebraMap FE R y

/-- **`eqEval` with the point in `R`**: `Π_l (1 + z_l + y_l)`. -/
def pR (z : List R) (y : List FE) : R := (List.zipWith fR z y).prod

theorem pR_nil : pR ([] : List R) [] = 1 := rfl

theorem pR_cons (a : R) (z : List R) (b : FE) (y : List FE) : pR (a :: z) (b :: y) = fR a b * pR z y := by
  simp [pR, List.zipWith_cons_cons, List.prod_cons]

theorem pR_append {z₁ z₂ : List R} {y₁ y₂ : List FE} (h : z₁.length = y₁.length) :
    pR (z₁ ++ z₂) (y₁ ++ y₂) = pR z₁ y₁ * pR z₂ y₂ := by
  simp only [pR, List.zipWith_append h, List.prod_append]

theorem two_R : (2 : R) = 0 := by
  rw [show (2 : R) = algebraMap FE R 2 from (map_ofNat _ 2).symm, show (2 : FE) = 0 from CharTwo.two_eq_zero,
    map_zero]

/-- `D`'s scale `(1 + z₁₈)(1 + z₁₉)` over `R`. -/
def kapR (z : List R) : R := (1 + z.getD 18 0) * (1 + z.getD 19 0)

/-- `D`'s small point over `R`: `z₀…z₁₇ ‖ z₂₀ z₂₁ ‖ 0 0`. -/
def dzR (z : List R) : List R := z.take 18 ++ [z.getD 20 0, z.getD 21 0, 0, 0]

/-- `zW` with values in `R`. -/
def zWR (x : List FE) (w : List FE → R) : R :=
  algebraMap FE R (1 - x.headD 0) *
    (regions.map fun r ↦ algebraMap FE R ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail) * w (relocF x r)).sum

/-- An `E3`-linear map takes `zWR` to `zW`. -/
theorem zW_lin (L : R →ₗ[FE] FE) (x : List FE) (w : List FE → R) : zW x (fun y ↦ L (w y)) = L (zWR x w) := by
  have h1 : ∀ (c : FE) (s : R), L (algebraMap FE R c * s) = c * L s := fun c s ↦ by
    rw [← Algebra.smul_def, L.map_smul, smul_eq_mul]
  unfold zW zWR
  rw [h1, map_list_sum, List.map_map]
  exact congrArg (_ * ·) (congrArg List.sum (List.map_congr_left fun r _ ↦ (h1 _ _).symm))

theorem split4G {α : Type} (z : List α) (n : ℕ) (h : z.length = n + 4) :
    ∃ zl a b c d, z = zl ++ [a, b, c, d] ∧ zl.length = n := by
  have hd : (z.drop n).length = 4 := by simp [h]
  obtain ⟨a, b, c, d, hd'⟩ : ∃ a b c d, z.drop n = [a, b, c, d] := by
    rcases hdd : z.drop n with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> rw [hdd] at hd <;>
      simp at hd
    exact ⟨a, b, c, d, rfl⟩
  exact ⟨z.take n, a, b, c, d, by rw [← hd', List.take_append_drop], by simp [h]⟩

theorem fR_zero (a : R) : fR a 0 = 1 + a := by simp [fR]

/-- **The bilinear interpolation** over `R`: `Σ_{u ∈ {0,1}²} eq(u, (a, b))·(1 + z₀ + u₀)(1 + z₁ + u₁)`. -/
theorem interp2 (z0 z1 : R) (a b : FE) :
    algebraMap FE R ((1 + 0 + a) * (1 + 0 + b)) * (fR z0 0 * fR z1 0) +
      algebraMap FE R ((1 + 1 + a) * (1 + 0 + b)) * (fR z0 1 * fR z1 0) +
      algebraMap FE R ((1 + 0 + a) * (1 + 1 + b)) * (fR z0 0 * fR z1 1) +
      algebraMap FE R ((1 + 1 + a) * (1 + 1 + b)) * (fR z0 1 * fR z1 1) = fR z0 a * fR z1 b := by
  simp only [fR, map_mul, map_add, map_one, map_zero]
  generalize algebraMap FE R a = A
  generalize algebraMap FE R b = B
  linear_combination ((2 + A + z0 + A * z0) * (1 + B + z1) + (2 + B + z1 + B * z1) * (1 + A + z0) +
    2 * (2 + A + z0 + A * z0) * (2 + B + z1 + B * z1)) * (two_R : (2 : R) = 0)

/-- `D`'s relocated point for region `l < 4`: `lo ‖ 0 0 ‖ sel(l)`. -/
theorem relocF_D (x0 : FE) (lo : List FE) (a b c d : FE) (hlo : lo.length = 18) (l : ℕ) :
    relocF (x0 :: (lo ++ [a, b, c, d])) (18, l * 2 ^ 20, l * 2 ^ 18) =
      lo ++ ([0, 0] ++ selectorPoint l (CMain.nu20 - 20)) := by
  simp only [relocF, List.tail_cons, List.append_assoc]
  rw [List.take_append_of_le_length (by (clear * - hlo; omega)), List.take_of_length_le (by (clear * - hlo; omega)), sel4]

theorem sel_bits (l : ℕ) (hl : l < 4) :
    selectorPoint l (CMain.nu20 - 20) = [eOfNat (l % 2), eOfNat (l / 2 % 2), 0] ∧
      selectorPoint ((l * 2 ^ 18) >>> 18) 4 = [eOfNat (l % 2), eOfNat (l / 2 % 2), 0, 0] := by
  have e : (l * 2 ^ 18) >>> 18 = l := by rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (by positivity)]
  rw [e]
  simp only [show CMain.nu20 - 20 = 3 from rfl, selectorPoint, List.range_succ, List.range_zero, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, Nat.shiftRight_eq_div_pow, List.cons.injEq, and_true]
  refine ⟨⟨by simp, by simp, ?_⟩, by simp, by simp, ?_, ?_⟩ <;>
    rw [show l / 2 ^ _ % 2 = 0 by (clear * - hl; omega)] <;> rfl

/-- **The `D` region sum over `R`** (`onStackZB_dpt` with the point in `R`). -/
theorem zWR_D (z : List R) (hz : z.length = 22) (x : List FE) (hx : x.length = CMain.nu20) :
    zWR x (fun y ↦ algebraMap FE R ((⟨22, 0⟩ : Placement).eqAbove y) * pR z (y.take 22)) =
      algebraMap FE R ((⟨22, 0⟩ : Placement).eqAbove (rotZ x)) * (kapR z * pR (dzR z) ((rotZ x).take 22)) := by
  have hnu : CMain.nu20 = 23 := rfl
  obtain ⟨zl, z18, z19, z20, z21, rfl, hzl⟩ := split4G z 18 (by omega)
  cases x with
  | nil => simp at hx
  | cons x0 xt =>
  obtain ⟨lo, a, b, c, d, rfl, hlo⟩ := split4 xt 18 (by simp only [List.length_cons] at hx; omega)
  have k1 : kapR (zl ++ [z18, z19, z20, z21]) = (1 + z18) * (1 + z19) := by
    simp [kapR, List.getD_eq_getElem?_getD, List.getElem?_append_right, hzl]
  have k2 : dzR (zl ++ [z18, z19, z20, z21]) = zl ++ [z20, z21, 0, 0] := by
    simp [dzR, List.getD_eq_getElem?_getD, List.getElem?_append_right, hzl, List.take_append_of_le_length]
  have hrot : rotZ (x0 :: (lo ++ [a, b, c, d])) = (lo ++ [a, b, c, d]) ++ [x0] := by simp [rotZ]
  have hl22 : (lo ++ [a, b, c, d]).length = 22 := by simp [hlo]
  rw [k1, k2, hrot, eqAbove_app 22 0 _ _ hl22, List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega), pR_append (by simp [hzl, hlo])]
  -- the regions: `D`'s four, the three blocks above `D`
  unfold zWR
  rw [regions, List.map_append, List.sum_append]
  have hterm : ∀ j < 3,
      algebraMap FE R ((⟨(20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20).1, (20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20).2.2⟩ :
        Placement).eqAbove (x0 :: (lo ++ [a, b, c, d])).tail) *
      (algebraMap FE R ((⟨22, 0⟩ : Placement).eqAbove (relocF (x0 :: (lo ++ [a, b, c, d]))
        (20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20))) *
        pR (zl ++ [z18, z19, z20, z21]) ((relocF (x0 :: (lo ++ [a, b, c, d]))
          (20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20)).take 22)) = 0 := by
    intro j hj3
    rw [relocF_20 x0 (lo ++ [a, b, c, d]) (by simp [hlo])]
    have hs : selectorPoint (4 + j) (CMain.nu20 - 20) =
        [eOfNat ((4 + j) % 2), eOfNat ((4 + j) / 2 % 2), 1] := by
      simp only [show CMain.nu20 - 20 = 3 from rfl, selectorPoint, List.range_succ, List.range_zero, List.map_cons,
        List.map_nil, List.nil_append, List.cons_append, Nat.shiftRight_eq_div_pow, List.cons.injEq, and_true]
      refine ⟨by simp, by simp, ?_⟩
      rw [show (4 + j) / 2 ^ 2 % 2 = 1 by rw [show (2 : ℕ) ^ 2 = 4 from rfl]; omega]; rfl
    have hlo20 : (lo ++ [a, b, c, d]).take 20 = lo ++ [a, b] := by
      rw [List.take_append, List.take_of_length_le (by omega), hlo]
      rfl
    rw [hs, hlo20, show lo ++ [a, b] ++ [eOfNat ((4 + j) % 2), eOfNat ((4 + j) / 2 % 2), 1] =
      (lo ++ [a, b, eOfNat ((4 + j) % 2), eOfNat ((4 + j) / 2 % 2)]) ++ [1] by simp,
      eqAbove_app 22 0 _ _ (by simp [hlo])]
    have h0 : eqEval (selectorPoint (0 >>> 22) [(1 : FE)].length) [1] = 0 := by
      simp [selectorPoint, eqEval, eOfNat_zero, CharTwo.add_self_eq_zero]
    rw [h0, map_zero, zero_mul, mul_zero]
  have hreg : ∀ f : ℕ × ℕ × ℕ → R, (∀ j < 3, f (20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20) = 0) →
      ((List.map (fun j => (20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20))
        (List.range (2 ^ (CMain.nu20 - 21) - 1))).map f).sum = 0 := by
    intro f hf
    rw [List.sum_eq_zero]
    intro t ht
    simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    exact hf j (by rw [show CMain.nu20 - 21 = 2 from rfl] at hj; simpa using hj)
  rw [hreg _ (fun j hj => hterm j hj), add_zero]
  -- `D`'s four regions
  have hD : ∀ l < 4, algebraMap FE R ((⟨18, l * 2 ^ 18⟩ : Placement).eqAbove (lo ++ [a, b, c, d])) *
      (algebraMap FE R ((⟨22, 0⟩ : Placement).eqAbove (relocF (x0 :: (lo ++ [a, b, c, d]))
        (18, l * 2 ^ 20, l * 2 ^ 18))) *
        pR (zl ++ [z18, z19, z20, z21]) ((relocF (x0 :: (lo ++ [a, b, c, d])) (18, l * 2 ^ 20, l * 2 ^ 18)).take 22)) =
      algebraMap FE R ((1 + 0 + c) * (1 + 0 + d)) * (pR zl lo * ((1 + z18) * (1 + z19))) *
        (algebraMap FE R ((1 + eOfNat (l % 2) + a) * (1 + eOfNat (l / 2 % 2) + b)) *
          (fR z20 (eOfNat (l % 2)) * fR z21 (eOfNat (l / 2 % 2)))) := by
    intro l hl
    obtain ⟨s3, s4⟩ := sel_bits l hl
    rw [relocF_D x0 lo a b c d hlo l, s3, eqAbove_app 18 _ lo _ hlo,
      show ([a, b, c, d] : List FE).length = 4 from rfl, s4,
      show lo ++ ([0, 0] ++ [eOfNat (l % 2), eOfNat (l / 2 % 2), 0]) =
        (lo ++ [0, 0, eOfNat (l % 2), eOfNat (l / 2 % 2)]) ++ [0] by simp,
      eqAbove_app 22 0 _ _ (by simp [hlo]), List.take_append_of_le_length (by simp [hlo]),
      List.take_of_length_le (by simp [hlo]), pR_append (by simp [hzl, hlo])]
    have e1 : eqEval (selectorPoint (0 >>> 22) [(0 : FE)].length) [0] = 1 := by simp [selectorPoint, eqEval, eOfNat_zero]
    rw [e1, map_one, one_mul]
    simp only [pR_cons, pR_nil, eqEval, List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons,
      List.foldl_nil, one_mul, fR_zero, map_mul]
    ring
  simp only [show (4 : ℕ) = 3 + 1 from rfl, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  simp only [Prod.fst, Prod.snd, List.tail_cons]
  rw [hD 0 (by norm_num), hD 1 (by norm_num), hD 2 (by norm_num), hD 3 (by norm_num)]
  simp only [Nat.zero_mod, Nat.zero_div, Nat.one_mod, show 1 / 2 % 2 = 0 from rfl, show 2 % 2 = 0 from rfl,
    show 2 / 2 % 2 = 1 from rfl, show 3 % 2 = 1 from rfl, show 3 / 2 % 2 = 1 from rfl, eOfNat_zero, eOfNat_one]
  have hI := interp2 z20 z21 a b
  simp only [selectorPoint, show 0 >>> 22 = 0 from rfl, List.length_singleton, List.range_one, List.map_cons,
    List.map_nil, Nat.zero_shiftRight, Nat.zero_mod, eOfNat_zero, eqEval, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.foldl_cons, List.foldl_nil, one_mul, pR_cons, pR_nil, mul_one]
  rw [fR_zero, fR_zero, CharTwo.sub_eq_add]
  simp only [fR, List.headD_cons, map_mul, map_add, map_one, map_zero] at hI ⊢
  -- factor the four regions' common product out and use `hI` (a `linear_combination` here ring-normalized the
  -- expanded degree-8 products: 3 M hb)
  simp only [add_zero] at hI ⊢
  rw [← mul_add, ← mul_add, ← mul_add, hI]
  ac_rfl

end Gen

end Lvm.Q2
