-- New for lvm2 S1 (E2-F, E2F-V), E2AC-DES §6 statement 15 (`fe2_mul_eq`): the machine-word `FE2`
-- (`LvmFieldE2Fast`) is `LvmFieldE2`'s `E2` (cf. E3's `LvmFieldCorrect`).
import LvmFieldE2Fast
import LvmFieldE2

/-!
# `FE2` is `E2`

`toE2 : FE2 → E2` reads the two words as `K` (`FK.toBF64`). It is a bijection, and the operations
are `E2`'s:
* **`fe2_mul_eq`** (statement 15): Karatsuba's three products give `E2`'s product;
* `toE2_add`, `toE2_sq`, `toE2_inv`, `toE2_mulK`, `toE2_ofK`, `toE2_npow`;
* `instField`: `FE2` is a field with the word operations, `ringEquivE2 : FE2 ≃+* E2`, and an
  `FK`-algebra by `ofK` (`instAlgebra`).
-/

set_option autoImplicit false

namespace Lvm.FE2

open LeanVM.Parameters

/-- The `E2` element of a machine-word pair. -/
def toE2 (a : FE2) : E2 := ⟨FK.toBF64 a.re, FK.toBF64 a.im⟩

/-- The machine-word pair of an `E2` element. -/
def ofE2 (y : E2) : FE2 := ⟨FK.ofBF64 y.re, FK.ofBF64 y.im⟩

@[simp] theorem ofE2_toE2 (a : FE2) : ofE2 (toE2 a) = a := rfl

@[simp] theorem toE2_ofE2 (y : E2) : toE2 (ofE2 y) = y := rfl

theorem toE2_injective : Function.Injective toE2 := fun a b h ↦ by
  rw [← ofE2_toE2 a, h, ofE2_toE2]

theorem toE2_re (a : FE2) : (toE2 a).re = FK.toBF64 a.re := rfl

theorem toE2_im (a : FE2) : (toE2 a).im = FK.toBF64 a.im := rfl

private theorem K_two : (2 : K) = 0 := CharP.cast_eq_zero K 2

private theorem hx : FK.toBF64 FK.x = g := rfl

@[simp] theorem toE2_zero : toE2 0 = 0 := rfl

@[simp] theorem toE2_one : toE2 1 = 1 := by
  refine QuadraticAlgebra.ext ?_ ?_
  · exact FK.toBF64_one
  · exact FK.toBF64_zero

@[simp] theorem toE2_add (a b : FE2) : toE2 (a + b) = toE2 a + toE2 b := by
  refine QuadraticAlgebra.ext ?_ ?_
  · exact FK.toBF64_add a.re b.re
  · exact FK.toBF64_add a.im b.im

/-- **Statement 15 (`fe2_mul_eq`)**: the fast product (Karatsuba, three `FK` products) is `E2`'s. -/
@[simp] theorem fe2_mul_eq (a b : FE2) : toE2 (a * b) = toE2 a * toE2 b := by
  rw [Quad.karatsuba]
  refine QuadraticAlgebra.ext ?_ ?_
  · change FK.toBF64 (a.re * b.re + a.im * b.im) = _
    rw [FK.toBF64_add, FK.toBF64_mul, FK.toBF64_mul]
    rfl
  · change FK.toBF64 ((a.re + a.im) * (b.re + b.im) + a.re * b.re + a.im * b.im +
      FK.x * (a.im * b.im)) = _
    simp only [FK.toBF64_add, FK.toBF64_mul, hx]
    rfl

@[simp] theorem toE2_sq (a : FE2) : toE2 (sq a) = toE2 a * toE2 a := by
  rw [Quad.karatsuba]
  refine QuadraticAlgebra.ext ?_ ?_
  · change FK.toBF64 (FK.sq a.re + FK.sq a.im) = _
    rw [FK.toBF64_add, FK.toBF64_sq, FK.toBF64_sq]
    rfl
  · change FK.toBF64 (FK.x * FK.sq a.im) = _
    rw [FK.toBF64_mul, FK.toBF64_sq, hx]
    change _ = (FK.toBF64 a.re + FK.toBF64 a.im) * (FK.toBF64 a.re + FK.toBF64 a.im) +
      FK.toBF64 a.re * FK.toBF64 a.re + FK.toBF64 a.im * FK.toBF64 a.im +
      g * (FK.toBF64 a.im * FK.toBF64 a.im)
    linear_combination
      (-(FK.toBF64 a.re * FK.toBF64 a.re) - FK.toBF64 a.im * FK.toBF64 a.im -
        FK.toBF64 a.re * FK.toBF64 a.im) * K_two

@[simp] theorem toE2_inv (a : FE2) : toE2 a⁻¹ = (toE2 a)⁻¹ := by
  set A0 := FK.toBF64 a.re with hA0
  set A1 := FK.toBF64 a.im with hA1
  set N := A0 * A0 + g * A0 * A1 + A1 * A1 with hNdef
  have hinv : toE2 a⁻¹ = ⟨(A0 + g * A1) * N⁻¹, A1 * N⁻¹⟩ := by
    refine QuadraticAlgebra.ext ?_ ?_
    · change FK.toBF64 ((a.re + FK.x * a.im) *
        (a.re * a.re + FK.x * a.re * a.im + a.im * a.im)⁻¹) = _
      simp only [FK.toBF64_add, FK.toBF64_mul, FK.toBF64_inv, hx]
      rfl
    · change FK.toBF64 (a.im * (a.re * a.re + FK.x * a.re * a.im + a.im * a.im)⁻¹) = _
      simp only [FK.toBF64_add, FK.toBF64_mul, FK.toBF64_inv, hx]
      rfl
  have hN : N = QuadraticAlgebra.norm (toE2 a) := by
    rw [QuadraticAlgebra.norm_def, toE2_re, toE2_im]
    linear_combination (A1 * A1) * K_two
  rw [hinv]
  by_cases hz : toE2 a = 0
  · have h0 : N = 0 := by rw [hN, hz, QuadraticAlgebra.norm_zero]
    rw [hz, inv_zero, h0, inv_zero]
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp
  · have hN0 : N ≠ 0 := by
      rw [hN]
      exact fun h ↦ hz (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h)
    have hc := mul_inv_cancel₀ hN0
    refine eq_inv_of_mul_eq_one_right ?_
    refine QuadraticAlgebra.ext ?_ ?_
    · rw [Quad.re_mul, toE2_re, toE2_im, QuadraticAlgebra.re_one]
      change A0 * ((A0 + g * A1) * N⁻¹) + A1 * (A1 * N⁻¹) = 1
      linear_combination hc
    · rw [Quad.im_mul, toE2_re, toE2_im, QuadraticAlgebra.im_one]
      change A0 * (A1 * N⁻¹) + A1 * ((A0 + g * A1) * N⁻¹) + g * A1 * (A1 * N⁻¹) = 0
      linear_combination (N⁻¹ * (A0 * A1 + g * A1 * A1)) * K_two

@[simp] theorem toE2_mulK (a : FE2) (k : FK) :
    toE2 (mulK a k) = toE2 a * Lvm.Quad.C (FK.toBF64 k) := by
  refine QuadraticAlgebra.ext ?_ ?_
  · rw [Quad.re_mul_C]
    exact FK.toBF64_mul a.re k
  · rw [Quad.im_mul_C]
    exact FK.toBF64_mul a.im k

@[simp] theorem toE2_ofK (k : FK) : toE2 (ofK k) = Lvm.Quad.C (FK.toBF64 k) := by
  refine QuadraticAlgebra.ext ?_ ?_
  · rfl
  · exact FK.toBF64_zero

@[simp] theorem toE2_neg (a : FE2) : toE2 (-a) = -toE2 a := by
  refine QuadraticAlgebra.ext ?_ ?_
  · rw [QuadraticAlgebra.re_neg, CharTwo.neg_eq]
    rfl
  · rw [QuadraticAlgebra.im_neg, CharTwo.neg_eq]
    rfl

@[simp] theorem toE2_sub (a b : FE2) : toE2 (a - b) = toE2 a - toE2 b := by
  change toE2 (a + b) = _
  rw [toE2_add, sub_eq_add_neg, ← toE2_neg]
  rfl

/-! ## The field structure, transported from `E2` -/

instance : SMul ℕ FE2 := ⟨nsmulRec⟩
instance : SMul ℤ FE2 := ⟨zsmulRec nsmulRec⟩
instance : NatCast FE2 := ⟨fun n => ofK (n : FK)⟩
instance : IntCast FE2 := ⟨fun n => ofK (n : FK)⟩

@[simp] theorem toE2_natCast (n : ℕ) : toE2 (n : FE2) = (n : E2) := by
  change toE2 (ofK (n : FK)) = _
  rw [toE2_ofK, FK.toBF64_natCast]
  exact QuadraticAlgebra.C_natCast n

@[simp] theorem toE2_intCast (n : ℤ) : toE2 (n : FE2) = (n : E2) := by
  change toE2 (ofK (n : FK)) = _
  rw [toE2_ofK, FK.toBF64_intCast]
  exact QuadraticAlgebra.C_intCast n

theorem toE2_nsmul (n : ℕ) (a : FE2) : toE2 (n • a) = n • toE2 a := by
  change toE2 (nsmulRec n a) = _
  induction n with
  | zero => rw [nsmulRec, zero_smul]; rfl
  | succ n ih => rw [nsmulRec, toE2_add, ih, succ_nsmul]

theorem toE2_zsmul (n : ℤ) (a : FE2) : toE2 (n • a) = n • toE2 a := by
  rcases n with n | n
  · exact (toE2_nsmul n a).trans (natCast_zsmul _ _).symm
  · change toE2 (-(nsmulRec (n + 1) a)) = _
    rw [toE2_neg, negSucc_zsmul]
    exact congrArg _ (toE2_nsmul (n + 1) a)

theorem toE2_powGo (k : ℕ) (b : FE2) (e : ℕ) (acc : FE2) (he : e ≤ k) :
    toE2 (powGo k b e acc) = toE2 acc * toE2 b ^ e := by
  induction k generalizing b e acc with
  | zero => obtain rfl : e = 0 := by (clear * - e he; omega)
            rw [powGo, pow_zero, mul_one]
  | succ k ih =>
    rw [powGo]
    split_ifs with h0 ho
    · rw [h0, pow_zero, mul_one]
    · rw [ih _ _ _ (by (clear * - e k he ho; omega)), fe2_mul_eq, toE2_sq]
      conv_rhs => rw [show e = 2 * (e / 2) + 1 by (clear * - e k ho; omega), pow_succ, pow_mul, _root_.sq]
      ring
    · rw [ih _ _ _ (by (clear * - e k he; omega)), toE2_sq]
      conv_rhs => rw [show e = 2 * (e / 2) by (clear * - e k ho; omega), pow_mul, _root_.sq]

theorem toE2_npow (a : FE2) (n : ℕ) : toE2 (a ^ n) = toE2 a ^ n := by
  change toE2 (powGo n a n 1) = _
  rw [toE2_powGo n a n 1 le_rfl, toE2_one, one_mul]

/-- The ring structure, pulled back along the injective `toE2` (the operations are `FE2`'s). -/
instance instCommRing : CommRing FE2 :=
  toE2_injective.commRing _ toE2_zero toE2_one toE2_add fe2_mul_eq toE2_neg toE2_sub
    toE2_nsmul toE2_zsmul toE2_npow toE2_natCast toE2_intCast

instance : Div FE2 := ⟨fun a b => a * b⁻¹⟩

/-- **`FE2` is a field**, with the word operations. -/
instance instField : Field FE2 where
  inv := inv
  div a b := a * b⁻¹
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel a h := toE2_injective (by
    show toE2 (a * a⁻¹) = toE2 1
    rw [fe2_mul_eq, toE2_inv, toE2_one]
    exact mul_inv_cancel₀ (fun h' => h (toE2_injective (h'.trans toE2_zero.symm))))
  inv_zero := toE2_injective (by
    show toE2 (0 : FE2)⁻¹ = toE2 0
    rw [toE2_inv, toE2_zero, inv_zero])
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

/-- `toE2` as a bijection. -/
def equivE2 : FE2 ≃ E2 where
  toFun := toE2
  invFun := ofE2
  left_inv := ofE2_toE2
  right_inv := toE2_ofE2

/-- `toE2` as a ring isomorphism. -/
def ringEquivE2 : FE2 ≃+* E2 where
  toEquiv := equivE2
  map_mul' := fe2_mul_eq
  map_add' := toE2_add

@[simp] theorem ringEquivE2_apply (a : FE2) : ringEquivE2 a = toE2 a := rfl

@[simp] theorem toE2_div (a b : FE2) : toE2 (a / b) = toE2 a / toE2 b := by
  change toE2 (a * b⁻¹) = _
  rw [fe2_mul_eq, toE2_inv, div_eq_mul_inv]

/-- `ofK` is the embedding of `FK` into `FE2`. -/
def ofKRingHom : FK →+* FE2 where
  toFun := ofK
  map_one' := rfl
  map_mul' a b := toE2_injective (by
    rw [fe2_mul_eq, toE2_ofK, toE2_ofK, toE2_ofK, FK.toBF64_mul]
    exact QuadraticAlgebra.C_mul _ _)
  map_zero' := rfl
  map_add' a b := toE2_injective (by
    rw [toE2_add, toE2_ofK, toE2_ofK, toE2_ofK, FK.toBF64_add]
    exact QuadraticAlgebra.C_add _ _)

/-- `FE2` is an `FK`-algebra by `ofK`. -/
instance instAlgebra : Algebra FK FE2 := ofKRingHom.toAlgebra

theorem algebraMap_eq_ofK (c : FK) : algebraMap FK FE2 c = ofK c := rfl

end Lvm.FE2
