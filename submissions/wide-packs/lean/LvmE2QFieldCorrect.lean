-- New for lvm2 E2F (slice S1, E2F-Q): the schoolbook form of `FE2`'s product (the form LoopIR's `E2` rows state,
-- coordinate by coordinate), from E2F-V's Karatsuba (LvmFieldE2Fast) and ring (LvmFieldE2Correct).
import LvmE2QField
import LvmFieldE2Correct

/-!
# `FE2`'s product, schoolbook

`mul_def`: `(a₀ + a₁X)(b₀ + b₁X) = a₀b₀ + a₁b₁ + (a₀b₁ + a₁b₀ + x·a₁b₁)X` (characteristic 2; E2F-V's `mul` is
Karatsuba with three products).
-/

set_option autoImplicit false

namespace Lvm.FE2

theorem fk_two : (2 : FK) = 0 := by
  have : (2 : FK) = 1 + 1 := by norm_num
  rw [this]; rfl

/-- **The product, schoolbook.** -/
theorem mul_def (a b : FE2) :
    a * b = ⟨a.re * b.re + a.im * b.im, a.re * b.im + a.im * b.re + FK.x * (a.im * b.im)⟩ := by
  have h : (a.re + a.im) * (b.re + b.im) + a.re * b.re + a.im * b.im + FK.x * (a.im * b.im) =
      a.re * b.im + a.im * b.re + FK.x * (a.im * b.im) := by
    linear_combination (a.re * b.re + a.im * b.im) * fk_two
  show (⟨a.re * b.re + a.im * b.im,
    (a.re + a.im) * (b.re + b.im) + a.re * b.re + a.im * b.im + FK.x * (a.im * b.im)⟩ : FE2) = _
  rw [h]

end Lvm.FE2
