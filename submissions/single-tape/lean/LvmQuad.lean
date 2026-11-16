-- New for lvm2 roll 7 (WP E2-S, phase G0). The quadratic ring `R[X]/(X² + tX + 1)` over a ring of
-- characteristic two: `E2 = Quad K x` (`LvmFieldE2`) and the verifier's `Quad Ext3 = Quad E x`.
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.LinearCombination

/-!
# `Quad R t = R[X]/(X² + tX + 1)` (ARCH-7 §2.1)

`E2 = K[X]/(X² + xX + 1)` and the verifier's ring `Quad Ext3 = E3[X]/(X² + xX + 1)` are one
construction over two base rings. `Quad R t` is Mathlib's `QuadraticAlgebra R 1 t`: the generator
`ω = X` satisfies `X² = 1 + tX`, which in characteristic two is `X² + tX + 1 = 0`. An element is
`re + im·X`; it is a commutative `R`-algebra with `R`-basis `1, X` (`QuadraticAlgebra.basis`).

* `re_mul`, `im_mul`: `(a₀ + a₁X)(b₀ + b₁X) = (a₀b₀ + a₁b₁) + (a₀b₁ + a₁b₀ + t·a₁b₁)X`, which is
  Karatsuba's `m₀ = a₀b₀`, `m₁ = a₁b₁`, `m₂ = (a₀ + a₁)(b₀ + b₁)`: `(m₀ + m₁, m₂ + m₀ + m₁ + t·m₁)`
  in characteristic two (`karatsuba`).
* **Field**: Mathlib's instance `QuadraticAlgebra.instField` makes `Quad R t` a field when `R` is a
  field and `[Fact (∀ r : R, r ^ 2 ≠ 1 + t * r)]` (no root of `X² + tX + 1` in `R`).
* `map φ t' h`: the ring hom `Quad R t →+* Quad S t'` applying `φ : R →+* S` to both coordinates
  when `φ t = t'`; with `φ = algebraMap K E` it is `E2 → Quad Ext3`.
* `C`: `R → Quad R t`, `r ↦ r + 0·X`; `re_mul_C`, `im_mul_C`: multiplying by `C s` scales both
  coordinates.
* `Fintype`, `DecidableEq`, `card_quad`: `|Quad R t| = |R|²`.

Nothing here uses that `Quad R t` is a field: the tensor switch is a ring identity (NOTE-FIELD
Prop 7.1, `LvmTensorSwitch`).
-/

set_option autoImplicit false

namespace Lvm

/-- **`R[X]/(X² + tX + 1)`** in characteristic two: Mathlib's `QuadraticAlgebra R 1 t`
(`X² = 1 + tX`). -/
abbrev Quad (R : Type*) [One R] (t : R) : Type _ := QuadraticAlgebra R 1 t

namespace Quad

open scoped QuadraticAlgebra

section Ring

variable {R : Type*} [CommRing R] {t : R}

/-- The real coordinate of a product. -/
theorem re_mul (z w : Quad R t) : (z * w).re = z.re * w.re + z.im * w.im := by
  simp only [QuadraticAlgebra.re_mul, one_mul]

/-- The `X` coordinate of a product. -/
theorem im_mul (z w : Quad R t) : (z * w).im = z.re * w.im + z.im * w.re + t * z.im * w.im :=
  QuadraticAlgebra.im_mul z w

/-- **Karatsuba** in characteristic two: three products `m₀ = a₀b₀`, `m₁ = a₁b₁`,
`m₂ = (a₀ + a₁)(b₀ + b₁)` and one product by `t`. -/
theorem karatsuba [CharP R 2] (z w : Quad R t) :
    z * w = ⟨z.re * w.re + z.im * w.im,
      (z.re + z.im) * (w.re + w.im) + z.re * w.re + z.im * w.im + t * (z.im * w.im)⟩ := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  ext
  · exact re_mul z w
  · rw [im_mul]
    linear_combination (-(z.re * w.re) - z.im * w.im) * h2

/-- `X² = 1 + tX`. -/
theorem omega_sq : (QuadraticAlgebra.omega : Quad R t) * QuadraticAlgebra.omega = ⟨1, t⟩ :=
  QuadraticAlgebra.omega_mul_omega_eq_mk

/-! ## The base ring inside `Quad R t` -/

/-- `r ↦ r + 0·X` (Mathlib's `QuadraticAlgebra.C`, which is `algebraMap R (Quad R t)`). -/
abbrev C (r : R) : Quad R t := QuadraticAlgebra.C r

theorem C_eq_algebraMap (r : R) : (C r : Quad R t) = algebraMap R (Quad R t) r := rfl

theorem re_mul_C (z : Quad R t) (s : R) : (z * C s).re = z.re * s := by
  simp [QuadraticAlgebra.re_C, QuadraticAlgebra.im_C]

theorem im_mul_C (z : Quad R t) (s : R) : (z * C s).im = z.im * s := by
  simp [QuadraticAlgebra.re_C, QuadraticAlgebra.im_C]

/-! ## Change of base ring -/

/-- **Coefficientwise base change** `Quad R t →+* Quad S t'` along `φ : R →+* S` with `φ t = t'`
(`E2 → Quad Ext3` for `φ = algebraMap K E`). -/
def map {S : Type*} [CommRing S] (φ : R →+* S) (t' : S) (h : φ t = t') : Quad R t →+* Quad S t' where
  toFun z := ⟨φ z.re, φ z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by
    ext
    · simp only [re_mul, map_add, map_mul]
    · simp only [im_mul, map_add, map_mul, h]
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

@[simp] theorem map_re {S : Type*} [CommRing S] (φ : R →+* S) (t' : S) (h : φ t = t') (z : Quad R t) :
    (map φ t' h z).re = φ z.re := rfl

@[simp] theorem map_im {S : Type*} [CommRing S] (φ : R →+* S) (t' : S) (h : φ t = t') (z : Quad R t) :
    (map φ t' h z).im = φ z.im := rfl

end Ring

/-! ## Finiteness and decidable equality -/

instance instDecidableEq {R : Type*} [One R] [DecidableEq R] {t : R} : DecidableEq (Quad R t) :=
  fun z w ↦ decidable_of_iff (z.re = w.re ∧ z.im = w.im) (QuadraticAlgebra.ext_iff (x := z) (y := w)).symm

instance instFintype {R : Type*} [One R] [Fintype R] {t : R} : Fintype (Quad R t) :=
  Fintype.ofEquiv (R × R) (QuadraticAlgebra.equivProd 1 t).symm

/-- `|Quad R t| = |R|²`. -/
theorem card_quad {R : Type*} [One R] [Fintype R] {t : R} :
    Fintype.card (Quad R t) = Fintype.card R ^ 2 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd 1 t), Fintype.card_prod, sq]

end Quad

end Lvm
