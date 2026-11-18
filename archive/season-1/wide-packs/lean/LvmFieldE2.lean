-- New for lvm2 roll 7 (WP E2-S, phase G0). The front field `E2 = K[X]/(X² + xX + 1)` = GF(2^128)
-- and the verifier's ring `Quad Ext3 = E3[X]/(X² + xX + 1)` (ARCH-7 §2.1, NOTE-FIELD §8).
import LvmQuad
import LvmFieldFacts
import LvmFieldKCorrect

/-!
# `E2 = K[X]/(X² + xX + 1)` and its `Quad Ext3` view

* **`E2`** is `Quad K g` (`LvmQuad`): `re + im·X` with `X² = 1 + xX`, `x = g` the generator of `K`.
* **`no_root`**: `X² + xX + 1` has no root in `K`, so `E2` is a field (Mathlib's
  `QuadraticAlgebra.instField` with the instance `fact_no_root`). The proof is the additive
  Hilbert 90 criterion: a root `r` gives `w = r/x` with `w² + w = 1/x²`, so `Tr(1/x²) = 0`, but
  `Tr(1/x²) = 1` (`trK_c`, a kernel check on `Lvm.FK` words; NOTE-F's `check_e2.py`).
  `trK_sq_add`: `Tr(w² + w) = w^(2^64) + w = 0`.
* `card_E2`: `|E2| = 2^128`.
* **`E6`** (ARCH-7's `Quad Ext3`) is `Quad E (ofK g)`, the ring the verifier uses to evaluate the
  two weights of a word claim at an `E3` point (`LvmTensorSwitch.tensorSwitch`). `e2ToE6` maps
  `E2` into it coefficientwise (`Quad.map`), `algebraMap E E6` maps `E3`. Neither a field proof for
  `E6` nor coprimality of the degrees is used anywhere (NOTE-FIELD §7).
-/

set_option autoImplicit false

namespace LeanVM.Parameters

open Lvm

/-! ## The trace and the irreducibility of `X² + xX + 1` -/

/-- The absolute trace `Tr(a) = Σ_{i < 64} a^(2^i)` of `K` over `GF(2)`. -/
noncomputable def trK (a : K) : K := ∑ i ∈ Finset.range 64, a ^ 2 ^ i

private theorem K_two : (2 : K) = 0 := CharP.cast_eq_zero K 2

private theorem K_pow_card (a : K) : a ^ 2 ^ 64 = a := by
  have h := FiniteField.pow_card a
  simp only [BF64.card_bf64] at h
  exact h

/-- `Tr(w² + w) = 0`: the sum telescopes to `w^(2^64) + w`. -/
theorem trK_sq_add (w : K) : trK (w ^ 2 + w) = 0 := by
  have hf : ∀ i : ℕ, (w ^ 2 + w) ^ 2 ^ i = w ^ 2 ^ (i + 1) - w ^ 2 ^ i := by
    intro i
    rw [add_pow_char_pow, ← pow_mul, ← pow_succ', CharTwo.sub_eq_add]
  rw [trK, Finset.sum_congr rfl fun i _ ↦ hf i, Finset.sum_range_sub (fun i ↦ w ^ 2 ^ i) 64,
    K_pow_card, pow_zero, pow_one, sub_self]

/-- The trace along `n` squarings on machine words: `acc + Σ_{i < n} a^(2^i)`. -/
private def trChain : ℕ → FK → FK → FK
  | 0, _, acc => acc
  | n + 1, a, acc => trChain n (a * a) (acc + a)

private theorem trChain_spec : ∀ (n : ℕ) (a acc : FK),
    FK.toBF64 (trChain n a acc) = FK.toBF64 acc + ∑ i ∈ Finset.range n, FK.toBF64 a ^ 2 ^ i
  | 0, _, _ => by simp [trChain]
  | n + 1, a, acc => by
    rw [trChain, trChain_spec n, FK.toBF64_add, FK.toBF64_mul, Finset.sum_range_succ']
    have e : ∀ i ∈ Finset.range n,
        (FK.toBF64 a * FK.toBF64 a) ^ 2 ^ i = FK.toBF64 a ^ 2 ^ (i + 1) := fun i _ ↦ by
      rw [← sq, ← pow_mul, pow_succ']
    rw [Finset.sum_congr rfl e]
    ring

/-- `1/x² = 0xc00000000000000b` on machine words. -/
private def cFK : FK := ⟨0xc00000000000000b⟩

private theorem hx : FK.toBF64 FK.x = g := rfl

/-- Kernel check: `c · x² = 1`. -/
private theorem cFK_mul : cFK * (FK.x * FK.x) = 1 := by decide +kernel

/-- `trChain` on the words as natural numbers (GOLF3: the kernel computes `ℕ`'s operations natively). -/
private def trN : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | n + 1, a, acc => trN n (FK.sqN a) (acc ^^^ a)

private theorem trChain_toNat : ∀ (n : ℕ) (a acc : FK),
    (trChain n a acc).val.toNat = trN n a.val.toNat acc.val.toNat
  | 0, _, _ => rfl
  | n + 1, a, acc => by rw [trChain, trN, trChain_toNat n, FK.mul_self_toNat, FK.add_toNat]

/-- Kernel check: `Tr(c) = 1` along 64 squarings. -/
private theorem cFK_tr : trChain 64 cFK 0 = 1 := by
  rw [FK.eq_iff_toNat, trChain_toNat]; decide +kernel

/-- `c = 1/x²` in `K`. -/
private theorem c_mul : FK.toBF64 cFK * (g * g) = 1 := by
  rw [← hx, ← FK.toBF64_mul, ← FK.toBF64_mul, cFK_mul, FK.toBF64_one]

/-- `Tr(1/x²) = 1`. -/
theorem trK_c : trK (FK.toBF64 cFK) = 1 := by
  have h := trChain_spec 64 cFK 0
  rw [FK.toBF64_zero, zero_add] at h
  rw [trK, ← h, cFK_tr, FK.toBF64_one]

/-- **`X² + xX + 1` has no root in `K`** (in Mathlib's form `r² ≠ 1 + x·r`). -/
theorem no_root (r : K) : r ^ 2 ≠ 1 + g * r := by
  intro h
  set c := FK.toBF64 cFK
  have hc := c_mul
  have hw : (r * g * c) ^ 2 + r * g * c = c := by
    linear_combination (g ^ 2 * c ^ 2) * h + (c * (1 + g * r)) * hc + (g * r * c) * K_two
  have := trK_sq_add (r * g * c)
  rw [hw, trK_c] at this
  exact one_ne_zero this

instance fact_no_root : Fact (∀ r : K, r ^ 2 ≠ 1 + g * r) := ⟨no_root⟩

/-! ## `E2` -/

/-- **`E2 = K[X]/(X² + xX + 1)` = GF(2^128)**: `re + im·X`. -/
abbrev E2 : Type := Quad K g

/-- `E2` is a field. -/
example : Field E2 := inferInstance

theorem card_E2 : Fintype.card E2 = 2 ^ 128 := by
  rw [Quad.card_quad, BF64.card_bf64]
  norm_num

/-! ## `Quad Ext3` -/

/-- **`Quad Ext3 = E3[X]/(X² + xX + 1)`**, a commutative ring (no field proof is used). -/
abbrev E6 : Type := Quad E (ofK g)

/-- `E2 → Quad Ext3`, coefficientwise. -/
def e2ToE6 : E2 →+* E6 := Quad.map (algebraMap K E) (ofK g) rfl

theorem e2ToE6_injective : Function.Injective e2ToE6 := by
  intro z w h
  have h0 := congrArg QuadraticAlgebra.re h
  have h1 := congrArg QuadraticAlgebra.im h
  simp only [e2ToE6] at h0 h1
  exact QuadraticAlgebra.ext ((algebraMap K E).injective h0) ((algebraMap K E).injective h1)

end LeanVM.Parameters
