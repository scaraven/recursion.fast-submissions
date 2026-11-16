-- New for lvm2 S1 (E2-F, E2F-V): field-generic lemmas about `LvmE2VBase` (the `PolyLE` API, `polyEvalF`
-- as a polynomial, `sumF`, the round splits), the twins of `LvmPolyLE`'s and `LvmKeccakRounds`' `E3`
-- lemmas, and the characteristic of `E2`.
import LvmE2VBase
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Lemmas on the front's base over a field `F`

* `PolyLEF.const`, `id`, `affine`, `mono`, `congr`, `add`, `mul`, `const_mul` (`LvmPolyLE`'s rules);
* `sumF_eq_sum`, `polyEvalF_eq_sum`, `polyEvalF_zero_cons`, `polyEvalF_one`;
* `listPolyF` (a message as a polynomial), `eval_listPolyF`, `natDegree_listPolyF`;
* `split_noneF`, `split_someF`: the messages the program builds pass the round's check
  (characteristic two);
* `charP_E2`: `E2` has characteristic two (from `K`).
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters Polynomial

section

variable {F : Type} [Field F]

/-! ## Polynomial functions of bounded degree -/

namespace PolyLEF

variable {d d' : ℕ} {f g : F → F}

/-- A constant is a polynomial of every degree. -/
theorem const (d : ℕ) (a : F) : PolyLEF d fun _ ↦ a :=
  ⟨C a, by simp, fun x ↦ by simp⟩

/-- The identity has degree one. -/
theorem id : PolyLEF 1 fun x : F ↦ x :=
  ⟨X, natDegree_X_le, fun x ↦ by simp⟩

/-- An affine function has degree one. -/
theorem affine (a b : F) : PolyLEF 1 fun x ↦ a + b * x :=
  ⟨C a + C b * X, natDegree_add_le_of_degree_le (by simp)
    ((natDegree_C_mul_le _ _).trans natDegree_X_le), fun x ↦ by simp⟩

/-- A larger degree bound. -/
theorem mono (h : PolyLEF d f) (hd : d ≤ d') : PolyLEF d' f := by
  obtain ⟨P, hP, hf⟩ := h
  exact ⟨P, hP.trans hd, hf⟩

/-- A function equal to a polynomial function is one. -/
theorem congr (h : PolyLEF d f) (hfg : ∀ x, f x = g x) : PolyLEF d g := by
  obtain ⟨P, hP, hf⟩ := h
  exact ⟨P, hP, fun x ↦ (hfg x).symm.trans (hf x)⟩

/-- Sums. -/
theorem add (hf : PolyLEF d f) (hg : PolyLEF d g) : PolyLEF d fun x ↦ f x + g x := by
  obtain ⟨P, hP, hfP⟩ := hf
  obtain ⟨Q, hQ, hgQ⟩ := hg
  exact ⟨P + Q, natDegree_add_le_of_degree_le hP hQ, fun x ↦ by simp [hfP, hgQ]⟩

/-- Products add degrees. -/
theorem mul (hf : PolyLEF d f) (hg : PolyLEF d' g) : PolyLEF (d + d') fun x ↦ f x * g x := by
  obtain ⟨P, hP, hfP⟩ := hf
  obtain ⟨Q, hQ, hgQ⟩ := hg
  exact ⟨P * Q, natDegree_mul_le_of_le hP hQ, fun x ↦ by simp [hfP, hgQ]⟩

/-- A constant multiple. -/
theorem const_mul (hf : PolyLEF d f) (a : F) : PolyLEF d fun x ↦ a * f x :=
  ((mul (const 0 a) hf).mono (by omega)).congr fun _ ↦ rfl

end PolyLEF

/-! ## Coefficient lists -/

/-- `sumF` is the list's sum. -/
theorem sumF_eq_sum (l : List F) : sumF l = l.sum := by
  unfold sumF
  suffices h : ∀ a : F, l.foldl (· + ·) a = a + l.sum by simpa using h 0
  induction l with
  | nil => simp
  | cons x l ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-- `polyEvalF` is the sum of the coefficients times the powers. -/
theorem polyEvalF_eq_sum : ∀ (l : List F) (x : F),
    polyEvalF l x = ∑ i ∈ Finset.range l.length, l.getD i 0 * x ^ i
  | [], x => by simp [polyEvalF]
  | c :: l, x => by
    have h : polyEvalF (c :: l) x = polyEvalF l x * x + c := rfl
    rw [h, polyEvalF_eq_sum l x, List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl fun i _ ↦ by
        rw [List.getD_cons_succ, pow_succ]; ring
    · rw [List.getD_cons_zero, pow_zero, mul_one]

/-- The value of a coefficient list at `0` is its first coefficient. -/
theorem polyEvalF_zero_cons (c : F) (l : List F) : polyEvalF (c :: l) 0 = c := by
  show polyEvalF l 0 * 0 + c = c
  simp

/-- The value of a coefficient list at `1` is the sum of its coefficients. -/
theorem polyEvalF_one : ∀ l : List F, polyEvalF l 1 = l.sum
  | [] => rfl
  | c :: l => by
    show polyEvalF l 1 * 1 + c = _
    rw [mul_one, polyEvalF_one l, List.sum_cons, add_comm]

/-- A message as a polynomial. -/
noncomputable def listPolyF (l : List F) : F[X] :=
  ∑ c ∈ Finset.range l.length, C (l.getD c 0) * X ^ c

theorem eval_listPolyF (l : List F) (x : F) : (listPolyF l).eval x = polyEvalF l x := by
  rw [polyEvalF_eq_sum, listPolyF, eval_finsetSum]
  simp

theorem natDegree_listPolyF (l : List F) : (listPolyF l).natDegree ≤ l.length - 1 := by
  unfold listPolyF
  refine natDegree_sum_le_of_forall_le _ _ fun c hc ↦ ?_
  have := Finset.mem_range.1 hc
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-! ## The round splits (characteristic two) -/

variable [CharP F 2]

/-- A plain round's message `c₀, claim + Σ tail, tail` passes the check. -/
theorem split_noneF (c0 claim : F) (tail : List F) :
    RoundSplitF none claim (polyEvalF (c0 :: (claim + sumF tail) :: tail) 0)
      (polyEvalF (c0 :: (claim + sumF tail) :: tail) 1) := by
  rw [RoundSplitF, polyEvalF_zero_cons, polyEvalF_one, sumF_eq_sum]
  simp only [List.sum_cons]
  linear_combination (CharTwo.two_eq_zero (R := F)) * (c0 + tail.sum)

/-- An equality-mode round's message `claim + r · Σ tail, tail` passes the check. -/
theorem split_someF (r claim : F) (tail : List F) :
    RoundSplitF (some r) claim (polyEvalF ((claim + r * sumF tail) :: tail) 0)
      (polyEvalF ((claim + r * sumF tail) :: tail) 1) := by
  rw [RoundSplitF, polyEvalF_zero_cons, polyEvalF_one, sumF_eq_sum]
  simp only [List.sum_cons]
  linear_combination (CharTwo.two_eq_zero (R := F)) * (r * claim + r * r * tail.sum + r * tail.sum)

end

/-! ## `E2` -/

/-- `E2` has characteristic two, as `K` (the injective `algebraMap K E2`). -/
instance charP_E2 : CharP E2 2 := charP_of_injective_algebraMap (algebraMap K E2).injective 2

end Lvm.E2V
