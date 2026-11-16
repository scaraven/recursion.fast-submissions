-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Complete/Tables.lean` (formal rev 40f877dc) as `LvmEqLemmas` for lvm (WP-2).
/-
  LeanVM.Protocol.Whir.Complete.Tables

  Value tables on the cube and the verifier's list arithmetic on them: folding, multilinear
  evaluation, the equality kernel, the sumcheck round polynomial of a product of two multilinear
  tables, and the functions that are their own multilinear extensions.
-/


import LvmVCore
import LvmClaims

-- (GOLF2: 46 declarations that `certified` does not use moved verbatim to `LvmE2QNodeChkGOff`, outside its import closure.)

/-!
# Tables on the cube

The honest WHIR prover holds two value tables on the cube `{0,1}^m` (index `i` is the cube point
`boolPoint m i`, bit `0` first): the message `g` and the weight `W` of the running claim
`Σ_x W(x)·g(x)`. Everything the verifier computes about them is a function of
`LeanVM.Protocol.Verifier` on lists, and this module proves what those functions compute.

* `foldPairs r t` fixes the first coordinate at `r`; `foldAll t r` fixes the first `|r|`
  coordinates (`getD_foldAll`: entry `x` is `Σ_j eq(j, r)·t[j + 2^|r|·x]`), so `multilinearEval t p`
  is the multilinear extension `Σ_i t[i]·eq(i, p)` (`multilinearEval_eq_sum`).
* `getD_eqKernel`: entry `j` of `eqKernel p` is `eq(j, p)`.
* `roundC0 W g`, `roundC2 W g`: the constant and quadratic coefficients of the round polynomial
  `h(X) = Σ_x (W(0,x)(1+X) + W(1,x)X)·(g(0,x)(1+X) + g(1,x)X)`, the two scalars the verifier
  reads; `roundQuad claim W g` is the polynomial the verifier builds from them
  (`sumcheckRoundPoly 3 claim none`). `polyEval_roundQuad`: when `claim = Σ W·g`, its value at `c`
  is the sum of the folded product, `Σ (foldPairs c W)·(foldPairs c g)`.
* `axpy s W T = W + s·T`: every one of these functions is linear in the weight table.
* `IsMultilinearFn` (`LeanVM.Protocol.EndToEnd.Claims`) holds for products of affine factors
  (`affProd`), hence for `eqEval z`, for linear combinations, and for a function of a rotated
  point (`isMultilinearFn_rotate`). Such a function is the multilinear extension of its table
  (`multilinearEval_tableOf`).

All of it is characteristic two: `E` has `1 + 1 = 0`.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd Finset

section

/-- `2 = 0` in `E`. -/
theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

/-- `1 + 1 = 0` in `E`. -/
theorem one_add_one_E : (1 : E) + 1 = 0 := by
  rw [one_add_one_eq_two, two_eq_zero_E]

/-! ## Folds as sums -/

theorem foldl_add_eq (l : List E) (a : E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem foldl_mul_eq (l : List E) (a : E) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

@[simp] theorem dot_nil_left (u : List E) : dot [] u = 0 := by simp [dot]

@[simp] theorem dot_nil_right (t : List E) : dot t [] = 0 := by simp [dot]

theorem dot_cons (a x : E) (t u : List E) : dot (a :: t) (x :: u) = a * x + dot t u := by
  simp only [dot, List.zipWith_cons_cons, foldl_add_eq, List.sum_cons, zero_add]

theorem sumE_eq (l : List E) : sumE l = l.sum := by
  rw [sumE, foldl_add_eq, zero_add]

/-- `dot` of two lists of equal length as a sum over the indices. -/
theorem dot_eq_sum : ∀ (t u : List E), t.length = u.length →
    dot t u = ∑ i ∈ range t.length, t.getD i 0 * u.getD i 0
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: t, x :: u, h => by
    rw [dot_cons, dot_eq_sum t u (by simpa using h), List.length_cons, sum_range_succ']
    simp [add_comm]

@[simp] theorem eqEval_nil_left (b : List E) : eqEval [] b = 1 := by simp [eqEval]

@[simp] theorem eqEval_nil_right (a : List E) : eqEval a [] = 1 := by simp [eqEval]

/-- The equality kernel peels its first coordinate. -/
theorem eqEval_cons (x z : E) (a b : List E) :
    eqEval (x :: a) (z :: b) = (1 + x + z) * eqEval a b := by
  simp only [eqEval, List.zipWith_cons_cons, foldl_mul_eq, List.prod_cons, one_mul]

/-- The equality kernel is symmetric. -/
theorem eqEval_comm : ∀ (a b : List E), eqEval a b = eqEval b a
  | [], b => by simp
  | _ :: _, [] => by simp
  | x :: a, z :: b => by rw [eqEval_cons, eqEval_cons, eqEval_comm a b]; ring

/-- The equality kernel of concatenated points is the product. -/
theorem eqEval_append : ∀ (a₁ a₂ b₁ b₂ : List E), a₁.length = b₁.length →
    eqEval (a₁ ++ a₂) (b₁ ++ b₂) = eqEval a₁ b₁ * eqEval a₂ b₂
  | [], _, [], _, _ => by simp
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | x :: a₁, a₂, z :: b₁, b₂, h => by
    simp only [List.cons_append, eqEval_cons, eqEval_append a₁ a₂ b₁ b₂ (by simpa using h)]
    ring

/-! ## Cube points -/

theorem length_boolPoint (m x : ℕ) : (boolPoint m x).length = m := by simp [boolPoint]

/-- The first coordinate of a cube point is its low bit. -/
theorem boolPoint_succ (m x : ℕ) :
    boolPoint (m + 1) x = (if x.testBit 0 then 1 else 0) :: boolPoint m (x / 2) := by
  simp only [boolPoint, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp [Nat.testBit_div_two]

theorem boolPoint_two_mul (m j : ℕ) : boolPoint (m + 1) (2 * j) = 0 :: boolPoint m j := by
  rw [boolPoint_succ]
  simp [Nat.testBit_zero, Nat.mul_div_cancel_left j (by norm_num : 0 < 2)]

theorem boolPoint_two_mul_add_one (m j : ℕ) :
    boolPoint (m + 1) (2 * j + 1) = 1 :: boolPoint m j := by
  rw [boolPoint_succ]
  have : (2 * j + 1) / 2 = j := by omega
  simp [Nat.testBit_zero, this]

@[simp] theorem boolPoint_zero (x : ℕ) : boolPoint 0 x = [] := rfl

/-! ## Sums over the cube -/

theorem sum_range_two_mul (f : ℕ → E) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-! ## Folding -/

/-- Fix the first `|r|` coordinates of a table at `r`, one at a time. -/
def foldAll (t r : List E) : List E := r.foldl (fun cur c ↦ foldPairs c cur) t

@[simp] theorem foldAll_nil (t : List E) : foldAll t [] = t := rfl

/-! ## The equality kernel -/

private theorem eqKernel_general : ∀ (p out : List E),
    (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).length =
      out.length * 2 ^ p.length ∧
    ∀ i j, i < out.length → j < 2 ^ p.length →
      (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).getD
        (i + out.length * j) 0 = out.getD i 0 * eqEval (boolPoint p.length j) p
  | [], out => by
    refine ⟨by simp, fun i j hi hj ↦ ?_⟩
    obtain rfl : j = 0 := by simpa using hj
    simp
  | r :: p, out => by
    obtain ⟨hl, hg⟩ := eqKernel_general p (out.map (· * (1 + r)) ++ out.map (· * r))
    simp only [List.length_append, List.length_map] at hl hg
    refine ⟨by rw [List.foldl_cons, hl, List.length_cons, pow_succ]; ring, fun i j hi hj ↦ ?_⟩
    rw [List.foldl_cons]
    rw [List.length_cons, pow_succ] at hj
    rcases Nat.even_or_odd' j with ⟨j', rfl | rfl⟩
    · have := hg i j' (by (clear * - hi; omega)) (by (clear * - hj; omega))
      rw [show i + out.length * (2 * j') = i + (out.length + out.length) * j' by ring, this,
        List.length_cons, boolPoint_two_mul, eqEval_cons]
      rw [List.getD_append _ _ _ _ (by simpa using hi)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
      simp; ring
    · have := hg (i + out.length) j' (by (clear * - hi; omega)) (by (clear * - hj; omega))
      rw [show i + out.length * (2 * j' + 1) = i + out.length + (out.length + out.length) * j' by
        ring, this, List.length_cons, boolPoint_two_mul_add_one, eqEval_cons]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_map, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem hi]
      simp only [Option.map_some, Option.getD_some]
      rw [one_add_one_E, zero_add]; ring

/-- The equality kernel has `2^|p|` entries. -/
theorem length_eqKernel (p : List E) : (eqKernel p).length = 2 ^ p.length := by
  have := (eqKernel_general p [1]).1
  simp only [List.length_singleton, one_mul] at this
  exact this

/-- Entry `j` of the equality kernel is `eq(j, p)`. -/
theorem getD_eqKernel (p : List E) (j : ℕ) (hj : j < 2 ^ p.length) :
    (eqKernel p).getD j 0 = eqEval (boolPoint p.length j) p := by
  have := (eqKernel_general p [1]).2 0 j (by simp) hj
  simpa [eqKernel] using this

/-! ## The round polynomial -/

/-! ## Linearity in the weight -/

/-! ## Tables of functions -/

/-- The table of a function on the cube `{0,1}^m`. -/
def tableOf (m : ℕ) (w : List E → E) : List E := (List.range (2 ^ m)).map fun i ↦ w (boolPoint m i)

@[simp] theorem length_tableOf (m : ℕ) (w : List E → E) : (tableOf m w).length = 2 ^ m := by
  simp [tableOf]

/-! ## Multilinear functions -/

/-! ## Rotating the coordinates -/

end
end LeanVM.Protocol.Whir.Complete
