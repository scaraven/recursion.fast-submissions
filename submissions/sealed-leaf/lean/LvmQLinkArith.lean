import LvmDecideV0
import LvmQSumcheck

-- (GOLF2: 29 declarations that `certified` does not use moved verbatim to `LvmQTypedHarZOff`, outside its import closure.)

/-!
# QA1 links: closed forms of the `CH` and `KS` link checks of `M3.ofParts` (the links of the former `M3.v0`) (WP-11b QA1)

`F`'s link functions (`LvmDecideV0`: `chShiftTarget0`, `chSc2Target0`, `chLink0`, `ksLink0`, WP-15a's
links, reviewed correct by WP-8) read `eq` tables as arrays (`eqKernelA`) and the shift kernel as
an `O(n²)` sum (`shiftEval`); `ksLink0`'s `contShift` sums over ≈ 9 k rows of two `2^ksLog` tables (`2^14` at `P20`, KS14).
The circuit evaluates the same values in `O(log)` rows; this module proves the forms equal:

* `eqKernel_getD`, `eqKernelA_eq`: `eqKernel a` at `z` is WP-10's `eqW a z` (first coordinate the
  low bit); `eqKernelA a = (eqKernel a).toArray`.
* `padConst_eq`, `chShiftTarget0_eq`: `C(1 + eq(ρ, 1ⁿ))` from six `eq` entries.
* `shiftEval_cons`: the shift kernel's low-bit recursion `S(x₀x, y₀y) = (1+x₀)y₀·eq(x,y) + x₀(1+y₀)·S(x,y)`
  (FR `FRShift.shiftPair`'s recursion, rf-k flock-recursive `FRShift.lean@8bff272b`; proved here for
  `F`'s index form directly).
* `chLink_sum_eq`: `Σ_q W̃(μ, q)·yS_q = α·Σ_{q<56} eq(ζ, q+8)·yS_q + β·Σ_{q<8} eq(ζ, q)·yS_{q+56}`,
  `α = Σ_m eq(μ,m)eq(λ,m)`, `β = Σ_m eq(μ,m)eq(λ,m+1)`.
* `contShift_eq`: `contShift` = `pre(B−1) + pre(K+30) + pre(K−1)` with `K = 2^r + 400`,
  `pre(H) = Σ_{k<H} eq(ρ', k)·eq(ρ, k+1)` in closed form by a low-bit recursion with three values
  per level (`preCF`, **`preCF_eq`**).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-! ## `eq` tables -/

/-- One doubling of `eqKernel`. -/
def eqStep (out : List FE) (r : FE) : List FE := out.map (· * (1 + r)) ++ out.map (· * r)

theorem eqKernel_foldl (a : List FE) : eqKernel a = a.foldl eqStep [1] := rfl

theorem sub_eq_add' (a b : FE) : a - b = a + b := CharTwo.sub_eq_add a b

theorem eqStep_length (out : List FE) (r : FE) : (eqStep out r).length = 2 * out.length := by
  simp [eqStep]; omega

theorem eqStep_getD (out : List FE) (r : FE) {w : Nat} (hw : w < 2 * out.length) :
    (eqStep out r).getD w 0 =
      if w < out.length then out.getD w 0 * (1 + r) else out.getD (w - out.length) 0 * r := by
  unfold eqStep
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; (clear * - h; omega))]
    simp only [List.length_map, List.getElem?_map]
    rw [List.getD_eq_getElem?_getD]
    cases out[w - out.length]? <;> simp

theorem foldl_eqStep_length : ∀ (a acc : List FE), (a.foldl eqStep acc).length = acc.length * 2 ^ a.length
  | [], acc => by simp
  | r :: rs, acc => by
    rw [List.foldl_cons, foldl_eqStep_length rs, eqStep_length, List.length_cons, pow_succ]; ring

theorem foldl_eqStep_getD : ∀ (a acc : List FE) (z : Nat), z < acc.length * 2 ^ a.length →
    (a.foldl eqStep acc).getD z 0 = acc.getD (z % acc.length) 0 * eqW a (z / acc.length)
  | [], acc, z, hz => by
    simp only [List.foldl_nil, List.length_nil, pow_zero, Nat.mul_one] at hz ⊢
    rw [Nat.mod_eq_of_lt hz]; simp [eqW]
  | r :: rs, acc, z, hz => by
    have hN : 0 < acc.length := by
      rcases Nat.eq_zero_or_pos acc.length with h | h
      · rw [h] at hz; simp at hz
      · exact h
    rw [List.foldl_cons, foldl_eqStep_getD rs (eqStep acc r) z
      (by rw [eqStep_length]; simp [pow_succ] at hz ⊢; nlinarith), eqStep_length]
    have hw : z % (2 * acc.length) < 2 * acc.length := Nat.mod_lt _ (by (clear * - hN; omega))
    rw [eqStep_getD acc r hw, eqW]
    have hdiv : z / (2 * acc.length) = z / acc.length / 2 := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [hdiv]
    have key : z % (2 * acc.length) = z % acc.length + acc.length * (z / acc.length % 2) := by
      rw [Nat.mul_comm 2 acc.length, Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one (z / acc.length) with h0 | h1
    · rw [key, h0, Nat.mul_zero, Nat.add_zero, if_pos (Nat.mod_lt _ hN), if_neg (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))]
      rw [sub_eq_add']; ring
    · rw [key, h1, Nat.mul_one, if_neg (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), if_pos rfl, Nat.add_sub_cancel]
      ring

/-- **`eqKernel a` at `z` is `eq(a, z)`** (`eqW`, first coordinate the low bit). -/
theorem eqKernel_getD (a : List FE) {z : Nat} (hz : z < 2 ^ a.length) :
    (eqKernel a).getD z 0 = eqW a z := by
  rw [eqKernel_foldl, foldl_eqStep_getD a [1] z (by simpa using hz)]
  simp [Nat.mod_one]

theorem eqKernel_length_lk (a : List FE) : (eqKernel a).length = 2 ^ a.length := by
  rw [eqKernel_foldl, foldl_eqStep_length]; simp

theorem eqKernelA_foldl : ∀ (a acc : List FE),
    a.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) acc.toArray =
      (a.foldl eqStep acc).toArray
  | [], acc => rfl
  | r :: rs, acc => by
    rw [List.foldl_cons, List.foldl_cons, ← eqKernelA_foldl rs]
    congr 1
    simp [eqStep]

theorem eqKernelA_eq (a : List FE) : eqKernelA a = (eqKernel a).toArray :=
  eqKernelA_foldl a [1]

theorem arr_getD (l : List FE) (i : Nat) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- An `eqKernelA` entry. -/
theorem eqKernelA_getD (a : List FE) {z : Nat} (hz : z < 2 ^ a.length) :
    (eqKernelA a).getD z 0 = eqW a z := by
  rw [eqKernelA_eq, arr_getD, eqKernel_getD a hz]

/-! ## List sums and products as `Finset` sums -/

theorem list_sum_range (f : Nat → FE) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]
    simp

theorem foldl_mul (a : FE) (l : List FE) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, mul_assoc]

/-- `eqEval` of two points of length `n`: `Π (1 + x_i + y_i)`. -/
theorem eqEval_cons (x0 y0 : FE) (x y : List FE) : eqEval (x0 :: x) (y0 :: y) = (1 + x0 + y0) * eqEval x y := by
  unfold eqEval
  rw [List.zipWith_cons_cons, List.foldl_cons, foldl_mul, foldl_mul]
  ring

/-! ## The `CH` link -/

/-! ## The `KS` link: interval shift sums in closed form -/

end Lvm.Q1
