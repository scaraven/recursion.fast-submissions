-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/LayoutStack.lean` (formal rev 40f877dc) as `LvmLayoutStack` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.LayoutStack

  The verifier's `stack_offsets` and `Placement::stack_point` as statements about sorted
  lists and cube points: the order is the stable sort by size, the offsets are prefix sums of the
  heights in that order, and a placed point is the claim's point between the bits of its index.
-/


import LvmLayoutArith

-- (GOLF2: 12 declarations that `certified` does not use moved verbatim to `LvmMPMidTOff`, outside its import closure.)

/-!
# `stack_offsets` and `stack_point`

Facts about the transcriptions of `crates/verifier/src/multilinear.rs:114-148` at leanVM `40f877dc`
(`Placement`, `stack_offsets`, `selector_point`), in the form the layout correspondence uses:

* `stackOffsets_eq`: the order of `stack_offsets`, sorted by "larger first, ties by index", is
  the *stable* sort of the indices by size (`mergeSort_range_stackLe`), and the offsets are the
  prefix sums of the heights in that order (`placeFold_getElem?`, `placeFold_snd`);
* `log2Ceil_eq_clog`: `log2_ceil` is `Nat.clog 2`;
* `stackPoint_aligned`, `stackPoint_strided`: a placed point is the claim's point followed by the
  bits of the index above the window, the slot bits below the window for a strided placement.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier List

section

/-! ## The order of `stack_offsets` -/

/-! ## `log2_ceil` -/

/-- `log2_ceil` is the ceiling logarithm. -/
theorem log2Ceil_eq_clog (t : ℕ) : log2Ceil t = Nat.clog 2 t := by
  rcases Nat.lt_or_ge t 2 with ht | ht
  · interval_cases t <;> rfl
  · have hm : t - 1 ≠ 0 := by omega
    have hL : log2Ceil t = Nat.log2 (t - 1) + 1 := by
      simp [log2Ceil, bitLength, hm]
    have hup : t - 1 < 2 ^ (Nat.log2 (t - 1) + 1) := Nat.lt_log2_self
    have hlo : 2 ^ Nat.log2 (t - 1) ≤ t - 1 := Nat.log2_self_le hm
    rw [hL]
    apply le_antisymm
    · by_contra h
      have h' : Nat.clog 2 t ≤ Nat.log2 (t - 1) := by omega
      rw [Nat.clog_le_iff_le_pow (by norm_num)] at h'
      omega
    · rw [Nat.clog_le_iff_le_pow (by norm_num)]
      omega

/-! ## Placed points -/

/-- Dropping the low `v` coordinates of the cube point of `n` leaves the cube point of
`n / 2 ^ v`. -/
theorem drop_boolPoint (μ v n : ℕ) :
    (boolPoint μ n).drop v = boolPoint (μ - v) (n / 2 ^ v) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_drop, getElem_boolPoint, Nat.testBit_div_two_pow]
  rw [Nat.add_comm]

/-- The low `k` coordinates of the cube point of `n`. -/
theorem take_boolPoint (μ k n : ℕ) (hk : k ≤ μ) :
    (boolPoint μ n).take k = boolPoint k n := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take, getElem_boolPoint]

/-- The cube point of `n` on `k` coordinates depends only on `n % 2 ^ k`. -/
theorem boolPoint_mod (k n : ℕ) : boolPoint k (n % 2 ^ k) = boolPoint k n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [getElem_boolPoint, Nat.testBit_mod_two_pow]
  simp only [length_boolPoint] at h1
  simp [h1]

/-- The cube point of `x + 2 ^ a · m`, for `x < 2 ^ a`: the bits of `x`, then those of `m`. -/
theorem boolPoint_add_two_pow_mul (a b x m : ℕ) (hx : x < 2 ^ a) :
    boolPoint (a + b) (x + 2 ^ a * m) = boolPoint a x ++ boolPoint b m := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [length_boolPoint] at h1
  rw [getElem_boolPoint, List.getElem_append]
  rw [show x + 2 ^ a * m = 2 ^ a * m + x by ring, Nat.testBit_two_pow_mul_add m hx]
  by_cases hi : i < a
  · simp only [hi, ↓reduceIte, ↓reduceDIte, length_boolPoint, getElem_boolPoint]
  · simp only [hi, ↓reduceIte, ↓reduceDIte, length_boolPoint, getElem_boolPoint]

end
end LeanVM.Protocol.EndToEnd.Front
