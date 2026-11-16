-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToCompPoly/AmbientStacking.lean` (formal rev 40f877dc) as `LvmCpAmbientStacking` for lvm (WP-2).
/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/

/-
  LeanVM.Protocol.ToCompPoly.AmbientStacking

  The multilinear extension of an aligned stack at an arbitrary point, for any pad. Candidate
  for CompPoly.
-/
import LvmCpMultilinear

-- ===== merged from `LvmCpStacking` (GOLF module merge: `LvmCpStacking.lean` is now a stub importing `LvmCpAmbientStacking`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToCompPoly/Stacking.lean` (formal rev 40f877dc) as `LvmCpStacking` for lvm (WP-2).
/-
  LeanVM.Protocol.ToCompPoly.Stacking

  Aligned stacking of hypercube tables of different heights into one table, and the selection
  identity: the stack at a point whose high coordinates are a block's selector bits is that
  block at the low coordinates. Candidate for CompPoly.
-/

/-!
# Aligned stacking

A `Blocks` is a list of sizes, largest first: block `b` has `2 ^ size b` entries. Laid end to
end in that order, each block starts at an offset that is a multiple of its own height
(`pow_size_dvd_offset`), so it occupies a subcube of any table tall enough to hold them all:
the subcube whose high coordinates are the bits of `selector b = offset b / 2 ^ size b`. The
layout knows sizes only. The tables are a separate argument, `t : B.Tables R`, one table per
block over any commutative ring, so one layout serves tables over different rings.

* `stackAt t μ pad` lays the tables out on `μ` variables and fills the rest with `pad`.
* `unstack hμ q b` reads block `b` off any table `q` of `μ` variables, stack or not.
* `extendPoint hμ b z` lifts a point of block `b` to the point `(z, selector bits)` of the stack;
  `lowPoint` and `highPoint` split a point of the stack the same way.
* The selection identity: `stack_eval` for a stack, and `unstack_eval₂`, `stack_eval₂` for any
  table or a stack when the point lies in another ring than the entries.
  `unstack_eval₂_eq_sumCube` writes it as a sum over the cube against a Lagrange basis.
* `map_stackAt`, `unstack_map`: mapping the entries commutes with stacking and reading.
* `total_eq_sum`, `prod_stackAt`: the total height is the sum of the blocks' heights, and the
  product of a stack's cells is the product of its blocks' cells times the pad once per cell no
  block covers.

Candidate for CompPoly, beside `CompPoly.Multilinear`: every object here is a CompPoly table or
its evaluation. The request it answers is tracked upstream as
[ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900). Nothing here transcribes a
source.

Derived from Verified-zkEVM/leanth `leanth-project` at 23929f8c, by Aristotle (Harmonic),
Stefano Rocca and Elias Judin: the layout is `ProofSystem/Stacking.lean:48` (`AlignedLayout`),
alignment is `pow_height_dvd_offset` (:388), the window lemmas are :397 and :409, the selection
identity is `eval_MLE_stack_block` (:603), and reading a block is `unstack` (:724-777), restated
little-endian. The proofs are new.

## Wrong readings excluded

* Alignment is a theorem of the descending order, not a hypothesis: sizes 2, 1, 0 in that order
  are aligned, in any other order they are not.
* The pad is a parameter, and no selection identity depends on it.
* `stackAt` is total: when the tables do not fit on `μ` variables it truncates. Every statement
  that needs the fit takes `B.total ≤ 2 ^ μ`.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

section

variable {R : Type*} [CommRing R]

/-- The sizes of the blocks of an aligned layout: `n` blocks, block `b` on `size b` variables,
largest first. -/
structure Blocks where
  /-- The number of blocks. -/
  n : ℕ
  /-- The number of variables of each block; its height is `2 ^ size b`. -/
  size : Fin n → ℕ
  /-- Largest first. -/
  descending : Antitone size

namespace Blocks

variable (B : Blocks)

/-- One table per block, over the ring `R`. -/
abbrev Tables (R : Type*) : Type _ := (b : Fin B.n) → CMlPolynomialEval R (B.size b)

/-! ## Offsets -/

/-- The sum of the heights of the first `k` blocks. -/
def offsetNat (k : ℕ) : ℕ :=
  ∑ c ∈ Finset.range k, if h : c < B.n then 2 ^ B.size ⟨c, h⟩ else 0

/-- The offset of block `b`: the sum of the heights of the blocks before it. -/
def offset (b : Fin B.n) : ℕ := B.offsetNat b.val

/-- The total height of the blocks. -/
def total : ℕ := B.offsetNat B.n

/-- The total height is the sum of the blocks' heights. -/
theorem total_eq_sum : B.total = ∑ b : Fin B.n, 2 ^ B.size b := by
  rw [total, offsetNat, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun b _ ↦ dite_eq_left b.isLt

theorem offsetNat_succ (k : ℕ) (hk : k < B.n) :
    B.offsetNat (k + 1) = B.offsetNat k + 2 ^ B.size ⟨k, hk⟩ := by
  simp [offsetNat, Finset.sum_range_succ, hk]

theorem offsetNat_mono : Monotone B.offsetNat := fun _ _ hab ↦
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

/-- Windows of distinct blocks are disjoint and in order. -/
theorem offset_add_pow_le_offset {b c : Fin B.n} (hbc : b < c) :
    B.offset b + 2 ^ B.size b ≤ B.offset c := by
  rw [offset, offset, ← B.offsetNat_succ b.val b.isLt]
  exact B.offsetNat_mono hbc

/-- Every window fits below the total. -/
theorem offset_add_pow_le_total (b : Fin B.n) : B.offset b + 2 ^ B.size b ≤ B.total := by
  rw [offset, total, ← B.offsetNat_succ b.val b.isLt]
  exact B.offsetNat_mono b.isLt

/-- Alignment: the offset of a block is a multiple of its height, because every earlier block
is at least as large. -/
theorem pow_size_dvd_offset (b : Fin B.n) : 2 ^ B.size b ∣ B.offset b := by
  unfold offset offsetNat
  refine Finset.dvd_sum fun c hc ↦ ?_
  rw [Finset.mem_range] at hc
  have hcn : c < B.n := lt_trans hc b.isLt
  rw [dite_eq_left hcn]
  exact Nat.pow_dvd_pow 2 (B.descending (Fin.le_def.mpr (Nat.le_of_lt hc)))

/-- Index `x` lies in the window of block `b`. -/
abbrev InWindow (b : Fin B.n) (x : ℕ) : Prop :=
  B.offset b ≤ x ∧ x < B.offset b + 2 ^ B.size b

theorem inWindow_unique {b c : Fin B.n} {x : ℕ} (hb : B.InWindow b x) (hc : B.InWindow c x) :
    b = c := by
  rcases lt_trichotomy b c with h | h | h
  · exact absurd (lt_of_lt_of_le hb.2 (B.offset_add_pow_le_offset h)) (not_lt.mpr hc.1)
  · exact h
  · exact absurd (lt_of_lt_of_le hc.2 (B.offset_add_pow_le_offset h)) (not_lt.mpr hb.1)

/-- Every index below the total belongs to a block window: there are no internal gaps. -/
theorem exists_inWindow {x : ℕ} (hx : x < B.total) : ∃ b, B.InWindow b x := by
  by_contra h
  have hno : ∀ b : Fin B.n, ¬ B.InWindow b x := by simpa using h
  have hprefix : ∀ k, k ≤ B.n → B.offsetNat k ≤ x := by
    intro k hk
    induction k with
    | zero => simp [offsetNat]
    | succ k ih =>
      have hk' : k < B.n := by (clear * - hk; omega)
      have hp := ih (by (clear * - hk; omega))
      rw [B.offsetNat_succ k hk']
      have hn := hno ⟨k, hk'⟩
      change ¬ (B.offsetNat k ≤ x ∧ x < B.offsetNat k + 2 ^ B.size ⟨k, hk'⟩) at hn
      (clear * - hk' hp hn; omega)
  have := hprefix B.n le_rfl
  exact (not_lt_of_ge this) hx

/-- Alignment identifies window membership with the quotient selecting the high slice. -/
theorem inWindow_iff_div (b : Fin B.n) (x : ℕ) :
    B.InWindow b x ↔ x / 2 ^ B.size b = B.offset b / 2 ^ B.size b := by
  have ha := Nat.mul_div_cancel' (B.pow_size_dvd_offset b)
  rw [Nat.div_eq_iff (Nat.two_pow_pos (B.size b))]
  rw [Nat.mul_comm (B.offset b / 2 ^ B.size b), ha]
  have hp := Nat.two_pow_pos (B.size b)
  change (B.offset b ≤ x ∧ x < B.offset b + 2 ^ B.size b) ↔ _
  omega

/-! ## The stack -/

/-- The stack on `μ` variables: block `b`'s entries at its window, `pad` past the total. -/
def stackAt (t : B.Tables R) (μ : ℕ) (pad : R) : CMlPolynomialEval R μ :=
  Vector.ofFn fun x ↦
    if B.total ≤ x.val then pad
    else ∑ b : Fin B.n,
      if B.InWindow b x.val then ((t b)[x.val - B.offset b]?).getD 0 else 0

theorem stackAt_getElem_of_inWindow (t : B.Tables R) {μ : ℕ} (pad : R) {b : Fin B.n} {x : ℕ}
    (hx : x < 2 ^ μ) (h : B.InWindow b x) :
    (B.stackAt t μ pad)[x] = (t b)[x - B.offset b]'(by have := h.2; omega) := by
  simp only [stackAt, Vector.getElem_ofFn]
  rw [ite_eq_right (by have := B.offset_add_pow_le_total b; omega), Finset.sum_eq_single b]
  · rw [ite_eq_left h, Vector.getElem?_eq_getElem (by have := h.2; omega), Option.getD_some]
  · intro c _ hc
    rw [ite_eq_right fun h' ↦ hc (B.inWindow_unique h' h)]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem stackAt_getElem_of_total_le (t : B.Tables R) {μ : ℕ} (pad : R) {x : ℕ}
    (hx : x < 2 ^ μ) (h : B.total ≤ x) : (B.stackAt t μ pad)[x] = pad := by
  simp [stackAt, h]

/-- Mapping the entries commutes with stacking, the pad included. No injectivity and no fit
hypothesis is needed. -/
theorem map_stackAt {S : Type*} [CommRing S] (φ : R →+* S) (t : B.Tables R) (μ : ℕ)
    (pad : R) :
    CMlPolynomialEval.map φ (B.stackAt t μ pad) =
      B.stackAt (fun b ↦ CMlPolynomialEval.map φ (t b)) μ (φ pad) := by
  apply Vector.ext
  intro x hx
  simp only [CMlPolynomialEval.map, Vector.getElem_map, stackAt, Vector.getElem_ofFn]
  change φ (if B.total ≤ x then pad else ∑ b : Fin B.n,
      if B.InWindow b x then ((t b)[x - B.offset b]?).getD 0 else 0) =
    if B.total ≤ x then φ pad else ∑ b : Fin B.n,
      if B.InWindow b x then (Vector.map φ (t b))[x - B.offset b]?.getD 0 else 0
  split_ifs <;>
    simp_all only [map_sum, apply_ite, Vector.getElem?_map, ← Option.getD_map, map_zero]

/-- A stack that the blocks fill does not depend on the pad. -/
theorem stackAt_eq_of_total_eq (t : B.Tables R) {μ : ℕ} (h : B.total = 2 ^ μ) (pad pad' : R) :
    B.stackAt t μ pad = B.stackAt t μ pad' := by
  apply Vector.ext
  intro i hi
  simp [stackAt, h, Nat.not_le.mpr hi]

/-! ## Selectors -/

/-- Every block fits in a stack of `μ` variables. -/
theorem size_le {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) : B.size b ≤ μ := by
  have h1 : 2 ^ B.size b ≤ 2 ^ μ :=
    le_trans (by have := B.offset_add_pow_le_total b; (clear * - this; omega)) hμ
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

/-- The selector of block `b` in a stack of `μ` variables: the index `offset_b >> size_b` of
the high `μ - size_b` coordinates. -/
def selector {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) : Fin (2 ^ (μ - B.size b)) :=
  ⟨B.offset b / 2 ^ B.size b, by
    have h1 := B.offset_add_pow_le_total b
    have h2 : B.offset b < 2 ^ B.size b * 2 ^ (μ - B.size b) := by
      rw [← pow_add, Nat.add_sub_cancel' (B.size_le hμ b)]
      have h3 := Nat.two_pow_pos (B.size b)
      omega
    exact Nat.div_lt_of_lt_mul h2⟩

@[simp] theorem selector_val {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) :
    (B.selector hμ b).val = B.offset b / 2 ^ B.size b := rfl

/-- A point of block `b` lifted to the stack: the point in the low coordinates, the bits of the
block's selector in the high ones. -/
def extendPoint {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R (B.size b)) :
    Vector R μ :=
  Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b))
    (z ++ (boolVec (B.selector hμ b) : Vector R (μ - B.size b)))

/-- The low coordinates of a point of the stack: a point of block `b`. -/
def lowPoint {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R μ) :
    Vector R (B.size b) :=
  lowVec (Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b)).symm z)

/-- The high coordinates of a point of the stack, on which block `b`'s selector is tested. -/
def highPoint {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R μ) :
    Vector R (μ - B.size b) :=
  highVec (Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b)).symm z)

omit [CommRing R] in
/-- A point of the stack is its low part followed by its high part. -/
theorem cast_lowPoint_append_highPoint {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (z : Vector R μ) :
    Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b))
      (B.lowPoint hμ b z ++ B.highPoint hμ b z) = z := by
  rw [lowPoint, highPoint, lowVec_append_highVec]
  simp

/-! ## Reading a block off a table -/

/-- Block `b` read off a table of `μ` variables: the cells of its window. The table need not be
a stack. -/
def unstack {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (q : CMlPolynomialEval R μ)
    (b : Fin B.n) : CMlPolynomialEval R (B.size b) :=
  slice (Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel' (B.size_le hμ b)).symm) q)
    (B.selector hμ b)

omit [CommRing R] in
/-- A block read is the cell at the block's offset plus the local index. -/
theorem unstack_getElem {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (q : CMlPolynomialEval R μ)
    (b : Fin B.n) {i : ℕ} (hi : i < 2 ^ B.size b) :
    (B.unstack hμ q b)[i] = q[i + B.offset b]'(by
      have := B.offset_add_pow_le_total b
      omega) := by
  rw [unstack, slice_getElem_nat _ _ hi]
  simp [selector_val, Nat.mul_div_cancel' (B.pow_size_dvd_offset b)]

/-- Reading a block off the stack returns the block. -/
@[simp] theorem unstack_stackAt (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R)
    (b : Fin B.n) : B.unstack hμ (B.stackAt t μ pad) b = t b := by
  apply Vector.ext
  intro i hi
  rw [B.unstack_getElem hμ _ b hi]
  have hx : i + B.offset b < 2 ^ μ := by
    have := B.offset_add_pow_le_total b
    omega
  rw [B.stackAt_getElem_of_inWindow t (b := b) pad hx ⟨by (clear * -; omega), by (clear * - hi; omega)⟩]
  simp

/-- Mapping the entries commutes with reading a block. -/
theorem unstack_map {S : Type*} [CommRing S] (φ : R →+* S) {μ : ℕ}
    (hμ : B.total ≤ 2 ^ μ) (q : CMlPolynomialEval R μ) (b : Fin B.n) :
    B.unstack hμ (CMlPolynomialEval.map φ q) b =
      CMlPolynomialEval.map φ (B.unstack hμ q b) := by
  apply Vector.ext
  intro i hi
  rw [B.unstack_getElem hμ _ b hi]
  simp only [CMlPolynomialEval.map, Vector.getElem_map]
  exact congrArg φ (B.unstack_getElem hμ q b hi).symm

/-! ## The selection identity -/

/-- The selection identity, for any table: the table at a lifted point is the block read off
it, at the point. -/
private theorem unstack_eval {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (q : CMlPolynomialEval R μ)
    (b : Fin B.n) (z : Vector R (B.size b)) :
    evalMle q (B.extendPoint hμ b z) = evalMle (B.unstack hμ q b) z := by
  have hk : B.size b + (μ - B.size b) = μ := Nat.add_sub_cancel' (B.size_le hμ b)
  have hq : q = Vector.cast (congrArg (2 ^ ·) hk)
      (Vector.cast (congrArg (2 ^ ·) hk.symm) q) := by simp
  rw [extendPoint]
  conv_lhs => rw [hq, evalMle_cast hk, evalMle_append_boolVec]
  rfl

/-- The selection identity at a point of another ring. -/
theorem unstack_eval₂ {S : Type*} [CommRing S] (φ : R →+* S) {μ : ℕ}
    (hμ : B.total ≤ 2 ^ μ) (q : CMlPolynomialEval R μ) (b : Fin B.n)
    (z : Vector S (B.size b)) :
    eval₂Mle q φ (B.extendPoint hμ b z) = eval₂Mle (B.unstack hμ q b) φ z := by
  rw [eval₂Mle, eval₂Mle, ← B.unstack_map]
  exact B.unstack_eval hμ (CMlPolynomialEval.map φ q) b z

/-- The selection identity for the stack at a point of another ring. -/
theorem stack_eval₂ {S : Type*} [CommRing S] (φ : R →+* S) (t : B.Tables R) {μ : ℕ}
    (hμ : B.total ≤ 2 ^ μ) (pad : R) (b : Fin B.n) (z : Vector S (B.size b)) :
    eval₂Mle (B.stackAt t μ pad) φ (B.extendPoint hμ b z) = eval₂Mle (t b) φ z := by
  rw [B.unstack_eval₂, B.unstack_stackAt]

/-! ## The product of a stack's cells -/

/-- The cells of the first `k` blocks, read off the stack as an initial segment, multiply to the
product of those blocks' cells. -/
private theorem prod_range_offsetNat (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R)
    (k : ℕ) (hk : k ≤ B.n) :
    ∏ x ∈ Finset.range (B.offsetNat k),
        (if h : x < 2 ^ μ then (B.stackAt t μ pad)[x] else 1) =
      ∏ c ∈ Finset.range k, if h : c < B.n then ∏ y : Fin (2 ^ B.size ⟨c, h⟩), (t ⟨c, h⟩)[y]
        else 1 := by
  induction k with
  | zero => simp [offsetNat]
  | succ k ih =>
    have hkn : k < B.n := by (clear * - hk; omega)
    rw [B.offsetNat_succ k hkn, Finset.prod_range_add, ih (by (clear * - hk; omega)), Finset.prod_range_succ,
      dite_eq_left hkn]
    congr 1
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun y _ ↦ ?_
    have hwin : B.InWindow ⟨k, hkn⟩ (B.offsetNat k + y) := ⟨by simp [offset], by simp [offset]⟩
    have hx : B.offsetNat k + y < 2 ^ μ := by
      have := B.offset_add_pow_le_total ⟨k, hkn⟩
      simp only [offset] at this
      omega
    rw [dite_eq_left hx, B.stackAt_getElem_of_inWindow t pad hx hwin]
    simp [offset]

/-- The product of a stack's cells is the product of its blocks' cells, times the pad once for
each cell no block covers. -/
theorem prod_stackAt (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R) :
    ∏ x : Fin (2 ^ μ), (B.stackAt t μ pad)[x] =
      (∏ b : Fin B.n, ∏ y : Fin (2 ^ B.size b), (t b)[y]) * pad ^ (2 ^ μ - B.total) := by
  have hrange : ∏ x : Fin (2 ^ μ), (B.stackAt t μ pad)[x] =
      ∏ x ∈ Finset.range (2 ^ μ), (if h : x < 2 ^ μ then (B.stackAt t μ pad)[x] else 1) := by
    rw [← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_congr rfl fun x _ ↦ by simp
  rw [hrange, show Finset.range (2 ^ μ) = Finset.range (B.total + (2 ^ μ - B.total)) by
    rw [Nat.add_sub_cancel' hμ], Finset.prod_range_add]
  congr 1
  · rw [total, B.prod_range_offsetNat t hμ pad B.n le_rfl, ← Fin.prod_univ_eq_prod_range]
    simp
  · rw [← Finset.card_range (2 ^ μ - B.total), ← Finset.prod_const]
    refine Finset.prod_congr (by simp) fun y hy ↦ ?_
    rw [Finset.mem_range] at hy
    have hx : B.total + y < 2 ^ μ := by omega
    rw [dite_eq_left hx, B.stackAt_getElem_of_total_le t pad hx (by omega)]

end Blocks

end
end LeanVM.Protocol
end
-- ===== end of `LvmCpStacking` =====

/-!
# A stack at an arbitrary point

At a point whose high coordinates are not selector bits, every block contributes. The block
`b` contributes its extension at the point's low coordinates, weighted by
`selectorWeight b`, the Lagrange basis of the high coordinates at the block's selector; the
cells no block covers contribute the pad, weighted by what is left of the partition of unity
(`stack_eval_ambient`). When the blocks fill the stack the weights sum to one
(`sum_selectorWeight_of_total_eq`).
`stack_eval₂_ambient` is the statement at a point of another ring than the entries. Over an
arbitrary commutative ring.

Candidate for CompPoly, beside `CompPoly.Multilinear`. The request it answers is tracked
upstream as [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900). Nothing here
transcribes a source.

Derived from Verified-zkEVM/leanth at 23929f8c922cd4461ab22dbfaa6520f3ad23a3b2,
`Leanth/LeanVM/Protocol.lean:9818-9850` (`eval_MLE_stack_ambient`), by Aristotle (Harmonic),
Stefano Rocca and Elias Judin. The source statement, for pad zero, is extended to any pad and
to a point of another ring.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

section

variable {R : Type*} [CommRing R]

private theorem evalMle_map_sub_const {n : ℕ} (t : CMlPolynomialEval R n) (a : R)
    (z : Vector R n) :
    evalMle (Vector.map (fun x ↦ x - a) t) z = evalMle t z - a := by
  rw [evalMle_eq_sum]
  simp only [Fin.getElem_fin, Vector.getElem_map, sub_mul, Finset.sum_sub_distrib]
  have hc : (∑ i : Fin (2 ^ n), a * (lagrangeBasis z)[i.val]) = a := by
    simpa only [evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_replicate] using
      evalMle_replicate a z
  rw [hc]
  congr 1
  exact (evalMle_eq_sum t z).symm

namespace Blocks

variable (B : Blocks)

/-- The weight of block `b` at a point of the stack: the Lagrange basis of the point's high
coordinates at the block's selector. -/
def selectorWeight {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R μ) : R :=
  (lagrangeBasis (B.highPoint hμ b z))[B.selector hμ b]

/-- A table placed in a block's window, zero outside it. -/
def windowTable {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (t : CMlPolynomialEval R (B.size b)) : CMlPolynomialEval R μ :=
  Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel' (B.size_le hμ b)))
    (placeSlice t (B.selector hμ b))

/-- A window table reads the local value inside its window and vanishes outside it. -/
theorem windowTable_getElem {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (t : CMlPolynomialEval R (B.size b)) (x : Fin (2 ^ μ)) :
    (B.windowTable hμ b t)[x] = if h : B.InWindow b x.val then
      t[x.val - B.offset b]'(by have := h.2; omega) else 0 := by
  simp only [windowTable, Fin.getElem_fin, Vector.getElem_cast, placeSlice,
    Vector.getElem_ofFn, selector_val]
  by_cases hx : B.InWindow b x.val
  · have hd := (B.inWindow_iff_div b x.val).mp hx
    have hm := Nat.mod_add_div x.val (2 ^ B.size b)
    rw [hd, Nat.mul_div_cancel' (B.pow_size_dvd_offset b)] at hm
    have he : x.val % 2 ^ B.size b = x.val - B.offset b := by omega
    simp [hx, hd, he]
  · simp [hx, (B.inWindow_iff_div b x.val).not.mp hx]

/-- The extension of a window table is the table's extension at the low coordinates, times the
block's weight. -/
theorem evalMle_windowTable {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (t : CMlPolynomialEval R (B.size b)) (z : Vector R μ) :
    evalMle (B.windowTable hμ b t) z =
      B.selectorWeight hμ b z * evalMle t (B.lowPoint hμ b z) := by
  conv_lhs => rw [← B.cast_lowPoint_append_highPoint hμ b z]
  rw [windowTable, evalMle_cast, evalMle_placeSlice]
  rfl

/-- The stack is the constant pad plus, on each window, the block minus the pad. -/
theorem stackAt_decomposition (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R) :
    B.stackAt t μ pad = Vector.ofFn (fun x ↦ pad +
      ∑ b : Fin B.n, (B.windowTable hμ b (Vector.map (fun v ↦ v - pad) (t b)))[x]) := by
  apply Vector.ext
  intro x hx
  simp only [Vector.getElem_ofFn]
  by_cases hp : B.total ≤ x
  · rw [B.stackAt_getElem_of_total_le t pad hx hp]
    have hn : ∀ b : Fin B.n, ¬ B.InWindow b x := by
      intro b hb
      have := B.offset_add_pow_le_total b
      (clear * - hp hb this; omega)
    simp [B.windowTable_getElem, hn]
  · obtain ⟨b, hb⟩ := B.exists_inWindow (Nat.lt_of_not_ge hp)
    rw [B.stackAt_getElem_of_inWindow t (b := b) pad hx hb, Finset.sum_eq_single b]
    · rw [B.windowTable_getElem, dite_eq_left hb]
      simp
    · intro c _ hc
      rw [B.windowTable_getElem, dite_eq_right (fun hh ↦ hc (B.inWindow_unique hh hb))]
    · simp

/-- The stack at an arbitrary point: every block at the point's low coordinates, weighted by
its selector at the high ones, plus the pad times the weight no block covers. -/
theorem stack_eval_ambient (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R)
    (z : Vector R μ) :
    evalMle (B.stackAt t μ pad) z =
      (∑ b : Fin B.n, B.selectorWeight hμ b z * evalMle (t b) (B.lowPoint hμ b z)) +
        pad * (1 - ∑ b : Fin B.n, B.selectorWeight hμ b z) := by
  rw [B.stackAt_decomposition t hμ pad, evalMle_eq_sum]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hc : (∑ i : Fin (2 ^ μ), pad * (lagrangeBasis z)[i.val]) = pad := by
    simpa only [evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_replicate] using
      evalMle_replicate pad z
  rw [hc]
  have ht (b : Fin B.n) :
      (∑ i : Fin (2 ^ μ), (B.windowTable hμ b (Vector.map (fun v ↦ v - pad) (t b)))[i.val] *
        (lagrangeBasis z)[i.val]) =
        B.selectorWeight hμ b z * (evalMle (t b) (B.lowPoint hμ b z) - pad) := by
    simpa only [evalMle_eq_sum, Fin.getElem_fin] using
      (B.evalMle_windowTable hμ b (Vector.map (fun v ↦ v - pad) (t b)) z).trans
        (congrArg (B.selectorWeight hμ b z * ·)
          (evalMle_map_sub_const (t b) pad (B.lowPoint hμ b z)))
  simp_rw [ht, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

/-- When the blocks fill the stack, their weights sum to one at every point. -/
theorem sum_selectorWeight_of_total_eq {μ : ℕ} (h : B.total = 2 ^ μ) (z : Vector R μ) :
    (∑ b : Fin B.n, B.selectorWeight h.le b z) = 1 := by
  let t : B.Tables R := fun b ↦ Vector.replicate (2 ^ B.size b) 0
  have h0 := B.stack_eval_ambient t h.le 0 z
  have h1 := B.stack_eval_ambient t h.le 1 z
  rw [B.stackAt_eq_of_total_eq t h 1 0, h0] at h1
  have hc : (0 : R) = 1 * (1 - ∑ b : Fin B.n, B.selectorWeight h.le b z) :=
    add_left_cancel (by simpa only [zero_mul, add_zero] using h1)
  rw [one_mul] at hc
  exact (sub_eq_zero.mp hc.symm).symm

end Blocks

end
end LeanVM.Protocol
