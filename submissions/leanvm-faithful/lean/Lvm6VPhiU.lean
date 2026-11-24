-- New for lvm6 (PHIV8): unreduced `E2` product sums. `m2B` spends most of its time outside the integer products:
-- seven bit reversals, of which three turn the high words back; the reduction itself is a few `xor`s. Both are
-- `GF(2)`-linear, so a sum of products can add the six raw words of each product (`m2U`) and finish once (`U6.fin`).
import Lvm6VMulB
import LvmE2VRingA

/-!
# Unreduced `E2` product sums

* `U6`: the six raw words of a `bmul64`-form product (the low words `l0`, `l1`, `lm` of `re·re`, `im·im`,
  `(re+im)·(re+im)`, and the low words `h0`, `h1`, `hm` of the bit-reversed operands' products); `U6.add` is the
  wordwise `xor`; `U6.fin` the three reversals, the `x·p₁` shift and the two reductions.
* `m2U a b`: the six words of one product. **`fin_m2U : (m2U a b).fin = m2B a b`**, `fin_m2U_eq` (`= a * b`),
  **`fin_add : (u.add v).fin = u.fin + v.fin`**, `fin_zero`, **`fin_ofE : (ofE v).fin = v`** (a value enters a sum
  with no product).
* `goSumU` (a lazy sum over an index range, `fin_goSumU`), `sumU` (`sumU_eq`), `foldU` (over an array, `fin_foldU`),
  `sumArrU` (`sumArrU_eq`).

The linearity rests on `FK.reduce`, `rev64`, `>>> 1`, `<<< 1` and `>>> 63` being `xor`-linear (`reduce_xor`,
MUL's `rev64_xor`, `u64_shl_xor`, `u64_shr_xor`); `m2B`'s `|||` of disjoint bits is an `xor` (`shl1_or_shr63`).
-/

set_option autoImplicit false

namespace Lvm6.V

open Lvm Lvm.FK

/-! ## Words -/

theorem u64_shl_xor (x y k : UInt64) : (x ^^^ y) <<< k = (x <<< k) ^^^ (y <<< k) := by
  apply UInt64.toBitVec_inj.mp
  simp [BitVec.shiftLeft_xor_distrib]

theorem u64_shr_xor (x y k : UInt64) : (x ^^^ y) >>> k = (x >>> k) ^^^ (y >>> k) := by
  apply UInt64.toBitVec_inj.mp
  simp [BitVec.ushiftRight_xor_distrib]

/-- The bits of `x <<< 1` and `y >>> 63` are disjoint. -/
theorem shl1_or_shr63 (x y : UInt64) : (x <<< 1) ||| (y >>> 63) = (x <<< 1) ^^^ (y >>> 63) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · rw [BitVec.getLsbD_of_ge y.toBitVec (63 + i) (by omega)]
    simp

theorem reduce_xor (a b c d : UInt64) :
    FK.reduce (a ^^^ c) (b ^^^ d) = FK.reduce a b ^^^ FK.reduce c d := by
  unfold FK.reduce
  simp only [u64_shr_xor, u64_shl_xor]
  ac_rfl

theorem rev64_zero : rev64 0 = 0 := by decide

theorem reduce_lo (a : UInt64) : FK.reduce a 0 = a := by
  unfold FK.reduce
  simp only [UInt64.zero_shiftRight, UInt64.zero_shiftLeft, UInt64.xor_zero]

/-! ## The unreduced product -/

/-- **Six raw words of an `E2` product** (`m2B` before its reversals and reductions), or a sum of such. -/
structure U6 where
  l0 : UInt64
  l1 : UInt64
  lm : UInt64
  h0 : UInt64
  h1 : UInt64
  hm : UInt64

namespace U6

/-- The empty sum. -/
@[inline] def zero : U6 := ⟨0, 0, 0, 0, 0, 0⟩

/-- Wordwise `xor`: the sum. -/
@[inline] def add (u v : U6) : U6 :=
  ⟨u.l0 ^^^ v.l0, u.l1 ^^^ v.l1, u.lm ^^^ v.lm, u.h0 ^^^ v.h0, u.h1 ^^^ v.h1, u.hm ^^^ v.hm⟩

/-- The finish's `re` word: `l0 + l1`, reduced with the reversed high words. -/
@[inline] def finRe (u : U6) : UInt64 := FK.reduce (u.l0 ^^^ u.l1) (rev64 (u.h0 ^^^ u.h1) >>> 1)

/-- The finish's `im` word: the middle product, `p₀ + p₁` and `x·p₁`, reduced. -/
@[inline] def finIm (u : U6) : UInt64 :=
  FK.reduce (u.lm ^^^ (u.l0 ^^^ u.l1) ^^^ (u.l1 <<< 1))
    ((rev64 (u.hm ^^^ u.h0 ^^^ u.h1) >>> 1) ^^^ (((rev64 u.h1 >>> 1) <<< 1) ^^^ (u.l1 >>> 63)))

/-- **The finish**: `m2B`'s tail (three reversals, `x·p₁`, two reductions), once per sum. -/
@[inline] def fin (u : U6) : FE2 := ⟨⟨finRe u⟩, ⟨finIm u⟩⟩

/-- A value as a sum of no product: `fin (ofE v) = v`. -/
@[inline] def ofE (v : FE2) : U6 := ⟨v.re.val, 0, v.re.val ^^^ v.im.val, 0, 0, 0⟩

end U6

/-- **The unreduced product**: `m2B`'s six `bmul64` words. -/
@[inline] def m2U (a b : FE2) : U6 :=
  let ar := a.re.val; let ai := a.im.val; let br := b.re.val; let bi := b.im.val
  let rar := rev64 ar; let rai := rev64 ai; let rbr := rev64 br; let rbi := rev64 bi
  ⟨bmul64 ar br, bmul64 ai bi, bmul64 (ar ^^^ ai) (br ^^^ bi), bmul64 rar rbr, bmul64 rai rbi,
    bmul64 (rar ^^^ rai) (rbr ^^^ rbi)⟩

theorem fin_m2U (a b : FE2) : (m2U a b).fin = m2B a b := by
  simp only [m2U, U6.fin, U6.finRe, U6.finIm, m2B, shl1_or_shr63]

theorem fin_m2U_eq (a b : FE2) : (m2U a b).fin = a * b := by
  rw [fin_m2U, m2B_eq, Lvm.Typed.KT.m2_eq]

theorem fe2_ext_val (a b : FE2) (hr : a.re.val = b.re.val) (hi : a.im.val = b.im.val) : a = b := by
  obtain ⟨⟨_⟩, ⟨_⟩⟩ := a
  obtain ⟨⟨_⟩, ⟨_⟩⟩ := b
  simp only at hr hi
  subst hr hi
  rfl

theorem fin_re (u : U6) : u.fin.re.val = U6.finRe u := rfl
theorem fin_im (u : U6) : u.fin.im.val = U6.finIm u := rfl
theorem fe2_add_re_val (a b : FE2) : (a + b).re.val = a.re.val ^^^ b.re.val := rfl
theorem fe2_add_im_val (a b : FE2) : (a + b).im.val = a.im.val ^^^ b.im.val := rfl

theorem finRe_add (u v : U6) : U6.finRe (u.add v) = U6.finRe u ^^^ U6.finRe v := by
  obtain ⟨a0, a1, am, b0, b1, bm⟩ := u
  obtain ⟨c0, c1, cm, d0, d1, dm⟩ := v
  simp only [U6.finRe, U6.add]
  rw [← reduce_xor]
  simp only [rev64_xor, u64_shr_xor]
  refine congrArg₂ FK.reduce ?_ ?_
  · apply P_inj
    simp only [P_xor]
    abel
  · apply P_inj
    simp only [P_xor]
    abel

theorem finIm_add (u v : U6) : U6.finIm (u.add v) = U6.finIm u ^^^ U6.finIm v := by
  obtain ⟨a0, a1, am, b0, b1, bm⟩ := u
  obtain ⟨c0, c1, cm, d0, d1, dm⟩ := v
  simp only [U6.finIm, U6.add]
  rw [← reduce_xor]
  simp only [rev64_xor, u64_shr_xor, u64_shl_xor]
  refine congrArg₂ FK.reduce ?_ ?_
  · apply P_inj
    simp only [P_xor]
    abel
  · apply P_inj
    simp only [P_xor]
    abel

theorem fin_add (u v : U6) : (u.add v).fin = u.fin + v.fin := by
  apply fe2_ext_val
  · rw [fin_re, fe2_add_re_val, fin_re, fin_re, finRe_add]
  · rw [fin_im, fe2_add_im_val, fin_im, fin_im, finIm_add]

theorem fin_zero : U6.zero.fin = 0 := by
  apply fe2_ext_val
  · rw [fin_re]
    simp only [U6.finRe, U6.zero, UInt64.xor_zero, rev64_zero, UInt64.zero_shiftRight, reduce_lo]
    rfl
  · rw [fin_im]
    simp only [U6.finIm, U6.zero, UInt64.xor_zero, rev64_zero, UInt64.zero_shiftRight, UInt64.zero_shiftLeft,
      reduce_lo]
    rfl

theorem fin_ofE (v : FE2) : (U6.ofE v).fin = v := by
  apply fe2_ext_val
  · rw [fin_re]
    simp only [U6.finRe, U6.ofE, UInt64.xor_zero, rev64_zero, UInt64.zero_shiftRight, reduce_lo]
  · rw [fin_im]
    simp only [U6.finIm, U6.ofE, UInt64.xor_zero, rev64_zero, UInt64.zero_shiftRight, UInt64.zero_shiftLeft,
      reduce_lo]
    rw [UInt64.xor_assoc, UInt64.xor_comm v.im.val, ← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]

/-! ## Lazy sums

The loops carry the six words as separate arguments: no `U6` is allocated per item once `f` is inlined and builds
its `U6` in one straight line (no branch returning a `U6`). -/

/-- `⟨l0, …, hm⟩ + Σ_{a ≤ i < b} f i`, unreduced. -/
@[specialize] def goSumU (f : ℕ → U6) (a b : ℕ) (l0 l1 lm h0 h1 hm : UInt64) : U6 :=
  if a < b then
    let u := f a
    goSumU f (a + 1) b (l0 ^^^ u.l0) (l1 ^^^ u.l1) (lm ^^^ u.lm) (h0 ^^^ u.h0) (h1 ^^^ u.h1) (hm ^^^ u.hm)
  else ⟨l0, l1, lm, h0, h1, hm⟩
termination_by b - a

theorem fin_goSumU (f : ℕ → U6) (b : ℕ) : ∀ (d a : ℕ) (l0 l1 lm h0 h1 hm : UInt64), b - a = d →
    (goSumU f a b l0 l1 lm h0 h1 hm).fin =
      (U6.mk l0 l1 lm h0 h1 hm).fin + ((List.range' a (b - a)).map fun i => (f i).fin).sum
  | 0, a, l0, l1, lm, h0, h1, hm, hd => by
    rw [goSumU, if_neg (by omega), hd]; simp
  | d + 1, a, l0, l1, lm, h0, h1, hm, hd => by
    rw [goSumU, if_pos (by omega)]
    dsimp only
    rw [fin_goSumU f b d (a + 1) _ _ _ _ _ _ (by omega),
      show U6.mk (l0 ^^^ (f a).l0) (l1 ^^^ (f a).l1) (lm ^^^ (f a).lm) (h0 ^^^ (f a).h0) (h1 ^^^ (f a).h1)
        (hm ^^^ (f a).hm) = (U6.mk l0 l1 lm h0 h1 hm).add (f a) from rfl, fin_add,
      show b - a = (b - (a + 1)) + 1 by omega, List.range'_succ, List.map_cons, List.sum_cons, add_assoc]

/-- `Σ_{a ≤ i < b} f i`, finished once. -/
@[inline] def sumU (f : ℕ → U6) (a b : ℕ) : FE2 := (goSumU f a b 0 0 0 0 0 0).fin

theorem sumU_eq (f : ℕ → U6) (a b : ℕ) : sumU f a b = ((List.range' a (b - a)).map fun i => (f i).fin).sum := by
  rw [sumU, fin_goSumU f b _ a _ _ _ _ _ _ rfl, show U6.mk 0 0 0 0 0 0 = U6.zero from rfl, fin_zero, zero_add]

/-- `⟨l0, …, hm⟩ + Σ_{t ∈ es[i:]} f t`, unreduced. -/
@[specialize] def foldU {α : Type} (es : Array α) (f : α → U6) (i : ℕ) (l0 l1 lm h0 h1 hm : UInt64) : U6 :=
  if h : i < es.size then
    let u := f es[i]
    foldU es f (i + 1) (l0 ^^^ u.l0) (l1 ^^^ u.l1) (lm ^^^ u.lm) (h0 ^^^ u.h0) (h1 ^^^ u.h1) (hm ^^^ u.hm)
  else ⟨l0, l1, lm, h0, h1, hm⟩
termination_by es.size - i

theorem fin_foldU {α : Type} (es : Array α) (f : α → U6) : ∀ (d i : ℕ) (l0 l1 lm h0 h1 hm : UInt64),
    es.size - i = d →
    (foldU es f i l0 l1 lm h0 h1 hm).fin =
      (U6.mk l0 l1 lm h0 h1 hm).fin + ((es.toList.drop i).map fun t => (f t).fin).sum
  | 0, i, l0, l1, lm, h0, h1, hm, hd => by
    rw [foldU, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]; simp
  | d + 1, i, l0, l1, lm, h0, h1, hm, hd => by
    have hi : i < es.size := by omega
    rw [foldU, dif_pos hi]
    dsimp only
    rw [fin_foldU es f d (i + 1) _ _ _ _ _ _ (by omega),
      show U6.mk (l0 ^^^ (f es[i]).l0) (l1 ^^^ (f es[i]).l1) (lm ^^^ (f es[i]).lm) (h0 ^^^ (f es[i]).h0)
        (h1 ^^^ (f es[i]).h1) (hm ^^^ (f es[i]).hm) = (U6.mk l0 l1 lm h0 h1 hm).add (f es[i]) from rfl, fin_add]
    conv_rhs => rw [List.drop_eq_getElem_cons (by simpa using hi)]
    simp only [Array.getElem_toList, List.map_cons, List.sum_cons, add_assoc]

/-- `Σ_{t ∈ es} f t`, finished once. -/
@[inline] def sumArrU {α : Type} (es : Array α) (f : α → U6) : FE2 := (foldU es f 0 0 0 0 0 0 0).fin

theorem sumArrU_eq {α : Type} (es : Array α) (f : α → U6) :
    sumArrU es f = (es.toList.map fun t => (f t).fin).sum := by
  rw [sumArrU, fin_foldU es f _ 0 _ _ _ _ _ _ rfl, show U6.mk 0 0 0 0 0 0 = U6.zero from rfl, fin_zero, zero_add,
    List.drop_zero]

end Lvm6.V
