-- New for lvm2 E2-FT (E2F-QH5): the algebra of the row switch's CRT weight (`LvmQRingCrt`): the trace-dual basis
-- of `K` over `F₂` (`dual_trace`, by Lagrange interpolation at the 64 conjugates of `x`), the CRT components of
-- V's tensor coordinates (`phiA_tensorWD`), and the weight as the components' `ν`-sum (`weight_crt`).
import LvmQRingRowReplay
import LvmE2QLSem
import LvmFieldKCorrect
import Mathlib.LinearAlgebra.Lagrange

/-!
# The row switch's weight by the CRT: the algebra

**The trace-dual basis** (`dual_trace`): with `f(y) = y⁶⁴ + y⁴ + y³ + y + 1`, `f(y)/(y − x) = Σ_{i<64} β_i y^i`
(`quotCoefs`) and `δ_i = β_i/f'(x)` (`dualK`; `f' = y² + 1` in characteristic 2),
`Σ_{k<64} (δ_i x^j)^(2^k) = [i = j]` for `i, j < 64`. Proof: the 64 conjugates `α_k = x^(2^k)` are distinct roots
of `f`; `B_k = (f/(y − x))^(σ^k) = f/(y − α_k)` vanishes at every `α_m`, `m ≠ k`, and is `f'(α_k)` at `α_k`; so
`Σ_k α_k^j/f'(α_k)·B_k` and `y^j` agree at the 64 conjugates and are equal (degree `< 64`); compare coefficient `i`.
The coefficients are checked once by the kernel (`quotOkB`, 65 word identities).

**The CRT components** (`phiA_tensorWD`): for a vector `v` of 128 `E3` values (coordinates on `β_j ⊗ 1`, `β_i = x^i`,
`β_{64+i} = x^i X`), `Φ_k(v) = (Σ_i (x^i)^(2^k) v_i, Σ_i (x^i)^(2^k) v_{64+i})` in `E3[X]/(X² + x^(2^k) X + 1)`
(`qm`); V's `tensorStepD` by `(z, r)` multiplies `Φ_k` by `(1 + z_re^(2^k) + r) + z_im^(2^k) X`.

**The weight** (`weight_crt`): `Σ_j ρ_j v_j = Σ_k (Σ_i δ_i^(2^k) ρ_i)·Φ_k(v)₀ + (Σ_i δ_i^(2^k) ρ_{64+i})·Φ_k(v)₁`.
-/

set_option autoImplicit false

noncomputable section

namespace Lvm.Q2

open Polynomial Finset

/-! ## The trace-dual basis -/

/-- `β_n` (`0` from `64` on). -/
def betaK (n : ℕ) : FK := if n < 64 then quotCoefs.getD n 0 else 0

/-- The coefficients of `f`. -/
def fC (n : ℕ) : FK := if n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 64 then 1 else 0

/-- **The kernel check**: `(y − x)·Σ β_i y^i = f` coefficientwise, degrees `0 … 64`. -/
def quotOkB : Bool :=
  (List.range 65).all fun n => (if n = 0 then 0 else betaK (n - 1)) + FK.x * betaK n == fC n

/-! `quotOkB` by the recurrence `β_{i−1} = f_i + x·β_i` that builds `quotCoefs` (`qcL_rec`, by induction): the
kernel checks only degree `0` (`quot0`), not the 65 products (5.7 M → 1.8 M hb). -/

/-- The fold behind `quotCoefs` after `k` steps (proof help). -/
private def qcL (k : ℕ) : List FK := (List.range k).foldl (fun (acc : List FK) i =>
    let b := acc.headD 1
    (fCoef (63 - i) + FK.x * b) :: acc) [1]

private theorem qcL_succ (k : ℕ) : qcL (k + 1) = (fCoef (63 - k) + FK.x * (qcL k).headD 1) :: qcL k := by
  rw [qcL, List.range_succ, List.foldl_append]; rfl

private theorem qcL_ne (k : ℕ) : qcL k ≠ [] := by
  cases k with
  | zero => exact List.cons_ne_nil _ _
  | succ k => rw [qcL_succ]; exact List.cons_ne_nil _ _

private theorem qcL_rec (k : ℕ) (hk : k ≤ 63) : ∀ j, j < k →
    (qcL k).getD j 0 = fCoef (63 - k + j + 1) + FK.x * (qcL k).getD (j + 1) 0 := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    rw [qcL_succ]
    cases j with
    | zero =>
      obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil (qcL_ne k)
      rw [hbt, List.getD_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.headD_cons,
        show 63 - (k + 1) + 0 + 1 = 63 - k by omega]
    | succ j =>
      rw [List.getD_cons_succ, List.getD_cons_succ, ih (by omega) j (by omega),
        show 63 - (k + 1) + (j + 1) + 1 = 63 - k + j + 1 by omega]

private theorem qcL_last (k : ℕ) : (qcL k).getD k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [qcL_succ, List.getD_cons_succ, ih]

private theorem betaK_qcL (m : ℕ) (hm : m < 64) : betaK m = (qcL 63).getD m 0 := by
  rw [betaK, if_pos hm, show quotCoefs = (qcL 63).toArray from rfl, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- `qcL` on the words as natural numbers (GOLF3: the kernel computes `ℕ`'s operations natively). -/
private def qcN (k : ℕ) : List ℕ := (List.range k).foldl (fun (acc : List ℕ) i =>
    ((fCoef (63 - i)).val.toNat ^^^ FK.mulN 2 (acc.headD 1)) :: acc) [1]

private theorem qcN_succ (k : ℕ) :
    qcN (k + 1) = ((fCoef (63 - k)).val.toNat ^^^ FK.mulN 2 ((qcN k).headD 1)) :: qcN k := by
  rw [qcN, List.range_succ, List.foldl_append]; rfl

private theorem qcL_toNat : ∀ k : ℕ, (qcL k).map (fun a : FK => a.val.toNat) = qcN k
  | 0 => rfl
  | k + 1 => by
    rw [qcL_succ, qcN_succ, List.map_cons, ← qcL_toNat k, FK.add_toNat, FK.mul_toNat]
    obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil (qcL_ne k)
    rw [hbt]
    rfl

private theorem quot0 : ((0 : FK) + FK.x * betaK 0 == fC 0) = true := by
  have h : ((qcL 63).getD 0 0).val.toNat = (qcN 63).getD 0 0 := by
    rw [← qcL_toNat]
    obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil (qcL_ne 63)
    rw [hbt]
    rfl
  rw [beq_iff_eq, FK.eq_iff_toNat, FK.add_toNat, FK.mul_toNat, betaK_qcL 0 (by decide), h]
  decide +kernel

theorem quotOkB_true : quotOkB = true := by
  refine List.all_eq_true.mpr fun n hn => beq_iff_eq.mpr ?_
  have hn := List.mem_range.mp hn
  rcases (show n = 0 ∨ (1 ≤ n ∧ n ≤ 63) ∨ n = 64 by (clear * - hn hn; omega)) with h | h | h
  · subst h; rw [if_pos rfl]; exact beq_iff_eq.mp quot0
  · rw [if_neg (by (clear * - h; omega)), betaK_qcL (n - 1) (by (clear * - h; omega)), betaK_qcL n (by (clear * - h; omega)),
      qcL_rec 63 le_rfl (n - 1) (by (clear * - h; omega)), show 63 - 63 + (n - 1) + 1 = n by (clear * - h; omega),
      show n - 1 + 1 = n by (clear * - h; omega), add_assoc, CharTwo.add_self_eq_zero, add_zero, fC, fCoef]
    exact if_congr (by (clear * - h; omega)) rfl rfl
  · subst h
    rw [if_neg (by (clear * -; omega)), show 64 - 1 = 63 from rfl, betaK_qcL 63 (by (clear * -; omega)), qcL_last,
      betaK, if_neg (by (clear * -; omega)), mul_zero, add_zero, fC, if_pos (by simp)]

theorem quot_coeff (n : ℕ) : (if n = 0 then 0 else betaK (n - 1)) + FK.x * betaK n = fC n := by
  by_cases hn : n < 65
  · have := List.all_eq_true.mp quotOkB_true n (List.mem_range.mpr hn)
    exact beq_iff_eq.mp this
  · have h1 : betaK (n - 1) = 0 := if_neg (by (clear * - hn; omega))
    have h2 : betaK n = 0 := if_neg (by (clear * - hn; omega))
    rw [if_neg (by (clear * - hn; omega)), h1, h2, mul_zero, add_zero, fC, if_neg (by (clear * - hn; omega))]

/-- `f`. -/
def fPoly : FK[X] := X ^ 64 + X ^ 4 + X ^ 3 + X + 1

/-- `f/(y − x)`. -/
def bPoly : FK[X] := ∑ i ∈ range 64, C (betaK i) * X ^ i

theorem bPoly_coeff (n : ℕ) : bPoly.coeff n = betaK n := by
  rw [bPoly, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (if_neg (by simpa using h)).symm

theorem fPoly_coeff (n : ℕ) : fPoly.coeff n = fC n := by
  simp only [fPoly, coeff_add, coeff_X_pow, coeff_X, coeff_one, fC]
  rcases (show n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 64 ∨ (n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 64) by (clear * -; omega)) with
    h | h | h | h | h | ⟨h0, h1, h3, h4, h64⟩ <;> (simp [*] <;> (clear * - h1; omega))

/-- **`(y − x)·B = f`.** -/
theorem quot_mul : (X - C FK.x) * bPoly = fPoly := by
  ext n
  rw [fPoly_coeff, ← quot_coeff, sub_mul, coeff_sub, coeff_C_mul, bPoly_coeff, CharTwo.sub_eq_add]
  cases n with
  | zero => rw [coeff_X_mul_zero, if_pos rfl]
  | succ m => rw [coeff_X_mul, bPoly_coeff, if_neg (by omega), Nat.add_sub_cancel]

/-- The Frobenius power `σ^k`. -/
abbrev frobK (k : ℕ) : FK →+* FK := iterateFrobenius FK 2 k

theorem frobK_apply (k : ℕ) (a : FK) : frobK k a = a ^ 2 ^ k := iterateFrobenius_def ..

/-- The conjugate `α_k = x^(2^k)`. -/
def alphaK (k : ℕ) : FK := FK.x ^ 2 ^ k

/-- `B_k = f/(y − α_k)`. -/
def bK (k : ℕ) : FK[X] := bPoly.map (frobK k)

theorem fPoly_map (k : ℕ) : fPoly.map (frobK k) = fPoly := by
  simp only [fPoly, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]

theorem quot_mul_k (k : ℕ) : (X - C (alphaK k)) * bK k = fPoly := by
  have := congrArg (Polynomial.map (frobK k)) quot_mul
  rwa [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, fPoly_map, frobK_apply] at this

theorem fPoly_root (k : ℕ) : fPoly.eval (alphaK k) = 0 := by
  rw [← quot_mul_k k, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]

theorem alphaK_inj {k m : ℕ} (hk : k < 64) (hm : m < 64) (h : alphaK k = alphaK m) : k = m := by
  have hn := FK.conj_distinct
  rw [List.nodup_iff_injective_get] at hn
  have := @hn ⟨k, by simpa using hk⟩ ⟨m, by simpa using hm⟩ (by simpa [alphaK] using h)
  simpa using congrArg Fin.val this

theorem bK_eval_ne {k m : ℕ} (hk : k < 64) (hm : m < 64) (hkm : k ≠ m) : (bK k).eval (alphaK m) = 0 := by
  have h := congrArg (eval (alphaK m)) (quot_mul_k k)
  rw [eval_mul, eval_sub, eval_X, eval_C, fPoly_root] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr fun e => hkm (alphaK_inj hm hk e).symm)

theorem fk_cast_two (n : ℕ) : ((2 * n : ℕ) : FK) = 0 := by
  rw [Nat.cast_mul, show ((2 : ℕ) : FK) = 0 from CharP.cast_eq_zero FK 2, zero_mul]

/-- `f'(α) = α² + 1`. -/
theorem fPoly_derivative_eval (a : FK) : (derivative fPoly).eval a = a ^ 2 + 1 := by
  simp only [fPoly, derivative_add, derivative_X_pow, derivative_X, derivative_one, eval_add, eval_mul, eval_C,
    eval_pow, eval_X, eval_one, add_zero]
  rw [show ((64 : ℕ) : FK) = ((2 * 32 : ℕ) : FK) from rfl, fk_cast_two, show ((4 : ℕ) : FK) = ((2 * 2 : ℕ) : FK) from rfl,
    fk_cast_two, show ((3 : ℕ) : FK) = ((2 * 1 : ℕ) : FK) + 1 by push_cast; ring, fk_cast_two]
  ring

theorem bK_eval_self (k : ℕ) : (bK k).eval (alphaK k) = alphaK k ^ 2 + 1 := by
  have h := congrArg (fun p => (derivative p).eval (alphaK k)) (quot_mul_k k)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul,
    eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at h
  rw [h, fPoly_derivative_eval]

theorem x_sq_add_one_ne : FK.x ^ 2 + 1 ≠ 0 := by decide +kernel

theorem alpha_sq_add_one (k : ℕ) : alphaK k ^ 2 + 1 = frobK k (FK.x ^ 2 + 1) := by
  rw [map_add, map_pow, map_one, frobK_apply, alphaK]

theorem alpha_sq_add_one_ne (k : ℕ) : alphaK k ^ 2 + 1 ≠ 0 := by
  rw [alpha_sq_add_one]; exact (_root_.map_ne_zero _).mpr x_sq_add_one_ne

theorem bPoly_degree : bPoly.degree < 64 := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i hi => ?_)
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast List.mem_range.mp (by simpa using hi))

/-- **Lagrange at the conjugates**: `Σ_k α_k^j/f'(α_k)·B_k = y^j`, `j < 64`. -/
theorem lagrange_conj {j : ℕ} (hj : j < 64) :
    ∑ k ∈ range 64, C (alphaK k ^ j * (alphaK k ^ 2 + 1)⁻¹) * bK k = X ^ j := by
  refine eq_of_degree_sub_lt_of_eval_finset_eq ((range 64).image alphaK) ?_ fun a ha => ?_
  · rw [Finset.card_image_of_injOn fun k hk m hm h => alphaK_inj (by simpa using hk) (by simpa using hm) h,
      card_range]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun k _ => ?_)
      exact lt_of_le_of_lt (degree_mul_le _ _) (lt_of_le_of_lt (add_le_add degree_C_le (degree_map_le))
        (by rw [zero_add]; exact bPoly_degree))
    · rw [degree_X_pow]; exact_mod_cast hj
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hm' := Finset.mem_range.mp hm
    rw [eval_finset_sum, Finset.sum_eq_single m (fun k hk hkm => by
        rw [eval_mul, bK_eval_ne (Finset.mem_range.mp hk) hm' hkm, mul_zero]) (fun h => absurd hm h),
      eval_mul, eval_C, bK_eval_self, eval_pow, eval_X, mul_assoc, inv_mul_cancel₀ (alpha_sq_add_one_ne m), mul_one]

/-- **The trace-dual basis**: `Tr(δ_i x^j) = [i = j]`, `i, j < 64`. -/
theorem dual_trace {i j : ℕ} (hi : i < 64) (hj : j < 64) :
    ∑ k ∈ range 64, (dualK i * FK.x ^ j) ^ 2 ^ k = if i = j then 1 else 0 := by
  have h := congrArg (fun p => p.coeff i) (lagrange_conj hj)
  simp only [finset_sum_coeff, coeff_C_mul, bK, coeff_map, bPoly_coeff, coeff_X_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← frobK_apply, dualK, show FK.x * FK.x + 1 = FK.x ^ 2 + 1 by ring, map_mul, map_mul, map_inv₀, map_pow,
    ← alpha_sq_add_one, frobK_apply k FK.x, show betaK i = quotCoefs.getD i 0 from if_pos hi, ← alphaK]
  ring

/-! ## Bits -/

theorem xPowK_eq {i : ℕ} (hi : i < 64) : xPowK i = FK.x ^ i := by
  rw [FK.x_pow_word ⟨i, hi⟩]
  apply fk_eq_of_testBit
  intro m
  rw [xPowK_toNat hi]
  show (2 ^ i).testBit m = (((1 : UInt64) <<< i.toUInt64).toNat).testBit m
  rw [UInt64.toNat_shiftLeft, Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by (clear * - hi; omega) : i < 2 ^ 64),
    Nat.mod_eq_of_lt (by (clear * - hi; omega) : i < 64), UInt64.toNat_one, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi)]

/-- **A word is its bits packed by the powers of `x`.** -/
theorem fk_eq_sum_bits (a : FK) : a = ∑ i ∈ range 64, if a.val.toNat.testBit i then FK.x ^ i else 0 := by
  have hb : ∀ i < 64, (fun i => if a.val.toNat.testBit i then (1 : FK) else 0) i = 0 ∨
      (fun i => if a.val.toNat.testBit i then (1 : FK) else 0) i = 1 := fun i _ => by
    by_cases h : a.val.toNat.testBit i <;> simp [h]
  have e : a = bitsum (fun i => if a.val.toNat.testBit i then (1 : FK) else 0) 64 := by
    apply fk_eq_of_testBit
    intro m
    rw [testBit_bitsum _ hb 64 le_rfl m]
    by_cases hm : m < 64
    · by_cases h : a.val.toNat.testBit m <;> simp [hm, h, show (0 : FK) ≠ 1 by decide]
    · simp only [hm, decide_false, Bool.false_and]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le a.val.toNat_lt (Nat.pow_le_pow_right (by norm_num) (by (clear * - hm; omega))))
  conv_lhs => rw [e]
  rw [bitsum, lsum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [xPowK_eq (Finset.mem_range.mp hi)]
  split_ifs <;> simp

/-! ## The CRT components of V's tensor coordinates -/

/-- `(A + BX)(α + βX)` in `E3[X]/(X² + tX + 1)`. -/
def qm (t : FE) (a b : FE × FE) : FE × FE :=
  (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1 + t * (a.2 * b.2))

/-- Coordinate `h` of an `E2` value. -/
def crd (h : Bool) (y : FE2) : FK := if h then y.im else y.re

/-- The weight of coordinate `j < 128` (`β_j`) in half `h` of component `k`: `(x^i)^(2^k)` when `j = i + 64h`. -/
def wH (k : ℕ) (h : Bool) (j : ℕ) : FE := if decide (64 ≤ j) = h then FE.ofK ((FK.x ^ (j % 64)) ^ 2 ^ k) else 0

/-- Half `h` of component `k` of 128 `E3` coordinates. -/
def phiH (k : ℕ) (h : Bool) (v : Array FE) : FE := ∑ j ∈ range 128, wH k h j * v.getD j 0

/-- **Component `k`** (`K ⊗ E3 ≅ E3⁶⁴`, `a ⊗ e ↦ (a^(2^k) e)_k`, on both halves). -/
def phiA (k : ℕ) (v : Array FE) : FE × FE := (phiH k false v, phiH k true v)

/-- A factor's component: `(1 + z_re^(2^k) + r) + z_im^(2^k) X`. -/
def fct (k : ℕ) (zr : FE2 × FE) : FE × FE := (1 + FE.ofK (zr.1.re ^ 2 ^ k) + zr.2, FE.ofK (zr.1.im ^ 2 ^ k))

/-- The twist of component `k`: `x^(2^k)`. -/
def twK (k : ℕ) : FE := FE.ofK (FK.x ^ 2 ^ k)

theorem ofK_frob_sum (s : Finset ℕ) (f : ℕ → FK) (k : ℕ) :
    FE.ofK ((∑ i ∈ s, f i) ^ 2 ^ k) = ∑ i ∈ s, FE.ofK (f i ^ 2 ^ k) := by
  rw [← frobK_apply, map_sum, show FE.ofK (∑ i ∈ s, frobK k (f i)) = FE.ofKRingHom (∑ i ∈ s, frobK k (f i)) from rfl,
    map_sum]
  rfl

/-- **The bits of `y`, weighted**: `Σ_{j : bit j of y} w_h(j) = coord_h(y)^(2^k)`. -/
theorem sum_bits_wH (k : ℕ) (h : Bool) (y : FE2) :
    ∑ j ∈ range 128, (if bitFE2 y j then wH k h j else 0) = FE.ofK (crd h y ^ 2 ^ k) := by
  rw [show 128 = 64 + 64 from rfl, Finset.sum_range_add]
  have e1 : ∀ i ∈ range 64, (if bitFE2 y i then wH k h i else 0) =
      if h then 0 else FE.ofK ((if y.re.val.toNat.testBit i then FK.x ^ i else 0) ^ 2 ^ k) := fun i hi => by
    have hi' := Finset.mem_range.mp hi
    simp only [bitFE2, hi', if_true, wH, show ¬ 64 ≤ i by (clear * - hi'; omega), decide_false, Nat.mod_eq_of_lt hi']
    cases h <;> by_cases hb : y.re.val.toNat.testBit i <;> simp [hb, zero_pow (pow_ne_zero k two_ne_zero)] <;> rfl
  have e2 : ∀ i ∈ range 64, (if bitFE2 y (64 + i) then wH k h (64 + i) else 0) =
      if h then FE.ofK ((if y.im.val.toNat.testBit i then FK.x ^ i else 0) ^ 2 ^ k) else 0 := fun i hi => by
    have hi' := Finset.mem_range.mp hi
    simp only [bitFE2, show ¬ 64 + i < 64 by (clear * -; omega), if_false, wH, show 64 ≤ 64 + i by (clear * -; omega), decide_true,
      Nat.add_sub_cancel_left, show (64 + i) % 64 = i by (clear * - hi'; omega)]
    cases h <;> by_cases hb : y.im.val.toNat.testBit i <;> simp [hb, zero_pow (pow_ne_zero k two_ne_zero)] <;> rfl
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  cases h
  · simp only [Bool.false_eq_true, if_false, Finset.sum_const_zero, add_zero, crd]
    rw [← ofK_frob_sum, ← fk_eq_sum_bits]
  · simp only [if_true, Finset.sum_const_zero, zero_add, crd]
    rw [← ofK_frob_sum, ← fk_eq_sum_bits]

/-- `σ^k` on `E2`'s coordinates is multiplicative into the twisted algebra. -/
theorem crd_mul_frob (k : ℕ) (a b : FE2) :
    (FE.ofK (crd false (a * b) ^ 2 ^ k), FE.ofK (crd true (a * b) ^ 2 ^ k)) =
      qm (twK k) (FE.ofK (a.re ^ 2 ^ k), FE.ofK (a.im ^ 2 ^ k)) (FE.ofK (b.re ^ 2 ^ k), FE.ofK (b.im ^ 2 ^ k)) := by
  simp only [crd, Bool.false_eq_true, if_false, if_true, FE2.mul_def, qm, twK]
  simp only [← frobK_apply, map_add, map_mul, show ∀ u : FK, FE.ofK u = FE.ofKRingHom u from fun _ => rfl]

/-- The basis element `β_j`'s coordinates under `σ^k`: the weights `wH k h j`. -/
theorem crd_basis (k : ℕ) (h : Bool) {j : ℕ} (hj : j < 128) : FE.ofK (crd h (basisFE2 j) ^ 2 ^ k) = wH k h j := by
  have hw : ∀ i < 64, (⟨(2 ^ i : ℕ).toUInt64⟩ : FK) = FK.x ^ i := fun i hi => (xPowK_eq hi).symm ▸ rfl
  by_cases hj64 : j < 64
  · simp only [basisFE2, hj64, if_true, crd, wH, show ¬ 64 ≤ j by (clear * - hj64; omega), decide_false, Nat.mod_eq_of_lt hj64]
    cases h
    · simp [hw j hj64]
    · simp [zero_pow (pow_ne_zero k two_ne_zero)]; rfl
  · simp only [basisFE2, hj64, if_false, crd, wH, show 64 ≤ j by (clear * - hj64; omega), decide_true]
    cases h
    · simp [zero_pow (pow_ne_zero k two_ne_zero)]; rfl
    · simp [hw (j - 64) (by (clear * - hj; omega)), show j % 64 = j - 64 by (clear * - hj hj64; omega)]

theorem getD_range_map {α : Type} (f : ℕ → α) (d : α) {n j : ℕ} (hj : j < n) :
    ((List.range n).toArray.map f).getD j d = f j := by
  simp [Array.getD_eq_getD_getElem?, hj]

theorem getD_modify (acc : Array FE) (i j : ℕ) (c : FE) :
    (acc.modify i (· + c)).getD j 0 = acc.getD j 0 + if i = j ∧ j < acc.size then c else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hij : i = j
  · subst hij
    by_cases hj : i < acc.size <;> simp [hj]
  · simp [hij]

theorem fold_modify (c : FE) (j : ℕ) : ∀ (L : List ℕ) (acc : Array FE),
    (L.foldl (fun acc l => acc.modify l (· + c)) acc).getD j 0 =
      acc.getD j 0 + (if j < acc.size then (L.map fun l => if l = j then c else 0).sum else 0) ∧
    (L.foldl (fun acc l => acc.modify l (· + c)) acc).size = acc.size
  | [], acc => by simp
  | l :: L, acc => by
    obtain ⟨h1, h2⟩ := fold_modify c j L (acc.modify l (· + c))
    rw [List.foldl_cons, Array.size_modify] at *
    refine ⟨?_, h2⟩
    rw [h1, getD_modify]
    by_cases hj : j < acc.size <;> simp [hj, List.sum_cons, add_assoc]

theorem lsum_filter (P : ℕ → Bool) (f : ℕ → FE) : ∀ L : List ℕ,
    ((L.filter P).map f).sum = (L.map fun l => if P l then f l else 0).sum
  | [] => rfl
  | l :: L => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← lsum_filter P f L]
    by_cases hl : P l <;> simp [hl]

/-- The scatter of `tensorStepD` (`mz`): entry `j < 128` is `Σ_{k : bit j of β_k z} v_k`. -/
theorem mz_getD (v : Array FE) (z : FE2) {j : ℕ} (hj : j < 128) :
    ((List.range 128).foldl (fun acc k =>
      ((((List.range 128).toArray.map fun k => (List.range 128).filter fun j => bitFE2 (basisFE2 k * z) j).getD k
        []).foldl (fun acc j => acc.modify j (· + v.getD k 0)) acc)) (Array.replicate 128 0)).getD j 0 =
      ∑ k ∈ range 128, if bitFE2 (basisFE2 k * z) j then v.getD k 0 else 0 := by
  have hgen : ∀ (Ks : List ℕ), (∀ k ∈ Ks, k < 128) → ∀ acc : Array FE, acc.size = 128 →
      (Ks.foldl (fun acc k =>
        ((((List.range 128).toArray.map fun k => (List.range 128).filter fun j => bitFE2 (basisFE2 k * z) j).getD k
          []).foldl (fun acc j => acc.modify j (· + v.getD k 0)) acc)) acc).getD j 0 =
        acc.getD j 0 + (Ks.map fun k => if bitFE2 (basisFE2 k * z) j then v.getD k 0 else 0).sum := by
    intro Ks
    induction Ks with
    | nil => intro _ acc _; simp
    | cons k Ks ih =>
      intro hK acc hacc
      have hk := hK k (List.mem_cons_self ..)
      rw [List.foldl_cons, getD_range_map _ _ hk]
      obtain ⟨h1, h2⟩ := fold_modify (v.getD k 0) j ((List.range 128).filter fun j => bitFE2 (basisFE2 k * z) j) acc
      rw [ih (fun k' hk' => hK k' (List.mem_cons_of_mem _ hk')) _ (by rw [h2, hacc]), h1, if_pos (by (clear * - hj hacc; omega)),
        lsum_filter, lsum_range, Finset.sum_eq_single j (fun i _ hij => by simp [hij])
          (fun h => absurd (Finset.mem_range.mpr hj) h)]
      simp only [if_true, List.map_cons, List.sum_cons]
      ring
  rw [hgen _ (fun k hk => List.mem_range.mp hk) _ (by simp), lsum_range]
  simp [Array.getD_eq_getD_getElem?, hj]

/-- Half `h` of component `k` after one factor (before the CRT product form). -/
theorem phiH_step (k : ℕ) (h : Bool) (v : Array FE) (zr : FE2 × FE) :
    phiH k h (tensorStepD v zr) =
      (1 + zr.2) * phiH k h v + ∑ k' ∈ range 128, v.getD k' 0 * FE.ofK (crd h (basisFE2 k' * zr.1) ^ 2 ^ k) := by
  unfold phiH tensorStepD
  dsimp only
  have e : ∀ j ∈ range 128, wH k h j * ((List.range 128).toArray.map fun j => (1 + zr.2) * v.getD j 0 +
      ((List.range 128).foldl (fun acc k =>
        ((((List.range 128).toArray.map fun k => (List.range 128).filter fun j => bitFE2 (basisFE2 k * zr.1) j).getD k
          []).foldl (fun acc j => acc.modify j (· + v.getD k 0)) acc)) (Array.replicate 128 0)).getD j 0).getD j 0 =
      (1 + zr.2) * (wH k h j * v.getD j 0) +
        ∑ k' ∈ range 128, if bitFE2 (basisFE2 k' * zr.1) j then v.getD k' 0 * wH k h j else 0 := fun j hj => by
    have hj' := Finset.mem_range.mp hj
    rw [getD_range_map _ _ hj', mz_getD v zr.1 hj', mul_add, Finset.mul_sum]
    exact congrArg₂ (· + ·) (mul_left_comm _ _ _) (Finset.sum_congr rfl fun k' _ => by
      split_ifs
      · exact mul_comm _ _
      · exact mul_zero _)
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  refine congrArg ((1 + zr.2) * phiH k h v + ·) (Finset.sum_congr rfl fun k' _ => ?_)
  rw [← sum_bits_wH, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp

/-- **One factor of V's tensor product is a product in every component.** -/
theorem phiA_step (k : ℕ) (v : Array FE) (zr : FE2 × FE) :
    phiA k (tensorStepD v zr) = qm (twK k) (phiA k v) (fct k zr) := by
  have hm := fun k' => crd_mul_frob k (basisFE2 k') zr.1
  have hsum : ∀ h : Bool, ∑ k' ∈ range 128, v.getD k' 0 * FE.ofK (crd h (basisFE2 k' * zr.1) ^ 2 ^ k) =
      if h then phiH k false v * FE.ofK (zr.1.im ^ 2 ^ k) + phiH k true v * FE.ofK (zr.1.re ^ 2 ^ k) +
          twK k * (phiH k true v * FE.ofK (zr.1.im ^ 2 ^ k))
        else phiH k false v * FE.ofK (zr.1.re ^ 2 ^ k) + phiH k true v * FE.ofK (zr.1.im ^ 2 ^ k) := by
    intro h
    have e : ∀ k' ∈ range 128, v.getD k' 0 * FE.ofK (crd h (basisFE2 k' * zr.1) ^ 2 ^ k) =
        if h then wH k false k' * v.getD k' 0 * FE.ofK (zr.1.im ^ 2 ^ k) +
            wH k true k' * v.getD k' 0 * FE.ofK (zr.1.re ^ 2 ^ k) +
            twK k * (wH k true k' * v.getD k' 0 * FE.ofK (zr.1.im ^ 2 ^ k))
          else wH k false k' * v.getD k' 0 * FE.ofK (zr.1.re ^ 2 ^ k) +
            wH k true k' * v.getD k' 0 * FE.ofK (zr.1.im ^ 2 ^ k) := fun k' hk' => by
      have hk'' := Finset.mem_range.mp hk'
      have e0 := congrArg Prod.fst (hm k')
      have e1 := congrArg Prod.snd (hm k')
      simp only [qm] at e0 e1
      rw [show FE.ofK ((basisFE2 k').re ^ 2 ^ k) = wH k false k' from crd_basis k false hk'',
        show FE.ofK ((basisFE2 k').im ^ 2 ^ k) = wH k true k' from crd_basis k true hk''] at e0 e1
      cases h
      · rw [e0]; simp only [Bool.false_eq_true, if_false]; ring
      · rw [e1]; simp only [if_true]; ring
    rw [Finset.sum_congr rfl e]
    cases h
    · simp only [Bool.false_eq_true, if_false, Finset.sum_add_distrib, ← Finset.sum_mul, phiH]
    · simp only [if_true, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, phiH]
  unfold phiA
  rw [phiH_step, phiH_step, hsum, hsum]
  simp only [Bool.false_eq_true, if_false, if_true, qm, fct]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> ring

theorem phiA_init (k : ℕ) :
    phiA k ((List.range 128).toArray.map fun j => if j = 0 then (1 : FE) else 0) = (1, 0) := by
  unfold phiA phiH
  have e : ∀ h : Bool, ∑ j ∈ range 128, wH k h j * ((List.range 128).toArray.map fun j =>
      if j = 0 then (1 : FE) else 0).getD j 0 = wH k h 0 := fun h => by
    rw [Finset.sum_congr rfl fun j hj => by rw [getD_range_map _ _ (Finset.mem_range.mp hj)]]
    simp
  rw [e, e]
  simp [wH]
  rfl

/-- **V's tensor coordinates by components**: `Φ_k(tensorW(z, r)) = Π_l ((1 + z_l^(2^k) + r_l) + …X)`. -/
theorem phiA_tensorWD (k : ℕ) (z : List FE2) (r : List FE) :
    phiA k (tensorWD z r) = (List.zip z r).foldl (fun P zr => qm (twK k) P (fct k zr)) (1, 0) := by
  unfold tensorWD
  rw [← phiA_init k]
  generalize ((List.range 128).toArray.map fun j => if j = 0 then (1 : FE) else 0) = v0
  induction (List.zip z r) generalizing v0 with
  | nil => rfl
  | cons zr L ih => rw [List.foldl_cons, List.foldl_cons, ih, phiA_step]

/-! ## The weight by components -/

/-- Half `h` of component `k` on the 64 coordinates `i + 64h`. -/
theorem phiH_split (k : ℕ) (h : Bool) (v : Array FE) :
    phiH k h v = ∑ i ∈ range 64, FE.ofK ((FK.x ^ i) ^ 2 ^ k) * v.getD (i + if h then 64 else 0) 0 := by
  unfold phiH
  rw [show 128 = 64 + 64 from rfl, Finset.sum_range_add]
  have e1 : ∀ i ∈ range 64, wH k h i * v.getD i 0 = if h then 0 else FE.ofK ((FK.x ^ i) ^ 2 ^ k) * v.getD i 0 :=
    fun i hi => by
      have hi' := Finset.mem_range.mp hi
      cases h <;> simp [wH, show ¬ 64 ≤ i by (clear * - hi'; omega), Nat.mod_eq_of_lt hi']
  have e2 : ∀ i ∈ range 64, wH k h (64 + i) * v.getD (64 + i) 0 =
      if h then FE.ofK ((FK.x ^ i) ^ 2 ^ k) * v.getD (i + 64) 0 else 0 := fun i hi => by
    have hi' := Finset.mem_range.mp hi
    cases h <;> simp [wH, Nat.mod_eq_of_lt hi', Nat.add_comm 64 i]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  cases h <;> simp

/-- `ν`'s coefficients: `δ_i^(2^k)`. -/
def dK (k i : ℕ) : FE := FE.ofK (dualK i ^ 2 ^ k)

/-- **The dual pairing**: `Σ_k (Σ_i δ_i^(2^k) u_i)(Σ_i (x^i)^(2^k) w_i) = Σ_i u_i w_i`. -/
theorem dual_pair (u w : ℕ → FE) :
    ∑ k ∈ range 64, (∑ i ∈ range 64, dK k i * u i) * (∑ i ∈ range 64, FE.ofK ((FK.x ^ i) ^ 2 ^ k) * w i) =
      ∑ i ∈ range 64, u i * w i := by
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  have e : ∀ i' ∈ range 64, ∑ k ∈ range 64, dK k i * u i * (FE.ofK ((FK.x ^ i') ^ 2 ^ k) * w i') =
      if i = i' then u i * w i' else 0 := fun i' hi' => by
    have h1 : ∀ k ∈ range 64, dK k i * u i * (FE.ofK ((FK.x ^ i') ^ 2 ^ k) * w i') =
        FE.ofK ((dualK i * FK.x ^ i') ^ 2 ^ k) * (u i * w i') := fun k _ => by
      rw [dK, mul_pow, show FE.ofK (dualK i ^ 2 ^ k * (FK.x ^ i') ^ 2 ^ k) =
        FE.ofKRingHom (dualK i ^ 2 ^ k * (FK.x ^ i') ^ 2 ^ k) from rfl, map_mul]
      show FE.ofK _ * u i * (FE.ofK _ * w i') = FE.ofK _ * FE.ofK _ * (u i * w i')
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul,
      show ∑ k ∈ range 64, FE.ofK ((dualK i * FK.x ^ i') ^ 2 ^ k) =
        FE.ofK (∑ k ∈ range 64, (dualK i * FK.x ^ i') ^ 2 ^ k) from (map_sum FE.ofKRingHom _ _).symm,
      dual_trace (Finset.mem_range.mp hi) (Finset.mem_range.mp hi')]
    split_ifs
    · show FE.ofK 1 * _ = _; rw [show FE.ofK 1 = 1 from rfl, one_mul]
    · show FE.ofK 0 * _ = _; rw [show FE.ofK 0 = 0 from rfl, zero_mul]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq (range 64) i, if_pos hi]

/-- `ν` of half `h`: `Σ_i δ_i^(2^k) ρ_{i + 64h}`. -/
def nuH (ρ : ℕ → FE) (h : Bool) (k : ℕ) : FE := ∑ i ∈ range 64, dK k i * ρ (i + if h then 64 else 0)

/-- **The weight by the CRT**: `Σ_{j<128} ρ_j v_j = Σ_k ν₀_k Φ_k(v)₀ + ν₁_k Φ_k(v)₁`. -/
theorem weight_crt (ρ : ℕ → FE) (v : Array FE) :
    ∑ j ∈ range 128, ρ j * v.getD j 0 =
      ∑ k ∈ range 64, (nuH ρ false k * (phiA k v).1 + nuH ρ true k * (phiA k v).2) := by
  rw [Finset.sum_add_distrib]
  simp only [phiA, phiH_split, nuH]
  rw [dual_pair, dual_pair, show 128 = 64 + 64 from rfl, Finset.sum_range_add]
  simp only [Bool.false_eq_true, if_false, if_true, Nat.add_zero, Nat.add_comm 64]

/-! ## The gadgets -/

section Gadgets

open Lvm.Loop Lvm.Loop.Build Lvm.Har

variable {c : Ctx} {M : Mem}

theorem hs_mapB_getD {α β : Type} (f : α → BM β) (P : α → β → Prop) (d : α) (e : β) :
    ∀ l : List α, (∀ a ∈ l, Hs c M (f a) (P a)) →
      Hs c M (mapB f l) (fun rs => rs.length = l.length ∧ ∀ i < l.length, P (l.getD i d) (rs.getD i e))
  | [], _ => hs_pure ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | a :: l, hf => hs_bind (hf a (List.mem_cons_self ..)) fun r hr =>
    hs_bind (hs_mapB_getD f P d e l fun b hb => hf b (List.mem_cons_of_mem _ hb)) fun rs ⟨hl, hrs⟩ =>
    hs_pure ⟨by simp [hl], fun i hi => by
      cases i with
      | zero => exact hr
      | succ i => exact hrs i (by simpa using hi)⟩

/-- **The Frobenius powers**: entry `k < 64` of `frobsK zk a` is `a^(2^k)`. -/
theorem hs_frobsK {zk : Cell} (hzk : zk.val M = 0) (a : Cell) :
    Hs c M (frobsK zk a) (fun l => ∀ k < 64, (l.getD k default).val M = a.val M ^ 2 ^ k) := by
  have hgen : ∀ n, Hs c M ((List.range n).foldl (fun (m : BM (List Cell)) _ => m >>= fun l =>
      mulAdd .K (l.getD 0 default) (l.getD 0 default) zk >>= fun s => pure (s :: l)) (pure [a]))
      (fun l => l.length = n + 1 ∧ ∀ i ≤ n, (l.getD i default).val M = a.val M ^ 2 ^ (n - i)) := by
    intro n
    induction n with
    | zero => exact hs_pure ⟨rfl, fun i hi => by obtain rfl : i = 0 := by (clear * - hi; omega)
                                                 simp⟩
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine hs_bind ih fun l ⟨hl, hv⟩ => hs_bind (hs_mulAdd _ _ _ _) fun s hs => hs_pure ⟨by simp [hl], ?_⟩
      intro i hi
      cases i with
      | zero =>
        rw [List.getD_cons_zero, hs, hzk, add_zero, hv 0 (by (clear * -; omega)), ← pow_two, ← pow_mul, Nat.sub_zero,
          Nat.sub_zero, pow_succ]
      | succ i => rw [List.getD_cons_succ, hv i (by (clear * - hi; omega)), show n + 1 - (i + 1) = n - i by (clear * -; omega)]
  unfold frobsK
  refine hs_bind (hgen 63) fun l ⟨hl, hv⟩ => hs_pure fun k hk => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by (clear * - hl hk; omega)), hl, ← List.getD_eq_getElem?_getD,
    hv _ (by (clear * -; omega)), show 63 + 1 - 1 - k = 63 - k by (clear * -; omega), show 63 - (63 - k) = k by (clear * - hk; omega)]

/-- The Frobenius powers of a `C2` value. -/
theorem hs_frob2 {zk : Cell} (hzk : zk.val M = 0) (x : C2) :
    Hs c M (frobsK zk x.re >>= fun fr => frobsK zk x.im >>= fun fi => pure (⟨fr, fi⟩ : Frob2))
      (fun F => ∀ k < 64, (F.re.getD k default).val M = x.re.val M ^ 2 ^ k ∧
        (F.im.getD k default).val M = x.im.val M ^ 2 ^ k) :=
  hs_bind (hs_frobsK hzk _) fun _ h1 => hs_bind (hs_frobsK hzk _) fun _ h2 => hs_pure fun k hk => ⟨h1 k hk, h2 k hk⟩

theorem qm_one (t : FE) (b : FE × FE) : qm t (1, 0) b = b := by
  simp only [qm]; exact Prod.ext (by ring) (by ring)

/-- `qmul` is `qm`. -/
theorem hs_qmul (t : FK) {z : Cell} (hz : z.val M = 0) (A B α β : Cell) :
    Hs c M (qmul t z A B α β) (fun r => (r.1.val M, r.2.val M) = qm (FE.ofK t) (A.val M, B.val M) (α.val M, β.val M)) := by
  unfold qmul
  refine hs_bind (hs_mulAdd _ _ _ _) fun q hq => hs_bind (hs_mulAdd _ _ _ _) fun re hre =>
    hs_bind (hs_lin _ _ _ _ _) fun tq htq => hs_bind (hs_mulAdd _ _ _ _) fun i1 hi1 =>
    hs_bind (hs_mulAdd _ _ _ _) fun im him => hs_pure ?_
  rw [hz, add_zero] at hq
  have h1 : FE.ofK (t + 1) = FE.ofK t + 1 := map_add FE.ofKRingHom t 1
  have h0 : FE.ofK 0 = 0 := rfl
  rw [h1, h0, add_zero, hq] at htq
  simp only [qm]
  refine Prod.ext ?_ ?_
  · show re.val M = _; rw [hre, hq]
  · show im.val M = _
    rw [him, hi1, htq]
    linear_combination (B.val M * β.val M) * CharTwo.two_eq_zero (R := FE)

/-- The value of a factor `(f, r)` in component `k`. -/
def fctV (M : Mem) (k : ℕ) (fr : Frob2 × Option Cell) : FE × FE :=
  match fr.2 with
  | some x => (1 + (fr.1.re.getD k default).val M + x.val M, (fr.1.im.getD k default).val M)
  | none => ((fr.1.re.getD k default).val M, (fr.1.im.getD k default).val M)

theorem hs_factorK (k : ℕ) (fr : Frob2 × Option Cell) :
    Hs c M (factorK k fr.1 fr.2) (fun ab => (ab.1.val M, ab.2.val M) = fctV M k fr) := by
  obtain ⟨f, r⟩ := fr
  cases r with
  | none => exact hs_pure rfl
  | some x =>
    refine hs_bind (hs_lin _ _ _ _ _) fun a ha => hs_pure ?_
    simp only [fctV]
    rw [ha, show FE.ofK 1 = 1 from rfl, one_mul]
    exact Prod.ext (by dsimp only; ring) rfl

/-- **A component's product** (`compK`): the `qm`-product of the factors' values. -/
theorem hs_compK {z : Cell} (hz : z.val M = 0) (k : ℕ) {fs : List (Frob2 × Option Cell)} (hfs : fs ≠ []) :
    Hs c M (compK z k fs) (fun r => (r.1.val M, r.2.val M) = (fs.map (fctV M k)).foldl (qm (twK k)) (1, 0)) := by
  obtain ⟨f0, fs, rfl⟩ : ∃ f0 fs', fs = f0 :: fs' := by
    cases fs with
    | nil => exact absurd rfl hfs
    | cons f0 fs' => exact ⟨f0, fs', rfl⟩
  unfold compK
  have hgen : ∀ (fs : List (Frob2 × Option Cell)) (m : BM (Cell × Cell)) (v : FE × FE),
      Hs c M m (fun r => (r.1.val M, r.2.val M) = v) →
      Hs c M (fs.foldl (fun (m : BM (Cell × Cell)) (fr : Frob2 × Option Cell) => m >>= fun acc =>
        factorK k fr.1 fr.2 >>= fun ab => qmul (twist k) z acc.1 acc.2 ab.1 ab.2) m)
        (fun r => (r.1.val M, r.2.val M) = (fs.map (fctV M k)).foldl (qm (twK k)) v) := by
    intro fs
    induction fs with
    | nil => intro m v hm; exact hm
    | cons fr fs ih =>
      intro m v hm
      rw [List.foldl_cons, List.map_cons, List.foldl_cons]
      refine ih _ _ (hs_bind hm fun acc hacc => hs_bind (hs_factorK k fr) fun ab hab =>
        hs_mono (hs_qmul _ hz _ _ _ _) fun r hr => ?_)
      rw [hr, show FE.ofK (twist k) = twK k by rw [twist, FK.frob_eq_pow]; rfl, hacc, hab]
  refine hs_bind (hs_factorK k f0) fun a0 ha0 => ?_
  rw [List.map_cons, List.foldl_cons, qm_one]
  exact hgen fs (pure a0) _ (hs_pure ha0)

/-- **The leaf's cells**: `Σ_k ν0_k·A_k + ν1_k·B_k`, `(A_k, B_k)` the component products. -/
theorem hs_rowLeafG (nu : RowNu) (zs : List C2) (κ : Option C2) (xb : ℕ) {z zk : Cell} (hz : z.val M = 0)
    (hzk : zk.val M = 0) (hne : zs ≠ []) :
    Hs c M (rowLeafG nu zs κ xb z zk) (fun r => ∃ fs : List (Frob2 × Option Cell), fs ≠ [] ∧
      (∀ k < 64, (fs.map (fctV M k)) =
        (List.range zs.length).map (fun l => (1 + (zs.getD l default).re.val M ^ 2 ^ k + M.e (xb + l),
          (zs.getD l default).im.val M ^ 2 ^ k)) ++
        (match κ with
          | some cκ => [(cκ.re.val M ^ 2 ^ k, cκ.im.val M ^ 2 ^ k)]
          | none => [])) ∧
      r.val M = ∑ k ∈ range 64, ((nu.nu0.getD k default).val M * ((fs.map (fctV M k)).foldl (qm (twK k)) (1, 0)).1 +
        (nu.nu1.getD k default).val M * ((fs.map (fctV M k)).foldl (qm (twK k)) (1, 0)).2)) := by
  unfold rowLeafG
  refine hs_bind (hs_mapB_getD _ (fun x F => ∀ k < 64, (F.re.getD k default).val M = x.re.val M ^ 2 ^ k ∧
    (F.im.getD k default).val M = x.im.val M ^ 2 ^ k) default ⟨[], []⟩ zs fun x _ => hs_frob2 hzk x)
    fun fz ⟨hfl, hfz⟩ => ?_
  refine hs_bind (P := fun fk : List (Frob2 × Option Cell) => ∀ k < 64, fk.map (fctV M k) =
      match κ with
      | some cκ => [(cκ.re.val M ^ 2 ^ k, cκ.im.val M ^ 2 ^ k)]
      | none => []) ?_ fun fk hfk => ?_
  · cases κ with
    | none => exact hs_pure fun k _ => rfl
    | some cκ =>
      exact hs_bind (hs_frobsK hzk _) fun fr hfr => hs_bind (hs_frobsK hzk _) fun fi hfi =>
        hs_pure fun k hk => by
          simp only [List.map_cons, List.map_nil, fctV]
          rw [hfr k hk, hfi k hk]
  · set fs := (List.range zs.length).map (fun l => (fz.getD l ⟨[], []⟩, some (ec (xb + l)))) ++ fk with hfsdef
    have hfsne : fs ≠ [] := by
      rw [hfsdef]; intro h
      have := congrArg List.length h
      simp only [List.length_append, List.length_map, List.length_range, List.length_nil] at this
      exact hne (List.eq_nil_of_length_eq_zero (by (clear * - this; omega)))
    refine hs_bind (hs_mapB_getD _ (fun k (P : Cell × Cell) => (P.1.val M, P.2.val M) =
      (fs.map (fctV M k)).foldl (qm (twK k)) (1, 0)) 0 (z, z) (List.range 64)
      fun k _ => hs_compK hz k hfsne) fun P ⟨hPl, hP⟩ => ?_
    refine hs_bind (P := fun z0 => z0 = z) (hs_pure rfl) fun z0 hz0 => ?_
    have hgen : ∀ n ≤ 64, Hs c M ((List.range n).foldl (fun (m : BM Cell) k => m >>= fun acc =>
        mulAdd .E (nu.nu0.getD k default) (P.getD k (z, z)).1 acc >>= fun a1 =>
        mulAdd .E (nu.nu1.getD k default) (P.getD k (z, z)).2 a1) (pure z0))
        (fun r => r.val M = ∑ k ∈ range n, ((nu.nu0.getD k default).val M * ((fs.map (fctV M k)).foldl
          (qm (twK k)) (1, 0)).1 + (nu.nu1.getD k default).val M * ((fs.map (fctV M k)).foldl (qm (twK k)) (1, 0)).2)) := by
      intro n hn
      induction n with
      | zero => exact hs_pure (by rw [hz0, hz, Finset.sum_range_zero])
      | succ n ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        refine hs_bind (ih (by (clear * - hn; omega))) fun acc hacc => hs_bind (hs_mulAdd _ _ _ _) fun a1 ha1 =>
          hs_mono (hs_mulAdd _ _ _ _) fun r hr => ?_
        have hPn := hP n (by simp; (clear * - hn; omega))
        rw [show (List.range 64).getD n 0 = n by simp [List.getD_eq_getElem?_getD, show n < 64 by (clear * - hn; omega)]] at hPn
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hPn
        dsimp only at h1 h2
        rw [hr, ha1, hacc, Finset.sum_range_succ, ← h1, ← h2]
        ring
    refine hs_mono (hgen 64 le_rfl) fun r hr => ⟨fs, hfsne, fun k hk => ?_, hr⟩
    rw [hfsdef, List.map_append, hfk k hk, List.map_map]
    congr 1
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    have := hfz l (by (clear * - hl'; omega)) k hk
    simp only [Function.comp_apply, fctV, Cell.val_E]
    rw [this.1, this.2]

theorem hs_linSumE : ∀ (acc : Cell) (l : List (FK × Cell)),
    Hs c M (linSumE acc l) (fun r => r.val M = acc.val M + (l.map fun e => FE.ofK e.1 * e.2.val M).sum)
  | acc, [] => hs_pure (by simp)
  | acc, (k, a) :: l => hs_bind (hs_lin _ _ _ _ _) fun a' ha' => hs_mono (hs_linSumE a' l) fun r hr => by
    rw [hr, ha', List.map_cons, List.sum_cons, show FE.ofK 0 = 0 from rfl, add_zero, add_assoc]

theorem dualAt_eq {k i : ℕ} (hk : k < 64) (hi : i < 64) : FE.ofK (dualAt k i) = dK k i := by
  rw [dualAt, dualTab, getD_range_map _ _ hk, getD_range_map _ _ hi, FK.frob_eq_pow]; rfl

/-- **`ν` of a switch** (`rowNuG`): on an `eq` table split by its last coordinate `r₆`
(`ρ_i = (ρ_i + ρ_{64+i})(1 + r₆)`, `ρ_{64+i} = (ρ_i + ρ_{64+i}) r₆`), the cells are `ν₀ = nuH ρ false`,
`ν₁ = nuH ρ true`. -/
theorem hs_rowNuG (rw : RowOut) {z o : ℕ} (hz : M.e z = 0) (ho : M.e o = 1)
    (hρ : ∀ i < 64, (rw.eqR.getD i default).val M =
        ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) * (1 + (rw.rr.getD 6 default).val M) ∧
      (rw.eqR.getD (i + 64) default).val M =
        ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) * (rw.rr.getD 6 default).val M) :
    Hs c M (rowNuG rw z o) (fun nu => ∀ k < 64,
      (nu.nu0.getD k default).val M = nuH (fun j => (rw.eqR.getD j default).val M) false k ∧
      (nu.nu1.getD k default).val M = nuH (fun j => (rw.eqR.getD j default).val M) true k) := by
  unfold rowNuG
  have hlin : ∀ a b : Cell, Hs c M (add a b) (fun r => r.val M = a.val M + b.val M) := fun a b =>
    hs_mono (hs_lin _ _ _ _ _) fun r hr => by rw [hr, show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl]; ring
  refine hs_bind (hs_mapB_getD _ (fun i (r : Cell) => r.val M = (rw.eqR.getD i default).val M +
    (rw.eqR.getD (i + 64) default).val M) 0 default (List.range 64) fun i _ => hlin _ _) fun e ⟨hel, he⟩ => ?_
  have he' : ∀ i < 64, (e.getD i default).val M = (rw.eqR.getD i default).val M +
      (rw.eqR.getD (i + 64) default).val M := fun i hi => by
    have := he i (by simpa using hi)
    rwa [show (List.range 64).getD i 0 = i by simp [List.getD_eq_getElem?_getD, hi]] at this
  refine hs_bind (hs_mapB_getD _ (fun k (r : Cell) => r.val M = ∑ i ∈ range 64, dK k i *
    ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M)) 0 default (List.range 64)
    fun k hk => hs_mono (hs_linSumE _ _) fun r hr => ?_) fun nu ⟨hnl, hnu⟩ => ?_
  · rw [hr, Cell.val_E, hz, zero_add, List.map_map, lsum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Function.comp_apply]
    rw [dualAt_eq (List.mem_range.mp hk) (Finset.mem_range.mp hi), he' i (Finset.mem_range.mp hi)]
  have hnu' : ∀ k < 64, (nu.getD k default).val M = ∑ i ∈ range 64, dK k i *
      ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) := fun k hk => by
    have := hnu k (by simpa using hk)
    rwa [show (List.range 64).getD k 0 = k by simp [List.getD_eq_getElem?_getD, hk]] at this
  refine hs_bind (hlin _ _) fun r6' hr6' => ?_
  refine hs_bind (hs_mapB_getD _ (fun k (r : Cell) => r.val M = (nu.getD k default).val M * r6'.val M) 0 default
    (List.range 64) fun k _ => hs_mono (hs_mulAdd _ _ _ _) fun r hr => by rw [hr, Cell.val_E, hz, add_zero])
    fun nu0 ⟨_, hn0⟩ => ?_
  refine hs_bind (hs_mapB_getD _ (fun k (r : Cell) => r.val M = (nu.getD k default).val M *
    (rw.rr.getD 6 default).val M) 0 default (List.range 64)
    fun k _ => hs_mono (hs_mulAdd _ _ _ _) fun r hr => by rw [hr, Cell.val_E, hz, add_zero]) fun nu1 ⟨_, hn1⟩ => ?_
  refine hs_pure fun k hk => ⟨?_, ?_⟩
  · have := hn0 k (by simpa using hk)
    rw [show (List.range 64).getD k 0 = k by simp [List.getD_eq_getElem?_getD, hk]] at this
    show (nu0.getD k default).val M = _
    rw [this, hnu' k hk, hr6', Cell.val_E, ho, nuH, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg Bool.false_ne_true, Nat.add_zero]
    linear_combination (-(dK k i)) * (hρ i (Finset.mem_range.mp hi)).1
  · have := hn1 k (by simpa using hk)
    rw [show (List.range 64).getD k 0 = k by simp [List.getD_eq_getElem?_getD, hk]] at this
    show (nu1.getD k default).val M = _
    rw [this, hnu' k hk, nuH, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos rfl]
    linear_combination (-(dK k i)) * (hρ i (Finset.mem_range.mp hi)).2


/-! ## The leaf is V's weight -/

theorem getD_map_lt {l : List FE} {f : FE → FE} {i : ℕ} (hi : i < l.length) : (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

theorem eqKernel_split (rr : List FE) (hl : rr.length = 7) {i : ℕ} (hi : i < 64) :
    (eqKernel rr).getD i 0 = (eqKernel (rr.take 6)).getD i 0 * (1 + rr.getD 6 0) ∧
      (eqKernel rr).getD (i + 64) 0 = (eqKernel (rr.take 6)).getD i 0 * rr.getD 6 0 := by
  have hr : rr = rr.take 6 ++ [rr.getD 6 0] := by
    apply List.ext_getElem
    · simp [hl]
    · intro n h1 h2
      by_cases hn : n < 6
      · rw [List.getElem_append_left (by simp [hl, hn])]; simp
      · have : n = 6 := by (clear * - hl h1 hn; omega)
        subst this
        rw [List.getElem_append_right (by simp [hl])]
        simp [List.getD_eq_getElem?_getD, hl]
  have e1 : eqKernel rr = (eqKernel (rr.take 6)).map (· * (1 + rr.getD 6 0)) ++
      (eqKernel (rr.take 6)).map (· * rr.getD 6 0) := by
    conv_lhs => rw [hr]
    simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hL : (eqKernel (rr.take 6)).length = 64 := by rw [Lvm.Q1.eqKernel_length_lk]; simp [hl]
  rw [e1]
  refine ⟨?_, ?_⟩
  · rw [List.getD_append _ _ _ _ (by rw [List.length_map, hL]; exact hi), getD_map_lt (by rw [hL]; exact hi)]
  · rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, hL]; (clear * -; omega)), List.length_map, hL,
      Nat.add_sub_cancel, getD_map_lt (by rw [hL]; exact hi)]

/-- **V's row weight** of an `eq` table `eqR` at the point `z` (`rowValD`'s weight, by `rfl`). -/
def rowW (eqR : List FE) (z : List FE2) (r : List FE) : FE :=
  sumE ((List.range 128).map fun j => eqR.getD j 0 * (tensorWD z r).getD j 0)

theorem rowValD_weight (z sv : List FE2) (eqR : List FE) : (rowValD z sv eqR).1.2 = rowW eqR z := by
  unfold rowValD rowW; rfl

/-- **A switch's `ν` cells by value** stand for the `eq` table `eqR` (`ν₀ = nuH eqR false`, `ν₁ = nuH eqR true`,
component `k` at list index `k`; the leaf `rowLeafG` of blob v3 reads them so). -/
def RowNuV (M : Mem) (nu : RowNu) (eqR : List FE) : Prop :=
  ∀ k < 64, (nu.nu0.getD k default).val M = nuH (fun j => eqR.getD j 0) false k ∧
    (nu.nu1.getD k default).val M = nuH (fun j => eqR.getD j 0) true k

/-- The `E` cell that a loop over one dimension of 64 iterations reads at iteration `j` through `nuAddr l` (the
cells `l[1] + j·(l[2] − l[1])`). -/
def nuAt (l : List Cell) (j : ℕ) : Cell :=
  ⟨.E, (l.getD 1 default).n + ((l.getD 2 default).n - (l.getD 1 default).n) * j⟩

/-- **A switch's `ν` cells stand for the `eq` table `eqR`**, both as read by index (`RowNuV`: blob v4's `lRhoG`) and
as the looped leaves read them (blob v4, lever L1: `rowLeafGL`, and blob GT's `lRhoGL` read component `k` at iteration
`(k + 63) mod 64` through `nuAddr`: the cells `nuAt` hold `ν₀ = nuH eqR false` and `ν₁ = nuH eqR true`). -/
def RowNuOk (M : Mem) (nu : RowNu) (eqR : List FE) : Prop :=
  RowNuV M nu eqR ∧ ∀ k < 64, (nuAt nu.nu0 ((k + 63) % 64)).val M = nuH (fun j => eqR.getD j 0) false k ∧
    (nuAt nu.nu1 ((k + 63) % 64)).val M = nuH (fun j => eqR.getD j 0) true k

/-- `RowNuOk` from the values at the list indices, when the looped reads are the list's cells. -/
theorem rowNuOk_of_v {nu : RowNu} {eqR : List FE} (hv : RowNuV M nu eqR)
    (ha : ∀ k < 64, nuAt nu.nu0 ((k + 63) % 64) = nu.nu0.getD k default ∧
      nuAt nu.nu1 ((k + 63) % 64) = nu.nu1.getD k default) : RowNuOk M nu eqR :=
  ⟨hv, fun k hk => by rw [(ha k hk).1, (ha k hk).2]; exact hv k hk⟩

/-- **A `ν` gadget's cells stand for the switch's `eq` table** (`eq(r'', ·)` in `rw.eqR`, `r''₆` in `rw.rr`), from
its specification in `hs_rowNuG`'s form (`rowNuG`; blob v4's looped `rowNuGL`). -/
theorem rowNuOk_of_hs (rw : RowOut) {G : BM RowNu}
    (hG : (∀ i < 64, (rw.eqR.getD i default).val M =
        ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) * (1 + (rw.rr.getD 6 default).val M) ∧
      (rw.eqR.getD (i + 64) default).val M =
        ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) * (rw.rr.getD 6 default).val M) →
      Hs c M G (fun nu => ∀ k < 64,
        (nu.nu0.getD k default).val M = nuH (fun j => (rw.eqR.getD j default).val M) false k ∧
        (nu.nu1.getD k default).val M = nuH (fun j => (rw.eqR.getD j default).val M) true k))
    (rv : List FE) (hrl : rv.length = 7)
    (hE : rw.eqR.map (Cell.val M) = eqKernel rv) (hr6 : (rw.rr.getD 6 default).val M = rv.getD 6 0) {p : Ptr}
    (h : SegsHold c M p (G p).2) : RowNuV M (G p).1 (eqKernel rv) := by
  have hEl : rw.eqR.length = 128 := by
    have := congrArg List.length hE; rw [List.length_map, Lvm.Q1.eqKernel_length_lk, hrl] at this; exact this
  have hρv : ∀ j < 128, (rw.eqR.getD j default).val M = (eqKernel rv).getD j 0 := fun j hj => by
    rw [← hE, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by (clear * - hEl hj; omega))]
    rfl
  have hρ : ∀ i < 64, (rw.eqR.getD i default).val M =
        ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) * (1 + (rw.rr.getD 6 default).val M) ∧
      (rw.eqR.getD (i + 64) default).val M =
        ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) * (rw.rr.getD 6 default).val M := by
    intro i hi
    obtain ⟨s1, s2⟩ := eqKernel_split rv hrl hi
    rw [hρv i (by (clear * - hi; omega)), hρv (i + 64) (by (clear * - hi; omega)), hr6, s1, s2]
    refine ⟨?_, ?_⟩
    · linear_combination (-((eqKernel (List.take 6 rv)).getD i 0 * rv.getD 6 0 * (1 + rv.getD 6 0))) *
        CharTwo.two_eq_zero (R := FE)
    · linear_combination (-((eqKernel (List.take 6 rv)).getD i 0 * rv.getD 6 0 * rv.getD 6 0)) *
        CharTwo.two_eq_zero (R := FE)
  intro k hk
  have hn := hG hρ p h k hk
  have hc : (fun j => (rw.eqR.getD j default).val M) = fun j => if j < 128 then (eqKernel rv).getD j 0 else
      (rw.eqR.getD j default).val M := funext fun j => by split_ifs with hj; exact hρv j hj; rfl
  have hn' : ∀ b : Bool, nuH (fun j => (rw.eqR.getD j default).val M) b k = nuH (fun j => (eqKernel rv).getD j 0) b k :=
    fun b => Finset.sum_congr rfl fun i hi => by
      dsimp only
      rw [hρv _ (by have := Finset.mem_range.mp hi; split <;> (clear * - this; omega))]
  exact ⟨hn.1.trans (hn' false), hn.2.trans (hn' true)⟩

/-- **`rowNuG`'s cells stand for the switch's `eq` table** (`eq(r'', ·)` in `rw.eqR`, `r''₆` in `rw.rr`). -/
theorem rowNuG_ok (rw : RowOut) {z o : ℕ} (hz : M.e z = 0) (ho : M.e o = 1) (rv : List FE) (hrl : rv.length = 7)
    (hE : rw.eqR.map (Cell.val M) = eqKernel rv) (hr6 : (rw.rr.getD 6 default).val M = rv.getD 6 0) {p : Ptr}
    (h : SegsHold c M p (rowNuG rw z o p).2) : RowNuV M (rowNuG rw z o p).1 (eqKernel rv) :=
  rowNuOk_of_hs rw (hs_rowNuG rw hz ho) rv hrl hE hr6 h

/-- **The row leaf is V's row weight** (big shape): with `ν`'s cells standing for `eqR`, the claim point's `E2`
coordinates `zs` (`K` cells) and the basis point's first `|zs|` coordinates in the `E` cells `xb + l`. -/
theorem rowLeaf_weightN (nu : RowNu) (eqR : List FE) (hnu : RowNuV M nu eqR) (zs : List C2) (hne : zs ≠ [])
    (hK : ∀ x ∈ zs, x.re.ty = .K ∧ x.im.ty = .K) (xb : ℕ) (xs : List FE) (hxl : xs.length = zs.length)
    (hx : ∀ l < zs.length, M.e (xb + l) = xs.getD l 0) {z zk : Cell} (hz : z.val M = 0) (hzk : zk.val M = 0) :
    Hs c M (rowLeafG nu zs none xb z zk) (fun r => r.val M = rowW eqR (zs.map (C2.val M)) xs) := by
  refine hs_mono (hs_rowLeafG nu zs none xb hz hzk hne) fun r ⟨fs, _, hfs, hv⟩ => ?_
  rw [hv, rowW, sumE_eq, lsum_range,
    show ∑ j ∈ range 128, eqR.getD j 0 * (tensorWD (zs.map (C2.val M)) xs).getD j 0 =
      ∑ j ∈ range 128, (fun j => eqR.getD j 0) j * (tensorWD (zs.map (C2.val M)) xs).getD j 0 from rfl, weight_crt]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hf : ∀ L : List (FE2 × FE), L.foldl (fun P zr => qm (twK k) P (fct k zr)) (1, 0) =
      (L.map (fct k)).foldl (qm (twK k)) (1, 0) := fun L => (List.foldl_map ..).symm
  rw [(hnu k hk').1, (hnu k hk').2, phiA_tensorWD, hf, hfs k hk', List.append_nil]
  have hzz : (List.zip (zs.map (C2.val M)) xs).map (fct k) = (List.range zs.length).map fun l =>
      (1 + (zs.getD l default).re.val M ^ 2 ^ k + M.e (xb + l), (zs.getD l default).im.val M ^ 2 ^ k) := by
    apply List.ext_getElem
    · simp [hxl]
    · intro l h1 _
      have hl : l < zs.length := by simpa [hxl] using h1
      have hKl := hK _ (List.getElem_mem hl)
      simp only [List.getElem_map, List.getElem_zip, List.getElem_range, fct]
      rw [hx l hl, List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by (clear * - hxl hKl; omega))]
      have hre : (zs[l]).re.val M = FE.ofK ((zs[l]).re.val M).c₀ := by
        rcases h : zs[l].re with ⟨ty, n⟩; rw [h] at hKl; obtain ⟨rfl, -⟩ := hKl; rfl
      have him : (zs[l]).im.val M = FE.ofK ((zs[l]).im.val M).c₀ := by
        rcases h : zs[l].im with ⟨ty, n⟩; rw [h] at hKl; obtain ⟨-, rfl⟩ := hKl; rfl
      have hp : ∀ a : FK, FE.ofK a ^ 2 ^ k = FE.ofK (a ^ 2 ^ k) := fun a => (map_pow FE.ofKRingHom a _).symm
      rw [hre, him, hp, hp]
      rfl
  rw [hzz]

/-- **The row leaf is V's row weight**, from the switch's cells (`rowNuG_ok`, `rowLeaf_weightN`). -/
theorem rowLeaf_weight (rw : RowOut) {z o : ℕ} (hz : M.e z = 0) (ho : M.e o = 1)
    {zk : Cell} (hzk : zk.val M = 0) (rv : List FE) (hrl : rv.length = 7)
    (hE : rw.eqR.map (Cell.val M) = eqKernel rv) (hr6 : (rw.rr.getD 6 default).val M = rv.getD 6 0)
    (zs : List C2) (hne : zs ≠ []) (hK : ∀ x ∈ zs, x.re.ty = .K ∧ x.im.ty = .K) (xb : ℕ) (xs : List FE)
    (hxl : xs.length = zs.length) (hx : ∀ l < zs.length, M.e (xb + l) = xs.getD l 0) {p1 p2 : Ptr}
    (h1 : SegsHold c M p1 (rowNuG rw z o p1).2)
    (h2 : SegsHold c M p2 (rowLeafG (rowNuG rw z o p1).1 zs none xb (ec z) zk p2).2) :
    (rowLeafG (rowNuG rw z o p1).1 zs none xb (ec z) zk p2).1.val M = rowW (eqKernel rv) (zs.map (C2.val M)) xs :=
  rowLeaf_weightN _ _ (rowNuG_ok rw hz ho rv hrl hE hr6 h1) zs hne hK xb xs hxl hx (by rw [Cell.val_E, hz]) hzk p2 h2

end Gadgets

end Lvm.Q2
