-- Vendored from `CompPoly/CompPoly/Multilinear/Basic.lean` (the contract's pin of the package) as `LvmMlBasic` for lvm (WP-2).
/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Aristotle (Harmonic), Elias Judin
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import CompPoly.Data.Nat.Bitwise
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.Fold
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Cases
-- (GOLF2 import pruning: dropped LvmMlListLemmas: unused by this module.)

-- (GOLF2: 48 declarations that `certified` does not use moved verbatim to `LvmTypedVEqPhasesXOff`, outside its import closure.)

-- ===== merged from `LvmMlVector` (GOLF module merge: `LvmMlVector.lean` is now a stub importing `LvmMlBasic`) =====
section
-- Vendored from `CompPoly/CompPoly/Data/Vector/Basic.lean` (the contract's pin of the package) as `LvmMlVector` for lvm (WP-2).
/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

/-!
# Definitions and lemmas for `Vector`

`accumulateProducts` separates product accumulation from reduction. Its reduction theorem
recovers `dotProduct` whenever reduction preserves zero, addition, and the chosen products.
-/

section
universe u

namespace Vector

-- TODO this is also defined in VCV-io, so is awkward as an Arklib dependency
-- added _temp as a temporary fix
@[elab_as_elim]
def induction₂_temp {α β} {motive : {n : ℕ} → Vector α n → Vector β n → Sort*}
    (v_empty : motive #v[] #v[])
  (v_insert : {n : ℕ} → (hd : α) → (tl : Vector α n) → (hd' : β) → (tl' : Vector β n) →
      motive tl tl' → motive (tl.insertIdx 0 hd) (tl'.insertIdx 0 hd')) {m : ℕ} :
    (v : Vector α m) → (v' : Vector β m) → motive v v' := by induction m with
  | zero => exact fun v v' => match v, v' with | ⟨⟨[]⟩, rfl⟩, ⟨⟨[]⟩, rfl⟩ => v_empty
  | succ n ih => exact fun v v' => match hv : v, hv' : v' with
    | ⟨⟨hd :: tl⟩, hSize⟩, ⟨⟨hd' :: tl'⟩, hSize'⟩ => by
      simpa [Vector.insertIdx] using
        v_insert hd ⟨⟨tl⟩, by simpa using hSize⟩ hd' ⟨⟨tl'⟩, by simpa using hSize'⟩
        (ih ⟨⟨tl⟩, by simpa using hSize⟩ ⟨⟨tl'⟩, by simpa using hSize'⟩)

/-- The empty vector. -/
def nil {α} : Vector α 0 := ⟨#[], rfl⟩ -- Vector.emptyWithCapacity 0

/-- Construct a vector by prepending an element to the front of a vector,
using `insertIdx` at `0`. -/
def cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : Vector α (n + 1) :=
  tl.insertIdx 0 hd

@[simp]
theorem head_cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : (cons hd tl).head = hd := by
  simp only [head, cons, insertIdx_zero, getElem_cast, zero_lt_one, getElem_append_left, getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero]

lemma cons_get_eq {α} {n : ℕ} (hd : α) (tl : Vector α n) (i : Fin (n + 1)) :
    (cons hd tl).get i =
      if hi: i.val == 0 then hd else tl.get (⟨i.val - 1, by
        simp only [beq_iff_eq, Fin.val_eq_zero_iff] at hi
        apply Nat.sub_lt_left_of_lt_add
        · by_contra hi_ne_gt_1
          simp only [not_le, Nat.lt_one_iff, Fin.val_eq_zero_iff] at hi_ne_gt_1
          contradiction
        · have hi_lt:= i.isLt; omega
      ⟩) := by
  simp only [cons, get_eq_getElem, Vector.insertIdx_zero, Vector.getElem_cast]
  split
  · -- head position: read from the singleton prefix
    next h =>
      have h0 : i.val = 0 := by simpa using h
      rw [Vector.getElem_append_left (by omega)]
      simp [h0]
  · -- tail position: read from `tl`, shifted past the singleton prefix
    next h =>
      have h0 : i.val ≠ 0 := by simpa using h
      rw [Vector.getElem_append_right (by omega) (by omega)]

@[simp]
lemma cons_empty_tail_eq_nil {α} (hd : α) (tl : Vector α 0) :
    cons hd tl = ⟨#[hd], rfl⟩ := by
  apply Vector.toArray_inj.mp
  simp only [Nat.reduceAdd]
  rw [cons]
  simp only [insertIdx_size_self, toArray_push]
  have hl_toArray: tl.toArray = #[] := by
    simp only [toArray_eq_empty_iff]
  rw [hl_toArray]
  simp only [Array.push_empty]

@[simp]
theorem tail_cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : (cons hd tl).tail = tl := by
  rw [cons, Vector.insertIdx]
  simp only [Nat.add_one_sub_one, Array.insertIdx_zero, tail_eq_cast_extract, extract_mk,
    Array.extract_append, List.extract_toArray, List.extract_eq_take_drop, add_tsub_cancel_right,
    List.drop_succ_cons, List.drop_nil, List.take_nil, List.size_toArray, List.length_cons,
    List.length_nil, tsub_self, Array.take_eq_extract, Array.empty_append, cast_mk, mk_eq,
    Array.extract_eq_self_iff, size_toArray, le_refl, and_self, or_true]

@[simp]
theorem cons_toList_eq_List_cons {α} {n : ℕ} (hd : α) (tl : Vector α n) :
    (cons hd tl).toList = hd :: tl.toList := by
  simp only [toList, cons, insertIdx]
  rw [Array.toList_insertIdx]
  simp only [List.insertIdx_zero]

theorem foldl_eq_toList_foldl {α β} {n : ℕ} (f : β → α → β) (init : β) (v : Vector α n) :
    v.foldl (f:=f) (b:=init) = v.toList.foldl (f:=f) (init:=init) := by
  rw [Vector.foldl]
  rw [←Array.foldl_toList]
  rfl

-- evaluation cons (hd:=6) (tl:=⟨#[2, 3], rfl⟩)

theorem zipWith_cons {α β γ} {n : ℕ} (f : α → β → γ)
    (a : α) (b : Vector α n) (c : β) (d : Vector β n) :
  zipWith f (cons a b) (cons c d) = cons (f a c) (zipWith f b d) := by
  apply Vector.toList_inj.mp
  conv_lhs => simp only [toList_zipWith]
  simp_rw [cons_toList_eq_List_cons]
  rw [List.zipWith_cons_cons]
  conv_rhs => rw [toList_zipWith]

variable {R : Type*} {n : ℕ}

/-- Inner product between two vectors of the same size. Should be faster than `_root_.dotProduct`
    due to efficient operations on `Vector`s. -/
def dotProduct [Zero R] [Add R] [Mul R] (a b : Vector R n) : R :=
  a.zipWith (· * ·) b |>.foldl (· + ·) 0

@[inherit_doc]
scoped notation:80 a " *ᵥ " b => dotProduct a b

@[simp]
lemma dotProduct_cons [AddCommMonoid R] [Mul R] (a : R) (b : Vector R n) (c : R) (d : Vector R n) :
    dotProduct (cons a b) (cons c d) = a * c + dotProduct b d := by
  unfold dotProduct
  rw [zipWith_cons]
  simp_rw [foldl_eq_toList_foldl]
  rw [cons_toList_eq_List_cons]
  have h : ∀ (init : R) (L : List R),
      List.foldl (fun x1 x2 => x1 + x2) init L = init + List.foldl (fun x1 x2 => x1 + x2) 0 L := by
    intro init L
    induction L generalizing init with
    | nil => simp
    | cons x xs ih =>
      show List.foldl _ (init + x) xs = init + List.foldl _ (0 + x) xs
      rw [ih (init + x), ih (0 + x), _root_.zero_add, _root_.add_assoc]
  rw [List.foldl_cons]
  show List.foldl _ (0 + a * c) _ = _
  rw [_root_.zero_add, h]

/-- A matrix represented as iterated vectors in row-major order.
`m` is the number of rows, and `n` is the number of columns -/
def Matrix (α : Type*) (m n : ℕ) := Vector (Vector α n) m

namespace Matrix

variable {α : Type*}

/- Note `Vector.flatten` converts a `Vector (m * n)` into a `Matrix α m n` -/
/-- Transpose a matrix by swapping rows and columns. -/
@[simp]
def transpose {m n : ℕ} (matrix : Matrix α m n) : Matrix α n m :=
  ofFn (fun j => ofFn (fun i => (matrix.get i).get j))

end Matrix

end Vector

section RootDotProduct

open Vector

variable {R : Type*} [AddCommMonoid R] [Mul R] {n : ℕ}

@[simp]
lemma dotProduct_cons (a : R) (b : Vector R n) (c : R) (d : Vector R n) :
    _root_.dotProduct (cons a b).get (cons c d).get = a * c + _root_.dotProduct b.get d.get := by
  unfold _root_.dotProduct
  if h_n: n = 0 then
    subst h_n
    simp only [cons_empty_tail_eq_nil]
    simp_all only [Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero,
                  Fin.isValue, Finset.sum_singleton,
                  Finset.univ_eq_empty, Finset.sum_empty, _root_.add_zero]
    rfl
  else
    -- ⊢ ∑ i, (cons a b).get i * (cons c d).get i = a * c + ∑ i, b.get i * d.get i
    rw [Fin.sum_univ_succ]
    rw [cons_get_eq, cons_get_eq]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, BEq.rfl, ↓reduceDIte]
    congr
    funext i
    simp_rw [cons_get_eq]
    simp only [Fin.val_succ, Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceDIte,
      add_tsub_cancel_right, Fin.eta]

end RootDotProduct

namespace Vector

variable {R : Type*} [AddCommMonoid R] [Mul R] {n : ℕ}

theorem dotProduct_eq_root_dotProduct (a b : Vector R n) :
    dotProduct a b = _root_.dotProduct a.get b.get := by
  refine induction₂_temp ?_ (fun hd tl hd' tl' ih => ?_) a b
  · simp [dotProduct, _root_.dotProduct]
  · simp [Vector.cast]
    -- By definition of dot product, we can expand the right-hand side.
    simp [dotProduct];
    -- By definition of dot product, we can expand the right-hand side.
    -- The left-hand side is the foldl of the zipWith operation on the two arrays,
    -- which is equivalent to the dot product of the corresponding vectors.
    simp [_root_.dotProduct];
    convert dotProduct_cons hd tl hd' tl' using 1;
    · -- The array's foldl of the zipWith operation is the same as the dot product
      -- of the vectors because the vector's dot product is defined as the sum
      -- of the products of corresponding elements.
      simp [dotProduct, Vector.cons];
      simp +decide [ Vector.foldl, Vector.zipWith ];
    · simp +decide [ Fin.sum_univ_succ, ih ];
      rfl

end Vector

namespace Vector

end Vector
end
end
-- ===== end of `LvmMlVector` =====

/-!
  # Multilinear Polynomials

  This file defines computable representations of **multilinear polynomials**.

  The first representation is by their coefficients, and the second representation is by their
  evaluations over the Boolean hypercube `{0,1}^n`. Both representations are defined as `Vector`s of
  length `2^n`, where `n` is the number of variables. We will define operations on these
  representations, and prove equivalence between them, and with the standard Mathlib definition of
  multilinear polynomials, which is the type `R⦃≤ 1⦄[X Fin n]` (notation for
  `MvPolynomial.restrictDegree (Fin n) R 1`).

  ## TODOs
  - The abstract zeta formula for `monoToLagrange`
  - A naive `O(4^n)` zeta spec `monoToLagrangeSpec` mirroring `lagrangeToMonoSpec`,
    plus equivalence `monoToLagrange = monoToLagrangeSpec`
-/

section

namespace CompPoly

/-- `CMlPolynomial n R` is the type of multilinear polynomials in `n` variables over a ring `R`.
  It is represented by its monomial coefficients as a `Vector` of length `2^n`.
  The indexing is **little-endian** (i.e. the least significant bit is the first bit). -/
@[reducible]
def CMlPolynomial (R : Type*) (n : ℕ) := Vector R (2 ^ n) -- coefficient of monomial basis
def CMlPolynomial.mk {R : Type*} (n : ℕ) (v : Vector R (2 ^ n)) : CMlPolynomial R n := v

/-- `CMlPolynomialEval n R` is the type of multilinear polynomials in `n` variables over a ring `R`.
  It is represented by its evaluations over the Boolean hypercube `{0,1}^n`,
  i.e. Lagrange basis coefficients.
  The indexing is **little-endian** (i.e. the least significant bit is the first bit). -/
@[reducible]
def CMlPolynomialEval (R : Type*) (n : ℕ) := Vector R (2 ^ n) -- coefficient of Lagrange basis
def CMlPolynomialEval.mk {R : Type*} (n : ℕ) (v : Vector R (2 ^ n)) : CMlPolynomialEval R n := v

variable {R : Type*} {n : ℕ}

-- Note: `finFunctionFinEquiv` maps `i : Fin (2 ^ n)` to its bit-vector in little‑endian order,
-- with bit 0 the least significant bit. For example, `6 : Fin 8` maps to `[0, 1, 1]`.
-- #check finFunctionFinEquiv

-- #check Pi.single

namespace CMlPolynomial

section CMlPolynomialInstances

-- Create a zero polynomial over n variables
@[inline]
def zero [Zero R] : CMlPolynomial R n := Vector.replicate (2 ^ n) 0

/-- Add two `CMlPolynomial`s -/
@[inline]
def add [Add R] (p q : CMlPolynomial R n) : CMlPolynomial R n := Vector.zipWith (· + ·) p q

/-- Negation of a `CMlPolynomial` -/
@[inline]
def neg [Neg R] (p : CMlPolynomial R n) : CMlPolynomial R n := p.map (fun a => -a)

/-- Scalar multiplication of a `CMlPolynomial` -/
@[inline]
def smul [Mul R] (r : R) (p : CMlPolynomial R n) : CMlPolynomial R n := p.map (fun a => r * a)

/-- Scalar multiplication of a `CMlPolynomial` by a natural number -/
@[inline]
def nsmul [SMul ℕ R] (m : ℕ) (p : CMlPolynomial R n) : CMlPolynomial R n :=
  p.map (fun a => m • a)

/-- Scalar multiplication of a `CMlPolynomial` by an integer -/
@[inline]
def zsmul [SMul ℤ R] (m : ℤ) (p : CMlPolynomial R n) : CMlPolynomial R n :=
  p.map (fun a => m • a)

instance [AddCommMonoid R] : AddCommMonoid (CMlPolynomial R n) where
  add := add
  add_assoc a b c := by
    change Vector.zipWith (· + ·) (Vector.zipWith (· + ·) a b) c =
      Vector.zipWith (· + ·) a (Vector.zipWith (· + ·) b c)
    ext; simp [add_assoc]
  add_comm a b := by
    change Vector.zipWith (· + ·) a b = Vector.zipWith (· + ·) b a
    ext; simp [add_comm]
  zero := zero
  zero_add a := by
    change Vector.zipWith (· + ·) (Vector.replicate (2 ^ n) 0) a = a
    ext; simp
  add_zero a := by
    change Vector.zipWith (· + ·) a (Vector.replicate (2 ^ n) 0) = a
    ext; simp
  nsmul := nsmul
  nsmul_zero a := by
    change Vector.map (fun a ↦ 0 • a) a = Vector.replicate (2 ^ n) 0
    ext; simp
  nsmul_succ n a := by
    change a.map (fun a ↦ (n + 1) • a) = Vector.zipWith (· + ·) (Vector.map (fun a ↦ n • a) a) a
    ext i; simp; exact AddMonoid.nsmul_succ n a[i]

instance [Semiring R] : Module R (CMlPolynomial R n) where
  smul := smul
  one_smul a := by
    change Vector.map (fun a ↦ 1 * a) a = a
    ext; simp
  mul_smul r s a := by
    simp [HSMul.hSMul, smul]
  smul_zero a := by
    change Vector.map (fun a_1 ↦ a * a_1) (Vector.replicate (2 ^ n) 0) = Vector.replicate (2 ^ n) 0
    ext; simp
  smul_add r a b := by
    change Vector.map (fun a ↦ r * a) (Vector.zipWith (· + ·) a b) =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ r * a) b)
    ext; simp [left_distrib]
  add_smul r s a := by
    change Vector.map (fun a ↦ (r + s) * a) a =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ s * a) a)
    ext; simp [right_distrib]
  zero_smul a := by
    change Vector.map (fun a ↦ 0 * a) a = Vector.replicate (2 ^ n) 0
    ext; simp
end CMlPolynomialInstances

section CMlPolynomialMonomialBasisAndEvaluations

variable [CommSemiring R]
variable {S : Type*} [CommSemiring S]

/-
Monomial-basis evaluations at point `w`.

Returns the length-`2^n` vector whose index `i : Fin (2^n)` encodes a Boolean vector in
little‑endian order (bit 0 is the least significant bit). The entry at `i` is
`∏_{j < n} (if the j-th bit of i is 1 then w[j] else 1)`.
-/
def monomialBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1)

@[simp]
theorem monomialBasis_zero {w : Vector R 0} : monomialBasis w = #v[1] := by
  ext i hi
  simp [monomialBasis]

-- evaluation monomialBasis #v[(1 : ℤ), 2, 3] (n := 3)
-- evaluation Nat.digits 2 8

/-- The `i`-th element of `monomialBasis w` is the product of `w[j]` if the `j`-th bit of `i` is 1,
    and `1` if the `j`-th bit of `i` is 0. -/
theorem monomialBasis_getElem {w : Vector R n} (i : Fin (2 ^ n)) :
    (monomialBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 := by
  rw [monomialBasis]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]

private lemma monomial_basis_even {n : ℕ} (x : Vector R (n + 1)) (j : Fin (2 ^ n)) :
    (monomialBasis x).get ⟨2 * j.val, by omega⟩ =
    (monomialBasis x.tail).get j := by
  unfold monomialBasis
  simp only [Vector.get_ofFn]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [← Nat.bit_false_apply j.val]
  simp only [Nat.testBit_bit_zero, Bool.false_eq_true, ite_false, one_mul]
  apply Finset.prod_congr rfl
  intro k _
  rw [Nat.testBit_bit_succ]
  simp [Vector.tail_eq_cast_extract, Nat.add_comm]

private lemma monomial_basis_odd {n : ℕ} (x : Vector R (n + 1)) (j : Fin (2 ^ n)) :
    (monomialBasis x).get ⟨2 * j.val + 1, by omega⟩ =
    x.head * (monomialBasis x.tail).get j := by
  unfold monomialBasis
  simp only [Vector.get_ofFn]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [← Nat.bit_true_apply j.val]
  simp only [Nat.testBit_bit_zero, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [Nat.testBit_bit_succ]
  simp [Vector.tail_eq_cast_extract, Nat.add_comm]

def map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (p : CMlPolynomial R n) : CMlPolynomial S n :=
  Vector.map f p

/-- One Horner reduction step, eliminating the next little-endian variable. -/
@[inline, specialize]
def evalHornerStep {n : ℕ}
    (coeffs : Vector R (2 ^ (n + 1))) (x0 : R) : Vector R (2 ^ n) :=
  Vector.ofFn fun j : Fin (2 ^ n) ↦
    coeffs.get ⟨2 * j.val, by omega⟩ + x0 * coeffs.get ⟨2 * j.val + 1, by omega⟩

/-- Evaluate dense multilinear coefficients by eliminating one variable at a time. -/
@[inline, specialize]
def evalHornerCoeffs :
    {n : ℕ} → Vector R (2 ^ n) → Vector R n → R
  | 0, coeffs, _ => coeffs.get ⟨0, by norm_num⟩
  | n + 1, coeffs, x =>
      evalHornerCoeffs (evalHornerStep coeffs x.head) x.tail

/-- Evaluate a `CMlPolynomial` at a point using a multilinear Horner method. -/
@[inline, specialize]
def evalHorner (p : CMlPolynomial R n) (x : Vector R n) : R :=
  evalHornerCoeffs p x

/-- Evaluate a `CMlPolynomial` using a ring homomorphism and multilinear Horner method. -/
@[inline, specialize]
def eval₂Horner (p : CMlPolynomial R n) (f : R →+* S) (x : Vector S n) : S :=
  evalHorner (map f p) x

/-- Evaluate a `CMlPolynomial` at a point -/
def eval (p : CMlPolynomial R n) (x : Vector R n) : R :=
  Vector.dotProduct p (monomialBasis x)

def eval₂ (p : CMlPolynomial R n) (f : R →+* S) (x : Vector S n) : S := eval (map f p) x

private lemma eval_horner_step_dot_product {n : ℕ}
    (p : CMlPolynomial R (n + 1)) (x : Vector R (n + 1)) :
    Vector.dotProduct (evalHornerStep p x.head) (monomialBasis x.tail) =
    Vector.dotProduct p (monomialBasis x) := by
  rw [Vector.dotProduct_eq_root_dotProduct, Vector.dotProduct_eq_root_dotProduct]
  unfold _root_.dotProduct
  have hsplit :
      (∑ i : Fin (2 ^ (n + 1)), p.get i * (monomialBasis x).get i) =
        (∑ i : Fin (2 ^ n), p.get ⟨2 * i.val, by omega⟩ *
          (monomialBasis x).get ⟨2 * i.val, by omega⟩) +
        (∑ i : Fin (2 ^ n), p.get ⟨2 * i.val + 1, by omega⟩ *
          (monomialBasis x).get ⟨2 * i.val + 1, by omega⟩) := by
    convert (Fin.sum_univ_pow_two_even_add_odd (n := n)
        (f := fun i ↦ if h : i < 2 ^ (n + 1) then
          p.get ⟨i, h⟩ * (monomialBasis x).get ⟨i, h⟩ else 0)).symm using 1
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.is_lt, dite_eq_left]
    · congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [dite_eq_left (by omega)]
      · apply Finset.sum_congr rfl
        intro i _
        rw [dite_eq_left (by omega)]
  rw [hsplit]
  unfold evalHornerStep
  simp only [Vector.get_ofFn]
  simp only [monomial_basis_even, monomial_basis_odd]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [add_mul]
  congr 1
  rw [mul_comm x.head, mul_assoc]

/-- Horner evaluation agrees with the dot-product evaluator. -/
theorem eval_horner_eq_eval (p : CMlPolynomial R n) (x : Vector R n) :
    evalHorner p x = eval p x := by
  induction n with
  | zero =>
      rw [eval, Vector.dotProduct_eq_root_dotProduct]
      simp [evalHorner, evalHornerCoeffs, monomialBasis, _root_.dotProduct]
  | succ n ih =>
      simp only [evalHorner, evalHornerCoeffs]
      trans Vector.dotProduct (evalHornerStep p x.head) (monomialBasis x.tail)
      · exact ih _ _
      · simp only [eval]
        exact eval_horner_step_dot_product p x

/-- Evaluation is additive in the coefficient vector. -/
@[simp] theorem eval_add (p q : CMlPolynomial R n) (x : Vector R n) :
    eval (p + q) x = eval p x + eval q x := by
  unfold eval
  rw [Vector.dotProduct_eq_root_dotProduct, Vector.dotProduct_eq_root_dotProduct,
    Vector.dotProduct_eq_root_dotProduct]
  simp only [_root_.dotProduct, ← Finset.sum_add_distrib, ← add_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Vector.get_eq_getElem, Vector.getElem_add]

/-- The zero coefficient vector evaluates to zero. -/
@[simp] theorem eval_zero (x : Vector R n) : eval (0 : CMlPolynomial R n) x = 0 := by
  unfold eval
  rw [Vector.dotProduct_eq_root_dotProduct]
  simp only [_root_.dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Vector.get_eq_getElem, Vector.getElem_zero, zero_mul]

/-- Evaluation commutes with scalar multiplication of the coefficient vector. -/
@[simp] theorem eval_smul (a : R) (p : CMlPolynomial R n) (x : Vector R n) :
    eval (a • p) x = a * eval p x := by
  unfold eval
  rw [Vector.dotProduct_eq_root_dotProduct, Vector.dotProduct_eq_root_dotProduct]
  simp only [_root_.dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.get_eq_getElem (a • p) i, Vector.get_eq_getElem p i, Vector.getElem_smul]
  simp only [smul_eq_mul, mul_assoc]

end CMlPolynomialMonomialBasisAndEvaluations

end CMlPolynomial

namespace CMlPolynomialEval

section CMlPolynomialEvalInstances

-- Create a zero polynomial over n variables
@[inline]
def zero [Zero R] : CMlPolynomialEval R n := Vector.replicate (2 ^ n) 0

/-- Add two `CMlPolynomialEval`s -/
@[inline]
def add [Add R] (p q : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  Vector.zipWith (· + ·) p q

/-- Negation of a `CMlPolynomialEval` -/
@[inline]
def neg [Neg R] (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  p.map (fun a => -a)

/-- Scalar multiplication of a `CMlPolynomialEval` -/
@[inline]
def smul [Mul R] (r : R) (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  p.map (fun a => r * a)

/-- Scalar multiplication of a `CMlPolynomialEval` by a natural number -/
@[inline]
def nsmul [SMul ℕ R] (m : ℕ) (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  p.map (fun a => m • a)

/-- Scalar multiplication of a `CMlPolynomialEval` by an integer -/
@[inline]
def zsmul [SMul ℤ R] (m : ℤ) (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  p.map (fun a => m • a)

instance [AddCommMonoid R] : AddCommMonoid (CMlPolynomialEval R n) where
  add := add
  add_assoc a b c := by
    change Vector.zipWith (· + ·) (Vector.zipWith (· + ·) a b) c =
      Vector.zipWith (· + ·) a (Vector.zipWith (· + ·) b c)
    ext; simp [add_assoc]
  add_comm a b := by
    change Vector.zipWith (· + ·) a b = Vector.zipWith (· + ·) b a
    ext; simp [add_comm]
  zero := zero
  zero_add a := by
    change Vector.zipWith (· + ·) (Vector.replicate (2 ^ n) 0) a = a
    ext; simp
  add_zero a := by
    change Vector.zipWith (· + ·) a (Vector.replicate (2 ^ n) 0) = a
    ext; simp
  nsmul := nsmul
  nsmul_zero a := by
    change Vector.map (fun a ↦ 0 • a) a = Vector.replicate (2 ^ n) 0
    ext; simp
  nsmul_succ n a := by
    change a.map (fun a ↦ (n + 1) • a) = Vector.zipWith (· + ·) (Vector.map (fun a ↦ n • a) a) a
    ext i; simp; exact AddMonoid.nsmul_succ n a[i]

instance [Semiring R] : Module R (CMlPolynomialEval R n) where
  smul := smul
  one_smul a := by
    change Vector.map (fun a ↦ 1 * a) a = a
    ext; simp
  mul_smul r s a := by
    simp [HSMul.hSMul, smul]
  smul_zero a := by
    change Vector.map (fun a_1 ↦ a * a_1) (Vector.replicate (2 ^ n) 0) = Vector.replicate (2 ^ n) 0
    ext; simp
  smul_add r a b := by
    change Vector.map (fun a ↦ r * a) (Vector.zipWith (· + ·) a b) =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ r * a) b)
    ext; simp [left_distrib]
  add_smul r s a := by
    change Vector.map (fun a ↦ (r + s) * a) a =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ s * a) a)
    ext; simp [right_distrib]
  zero_smul a := by
    change Vector.map (fun a ↦ 0 * a) a = Vector.replicate (2 ^ n) 0
    ext; simp

end CMlPolynomialEvalInstances

section CMlPolynomialLagrangeBasisAndEvaluations

variable [CommRing R]
variable {S : Type*} [CommRing S]

/-- Lagrange (hypercube) basis at point `w`.

Returns the length-`2^n` vector `v` such that for any `x ∈ {0,1}^n`, letting
`i = ∑_{j=0}^{n-1} x_j · 2^j` (little‑endian indexing), we have
`v[i] = ∏_{j < n} (x_j · w[j] + (1 - x_j) · (1 - w[j]))`.
Equivalently, for `i : Fin (2^n)`,
`v[i] = ∏_{j < n}, (if the j-th bit of i is 1 then w[j] else 1 - w[j])`.
-/
def lagrangeBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j])

@[simp]
theorem lagrangeBasis_zero {w : Vector R 0} : lagrangeBasis w = #v[1] := by
  ext i hi
  simp [lagrangeBasis]

-- evaluation lagrangeBasis #v[(1 : ℤ), 2, 3] (n := 3)
-- evaluation Nat.digits 2 8

/-- The `i`-th element of `lagrangeBasis w` is the product of `w[j]` if the `j`-th bit of `i` is 1,
    and `1 - w[j]` if the `j`-th bit of `i` is 0. -/
theorem lagrangeBasis_getElem {w : Vector R n} (i : Fin (2 ^ n)) :
    (lagrangeBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j] := by
  rw [lagrangeBasis]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]

private lemma lagrange_basis_even {n : ℕ} (x : Vector R (n + 1)) (j : Fin (2 ^ n)) :
    (lagrangeBasis x).get ⟨2 * j.val, by omega⟩ =
    (1 - x.head) * (lagrangeBasis x.tail).get j := by
  unfold lagrangeBasis
  simp only [Vector.get_ofFn]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [← Nat.bit_false_apply j.val]
  simp only [Nat.testBit_bit_zero, Bool.false_eq_true, ite_false]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [Nat.testBit_bit_succ]
  simp [Vector.tail_eq_cast_extract, Nat.add_comm]

private lemma lagrange_basis_odd {n : ℕ} (x : Vector R (n + 1)) (j : Fin (2 ^ n)) :
    (lagrangeBasis x).get ⟨2 * j.val + 1, by omega⟩ =
    x.head * (lagrangeBasis x.tail).get j := by
  unfold lagrangeBasis
  simp only [Vector.get_ofFn]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [← Nat.bit_true_apply j.val]
  simp only [Nat.testBit_bit_zero, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [Nat.testBit_bit_succ]
  simp [Vector.tail_eq_cast_extract, Nat.add_comm]

/-- Map a ring homomorphism over a `CMlPolynomialEval` -/
def map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (p : CMlPolynomialEval R n) : CMlPolynomialEval S n :=
  Vector.map (fun a => f a) p

/-- One multilinear-extension interpolation step, eliminating the next little-endian variable. -/
@[inline, specialize]
def evalMleStep {n : ℕ}
    (values : Vector R (2 ^ (n + 1))) (x0 : R) : Vector R (2 ^ n) :=
  Vector.ofFn fun j : Fin (2 ^ n) ↦
    (1 - x0) * values.get ⟨2 * j.val, by omega⟩ +
      x0 * values.get ⟨2 * j.val + 1, by omega⟩

/-- Public multilinear-extension interpolation layer. -/
@[inline, specialize]
def evalMleLayer {n : ℕ}
    (values : CMlPolynomialEval R (n + 1)) (x0 : R) : CMlPolynomialEval R n :=
  evalMleStep values x0

omit [CommRing R] in
/-- The `j`-th entry after one MLE layer is the affine interpolation of its input pair. -/
@[simp]
theorem evalMleLayer_get [CommRing R] {n : ℕ}
    (values : CMlPolynomialEval R (n + 1)) (x0 : R) (j : Fin (2 ^ n)) :
    (evalMleLayer values x0).get j =
      (1 - x0) * values.get ⟨2 * j.val, by omega⟩ +
        x0 * values.get ⟨2 * j.val + 1, by omega⟩ := by
  simp [evalMleLayer, evalMleStep]

/-- Evaluate hypercube values by recursively interpolating the multilinear extension. -/
@[inline, specialize]
def evalMleValues :
    {n : ℕ} → Vector R (2 ^ n) → Vector R n → R
  | 0, values, _ => values.get ⟨0, by norm_num⟩
  | n + 1, values, x =>
      evalMleValues (evalMleStep values x.head) x.tail

/-- Evaluate a `CMlPolynomialEval` by recursive multilinear-extension interpolation. -/
@[inline, specialize]
def evalMle (p : CMlPolynomialEval R n) (x : Vector R n) : R :=
  evalMleValues p x

omit [CommRing R] in
/-- Evaluating a zero-variable hypercube table returns its only value. -/
@[simp]
theorem evalMle_zero [CommRing R] (p : CMlPolynomialEval R 0) (x : Vector R 0) :
    evalMle p x = p.get ⟨0, by norm_num⟩ := by
  rfl

omit [CommRing R] in
/-- Recursive MLE evaluation first folds the head variable, then evaluates the tail. -/
@[simp]
theorem evalMle_succ [CommRing R] {n : ℕ}
    (p : CMlPolynomialEval R (n + 1)) (x : Vector R (n + 1)) :
    evalMle p x = evalMle (evalMleLayer p x.head) x.tail := by
  rfl

/-- Evaluate a `CMlPolynomialEval` through a ring homomorphism using multilinear-extension
interpolation. -/
@[inline, specialize]
def eval₂Mle (p : CMlPolynomialEval R n) (f : R →+* S) (x : Vector S n) : S :=
  evalMle (map f p) x

/-- Evaluate a `CMlPolynomialEval` at a point -/
def eval (p : CMlPolynomialEval R n) (x : Vector R n) : R :=
  Vector.dotProduct p (lagrangeBasis x)

/-- Evaluation commutes with scalar multiplication of a hypercube table. -/
@[simp] theorem eval_smul (a : R) (p : CMlPolynomialEval R n) (x : Vector R n) :
    eval (a • p) x = a * eval p x := by
  unfold eval
  rw [Vector.dotProduct_eq_root_dotProduct, Vector.dotProduct_eq_root_dotProduct]
  simp only [_root_.dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.get_eq_getElem (a • p) i, Vector.get_eq_getElem p i,
    Vector.getElem_smul]
  simp only [smul_eq_mul, mul_assoc]

/-- Evaluate a `CMlPolynomialEval` at a point using a ring homomorphism -/
def eval₂ (p : CMlPolynomialEval R n) (f : R →+* S) (x : Vector S n) : S := eval (map f p) x

/-- Evaluate the multilinear equality kernel `eq̃(w, x)`. -/
@[inline] def eqTilde (w x : Vector R n) : R :=
  eval (lagrangeBasis w) x

-- Theorems about evaluations

private lemma eval_mle_step_dot_product {n : ℕ}
    (p : CMlPolynomialEval R (n + 1)) (x : Vector R (n + 1)) :
    Vector.dotProduct (evalMleStep p x.head) (lagrangeBasis x.tail) =
    Vector.dotProduct p (lagrangeBasis x) := by
  rw [Vector.dotProduct_eq_root_dotProduct, Vector.dotProduct_eq_root_dotProduct]
  unfold _root_.dotProduct
  have hsplit :
      (∑ i : Fin (2 ^ (n + 1)), p.get i * (lagrangeBasis x).get i) =
        (∑ i : Fin (2 ^ n), p.get ⟨2 * i.val, by omega⟩ *
          (lagrangeBasis x).get ⟨2 * i.val, by omega⟩) +
        (∑ i : Fin (2 ^ n), p.get ⟨2 * i.val + 1, by omega⟩ *
          (lagrangeBasis x).get ⟨2 * i.val + 1, by omega⟩) := by
    convert (Fin.sum_univ_pow_two_even_add_odd (n := n)
        (f := fun i ↦ if h : i < 2 ^ (n + 1) then
          p.get ⟨i, h⟩ * (lagrangeBasis x).get ⟨i, h⟩ else 0)).symm using 1
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.is_lt, dite_eq_left]
    · congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [dite_eq_left (by omega)]
      · apply Finset.sum_congr rfl
        intro i _
        rw [dite_eq_left (by omega)]
  rw [hsplit]
  unfold evalMleStep
  simp only [Vector.get_ofFn]
  simp only [lagrange_basis_even, lagrange_basis_odd]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [add_mul]
  congr 1
  · rw [mul_comm (1 - x.head) (p.get ⟨2 * j.val, by omega⟩), mul_assoc]
  · rw [mul_comm x.head (p.get ⟨2 * j.val + 1, by omega⟩), mul_assoc]

/-- Multilinear-extension interpolation agrees with the dot-product evaluator. -/
theorem eval_mle_eq_eval (p : CMlPolynomialEval R n) (x : Vector R n) :
    evalMle p x = eval p x := by
  induction n with
  | zero =>
      rw [eval, Vector.dotProduct_eq_root_dotProduct]
      simp [evalMle, evalMleValues, lagrangeBasis, _root_.dotProduct]
  | succ n ih =>
      simp only [evalMle, evalMleValues]
      trans Vector.dotProduct (evalMleStep p x.head) (lagrangeBasis x.tail)
      · exact ih _ _
      · simp only [eval]
        exact eval_mle_step_dot_product p x

/-- The multilinear equality kernel is the product of its coordinatewise affine factors. -/
theorem eqTilde_eq_prod (w x : Vector R n) :
    eqTilde w x = ∏ i : Fin n, (w[i] * x[i] + (1 - w[i]) * (1 - x[i])) := by
  rw [eqTilde, ← eval_mle_eq_eval]
  induction n with
  | zero => simp [evalMle, evalMleValues]
  | succ n ih =>
      rw [evalMle_succ]
      have hstep : evalMleLayer (lagrangeBasis w) x.head =
          (w.head * x.head + (1 - w.head) * (1 - x.head)) • lagrangeBasis w.tail := by
        apply Vector.ext
        intro j hj
        rw [← Vector.get_eq_getElem (evalMleLayer (lagrangeBasis w) x.head) ⟨j, hj⟩]
        rw [← Vector.get_eq_getElem
          ((w.head * x.head + (1 - w.head) * (1 - x.head)) • lagrangeBasis w.tail)
          ⟨j, hj⟩]
        rw [evalMleLayer_get, lagrange_basis_even, lagrange_basis_odd]
        rw [Vector.get_eq_getElem
          ((w.head * x.head + (1 - w.head) * (1 - x.head)) • lagrangeBasis w.tail)
          ⟨j, hj⟩]
        rw [Vector.getElem_smul]
        simp only [smul_eq_mul]
        change (1 - x.head) * ((1 - w.head) * (lagrangeBasis w.tail).get ⟨j, hj⟩) +
            x.head * (w.head * (lagrangeBasis w.tail).get ⟨j, hj⟩) =
          (w.head * x.head + (1 - w.head) * (1 - x.head)) *
            (lagrangeBasis w.tail).get ⟨j, hj⟩
        ring
      rw [hstep, eval_mle_eq_eval, eval_smul, ← eval_mle_eq_eval, ih,
        Fin.prod_univ_succ]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by simp [Nat.add_comm]

/-- Evaluation is additive in the coefficient vector. -/
@[simp] theorem eval_add (p q : CMlPolynomialEval R n) (x : Vector R n) :
    eval (p + q) x = eval p x + eval q x := by
  unfold eval
  rw [Vector.dotProduct_eq_root_dotProduct, Vector.dotProduct_eq_root_dotProduct,
    Vector.dotProduct_eq_root_dotProduct]
  simp only [_root_.dotProduct, ← Finset.sum_add_distrib, ← add_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Vector.get_eq_getElem, Vector.getElem_add]

/-- The zero coefficient vector evaluates to zero. -/
@[simp] theorem eval_zero (x : Vector R n) : eval (0 : CMlPolynomialEval R n) x = 0 := by
  unfold eval
  rw [Vector.dotProduct_eq_root_dotProduct]
  simp only [_root_.dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Vector.get_eq_getElem, Vector.getElem_zero, zero_mul]

end CMlPolynomialLagrangeBasisAndEvaluations

end CMlPolynomialEval

namespace CMlPolynomial

-- Conversion between the coefficient (i.e. monomial) and evaluation (on the Boolean hypercube)
-- representations.

variable {R : Type*} [AddCommGroup R]

-- evaluation lagrangeToMono 2 #v[(78 : ℤ), 3, 4, 100]
-- evaluation lagrangeToMonoSpec (n:=2) #v[(78 : ℤ), 3, 4, 100]

end CMlPolynomial

end CompPoly

/-! ### evaluation Tests

This section contains tests to verify the functionality of multilinear polynomial operations.
-/
section Tests

-- evaluation CMlPolynomial.zero (n := 2) (R := ℤ)
-- evaluation CMlPolynomial.add #v[1, 2, 3, 4] #v[5, 6, 7, 8] (n := 2) (R := ℤ)
-- evaluation CMlPolynomial.smul 2 #v[1, 2, 3, 4] (n := 2) (R := ℤ)
-- evaluation CMlPolynomialEval.lagrangeBasis #v[(1 : ℤ), 2, 3] (n := 3)
-- evaluation CMlPolynomialEval.lagrangeBasis #v[(1 : ℤ), 2] (n := 2)
-- evaluation CMlPolynomialEval.eval #v[1, 2, 3, 4] #v[(1 : ℤ), 2] (n := 2)
-- evaluation CMlPolynomial.monoToLagrange 2 #v[(1 : ℤ), 2, 3, 4]
-- evaluation CMlPolynomial.lagrangeToMono 2 #v[(1 : ℤ), 3, 4, 10]
-- evaluation CMlPolynomial.lagrangeToMono 2 (CMlPolynomial.monoToLagrange 2 #v[(1 : ℤ), 2, 3, 4])
-- evaluation CMlPolynomial.monoToLagrange 2 (CMlPolynomial.lagrangeToMono 2 #v[(1 : ℤ), 3, 4, 10])
-- evaluation CMlPolynomial.monoToLagrange 1 #v[(1 : ℤ), 2]
-- evaluation CMlPolynomial.monoToLagrange 3 #v[(1 : ℤ), 2, 3, 4, 5, 6, 7, 8]
-- evaluation CMlPolynomialEval.lagrangeBasis #v[(1 : ℤ)] (n := 1)
-- evaluation CMlPolynomialEval.lagrangeBasis #v[(1 : ℤ), 2, 3, 4] (n := 4)
-- evaluation (CMlPolynomial.mk 2 #v[1, 2, 3, 4]) + (CMlPolynomial.mk 2 #v[5, 6, 7, 8])
-- evaluation ((4: ℤ) • (CMlPolynomial.mk 2 #v[(1: ℤ), 2, 3, 4]))

end Tests
