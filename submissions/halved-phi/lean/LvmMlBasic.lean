-- Vendored from `CompPoly/CompPoly/Multilinear/Basic.lean` (the contract's pin of the package) as `LvmMlBasic` for lvm (WP-2).
/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Aristotle (Harmonic), Elias Judin
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import LvmMlListLemmas
import CompPoly.Data.Nat.Bitwise
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.Fold
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

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

theorem foldl_succ
    {α β} {n : ℕ} [NeZero n] (f : β → α → β) (init : β) (v : Vector α n) :
    v.foldl (f:=f) (b:=init) = v.tail.foldl (f:=f) (b:=f init v.head) := by
  rw [foldl_eq_toList_foldl, foldl_eq_toList_foldl]
  rw [toList_tail]
  have h_ne : v.toList ≠ [] := by
    simp only [ne_eq, toList_eq_nil_iff]
    exact NeZero.ne n
  rw [List.foldl_split_inner f init v.toList h_ne]
  congr 2
  simp only [head, List.head_eq_getElem, getElem_toList]

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

/-- Accumulate paired products from equal-length vectors, from left to right, starting at `init`.
The products and accumulator lie in `W`; no reduction is performed. -/
def accumulateProducts {W : Type*} [Add W] (product : R → R → W) (init : W)
    (a b : Vector R n) : W :=
  a.zipWith product b |>.foldl (· + ·) init

/-- If reduction preserves addition and each paired product, reducing the accumulator gives
the reduced initial value plus the dot product of the input vectors. -/
theorem reduce_accumulateProducts {W : Type*} [AddZero W] [AddMonoid R] [Mul R]
    (reduce : W →+ R) (product : R → R → W)
    (hproduct : ∀ x y, reduce (product x y) = x * y) (init : W) (a b : Vector R n) :
    reduce (accumulateProducts product init a b) = reduce init + dotProduct a b := by
  have hmap : (a.zipWith product b).map reduce = a.zipWith (· * ·) b := by
    ext i
    simp only [getElem_map, getElem_zipWith, hproduct]
  calc
    reduce (accumulateProducts product init a b) =
        ((a.zipWith product b).map reduce).foldl (· + ·) (reduce init) :=
      (foldl_map_hom (fun x y => (map_add reduce x y).symm)).symm
    _ = (a.zipWith (· * ·) b).foldl (· + ·) (reduce init) := by rw [hmap]
    _ = reduce init + dotProduct a b := by
      simpa only [dotProduct, _root_.add_zero] using
        (foldl_assoc (op := (· + ·)) (xs := a.zipWith (· * ·) b)
          (a₁ := reduce init) (a₂ := 0))

/-- Reducing a product accumulator initialized at zero recovers the dot product. -/
theorem reduce_accumulateProducts_zero {W : Type*} [AddZero W] [AddMonoid R] [Mul R]
    (reduce : W →+ R) (product : R → R → W)
    (hproduct : ∀ x y, reduce (product x y) = x * y) (a b : Vector R n) :
    reduce (accumulateProducts product 0 a b) = dotProduct a b := by
  rw [reduce_accumulateProducts reduce product hproduct, map_zero, _root_.zero_add]

/-- Ordinary multiplication is an eager product accumulator, with identity reduction. -/
theorem accumulateProducts_mul [AddMonoid R] [Mul R] (init : R) (a b : Vector R n) :
    accumulateProducts (· * ·) init a b = init + dotProduct a b :=
  reduce_accumulateProducts (AddMonoidHom.id R) (· * ·) (fun _ _ => rfl) init a b

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
/-- Matrix-vector multiplication over `α`.
`M` is given as a vector of row-vectors. -/
def mulVec [Zero α] [Add α] [Mul α] {numRows numCols : Nat}
    (M : Vector (Vector α numCols) numRows)
  (x : Vector α numCols) : Vector α numRows :=
  M.map (fun row => row *ᵥ x)

/-- Convert a flat row-major vector of length `m*n` into an `m × n` row-major matrix
represented as `Vector (Vector α n) m`. -/
def ofFlatten {m n : ℕ} (v : Vector α (m * n)) : Matrix α m n :=
  (Vector.finRange m).map (fun i => (v.extract (i.val * n) (i.val * n + n)).cast
    (by
    -- Why can't `omega`, `aesop`, `grind`, etc. solve this?
      rcases i with ⟨i, h⟩
      have : i * n + n ≤ m * n := by
        calc
        _ = (i + 1) * n := by ring
        _ ≤ m * n := by gcongr; exact h
      simp [this]))

/-- Convert to a `Fin`-indexed matrix (the definition in Mathlib): `Fin m → Fin n → α` -/
def toFinMatrix {m n : ℕ} (matrix : Matrix α m n) : _root_.Matrix (Fin m) (Fin n) α :=
  fun i j => (matrix.get i).get j

/-- Convert from a `Fin`-indexed matrix (the definition in Mathlib): `Fin m → Fin n → α` -/
def ofFinMatrix {m n : ℕ} (matrix : _root_.Matrix (Fin m) (Fin n) α) : Matrix α m n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => matrix i j))

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

/-- A ring homomorphism maps a dot product to the dot product of the mapped vectors. -/
theorem map_dotProduct {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) {n : ℕ} (a b : Vector R n) :
    f (dotProduct a b) = dotProduct (a.map f) (b.map f) := by
  rw [dotProduct_eq_root_dotProduct, f.map_dotProduct, dotProduct_eq_root_dotProduct]
  congr 1 <;> funext i <;>
    simp only [Function.comp_apply, Vector.get_eq_getElem, Vector.getElem_map]

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

instance inhabited [Inhabited R] : Inhabited (CMlPolynomial R n) := by
  simp [CMlPolynomial]; infer_instance

/-- Conform a list of coefficients to a `CMlPolynomial` with a given number of variables.
    May either pad with zeros or truncate. -/
@[inline]
def ofArray [Zero R] (coeffs : Array R) (n : ℕ) : CMlPolynomial R n :=
  .ofFn (fun i => if h : i.1 < coeffs.size then coeffs[i] else 0)
  -- ⟨((coeffs.take (2 ^ n)).rightpad (2 ^ n) 0 : Array R), by simp⟩
  -- Not sure which is better performance wise?

-- Create a zero polynomial over n variables
@[inline]
def zero [Zero R] : CMlPolynomial R n := Vector.replicate (2 ^ n) 0

lemma zero_def [Zero R] : zero = Vector.replicate (2 ^ n) 0 := rfl

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

/-- Mapping each monomial-basis value by a ring homomorphism equals evaluating the
monomial basis at the mapped point. -/
theorem map_monomialBasis (f : R →+* S) (x : Vector R n) :
    (monomialBasis x).map f = monomialBasis (x.map f) := by
  ext i hi
  simp only [Vector.getElem_map, monomialBasis, Vector.getElem_ofFn, map_prod,
    apply_ite, map_one, Fin.getElem_fin]

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

/-- Mapping a coefficient-form evaluation by a ring homomorphism equals evaluating the
mapped coefficients at the mapped point. -/
theorem map_eval (f : R →+* S) (p : CMlPolynomial R n) (x : Vector R n) :
    f (eval p x) = eval (map f p) (x.map f) := by
  unfold eval
  rw [Vector.map_dotProduct, map_monomialBasis]
  rfl

/-- Evaluate monomial coefficients by accumulating their products with the monomial-basis
values in `W`, starting at zero, then reducing once to a value in `R`. -/
def evalWithProducts {W : Type*} [AddZero W] (product : R → R → W) (reduce : W →+ R)
    (p : CMlPolynomial R n) (x : Vector R n) : R :=
  reduce (Vector.accumulateProducts product 0 p (monomialBasis x))

/-- Product accumulation followed by additive reduction agrees with coefficient evaluation
when reducing each product gives the ordinary product of its two factors. -/
theorem evalWithProducts_eq_eval {W : Type*} [AddZero W]
    (product : R → R → W) (reduce : W →+ R)
    (hproduct : ∀ a b, reduce (product a b) = a * b)
    (p : CMlPolynomial R n) (x : Vector R n) :
    evalWithProducts product reduce p x = eval p x :=
  Vector.reduce_accumulateProducts_zero reduce product hproduct p (monomialBasis x)

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

/-- Horner evaluation through a ring homomorphism agrees with the dot-product evaluator. -/
theorem eval₂_horner_eq_eval₂ (p : CMlPolynomial R n) (f : R →+* S) (x : Vector S n) :
    eval₂Horner p f x = eval₂ p f x := by
  simpa [eval₂Horner, eval₂] using
    (eval_horner_eq_eval (p := map f p) (x := x))
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

instance inhabited [Inhabited R] : Inhabited (CMlPolynomialEval R n) := by
  simp only [CMlPolynomialEval]; infer_instance

/-- Conform a list of coefficients to a `CMlPolynomialEval` with a given number of variables.
    May either pad with zeros or truncate. -/
@[inline]
def ofArray [Zero R] (coeffs : Array R) (n : ℕ) : CMlPolynomialEval R n :=
  .ofFn (fun i => if h : i.1 < coeffs.size then coeffs[i] else 0)
  -- ⟨((coeffs.take (2 ^ n)).rightpad (2 ^ n) 0 : Array R), by simp⟩
  -- Not sure which is better performance wise?

-- Create a zero polynomial over n variables
@[inline]
def zero [Zero R] : CMlPolynomialEval R n := Vector.replicate (2 ^ n) 0

lemma zero_def [Zero R] : zero = Vector.replicate (2 ^ n) 0 := rfl

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

/-- The equality kernel factors across appended coordinate blocks. -/
theorem eqTilde_append {m : ℕ} (w₁ x₁ : Vector R n) (w₂ x₂ : Vector R m) :
    eqTilde (w₁ ++ w₂) (x₁ ++ x₂) = eqTilde w₁ x₁ * eqTilde w₂ x₂ := by
  simp only [eqTilde_eq_prod]
  rw [Fin.prod_univ_add]
  congr 1 <;> exact Finset.prod_congr rfl fun i _ => by simp

/-- Multilinear-extension interpolation through a ring homomorphism agrees with the
dot-product evaluator. -/
theorem eval₂_mle_eq_eval₂ (p : CMlPolynomialEval R n) (f : R →+* S) (x : Vector S n) :
    eval₂Mle p f x = eval₂ p f x := by
  simpa [eval₂Mle, eval₂] using
    (eval_mle_eq_eval (p := map f p) (x := x))

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

/-- **One level** of the zeta‑transform (coefficient to evaluation).

Processes the `j`-th variable by folding the "partner" index (with bit `j` cleared) into
every index that has bit `j` set. At output index `i`:
$$ (\text{monoToLagrangeLevel}\ j\ v)[i] \ =\ \begin{cases}
  v[i] + v[i - 2^j] & \text{if bit } j \text{ of } i \text{ is } 1 \\
  v[i] & \text{otherwise}
\end{cases} $$

After applying every level `0, 1, …, n-1` the resulting entry at `i` is
$\sum_{j \subseteq i} p[j]$ (bitwise subset), which is the hypercube evaluation at the
Boolean point encoded by `i`. Cost per level: $O(2^n)$ additions, so the full transform
is $O(n \cdot 2^n)$.

The `stride` is $2^j$, the distance between indices that differ only in bit `j`.
-/
@[inline] def monoToLagrangeLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    let stride : ℕ := 2 ^ j.val    -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] + v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full zeta transform**: coefficients → evaluations.

Applies `monoToLagrangeLevel 0, 1, …, n-1` in that order via `foldl`. The resulting entry
at each index `i : Fin (2 ^ n)` is $\sum_{j \subseteq i} p[j]$ (the classical zeta
transform on the Boolean lattice).

**Complexity:** $O(n \cdot 2^n)$ additions — this is the butterfly form. Contrast with
the naive `monoToLagrangeSpec` which is $O(4^n)$. -/
@[inline] def monoToLagrange (n : ℕ) : CMlPolynomial R n → CMlPolynomialEval R n :=
  (List.finRange n).foldl (fun acc level => monoToLagrangeLevel level acc)

/-- **One level** of the inverse zeta‑transform / Möbius transform (evaluation to
coefficient).

Processes the `j`-th variable by subtracting the partner entry (bit `j` cleared) from
every index that has bit `j` set. At output index `i`:
$$ (\text{lagrangeToMonoLevel}\ j\ v)[i] \ =\ \begin{cases}
  v[i] - v[i - 2^j] & \text{if bit } j \text{ of } i \text{ is } 1 \\
  v[i] & \text{otherwise}
\end{cases} $$

Each level is the exact inverse of `monoToLagrangeLevel j` (see
`lagrangeToMonoLevel_monoToLagrangeLevel_id`).

The `stride` is $2^j$.
-/
@[inline] def lagrangeToMonoLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    let stride : ℕ := 2 ^ j.val  -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] - v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full inverse / Möbius transform**: evaluations → coefficients.

Applies `lagrangeToMonoLevel (n-1), (n-2), …, 0` via `foldr`. The resulting entry at
each index `i : Fin (2 ^ n)` is the inclusion-exclusion sum
$\sum_{j \subseteq i} (-1)^{\mathrm{popCount}(i) - \mathrm{popCount}(j)} \cdot p[j]$ —
see `lagrangeToMono_eq_lagrangeToMonoSpec`.

**Complexity:** $O(n \cdot 2^n)$ additions/subtractions. Contrast with the naive
`lagrangeToMonoSpec` which is $O(4^n)$. -/
@[inline]
def lagrangeToMono (n : ℕ) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  (List.finRange n).foldr (fun h acc => lagrangeToMonoLevel h acc)

/-- The $O(4^n)$ inclusion-exclusion specification for the Möbius transform.

For each output index `i`, this sums over all indices `j` that are bitwise subsets of `i`
(`i &&& j = j`), with sign
$(-1)^{\mathrm{popCount}(i) - \mathrm{popCount}(j)}$:
$$ (\text{lagrangeToMonoSpec}\ p)[i]
  = \sum_{j \subseteq i} (-1)^{\mathrm{popCount}(i) - \mathrm{popCount}(j)} \cdot p[j]. $$

Provable equivalent to the fast `lagrangeToMono` — see `lagrangeToMono_eq_lagrangeToMonoSpec`.
-/
def lagrangeToMonoSpec (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  -- We define the output vector by specifying the value for each entry `i`.
  Vector.ofFn (fun i =>
    -- For each output entry `i`, we compute a sum over all possible input indices `j`.
    Finset.sum Finset.univ (fun j =>
      -- The sum is only over `j` that are bitwise subsets of `i`.
      if (i.val &&& j.val = j.val) then
        -- The term is added or subtracted based on the parity of the difference
        -- in the number of set bits (Hamming weight).
        if (i.val.popCount - j.val.popCount) % 2 = 0 then
          p.get j -- Add if the difference is even
        else
          -p.get j -- Subtract if the difference is odd
      else
        0 -- If j is not a subset of i, the term is zero.
    )
  )

/-- The $O(4^n)$ specification for the zeta transform (the mirror of
`lagrangeToMonoSpec`).

For each output index `i`, this sums `p[j]` over every index `j` that is a bitwise subset
of `i` (`i &&& j = j`):
$$ (\text{monoToLagrangeSpec}\ p)[i]\ =\ \sum_{j \subseteq i} p[j]. $$

Provable equivalent to the fast `monoToLagrange` — see `monoToLagrange_eq_monoToLagrangeSpec`.
-/
def monoToLagrangeSpec (p : CMlPolynomial R n) : CMlPolynomialEval R n :=
  Vector.ofFn (fun i ↦
    Finset.sum Finset.univ (fun j ↦
      if (i.val &&& j.val = j.val) then p.get j else 0))

-- evaluation lagrangeToMono 2 #v[(78 : ℤ), 3, 4, 100]
-- evaluation lagrangeToMonoSpec (n:=2) #v[(78 : ℤ), 3, 4, 100]

/--
Generates a list of indices representing a range of bit positions [l, r] in increasing order.
Used for optimized recursive transforms that operate on segments of variables.
Returns a list containing `l, l+1, ..., r`.
The result is used to fold over dimensions in `monoToLagrangeSegment` and `lagrangeToMonoSegment`.
-/
def forwardRange (n : ℕ) (r : Fin (n)) (l : Fin (r.val + 1)) : List (Fin n) :=
  let len := r.val - l.val + 1
  List.ofFn (fun (k : Fin len) =>
    let val := l.val + k.val
    have h_bound : val < n := by omega
    ⟨val, h_bound⟩
  )

lemma forwardRange_length (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :
    (forwardRange n r l).length = r.val - l.val + 1 := by
  unfold forwardRange
  simp only [List.length_ofFn]

lemma forwardRange_eq_of_r_eq (n : ℕ) (r1 r2 : Fin n) (h_r_eq : r1 = r2) (l : Fin (r1.val + 1)) :
    forwardRange n r1 l = forwardRange n r2 ⟨l, by omega⟩ := by
  subst h_r_eq
  rfl

lemma forwardRange_getElem (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) (k : Fin (r.val - l.val + 1)) :
    (forwardRange n r l).get ⟨k, by
    rw [forwardRange]; simp only [List.length_ofFn]; omega⟩ = ⟨l.val + k, by omega⟩ := by
  unfold forwardRange
  simp only [List.get_eq_getElem]
  simp only [List.getElem_ofFn]

lemma forwardRange_succ_right_ne_empty (n : ℕ) (r : Fin (n - 1)) (l : Fin (r.val + 1)) :
    forwardRange n ⟨r + 1, by omega⟩ ⟨l, by simp only; omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_pred_le_ne_empty (n : ℕ) (r : Fin n) (l : Fin (r.val + 1))
    (h_l_gt_0 : l.val > 0) : forwardRange n r ⟨l.val - 1, by omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_dropLast (n : ℕ) (r : Fin (n - 1)) (l : Fin (r.val + 1)) :
    (forwardRange n ⟨r + 1, by omega⟩ ⟨l, by simp only; omega⟩).dropLast
  = forwardRange n ⟨r, by omega⟩ ⟨l, by simp only [Fin.is_lt]⟩ := by
  apply List.ext_getElem
  · rw [List.length_dropLast, forwardRange_length, forwardRange_length]
    simp only [add_tsub_cancel_right]
    omega
  · intro i h₁ h₂
    simp only [List.length_dropLast, forwardRange_length, add_tsub_cancel_right, Fin.eta] at h₁ h₂
    simp only [List.getElem_dropLast, Fin.eta]
    have hleft := forwardRange_getElem n
      ⟨r.val + 1, by omega⟩ ⟨l, by simp only; omega⟩ (k:=⟨i, by simp only; omega⟩)
    have hright := forwardRange_getElem n
      ⟨r.val, by omega⟩ ⟨l, by simp only; omega⟩ (k:=⟨i, by simp only; omega⟩)
    simp only [List.get_eq_getElem, Fin.eta] at hleft hright
    rw [hleft, hright]

lemma forwardRange_tail (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) (h_l_gt_0 : l.val > 0) :
    (forwardRange n r ⟨l.val - 1, by omega⟩).tail = forwardRange n r l := by
  apply List.ext_getElem
  · rw [List.length_tail, forwardRange_length, forwardRange_length]
    simp only [add_tsub_cancel_right]
    omega
  · intro i h₁ h₂
    simp only [List.length_tail, forwardRange_length, add_tsub_cancel_right] at h₁ h₂
    simp only [List.getElem_tail]
    have hleft := forwardRange_getElem n r ⟨l.val - 1, by omega⟩ (k:=⟨i + 1, by simp only; omega⟩)
    have hright := forwardRange_getElem n r l (k:=⟨i, by omega⟩)
    simp only [List.get_eq_getElem] at hleft hright
    rw [hleft, hright]
    rw [Fin.mk.injEq, Nat.add_comm i 1, ←Nat.add_assoc, Nat.sub_one_add_one (a:=l.val) (by omega)]

lemma forwardRange_0_eq_finRange (n : ℕ) [NeZero n] : forwardRange n ⟨n - 1, by
    have h_ne_zero : n ≠ 0 := NeZero.ne n
    omega
  ⟩ 0 = List.finRange n := by
  apply List.ext_get
  · rw [forwardRange_length, List.length_finRange]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero]
    have : n ≥ 1 := by
      exact NeZero.one_le
    simp_all only [ge_iff_le, Nat.sub_add_cancel]
  · intro i hi h₂
    have h_fr_get := forwardRange_getElem (n:=n) (r:=⟨n - 1, by grind⟩) (l:=0) (k:=⟨i, by
      rw [forwardRange_length] at hi
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero] at hi
      exact hi
    ⟩)
    simpa [forwardRange] using h_fr_get

/--
Performs the zeta-transform (coefficient to evaluation) on a segment of dimensions from `l` to `r`.
Iteratively applies `monoToLagrangeLevel` for each dimension in the range.
`0 ≤ l ≤ r < n`.
-/
def monoToLagrangeSegment (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  let range := forwardRange n r l
  (range.foldl (fun acc h => monoToLagrangeLevel h acc))

/--

Performs the inverse zeta-transform (evaluation to coefficient) on a segment of dimensions

from `l` to `r`.

Iteratively applies `lagrangeToMonoLevel` for each dimension in the range (in reverse order).

`0 ≤ l ≤ r < n`.

-/
def lagrangeToMonoSegment (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :

    Vector R (2 ^ n) → Vector R (2 ^ n) :=

  let range := forwardRange n r l

  (range.foldr (fun h acc => lagrangeToMonoLevel h acc))

lemma monoToLagrange_eq_monoToLagrangeSegment (n : ℕ) [NeZero n] (v : Vector R (2 ^ n)) :
    have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  monoToLagrange n v = monoToLagrangeSegment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold monoToLagrange monoToLagrangeSegment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma lagrangeToMono_eq_lagrangeToMonoSegment (n : ℕ) [NeZero n] (v : Vector R (2 ^ n)) :
    have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  lagrangeToMono n v = lagrangeToMonoSegment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold lagrangeToMono lagrangeToMonoSegment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma testBit_of_sub_two_pow_of_bit_1 {n i : ℕ} (h_testBit_eq_1 : (n).testBit i = true) :
    (n - 2^i).testBit i = false := by
  have h := Nat.testBit_false_eq_getBit_eq_0 (n:=n - 2^i) (k:=i)
  rw [h]
  have h_getBit_eq_0: Nat.getBit i (n - 2^i) = 0 := by
    rw [Nat.getBit_of_sub_two_pow_of_bit_1]
    simp only [↓reduceIte]
    rw [Nat.testBit_true_eq_getBit_eq_1] at h_testBit_eq_1
    exact h_testBit_eq_1
  exact h_getBit_eq_0

theorem lagrangeToMonoLevel_monoToLagrangeLevel_id (v : Vector R (2 ^ n)) (i : Fin n) :
    lagrangeToMonoLevel i (monoToLagrangeLevel i v) = v := by
  unfold lagrangeToMonoLevel monoToLagrangeLevel
  simp only [Vector.getElem_ofFn]
  ext i1 i1_isLt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have hi1_lt : i1 < 2 ^ n := by
      simpa using i1_isLt
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      exact Nat.sub_lt_of_lt hi1_lt
    have h_as_assoc := add_sub_assoc (a:=v[i1]'(by omega))
      (b:=v[i1 - 2 ^ i.val]'(h_id_lt)) (c:=v[i1 - 2 ^ i.val]'(h_id_lt))
    rw [h_as_assoc, sub_self, add_zero]
  else
    simp only [h_i1_testBit, Bool.false_eq_true, ↓reduceIte]

theorem monoToLagrangeLevel_lagrangeToMonoLevel_id (v : Vector R (2 ^ n)) (i : Fin n) :
    monoToLagrangeLevel i (lagrangeToMonoLevel i v) = v := by
  unfold lagrangeToMonoLevel monoToLagrangeLevel
  simp only [Vector.getElem_ofFn]
  ext i1 i1_isLt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have hi1_lt : i1 < 2 ^ n := by
      simpa using i1_isLt
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      exact Nat.sub_lt_of_lt hi1_lt
    rw [sub_add_cancel]
  else
    simp only [h_i1_testBit, Bool.false_eq_true, ↓reduceIte]

theorem mobius_apply_zeta_apply_eq_id (n : ℕ) [NeZero n] (r : Fin n) (l : Fin (r.val + 1))
    (v : Vector R (2 ^ n)) : lagrangeToMonoSegment n r l (monoToLagrangeSegment n r l v) = v := by
  induction r using Fin.succRecOnSameFinType with
  | zero =>
    rw [lagrangeToMonoSegment, monoToLagrangeSegment, forwardRange]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_eq_zero, tsub_self, zero_add,
      List.ofFn_succ, Fin.isValue, Fin.cast_zero, Nat.mod_succ, add_zero, Fin.mk_zero',
      Fin.val_cast, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
      List.foldr_cons, List.foldr_nil]
    exact lagrangeToMonoLevel_monoToLagrangeLevel_id v 0
  | succ r1 r1_lt_n h_r1 =>
    unfold lagrangeToMonoSegment monoToLagrangeSegment
    if h_l_eq_r: l.val = (r1 + 1).val then
      rw [forwardRange]
      simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ,
        List.foldl_cons, List.foldr_cons]
      simp_rw [h_l_eq_r]
      simp only [Fin.eta, tsub_self, List.ofFn_zero, List.foldl_nil, List.foldr_nil]
      exact lagrangeToMonoLevel_monoToLagrangeLevel_id v (r1 + 1)
    else
      have h_l_lt_r: l.val < (r1 + 1).val := by omega
      have h_r1_add_1_val: (r1 + 1).val = r1.val + 1 := by
        rw [Fin.val_add_one']; omega
      have h_range_ne_empty: forwardRange n (r1 + 1) l ≠ [] := by
        have h:= forwardRange_succ_right_ne_empty n
          (r:=⟨r1, by omega⟩) (l:=⟨l, by simp only; omega⟩)
        simp only [ne_eq] at h
        have h_r1_add_1: r1 + 1 = ⟨r1.val + 1, by omega⟩ := by
          exact Fin.eq_mk_iff_val_eq.mpr h_r1_add_1_val
        rw [forwardRange_eq_of_r_eq (r1:=r1 + 1) (r2:=⟨r1.val + 1, by omega⟩) (h_r_eq:=h_r1_add_1)]
        exact h
      rw [List.foldr_split_inner (h:=h_range_ne_empty)]
      rw [List.foldl_split_outer (h:=h_range_ne_empty)]
      rw [lagrangeToMonoLevel_monoToLagrangeLevel_id]
      have h_inductive := h_r1 (l := ⟨l, by exact Nat.lt_of_lt_of_eq h_l_lt_r h_r1_add_1_val⟩)
      rw [lagrangeToMonoSegment, monoToLagrangeSegment] at h_inductive
      simp only at h_inductive
      have h_range_droplast: (forwardRange n (r1 + 1) l).dropLast
        = forwardRange n r1 ⟨↑l, by omega⟩ := by
        have h := forwardRange_dropLast n (r:=⟨r1, by omega⟩) (l:=⟨l, by simp only; omega⟩)
        simp only [Fin.eta] at h
        convert h
      convert h_inductive

lemma zeta_apply_mobius_apply_eq_id (n : ℕ) (r : Fin n) (l : Fin (r.val + 1))
    (v : Vector R (2 ^ n)) :
    monoToLagrangeSegment n r l (lagrangeToMonoSegment n r l v) = v := by
  induction l using Fin.predRecOnSameFinType with
  | last =>
    rw [lagrangeToMonoSegment, monoToLagrangeSegment, forwardRange]
    simp only [add_tsub_cancel_right, tsub_self, zero_add, List.ofFn_succ, Nat.add_one_sub_one,
      Fin.isValue, Fin.cast_zero, Fin.coe_ofNat_eq_mod, Nat.mod_succ, add_zero, Fin.eta,
      Fin.val_cast, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
      List.foldl_cons, List.foldl_nil]
    exact monoToLagrangeLevel_lagrangeToMonoLevel_id v r
  | succ l1 l1_gt_0 h_l1 =>
    unfold lagrangeToMonoSegment monoToLagrangeSegment
    have h_l1_sub_1_lt_r: (⟨l1.val - 1, by omega⟩: Fin (r.val + 1)).val < r.val := by
      simp only
      have h_l1 := l1.isLt
      apply Nat.lt_of_add_lt_add_right (n:=1)
      rw [Nat.sub_one_add_one (by omega)]
      omega
    have h_range_ne_empty: forwardRange n r ⟨l1.val - 1, by omega⟩ ≠ [] := by
      have h:= forwardRange_pred_le_ne_empty n
        (r:=⟨r, by omega⟩) (l:=⟨l1, by simp only; omega⟩) (by omega)
      simp only [ne_eq, h, not_false_eq_true]
    rw [List.foldr_split_outer (h:=h_range_ne_empty)]
    rw [List.foldl_split_inner (h:=h_range_ne_empty)]
    rw [monoToLagrangeLevel_lagrangeToMonoLevel_id]
    have h_inductive := h_l1
    rw [lagrangeToMonoSegment, monoToLagrangeSegment] at h_inductive
    simp only at h_inductive
    have h_range_tail: (forwardRange n r ⟨l1.val - 1, by omega⟩).tail = forwardRange n r l1 := by
      have h := forwardRange_tail n (r:=r) (l:=l1) (by omega)
      convert h
    convert h_inductive

/--
The equivalence between the monomial basis representation (`CMlPolynomial`)
and the Lagrange basis representation (`CMlPolynomialEval`) of a multilinear polynomial.
The forward map is `monoToLagrange` (zeta transform) and the inverse is `lagrangeToMono`
(inverse zeta transform/Mobius transform).
-/
def equivMonomialLagrangeRepr : CMlPolynomial R n ≃ CMlPolynomialEval R n where
  toFun := monoToLagrange n
  invFun := lagrangeToMono n
  left_inv v := by
    if h_n_eq_0: n = 0 then
      subst h_n_eq_0; rfl
    else
      have h_n_ne_zero: n ≠ 0 := by omega
      let: NeZero n := by exact { out := h_n_eq_0 }
      rw [lagrangeToMono_eq_lagrangeToMonoSegment (n:=n)]
      rw [monoToLagrange_eq_monoToLagrangeSegment (n:=n)]
      simp only [Fin.zero_eta]
      exact
        mobius_apply_zeta_apply_eq_id n
          ⟨n - 1, by have := NeZero.ne n; omega⟩
          0 v
  right_inv v := by
    if h_n_eq_0: n = 0 then
      subst h_n_eq_0; rfl
    else
      have h_n_ne_zero: n ≠ 0 := by omega
      let: NeZero n := by exact { out := h_n_eq_0 }
      rw [lagrangeToMono_eq_lagrangeToMonoSegment (n:=n)]
      rw [monoToLagrange_eq_monoToLagrangeSegment (n:=n)]
      exact
        zeta_apply_mobius_apply_eq_id n
          ⟨n - 1, by have := NeZero.ne n; omega⟩
          ⟨0, by have := NeZero.ne n; omega⟩
          v

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
