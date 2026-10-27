-- New for `flock-recursive` (BLUEPRINT B-4, §2.1). The fast twin and its correctness proof follow
-- `submissions/spartan-srom/lean/SpartanSromFieldExt.lean` and `SpartanSromFieldExtCorrect.lean`
-- (this repository, branch `v4/flock-recursive` at `30b6999`): the map to CompPoly's `Ext`, the
-- coordinates `c₀ + c₁ g`, the transported `CommRing` and `Field`.
import FRFieldBaseCorrect
import CompPoly.Fields.Extension
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Basic

/-!
# `GF(2^128)` as a quadratic extension of `GF(2^64)`

The specification is CompPoly's computable extension framework over CompPoly's `BF64`:

* `BF128 := Ext f128Params`, the quotient `BF64[y] / (y^2 + y + β)` with `β = x^63`
  (`B64.beta`, `betaBF`); its `Field` instance is CompPoly's `Ext.instField`, which needs the
  irreducibility of the modulus.
* **Irreducibility by the trace criterion** (`quadratic_irreducible`): over a field `L` of `2^n`
  elements, a root `r` of `X^2 + X + γ` gives `γ = r^2 + r`, so the absolute trace
  `∑_{i<n} γ^(2^i)` telescopes to `r^(2^n) + r = 0`. The trace of `β` is `1`
  (`absTrace_beta`), evaluated by the kernel on the word arithmetic (`B64.frobSum_beta`).

The fast twin `F` stores the two coefficients of `c₀ + c₁ y` as `B64` words:

* addition is coefficientwise `xor`;
* multiplication is Karatsuba over the coefficients with lazy reduction: three unreduced
  `clmul64` products, `c₁ = (a₀ + a₁)(b₀ + b₁) + a₀ b₀` and `c₀ = a₀ b₀ + β a₁ b₁`, where
  `β a₁ b₁` is the reduced `a₁ b₁` shifted by `63`, three `reduce` in all (`y^2 = y + β`);
* squaring is `(c₀^2 + β c₁^2) + c₁^2 y`;
* inversion is by the norm to `GF(2^64)`: `(c₀ + c₁ y)((c₀ + c₁) + c₁ y) = c₀ (c₀ + c₁) + β c₁^2`,
  one `B64` inversion;
* bytes are the two coefficients' eight little-endian bytes, `c₀` first (BLUEPRINT §1).

`F.toExt : F → BF128` sends `⟨c₀, c₁⟩` to the coefficient vector of `BF128`; it commutes with every
operation (`toExt_mul`, `toExt_sq`, `toExt_inv`, …), is a ring isomorphism (`ringEquivBF128`), and
`F` is a field through it (`F.instField`), with `2^128` elements (`card_F`).
-/

namespace FR

open Polynomial CompPoly.Extension

/-! ## The trace criterion -/

/-- The absolute trace `∑_{i < n} a^(2^i)` of a field of `2^n` elements to `GF(2)`. -/
def absTrace {L : Type*} [CommRing L] (n : ℕ) (a : L) : L := ∑ i ∈ Finset.range n, a ^ 2 ^ i

/-- **The trace criterion**: over a field of `2^n` elements, `X^2 + X + γ` is irreducible when the
absolute trace of `γ` is not zero. -/
theorem quadratic_irreducible {L : Type*} [Field L] [Finite L] [CharP L 2] {n : ℕ}
    (hcard : Nat.card L = 2 ^ n) {γ : L} (htr : absTrace n γ ≠ 0) :
    Irreducible (X ^ 2 + X + C γ : L[X]) := by
  have hdeg : (X ^ 2 + X + C γ : L[X]).natDegree = 2 := by compute_degree!
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [hdeg]; decide) fun r hr => htr ?_
  have hγ : γ = r ^ 2 + r := by
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hr
    linear_combination hr + (-(r ^ 2 + r)) * CharTwo.two_eq_zero (R := L)
  have hterm : ∀ i, (r ^ 2 + r) ^ 2 ^ i = r ^ 2 ^ (i + 1) - r ^ 2 ^ i := fun i => by
    rw [add_pow_char_pow, ← pow_mul, ← pow_succ', CharTwo.sub_eq_add]
  rw [hγ, absTrace, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_range_sub (fun i => r ^ 2 ^ i), pow_zero, pow_one]
  let := Fintype.ofFinite L
  have hc : Fintype.card L = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
  rw [← hc, FiniteField.pow_card, sub_self]

/-- `k` squarings with a running sum: `frobSum sq k t acc = acc + t + sq t + … + sq^(k-1) t`. It is
evaluated by the kernel on the word arithmetic; `map_frobSum` reads it as an `absTrace`. -/
def frobSum {α : Type} (add : α → α → α) (sq : α → α) : Nat → α → α → α
  | 0, _, acc => acc
  | k + 1, t, acc => frobSum add sq k (sq t) (add acc t)

theorem map_frobSum {α : Type} {R : Type*} [CommRing R] (f : α → R) (add : α → α → α)
    (sq : α → α) (hadd : ∀ a b, f (add a b) = f a + f b) (hsq : ∀ a, f (sq a) = f a ^ 2) (k : ℕ)
    (t acc : α) : f (frobSum add sq k t acc) = f acc + absTrace k (f t) := by
  induction k generalizing t acc with
  | zero => simp [frobSum, absTrace]
  | succ k ih =>
    rw [frobSum, ih, hadd, hsq, absTrace, absTrace, Finset.sum_range_succ', pow_zero, pow_one]
    simp only [← pow_mul, ← pow_succ']
    ring

/-! ## The specification `BF128 = BF64[y] / (y^2 + y + β)` -/

/-- `β = x^63 ∈ BF64`, the constant term of the modulus. -/
def betaBF : BF64 := B64.toBF64 B64.beta

/-- `β` is `x^63`. -/
theorem beta_eq_x_pow : B64.beta = B64.x ^ 63 := by
  rw [B64.x_pow_word ⟨63, by norm_num⟩]; rfl

/-- The parameters of `BF64[y] / (y^2 + y + β)`: lower coefficients `β, 1` of `y^0, y^1`. -/
def f128Params : ExtensionParams BF64 where
  d := 2
  two_le := le_rfl
  lower := #v[betaBF, 1]
  q := 2 ^ 64

/-- The parameters' modulus is `y^2 + y + β`. -/
theorem f128Params_poly : f128Params.poly = X ^ 2 + X + C betaBF := by
  have h0 : f128Params.lowerCoeff ⟨0, by decide⟩ = betaBF := rfl
  have h1 : f128Params.lowerCoeff ⟨1, by decide⟩ = 1 := rfl
  rw [ExtensionParams.poly]
  show X ^ 2 + (∑ i : Fin 2, C (f128Params.lowerCoeff i) * X ^ (i : ℕ)) = _
  rw [Fin.sum_univ_two, show f128Params.lowerCoeff (0 : Fin 2) = betaBF from h0,
    show f128Params.lowerCoeff (1 : Fin 2) = 1 from h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, map_one, one_mul]
  ring

/-- **`Tr β = 1`**, by kernel evaluation of 64 squarings of the word `β`. -/
theorem B64.frobSum_beta : frobSum B64.add B64.sq 64 B64.beta 0 = 1 := by decide +kernel

/-- **The absolute trace of `β` is `1`.** -/
theorem absTrace_beta : absTrace 64 betaBF = 1 := by
  have h := map_frobSum B64.toBF64 B64.add B64.sq B64.toBF64_add
    (fun a => (B64.toBF64_sq a).trans (_root_.sq _).symm) 64 B64.beta 0
  rw [B64.frobSum_beta, B64.toBF64_zero, zero_add, B64.toBF64_one] at h
  exact h.symm

/-- **`y^2 + y + β` is irreducible over `BF64`.** -/
theorem f128_irreducible : Irreducible f128Params.poly := by
  rw [f128Params_poly]
  exact quadratic_irreducible BF64.nat_card_bf64 (by rw [absTrace_beta]; exact one_ne_zero)

instance : Fact (Nat.card BF64 = f128Params.q) := ⟨BF64.nat_card_bf64⟩

instance : Fact (Irreducible f128Params.poly) := ⟨f128_irreducible⟩

/-- `GF(2^128) = BF64[y] / (y^2 + y + β)`, CompPoly's extension field (the specification). -/
abbrev BF128 : Type := Ext f128Params

instance : CharP BF128 2 := charP_of_injective_algebraMap' (R := BF64) (A := BF128) 2

/-- `BF128` has `2^128` elements. -/
theorem nat_card_BF128 : Nat.card BF128 = 2 ^ 128 := by
  rw [Ext.nat_card_ext]; rfl

/-- The adjoined root `y`. -/
def gen128 : BF128 := Ext.gen

/-- **The defining relation** `y^2 = y + β`. -/
theorem gen128_sq : gen128 ^ 2 = gen128 + algebraMap BF64 BF128 betaBF := by
  have h : aeval gen128 f128Params.poly = 0 := Ext.aeval_gen_poly
  rw [f128Params_poly] at h
  simp only [map_add, map_pow, aeval_X, aeval_C] at h
  linear_combination h + (-(gen128 + algebraMap BF64 BF128 betaBF)) *
    CharTwo.two_eq_zero (R := BF128)

/-! ## Quadratic-extension identities (proof helpers) -/

section Quadratic

variable {R : Type*} [CommRing R] {g γ : R}

/-- The product in a basis `1, g` with `g^2 = g + γ`, in characteristic two. -/
theorem quad_mul (hg : g ^ 2 = g + γ) (h2 : (2 : R) = 0) (a₀ a₁ b₀ b₁ : R) :
    (a₀ + a₁ * g) * (b₀ + b₁ * g) =
      (a₀ * b₀ + γ * (a₁ * b₁)) + ((a₀ + a₁) * (b₀ + b₁) + a₀ * b₀) * g := by
  linear_combination (a₁ * b₁) * hg - (a₀ * b₀ * g) * h2

/-- The square in a basis `1, g` with `g^2 = g + γ`, in characteristic two. -/
theorem quad_sq (hg : g ^ 2 = g + γ) (h2 : (2 : R) = 0) (a₀ a₁ : R) :
    (a₀ + a₁ * g) * (a₀ + a₁ * g) = (a₀ * a₀ + γ * (a₁ * a₁)) + (a₁ * a₁) * g := by
  linear_combination (a₁ * a₁) * hg + (a₀ * a₁ * g) * h2

/-- The norm: `(a₀ + a₁ g)((a₀ + a₁) + a₁ g) = a₀ (a₀ + a₁) + γ a₁^2`, in characteristic two. -/
theorem quad_norm (hg : g ^ 2 = g + γ) (h2 : (2 : R) = 0) (a₀ a₁ : R) :
    (a₀ + a₁ * g) * ((a₀ + a₁) + a₁ * g) = a₀ * (a₀ + a₁) + γ * (a₁ * a₁) := by
  linear_combination (a₁ * a₁) * hg + (a₀ * a₁ * g + a₁ * a₁ * g) * h2

end Quadratic

/-! ## The fast twin `F` -/

/-- An element `c₀ + c₁ y` of `GF(2^128) = GF(2^64)[y] / (y^2 + y + β)`, on two words. -/
structure F where
  /-- The constant coefficient. -/
  c₀ : B64
  /-- The coefficient of `y`. -/
  c₁ : B64
  deriving DecidableEq, Inhabited, Hashable

namespace F

instance : BEq F := ⟨fun a b => a.c₀ == b.c₀ && a.c₁ == b.c₁⟩

/-- `==` is equality (review S-A-m1). -/
instance : LawfulBEq F where
  eq_of_beq {a b} h := by
    cases a; cases b
    change (_ && _) = true at h
    rw [Bool.and_eq_true] at h
    exact congrArg₂ _ (eq_of_beq h.1) (eq_of_beq h.2)
  rfl {a} := by
    change (a.c₀ == a.c₀ && a.c₁ == a.c₁) = true
    rw [beq_self_eq_true, beq_self_eq_true]; rfl

instance : Repr F := ⟨fun a _ => repr (a.c₀, a.c₁)⟩

instance : Zero F := ⟨⟨0, 0⟩⟩
instance : One F := ⟨⟨1, 0⟩⟩

/-- The base field element `c` as `c + 0 y`. -/
@[inline] def ofB64 (c : B64) : F := ⟨c, 0⟩

/-- Coefficientwise addition; it is also subtraction, and negation is the identity. -/
@[inline] def add (a b : F) : F := ⟨a.c₀ + b.c₀, a.c₁ + b.c₁⟩

instance : Add F := ⟨add⟩
instance : Sub F := ⟨add⟩
instance : Neg F := ⟨fun a => a⟩

/-- Multiplication: three unreduced `clmul64` products (Karatsuba), then
`c₀ = a₀ b₀ + β a₁ b₁` and `c₁ = (a₀ + a₁)(b₀ + b₁) + a₀ b₀`, each reduced once; `β a₁ b₁` is the
reduced `a₁ b₁` times `x^63`, i.e. shifted into the two words. -/
def mul (a b : F) : F :=
  let p0 := B64.clmul64 a.c₀.val b.c₀.val
  let p1 := B64.clmul64 a.c₁.val b.c₁.val
  let pm := B64.clmul64 (a.c₀.val ^^^ a.c₁.val) (b.c₀.val ^^^ b.c₁.val)
  let r1 := B64.reduce p1.lo p1.hi
  ⟨⟨B64.reduce (p0.lo ^^^ (r1 <<< 63)) (p0.hi ^^^ (r1 >>> 1))⟩,
    ⟨B64.reduce (pm.lo ^^^ p0.lo) (pm.hi ^^^ p0.hi)⟩⟩

instance : Mul F := ⟨mul⟩

/-- Squaring: `(c₀ + c₁ y)^2 = (c₀^2 + β c₁^2) + c₁^2 y`. -/
def sq (a : F) : F :=
  let s1 := B64.sq a.c₁
  ⟨B64.sq a.c₀ + B64.mulBeta s1, s1⟩

/-- Multiplication by a base field element: two `B64` products. -/
@[inline] def smulBase (c : B64) (a : F) : F := ⟨c * a.c₀, c * a.c₁⟩

/-- The norm `c₀ (c₀ + c₁) + β c₁^2` of `c₀ + c₁ y` to `GF(2^64)`. -/
@[inline] def norm (a : F) : B64 := a.c₀ * (a.c₀ + a.c₁) + B64.mulBeta (B64.sq a.c₁)

/-- The inverse `((c₀ + c₁) + c₁ y) / norm`, with `0⁻¹ = 0`. -/
def inv (a : F) : F := smulBase (norm a)⁻¹ ⟨a.c₀ + a.c₁, a.c₁⟩

instance : Inv F := ⟨inv⟩

/-- Square-and-multiply: `powGo k b e acc = acc * b ^ e` whenever `e ≤ k`; the fuel `k` makes the
recursion structural (as `B64.powGo`). -/
def powGo : Nat → F → Nat → F → F
  | 0, _, _, acc => acc
  | k + 1, b, e, acc =>
    if e = 0 then acc else powGo k (sq b) (e / 2) (if e % 2 = 1 then acc * b else acc)

/-- Powers by repeated squaring. -/
instance : Pow F ℕ := ⟨fun a n => powGo n a n 1⟩

/-- The Frobenius power `a ^ (2 ^ k)`, by `k` squarings. -/
def frob : Nat → F → F
  | 0, a => a
  | k + 1, a => frob k (sq a)

/-- The generator `y` of `F` over `GF(2^64)`, a root of `y^2 + y + β`. -/
def y : F := ⟨0, 1⟩

/-- The sixteen bytes: `c₀`'s eight little-endian bytes, then `c₁`'s (BLUEPRINT §1). -/
def toBytes (a : F) : Vector UInt8 16 := a.c₀.toBytes ++ a.c₁.toBytes

/-- Decode two coefficients of eight bytes each; every byte string decodes. -/
def ofBytes (v : Vector UInt8 16) : F :=
  ⟨B64.ofBytes (Vector.ofFn fun i : Fin 8 => v[i.1]),
    B64.ofBytes (Vector.ofFn fun i : Fin 8 => v[8 + i.1])⟩

/-! ## The map to `BF128` -/

open B64

/-- The `BF128` element with the same coefficients. -/
def toExt (a : F) : BF128 := Ext.ofVector #v[toBF64 a.c₀, toBF64 a.c₁]

/-- The `F` element with the same coefficients. -/
def ofExt (z : BF128) : F :=
  ⟨ofBF64 (Ext.coeff z ⟨0, by decide⟩), ofBF64 (Ext.coeff z ⟨1, by decide⟩)⟩

@[simp] theorem ofExt_toExt (a : F) : ofExt (toExt a) = a := rfl

@[simp] theorem toExt_ofExt (z : BF128) : toExt (ofExt z) = z := by
  ext ⟨i, hi⟩
  change i < 2 at hi
  interval_cases i <;> rfl

/-- `F` and `BF128` are in bijection by their common coefficients. -/
def equivBF128 : F ≃ BF128 where
  toFun := toExt
  invFun := ofExt
  left_inv := ofExt_toExt
  right_inv := toExt_ofExt

theorem toExt_injective : Function.Injective toExt := equivBF128.injective

theorem toExt_inj {a b : F} : toExt a = toExt b ↔ a = b := toExt_injective.eq_iff

local notation "C" => algebraMap BF64 BF128
local notation "g" => gen128

/-- Every element is `c₀ + c₁ g`. -/
theorem toExt_eq (a : F) : toExt a = C (toBF64 a.c₀) + C (toBF64 a.c₁) * g := by
  apply Ext.toQuot_injective
  simp only [Ext.algebraMap_eq_ofBase, Ext.toQuot_add, Ext.toQuot_mul, Ext.toQuot_ofBase, gen128,
    Ext.toQuot_gen]
  rw [Ext.toQuot]
  change (∑ i : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  have h0 : Ext.coeff (toExt a) (0 : Fin 2) = toBF64 a.c₀ := rfl
  have h1 : Ext.coeff (toExt a) (1 : Fin 2) = toBF64 a.c₁ := rfl
  rw [h0, h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, mul_one, pow_one]

private theorem two_eq_zero : (2 : BF128) = 0 := CharTwo.two_eq_zero

private theorem gsq : g ^ 2 = g + C betaBF := gen128_sq

/-! ### The coefficients of the product (proof helpers) -/

/-- The reduced `a₁ b₁`. -/
private theorem Q_r1 (u v : UInt64) :
    Q (reduce (clmul64 u v).lo (clmul64 u v).hi) = Q u * Q v := by
  rw [mk_reduce, P_clmul64, map_mul]

/-- **The constant coefficient of the product** is `a₀ b₀ + β a₁ b₁`. -/
theorem mul_c₀ (a b : F) : (a * b).c₀ = a.c₀ * b.c₀ + beta * (a.c₁ * b.c₁) := by
  apply toBF64_injective
  apply BF64.toQuot_injective
  simp only [toBF64_add, toBF64_mul, BF64.toQuot_add, BF64.toQuot_mul, toQuot_toBF64]
  rw [Q_beta, ← Q_r1 a.c₁.val b.c₁.val]
  change Q (reduce _ _) = _
  set r1 := reduce (clmul64 a.c₁.val b.c₁.val).lo (clmul64 a.c₁.val b.c₁.val).hi
  have hs := P_shiftLeft r1 63 (by norm_num) (s := 63) (r := 1) (by simp) (by simp)
  have h0 := P_clmul64 a.c₀.val b.c₀.val
  rw [mk_reduce, Q, Q, Q, ← map_mul, ← map_mul, ← map_add]
  refine congrArg _ ?_
  simp only [P_xor]
  linear_combination h0 + hs

/-- **The coefficient of `y` in the product** is `(a₀ + a₁)(b₀ + b₁) + a₀ b₀`. -/
theorem mul_c₁ (a b : F) : (a * b).c₁ = (a.c₀ + a.c₁) * (b.c₀ + b.c₁) + a.c₀ * b.c₀ := by
  apply toBF64_injective
  apply BF64.toQuot_injective
  simp only [toBF64_add, toBF64_mul, BF64.toQuot_add, BF64.toQuot_mul, toQuot_toBF64]
  change Q (reduce _ _) = _
  have h0 := P_clmul64 a.c₀.val b.c₀.val
  have hm := P_clmul64 (a.c₀.val ^^^ a.c₁.val) (b.c₀.val ^^^ b.c₁.val)
  rw [P_xor, P_xor] at hm
  rw [mk_reduce, Q, Q, Q, Q, ← map_add, ← map_add, ← map_mul, ← map_mul, ← map_add]
  refine congrArg _ ?_
  simp only [P_xor]
  linear_combination hm + h0

/-! ## The operations are `BF128`'s -/

@[simp] theorem toExt_zero : toExt 0 = 0 := rfl

@[simp] theorem toExt_one : toExt 1 = 1 := rfl

/-- **Addition is `BF128`'s.** -/
@[simp] theorem toExt_add (a b : F) : toExt (a + b) = toExt a + toExt b := by
  rw [toExt_eq, toExt_eq a, toExt_eq b]
  change C (toBF64 (a.c₀ + b.c₀)) + C (toBF64 (a.c₁ + b.c₁)) * g = _
  simp only [toBF64_add, map_add]
  ring

@[simp] theorem toExt_neg (a : F) : toExt (-a) = -toExt a := by
  change toExt a = _
  rw [eq_neg_iff_add_eq_zero, ← toExt_add, ← toExt_zero]
  congr 1
  change (⟨a.c₀ + a.c₀, a.c₁ + a.c₁⟩ : F) = ⟨0, 0⟩
  simp only [CharTwo.add_self_eq_zero]

@[simp] theorem toExt_sub (a b : F) : toExt (a - b) = toExt a - toExt b := by
  change toExt (a + b) = _
  rw [toExt_add, sub_eq_add_neg, ← toExt_neg]
  rfl

/-- **Multiplication is `BF128`'s.** -/
@[simp] theorem toExt_mul (a b : F) : toExt (a * b) = toExt a * toExt b := by
  rw [toExt_eq, toExt_eq a, toExt_eq b, mul_c₀, mul_c₁, quad_mul gsq two_eq_zero]
  simp only [toBF64_add, toBF64_mul, map_add, map_mul, betaBF]

/-- **Squaring is `BF128`'s.** -/
@[simp] theorem toExt_sq (a : F) : toExt (sq a) = toExt a * toExt a := by
  rw [toExt_eq, toExt_eq a, quad_sq gsq two_eq_zero]
  change C (toBF64 (B64.sq a.c₀ + mulBeta (B64.sq a.c₁))) + C (toBF64 (B64.sq a.c₁)) * g = _
  simp only [toBF64_add, toBF64_sq, toBF64_mulBeta, map_add, map_mul, betaBF]

/-- Multiplication by a base field element is the `algebraMap` product. -/
@[simp] theorem toExt_smulBase (c : B64) (a : F) :
    toExt (smulBase c a) = C (toBF64 c) * toExt a := by
  simp only [toExt_eq, smulBase, toBF64_mul, map_mul]
  ring

/-- The base field embedding. -/
@[simp] theorem toExt_ofB64 (c : B64) : toExt (ofB64 c) = C (toBF64 c) := by
  simp [toExt_eq, ofB64]

/-! ### The inverse -/

/-- The conjugate `(c₀ + c₁) + c₁ y` times `a` is the norm. -/
private theorem mul_conj (a : F) :
    toExt a * toExt ⟨a.c₀ + a.c₁, a.c₁⟩ = C (toBF64 (norm a)) := by
  rw [toExt_eq, toExt_eq ⟨_, _⟩]
  simp only [toBF64_add, map_add]
  rw [quad_norm gsq two_eq_zero]
  simp only [norm, toBF64_add, toBF64_mul, toBF64_mulBeta, toBF64_sq, map_add, map_mul, betaBF]

/-- The norm of a nonzero element is nonzero. -/
private theorem norm_ne_zero {a : F} (ha : a ≠ 0) : toBF64 (norm a) ≠ 0 := by
  intro h
  rcases mul_eq_zero.mp ((mul_conj a).trans (by rw [h, map_zero])) with hc | hc
  · exact ha (toExt_injective (hc.trans toExt_zero.symm))
  · obtain ⟨h0, h1⟩ := F.mk.inj (toExt_injective (hc.trans toExt_zero.symm))
    rw [h1, add_zero] at h0
    exact ha (by cases a; cases h0; cases h1; rfl)

/-- **The inverse is `BF128`'s.** -/
@[simp] theorem toExt_inv (a : F) : toExt a⁻¹ = (toExt a)⁻¹ := by
  change toExt (smulBase (norm a)⁻¹ ⟨a.c₀ + a.c₁, a.c₁⟩) = _
  rw [toExt_smulBase, toBF64_inv]
  by_cases ha : a = 0
  · subst ha
    have : toBF64 (norm (0 : F)) = 0 := by decide +kernel
    rw [this, inv_zero, map_zero, zero_mul, toExt_zero, inv_zero]
  · refine eq_inv_of_mul_eq_one_right ?_
    rw [mul_left_comm, mul_conj, ← map_mul, inv_mul_cancel₀ (norm_ne_zero ha), map_one]

/-! ## The field structure, transported from `BF128` -/

instance : SMul ℕ F := ⟨nsmulRec⟩
instance : SMul ℤ F := ⟨zsmulRec nsmulRec⟩
instance : NatCast F := ⟨fun n => ofB64 (n : B64)⟩
instance : IntCast F := ⟨fun n => ofB64 (n : B64)⟩

@[simp] theorem toExt_natCast (n : ℕ) : toExt (n : F) = (n : BF128) := by
  change toExt (ofB64 (n : B64)) = _
  rw [toExt_ofB64, toBF64_natCast, map_natCast]

@[simp] theorem toExt_intCast (n : ℤ) : toExt (n : F) = (n : BF128) := by
  change toExt (ofB64 (n : B64)) = _
  rw [toExt_ofB64, toBF64_intCast, map_intCast]

theorem toExt_nsmul (n : ℕ) (a : F) : toExt (n • a) = n • toExt a := by
  change toExt (nsmulRec n a) = _
  induction n with
  | zero => simp [nsmulRec]
  | succ n ih => rw [nsmulRec, toExt_add, ih, succ_nsmul]

theorem toExt_zsmul (n : ℤ) (a : F) : toExt (n • a) = n • toExt a := by
  rcases n with n | n
  · exact (toExt_nsmul n a).trans (natCast_zsmul _ _).symm
  · change toExt (-(nsmulRec (n + 1) a)) = _
    rw [toExt_neg, negSucc_zsmul]
    exact congrArg _ (toExt_nsmul (n + 1) a)

theorem toExt_powGo (k : ℕ) (b : F) (e : ℕ) (acc : F) (he : e ≤ k) :
    toExt (powGo k b e acc) = toExt acc * toExt b ^ e := by
  induction k generalizing b e acc with
  | zero => obtain rfl : e = 0 := by omega
            simp [powGo]
  | succ k ih =>
    rw [powGo]
    split_ifs with h0 ho
    · simp [h0]
    · rw [ih _ _ _ (by omega)]; simp only [toExt_mul, toExt_sq]
      conv_rhs => rw [show e = 2 * (e / 2) + 1 by omega, pow_succ, pow_mul, _root_.sq]
      ring
    · rw [ih _ _ _ (by omega), toExt_sq]
      conv_rhs => rw [show e = 2 * (e / 2) by omega, pow_mul, _root_.sq]

theorem toExt_npow (a : F) (n : ℕ) : toExt (a ^ n) = toExt a ^ n := by
  change toExt (powGo n a n 1) = _
  rw [toExt_powGo n a n 1 le_rfl, toExt_one, one_mul]

/-- The ring structure, pulled back along the injective `toExt`. -/
instance instCommRing : CommRing F :=
  toExt_injective.commRing _ toExt_zero toExt_one toExt_add toExt_mul toExt_neg
    toExt_sub toExt_nsmul toExt_zsmul toExt_npow toExt_natCast toExt_intCast

instance : Div F := ⟨fun a b => a * b⁻¹⟩

private theorem mul_inv_cancel_ (a : F) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  apply toExt_injective
  rw [toExt_mul, toExt_inv, toExt_one]
  exact Ext.mul_inv_cancel' fun h' => h (toExt_injective (h'.trans toExt_zero.symm))

private theorem inv_zero_ : (0 : F)⁻¹ = 0 := by
  apply toExt_injective
  rw [toExt_inv, toExt_zero, inv_zero]

/-- **`F` is a field**, with the word-level operations. -/
instance instField : Field F where
  inv := inv
  div a b := a * b⁻¹
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := mul_inv_cancel_
  inv_zero := inv_zero_
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

/-- `toExt` as a ring isomorphism: **the twin is the specification field**. -/
def ringEquivBF128 : F ≃+* BF128 where
  toEquiv := equivBF128
  map_mul' := toExt_mul
  map_add' := toExt_add

@[simp] theorem ringEquivBF128_apply (a : F) : ringEquivBF128 a = toExt a := rfl

@[simp] theorem toExt_div (a b : F) : toExt (a / b) = toExt a / toExt b := by
  change toExt (a * b⁻¹) = _
  rw [toExt_mul, toExt_inv, div_eq_mul_inv]

/-- `ofB64` is the embedding of `B64` into `F`, `algebraMap` on the `CompPoly` side. -/
def ofB64RingHom : B64 →+* F where
  toFun := ofB64
  map_one' := rfl
  map_mul' a b := toExt_injective (by simp only [toExt_ofB64, toExt_mul, toBF64_mul, map_mul])
  map_zero' := rfl
  map_add' a b := toExt_injective (by simp only [toExt_ofB64, toExt_add, toBF64_add, map_add])

/-- `F` is a `B64`-algebra by `ofB64`. -/
instance instAlgebra : Algebra B64 F := ofB64RingHom.toAlgebra

theorem algebraMap_eq_ofB64 (c : B64) : algebraMap B64 F c = ofB64 c := rfl

theorem smulBase_eq_mul (c : B64) (a : F) : smulBase c a = ofB64 c * a :=
  toExt_injective (by rw [toExt_smulBase, toExt_mul, toExt_ofB64])

instance : CharP F 2 where
  cast_eq_zero_iff n := by
    rw [← toExt_inj, toExt_natCast, toExt_zero]
    exact CharP.cast_eq_zero_iff BF128 2 n

/-! ## Cardinality, Frobenius powers -/

instance : Finite F := Finite.of_equiv BF128 equivBF128.symm

/-- `F` has `2 ^ 128` elements. -/
theorem nat_card_F : Nat.card F = 2 ^ 128 := by
  rw [Nat.card_congr equivBF128, nat_card_BF128]

/-- An enumeration of `F`, for statements that need one; noncomputable on purpose, as for
`B64`. -/
noncomputable instance : Fintype F := Fintype.ofFinite F

/-- Every enumeration of `F` has `2 ^ 128` elements. -/
theorem card_F [Fintype F] : Fintype.card F = 2 ^ 128 := by
  rw [← Nat.card_eq_fintype_card, nat_card_F]

theorem sq_eq_mul (a : F) : sq a = a * a := toExt_injective (by rw [toExt_sq, toExt_mul])

/-- `frob k` is the `2 ^ k`-th power. -/
theorem frob_eq_pow (k : ℕ) (a : F) : frob k a = a ^ (2 ^ k) := by
  induction k generalizing a with
  | zero => simp [frob]
  | succ k ih => rw [frob, ih, sq_eq_mul, ← _root_.sq, ← pow_mul, pow_succ, mul_comm]

/-- `y` is the adjoined root: it maps to `gen128`. -/
theorem toExt_y : toExt y = gen128 := by simp [toExt_eq, y]

/-- `y^2 = y + β` in the twin. -/
theorem y_sq : y * y = y + ofB64 beta :=
  toExt_injective (by rw [toExt_mul, toExt_add, toExt_y, toExt_ofB64, ← _root_.sq, gsq]; rfl)

/-! ## Bytes -/

/-- The first half of a concatenation (here and in `K`). -/
theorem slice0 {n : ℕ} (u v : Vector UInt8 n) : (Vector.ofFn fun i : Fin n => (u ++ v)[i.1]) = u :=
  Vector.ext fun _ _ => by simp

/-- The second half of a concatenation (here and in `K`). -/
theorem slice1 {n : ℕ} (u v : Vector UInt8 n) :
    (Vector.ofFn fun i : Fin n => (u ++ v)[n + i.1]) = v :=
  Vector.ext fun _ _ => by simp [Vector.getElem_append_right]

/-- Decoding inverts encoding. -/
@[simp] theorem ofBytes_toBytes (a : F) : ofBytes (toBytes a) = a := by
  simp only [ofBytes, toBytes, slice0, slice1, B64.ofBytes_toBytes]

/-- Encoding inverts decoding: every 16-byte string is an encoding. -/
@[simp] theorem toBytes_ofBytes (v : Vector UInt8 16) : toBytes (ofBytes v) = v := by
  apply Vector.ext
  intro i hi
  simp only [toBytes, ofBytes, B64.toBytes_ofBytes]
  by_cases h8 : i < 8
  · rw [Vector.getElem_append_left h8, Vector.getElem_ofFn]
  · rw [Vector.getElem_append_right (by omega) (by omega), Vector.getElem_ofFn]
    congr 1; dsimp only; omega

/-- The bytes as an equivalence: each `F` value has exactly one 16-byte encoding. -/
def bytesEquiv : F ≃ Vector UInt8 16 where
  toFun := toBytes
  invFun := ofBytes
  left_inv := ofBytes_toBytes
  right_inv := toBytes_ofBytes

end F

end FR
