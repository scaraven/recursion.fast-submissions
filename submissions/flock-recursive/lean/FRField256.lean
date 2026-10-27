-- New for `flock-recursive` (BLUEPRINT B-4, §2.1); the same pattern as `FRField128` one level up.
import FRField128

/-!
# `GF(2^256)` as a quadratic extension of `GF(2^128)`

The specification is CompPoly's extension framework over `BF128`:

* `BF256 := Ext f256Params`, the quotient `BF128[u] / (u^2 + u + α)` with `α = β y`
  (`F.alpha`, `alphaE`), irreducible by the trace criterion (`quadratic_irreducible`): the absolute
  trace of `α` over `GF(2)` is `1` (`absTrace_alpha`), evaluated by the kernel on the word
  arithmetic (`F.frobSum_alpha`, 128 squarings in `F`).

The fast twin `K` stores the two coefficients of `f₀ + f₁ u` as elements of `F` (the coordinate
split `K = F ⊕ F·u`, `K.eq_split`):

* addition is coefficientwise;
* multiplication is Karatsuba over `F.mul`: `f₀ = a₀ b₀ + α a₁ b₁`, `f₁ = (a₀ + a₁)(b₀ + b₁) +
  a₀ b₀`, three `F` products; `α z = β^2 z₁ + β (z₀ + z₁) y` is three shifts by `63`
  (`F.mulAlpha`);
* squaring is `(f₀^2 + α f₁^2) + f₁^2 u`;
* inversion is by the norm `f₀ (f₀ + f₁) + α f₁^2` to `F`, one `F` inversion;
* bytes are `f₀`'s sixteen bytes, then `f₁`'s (BLUEPRINT §1).

`K.toExt : K → BF256` commutes with every operation, is a ring isomorphism (`ringEquivBF256`),
and `K` is a field through it (`K.instField`), with `2^256` elements (`card_K`).
-/

namespace FR

open Polynomial CompPoly.Extension

/-! ## `α` in `F` -/

namespace F

/-- `α = β y`, the constant term of the modulus of `K` over `F`. -/
def alpha : F := ⟨0, B64.beta⟩

/-- Multiplication by `α = β y`: `α (z₀ + z₁ y) = β^2 z₁ + β (z₀ + z₁) y`, since `y^2 = y + β`. -/
@[inline] def mulAlpha (z : F) : F := ⟨B64.mulBeta (B64.mulBeta z.c₁), B64.mulBeta (z.c₀ + z.c₁)⟩

open B64 in
/-- **`mulAlpha` is the product by `α`.** -/
@[simp] theorem toExt_mulAlpha (z : F) : toExt (mulAlpha z) = toExt alpha * toExt z := by
  rw [toExt_eq, toExt_eq alpha, toExt_eq z, quad_mul gen128_sq CharTwo.two_eq_zero]
  change algebraMap BF64 BF128 (toBF64 (mulBeta (mulBeta z.c₁))) +
    algebraMap BF64 BF128 (toBF64 (mulBeta (z.c₀ + z.c₁))) * gen128 =
    (algebraMap BF64 BF128 (toBF64 0) * _ + _) + ((algebraMap BF64 BF128 (toBF64 0) + _) * _ +
      algebraMap BF64 BF128 (toBF64 0) * _) * gen128
  simp only [alpha, toBF64_mulBeta, toBF64_add, toBF64_zero, map_add, map_mul, map_zero, betaBF]
  ring

theorem mulAlpha_eq (z : F) : mulAlpha z = alpha * z :=
  toExt_injective (by rw [toExt_mulAlpha, toExt_mul])

/-- **`Tr α = 1`**, by kernel evaluation of 128 squarings of `α` in `F`. -/
theorem frobSum_alpha : frobSum F.add F.sq 128 alpha 0 = 1 := by decide +kernel

end F

/-! ## The specification `BF256 = BF128[u] / (u^2 + u + α)` -/

/-- `α = β y ∈ BF128`. -/
def alphaE : BF128 := F.toExt F.alpha

/-- The parameters of `BF128[u] / (u^2 + u + α)`: lower coefficients `α, 1` of `u^0, u^1`. -/
def f256Params : ExtensionParams BF128 where
  d := 2
  two_le := le_rfl
  lower := #v[alphaE, 1]
  q := 2 ^ 128

/-- The parameters' modulus is `u^2 + u + α`. -/
theorem f256Params_poly : f256Params.poly = X ^ 2 + X + C alphaE := by
  have h0 : f256Params.lowerCoeff ⟨0, by decide⟩ = alphaE := rfl
  have h1 : f256Params.lowerCoeff ⟨1, by decide⟩ = 1 := rfl
  rw [ExtensionParams.poly]
  show X ^ 2 + (∑ i : Fin 2, C (f256Params.lowerCoeff i) * X ^ (i : ℕ)) = _
  rw [Fin.sum_univ_two, show f256Params.lowerCoeff (0 : Fin 2) = alphaE from h0,
    show f256Params.lowerCoeff (1 : Fin 2) = 1 from h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, map_one, one_mul]
  ring

/-- **The absolute trace of `α` is `1`.** -/
theorem absTrace_alpha : absTrace 128 alphaE = 1 := by
  have h := map_frobSum F.toExt F.add F.sq F.toExt_add
    (fun a => (F.toExt_sq a).trans (_root_.sq _).symm) 128 F.alpha 0
  rw [F.frobSum_alpha, F.toExt_zero, zero_add, F.toExt_one] at h
  exact h.symm

/-- **`u^2 + u + α` is irreducible over `BF128`.** -/
theorem f256_irreducible : Irreducible f256Params.poly := by
  rw [f256Params_poly]
  exact quadratic_irreducible nat_card_BF128 (by rw [absTrace_alpha]; exact one_ne_zero)

instance : Fact (Nat.card BF128 = f256Params.q) := ⟨nat_card_BF128⟩

instance : Fact (Irreducible f256Params.poly) := ⟨f256_irreducible⟩

/-- `GF(2^256) = BF128[u] / (u^2 + u + α)`, CompPoly's extension field (the specification). -/
abbrev BF256 : Type := Ext f256Params

instance : CharP BF256 2 := charP_of_injective_algebraMap' (R := BF128) (A := BF256) 2

/-- `BF256` has `2^256` elements. -/
theorem nat_card_BF256 : Nat.card BF256 = 2 ^ 256 := by
  rw [Ext.nat_card_ext]; rfl

/-- The adjoined root `u`. -/
def gen256 : BF256 := Ext.gen

/-- **The defining relation** `u^2 = u + α`. -/
theorem gen256_sq : gen256 ^ 2 = gen256 + algebraMap BF128 BF256 alphaE := by
  have h : aeval gen256 f256Params.poly = 0 := Ext.aeval_gen_poly
  rw [f256Params_poly] at h
  simp only [map_add, map_pow, aeval_X, aeval_C] at h
  linear_combination h + (-(gen256 + algebraMap BF128 BF256 alphaE)) *
    CharTwo.two_eq_zero (R := BF256)

/-! ## The fast twin `K` -/

/-- An element `f₀ + f₁ u` of `GF(2^256) = GF(2^128)[u] / (u^2 + u + α)`. -/
structure K where
  /-- The constant coefficient. -/
  f₀ : F
  /-- The coefficient of `u`. -/
  f₁ : F
  deriving DecidableEq, Inhabited, Hashable

namespace K

instance : BEq K := ⟨fun a b => a.f₀ == b.f₀ && a.f₁ == b.f₁⟩

/-- `==` is equality (review S-A-m1). -/
instance : LawfulBEq K where
  eq_of_beq {a b} h := by
    cases a; cases b
    change (_ && _) = true at h
    rw [Bool.and_eq_true] at h
    exact congrArg₂ _ (eq_of_beq h.1) (eq_of_beq h.2)
  rfl {a} := by
    change (a.f₀ == a.f₀ && a.f₁ == a.f₁) = true
    rw [beq_self_eq_true, beq_self_eq_true]; rfl

instance : Repr K := ⟨fun a _ => repr (a.f₀, a.f₁)⟩

instance : Zero K := ⟨⟨0, 0⟩⟩
instance : One K := ⟨⟨1, 0⟩⟩

/-- The element `c + 0 u` of `K` for `c ∈ F`. -/
@[inline] def ofF (c : F) : K := ⟨c, 0⟩

/-- Coefficientwise addition; it is also subtraction, and negation is the identity. -/
@[inline] def add (a b : K) : K := ⟨a.f₀ + b.f₀, a.f₁ + b.f₁⟩

instance : Add K := ⟨add⟩
instance : Sub K := ⟨add⟩
instance : Neg K := ⟨fun a => a⟩

/-- Multiplication: Karatsuba over the coefficients (three `F` products), then `u^2 = u + α`:
`f₀ = a₀ b₀ + α a₁ b₁`, `f₁ = (a₀ + a₁)(b₀ + b₁) + a₀ b₀`. -/
def mul (a b : K) : K :=
  let m0 := a.f₀ * b.f₀
  let m1 := a.f₁ * b.f₁
  let mm := (a.f₀ + a.f₁) * (b.f₀ + b.f₁)
  ⟨m0 + F.mulAlpha m1, mm + m0⟩

instance : Mul K := ⟨mul⟩

/-- Squaring: `(f₀ + f₁ u)^2 = (f₀^2 + α f₁^2) + f₁^2 u`. -/
def sq (a : K) : K :=
  let s1 := F.sq a.f₁
  ⟨F.sq a.f₀ + F.mulAlpha s1, s1⟩

/-- Multiplication by an element of `F`: two `F` products. -/
@[inline] def smulF (c : F) (a : K) : K := ⟨c * a.f₀, c * a.f₁⟩

/-- The norm `f₀ (f₀ + f₁) + α f₁^2` of `f₀ + f₁ u` to `F`. -/
@[inline] def norm (a : K) : F := a.f₀ * (a.f₀ + a.f₁) + F.mulAlpha (F.sq a.f₁)

/-- The inverse `((f₀ + f₁) + f₁ u) / norm`, with `0⁻¹ = 0`. -/
def inv (a : K) : K := smulF (norm a)⁻¹ ⟨a.f₀ + a.f₁, a.f₁⟩

instance : Inv K := ⟨inv⟩

/-- Square-and-multiply: `powGo k b e acc = acc * b ^ e` whenever `e ≤ k` (as `F.powGo`). -/
def powGo : Nat → K → Nat → K → K
  | 0, _, _, acc => acc
  | k + 1, b, e, acc =>
    if e = 0 then acc else powGo k (sq b) (e / 2) (if e % 2 = 1 then acc * b else acc)

/-- Powers by repeated squaring. -/
instance : Pow K ℕ := ⟨fun a n => powGo n a n 1⟩

/-- The Frobenius power `a ^ (2 ^ k)`, by `k` squarings. -/
def frob : Nat → K → K
  | 0, a => a
  | k + 1, a => frob k (sq a)

/-- The generator `u` of `K` over `F`, a root of `u^2 + u + α`. -/
def u : K := ⟨0, 1⟩

/-- The thirty-two bytes: `f₀`'s sixteen bytes, then `f₁`'s (BLUEPRINT §1). -/
def toBytes (a : K) : Vector UInt8 32 := a.f₀.toBytes ++ a.f₁.toBytes

/-- Decode two coefficients of sixteen bytes each; every byte string decodes. -/
def ofBytes (v : Vector UInt8 32) : K :=
  ⟨F.ofBytes (Vector.ofFn fun i : Fin 16 => v[i.1]),
    F.ofBytes (Vector.ofFn fun i : Fin 16 => v[16 + i.1])⟩

/-! ## The map to `BF256` -/

/-- The `BF256` element with the same coefficients. -/
def toExt (a : K) : BF256 := Ext.ofVector #v[F.toExt a.f₀, F.toExt a.f₁]

/-- The `K` element with the same coefficients. -/
def ofExt (z : BF256) : K :=
  ⟨F.ofExt (Ext.coeff z ⟨0, by decide⟩), F.ofExt (Ext.coeff z ⟨1, by decide⟩)⟩

@[simp] theorem ofExt_toExt (a : K) : ofExt (toExt a) = a := rfl

@[simp] theorem toExt_ofExt (z : BF256) : toExt (ofExt z) = z := by
  refine Ext.ext fun ⟨i, hi⟩ => ?_
  change i < 2 at hi
  interval_cases i <;> exact F.toExt_ofExt _

/-- `K` and `BF256` are in bijection by their common coefficients. -/
def equivBF256 : K ≃ BF256 where
  toFun := toExt
  invFun := ofExt
  left_inv := ofExt_toExt
  right_inv := toExt_ofExt

theorem toExt_injective : Function.Injective toExt := equivBF256.injective

theorem toExt_inj {a b : K} : toExt a = toExt b ↔ a = b := toExt_injective.eq_iff

local notation "C" => algebraMap BF128 BF256
local notation "g" => gen256

/-- Every element is `f₀ + f₁ g`. -/
theorem toExt_eq (a : K) : toExt a = C (F.toExt a.f₀) + C (F.toExt a.f₁) * g := by
  apply Ext.toQuot_injective
  simp only [Ext.algebraMap_eq_ofBase, Ext.toQuot_add, Ext.toQuot_mul, Ext.toQuot_ofBase, gen256,
    Ext.toQuot_gen]
  rw [Ext.toQuot]
  change (∑ i : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  have h0 : Ext.coeff (toExt a) (0 : Fin 2) = F.toExt a.f₀ := rfl
  have h1 : Ext.coeff (toExt a) (1 : Fin 2) = F.toExt a.f₁ := rfl
  rw [h0, h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, mul_one, pow_one]

private theorem two_eq_zero : (2 : BF256) = 0 := CharTwo.two_eq_zero

private theorem gsq : g ^ 2 = g + C alphaE := gen256_sq

/-! ## The operations are `BF256`'s -/

@[simp] theorem toExt_zero : toExt 0 = 0 := rfl

@[simp] theorem toExt_one : toExt 1 = 1 := rfl

/-- **Addition is `BF256`'s.** -/
@[simp] theorem toExt_add (a b : K) : toExt (a + b) = toExt a + toExt b := by
  rw [toExt_eq, toExt_eq a, toExt_eq b]
  change C (F.toExt (a.f₀ + b.f₀)) + C (F.toExt (a.f₁ + b.f₁)) * g = _
  simp only [F.toExt_add, map_add]
  ring

@[simp] theorem toExt_neg (a : K) : toExt (-a) = -toExt a := by
  change toExt a = _
  rw [eq_neg_iff_add_eq_zero, ← toExt_add, ← toExt_zero]
  congr 1
  change (⟨a.f₀ + a.f₀, a.f₁ + a.f₁⟩ : K) = ⟨0, 0⟩
  simp only [CharTwo.add_self_eq_zero]

@[simp] theorem toExt_sub (a b : K) : toExt (a - b) = toExt a - toExt b := by
  change toExt (a + b) = _
  rw [toExt_add, sub_eq_add_neg, ← toExt_neg]
  rfl

/-- **Multiplication is `BF256`'s.** -/
@[simp] theorem toExt_mul (a b : K) : toExt (a * b) = toExt a * toExt b := by
  rw [toExt_eq, toExt_eq a, toExt_eq b, quad_mul gsq two_eq_zero]
  change C (F.toExt (a.f₀ * b.f₀ + F.mulAlpha (a.f₁ * b.f₁))) +
    C (F.toExt ((a.f₀ + a.f₁) * (b.f₀ + b.f₁) + a.f₀ * b.f₀)) * g = _
  simp only [F.toExt_add, F.toExt_mul, F.toExt_mulAlpha, map_add, map_mul, alphaE]

/-- **Squaring is `BF256`'s.** -/
@[simp] theorem toExt_sq (a : K) : toExt (sq a) = toExt a * toExt a := by
  rw [toExt_eq, toExt_eq a, quad_sq gsq two_eq_zero]
  change C (F.toExt (F.sq a.f₀ + F.mulAlpha (F.sq a.f₁))) + C (F.toExt (F.sq a.f₁)) * g = _
  simp only [F.toExt_add, F.toExt_sq, F.toExt_mulAlpha, map_add, map_mul, alphaE]

/-- Multiplication by an element of `F` is the `algebraMap` product. -/
@[simp] theorem toExt_smulF (c : F) (a : K) : toExt (smulF c a) = C (F.toExt c) * toExt a := by
  simp only [toExt_eq, smulF, F.toExt_mul, map_mul]
  ring

/-- The embedding of `F`. -/
@[simp] theorem toExt_ofF (c : F) : toExt (ofF c) = C (F.toExt c) := by simp [toExt_eq, ofF]

/-! ### The inverse -/

/-- The conjugate `(f₀ + f₁) + f₁ u` times `a` is the norm. -/
private theorem mul_conj (a : K) :
    toExt a * toExt ⟨a.f₀ + a.f₁, a.f₁⟩ = C (F.toExt (norm a)) := by
  rw [toExt_eq, toExt_eq ⟨_, _⟩]
  simp only [F.toExt_add, map_add]
  rw [quad_norm gsq two_eq_zero]
  simp only [norm, F.toExt_add, F.toExt_mul, F.toExt_mulAlpha, F.toExt_sq, map_add, map_mul,
    alphaE]

/-- The norm of a nonzero element is nonzero. -/
private theorem norm_ne_zero {a : K} (ha : a ≠ 0) : F.toExt (norm a) ≠ 0 := by
  intro h
  rcases mul_eq_zero.mp ((mul_conj a).trans (by rw [h, map_zero])) with hc | hc
  · exact ha (toExt_injective (hc.trans toExt_zero.symm))
  · obtain ⟨h0, h1⟩ := K.mk.inj (toExt_injective (hc.trans toExt_zero.symm))
    rw [h1, add_zero] at h0
    exact ha (by cases a; cases h0; cases h1; rfl)

/-- **The inverse is `BF256`'s.** -/
@[simp] theorem toExt_inv (a : K) : toExt a⁻¹ = (toExt a)⁻¹ := by
  change toExt (smulF (norm a)⁻¹ ⟨a.f₀ + a.f₁, a.f₁⟩) = _
  rw [toExt_smulF, F.toExt_inv]
  by_cases ha : a = 0
  · subst ha
    have : F.toExt (norm (0 : K)) = 0 := by rw [show norm 0 = 0 by decide +kernel]; rfl
    rw [this, inv_zero, map_zero, zero_mul, toExt_zero, inv_zero]
  · refine eq_inv_of_mul_eq_one_right ?_
    rw [mul_left_comm, mul_conj, ← map_mul, inv_mul_cancel₀ (norm_ne_zero ha), map_one]

/-! ## The field structure, transported from `BF256` -/

instance : SMul ℕ K := ⟨nsmulRec⟩
instance : SMul ℤ K := ⟨zsmulRec nsmulRec⟩
instance : NatCast K := ⟨fun n => ofF (n : F)⟩
instance : IntCast K := ⟨fun n => ofF (n : F)⟩

@[simp] theorem toExt_natCast (n : ℕ) : toExt (n : K) = (n : BF256) := by
  change toExt (ofF (n : F)) = _
  rw [toExt_ofF, F.toExt_natCast, map_natCast]

@[simp] theorem toExt_intCast (n : ℤ) : toExt (n : K) = (n : BF256) := by
  change toExt (ofF (n : F)) = _
  rw [toExt_ofF, F.toExt_intCast, map_intCast]

theorem toExt_nsmul (n : ℕ) (a : K) : toExt (n • a) = n • toExt a := by
  change toExt (nsmulRec n a) = _
  induction n with
  | zero => simp [nsmulRec]
  | succ n ih => rw [nsmulRec, toExt_add, ih, succ_nsmul]

theorem toExt_zsmul (n : ℤ) (a : K) : toExt (n • a) = n • toExt a := by
  rcases n with n | n
  · exact (toExt_nsmul n a).trans (natCast_zsmul _ _).symm
  · change toExt (-(nsmulRec (n + 1) a)) = _
    rw [toExt_neg, negSucc_zsmul]
    exact congrArg _ (toExt_nsmul (n + 1) a)

theorem toExt_powGo (k : ℕ) (b : K) (e : ℕ) (acc : K) (he : e ≤ k) :
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

theorem toExt_npow (a : K) (n : ℕ) : toExt (a ^ n) = toExt a ^ n := by
  change toExt (powGo n a n 1) = _
  rw [toExt_powGo n a n 1 le_rfl, toExt_one, one_mul]

/-- The ring structure, pulled back along the injective `toExt`. -/
instance instCommRing : CommRing K :=
  toExt_injective.commRing _ toExt_zero toExt_one toExt_add toExt_mul toExt_neg
    toExt_sub toExt_nsmul toExt_zsmul toExt_npow toExt_natCast toExt_intCast

instance : Div K := ⟨fun a b => a * b⁻¹⟩

private theorem mul_inv_cancel_ (a : K) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  apply toExt_injective
  rw [toExt_mul, toExt_inv, toExt_one]
  exact Ext.mul_inv_cancel' fun h' => h (toExt_injective (h'.trans toExt_zero.symm))

private theorem inv_zero_ : (0 : K)⁻¹ = 0 := by
  apply toExt_injective
  rw [toExt_inv, toExt_zero, inv_zero]

/-- **`K` is a field**, with the word-level operations. -/
instance instField : Field K where
  inv := inv
  div a b := a * b⁻¹
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := mul_inv_cancel_
  inv_zero := inv_zero_
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

/-- `toExt` as a ring isomorphism: **the twin is the specification field**. -/
def ringEquivBF256 : K ≃+* BF256 where
  toEquiv := equivBF256
  map_mul' := toExt_mul
  map_add' := toExt_add

@[simp] theorem ringEquivBF256_apply (a : K) : ringEquivBF256 a = toExt a := rfl

@[simp] theorem toExt_div (a b : K) : toExt (a / b) = toExt a / toExt b := by
  change toExt (a * b⁻¹) = _
  rw [toExt_mul, toExt_inv, div_eq_mul_inv]

/-- `ofF` is the embedding of `F` into `K`, `algebraMap` on the `CompPoly` side. -/
def ofFRingHom : F →+* K where
  toFun := ofF
  map_one' := rfl
  map_mul' a b := toExt_injective (by simp only [toExt_ofF, toExt_mul, F.toExt_mul, map_mul])
  map_zero' := rfl
  map_add' a b := toExt_injective (by simp only [toExt_ofF, toExt_add, F.toExt_add, map_add])

/-- `K` is an `F`-algebra by `ofF`. -/
instance instAlgebra : Algebra F K := ofFRingHom.toAlgebra

theorem algebraMap_eq_ofF (c : F) : algebraMap F K c = ofF c := rfl

theorem smulF_eq_mul (c : F) (a : K) : smulF c a = ofF c * a :=
  toExt_injective (by rw [toExt_smulF, toExt_mul, toExt_ofF])

instance : CharP K 2 where
  cast_eq_zero_iff n := by
    rw [← toExt_inj, toExt_natCast, toExt_zero]
    exact CharP.cast_eq_zero_iff BF256 2 n

/-! ## Cardinality, Frobenius powers, the coordinate split -/

instance : Finite K := Finite.of_equiv BF256 equivBF256.symm

/-- `K` has `2 ^ 256` elements. -/
theorem nat_card_K : Nat.card K = 2 ^ 256 := by
  rw [Nat.card_congr equivBF256, nat_card_BF256]

/-- An enumeration of `K`, for statements that need one; noncomputable on purpose. -/
noncomputable instance : Fintype K := Fintype.ofFinite K

/-- Every enumeration of `K` has `2 ^ 256` elements. -/
theorem card_K [Fintype K] : Fintype.card K = 2 ^ 256 := by
  rw [← Nat.card_eq_fintype_card, nat_card_K]

theorem sq_eq_mul (a : K) : sq a = a * a := toExt_injective (by rw [toExt_sq, toExt_mul])

/-- `frob k` is the `2 ^ k`-th power. -/
theorem frob_eq_pow (k : ℕ) (a : K) : frob k a = a ^ (2 ^ k) := by
  induction k generalizing a with
  | zero => simp [frob]
  | succ k ih => rw [frob, ih, sq_eq_mul, ← _root_.sq, ← pow_mul, pow_succ, mul_comm]

/-- `u` is the adjoined root: it maps to `gen256`. -/
theorem toExt_u : toExt u = gen256 := by simp [toExt_eq, u]

/-- `u^2 = u + α` in the twin. -/
theorem u_sq : u * u = u + ofF F.alpha :=
  toExt_injective (by rw [toExt_mul, toExt_add, toExt_u, toExt_ofF, ← _root_.sq, gsq]; rfl)

/-- **The coordinate split** `K = F ⊕ F·u`: every element is `f₀ + f₁ u`. -/
theorem eq_split (a : K) : a = ofF a.f₀ + ofF a.f₁ * u :=
  toExt_injective (by rw [toExt_add, toExt_mul, toExt_ofF, toExt_ofF, toExt_u, toExt_eq])

/-! ## Bytes -/

/-- Decoding inverts encoding. -/
@[simp] theorem ofBytes_toBytes (a : K) : ofBytes (toBytes a) = a := by
  simp only [ofBytes, toBytes, F.slice0, F.slice1, F.ofBytes_toBytes]

/-- Encoding inverts decoding: every 32-byte string is an encoding. -/
@[simp] theorem toBytes_ofBytes (v : Vector UInt8 32) : toBytes (ofBytes v) = v := by
  apply Vector.ext
  intro i hi
  simp only [toBytes, ofBytes, F.toBytes_ofBytes]
  by_cases h16 : i < 16
  · rw [Vector.getElem_append_left h16, Vector.getElem_ofFn]
  · rw [Vector.getElem_append_right (by omega) (by omega), Vector.getElem_ofFn]
    congr 1; dsimp only; omega

/-- The bytes as an equivalence: each `K` value has exactly one 32-byte encoding. -/
def bytesEquiv : K ≃ Vector UInt8 32 where
  toFun := toBytes
  invFun := ofBytes
  left_inv := ofBytes_toBytes
  right_inv := toBytes_ofBytes

end K

end FR
