-- New for lvm2 S2GT (GT-W, STMT 6 `PhiQGC_eq`): `E3 ⊗_K E2` as a value ring of the compiled evaluator
-- (`K.KRing`), `E2` inside it, and the leaf map back to `E2`.
import LvmE2VPhiT
import LvmFieldKCorrect
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# `E3 ⊗ E2` and the leaf map

`FEA = E3[X]/(X² + xX + 1)`, written `u + v·X` with `u, v ∈ E3 = FE` (`x ∈ K`). It is a commutative ring of
characteristic two (`CommRing.ofMinimalAxioms`), `E3` maps in by `ofE w = w` (`K.KRing`), and `E2 = K[X]/(X² + xX + 1)`
maps in by `emb (a₀ + a₁X) = a₀ + a₁X` (`emb`, a ring map).

**The leaf map** `lam L : FEA → FE2` (for `L = (ρ₁, ρ₂)`): `lam (u + vX) = λ(u) + X·λ(v)` with
`λ(c₀ + c₁y + c₂y²) = c₀ + c₁ρ₁ + c₂ρ₂`. It is additive and `E2`-linear: `lam (emb a * z) = a * lam z`
(`lam_emb_mul`). It is not multiplicative; the fast evaluator multiplies under it only when one factor is in `E2`
(`linOk`).
-/

set_option autoImplicit false

namespace Lvm.Typed.KT

open Lvm Lvm.Typed.K

/-- `E3 ⊗_K E2 = E3[X]/(X² + xX + 1)`: `u + v·X`. -/
@[ext] structure FEA where
  /-- The constant coordinate. -/
  u : FE
  /-- The `X` coordinate. -/
  v : FE
  deriving DecidableEq, Inhabited

namespace FEA

/-- `x ∈ K ⊂ E3` (`X² = 1 + xX`). -/
def xE : FE := FE.ofK FK.x

instance : Zero FEA := ⟨⟨0, 0⟩⟩
instance : One FEA := ⟨⟨1, 0⟩⟩
instance : Add FEA := ⟨fun a b ↦ ⟨a.u + b.u, a.v + b.v⟩⟩
instance : Neg FEA := ⟨fun a ↦ ⟨-a.u, -a.v⟩⟩
instance : Mul FEA := ⟨fun a b ↦ ⟨a.u * b.u + a.v * b.v, a.u * b.v + a.v * b.u + xE * (a.v * b.v)⟩⟩

@[simp] theorem zero_u : (0 : FEA).u = 0 := rfl
@[simp] theorem zero_v : (0 : FEA).v = 0 := rfl
@[simp] theorem one_u : (1 : FEA).u = 1 := rfl
@[simp] theorem one_v : (1 : FEA).v = 0 := rfl
@[simp] theorem add_u (a b : FEA) : (a + b).u = a.u + b.u := rfl
@[simp] theorem add_v (a b : FEA) : (a + b).v = a.v + b.v := rfl
@[simp] theorem neg_u (a : FEA) : (-a).u = -a.u := rfl
@[simp] theorem neg_v (a : FEA) : (-a).v = -a.v := rfl
@[simp] theorem mul_u (a b : FEA) : (a * b).u = a.u * b.u + a.v * b.v := rfl
@[simp] theorem mul_v (a b : FEA) : (a * b).v = a.u * b.v + a.v * b.u + xE * (a.v * b.v) := rfl

/-- **`FEA` is a commutative ring** (`X² = 1 + xX` over `E3`: the product's identities are `E3`'s). -/
instance instCommRing : CommRing FEA :=
  CommRing.ofMinimalAxioms
    (fun a b c ↦ by ext <;> simp only [add_u, add_v] <;> ring)
    (fun a ↦ by ext <;> simp only [add_u, add_v, zero_u, zero_v] <;> ring)
    (fun a ↦ by ext <;> simp only [add_u, add_v, neg_u, neg_v, zero_u, zero_v] <;> ring)
    (fun a b c ↦ by ext <;> simp only [mul_u, mul_v] <;> ring)
    (fun a b ↦ by ext <;> simp only [mul_u, mul_v] <;> ring)
    (fun a ↦ by ext <;> simp only [mul_u, mul_v, one_u, one_v] <;> ring)
    (fun a b c ↦ by ext <;> simp only [mul_u, mul_v, add_u, add_v] <;> ring)

/-- `E3 → FEA`, `w ↦ w + 0·X`. -/
def ofERing : FE →+* FEA where
  toFun w := ⟨w, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp only [mul_u, mul_v] <;> ring
  map_zero' := by ext <;> rfl
  map_add' a b := by ext <;> simp only [add_u, add_v] <;> ring

instance : KRing FEA := ⟨ofERing⟩

@[simp] theorem ofE_u (w : FE) : (KRing.ofE w : FEA).u = w := by
  show (ofERing w).u = w; rfl
@[simp] theorem ofE_v (w : FE) : (KRing.ofE w : FEA).v = 0 := by
  show (ofERing w).v = 0; rfl

instance : Nontrivial FEA := ⟨⟨0, 1, fun h ↦ zero_ne_one (congrArg FEA.u h)⟩⟩

instance : CharP FEA 2 :=
  charP_of_injective_ringHom (f := ofERing) (fun a b h ↦ by
    have := congrArg FEA.u h
    exact this) 2

end FEA

/-! ## `E2` inside `FEA` -/

instance kt_charP_FE2 : CharP FE2 2 := charP_of_injective_algebraMap (algebraMap FK FE2).injective 2

/-- `FE.ofK` as a ring map (`FE.ofKRingHom`). -/
theorem kt_ofK_mul (a b : FK) : FE.ofK (a * b) = FE.ofK a * FE.ofK b := map_mul FE.ofKRingHom a b
theorem kt_ofK_add (a b : FK) : FE.ofK (a + b) = FE.ofK a + FE.ofK b := map_add FE.ofKRingHom a b

/-- **`E2 → FEA`**: `a₀ + a₁X ↦ a₀ + a₁X` (`K ⊂ E3`). -/
def emb : FE2 →+* FEA where
  toFun a := ⟨FE.ofK a.re, FE.ofK a.im⟩
  map_one' := rfl
  map_mul' a b := by
    rw [FE2.mul_def]
    ext <;> simp only [FEA.mul_u, FEA.mul_v, kt_ofK_mul, kt_ofK_add, FEA.xE]
  map_zero' := by ext <;> rfl
  map_add' a b := by
    ext
    · exact kt_ofK_add a.re b.re
    · exact kt_ofK_add a.im b.im

@[simp] theorem emb_u (a : FE2) : (emb a).u = FE.ofK a.re := by
  show (FEA.mk (FE.ofK a.re) (FE.ofK a.im)).u = _; rfl
@[simp] theorem emb_v (a : FE2) : (emb a).v = FE.ofK a.im := by
  show (FEA.mk (FE.ofK a.re) (FE.ofK a.im)).v = _; rfl

/-! ## The leaf map -/

/-- `λ(c₀ + c₁y + c₂y²) = c₀ + c₁ρ₁ + c₂ρ₂`, `K`-linear `E3 → E2`. -/
def lamE (L : Lam) (c : FE) : FE2 := FE2.ofK c.c₀ + FE2.ofK c.c₁ * L.r1 + FE2.ofK c.c₂ * L.r2

/-- **The leaf map** `FEA → E2`: `u + vX ↦ λ(u) + X·λ(v)`. -/
def lam (L : Lam) (z : FEA) : FE2 := lamE L z.u + ⟨0, 1⟩ * lamE L z.v

theorem kt_ofK2_add (a b : FK) : FE2.ofK (a + b) = FE2.ofK a + FE2.ofK b := map_add FE2.ofKRingHom a b
theorem kt_ofK2_mul (a b : FK) : FE2.ofK (a * b) = FE2.ofK a * FE2.ofK b := map_mul FE2.ofKRingHom a b

theorem lamE_add (L : Lam) (a b : FE) : lamE L (a + b) = lamE L a + lamE L b := by
  simp only [lamE, tw_fe_add_def, kt_ofK2_add]; ring

theorem lamE_zero (L : Lam) : lamE L 0 = 0 := by
  simp only [lamE, show (0 : FE) = ⟨0, 0, 0⟩ from rfl, show FE2.ofK 0 = 0 from rfl]; ring

theorem lamE_ofK_mul (L : Lam) (k : FK) (c : FE) : lamE L (FE.ofK k * c) = FE2.ofK k * lamE L c := by
  rw [← FE.smulBase_eq_mul]
  simp only [lamE, FE.smulBase, kt_ofK2_mul]; ring

theorem lam_add (L : Lam) (a b : FEA) : lam L (a + b) = lam L a + lam L b := by
  simp only [lam, FEA.add_u, FEA.add_v, lamE_add]; ring

theorem lam_zero (L : Lam) : lam L 0 = 0 := by
  simp only [lam, FEA.zero_u, FEA.zero_v, lamE_zero, mul_zero, add_zero]

/-- `X·X = 1 + x·X` in `E2`. -/
theorem kt_XX : (⟨0, 1⟩ : FE2) * ⟨0, 1⟩ = 1 + FE2.ofK FK.x * ⟨0, 1⟩ := by
  rw [FE2.mul_def, FE2.mul_def]
  show (⟨_, _⟩ : FE2) = ⟨1 + (FK.x * 0 + 0 * 0), 0 + (FK.x * 1 + 0 * 0 + FK.x * (0 * 1))⟩
  congr 1 <;> ring

/-- `a = a₀ + a₁X`. -/
theorem kt_split2 (a : FE2) : a = FE2.ofK a.re + FE2.ofK a.im * ⟨0, 1⟩ := by
  obtain ⟨a0, a1⟩ := a
  rw [FE2.mul_def]
  show (⟨a0, a1⟩ : FE2) = ⟨a0 + (a1 * 0 + 0 * 1), 0 + (a1 * 1 + 0 * 0 + FK.x * (0 * 1))⟩
  congr 1 <;> ring

theorem lam_emb (L : Lam) (a : FE2) : lam L (emb a) = a := by
  simp only [lam, emb_u, emb_v, lamE, FE.ofK, show FE2.ofK 0 = 0 from rfl]
  conv_rhs => rw [kt_split2 a]
  ring

/-- **The leaf map is `E2`-linear.** -/
theorem lam_emb_mul (L : Lam) (a : FE2) (z : FEA) : lam L (emb a * z) = a * lam L z := by
  obtain ⟨u, v⟩ := z
  simp only [lam, FEA.mul_u, FEA.mul_v, emb_u, emb_v, lamE_add, FEA.xE, ← mul_assoc, ← kt_ofK_mul,
    lamE_ofK_mul, kt_ofK2_mul]
  conv_rhs => rw [kt_split2 a]
  have h2 : (2 : FE2) = 0 := CharTwo.two_eq_zero
  linear_combination (FE2.ofK a.im * lamE L v) * kt_XX +
    (FE2.ofK a.im * lamE L v * (1 + ⟨0, 1⟩ * FE2.ofK FK.x - ⟨0, 1⟩ ^ 2)) * h2

theorem lam_ofE (L : Lam) (w : FE) : lam L (KRing.ofE w) = lamE L w := by
  simp only [lam, FEA.ofE_u, FEA.ofE_v, lamE_zero, mul_zero, add_zero]

/-! ## `E2`'s word product (`m2`) is `FE2`'s -/

section M2

open Polynomial BinaryField

/-- Words' classes are additive. -/
theorem kt_Q_xor (x y : UInt64) : FK.Q (x ^^^ y) = FK.Q x + FK.Q y := by
  simp only [FK.Q, FK.P_xor, map_add]

/-- Two `K` elements are equal when their classes are. -/
theorem kt_FK_eq {a b : FK} (h : FK.Q a.val = FK.Q b.val) : a = b := by
  apply FK.toBF64_injective
  apply BF64.toQuot_injective
  rwa [FK.toQuot_toBF64, FK.toQuot_toBF64]

/-- A word's top bit as a word. -/
theorem kt_shr63 (v : UInt64) : v >>> 63 = 0 ∨ v >>> 63 = 1 := by
  have h : (v >>> 63).toNat < 2 := by
    rw [UInt64.toNat_shiftRight]
    have := v.toNat_lt
    norm_num [Nat.shiftRight_eq_div_pow]
    omega
  have h' : (v >>> 63).toNat = 0 ∨ (v >>> 63).toNat = 1 := by omega
  rcases h' with h' | h'
  · exact Or.inl (UInt64.toNat_inj.1 (by simpa using h'))
  · exact Or.inr (UInt64.toNat_inj.1 (by simpa using h'))

/-- The high word of a carry-less product has its top bit clear (the product has degree `≤ 126`). -/
theorem kt_clmul_hi (a b : UInt64) : (FK.clmul64 a b).hi >>> 63 = 0 := by
  have h := FK.P_clmul64 a b
  have hc := congrArg (fun p : (ZMod 2)[X] ↦ p.coeff 127) h
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', FK.P, toPoly_coeff] at hc
  have hab : (toPoly a.toBitVec * toPoly b.toBitVec).coeff 127 = 0 := by
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    simp only [toPoly_coeff]
    split_ifs <;> first | (exfalso; omega) | simp
  rw [hab] at hc
  simp only [show ¬ (127 < 64) by norm_num, dite_false, zero_add, show 64 ≤ 127 by norm_num, ite_true,
    show 127 - 64 = 63 by norm_num, show (63 < 64) by norm_num, dite_true] at hc
  have hbit : (FK.clmul64 a b).hi.toBitVec.getLsbD 63 = false := by
    by_contra hb
    simp only [Bool.not_eq_false] at hb
    simp [BitVec.getLsb_eq_getElem, ← BitVec.getLsbD_eq_getElem, hb] at hc
  rcases kt_shr63 (FK.clmul64 a b).hi with h | h
  · exact h
  · exfalso
    have h2 := congrArg (fun x : UInt64 ↦ x.toBitVec.getLsbD 0) h
    simp only [UInt64.toBitVec_shiftRight, BitVec.getLsbD_ushiftRight] at h2
    simp_all

/-- `x·(lo + x^64 hi)` as the shifted pair, when `hi`'s top bit is clear. -/
theorem kt_or_xor (lo hi : UInt64) : (hi <<< 1) ||| (lo >>> 63) = (hi <<< 1) ^^^ (lo >>> 63) := by
  apply UInt64.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_xor, BitVec.getLsbD_or, BitVec.getLsbD_xor,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  · have : ¬ (63 + i < 64) := by omega
    simp_all

/-- `x·(lo + x^64 hi)` as the shifted pair, when `hi`'s top bit is clear. -/
theorem kt_shift128 (lo hi : UInt64) (h : hi >>> 63 = 0) :
    FK.P (lo <<< 1) + X ^ 64 * FK.P ((hi <<< 1) ||| (lo >>> 63)) = X * (FK.P lo + X ^ 64 * FK.P hi) := by
  have e1 := FK.P_shiftLeft lo 1 (by norm_num) (s := 1) (r := 63) (by simp) (by simp)
  have e2 := FK.P_shiftLeft hi 1 (by norm_num) (s := 1) (r := 63) (by simp) (by simp)
  have hP0 : FK.P 0 = 0 := toPoly_zero_eq_zero
  rw [kt_or_xor, FK.P_xor, e1, e2, h, hP0]
  ring

/-- `x`'s word is the polynomial `X`. -/
theorem kt_P_x : FK.P FK.x.val = X := by
  have h : FK.x.val.toBitVec = (((1 <<< 1 : ℕ)) : BitVec 64) := by decide
  rw [FK.P, h, toPoly_one_shiftLeft (w := 64) 1 (by norm_num), pow_one]

/-- The word of `x^4 + x^3 + x + 1` (`0x1B`). -/
theorem kt_P_1B : FK.P 0x1B = X ^ 4 + X ^ 3 + X + 1 := by
  have h : (0x1B : UInt64).toBitVec = (((1 <<< 4 : ℕ)) : BitVec 64) ^^^ (((1 <<< 3 : ℕ)) : BitVec 64) ^^^
      (((1 <<< 1 : ℕ)) : BitVec 64) ^^^ (((1 <<< 0 : ℕ)) : BitVec 64) := by
    decide
  rw [FK.P, h, toPoly_xor, toPoly_xor, toPoly_xor, toPoly_one_shiftLeft (w := 64) 4 (by norm_num),
    toPoly_one_shiftLeft (w := 64) 3 (by norm_num), toPoly_one_shiftLeft (w := 64) 1 (by norm_num),
    toPoly_one_shiftLeft (w := 64) 0 (by norm_num), pow_one, pow_zero]

/-- **`mulXw` is `x·`** in `K`. -/
theorem mulXw_eq (v : UInt64) : FK.Q (mulXw v) = FK.Q FK.x.val * FK.Q v := by
  have e1 := FK.P_shiftLeft v 1 (by norm_num) (s := 1) (r := 63) (by simp) (by simp)
  have hb : v >>> 63 = 0 ∨ v >>> 63 = 1 := kt_shr63 v
  have hP0 : FK.P 0 = 0 := toPoly_zero_eq_zero
  have hP1 : FK.P 1 = 1 := toPoly_one_eq_one (by norm_num)
  simp only [FK.Q, mulXw, FK.P_xor, e1, kt_P_x, ← map_mul]
  rcases hb with hb | hb
  · rw [hb, show (0 : UInt64) * 27 = 0 by simp, hP0]
    exact congrArg (AdjoinRoot.mk BF64.basePoly) (by ring)
  · rw [hb, show (1 : UInt64) * 27 = 27 by simp, hP1, kt_P_1B, AdjoinRoot.mk_eq_mk, BF64.basePoly_eq]
    refine ⟨-1, ?_⟩
    linear_combination (X ^ 4 + X ^ 3 + X + 1 : (ZMod 2)[X]) * ZMod2Poly.two_eq_zero

/-- **`mX` is `X·`** in `E2`. -/
theorem mX_eq (a : FE2) : mX a = ⟨0, 1⟩ * a := by
  rw [FE2.mul_def]
  show (⟨a.im, ⟨a.re.val ^^^ mulXw a.im.val⟩⟩ : FE2) = ⟨0 * a.re + 1 * a.im, 0 * a.im + 1 * a.re + FK.x * (1 * a.im)⟩
  congr 1
  · ring
  · apply kt_FK_eq
    rw [show (0 * a.im + 1 * a.re + FK.x * (1 * a.im)) = a.re + FK.x * a.im by ring]
    show FK.Q (a.re.val ^^^ mulXw a.im.val) = FK.Q (a.re + FK.x * a.im).val
    rw [kt_Q_xor, mulXw_eq, show (a.re + FK.x * a.im).val = a.re.val ^^^ (FK.x * a.im).val from rfl, kt_Q_xor,
      FK.Q_mul]

theorem m2_re_def (a b : FE2) : (m2 a b).re.val = FK.reduce
    ((FK.clmul64 a.re.val b.re.val).lo ^^^ (FK.clmul64 a.im.val b.im.val).lo)
    ((FK.clmul64 a.re.val b.re.val).hi ^^^ (FK.clmul64 a.im.val b.im.val).hi) := rfl

theorem m2_im_def (a b : FE2) : (m2 a b).im.val = FK.reduce
    ((FK.clmul64 (a.re.val ^^^ a.im.val) (b.re.val ^^^ b.im.val)).lo ^^^
      ((FK.clmul64 a.re.val b.re.val).lo ^^^ (FK.clmul64 a.im.val b.im.val).lo) ^^^
      ((FK.clmul64 a.im.val b.im.val).lo <<< 1))
    ((FK.clmul64 (a.re.val ^^^ a.im.val) (b.re.val ^^^ b.im.val)).hi ^^^
      ((FK.clmul64 a.re.val b.re.val).hi ^^^ (FK.clmul64 a.im.val b.im.val).hi) ^^^
      (((FK.clmul64 a.im.val b.im.val).hi <<< 1) ||| ((FK.clmul64 a.im.val b.im.val).lo >>> 63))) := rfl

/-- `m2`'s constant coordinate is `E2`'s. -/
theorem m2_re (a b : FE2) : (m2 a b).re = a.re * b.re + a.im * b.im := by
  have h0 := FK.P_clmul64 a.re.val b.re.val
  have h1 := FK.P_clmul64 a.im.val b.im.val
  apply kt_FK_eq
  rw [show (a.re * b.re + a.im * b.im).val = (a.re * b.re).val ^^^ (a.im * b.im).val from rfl, kt_Q_xor, FK.Q_mul,
    FK.Q_mul]
  rw [m2_re_def, FK.mk_reduce]
  simp only [FK.Q, ← map_mul, ← map_add, FK.P_xor]
  refine congrArg (AdjoinRoot.mk BF64.basePoly) ?_
  rw [← h0, ← h1, mul_add, add_add_add_comm]

/-- `m2`'s `X` coordinate is `E2`'s. -/
theorem m2_im (a b : FE2) : (m2 a b).im = a.re * b.im + a.im * b.re + FK.x * (a.im * b.im) := by
  have h0 := FK.P_clmul64 a.re.val b.re.val
  have h1 := FK.P_clmul64 a.im.val b.im.val
  have hm := FK.P_clmul64 (a.re.val ^^^ a.im.val) (b.re.val ^^^ b.im.val)
  rw [FK.P_xor, FK.P_xor] at hm
  have hs := kt_shift128 (FK.clmul64 a.im.val b.im.val).lo (FK.clmul64 a.im.val b.im.val).hi
    (kt_clmul_hi a.im.val b.im.val)
  apply kt_FK_eq
  rw [show (a.re * b.im + a.im * b.re + FK.x * (a.im * b.im)).val =
      (a.re * b.im).val ^^^ (a.im * b.re).val ^^^ (FK.x * (a.im * b.im)).val from rfl, kt_Q_xor, kt_Q_xor,
    FK.Q_mul, FK.Q_mul, FK.Q_mul, FK.Q_mul]
  rw [m2_im_def, FK.mk_reduce]
  simp only [FK.Q, ← map_mul, ← map_add, FK.P_xor, kt_P_x]
  refine congrArg (AdjoinRoot.mk BF64.basePoly) ?_
  -- regroup into the four products' sides and rewrite them (one `linear_combination` over everything: 2.7 M hb)
  have key : ∀ u0 u1 u2 u3 w0 w1 w2 w3 : (ZMod 2)[X], u0 + (u1 + u2) + u3 + X ^ 64 * (w0 + (w1 + w2) + w3) =
      (u0 + X ^ 64 * w0) + (u1 + X ^ 64 * w1) + (u2 + X ^ 64 * w2) + (u3 + X ^ 64 * w3) := by
    intro u0 u1 u2 u3 w0 w1 w2 w3; ring
  rw [key, hm, h0, h1, hs, h1]
  linear_combination (FK.P a.re.val * FK.P b.re.val + FK.P a.im.val * FK.P b.im.val) * ZMod2Poly.two_eq_zero

/-- **`m2` is `E2`'s product.** -/
theorem m2_eq (a b : FE2) : m2 a b = a * b := by
  rw [FE2.mul_def, ← m2_re, ← m2_im]

end M2

end Lvm.Typed.KT
