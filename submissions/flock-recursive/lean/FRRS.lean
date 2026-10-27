-- New for `flock-recursive` (BLUEPRINT §2.1, Appendix A.1; BP-C-M4). The novel-basis part follows
-- `submissions/spartan-srom/lean/SpartanSromRS.lean` (this repository, `v4/flock-recursive` at
-- `783328c`: `bitProd`, `bit_induction`, `basis_deg`, `exists_encPoly`), with LCH14's normalised
-- subspace polynomials instead of spartan-srom's unnormalised recursion.
import FRField256
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# The Reed–Solomon code of the Ligerito levels (BLUEPRINT §2.1)

**Generic part** (any field `K`, any `n` evaluation points `x : Fin n → K`):

* `rsCode x k`, the Reed–Solomon code: the words `j ↦ p(x j)` of the polynomials `p` of degree
  `< k`, a `K`-subspace of `K^n`;
* `agreeSet u w`, the positions where two words agree; `agreeSet₂` for pairs of words;
* `rs_eq_of_agree` (two codewords agreeing on `k` points are equal), `rs_interp` (any data on at
  most `k` points is matched by a codeword: Lagrange interpolation), `rs_minDist` (distance
  `n − k + 1`).
-/

namespace FR

open Polynomial Finset

section Agree

variable {K : Type*} [DecidableEq K] {n : ℕ}

/-- The positions where the words `u` and `w` agree. -/
def agreeSet (u w : Fin n → K) : Finset (Fin n) := univ.filter fun j => u j = w j

/-- The positions where `u₀ = v₀` and `u₁ = v₁` (the joint agreement of two pairs of words). -/
def agreeSet₂ (u₀ u₁ v₀ v₁ : Fin n → K) : Finset (Fin n) :=
  univ.filter fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j

@[simp] theorem mem_agreeSet {u w : Fin n → K} {j : Fin n} : j ∈ agreeSet u w ↔ u j = w j := by
  simp [agreeSet]

@[simp] theorem mem_agreeSet₂ {u₀ u₁ v₀ v₁ : Fin n → K} {j : Fin n} :
    j ∈ agreeSet₂ u₀ u₁ v₀ v₁ ↔ u₀ j = v₀ j ∧ u₁ j = v₁ j := by
  simp [agreeSet₂]

end Agree

section Generic

variable {K : Type*} [Field K] {n : ℕ}

/-- The word of the evaluations of `p` at the points `x`. -/
def evalWord (x : Fin n → K) (p : K[X]) : Fin n → K := fun j => p.eval (x j)

/-- `evalWord x` as a `K`-linear map. -/
noncomputable def evalWordL (x : Fin n → K) : K[X] →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun j => Polynomial.leval (x j)

theorem evalWordL_apply (x : Fin n → K) (p : K[X]) : evalWordL x p = evalWord x p := rfl

/-- **The Reed–Solomon code** `RS[K, x, k]`: evaluations at `x` of the polynomials of degree
`< k`. -/
noncomputable def rsCode (x : Fin n → K) (k : ℕ) : Submodule K (Fin n → K) :=
  (degreeLT K k).map (evalWordL x)

theorem mem_rsCode {x : Fin n → K} {k : ℕ} {w : Fin n → K} :
    w ∈ rsCode x k ↔ ∃ p : K[X], p.degree < k ∧ evalWord x p = w := by
  simp [rsCode, mem_degreeLT, evalWordL_apply]

theorem evalWord_mem_rsCode {x : Fin n → K} {k : ℕ} {p : K[X]} (hp : p.degree < k) :
    evalWord x p ∈ rsCode x k := mem_rsCode.2 ⟨p, hp, rfl⟩

variable [DecidableEq K]

/-- Two polynomials of degree `< k` agreeing at `k` distinct points `x j`, `j ∈ S`, are equal. -/
theorem poly_eq_of_agree {x : Fin n → K} (hx : Function.Injective x) {k : ℕ} {p q : K[X]}
    (hp : p.degree < k) (hq : q.degree < k) (S : Finset (Fin n)) (hS : k ≤ S.card)
    (h : ∀ j ∈ S, p.eval (x j) = q.eval (x j)) : p = q := by
  have hS' : (k : WithBot ℕ) ≤ (S.image x).card := by
    rw [card_image_of_injective _ hx]; exact_mod_cast hS
  exact eq_of_degrees_lt_of_eval_finset_eq _ (hp.trans_le hS') (hq.trans_le hS')
    (forall_mem_image.2 h)

/-- **`rs_eq_of_agree`**: two codewords of `RS[K, x, k]` that agree on `k` positions are equal. -/
theorem rs_eq_of_agree {x : Fin n → K} (hx : Function.Injective x) {k : ℕ} {v w : Fin n → K}
    (hv : v ∈ rsCode x k) (hw : w ∈ rsCode x k) (S : Finset (Fin n)) (hS : k ≤ S.card)
    (h : ∀ j ∈ S, v j = w j) : v = w := by
  obtain ⟨p, hp, rfl⟩ := mem_rsCode.1 hv
  obtain ⟨q, hq, rfl⟩ := mem_rsCode.1 hw
  rw [poly_eq_of_agree hx hp hq S hS h]

omit [DecidableEq K] in
/-- **`rs_interp`** (`interp_agree`): data on at most `k` positions `S` is matched by a codeword,
the Lagrange interpolant through `(x j, u j)`, `j ∈ S`. -/
theorem rs_interp {x : Fin n → K} (hx : Function.Injective x) {k : ℕ} (S : Finset (Fin n))
    (hS : S.card ≤ k) (u : Fin n → K) : ∃ v ∈ rsCode x k, ∀ j ∈ S, v j = u j := by
  refine ⟨evalWord x (Lagrange.interpolate S x u), evalWord_mem_rsCode ?_, fun j hj => ?_⟩
  · exact (Lagrange.degree_interpolate_lt u hx.injOn).trans_le (by exact_mod_cast hS)
  · exact Lagrange.eval_interpolate_at_node u hx.injOn hj

/-- **`rs_minDist`**: distinct codewords of `RS[K, x, k]` differ in at least `n − k + 1`
positions. -/
theorem rs_minDist {x : Fin n → K} (hx : Function.Injective x) {k : ℕ} {v w : Fin n → K}
    (hv : v ∈ rsCode x k) (hw : w ∈ rsCode x k) (hne : v ≠ w) : n + 1 ≤ k + hammingDist v w := by
  by_contra hlt
  apply hne
  refine rs_eq_of_agree hx hv hw (agreeSet v w) ?_ (fun j hj => mem_agreeSet.1 hj)
  have : (agreeSet v w).card + hammingDist v w = n := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) fun j => v j = w j
    rwa [card_univ, Fintype.card_fin] at h
  omega

end Generic

/-! ## Bit products, `eq` on the bits, the tensor identity -/

section Bits

variable {R : Type*} [CommMonoid R]

/-- `∏_{i<ℓ} (f_i if bit i of j else g_i)`. -/
def bitSel (f g : ℕ → R) (ℓ j : ℕ) : R := ∏ i ∈ range ℓ, if j.testBit i then f i else g i

/-- `∏_{i<ℓ} f_i^{bit_i j}` (spartan-srom's `bitProd`). -/
def bitProd (f : ℕ → R) (ℓ j : ℕ) : R := bitSel f 1 ℓ j

theorem bitSel_succ_lo (f g : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitSel f g (ℓ + 1) j = bitSel f g ℓ j * g ℓ := by
  simp [bitSel, prod_range_succ, Nat.testBit_lt_two_pow hj]

theorem bitSel_succ_hi (f g : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitSel f g (ℓ + 1) (2 ^ ℓ + j) = bitSel f g ℓ j * f ℓ := by
  simp only [bitSel, prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj,
    Bool.not_false, ite_true]
  congr 1
  exact prod_congr rfl fun i hi => by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hi)]

theorem bitProd_succ_lo (f : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitProd f (ℓ + 1) j = bitProd f ℓ j := by
  simp [bitProd, bitSel_succ_lo _ _ hj]

theorem bitProd_succ_hi (f : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitProd f (ℓ + 1) (2 ^ ℓ + j) = bitProd f ℓ j * f ℓ := bitSel_succ_hi _ _ hj

/-- Induction on `ℓ` for statements about `j < 2^ℓ`, splitting off the top bit (spartan-srom). -/
theorem bit_induction {P : ℕ → ℕ → Prop} (h0 : P 0 0)
    (hlo : ∀ ℓ j, j < 2 ^ ℓ → P ℓ j → P (ℓ + 1) j)
    (hhi : ∀ ℓ j, j < 2 ^ ℓ → P ℓ j → P (ℓ + 1) (2 ^ ℓ + j)) : ∀ ℓ j, j < 2 ^ ℓ → P ℓ j := by
  intro ℓ
  induction ℓ with
  | zero => intro j hj; rwa [Nat.lt_one_iff.1 hj]
  | succ ℓ ih =>
    intro j hj
    by_cases hlt : j < 2 ^ ℓ
    · exact hlo ℓ j hlt (ih j hlt)
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlt)
      have : j' < 2 ^ ℓ := by rw [pow_succ] at hj; omega
      exact hhi ℓ j' this (ih j' this)

/-- `bitProd f ℓ j` does not depend on `ℓ` once `j < 2^ℓ`. -/
theorem bitProd_congr (f : ℕ → R) {ℓ ℓ' j : ℕ} (hj : j < 2 ^ ℓ) (hj' : j < 2 ^ ℓ') :
    bitProd f ℓ j = bitProd f ℓ' j := by
  have key : ∀ a b, j < 2 ^ a → a ≤ b → bitProd f b j = bitProd f a j := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => rfl
    | succ b hab ih =>
      rw [bitProd_succ_lo _ (ha.trans_le (Nat.pow_le_pow_right (by norm_num) hab)), ih]
  rcases le_total ℓ ℓ' with h | h
  · exact (key _ _ hj h).symm
  · exact key _ _ hj' h

end Bits

section Tensor

variable {R : Type*} [CommRing R]

/-- `eq(r, x)` on the bits of `x`, bit `v` of `x` against `r_v` (little-endian):
`∏_{v<ℓ} (r_v if bit v of x else 1 − r_v)`. -/
def eqBits (r : ℕ → R) (ℓ x : ℕ) : R := bitSel r (fun v => 1 - r v) ℓ x

/-- **The tensor identity** (BLUEPRINT §2.1, BP-C-M4), over any commutative ring:
`Σ_{x<2^ℓ} eq(r, x) ∏_{v ∈ bits x} w_v = ∏_{v<ℓ} (1 − r_v + r_v w_v)`. -/
theorem tensor_identity (r w : ℕ → R) (ℓ : ℕ) :
    ∑ x ∈ range (2 ^ ℓ), eqBits r ℓ x * bitProd w ℓ x = ∏ v ∈ range ℓ, (1 - r v + r v * w v) := by
  induction ℓ with
  | zero => simp [eqBits, bitSel, bitProd]
  | succ ℓ ih =>
    rw [pow_succ, mul_two, sum_range_add, prod_range_succ, ← ih, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun x hx => ?_
    have hx' := mem_range.1 hx
    simp only [eqBits, bitSel_succ_lo _ _ hx', bitSel_succ_hi _ _ hx', bitProd_succ_lo _ hx',
      bitProd_succ_hi _ hx']
    ring

end Tensor

/-! ## The novel basis (LCH14; BLUEPRINT §2.1, Appendix A.1) -/

section NovelBasis

variable {L : Type*} [Field L]

/-- The subspace vanishing polynomial `W_v(X) = ∏_{a < 2^v} (X − pt a)`. -/
noncomputable def subW (pt : ℕ → L) (v : ℕ) : L[X] := ∏ a ∈ range (2 ^ v), (X - C (pt a))

/-- The normalised `Ŵ_v = W_v / W_v(pt (2^v))`. -/
noncomputable def normW (pt : ℕ → L) (v : ℕ) : L[X] :=
  C ((subW pt v).eval (pt (2 ^ v)))⁻¹ * subW pt v

/-- The novel basis polynomial `X_x = ∏_{v ∈ bits x} Ŵ_v`. -/
noncomputable def novelX (pt : ℕ → L) (x : ℕ) : L[X] := bitProd (normW pt) x x

theorem eval_subW (pt : ℕ → L) (v : ℕ) (y : L) :
    (subW pt v).eval y = ∏ a ∈ range (2 ^ v), (y - pt a) := by
  simp [subW, eval_prod]

theorem subW_monic (pt : ℕ → L) (v : ℕ) : (subW pt v).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C (pt a)

theorem natDegree_subW (pt : ℕ → L) (v : ℕ) : (subW pt v).natDegree = 2 ^ v := by
  rw [subW, natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C (pt a)]
  simp

variable {pt : ℕ → L} {N : ℕ}

/-- `W_v(pt (2^v)) ≠ 0` for `v < N` when `pt` is injective on `[0, 2^N)`. -/
theorem subW_eval_ne (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {v : ℕ} (hv : v < N) :
    (subW pt v).eval (pt (2 ^ v)) ≠ 0 := by
  have hvN : 2 ^ v < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) hv
  rw [eval_subW, prod_ne_zero_iff]
  intro a ha h
  have := hpt (Set.mem_Iio.2 hvN) (Set.mem_Iio.2 ((mem_range.1 ha).trans hvN)) (sub_eq_zero.1 h)
  exact absurd (mem_range.1 ha) (by omega)

theorem normW_eval_self (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {v : ℕ} (hv : v < N) :
    (normW pt v).eval (pt (2 ^ v)) = 1 := by
  rw [normW, eval_mul, eval_C, inv_mul_cancel₀ (subW_eval_ne hpt hv)]

/-- `Ŵ_v` vanishes on `pt a`, `a < 2^v`. -/
theorem normW_eval_lt (pt : ℕ → L) {v a : ℕ} (ha : a < 2 ^ v) : (normW pt v).eval (pt a) = 0 := by
  rw [normW, eval_mul, eval_C, eval_subW pt v (pt a), prod_eq_zero (mem_range.2 ha) (sub_self _),
    mul_zero]

theorem normW_natDegree (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {v : ℕ} (hv : v < N) :
    normW pt v ≠ 0 ∧ (normW pt v).natDegree = 2 ^ v := by
  have hc : ((subW pt v).eval (pt (2 ^ v)))⁻¹ ≠ 0 := inv_ne_zero (subW_eval_ne hpt hv)
  refine ⟨mul_ne_zero (C_ne_zero.2 hc) (subW_monic pt v).ne_zero, ?_⟩
  rw [normW, natDegree_C_mul hc, natDegree_subW]

theorem novelX_eq_bitProd (pt : ℕ → L) {ℓ x : ℕ} (hx : x < 2 ^ ℓ) :
    novelX pt x = bitProd (normW pt) ℓ x :=
  bitProd_congr _ Nat.lt_two_pow_self hx

/-- **`novelX_natDegree`**: `X_x ≠ 0` has degree exactly `x` for `x < 2^N`. -/
theorem novelX_natDegree (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {x : ℕ} (hx : x < 2 ^ N) :
    novelX pt x ≠ 0 ∧ (novelX pt x).natDegree = x := by
  rw [novelX_eq_bitProd pt hx]
  have key : ∀ ℓ j, j < 2 ^ ℓ → ℓ ≤ N →
      bitProd (normW pt) ℓ j ≠ 0 ∧ (bitProd (normW pt) ℓ j).natDegree = j := by
    apply bit_induction
    · intro _; simp [bitProd, bitSel]
    · intro ℓ j hj ih hℓ; rw [bitProd_succ_lo _ hj]; exact ih (by omega)
    · intro ℓ j hj ih hℓ
      obtain ⟨h0, hd⟩ := ih (by omega)
      obtain ⟨hW0, hWd⟩ := normW_natDegree hpt (show ℓ < N by omega)
      rw [bitProd_succ_hi _ hj]
      exact ⟨mul_ne_zero h0 hW0, by rw [natDegree_mul h0 hW0, hd, hWd, add_comm]⟩
  exact key N x hx le_rfl

/-- **Block-triangularity** (BLUEPRINT §2.1): `X_x(pt j) = 0` when bit `v` of `x` is set and
`j < 2^v`. -/
theorem novelX_eval_zero (pt : ℕ → L) {x v j : ℕ} (hb : x.testBit v = true) (hj : j < 2 ^ v) :
    (novelX pt x).eval (pt j) = 0 := by
  have hv : v < x := Nat.lt_two_pow_self.trans_le (Nat.ge_two_pow_of_testBit hb)
  rw [novelX, bitProd, bitSel, eval_prod]
  exact prod_eq_zero (mem_range.2 hv) (by simp only [hb, ite_true]; exact normW_eval_lt pt hj)

/-- Block-triangularity at the top bit: `X_x(pt j) = 0` for `j < 2^msb(x)`. -/
theorem novelX_eval_lt_msb (pt : ℕ → L) {x j : ℕ} (hx : x ≠ 0) (hj : j < 2 ^ x.log2) :
    (novelX pt x).eval (pt j) = 0 :=
  novelX_eval_zero pt (Nat.testBit_log2 hx) hj

/-- The tensor identity for the novel basis: `Σ_{x<2^ℓ} eq(r, x) X_x(y) =
∏_{v<ℓ} (1 − r_v + r_v Ŵ_v(y))`. -/
theorem novelX_tensor (pt : ℕ → L) (r : ℕ → L) (ℓ : ℕ) (y : L) :
    ∑ x ∈ range (2 ^ ℓ), eqBits r ℓ x * (novelX pt x).eval y =
      ∏ v ∈ range ℓ, (1 - r v + r v * (normW pt v).eval y) := by
  rw [← tensor_identity]
  refine sum_congr rfl fun x hx => ?_
  rw [novelX_eq_bitProd pt (mem_range.1 hx), bitProd, bitSel, bitProd, bitSel, eval_prod]
  congr 1
  exact prod_congr rfl fun v _ => by split_ifs <;> simp

end NovelBasis

/-! ## `W_v` is additive on a subspace domain (`W_linear`) -/

section Linear

variable {L : Type*} [Field L] [CharP L 2] {pt : ℕ → L}

theorem two_pow_add_eq_xor {v a : ℕ} (ha : a < 2 ^ v) : 2 ^ v + a = 2 ^ v ^^^ a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy i v with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [h.ne']
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha]; simp
  · have h1 : 2 ^ v + a < 2 ^ i :=
      calc 2 ^ v + a < 2 ^ v + 2 ^ v := by omega
        _ = 2 ^ (v + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    rw [Nat.testBit_lt_two_pow h1,
      Nat.testBit_lt_two_pow (ha.trans (Nat.pow_lt_pow_right (by norm_num) h))]
    simp [h.ne]

omit [CharP L 2] in
/-- The recursion `W_{v+1}(y) = W_v(y) (W_v(y) − W_v(pt 2^v))`, given the additivity of `W_v`. -/
theorem eval_subW_succ (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) {v : ℕ}
    (hW : ∀ y z, (subW pt v).eval (y + z) = (subW pt v).eval y + (subW pt v).eval z) (y : L) :
    (subW pt (v + 1)).eval y =
      (subW pt v).eval y * ((subW pt v).eval y - (subW pt v).eval (pt (2 ^ v))) := by
  have hsh : (subW pt v).eval y - (subW pt v).eval (pt (2 ^ v)) =
      (subW pt v).eval (y - pt (2 ^ v)) := by
    rw [sub_eq_iff_eq_add, ← hW, sub_add_cancel]
  rw [hsh, eval_subW pt (v + 1) y, eval_subW pt v y, eval_subW pt v (y - pt (2 ^ v)), pow_succ,
    mul_two, prod_range_add]
  congr 1
  refine prod_congr rfl fun a ha => ?_
  rw [two_pow_add_eq_xor (mem_range.1 ha), hadd]
  ring

/-- **`W_linear`** (Appendix A.1): on a domain with `pt (a xor b) = pt a + pt b`, every `W_v` is
additive (a linearised polynomial). -/
theorem subW_add (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (v : ℕ) (y z : L) :
    (subW pt v).eval (y + z) = (subW pt v).eval y + (subW pt v).eval z := by
  induction v generalizing y z with
  | zero =>
    have h0 : pt 0 = 0 := by simpa using hadd 0 0
    simp [eval_subW, h0]
  | succ v ih =>
    rw [eval_subW_succ hadd ih, eval_subW_succ hadd ih, eval_subW_succ hadd ih, ih]
    linear_combination ((subW pt v).eval y * (subW pt v).eval z) * CharTwo.two_eq_zero (R := L)

theorem normW_add (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (v : ℕ) (y z : L) :
    (normW pt v).eval (y + z) = (normW pt v).eval y + (normW pt v).eval z := by
  simp only [normW, eval_mul, eval_C, subW_add hadd, mul_add]

/-- The LCH recursion on normalised values: with `p = pt 2^{v+1}`,
`Ŵ_{v+1}(y) = Ŵ_v(y)(Ŵ_v(y) − 1) / (Ŵ_v(p)(Ŵ_v(p) − 1))`. -/
theorem normW_succ (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) {N : ℕ}
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {v : ℕ} (hv : v + 1 < N) (y : L) :
    (normW pt (v + 1)).eval y =
      (normW pt v).eval y * ((normW pt v).eval y - 1) /
        ((normW pt v).eval (pt (2 ^ (v + 1))) * ((normW pt v).eval (pt (2 ^ (v + 1))) - 1)) := by
  have hc := subW_eval_ne hpt (show v < N by omega)
  have hc1 := subW_eval_ne hpt hv
  simp only [normW, eval_mul, eval_C] at hc1 ⊢
  rw [eval_subW_succ hadd (subW_add hadd v), eval_subW_succ hadd (subW_add hadd v)] at *
  set a := (subW pt v).eval y
  set b := (subW pt v).eval (pt (2 ^ (v + 1)))
  set c := (subW pt v).eval (pt (2 ^ v))
  have hb : b * (b - c) ≠ 0 := hc1
  have hb' : c⁻¹ * b * (c⁻¹ * b - 1) ≠ 0 := by
    rw [show c⁻¹ * b * (c⁻¹ * b - 1) = c⁻¹ * c⁻¹ * (b * (b - c)) by field_simp]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hc) (inv_ne_zero hc)) hb
  field_simp

end Linear

/-! ## The encoding `Enc_k` (BLUEPRINT §2.1) -/

section Enc

variable {L M : Type*} [Field L] [Field M] [Algebra L M]

/-- **`Enc_k`**: `Enc_k(c)[j] = Σ_{x<k} c_x X_x(pt j)` for `c ∈ M^k`, `j < n`; the message is the
vector of novel-basis coefficients. -/
noncomputable def enc (pt : ℕ → L) (n k : ℕ) (c : Fin k → M) : Fin n → M :=
  fun j => ∑ x : Fin k, c x * algebraMap L M ((novelX pt x).eval (pt j))

/-- `Enc_k` as an `M`-linear map. -/
noncomputable def encL (pt : ℕ → L) (n k : ℕ) : (Fin k → M) →ₗ[M] (Fin n → M) where
  toFun := enc pt n k
  map_add' c c' := by funext j; simp [enc, add_mul, sum_add_distrib]
  map_smul' a c := by funext j; simp [enc, mul_sum, mul_assoc]

/-- The code `C_M = Enc_k(M^k)` (`C_K` over `K`, `C_F` over `F`). -/
noncomputable def encCode (pt : ℕ → L) (n k : ℕ) : Submodule M (Fin n → M) :=
  LinearMap.range (encL (M := M) pt n k)

/-- The polynomial `Σ_x c_x X_x ∈ M[X]` that `Enc_k(c)` evaluates. -/
noncomputable def encPoly (pt : ℕ → L) {k : ℕ} (c : Fin k → M) : M[X] :=
  ∑ x : Fin k, C (c x) * (novelX pt x).map (algebraMap L M)

theorem encPoly_eval (pt : ℕ → L) (n k : ℕ) (c : Fin k → M) (j : Fin n) :
    (encPoly pt c).eval (algebraMap L M (pt j)) = enc pt n k c j := by
  simp only [encPoly, enc, eval_finsetSum, eval_mul, eval_C, eval_map, eval₂_at_apply]

variable {pt : ℕ → L} {N : ℕ}

theorem novelX_map (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {x : ℕ} (hx : x < 2 ^ N) :
    ((novelX pt x).map (algebraMap L M)).natDegree = x ∧
      ((novelX pt x).map (algebraMap L M)).leadingCoeff ≠ 0 := by
  obtain ⟨h0, hd⟩ := novelX_natDegree hpt hx
  refine ⟨by rw [natDegree_map, hd], ?_⟩
  rw [leadingCoeff_map, ne_eq, map_eq_zero, leadingCoeff_eq_zero]
  exact h0

theorem encPoly_mem (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {k : ℕ} (hk : k ≤ 2 ^ N)
    (c : Fin k → M) : encPoly pt c ∈ degreeLT M k := by
  refine sum_mem fun x _ => ?_
  rw [← smul_eq_C_mul]
  refine Submodule.smul_mem _ _ (mem_degreeLT.2 (degree_le_natDegree.trans_lt ?_))
  rw [(novelX_map (M := M) hpt (x.2.trans_le hk)).1]; exact_mod_cast x.2

theorem encPoly_add (pt : ℕ → L) {k : ℕ} (c c' : Fin k → M) :
    encPoly pt (c + c') = encPoly pt c + encPoly pt c' := by
  simp [encPoly, add_mul, sum_add_distrib]

theorem encPoly_single (pt : ℕ → L) {k : ℕ} (t : Fin k) (a : M) :
    encPoly pt (Pi.single t a) = C a * (novelX pt t).map (algebraMap L M) := by
  classical
  rw [encPoly, sum_eq_single t (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- Every polynomial of degree `< k ≤ 2^N` is `Σ_x c_x X_x`. -/
theorem exists_encPoly (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {k : ℕ} (hk : k ≤ 2 ^ N) :
    ∀ d, d < k → ∀ p : M[X], p.natDegree ≤ d → ∃ c : Fin k → M, encPoly pt c = p := by
  intro d
  induction d with
  | zero =>
    intro h0 p hp
    refine ⟨Pi.single ⟨0, h0⟩ (p.coeff 0), ?_⟩
    rw [encPoly_single, eq_C_of_natDegree_le_zero hp]
    simp [novelX, bitProd, bitSel]
  | succ d ih =>
    intro hd p hp
    set t : Fin k := ⟨d + 1, hd⟩
    obtain ⟨hdeg, hlc⟩ := novelX_map (M := M) hpt (show d + 1 < 2 ^ N by omega)
    set Y := (novelX pt (d + 1)).map (algebraMap L M)
    set q := p - C (p.coeff (d + 1) / Y.leadingCoeff) * Y
    have hq : q.natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      simp only [q, coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (d + 1) i with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt h),
          coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt h), mul_zero, sub_zero]
      · obtain rfl : i = d + 1 := by omega
        rw [show Y.coeff (d + 1) = Y.leadingCoeff by rw [leadingCoeff, hdeg],
          div_mul_cancel₀ _ hlc, sub_self]
    obtain ⟨c, hc⟩ := ih (by omega) q hq
    refine ⟨c + Pi.single t (p.coeff (d + 1) / Y.leadingCoeff), ?_⟩
    rw [encPoly_add, hc, encPoly_single]
    simp [q, Y, t]

/-- **`C_M = RS[M, pt, k]`**: the novel-basis code is the Reed–Solomon code on the points `pt j`
(for `k ≤ 2^N`). Distance, interpolation and the proximity lemmas therefore apply to it. -/
theorem encCode_eq_rsCode (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {n k : ℕ} (hk : k ≤ 2 ^ N) :
    encCode (M := M) pt n k = rsCode (fun j : Fin n => algebraMap L M (pt j)) k := by
  ext w
  rw [mem_rsCode]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨encPoly pt c, mem_degreeLT.1 (encPoly_mem hpt hk c),
      funext fun j => encPoly_eval pt n k c j⟩
  · rintro ⟨p, hp, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · obtain rfl : p = 0 := by simpa using hp
      exact ⟨0, funext fun j => by simp [evalWord, encL, enc]⟩
    obtain ⟨c, rfl⟩ := exists_encPoly hpt hk (k - 1) (by omega) p
      (natDegree_le_pred (natDegree_le_of_degree_le hp.le) (coeff_eq_zero_of_degree_lt hp))
    exact ⟨c, funext fun j => (encPoly_eval pt n k c j).symm⟩

/-- `Σ_x c_x X_x ≠ 0` for `c ≠ 0`: its coefficient at the top nonzero index `t` is
`c_t · lc(X_t) ≠ 0`. -/
theorem encPoly_ne_zero (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {k : ℕ} (hk : k ≤ 2 ^ N)
    {c : Fin k → M} (h : c ≠ 0) : encPoly pt c ≠ 0 := by
  classical
  have hne : (univ.filter fun x => c x ≠ 0).Nonempty := by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 h; exact ⟨x, by simpa using hx⟩
  set t := (univ.filter fun x => c x ≠ 0).max' hne
  have ht : c t ≠ 0 := by simpa using (univ.filter fun x => c x ≠ 0).max'_mem hne
  intro h0
  have hc := congrArg (fun p => p.coeff t) h0
  simp only [encPoly, finsetSum_coeff, coeff_C_mul, coeff_zero] at hc
  rw [sum_eq_single t] at hc
  · obtain ⟨hdeg, hlc⟩ := novelX_map (M := M) hpt (t.2.trans_le hk)
    rw [leadingCoeff, hdeg] at hlc
    exact mul_ne_zero ht hlc hc
  · intro x _ hxt
    by_cases hx : c x = 0
    · simp [hx]
    rw [coeff_eq_zero_of_natDegree_lt (by
      rw [(novelX_map (M := M) hpt (x.2.trans_le hk)).1]
      exact (le_max' _ x (by simpa using hx)).lt_of_ne hxt), mul_zero]
  · simp

/-- **`enc_injective`** (`coeffs_of_values` is well defined): with `k ≤ n` points, `Enc_k` is
injective, so a codeword has one message. -/
theorem enc_injective (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {n k : ℕ} (hk : k ≤ 2 ^ N)
    (hn : n ≤ 2 ^ N) (hkn : k ≤ n) : Function.Injective (enc (M := M) pt n k) := by
  classical
  intro c c' h
  by_contra hne
  apply encPoly_ne_zero hpt hk (sub_ne_zero.2 hne)
  have hinj : Function.Injective fun j : Fin n => algebraMap L M (pt j) := fun a b e =>
    Fin.ext (hpt (Set.mem_Iio.2 (a.2.trans_le hn)) (Set.mem_Iio.2 (b.2.trans_le hn))
      ((algebraMap L M).injective e))
  have hc := poly_eq_of_agree hinj (mem_degreeLT.1 (encPoly_mem hpt hk c))
    (mem_degreeLT.1 (encPoly_mem hpt hk c')) univ (by simpa using hkn) fun j _ => by
      rw [encPoly_eval pt n k, encPoly_eval pt n k, h]
  rw [show encPoly pt (c - c') = encPoly pt c - encPoly pt c' by
    simp [encPoly, sub_mul, sum_sub_distrib], hc, sub_self]

end Enc

/-! ## The protocol's domain `D ⊂ F` and the codes `C_F`, `C_K` (Appendix A.1) -/

section Domain

/-- **`D[j] := (toBF64 j, 0) ∈ F`**: the word `j` as a `BF64` element, the `F₂`-span of
`1, x, …, x^63` (Appendix A.1; the protocol uses `j < 2^20`). -/
def D (j : ℕ) : F := F.ofB64 ⟨UInt64.ofNat j⟩

/-- `D` is `F₂`-linear in the bits of `j`. -/
theorem D_xor (a b : ℕ) : D (a ^^^ b) = D a + D b := by
  have h : UInt64.ofNat (a ^^^ b) = UInt64.ofNat a ^^^ UInt64.ofNat b := by
    apply UInt64.toNat_inj.1
    simp
  change F.ofB64 _ = F.add (F.ofB64 _) (F.ofB64 _)
  simp only [F.ofB64, F.add, h]
  rfl

/-- **`D_inj`**: `D` is injective on `[0, 2^64)`. -/
theorem D_injOn : Set.InjOn D (Set.Iio (2 ^ 64)) := by
  intro a ha b hb h
  have := congrArg (fun z : F => z.c₀.val.toNat) h
  simp only [D, F.ofB64] at this
  rwa [UInt64.toNat_ofNat_of_lt' ha, UInt64.toNat_ofNat_of_lt' hb] at this

/-- `D` as `n` points of `M ⊇ F` (`M = F` or `K`). -/
def Dpts {M : Type*} [Field M] [Algebra F M] (n : ℕ) : Fin n → M := fun j => algebraMap F M (D j)

theorem Dpts_injective {M : Type*} [Field M] [Algebra F M] {n : ℕ} (hn : n ≤ 2 ^ 64) :
    Function.Injective (Dpts (M := M) n) := by
  intro a b h
  exact Fin.ext (D_injOn (Set.mem_Iio.2 (a.2.trans_le hn)) (Set.mem_Iio.2 (b.2.trans_le hn))
    ((algebraMap F M).injective h))

/-- **`C_K = RS[K, D, k]`** (and `C_F` with `M = F`): the novel-basis code over the protocol's
domain is the Reed–Solomon code. -/
theorem encCode_D {M : Type*} [Field M] [Algebra F M] {n k : ℕ} (hk : k ≤ 2 ^ 64) :
    encCode (M := M) D n k = rsCode (Dpts n) k :=
  encCode_eq_rsCode D_injOn hk

end Domain

end FR
