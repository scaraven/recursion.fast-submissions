-- WP-13b: the pure decoder of `C_rec` (BLUEPRINT §6.2 steps 5–6) and its correctness. New on the model of
-- rf-k/submissions/flock-recursive/lean/FRXLevel.lean@8bff272b (`level_decode`: interpolate on the first `k`
-- agreeing positions, then the butterflies) and FRXBaryDefs.lean (`decode_agree`); the proof uses the ported
-- `Lvm.Nb.decode_row` (FR `decode_row`).
import LvmMcaUd
import CompPoly.Fields.Binary.BF64.Ext3
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.GetD

-- (GOLF2: 22 declarations that `certified` does not use moved verbatim to `LvmXDecUdOff`, outside its import closure.)

-- ===== merged from `LvmXEnc` (GOLF module merge: `LvmXEnc.lean` is now a stub importing `LvmXDec`) =====
section
-- WP-13b. adapted from rf-k/submissions/flock-recursive/lean@8bff272b, generic over the field:
-- FRRS.lean (sections Generic (`rsCode` part), Bits, Tensor, NovelBasis, Linear, Enc), FRSoundnessCoreTruths.lean
-- (section `Twin`, formerly `FRRSEval`), FRXBaryDefs.lean (sections `Bfly`, `Pure`) and FRXFwd.lean (section
-- `FRXEncB`, generalised from FR's domain `D` to any additive `pt`: `pt_block`, `normW_block`, `fwdRun_block`,
-- `fwdRun_enc`). Namespace `FR` → `Lvm.Nb`. Proofs verbatim except where the generalisation needs it.

/-!
# The novel basis, its encoder, the additive NTT and interpolation (generic)

Over a field `L` of characteristic 2 with a domain `pt : ℕ → L` additive in the bits
(`pt (a xor b) = pt a + pt b`) and injective on `[0, 2^N)`, and an extension `M ⊇ L`:

* `normW pt v = Ŵ_v` (LCH14's normalised subspace polynomial `W_v / W_v(pt 2^v)`,
  `W_v = Π_{a < 2^v} (X − pt a)`), `novelX pt x = X_x = Π_{v ∈ bits x} Ŵ_v`;
* `enc`, `encN`: `Enc_k(c)[j] = Σ_{x<k} c_x X_x(pt j)`, injective for `k ≤ n ≤ 2^N`
  (`enc_injective`); its range is the Reed–Solomon code on `pt` (`encCode_eq_rsCode`);
* `wRow`, `wAt`: the computable table `Ŵ_v(pt 2^i)` (LCH recursion) and `Ŵ_v(pt j)` by additivity
  (`wAt_eq`);
* `coeffsAt` (the inverse additive NTT, top-down) and `bflyRun` (the same, bottom-up in place):
  values on `pt [0, 2^ℓ)` to novel-basis coefficients (`coeffs_spec`, `coeffs_unique`,
  `bflyRun_coeffs`);
* `fwdRun` (the forward additive NTT, in place): `Enc` of a zero-padded message at every position
  (`fwdRun_enc`);
* `interpF` (Lagrange interpolation at `pt`), `interpF_eq`, `decode_row` (interpolate on `2^ℓ`
  agreeing positions, then take coefficients: the message), and the barycentric forms
  `interpF_self`, `interpF_bary`.

lvm's instance (`L = K = BF64`, `pt j = K.ofBits j`, `N = 15`) is in `LvmXDec`.
-/

namespace Lvm.Nb

open Polynomial Finset

section Generic

variable {K : Type*} [Field K] {n : ℕ}

/-- `evalWord x` as a `K`-linear map. -/
noncomputable def evalWordL (x : Fin n → K) : K[X] →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun j => Polynomial.leval (x j)

/-- **The Reed–Solomon code** `RS[K, x, k]`: evaluations at `x` of the polynomials of degree
`< k`. -/
noncomputable def rsCode (x : Fin n → K) (k : ℕ) : Submodule K (Fin n → K) :=
  (degreeLT K k).map (evalWordL x)

variable [DecidableEq K]

/-- Two polynomials of degree `< k` agreeing at `k` distinct points `x j`, `j ∈ S`, are equal. -/
theorem poly_eq_of_agree {x : Fin n → K} (hx : Function.Injective x) {k : ℕ} {p q : K[X]}
    (hp : p.degree < k) (hq : q.degree < k) (S : Finset (Fin n)) (hS : k ≤ S.card)
    (h : ∀ j ∈ S, p.eval (x j) = q.eval (x j)) : p = q := by
  have hS' : (k : WithBot ℕ) ≤ (S.image x).card := by
    rw [card_image_of_injective _ hx]; exact_mod_cast hS
  exact eq_of_degrees_lt_of_eval_finset_eq _ (hp.trans_le hS') (hq.trans_le hS')
    (forall_mem_image.2 h)

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
      have : j' < 2 ^ ℓ := by rw [pow_succ] at hj; (clear * - hj; omega)
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
  exact absurd (mem_range.1 ha) (by (clear * - this; omega))

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
      calc 2 ^ v + a < 2 ^ v + 2 ^ v := by (clear * - ha; omega)
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
  have hc := subW_eval_ne hpt (show v < N by (clear * - hv; omega))
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
section Twin

variable {L : Type*} [Field L]

/-- **The basis table row** `v`: `(Ŵ_v(pt 2^i))_{i<N}`, by the LCH recursion on values. -/
def wRow (pt : ℕ → L) (N : ℕ) : ℕ → List L
  | 0 => (List.range N).map fun i => (pt (2 ^ i) - pt 0) / (pt 1 - pt 0)
  | v + 1 =>
    let r := wRow pt N v
    let b := r.getD (v + 1) 0
    r.map fun a => a * (a - 1) / (b * (b - 1))

/-- **`Ŵ_v(pt j)`** from the table: the sum over the set bits `i` of `j` of `Ŵ_v(pt 2^i)`. -/
def wAt (pt : ℕ → L) (N v j : ℕ) : L :=
  ∑ i ∈ range N, if j.testBit i then (wRow pt N v).getD i 0 else 0

theorem wRow_length (pt : ℕ → L) (N : ℕ) : ∀ v, (wRow pt N v).length = N
  | 0 => by simp [wRow]
  | v + 1 => by simp [wRow, wRow_length pt N v]

theorem normW_zero_eval (pt : ℕ → L) (y : L) :
    (normW pt 0).eval y = (y - pt 0) / (pt 1 - pt 0) := by
  simp [normW, eval_subW, div_eq_mul_inv, mul_comm]

variable [CharP L 2] {pt : ℕ → L} {N : ℕ}

/-- The table holds the values of `Ŵ_v` at the basis points. -/
theorem wRow_spec (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) :
    ∀ v, v < N → ∀ i, i < N → (wRow pt N v).getD i 0 = (normW pt v).eval (pt (2 ^ i)) := by
  intro v
  induction v with
  | zero =>
    intro _ i hi
    simp [wRow, List.getD_eq_getElem?_getD, hi, normW_zero_eval]
  | succ v ih =>
    intro hv i hi
    have hlen := wRow_length pt N v
    rw [wRow, List.getD_eq_getElem _ _ (by simpa [hlen]), List.getElem_map,
      ← List.getD_eq_getElem _ 0, ih (by omega) i hi, ih (by omega) (v + 1) hv,
      normW_succ hadd hpt hv]

omit [CharP L 2] in
/-- `pt j` is the sum of `pt 2^i` over the set bits `i` of `j < 2^ℓ`. -/
theorem pt_bits (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) :
    ∀ ℓ j, j < 2 ^ ℓ → pt j = ∑ i ∈ range ℓ, if j.testBit i then pt (2 ^ i) else 0 := by
  have h0 : pt 0 = 0 := by simpa using hadd 0 0
  apply bit_induction
  · simp [h0]
  · intro ℓ j hj ih
    rw [sum_range_succ, Nat.testBit_lt_two_pow hj, ih]; simp
  · intro ℓ j hj ih
    rw [two_pow_add_eq_xor hj, hadd, ← two_pow_add_eq_xor hj, sum_range_succ,
      Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj, ih]
    simp only [Bool.not_false, ite_true]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun i hi => by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hi)]

theorem normW_eval_sum (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (v : ℕ) {ι : Type*}
    (s : Finset ι) (g : ι → L) :
    (normW pt v).eval (∑ i ∈ s, g i) = ∑ i ∈ s, (normW pt v).eval (g i) := by
  classical
  have h0 : (normW pt v).eval 0 = 0 := by simpa using normW_add hadd v 0 0
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, normW_add hadd, ih]

/-- **`wAt_eq`**: the table value is `Ŵ_v(pt j)` (`v < N`, `j < 2^N`). -/
theorem wAt_eq (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (hpt : Set.InjOn pt (Set.Iio (2 ^ N)))
    {v j : ℕ} (hv : v < N) (hj : j < 2 ^ N) : wAt pt N v j = (normW pt v).eval (pt j) := by
  rw [pt_bits hadd N j hj, normW_eval_sum hadd, wAt]
  refine sum_congr rfl fun i hi => ?_
  split_ifs
  · exact wRow_spec hadd hpt v hv i (mem_range.1 hi)
  · simpa using (normW_eval_sum hadd v (∅ : Finset ℕ) fun _ => (0 : L)).symm

variable {M : Type*} [Field M] [Algebra L M]

/-! ## Values to coefficients, interpolation (S-D2; BLUEPRINT §6.2) -/

/-- `Enc` as a word indexed by `ℕ`: `encN pt c j = Σ_x c_x X_x(pt j)` (`enc pt n k c j` for
`j < n`, `enc_eq_encN`). -/
noncomputable def encN (pt : ℕ → L) {k : ℕ} (c : Fin k → M) (j : ℕ) : M :=
  ∑ x : Fin k, c x * algebraMap L M ((novelX pt x).eval (pt j))

omit [CharP L 2] in
theorem enc_eq_encN (pt : ℕ → L) {n k : ℕ} (c : Fin k → M) (j : Fin n) :
    enc pt n k c j = encN pt c j := rfl

omit [CharP L 2] in
theorem novelX_two_pow_add (pt : ℕ → L) {ℓ x : ℕ} (hx : x < 2 ^ ℓ) :
    novelX pt (2 ^ ℓ + x) = novelX pt x * normW pt ℓ := by
  rw [novelX_eq_bitProd pt (show 2 ^ ℓ + x < 2 ^ (ℓ + 1) by rw [pow_succ]; omega),
    bitProd_succ_hi _ hx, ← novelX_eq_bitProd pt hx]

/-- **The inverse additive NTT** on the coset `pt s + pt [0, 2^ℓ)`: from the values `y j` at
`pt (s + j)`, `j < 2^ℓ`, the novel-basis coefficients (`coeffsAt_spec`). One level: with
`α = Ŵ_ℓ(pt s)`, the halves give `u = c_lo + α c_hi` and `w = c_lo + (α + 1) c_hi`. -/
def coeffsAt (pt : ℕ → L) (N : ℕ) : ℕ → ℕ → (ℕ → M) → ℕ → M
  | 0, _, y => y
  | ℓ + 1, s, y => fun x =>
    let u := coeffsAt pt N ℓ s y
    let w := coeffsAt pt N ℓ (s + 2 ^ ℓ) fun j => y (2 ^ ℓ + j)
    let α := algebraMap L M (wAt pt N ℓ s)
    if x < 2 ^ ℓ then u x - α * (w x - u x) else w (x - 2 ^ ℓ) - u (x - 2 ^ ℓ)

omit [CharP L 2] in
theorem sum_novel_succ (pt : ℕ → L) (ℓ : ℕ) (c : ℕ → M) (P : L) :
    ∑ x ∈ range (2 ^ (ℓ + 1)), c x * algebraMap L M ((novelX pt x).eval P) =
      ∑ x ∈ range (2 ^ ℓ), (c x + c (2 ^ ℓ + x) * algebraMap L M ((normW pt ℓ).eval P)) *
        algebraMap L M ((novelX pt x).eval P) := by
  rw [pow_succ, mul_two, sum_range_add, ← sum_add_distrib]
  refine sum_congr rfl fun x hx => ?_
  rw [novelX_two_pow_add pt (mem_range.1 hx), eval_mul, map_mul]
  ring

/-- **`coeffsAt_spec`**: on a coset `pt s + pt [0, 2^ℓ)` (`pt (s + j) = pt s + pt j`), the
coefficients reproduce the values. -/
theorem coeffsAt_spec (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) :
    ∀ ℓ s (y : ℕ → M), ℓ ≤ N → s + 2 ^ ℓ ≤ 2 ^ N → (∀ j < 2 ^ ℓ, pt (s + j) = pt s + pt j) →
      ∀ j < 2 ^ ℓ, ∑ x ∈ range (2 ^ ℓ),
        coeffsAt pt N ℓ s y x * algebraMap L M ((novelX pt x).eval (pt (s + j))) = y j := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro s y _ _ _ j hj
    obtain rfl : j = 0 := by simpa using hj
    simp [coeffsAt, novelX, bitProd, bitSel]
  | succ ℓ ih =>
    intro s y hN hs H j hj
    have hsN : s < 2 ^ N := by have := Nat.one_le_two_pow (n := ℓ + 1); (clear * - hs this; omega)
    have hα : (normW pt ℓ).eval (pt s) = wAt pt N ℓ s := (wAt_eq hadd hpt (by (clear * - hN; omega)) hsN).symm
    have hpow : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
    have hW : ∀ i < 2 ^ ℓ, (normW pt ℓ).eval (pt i) = 0 := fun i hi => normW_eval_lt pt hi
    have hup : ∀ j' < 2 ^ ℓ, pt (2 ^ ℓ + j') = pt (2 ^ ℓ) + pt j' := fun j' h' => by
      rw [two_pow_add_eq_xor h', hadd]
    rw [sum_novel_succ]
    simp only [coeffsAt]
    by_cases hlo : j < 2 ^ ℓ
    · rw [H j (by omega), normW_add hadd, hW j hlo, add_zero, hα, ← H j (by omega)]
      rw [← ih s y (by (clear * - hN; omega)) (by (clear * - hs hsN; omega)) (fun i hi => H i (by (clear * - hj hi; omega))) j hlo]
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      simp only [hx', ite_true, show ¬ (2 ^ ℓ + x < 2 ^ ℓ) by (clear * -; omega), ite_false,
        Nat.add_sub_cancel_left]
      ring
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlo)
      have hj' : j' < 2 ^ ℓ := by (clear * - hj; omega)
      have hP : pt (s + (2 ^ ℓ + j')) = pt (s + 2 ^ ℓ + j') := by rw [Nat.add_assoc]
      have H' : ∀ i < 2 ^ ℓ, pt (s + 2 ^ ℓ + i) = pt (s + 2 ^ ℓ) + pt i := fun i hi => by
        rw [Nat.add_assoc, H _ (by (clear * - hi; omega)), H _ (by (clear * - hi; omega)), hup i hi, add_assoc]
      have hWv : (normW pt ℓ).eval (pt (s + (2 ^ ℓ + j'))) = wAt pt N ℓ s + 1 := by
        rw [H _ (by omega), normW_add hadd, hup j' hj', normW_add hadd, hW j' hj',
          normW_eval_self hpt (by (clear * - hN; omega)), add_zero, hα]
      rw [hWv, hP]
      rw [← ih (s + 2 ^ ℓ) (fun i => y (2 ^ ℓ + i)) (by (clear * - hN; omega)) (by (clear * - hs; omega)) H' j' hj']
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      simp only [hx', ite_true, show ¬ (2 ^ ℓ + x < 2 ^ ℓ) by (clear * -; omega), ite_false,
        Nat.add_sub_cancel_left, map_add, map_one]
      ring

/-- **`coeffs_of_values`**: the novel-basis message of the codeword whose values on
`pt 0, …, pt (2^ℓ − 1)` are `y` (the inverse additive NTT, `O(ℓ 2^ℓ)` butterflies). -/
def coeffsOfValues (pt : ℕ → L) (N ℓ : ℕ) (y : ℕ → M) : Fin (2 ^ ℓ) → M :=
  fun x => coeffsAt pt N ℓ 0 y x

/-- **`coeffs_spec`**: `Enc(coeffs_of_values y)` takes the values `y` on `pt [0, 2^ℓ)`. -/
theorem coeffs_spec (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ : ℕ} (hℓ : ℓ ≤ N) (y : ℕ → M) {j : ℕ}
    (hj : j < 2 ^ ℓ) : encN pt (coeffsOfValues pt N ℓ y) j = y j := by
  have h0 : pt 0 = 0 := by simpa using hadd 0 0
  have := coeffsAt_spec hadd hpt ℓ 0 y hℓ (by simpa using Nat.pow_le_pow_right two_pos hℓ)
    (fun i _ => by simp [h0]) j hj
  rw [zero_add] at this
  rw [encN, ← this]
  exact Fin.sum_univ_eq_sum_range (fun x => coeffsAt pt N ℓ 0 y x *
    algebraMap L M ((novelX pt x).eval (pt j))) _

/-- The message is determined by the values on `pt [0, 2^ℓ)`: `coeffs_of_values` inverts
`Enc`. -/
theorem coeffs_unique (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ : ℕ} (hℓ : ℓ ≤ N) (y : ℕ → M)
    (c : Fin (2 ^ ℓ) → M) (hc : ∀ j < 2 ^ ℓ, encN pt c j = y j) :
    coeffsOfValues pt N ℓ y = c := by
  have hk : 2 ^ ℓ ≤ 2 ^ N := Nat.pow_le_pow_right two_pos hℓ
  refine enc_injective (n := 2 ^ ℓ) hpt hk hk le_rfl (funext fun j => ?_)
  rw [enc_eq_encN, enc_eq_encN, coeffs_spec hadd hpt hℓ y j.2, hc j j.2]

/-- **`interpF`**: Lagrange interpolation through the values `y i` at `pt i`, `i ∈ J`, evaluated at
`pt j`: `Σ_{i∈J} y_i ∏_{m ∈ J∖i} (pt j − pt m)/(pt i − pt m)`. -/
def interpF (pt : ℕ → L) (J : Finset ℕ) (y : ℕ → M) (j : ℕ) : M :=
  ∑ i ∈ J, y i * ∏ m ∈ J.erase i,
    (algebraMap L M (pt j) - algebraMap L M (pt m)) /
      (algebraMap L M (pt i) - algebraMap L M (pt m))

omit [CharP L 2] in
theorem interpF_congr (pt : ℕ → L) (J : Finset ℕ) {y y' : ℕ → M} (h : ∀ i ∈ J, y i = y' i)
    (j : ℕ) : interpF pt J y j = interpF pt J y' j :=
  sum_congr rfl fun i hi => by rw [h i hi]

omit [CharP L 2] in
/-- **`interpF_eq`**: on distinct points, `interpF` evaluates every polynomial of degree `< |J|`
from its values on `J`. -/
theorem interpF_eq {pt : ℕ → L} {J : Finset ℕ} (hJ : Set.InjOn pt J) {p : M[X]}
    (hp : p.degree < J.card) (j : ℕ) :
    interpF pt J (fun i => p.eval (algebraMap L M (pt i))) j = p.eval (algebraMap L M (pt j)) := by
  have hv : Set.InjOn (fun i => algebraMap L M (pt i)) J := fun a ha b hb h =>
    hJ ha hb ((algebraMap L M).injective h)
  conv_rhs => rw [Lagrange.eq_interpolate hv hp]
  simp [interpF, Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor,
    eval_finsetSum, eval_prod, div_eq_inv_mul]

/-- **Erasure decoding of a row** (BLUEPRINT §6.2): if the word `u` agrees with `Enc(c)` on a set
`J` of `2^ℓ` distinct points, interpolating on `J` and taking coefficients returns `c`. -/
theorem decode_row (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ : ℕ} (hℓ : ℓ ≤ N) {J : Finset ℕ}
    (hJ : Set.InjOn pt J) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → M) (u : ℕ → M)
    (hu : ∀ i ∈ J, u i = encN pt c i) :
    coeffsOfValues pt N ℓ (interpF pt J u) = c := by
  refine coeffs_unique hadd hpt hℓ _ c fun j _ => ?_
  have hdeg : (encPoly pt c).degree < J.card := by
    rw [hJc]; exact mem_degreeLT.1 (encPoly_mem hpt (Nat.pow_le_pow_right two_pos hℓ) c)
  have he : ∀ i, encN pt c i = (encPoly pt c).eval (algebraMap L M (pt i)) := fun i =>
    (encPoly_eval pt (i + 1) _ c ⟨i, by (clear * -; omega)⟩).symm
  rw [interpF_congr pt J hu, funext he, interpF_eq hJ hdeg]

end Twin
section Bfly

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **One butterfly level** `l`: in each block of `2^(l+1)` at `base`, the halves' coefficients
`u` (low) and `w` (high) merge into `u − α (w − u)` (low) and `w − u` (high), with
`α = Ŵ_l(pt (s₀ + base))` (`coeffsAt`'s step). -/
def bflyLevel (pt : ℕ → L) (N s0 l : ℕ) (A : ℕ → M) (i : ℕ) : M :=
  let base := i / 2 ^ (l + 1) * 2 ^ (l + 1)
  let x := i % 2 ^ (l + 1)
  let u := A (base + x % 2 ^ l)
  let w := A (base + 2 ^ l + x % 2 ^ l)
  let α := algebraMap L M (wAt pt N l (s0 + base))
  if x < 2 ^ l then u - α * (w - u) else w - u

/-- **The iteration**: levels `0, …, ℓ − 1`. -/
def bflyRun (pt : ℕ → L) (N s0 : ℕ) : ℕ → (ℕ → M) → ℕ → M
  | 0, A => A
  | l + 1, A => bflyLevel pt N s0 l (bflyRun pt N s0 l A)

/-- **The block invariant**: after `l` levels, block `b` holds `coeffsAt` of its coset. -/
theorem bflyRun_block (pt : ℕ → L) (N s0 : ℕ) (y : ℕ → M) :
    ∀ l b x, x < 2 ^ l → bflyRun pt N s0 l y (b * 2 ^ l + x) =
      coeffsAt pt N l (s0 + b * 2 ^ l) (fun j => y (b * 2 ^ l + j)) x := by
  intro l
  induction l with
  | zero =>
    intro b x hx
    obtain rfl : x = 0 := by simpa using hx
    simp [bflyRun, coeffsAt]
  | succ l ih =>
    intro b x hx
    have hp : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ l := by positivity
    have hdiv : (b * 2 ^ (l + 1) + x) / 2 ^ (l + 1) = b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hx,
        Nat.zero_add]
    have hmod : (b * 2 ^ (l + 1) + x) % 2 ^ (l + 1) = x := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
    have hu := ih (2 * b) (x % 2 ^ l) (Nat.mod_lt _ hpos)
    have hw := ih (2 * b + 1) (x % 2 ^ l) (Nat.mod_lt _ hpos)
    have e1 : 2 * b * 2 ^ l = b * 2 ^ (l + 1) := by rw [hp]; ring
    have e2 : (2 * b + 1) * 2 ^ l = b * 2 ^ (l + 1) + 2 ^ l := by rw [hp]; ring
    rw [e1] at hu
    rw [e2] at hw
    simp only [bflyRun, bflyLevel, hdiv, hmod, coeffsAt]
    rw [hu, hw]
    have hY : (fun j => y (b * 2 ^ (l + 1) + 2 ^ l + j)) =
        fun j => (fun j => y (b * 2 ^ (l + 1) + j)) (2 ^ l + j) := by
      funext j; rw [Nat.add_assoc]
    rw [hY, ← Nat.add_assoc]
    by_cases hx' : x < 2 ^ l
    · rw [if_pos hx', if_pos hx', Nat.mod_eq_of_lt hx']
    · rw [if_neg hx', if_neg hx', show x % 2 ^ l = x - 2 ^ l by
        rw [Nat.mod_eq_sub_mod (by (clear * - hmod e2 hx'; omega)), Nat.mod_eq_of_lt (by (clear * - hx hmod e2 hx'; omega))]]

/-- **The iteration is `coeffsAt`** on the array's first `2^ℓ` entries. -/
theorem bflyRun_eq (pt : ℕ → L) (N s0 ℓ : ℕ) (y : ℕ → M) {i : ℕ} (hi : i < 2 ^ ℓ) :
    bflyRun pt N s0 ℓ y i = coeffsAt pt N ℓ s0 y i := by
  simpa using bflyRun_block pt N s0 y ℓ 0 i hi

end Bfly

/-! ## The pure form -/

section Pure

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **On `J`, the interpolation returns the value.** -/
theorem interpF_self {pt : ℕ → L} {J : Finset ℕ} (hJ : Set.InjOn pt J) (y : ℕ → M) {s : ℕ}
    (hs : s ∈ J) : interpF pt J y s = y s := by
  unfold interpF
  rw [Finset.sum_eq_single s]
  · rw [Finset.prod_eq_one, mul_one]
    intro m hm
    obtain ⟨hne, hmJ⟩ := Finset.mem_erase.1 hm
    have : algebraMap L M (pt s) - algebraMap L M (pt m) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hne (hJ hmJ hs ((algebraMap L M).injective h).symm)
    exact div_self this
  · intro i hi hne
    rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨Ne.symm hne, hs⟩) (by simp), mul_zero]
  · intro h; exact absurd hs h

/-- **Off `J`, the interpolation is barycentric**: `ℓ(s) · Σ_i y i · w_i (pt s − pt i)⁻¹`. -/
theorem interpF_bary {pt : ℕ → L} {J : Finset ℕ} {s : ℕ} (hs : ∀ m ∈ J, pt s ≠ pt m)
    (y : ℕ → M) :
    interpF pt J y s = algebraMap L M (∏ m ∈ J, (pt s - pt m)) *
      ∑ i ∈ J, y i * algebraMap L M ((∏ m ∈ J.erase i, (pt i - pt m))⁻¹ * (pt s - pt i)⁻¹) := by
  unfold interpF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsi : pt s - pt i ≠ 0 := sub_ne_zero.2 (hs i hi)
  have hl : ∏ m ∈ J, (pt s - pt m) = (pt s - pt i) * ∏ m ∈ J.erase i, (pt s - pt m) :=
    (Finset.mul_prod_erase J (fun m => pt s - pt m) hi).symm
  have e : ∏ m ∈ J.erase i, (algebraMap L M (pt s) - algebraMap L M (pt m)) /
      (algebraMap L M (pt i) - algebraMap L M (pt m)) =
      algebraMap L M (∏ m ∈ J.erase i, (pt s - pt m) / (pt i - pt m)) := by
    rw [map_prod]; simp [map_sub, map_div₀]
  rw [e, Finset.prod_div_distrib, hl]
  rw [mul_left_comm, ← map_mul]
  congr 2
  field_simp

end Pure

/-- `b·2^k + j = b·2^k ⊕ j` for `j < 2^k`. -/
theorem mul_two_pow_add_eq_xor {b k j : ℕ} (hj : j < 2 ^ k) : b * 2 ^ k + j = b * 2 ^ k ^^^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hj, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases h : i < k
  · simp [h, show ¬ (k ≤ i) by (clear * - h; omega)]
  · rw [if_neg h, Nat.testBit_lt_two_pow (hj.trans_le (Nat.pow_le_pow_right (by norm_num)
      (by (clear * - h; omega))))]
    simp [show k ≤ i by (clear * - h; omega)]

/-- `pt` is additive on an aligned block: `pt (b·2^k + j) = pt (b·2^k) + pt j` (`j < 2^k`). -/
theorem pt_block {L : Type*} [Field L] {pt : ℕ → L} (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    {b k j : ℕ} (hj : j < 2 ^ k) : pt (b * 2 ^ k + j) = pt (b * 2 ^ k) + pt j := by
  rw [mul_two_pow_add_eq_xor hj, hadd]

section Fwd

variable {L : Type*} [Field L] [CharP L 2] {M : Type*} [Field M] [Algebra L M]

/-- **One forward level** `l`: in each block of `2^(l+1)` at `base`, the halves `u` (low) and
`w` (high) become `u + α w` (low) and `u + α w + w` (high), `α = Ŵ_l(pt base)` (`bflyLevel`'s
inverse). -/
def fwdLevel (pt : ℕ → L) (N : ℕ) (l : ℕ) (A : ℕ → M) (i : ℕ) : M :=
  let base := i / 2 ^ (l + 1) * 2 ^ (l + 1)
  let x := i % 2 ^ (l + 1)
  let u := A (base + x % 2 ^ l)
  let w := A (base + 2 ^ l + x % 2 ^ l)
  let α := algebraMap L M (wAt pt N l base)
  if x < 2 ^ l then u + α * w else u + α * w + w

/-- **The forward iteration**: levels `ℓ − 1, ℓ − 2, …, 0`. -/
def fwdRun (pt : ℕ → L) (N : ℕ) : ℕ → (ℕ → M) → ℕ → M
  | 0, A => A
  | l + 1, A => fwdRun pt N l (fwdLevel pt N l A)

/-- `Ŵ_ℓ` on the block `b` of size `2^(ℓ+1)`: `Ŵ_ℓ(pt(b·2^(ℓ+1) + j))` is `α` on the low half
and `α + 1` on the high half. -/
theorem normW_block {pt : ℕ → L} {N : ℕ} (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ b j : ℕ} (hN : (b + 1) * 2 ^ (ℓ + 1) ≤ 2 ^ N)
    (hj : j < 2 ^ (ℓ + 1)) :
    (normW pt ℓ).eval (pt (b * 2 ^ (ℓ + 1) + j)) =
      wAt pt N ℓ (b * 2 ^ (ℓ + 1)) + if j < 2 ^ ℓ then 0 else 1 := by
  have hℓ : ℓ < N := by
    by_contra h
    have : 2 ^ (N + 1) ≤ 2 ^ (ℓ + 1) := Nat.pow_le_pow_right (by norm_num) (by (clear * - h; omega))
    have h2 : 2 ^ (ℓ + 1) ≤ (b + 1) * 2 ^ (ℓ + 1) := Nat.le_mul_of_pos_left _ (by (clear * -; omega))
    have h3 : 2 ^ N < 2 ^ (N + 1) := Nat.pow_lt_pow_right (by norm_num) (by (clear * -; omega))
    (clear * - hN this h2 h3; omega)
  have hb : b * 2 ^ (ℓ + 1) < 2 ^ N := by
    have : 0 < 2 ^ (ℓ + 1) := by positivity
    nlinarith
  rw [pt_block hadd hj, normW_add hadd, wAt_eq hadd hpt hℓ hb]
  congr 1
  split_ifs with h
  · exact normW_eval_lt pt h
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
    rw [two_pow_add_eq_xor (show j' < 2 ^ ℓ by (clear * - hj; omega)), hadd, normW_add hadd,
      normW_eval_lt pt (show j' < 2 ^ ℓ by (clear * - hj; omega)), add_zero]
    exact normW_eval_self hpt hℓ

/-- **The block invariant**: after the levels `ℓ − 1, …, 0`, position `j` of block `b` holds the
value at `pt(b·2^ℓ + j)` of the block's coefficients. -/
theorem fwdRun_block {pt : ℕ → L} {N : ℕ} (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) :
    ∀ (ℓ : ℕ) (A : ℕ → M) (b j : ℕ), j < 2 ^ ℓ → (b + 1) * 2 ^ ℓ ≤ 2 ^ N →
    fwdRun pt N ℓ A (b * 2 ^ ℓ + j) = ∑ x ∈ range (2 ^ ℓ),
      A (b * 2 ^ ℓ + x) * algebraMap L M ((novelX pt x).eval (pt (b * 2 ^ ℓ + j))) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro A b j hj _
    obtain rfl : j = 0 := by simpa using hj
    simp [fwdRun, novelX, bitProd, bitSel]
  | succ ℓ ih =>
    intro A b j hj hN
    have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ ℓ := by positivity
    -- the level's value at the two halves
    have hval : ∀ x < 2 ^ ℓ, ∀ e < 2, fwdLevel pt N ℓ A ((2 * b + e) * 2 ^ ℓ + x) =
        A (b * 2 ^ (ℓ + 1) + x) + algebraMap L M (wAt pt N ℓ (b * 2 ^ (ℓ + 1))) *
          A (b * 2 ^ (ℓ + 1) + 2 ^ ℓ + x) + if e = 0 then 0 else A (b * 2 ^ (ℓ + 1) + 2 ^ ℓ + x) := by
      intro x hx e he
      have hi : (2 * b + e) * 2 ^ ℓ + x = b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x) := by rw [hp]; ring
      have hlt : e * 2 ^ ℓ + x < 2 ^ (ℓ + 1) := by
        rw [hp]; interval_cases e <;> (clear * - hx hi; omega)
      have hdiv : (b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x)) / 2 ^ (ℓ + 1) = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt,
          Nat.zero_add]
      have hmod : (b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x)) % 2 ^ (ℓ + 1) = e * 2 ^ ℓ + x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
      have hxm : (e * 2 ^ ℓ + x) % 2 ^ ℓ = x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rw [hi, fwdLevel]
      simp only [hdiv, hmod, hxm]
      interval_cases e
      · simp [hx]
      · rw [if_neg (by (clear * - hi hmod hxm; omega)), if_neg (by (clear * -; omega))]
    -- the target, split by the top coefficient bit
    have hN' : (2 * b + 1 + 1) * 2 ^ ℓ ≤ 2 ^ N := by
      have : (2 * b + 1 + 1) * 2 ^ ℓ = (b + 1) * 2 ^ (ℓ + 1) := by rw [hp]; ring
      (clear * - hN this; omega)
    have key : ∀ e < 2, ∀ j' < 2 ^ ℓ, j = e * 2 ^ ℓ + j' →
        fwdRun pt N (ℓ + 1) A (b * 2 ^ (ℓ + 1) + j) = ∑ x ∈ range (2 ^ (ℓ + 1)),
          A (b * 2 ^ (ℓ + 1) + x) * algebraMap L M ((novelX pt x).eval (pt (b * 2 ^ (ℓ + 1) + j))) := by
      intro e he j' hj' hjj
      have hpos2 : b * 2 ^ (ℓ + 1) + j = (2 * b + e) * 2 ^ ℓ + j' := by rw [hjj, hp]; ring
      rw [fwdRun, hpos2, ih (fwdLevel pt N ℓ A) (2 * b + e) j' hj' (by
        have : (2 * b + e + 1) * 2 ^ ℓ ≤ (2 * b + 1 + 1) * 2 ^ ℓ :=
          Nat.mul_le_mul_right _ (by (clear * - he; omega))
        (clear * - hN' this; omega))]
      rw [← hpos2, sum_novel_succ, normW_block hadd hpt (by rwa [show (b + 1) * 2 ^ (ℓ + 1) =
        (2 * b + 1 + 1) * 2 ^ ℓ by rw [hp]; ring]) hj]
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      rw [hval x hx' e he]
      have hjlt : (j < 2 ^ ℓ) ↔ e = 0 := by
        constructor
        · intro h; by_contra h'; have : e = 1 := by (clear * - he h'; omega)
          subst this; (clear * - h hjj; omega)
        · intro h; subst h; (clear * - hj' hjj; omega)
      by_cases h0 : e = 0
      · rw [if_pos h0, if_pos (hjlt.2 h0), Nat.add_assoc, add_zero, add_zero]; ring
      · rw [if_neg h0, if_neg (fun h => h0 (hjlt.1 h)), Nat.add_assoc, map_add, map_one]; ring
    by_cases hlo : j < 2 ^ ℓ
    · exact key 0 (by norm_num) j hlo (by ring)
    · exact key 1 (by norm_num) (j - 2 ^ ℓ) (by rw [hp] at hj; (clear * - hj hlo; omega)) (by (clear * - hlo; omega))

/-- **The forward run is `Enc`**: on a message `c` of `2^m` coefficients zero-padded to `2^n`
(`m ≤ n ≤ N`), the `n` forward levels give `encN pt c j` at every position `j < 2^n`. -/
theorem fwdRun_enc {pt : ℕ → L} {N : ℕ} (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ N)
    (c : Fin (2 ^ m) → M)
    (A : ℕ → M) (hA : ∀ x, A x = if h : x < 2 ^ m then c ⟨x, h⟩ else 0) {j : ℕ} (hj : j < 2 ^ n) :
    fwdRun pt N n A j = encN pt c j := by
  have hnN : 2 ^ n ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hn
  have hN : (0 + 1) * 2 ^ n ≤ 2 ^ N := by (clear * - hnN; omega)
  have h := fwdRun_block hadd hpt n A 0 j hj hN
  simp only [Nat.zero_mul, Nat.zero_add] at h
  have hm : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hmn
  rw [h, encN, ← sum_range_add_sum_Ico _ hm, sum_eq_zero (s := Ico _ _) (fun x hx => by
      rw [hA x, dif_neg (by have := (mem_Ico.1 hx).1; (clear * - this; omega)), zero_mul]), add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun x => A x * algebraMap L M ((novelX pt x).eval (pt j)))]
  exact sum_congr rfl fun x _ => by rw [hA x, dif_pos x.2]

end Fwd

end Lvm.Nb
end
-- ===== end of `LvmXEnc` =====

/-!
# Decoding `C_rec`: the pure specification and its correctness

`C_rec` (BLUEPRINT §3.1, §11 A11) commits `2^19` words of `K = BF64` as 64 lane blocks ("rows")
of `k = 2^13` novel-basis coefficients; row `l` is words `l·2^13 + v`, `v < 2^13`. Its codeword
has `n₀ = 2^15` positions (rate `1/4`): position `q` is the point `x_q = K.ofBits q` (`ptK q`), and
the leaf at `q` holds 64 words, **leaf word `t` = row `63 − t`** (`rowW`). The extractor reads a
word `wd` (`wd q t` = leaf word `t` at position `q`; a missing leaf reads as zeros, as in WP-5's
`wordOf`) and decodes it with the fold challenges `α ∈ E^6` and the final `f₁` (`2^13` `E`
coefficients) of the proof:

* `foldAt α wd q = Σ_{l<64} eq(α, l)·w[l, q]`, `eq(α, l) = Π_i (l_i ? α_i : 1 − α_i)` (bit 0
  first: the first fold challenge is on the lowest lane bit, WP-0);
* `enc0 f₁ q = Σ_{v<2^13} f₁(v)·X_v(x_q)` (`Enc₀`, leanVM's novel-basis encoder);
* `agreeL`: the positions `q < 2^15`, increasing, with `foldAt α wd q = enc0 f₁ q`;
  `selJ`: its first `2^13`;
* `decWord i`: row `l = i / 2^13`, interpolated on `selJ` at the points `x_s`, `s < 2^13`
  (`interpF`), then converted to novel-basis coefficients by the inverse additive NTT
  (`coeffsAt`); `decWord i` is coefficient `i % 2^13`;
* **`decodeRec wd α f₁`**: `none` if fewer than `2^13` positions agree, else the `2^19` words
  `decWord 0, …, decWord (2^19 − 1)`.

## Correctness (`decodeRec_correct`, what WP-14 consumes)

Let `msg` be a message (`2^19` words) with codeword `cwRec msg` (row `l` = `Enc(row l of msg)`).
If

* (`hclose`) at least `2^13` positions agree with `cwRec msg` on all 64 rows (WP-6: in the UD regime
  the close codeword has `udThr 13 2 = 20480 ≥ 2^13` such positions, `decodeRec_correct_ud`),
* (`hf`) `f₁` is the fold of `msg` by `α`: `f₁(v) = Σ_l eq(α, l)·msg(l·2^13 + v)`,
* (`hluck`) the luck event fails: every position where the fold of `wd` agrees with `Enc₀(f₁)`
  agrees with `cwRec msg` on all rows (WP-6's `Ud.card_foldAllLuck_le` prices its complement),

then `decodeRec wd α f₁ = some [msg 0, …, msg (2^19 − 1)]`. Proof: the agreement set contains the
close positions (`Enc₀` is linear, so `fold(cwRec msg) = Enc₀(f₁)`), so it has `≥ 2^13` members;
it is contained in them (`hluck`); interpolation on `2^13` agreeing points and the inverse NTT
return the message (`Lvm.Nb.decode_row`).

## Equality with leanVM's encoder

`lvNovelAt` is leanVM's `novelAt` (`Protocol/Whir/NovelBasis.lean`, with `Subspace.lean`'s
`vanishingAt`, `normVanishingAt`, `basisVec`), transcribed; **`nbAt_eq_lvNovelAt`**: `X_v(x_q)`
here is `novelAt v (K.ofBits q)` there, so `enc0` and `cwRec` are leanVM's `enc`/`encK` at `κ = 13`,
`R = 2` (up to the reindexing `bitsToNat` of cube points). WP-7's `LvmNovelBasis` ports the same
definitions; the identification of the two copies is a later obligation (definitional when they
match leanVM's text).
-/

namespace Lvm.X

open Polynomial Finset Lvm.Nb CompPoly.Extension BF64

/-! ## The domain -/

/-- **The domain point** of index `j`: the `K` word whose bit `c` is the coefficient of `x^c`
(leanVM's `K.ofBits`). -/
def ptK (j : ℕ) : BF64 := BF64.ofBitVec (BitVec.ofNat 64 j)

theorem ptK_xor (a b : ℕ) : ptK (a ^^^ b) = ptK a + ptK b := by
  simp only [ptK, BitVec.ofNat_xor]; rfl

theorem ptK_zero : ptK 0 = 0 := rfl

theorem ptK_injOn64 : Set.InjOn ptK (Set.Iio (2 ^ 64)) := by
  intro a ha b hb h
  have h' := congrArg (fun x : BF64 => (BF64.toBitVec x).toNat) h
  simp only [ptK, BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat] at h'
  rwa [Nat.mod_eq_of_lt (Set.mem_Iio.1 ha), Nat.mod_eq_of_lt (Set.mem_Iio.1 hb)] at h'

/-- `ptK` is injective below `2^N` for `N ≤ 64`. -/
theorem ptK_injOn {N : ℕ} (hN : N ≤ 64) : Set.InjOn ptK (Set.Iio (2 ^ N)) := fun a ha b hb h =>
  ptK_injOn64 (Set.mem_Iio.2 ((Set.mem_Iio.1 ha).trans_le (Nat.pow_le_pow_right (by norm_num) hN)))
    (Set.mem_Iio.2 ((Set.mem_Iio.1 hb).trans_le (Nat.pow_le_pow_right (by norm_num) hN))) h

/-- The table size of the decoder: points below `2^15`. -/
abbrev nLog : ℕ := 15

theorem ptK_injOn15 : Set.InjOn ptK (Set.Iio (2 ^ nLog)) := ptK_injOn (by decide)

/-! ## The objects of the decoder -/

/-- `K` inside `E`. -/
abbrev ofK (a : BF64) : Ext3 := algebraMap BF64 Ext3 a

/-- `X_v(x_q)`: the novel basis polynomial `v` at the point of position `q`. -/
noncomputable def nbAt (v q : ℕ) : BF64 := (novelX ptK v).eval (ptK q)

/-- **The `K`-codeword of a message** (`2^19` words): row `l` at position `q` is
`Enc(msg(l·2^13 + ·))[q] = Σ_{v<2^13} msg(l·2^13 + v)·X_v(x_q)`. -/
noncomputable def cwRec (msg : ℕ → BF64) (l q : ℕ) : BF64 :=
  ∑ v ∈ range (2 ^ 13), msg (l * 2 ^ 13 + v) * nbAt v q

/-- **`Enc₀`** of the final message `f₁` (`2^13` `E` coefficients) at position `q`. -/
noncomputable def enc0 (f₁ : ℕ → Ext3) (q : ℕ) : Ext3 :=
  ∑ v ∈ range (2 ^ 13), f₁ v * ofK (nbAt v q)

/-- Row `l` (lane block `l`) of the read word at position `q`: leaf word `63 − l`. -/
def rowW (wd : ℕ → ℕ → BF64) (l q : ℕ) : BF64 := wd q (63 - l)

/-- `eq(α, l) = Π_{i<6} (l_i ? α_i : 1 − α_i)`, bit 0 of the lane index first. -/
def eqA (α : ℕ → Ext3) (l : ℕ) : Ext3 := eqBits α 6 l

/-- **The fold** of the read word at position `q`: `Σ_{l<64} eq(α, l)·w[l, q]`. -/
def foldAt (α : ℕ → Ext3) (wd : ℕ → ℕ → BF64) (q : ℕ) : Ext3 :=
  ∑ l ∈ range 64, eqA α l * ofK (rowW wd l q)

/-- **The agreement list**: the positions `q < 2^15`, increasing, where the fold agrees with
`Enc₀(f₁)`. -/
noncomputable def agreeL (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) : List ℕ :=
  (List.range (2 ^ 15)).filter fun q => decide (foldAt α wd q = enc0 f₁ q)

/-- The interpolation positions: the first `2^13` of the agreement list. -/
noncomputable def selJ (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) : List ℕ :=
  (agreeL wd α f₁).take (2 ^ 13)

/-- **Word `i` of the decoded message**: row `i / 2^13` interpolated on `selJ` at the points
`x_s`, `s < 2^13`, then coefficient `i % 2^13` of the inverse additive NTT. -/
noncomputable def decWord (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) (i : ℕ) : BF64 :=
  coeffsAt ptK nLog 13 0 (interpF ptK (selJ wd α f₁).toFinset (rowW wd (i / 2 ^ 13))) (i % 2 ^ 13)

/-- **The decoder of `C_rec`**: `none` when fewer than `2^13` positions agree, else the `2^19`
message words. -/
noncomputable def decodeRec (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) : Option (List BF64) :=
  if 2 ^ 13 ≤ (agreeL wd α f₁).length then
    some ((List.range (2 ^ 19)).map (decWord wd α f₁))
  else none

/-! ## Correctness -/

open Classical in
/-- The positions where the read word agrees with a codeword on all rows. -/
noncomputable def closeSet (wd : ℕ → ℕ → BF64) (msg : ℕ → BF64) : Finset ℕ :=
  (range (2 ^ 15)).filter fun q => ∀ l < 64, rowW wd l q = cwRec msg l q

/-- `cwRec` is `Enc` of the row (FR's `encN`). -/
theorem cwRec_eq_encN (msg : ℕ → BF64) (l q : ℕ) :
    cwRec msg l q = encN ptK (fun x : Fin (2 ^ 13) => msg (l * 2 ^ 13 + x)) q := by
  rw [cwRec, encN, ← Fin.sum_univ_eq_sum_range (fun v => msg (l * 2 ^ 13 + v) * nbAt v q)]
  rfl

/-- **`Enc₀` is linear**: the fold of the codeword is `Enc₀` of the folded message. -/
theorem fold_cwRec (α : ℕ → Ext3) (msg : ℕ → BF64) (q : ℕ) :
    ∑ l ∈ range 64, eqA α l * ofK (cwRec msg l q) =
      enc0 (fun v => ∑ l ∈ range 64, eqA α l * ofK (msg (l * 2 ^ 13 + v))) q := by
  simp only [cwRec, enc0, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem nodup_agreeL (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) : (agreeL wd α f₁).Nodup :=
  List.nodup_range.filter _

theorem mem_agreeL {wd : ℕ → ℕ → BF64} {α f₁ : ℕ → Ext3} {q : ℕ} :
    q ∈ agreeL wd α f₁ ↔ q < 2 ^ 15 ∧ foldAt α wd q = enc0 f₁ q := by
  simp [agreeL]

/-- **Correctness of the decoder** (BLUEPRINT §6.2): close, folded, and not lucky ⇒ the message. -/
theorem decodeRec_correct (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) (msg : ℕ → BF64)
    (hclose : 2 ^ 13 ≤ (closeSet wd msg).card)
    (hf : ∀ v < 2 ^ 13, f₁ v = ∑ l ∈ range 64, eqA α l * ofK (msg (l * 2 ^ 13 + v)))
    (hluck : ∀ q < 2 ^ 15, foldAt α wd q = enc0 f₁ q → ∀ l < 64, rowW wd l q = cwRec msg l q) :
    decodeRec wd α f₁ = some ((List.range (2 ^ 19)).map msg) := by
  -- the agreement set contains the close set
  have henc : ∀ q, enc0 f₁ q =
      enc0 (fun v => ∑ l ∈ range 64, eqA α l * ofK (msg (l * 2 ^ 13 + v))) q := fun q =>
    Finset.sum_congr rfl fun v hv => by rw [hf v (mem_range.1 hv)]
  have hsub : closeSet wd msg ⊆ (agreeL wd α f₁).toFinset := by
    intro q hq
    simp only [closeSet, mem_filter, mem_range] at hq
    rw [List.mem_toFinset, mem_agreeL]
    refine ⟨hq.1, ?_⟩
    rw [henc, ← fold_cwRec, foldAt]
    exact Finset.sum_congr rfl fun l hl => by rw [hq.2 l (mem_range.1 hl)]
  have hlen : 2 ^ 13 ≤ (agreeL wd α f₁).length := by
    have := (card_le_card hsub).trans (List.toFinset_card_le _)
    omega
  rw [decodeRec, if_pos hlen]
  refine congrArg some (List.map_congr_left fun i hi => ?_)
  have hi' := List.mem_range.1 hi
  -- the interpolation positions
  set J := (selJ wd α f₁).toFinset with hJ
  have hJsub : ∀ q ∈ J, q ∈ agreeL wd α f₁ := fun q hq =>
    List.mem_of_mem_take (List.mem_toFinset.1 hq)
  have hJcard : J.card = 2 ^ 13 := by
    rw [hJ, selJ, List.toFinset_card_of_nodup
      ((nodup_agreeL wd α f₁).sublist (List.take_sublist _ _)), List.length_take,
      Nat.min_eq_left hlen]
  have hJlt : ∀ q ∈ J, q < 2 ^ nLog := fun q hq => (mem_agreeL.1 (hJsub q hq)).1
  set l := i / 2 ^ 13 with hl
  have hl64 : l < 64 := by rw [hl]; omega
  have hrow : ∀ q ∈ J, rowW wd l q = encN ptK (fun x : Fin (2 ^ 13) => msg (l * 2 ^ 13 + x)) q :=
    fun q hq => by
      obtain ⟨hq15, hfq⟩ := mem_agreeL.1 (hJsub q hq)
      rw [← cwRec_eq_encN]; exact hluck q hq15 hfq l hl64
  have hdec := decode_row ptK_xor ptK_injOn15 (ℓ := 13) (by decide)
    (fun a ha b hb h => ptK_injOn15 (hJlt a ha) (hJlt b hb) h) hJcard _ (rowW wd l) hrow
  have hv : i % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by positivity)
  have := congrFun hdec ⟨i % 2 ^ 13, hv⟩
  simp only [coeffsOfValues] at this
  rw [decWord, ← hl, this]
  show msg (l * 2 ^ 13 + i % 2 ^ 13) = msg i
  rw [hl, Nat.div_add_mod' i (2 ^ 13)]

end Lvm.X
