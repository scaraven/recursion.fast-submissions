-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/NovelBasis.lean` (formal rev 40f877dc) as `LvmNovelBasis` for lvm (WP-7): `ReedSolomon.code`/`evalOnPoints` are LvmRS's `rsCode`/`evalOnPoints`; one 4.34.1 drift fix in `enc_eq_evalOnPoints` (WP-2).
/-
  LeanVM.Protocol.Whir.NovelBasis

  The novel polynomial basis `X_j = ∏_i Ŵ_i^{j_i}`, the evaluation domain `D_{κ,R}`, and the
  encoder `Enc_{κ,R}` of leanVM's binary Reed-Solomon code, with its range: exactly the
  Reed-Solomon code of degree `2^κ` on `D_{κ,R}`.
-/
import LvmRS
import LvmFieldFacts
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.Basic

-- ===== merged from `LvmSubspace` (GOLF module merge: `LvmSubspace.lean` is now a stub importing `LvmNovelBasis`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Subspace.lean` (formal rev 40f877dc) as `LvmSubspace` for lvm (WP-7).
/-
  LeanVM.Protocol.Whir.Subspace

  The F₂-subspaces `U_i` of `K` spanned by the first `i` powers of `x`, their vanishing
  polynomials `W_i`, and the normalized `Ŵ_i = W_i / W_i(e_i)`: the subspace polynomials of
  leanVM's binary Reed-Solomon code.
-/

/-!
# Subspace vanishing polynomials

Annex D ("Novel polynomial basis and additive NTT", `app:ntt`; Annex B §B.6 until `127510d1`) of
the leanVM specification, `doc/leanvm/body/d-novel-basis.tex:2-27` at leanVM pin
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`. The definitions are the Annex's, and the
lemma is its Lemma `lem:subspace`, parts (i) and (ii) proved here; its first sentence, added at
`127510d1` (each `W_i` has only the monomials `X^(2^j)`), is not formalized.

* `basisVec c` is `e_c = x^c`, the word `K.ofBits (2^c)`; `e_0 = 1`.
* `subspace i` is `U_i = ⟨e_0, …, e_{i-1}⟩_{F₂}`, the words `K.ofBits v` for `v < 2^i`
  (`ofBits_eq_sum`: the word with bits `v` is `Σ_c v_c e_c`). Below `2^64` the words are distinct
  (`ofBits_injOn`), so `|U_i| = 2^i` for `i ≤ 64`.
* `vanishing i` is `W_i(X) = ∏_{u ∈ U_i} (X + u)`, written as the product over `v < 2^i`
  (`vanishing_eq_prod_subspace` for `i ≤ 64`); `vanishingAt i a` is its computable evaluation.
  Monic of degree `2^i` (`vanishing_monic`, `natDegree_vanishing`), with roots exactly `U_i`
  (`vanishingAt_eq_zero_iff`).
* Lemma `lem:subspace`: (i) `W_{i+1} = W_i·(W_i + W_i(e_i))` (`vanishing_succ`) with
  `W_i(e_i) ≠ 0` for `i < 64` (`vanishingAt_basisVec_ne_zero`); (ii) `W_i(X + Y) = W_i(X) + W_i(Y)`
  in `K[X, Y]` (`vanishing_add_bivariate`, from `aeval_vanishing_add` in any commutative
  `K`-algebra), `W_i(X + a) = W_i(X) + W_i(a)` in `K[X]` (`vanishing_comp_add`), so `W_i` is
  additive on `K` (`vanishingAt_add`).
* `normVanishing i` is `Ŵ_i = W_i / W_i(e_i)`, with `Ŵ_i(e_i) = 1` (`normVanishingAt_basisVec`),
  degree `2^i` for `i < 64` (`natDegree_normVanishing`), additive, and `Ŵ_0 = X`
  (`normVanishing_zero`).

## Wrong readings excluded

* `W_i` vanishes on the *subspace* `U_i`, not on the first `2^i` integers read as field elements
  under some other encoding: `K.ofBits v` is the word whose bit `c` is the coefficient of `x^c`.
* The recurrence (i) and the identity (ii) hold for every `i`; only `W_i(e_i) ≠ 0` needs
  `i < 64`. At `i ≥ 64` the word `2^i` wraps to `0`, `e_i = 0`, and `Ŵ_i` is `0` by Lean's
  convention `0⁻¹ = 0`.
-/

namespace LeanVM.Protocol.Whir

open LeanVM.Parameters Polynomial

section

/-! ## Words and the basis `e_c` -/

/-- `e_c = x^c`, the word with the single bit `c`. -/
def basisVec (c : ℕ) : K := K.ofBits (2 ^ c)

/-- `U_i = ⟨e_0, …, e_{i-1}⟩_{F₂}`, as the words whose bits lie below `i`. -/
def subspace (i : ℕ) : Finset K := (Finset.range (2 ^ i)).image K.ofBits

/-- `e_0 = 1`. -/
theorem basisVec_zero : basisVec 0 = 1 := rfl

/-- `K.ofBits 0 = 0`. -/
@[simp] theorem ofBits_zero : K.ofBits 0 = 0 := rfl

/-- A word below `2^64` is read back exactly. -/
theorem toNat_ofBits {n : ℕ} (hn : n < 2 ^ 64) : (K.ofBits n).toBitVec.toNat = n := by
  simpa [K.ofBits] using hn

/-- Words below `2^64` are distinct field elements. -/
theorem ofBits_injOn : Set.InjOn K.ofBits {n | n < 2 ^ 64} := by
  intro a ha b hb h
  rw [← toNat_ofBits ha, ← toNat_ofBits hb, h]

/-- A word below `2^64` is zero only when it is `0`. -/
theorem ofBits_eq_zero_iff {n : ℕ} (hn : n < 2 ^ 64) : K.ofBits n = 0 ↔ n = 0 :=
  ⟨fun h ↦ ofBits_injOn (show n < 2 ^ 64 from hn) (show 0 < 2 ^ 64 by norm_num) h,
    fun h ↦ h ▸ ofBits_zero⟩

/-- Below `2^i`, adding `2^i` sets a bit that is clear: it is the exclusive or. -/
theorem two_pow_add_eq_xor {i v : ℕ} (hv : v < 2 ^ i) : 2 ^ i + v = 2 ^ i ^^^ v := by
  have h := Nat.two_pow_add_eq_or_of_lt hv 1
  rw [mul_one] at h
  rw [h]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hj : i = j
  · subst hj
    simp [Nat.testBit_lt_two_pow hv]
  · simp [hj]

/-- Sum in `K` is bitwise exclusive or of words. -/
theorem ofBits_xor (a b : ℕ) : K.ofBits (a ^^^ b) = K.ofBits a + K.ofBits b := by
  simp only [K.ofBits, BitVec.ofNat_xor]
  rfl

/-- `x_{2^i + v} = e_i + x_v` for `v < 2^i`: the coset `e_i + U_i`. -/
theorem ofBits_two_pow_add {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits (2 ^ i + v) = basisVec i + K.ofBits v := by
  rw [two_pow_add_eq_xor hv, ofBits_xor, basisVec]

/-- The word with bits `v` is `Σ_c v_c e_c`: `U_i` is the span of `e_0, …, e_{i-1}`. -/
theorem ofBits_eq_sum {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits v = ∑ c ∈ Finset.range i, if v.testBit c then basisVec c else 0 := by
  induction i generalizing v with
  | zero =>
    obtain rfl : v = 0 := by simpa using hv
    simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    by_cases hb : v.testBit i
    · have hlt : v - 2 ^ i < 2 ^ i := by
        have := Nat.ge_two_pow_of_testBit hb
        rw [pow_succ] at hv
        omega
      have hv' : v = 2 ^ i + (v - 2 ^ i) := by
        have := Nat.ge_two_pow_of_testBit hb
        omega
      have hbits : ∀ c < i, v.testBit c = (v - 2 ^ i).testBit c := by
        intro c hc
        conv_lhs => rw [hv']
        exact Nat.testBit_two_pow_add_gt hc _
      have hb' : (2 ^ i + (v - 2 ^ i)).testBit i = true := by rw [← hv']; exact hb
      rw [hv', ofBits_two_pow_add hlt, ih hlt, hb']
      simp only [ite_true]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun c hc ↦ ?_
      rw [← hv', hbits c (Finset.mem_range.mp hc)]
    · have hlt : v < 2 ^ i := by
        by_contra h
        have h1 : 2 ^ i ≤ v := not_lt.mp h
        have : v.testBit i = true := by
          have hv2 : v - 2 ^ i < 2 ^ i := by rw [pow_succ] at hv; omega
          have := Nat.testBit_two_pow_add_eq (v - 2 ^ i) i
          rw [Nat.add_sub_cancel' h1, Nat.testBit_lt_two_pow hv2] at this
          simpa using this
        exact hb this
      simp only [Bool.not_eq_true] at hb
      rw [ih hlt, hb]
      simp

/-! ## The vanishing polynomials -/

/-- `W_i(X) = ∏_{u ∈ U_i} (X + u)`, the product over the words `v < 2^i`. -/
noncomputable def vanishing (i : ℕ) : K[X] := ∏ v ∈ Finset.range (2 ^ i), (X + C (K.ofBits v))

/-- `W_i(a)`, computed from the product. -/
def vanishingAt (i : ℕ) (a : K) : K := ∏ v ∈ Finset.range (2 ^ i), (a + K.ofBits v)

/-- `vanishingAt` evaluates `vanishing`. -/
@[simp] theorem eval_vanishing (i : ℕ) (a : K) : (vanishing i).eval a = vanishingAt i a := by
  simp [vanishing, vanishingAt, eval_prod]

/-- `deg W_i = 2^i`. -/
theorem natDegree_vanishing (i : ℕ) : (vanishing i).natDegree = 2 ^ i := by
  rw [vanishing, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _]
  simp

/-- `W_0 = X`. -/
theorem vanishing_zero : vanishing 0 = X := by simp [vanishing]

/-- The roots of `W_i` are exactly `U_i`. -/
theorem vanishingAt_eq_zero_iff (i : ℕ) (a : K) : vanishingAt i a = 0 ↔ a ∈ subspace i := by
  simp only [vanishingAt, Finset.prod_eq_zero_iff, subspace, Finset.mem_image]
  refine exists_congr fun v ↦ and_congr_right fun _ ↦ ?_
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq, eq_comm]

/-- `W_i(X + e_i)` is the product over the coset `e_i + U_i`, the upper half of `U_{i+1}`. -/
private theorem vanishing_succ_split (i : ℕ) :
    vanishing (i + 1) = vanishing i * (vanishing i).comp (X + C (basisVec i)) := by
  rw [vanishing, pow_succ, mul_two, Finset.prod_range_add, vanishing, prod_comp]
  congr 1
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  rw [ofBits_two_pow_add (Finset.mem_range.mp hv)]
  simp only [add_comp, X_comp, C_comp, C_add]
  ring

/-- `(A + B)(A + B + c) = A(A + c) + B(B + c)` in characteristic two. -/
private theorem char_two_cross (A B c : K[X]) :
    (A + B) * (A + B + c) = A * (A + c) + B * (B + c) := by
  linear_combination (A * B) * (CharTwo.two_eq_zero : (2 : K[X]) = 0)

/-- Lemma `lem:subspace`, jointly: (ii) at `i`, then (i) at `i`. -/
private theorem vanishing_comp_add_and_succ (i : ℕ) :
    (∀ a : K, (vanishing i).comp (X + C a) = vanishing i + C (vanishingAt i a)) ∧
      vanishing (i + 1) =
        vanishing i * (vanishing i + C (vanishingAt i (basisVec i))) := by
  have step : ∀ i, (∀ a : K, (vanishing i).comp (X + C a) = vanishing i + C (vanishingAt i a)) →
      vanishing (i + 1) = vanishing i * (vanishing i + C (vanishingAt i (basisVec i))) := by
    intro i h
    rw [vanishing_succ_split, h]
  induction i with
  | zero =>
    refine ⟨fun a ↦ ?_, step 0 fun a ↦ ?_⟩ <;>
    · simp [vanishing_zero, vanishingAt]
  | succ i ih =>
    have hadd : ∀ a : K,
        (vanishing (i + 1)).comp (X + C a) = vanishing (i + 1) + C (vanishingAt (i + 1) a) := by
      intro a
      rw [← eval_vanishing (i + 1) a, ih.2, mul_comp, add_comp, C_comp, ih.1 a, eval_mul,
        eval_add, eval_C, eval_vanishing, C_mul, C_add]
      exact char_two_cross _ _ _
    exact ⟨hadd, step _ hadd⟩

/-- Lemma `lem:subspace` (ii): `W_i(X + a) = W_i(X) + W_i(a)`, a polynomial identity in `X`. -/
theorem vanishing_comp_add (i : ℕ) (a : K) :
    (vanishing i).comp (X + C a) = vanishing i + C (vanishingAt i a) :=
  (vanishing_comp_add_and_succ i).1 a

/-- Lemma `lem:subspace` (i): `W_{i+1} = W_i·(W_i + W_i(e_i))`. -/
theorem vanishing_succ (i : ℕ) :
    vanishing (i + 1) = vanishing i * (vanishing i + C (vanishingAt i (basisVec i))) :=
  (vanishing_comp_add_and_succ i).2

/-- The recurrence (i), evaluated: `W_{i+1}(a) = W_i(a)^2 + W_i(e_i)·W_i(a)`, the update of the
verifier's `subspace_roots` (`crates/verifier/src/whir.rs:92-104`) and of the prover's `next_s`. -/
theorem vanishingAt_succ (i : ℕ) (a : K) :
    vanishingAt (i + 1) a = vanishingAt i a ^ 2 + vanishingAt i (basisVec i) * vanishingAt i a := by
  rw [← eval_vanishing, vanishing_succ, eval_mul, eval_add, eval_C, eval_vanishing]
  ring

/-- `W_i` is additive on `K`, hence `F₂`-linear. -/
theorem vanishingAt_add (i : ℕ) (a b : K) :
    vanishingAt i (a + b) = vanishingAt i a + vanishingAt i b := by
  have h := congrArg (eval a) (vanishing_comp_add i b)
  rw [eval_comp, eval_add, eval_X, eval_C, eval_add, eval_C, eval_vanishing,
    eval_vanishing] at h
  exact h

/-- `W_i(0) = 0`. -/
@[simp] theorem vanishingAt_zero (i : ℕ) : vanishingAt i 0 = 0 :=
  (vanishingAt_eq_zero_iff i 0).mpr
    (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.two_pow_pos i), ofBits_zero⟩)

/-- Lemma `lem:subspace`: `W_i(e_i) ≠ 0` for `i < 64`, since `e_i ∉ U_i`. -/
theorem vanishingAt_basisVec_ne_zero {i : ℕ} (hi : i < 64) : vanishingAt i (basisVec i) ≠ 0 := by
  rw [vanishingAt]
  refine Finset.prod_ne_zero_iff.mpr fun v hv ↦ ?_
  have hv' := Finset.mem_range.mp hv
  rw [← ofBits_two_pow_add hv']
  have hlt : 2 ^ i + v < 2 ^ 64 := by
    have : 2 ^ (i + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hi
    rw [pow_succ] at this
    omega
  rw [Ne, ofBits_eq_zero_iff hlt]
  have := Nat.two_pow_pos i
  omega

/-! ## The normalized polynomials -/

/-- `Ŵ_i = W_i / W_i(e_i)`. The hat is normalization, not multilinear extension. -/
noncomputable def normVanishing (i : ℕ) : K[X] := C (vanishingAt i (basisVec i))⁻¹ * vanishing i

/-- `Ŵ_i(a)`, computed from the product. -/
def normVanishingAt (i : ℕ) (a : K) : K := vanishingAt i a * (vanishingAt i (basisVec i))⁻¹

/-- `normVanishingAt` evaluates `normVanishing`. -/
@[simp] theorem eval_normVanishing (i : ℕ) (a : K) :
    (normVanishing i).eval a = normVanishingAt i a := by
  rw [normVanishing, normVanishingAt, eval_mul, eval_C, eval_vanishing, mul_comm]

/-- `Ŵ_i(e_i) = 1` for `i < 64`. -/
theorem normVanishingAt_basisVec {i : ℕ} (hi : i < 64) : normVanishingAt i (basisVec i) = 1 :=
  mul_inv_cancel₀ (vanishingAt_basisVec_ne_zero hi)

/-- `deg Ŵ_i = 2^i` for `i < 64`. -/
theorem natDegree_normVanishing {i : ℕ} (hi : i < 64) :
    (normVanishing i).natDegree = 2 ^ i := by
  rw [normVanishing, natDegree_C_mul (inv_ne_zero (vanishingAt_basisVec_ne_zero hi)),
    natDegree_vanishing]

/-- `Ŵ_i ≠ 0` for `i < 64`. -/
theorem normVanishing_ne_zero {i : ℕ} (hi : i < 64) : normVanishing i ≠ 0 := by
  intro h
  have := natDegree_normVanishing hi
  rw [h, natDegree_zero] at this
  exact (Nat.two_pow_pos i).ne this

/-- `Ŵ_i` is additive on `K`. -/
theorem normVanishingAt_add (i : ℕ) (a b : K) :
    normVanishingAt i (a + b) = normVanishingAt i a + normVanishingAt i b := by
  rw [normVanishingAt, normVanishingAt, normVanishingAt, vanishingAt_add, add_mul]

end
end LeanVM.Protocol.Whir
end
-- ===== end of `LvmSubspace` =====

/-!
# The novel basis and the encoder

The leanVM specification at leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`: Annex B §B.2
"Reed-Solomon codes over binary fields" (`sec:binary-rs`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex:87-94`) and Annex D Definition `def:enc`
(`doc/leanvm/body/d-novel-basis.tex:40-46`; in Annex B until `127510d1`). The
definitions are the Annex's and the claims of `def:enc` are proved here.

* Cube points `u : Fin κ → Bool` are read bit `0` first: `bitsToNat u = ⟨u⟩ = Σ_i u_i 2^i`, and
  `bitsEquiv κ : (Fin κ → Bool) ≃ Fin (2^κ)` is the bijection, with inverse
  `j ↦ (i ↦ j.testBit i)`, CompPoly's table indexing.
* `novel j` is `X_j = ∏_i Ŵ_i^{j_i}`, with `deg X_j = j` for `j < 2^64` (`natDegree_novel`), and
  `novelAt j a` its computable evaluation.
* `domain κ R h` is `D_{κ,R} = ⟨e_0, …, e_{κ+R-1}⟩_{F₂} = {x_v = K.ofBits v | v < 2^(κ+R)}`, as an
  embedding `Fin (2^(κ+R)) ↪ E` through `ofK`; it needs `h : κ + R ≤ 64`.
* `enc κ R` is `Enc_{κ,R}`, `g ↦ (Σ_u g(u)·X_⟨u⟩(x_v))_v`, an `E`-linear map; the message is read
  directly as novel-basis coefficients. `encK κ R` is the same sum for a `K`-valued message.

The claims of `def:enc` and §B.2, for `κ + R ≤ 64`:

* `enc_eq_evalOnPoints`: `Enc_{κ,R}(g)` is the evaluation on `D_{κ,R}` of the message polynomial
  `msgPoly κ g = P_g = Σ_u g(u)·X_⟨u⟩`;
* `range_msgPoly`: the `X_j`, `j < 2^κ`, span exactly the polynomials of degree `< 2^κ`;
* `range_enc`: the range of `Enc_{κ,R}` is ArkLib's `rsCode (domain κ R h) (2^κ)`;
* `enc_injective`: `Enc_{κ,R}` is injective;
* `enc_ofK`, `isInK_enc_ofK`: a `K`-valued message gives a `K`-valued word.

The rate `2^-R` is `2^κ / |D_{κ,R}|`; §B.2 assumes `R ≥ 1` (`def:enc` allows `R ≥ 0`), which none
of the statements here needs.

## Wrong readings excluded

* `⟨u⟩` reads `u 0` as the *low* bit. Reading it high bit first is a different encoder (the
  negative test in `LeanVMTests.Protocol.Whir.NovelBasis`).
* No change of basis is applied to the message: `g(u)` is the coefficient of `X_⟨u⟩`, not of the
  monomial `X^⟨u⟩`.
* The domain is the subspace `U_{κ+R}` itself, not a coset of it and not a multiplicative group.
-/

namespace LeanVM.Protocol.Whir

open LeanVM.Parameters Polynomial

section

/-! ## Cube points as integers -/

/-- `⟨u⟩ = Σ_i u_i 2^i`, the integer whose bits are `u`, bit `0` first. -/
def bitsToNat {κ : ℕ} (u : Fin κ → Bool) : ℕ := ∑ i, (u i).toNat * 2 ^ (i : ℕ)

/-- The bijection `u ↦ ⟨u⟩` between cube points and `Fin (2^κ)`. -/
def bitsEquiv (κ : ℕ) : (Fin κ → Bool) ≃ Fin (2 ^ κ) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- `bitsEquiv` sends `u` to `⟨u⟩`. -/
theorem bitsEquiv_val {κ : ℕ} (u : Fin κ → Bool) : (bitsEquiv κ u : ℕ) = bitsToNat u := by
  rw [bitsEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply, bitsToNat]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply]
  cases u i <;> rfl

/-- The inverse of `bitsEquiv` reads the bits of an index. -/
theorem bitsEquiv_symm_apply {κ : ℕ} (j : Fin (2 ^ κ)) (i : Fin κ) :
    (bitsEquiv κ).symm j i = (j : ℕ).testBit i := by
  rw [bitsEquiv, Equiv.symm_trans_apply, Nat.testBit_eq_decide_div_mod_eq]
  simp only [Equiv.arrowCongr_symm, Equiv.symm_symm, Equiv.arrowCongr_apply, Equiv.coe_refl,
    Function.comp_apply, id_eq]
  have h := finFunctionFinEquiv_symm_apply_val j i
  rcases Nat.mod_two_eq_zero_or_one ((j : ℕ) / 2 ^ (i : ℕ)) with h2 | h2
  · have : finFunctionFinEquiv.symm j i = 0 := Fin.ext (by rw [h, h2]; rfl)
    rw [this, h2]
    rfl
  · have : finFunctionFinEquiv.symm j i = 1 := Fin.ext (by rw [h, h2]; rfl)
    rw [this, h2]
    rfl

/-- `⟨u⟩ < 2^κ`. -/
theorem bitsToNat_lt {κ : ℕ} (u : Fin κ → Bool) : bitsToNat u < 2 ^ κ := by
  rw [← bitsEquiv_val]
  exact (bitsEquiv κ u).isLt

/-- Bit `i` of `⟨u⟩` is `u i`. -/
theorem testBit_bitsToNat {κ : ℕ} (u : Fin κ → Bool) (i : Fin κ) :
    (bitsToNat u).testBit i = u i := by
  rw [← bitsEquiv_val, ← bitsEquiv_symm_apply, Equiv.symm_apply_apply]

/-- The bits of `j < 2^κ` read back to `j`. -/
theorem bitsToNat_testBit {κ j : ℕ} (hj : j < 2 ^ κ) :
    bitsToNat (fun i : Fin κ ↦ j.testBit i) = j := by
  have h := bitsEquiv_val ((bitsEquiv κ).symm ⟨j, hj⟩)
  rw [Equiv.apply_symm_apply, show (bitsEquiv κ).symm ⟨j, hj⟩ = fun i : Fin κ ↦ j.testBit i from
    funext fun i ↦ bitsEquiv_symm_apply _ i] at h
  exact h.symm

/-! ## The novel basis -/

/-- The novel basis polynomial `X_j = ∏_i Ŵ_i^{j_i}`, over the 64 bits a word can have. -/
noncomputable def novel (j : ℕ) : K[X] :=
  ∏ i ∈ Finset.range 64, if j.testBit i then normVanishing i else 1

/-- `X_j(a)`, computed from the products. -/
def novelAt (j : ℕ) (a : K) : K :=
  ∏ i ∈ Finset.range 64, if j.testBit i then normVanishingAt i a else 1

/-- `novelAt` evaluates `novel`. -/
@[simp] theorem eval_novel (j : ℕ) (a : K) : (novel j).eval a = novelAt j a := by
  rw [novel, novelAt, eval_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  split <;> simp

/-- On a cube point of dimension `κ ≤ 64` only the first `κ` factors remain. -/
private theorem prod_range_testBit {M : Type*} [CommMonoid M] {κ : ℕ} (hκ : κ ≤ 64)
    (u : Fin κ → Bool) (f : ℕ → M) :
    ∏ i ∈ Finset.range 64, (if (bitsToNat u).testBit i then f i else 1) =
      ∏ i : Fin κ, if u i then f i else 1 := by
  rw [← Finset.prod_subset (Finset.range_subset_range.mpr hκ), Finset.prod_range]
  · exact Finset.prod_congr rfl fun i _ ↦ by rw [testBit_bitsToNat]
  · intro i _ hi
    have hi' : κ ≤ i := not_lt.mp (Finset.mem_range.not.mp hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (bitsToNat_lt u)
      (Nat.pow_le_pow_right (by norm_num) hi'))]
    rfl

/-- `X_⟨u⟩(a) = ∏_{i<κ} Ŵ_i(a)^{u_i}` for a cube point of dimension `κ ≤ 64`. -/
theorem novelAt_bitsToNat {κ : ℕ} (hκ : κ ≤ 64) (u : Fin κ → Bool) (a : K) :
    novelAt (bitsToNat u) a = ∏ i : Fin κ, if u i then normVanishingAt i a else 1 :=
  prod_range_testBit hκ u _

/-- `X_j ≠ 0`. -/
theorem novel_ne_zero (j : ℕ) : novel j ≠ 0 := by
  rw [novel, Finset.prod_ne_zero_iff]
  intro i hi
  split
  · exact normVanishing_ne_zero (Finset.mem_range.mp hi)
  · exact one_ne_zero

/-- `deg X_j = j` for `j < 2^64`: the `X_j`, `j < 2^κ`, are a triangular basis. -/
theorem natDegree_novel {j : ℕ} (hj : j < 2 ^ 64) : (novel j).natDegree = j := by
  rw [novel, natDegree_prod _ _ fun i hi ↦ by
    split
    · exact normVanishing_ne_zero (Finset.mem_range.mp hi)
    · exact one_ne_zero]
  conv_rhs => rw [← bitsToNat_testBit hj]
  rw [bitsToNat, ← Finset.sum_range (fun i ↦ (j.testBit i).toNat * 2 ^ i)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  split
  · rename_i h
    rw [natDegree_normVanishing (Finset.mem_range.mp hi), h]
    simp
  · rename_i h
    simp [h]

/-! ## The domain and the encoder -/

/-- `D_{κ,R} = {x_v = K.ofBits v | v < 2^(κ+R)}` in `E`, for `κ + R ≤ 64`. -/
def domain (κ R : ℕ) (h : κ + R ≤ 64) : Fin (2 ^ (κ + R)) ↪ E where
  toFun v := ofK (K.ofBits v)
  inj' := by
    intro a b hab
    have hle : 2 ^ (κ + R) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) h
    exact Fin.ext (ofBits_injOn (show (a : ℕ) < 2 ^ 64 from lt_of_lt_of_le a.isLt hle)
      (show (b : ℕ) < 2 ^ 64 from lt_of_lt_of_le b.isLt hle) (ofK_injective hab))

/-- `Enc_{κ,R}(g) = (Σ_u g(u)·X_⟨u⟩(x_v))_{v < 2^(κ+R)}`. -/
def enc (κ R : ℕ) : ((Fin κ → Bool) → E) →ₗ[E] (Fin (2 ^ (κ + R)) → E) where
  toFun g v := ∑ u, g u * ofK (novelAt (bitsToNat u) (K.ofBits v))
  map_add' g h := by
    funext v
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c g := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- The defining sum of `enc`. -/
theorem enc_apply (κ R : ℕ) (g : (Fin κ → Bool) → E) (v : Fin (2 ^ (κ + R))) :
    enc κ R g v = ∑ u, g u * ofK (novelAt (bitsToNat u) (K.ofBits v)) := rfl

/-- The encoder on a `K`-valued message. -/
def encK (κ R : ℕ) (g : (Fin κ → Bool) → K) (v : Fin (2 ^ (κ + R))) : K :=
  ∑ u, g u * novelAt (bitsToNat u) (K.ofBits v)

/-- A `K`-valued message gives a `K`-valued word: `encK` lifted. -/
theorem enc_ofK (κ R : ℕ) (g : (Fin κ → Bool) → K) :
    enc κ R (fun u ↦ ofK (g u)) = fun v ↦ ofK (encK κ R g v) := by
  funext v
  rw [enc_apply, encK]
  change _ = algebraMap K E _
  rw [map_sum]
  exact Finset.sum_congr rfl fun u _ ↦ (ofK_mul _ _).symm

/-! ## The message polynomial and the range -/

/-- `X_j` over `E`. -/
noncomputable abbrev novelE (j : ℕ) : E[X] := (novel j).map (algebraMap K E)

/-- `P_g = Σ_u g(u)·X_⟨u⟩`, the polynomial whose evaluations are the codeword. -/
noncomputable def msgPoly (κ : ℕ) : ((Fin κ → Bool) → E) →ₗ[E] E[X] where
  toFun g := ∑ u, g u • novelE (bitsToNat u)
  map_add' g h := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c g := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
    mul_smul]

/-- `Enc_{κ,R}(g)` is `P_g` evaluated on `D_{κ,R}`. -/
theorem enc_eq_evalOnPoints {κ R : ℕ} (h : κ + R ≤ 64) (g : (Fin κ → Bool) → E) :
    enc κ R g = evalOnPoints (domain κ R h) (msgPoly κ g) := by
  funext v
  simp only [enc_apply, evalOnPoints, msgPoly, LinearMap.coe_mk, AddHom.coe_mk,
    eval_finsetSum, eval_smul, smul_eq_mul, domain]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [eval_map]
  change _ = g u * eval₂ (algebraMap K E) (algebraMap K E (K.ofBits (v : ℕ))) (novel (bitsToNat u))
  rw [eval₂_hom, eval_novel]
  rfl

/-- `deg X_⟨u⟩ < 2^κ` for `κ ≤ 64`. -/
private theorem novelE_mem_degreeLT {κ : ℕ} (hκ : κ ≤ 64) (u : Fin κ → Bool) :
    novelE (bitsToNat u) ∈ degreeLT E (2 ^ κ) := by
  have hlt : bitsToNat u < 2 ^ 64 :=
    lt_of_lt_of_le (bitsToNat_lt u) (Nat.pow_le_pow_right (by norm_num) hκ)
  rw [mem_degreeLT]
  refine lt_of_le_of_lt degree_le_natDegree ?_
  rw [natDegree_map, natDegree_novel hlt]
  exact_mod_cast bitsToNat_lt u

/-- `X_⟨u⟩` is the message polynomial of the indicator of `u`. -/
private theorem msgPoly_single {κ : ℕ} (u : Fin κ → Bool) :
    msgPoly κ (Pi.single u 1) = novelE (bitsToNat u) := by
  simp only [msgPoly, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The `X_j`, `j < 2^κ`, span exactly the polynomials of degree `< 2^κ` (for `κ ≤ 64`). -/
theorem range_msgPoly {κ : ℕ} (hκ : κ ≤ 64) :
    LinearMap.range (msgPoly κ) = degreeLT E (2 ^ κ) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact Submodule.sum_mem _ fun u _ ↦ Submodule.smul_mem _ _ (novelE_mem_degreeLT hκ u)
  · suffices H : ∀ n ≤ 2 ^ κ, degreeLT E n ≤ LinearMap.range (msgPoly κ) from H _ le_rfl
    intro n
    induction n with
    | zero =>
      intro _ p hp
      rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp
      have hp0 : p = 0 := Polynomial.ext fun m ↦ by simpa using hp m (Nat.zero_le m)
      rw [hp0]
      exact Submodule.zero_mem _
    | succ n ih =>
      intro hn p hp
      set u := (bitsEquiv κ).symm ⟨n, hn⟩ with hu_def
      have hu : bitsToNat u = n := by rw [← bitsEquiv_val, hu_def, Equiv.apply_symm_apply]
      have hn64 : n < 2 ^ 64 :=
        lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hκ)
      set q := novelE n
      have hqdeg : q.natDegree = n := by rw [natDegree_map, natDegree_novel hn64]
      have hq0 : q ≠ 0 := by
        rw [Ne, Polynomial.map_eq_zero_iff (algebraMap K E).injective]
        exact novel_ne_zero n
      have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
      set c := p.coeff n / q.leadingCoeff
      have hp' : p - c • q ∈ degreeLT E n := by
        rw [mem_degreeLT, degree_lt_iff_coeff_zero]
        intro m hm
        rw [coeff_sub, coeff_smul, smul_eq_mul]
        rcases eq_or_lt_of_le hm with hm | hm
        · subst hm
          rw [← hqdeg, coeff_natDegree, hqdeg, div_mul_cancel₀ _ hlc, sub_self]
        · rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp
          rw [hp m (by exact_mod_cast hm), coeff_eq_zero_of_natDegree_lt (by (clear * - hn hu hqdeg hm; omega)), mul_zero,
            sub_zero]
      have hq : q ∈ LinearMap.range (msgPoly κ) := ⟨Pi.single u 1, by rw [msgPoly_single, hu]⟩
      have := Submodule.add_mem _ (ih (by (clear * - hn hu hqdeg; omega)) hp') (Submodule.smul_mem _ c hq)
      rwa [sub_add_cancel] at this

/-- The message polynomial is injective (for `κ ≤ 64`): the `X_j`, `j < 2^κ`, are linearly
independent, by dimension count against `range_msgPoly`. -/
theorem msgPoly_injective {κ : ℕ} (hκ : κ ≤ 64) : Function.Injective (msgPoly κ) := by
  have hmem : ∀ g, msgPoly κ g ∈ degreeLT E (2 ^ κ) := fun g ↦
    range_msgPoly hκ ▸ LinearMap.mem_range_self _ g
  set f := (msgPoly κ).codRestrict (degreeLT E (2 ^ κ)) hmem
  have hrank : Module.finrank E ((Fin κ → Bool) → E) = Module.finrank E (degreeLT E (2 ^ κ)) := by
    rw [Module.finrank_fintype_fun_eq_card, (degreeLTEquiv E (2 ^ κ)).finrank_eq,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  have : FiniteDimensional E (degreeLT E (2 ^ κ)) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv E (2 ^ κ)).symm
  have hsurj : Function.Surjective f := by
    rintro ⟨p, hp⟩
    rw [← range_msgPoly hκ] at hp
    obtain ⟨g, rfl⟩ := hp
    exact ⟨g, rfl⟩
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj
  intro a b hab
  exact hinj (Subtype.ext hab)

/-- The range of `Enc_{κ,R}` is the Reed-Solomon code of degree `2^κ` on `D_{κ,R}`. -/
theorem range_enc {κ R : ℕ} (h : κ + R ≤ 64) :
    LinearMap.range (enc κ R) = rsCode (domain κ R h) (2 ^ κ) := by
  have : enc κ R = (evalOnPoints (domain κ R h)).comp (msgPoly κ) :=
    LinearMap.ext fun g ↦ enc_eq_evalOnPoints h g
  rw [this, LinearMap.range_comp, range_msgPoly (by (clear * - h; omega)), rsCode]

/-- `Enc_{κ,R}` is injective for `κ + R ≤ 64`: a polynomial of degree `< 2^κ` vanishing on the
`2^(κ+R)` points of `D_{κ,R}` is zero. -/
theorem enc_injective {κ R : ℕ} (h : κ + R ≤ 64) : Function.Injective (enc κ R) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  apply msgPoly_injective (show κ ≤ 64 by (clear * - h; omega))
  rw [map_zero]
  have hmem : msgPoly κ g ∈ degreeLT E (2 ^ κ) :=
    range_msgPoly (show κ ≤ 64 by (clear * - h; omega)) ▸ LinearMap.mem_range_self _ g
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (domain κ R h).injective
    (fun v ↦ ?_) ?_
  · have := congrFun (enc_eq_evalOnPoints h g) v
    rw [hg] at this
    exact this.symm
  · rw [Fintype.card_fin]
    rw [mem_degreeLT] at hmem
    have hlt : (msgPoly κ g).natDegree < 2 ^ κ := by
      by_cases h0 : msgPoly κ g = 0
      · rw [h0, natDegree_zero]
        exact Nat.two_pow_pos κ
      · exact (natDegree_lt_iff_degree_lt h0).mpr hmem
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by (clear * -; omega)))

end
end LeanVM.Protocol.Whir
