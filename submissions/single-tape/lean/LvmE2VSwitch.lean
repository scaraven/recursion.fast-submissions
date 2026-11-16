-- New for lvm2 S1 (E2-F, E2F-V), E2AC-DES §6 statements 8 and 9: the 128-row switch of the `E2` front's bit
-- slices (`rowSwitch`, `rowSwitchSpec`, from E2-S's `switch_sound_E2`) and the `E2` word claims as two
-- `K`-linear block claims (`wordClaimsE2`, `wordClaimE2`; the weights `tensorW`, `wordW` against
-- `tensor_repr`/`tensorSwitch_E2`).
import LvmE2VSample
import LvmTensorSwitch
import LvmVEqMid
import LvmWhirSumcheck

/-!
# The row switch and the word claims at `E2`

**Row switch** (E2-S-switch, `LvmTensorSwitch`'s D1 form). The front's slot phases leave 64 slice
values `s_i ∈ E2` claimed to be `Σ_u [bit i of col(u)]·eq(z, u)` at an `E2` point `z` (`SlicesTrueE2`).
`V`:
* transposes them into 128 rows of `K` (`rowWord`, row `j = i + 64h` = bit `i` of coordinate `h`,
  E2-S's pinned `eRow`), with no new proof bytes;
* draws `r'' ∈ E3^7` (seven `E3` samples, no nonce, one group);
* claims `Σ_u W(u)·col(u) = Σ_j eq(r'', j)·t_j` (`rowTarget`), `W(u) = Σ_j eq(r'', j) ε_j(u)`,
  `ε_j(u)` the `j`-th `F₂`-coordinate of `eq(z, u)`; at a point `r ∈ E3^m` `V` evaluates `W`'s
  extension as `Σ_j eq(r'', j)·tensorW z r j`, `tensorW` the coordinates of
  `Π_l (1 + 1⊗z_l + r_l⊗1)` in `E3 ⊗_{F₂} E2` (`rowWeight`).

* **`tensorW_eq`** (statement 9): `tensorW z r j = Σ_u eq(r, u)·ε_j(u)` (`tensor_repr`'s right side);
* **`rowSwitchSpec`** (statement 8): from doom of the slice claims to doom of the switched claim on
  the column (`RowColTrue`), the seven samples escaping at `L₀/|E3|` each (start: `slicesTrue_iff`;
  per coordinate: a nonzero table folded by one coordinate vanishes for one value at most; end:
  `claim_iff`, `weight_ext`; the joint form is `switch_sound_E2`).

**Word claims** (NOTE-FIELD Prop 7.1). `f̃(z) = v` at `z ∈ E2^m` on a `K` column is the pair of
`K`-linear claims with weights the two coordinates of `eq(z, ·)`; at `r ∈ E3^m` `V` reads both off
`wordW z r = Π_l (z_l·r_l + (1 + z_l)(1 + r_l))` in `Quad Ext3` (`E6`):
* **`wordClaimE2`** (statement 9): the word claim holds iff both block claims of
  `wordClaimsE2 blk z v` hold on the block;
* `wordW_eq`: `wordW z r = ⟨Σ_u eq(r, u)·(eq(z, u)).re, Σ_u eq(r, u)·(eq(z, u)).im⟩`
  (`tensorSwitch_E2`); `isMultiaffine_wordW`, `isMultiaffine_rowWeight`: the weights are multiaffine
  (the PCS's premise).
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (errE eqAt)
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open Finset
open scoped ENNReal

/-! ## `E2`'s 128 coordinates -/

/-- Coordinate `j = i + 64h` of `y ∈ E2` over `F₂`: bit `i` of `re` (`h = 0`) or of `im` (`h = 1`). -/
def bitE2 (y : E2) (j : ℕ) : Bool :=
  if j < 64 then y.re.toBitVec.getLsbD j else y.im.toBitVec.getLsbD (j - 64)

/-- The basis element `β_j = x^i·X^h` of `E2`, `j = i + 64h`. -/
def basisE2 (j : ℕ) : E2 :=
  if j < 64 then ⟨K.ofBits (2 ^ j), 0⟩ else ⟨0, K.ofBits (2 ^ (j - 64))⟩

/-- `ofK` of a coordinate bit. -/
def bitE (b : Bool) : E := if b then 1 else 0

theorem eqAt_set_affine : ∀ (l : List E) (k m : ℕ), k < l.length → ∀ X : E,
    eqAt (l.set k X) m = (1 - X) * eqAt (l.set k 0) m + X * eqAt (l.set k 1) m
  | [], k, m, hk, X => absurd hk (by simp)
  | a :: l, 0, m, _, X => by
    simp only [List.set_cons_zero, LeanVM.Protocol.KeccakGkr.eqAt_cons]
    split_ifs <;> ring
  | a :: l, k + 1, m, hk, X => by
    simp only [List.set_cons_succ, LeanVM.Protocol.KeccakGkr.eqAt_cons]
    rw [eqAt_set_affine l k (m / 2) (by simpa using hk) X]
    ring

/-- `eq(·, m)` is multiaffine. -/
theorem isMultiaffine_eqAt' (n m : ℕ) : IsMultiaffine n fun X ↦ eqAt X m :=
  fun l hl k hk X ↦ eqAt_set_affine l k m (hl ▸ hk) X

/-- A weight that agrees on lists of length `n` with a multiaffine one is multiaffine. -/
private theorem isMultiaffine_congr {n : ℕ} {Φ Ψ : List E → E} (h : IsMultiaffine n Ψ)
    (he : ∀ l : List E, l.length = n → Φ l = Ψ l) : IsMultiaffine n Φ := by
  intro l hl k hk X
  rw [he _ (by rw [List.length_set, hl]), he _ (by rw [List.length_set, hl]),
    he _ (by rw [List.length_set, hl])]
  exact h l hl k hk X

/-- `Σ_n c_n·eq(·, n)` is multiaffine. -/
theorem isMultiaffine_sum_eqAt (n N : ℕ) (c : ℕ → E) :
    IsMultiaffine n fun x ↦ ∑ i ∈ range N, eqAt x i * c i :=
  isMultiaffine_congr (Ψ := fun x ↦ ∑ i ∈ range N, c i * eqAt x i)
    (IsMultiaffine.sum _ _ fun i _ ↦ (isMultiaffine_eqAt' n i).const_mul _)
    fun _ _ ↦ sum_congr rfl fun _ _ ↦ mul_comm _ _

/-! ### `E2`'s coordinates: additivity, the basis, the expansion -/

theorem toBitVec_zero_K : BF64.toBitVec (0 : K) = 0 := rfl

theorem bitE2_zero (j : ℕ) : bitE2 0 j = false := by
  unfold bitE2
  split_ifs <;> simp [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]

theorem bitE2_add (a b : E2) (j : ℕ) : bitE2 (a + b) j = (bitE2 a j ^^ bitE2 b j) := by
  unfold bitE2
  split_ifs <;>
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, BF64.add_def, BF64.toBitVec_ofBitVec,
      BitVec.getLsbD_xor]

private theorem bitE_xor (a b : Bool) : bitE (a ^^ b) = bitE a + bitE b := by
  cases a <;> cases b <;>
    simp [bitE, LeanVM.Protocol.Whir.Complete.one_add_one_E]

theorem bitE_injective : Function.Injective bitE := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitE]

/-- Coordinate `j` of `E2` as an additive map into `E`. -/
def bitHom (j : ℕ) : E2 →+ E where
  toFun x := bitE (bitE2 x j)
  map_zero' := by rw [bitE2_zero]; rfl
  map_add' a b := by rw [bitE2_add, bitE_xor]

theorem bitE_bitE2_add (a b : E2) (j : ℕ) :
    bitE (bitE2 (a + b) j) = bitE (bitE2 a j) + bitE (bitE2 b j) :=
  (bitHom j).map_add a b

theorem bitE_bitE2_sum (s : Finset ℕ) (f : ℕ → E2) (j : ℕ) :
    bitE (bitE2 (∑ k ∈ s, f k) j) = ∑ k ∈ s, bitE (bitE2 (f k) j) :=
  map_sum (bitHom j) f s

theorem getLsbD_ofBits_two_pow (k i : ℕ) (hi : i < 64) :
    (K.ofBits (2 ^ k)).toBitVec.getLsbD i = decide (k = i) := by
  show (BitVec.ofNat 64 (2 ^ k)).getLsbD i = _
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow, decide_eq_true hi, Bool.true_and]

theorem bitE2_basisE2 {k j : ℕ} (hk : k < 128) (hj : j < 128) :
    bitE2 (basisE2 k) j = decide (k = j) := by
  unfold bitE2 basisE2
  by_cases hk64 : k < 64 <;> by_cases hj64 : j < 64
  · simp only [hk64, hj64, ite_true]
    exact getLsbD_ofBits_two_pow k j hj64
  · simp only [hk64, hj64, ite_true, ite_false]
    rw [toBitVec_zero_K]
    exact (by simp : BitVec.getLsbD (0 : BitVec 64) _ = false).trans (decide_eq_false (by omega)).symm
  · simp only [hk64, hj64, ite_true, ite_false]
    rw [toBitVec_zero_K]
    exact (by simp : BitVec.getLsbD (0 : BitVec 64) _ = false).trans (decide_eq_false (by omega)).symm
  · simp only [hk64, hj64, ite_false]
    rw [getLsbD_ofBits_two_pow _ _ (by omega)]
    simp only [decide_eq_decide]
    omega

theorem ext_bitE2 {x y : E2} (h : ∀ j < 128, bitE2 x j = bitE2 y j) : x = y := by
  refine QuadraticAlgebra.ext (BF64.toBitVec_injective (BitVec.eq_of_getLsbD_eq fun i hi ↦ ?_))
    (BF64.toBitVec_injective (BitVec.eq_of_getLsbD_eq fun i hi ↦ ?_))
  · have := h i (by omega)
    simpa [bitE2, hi] using this
  · have := h (i + 64) (by omega)
    simpa [bitE2] using this

theorem bitE_basisE2 {k j : ℕ} (hk : k < 128) (hj : j < 128) :
    bitE (bitE2 (basisE2 k) j) = if k = j then 1 else 0 := by
  rw [bitE2_basisE2 hk hj]
  by_cases h : k = j <;> simp [h, bitE]

/-- **The expansion of `x ∈ E2` in the basis `β_k`.** -/
theorem expand_E2 (x : E2) : x = ∑ k ∈ range 128, if bitE2 x k then basisE2 k else 0 := by
  refine ext_bitE2 fun j hj ↦ bitE_injective ?_
  rw [bitE_bitE2_sum]
  have e : ∀ k ∈ range 128, bitE (bitE2 (if bitE2 x k then basisE2 k else 0) j) =
      if k = j then bitE (bitE2 x k) else 0 := by
    intro k hk
    have hk' := mem_range.1 hk
    by_cases hb : bitE2 x k
    · rw [ite_eq_left hb, bitE_basisE2 hk' hj, hb]
      rfl
    · rw [ite_eq_right hb, bitE2_zero]
      by_cases hkj : k = j
      · rw [ite_eq_left hkj, Bool.eq_false_iff.2 hb]
      · rw [ite_eq_right hkj]
        rfl
  rw [sum_congr rfl e, sum_ite_eq', ite_eq_left (mem_range.2 hj)]

/-- **Multiplication on coordinates**: coordinate `j` of `x·y` is `Σ_k x_k·(coordinate j of β_k y)`. -/
theorem bitE_mul (x y : E2) (j : ℕ) :
    bitE (bitE2 (x * y) j) = ∑ k ∈ range 128, bitE (bitE2 x k) * bitE (bitE2 (basisE2 k * y) j) := by
  conv_lhs => rw [expand_E2 x]
  rw [sum_mul, bitE_bitE2_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  cases bitE2 x k
  · rw [ite_eq_right Bool.false_ne_true, zero_mul, bitE2_zero]
    simp [bitE]
  · rw [ite_eq_left rfl]
    simp [bitE]

/-! ### Generic sums and `eq` at even and odd indices -/

private theorem foldl_mul_eq {R : Type*} [CommMonoid R] :
    ∀ (a : R) (l : List R), l.foldl (· * ·) a = a * l.foldl (· * ·) 1
  | a, [] => by simp
  | a, x :: l => by
    rw [List.foldl_cons, List.foldl_cons, foldl_mul_eq (a * x) l, foldl_mul_eq (1 * x) l, one_mul,
      mul_assoc]

private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ N : ℕ,
    ∑ n ∈ range (2 * N), f n = ∑ k ∈ range N, (f (2 * k) + f (2 * k + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_two_mul f N,
      sum_range_succ, add_assoc]

theorem sum_range_pow_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ n ∈ range (2 ^ (m + 1)), f n = ∑ k ∈ range (2 ^ m), (f (2 * k) + f (2 * k + 1)) := by
  rw [pow_succ', sum_range_two_mul]

theorem eqAt_two_mul (a : E) (l : List E) (k : ℕ) : eqAt (a :: l) (2 * k) = (1 + a) * eqAt l k := by
  rw [LeanVM.Protocol.KeccakGkr.eqAt_cons, ite_eq_right (by omega),
    show 2 * k / 2 = k by omega]

theorem eqAt_two_mul_add_one (a : E) (l : List E) (k : ℕ) :
    eqAt (a :: l) (2 * k + 1) = a * eqAt l k := by
  rw [LeanVM.Protocol.KeccakGkr.eqAt_cons, ite_eq_left (by omega),
    show (2 * k + 1) / 2 = k by omega]

theorem eqAtF_cons {F : Type} [Field F] (a : F) (l : List F) (n : ℕ) :
    eqAtF (a :: l) n = (if n % 2 = 1 then a else 1 + a) * eqAtF l (n / 2) := rfl

theorem eqAtF_two_mul {F : Type} [Field F] (a : F) (l : List F) (k : ℕ) :
    eqAtF (a :: l) (2 * k) = (1 + a) * eqAtF l k := by
  rw [eqAtF_cons, ite_eq_right (by omega), show 2 * k / 2 = k by omega]

theorem eqAtF_two_mul_add_one {F : Type} [Field F] (a : F) (l : List F) (k : ℕ) :
    eqAtF (a :: l) (2 * k + 1) = a * eqAtF l k := by
  rw [eqAtF_cons, ite_eq_left (by omega),
    show (2 * k + 1) / 2 = k by omega]

/-! ## The row switch -/

/-- **Row `j = i + 64h`** of the slice values: the `K` word whose bit `i'` is coordinate `j` of `s_{i'}`. -/
def rowWord (sv : List E2) (j : ℕ) : K :=
  K.ofBits ((List.range 64).foldl (fun acc i ↦ if bitE2 (sv.getD i 0) j then acc + 2 ^ i else acc) 0)

/-- The switched target `Σ_j eq(r'', j)·t_j`. -/
def rowTarget (rr : List E) (sv : List E2) : E :=
  ∑ j ∈ range 128, eqAt rr j * ofK (rowWord sv j)

/-- One factor of `Π_l (1 + 1⊗z_l + r_l⊗1)` on a coordinate vector (basis `1 ⊗ β_j` over `E3`):
`v ↦ (1 + r_l)·v + M_{z_l} v`, `(M_z v)_j = Σ_k [coordinate j of β_k z]·v_k`. -/
def tensorStep (v : List E) (zr : E2 × E) : List E :=
  (List.range 128).map fun j ↦
    (1 + zr.2) * v.getD j 0 +
      ∑ k ∈ range 128, if bitE2 (basisE2 k * zr.1) j then v.getD k 0 else 0

/-- **`V`'s tensor coordinates**: `Π_l (1 + 1⊗z_l + r_l⊗1)` in `E3 ⊗_{F₂} E2`, as its 128 `E3`
coordinates in the basis `1 ⊗ β_j`, from `1 = 1 ⊗ β_0`. -/
def tensorW (z : List E2) (r : List E) : List E :=
  (List.zip z r).foldl tensorStep ((List.range 128).map fun j ↦ if j = 0 then 1 else 0)

/-- The switched weight's extension at `r`: `Σ_j eq(r'', j)·tensorW z r j`. -/
def rowWeight (z : List E2) (rr r : List E) : E :=
  ∑ j ∈ range 128, eqAt rr j * (tensorW z r).getD j 0

/-- **The row switch**: seven `E3` samples `r''`, then the switched claim's value and weight. -/
def rowSwitch (z sv : List E2) : VerifierProgram (E × (List E → E)) :=
  VerifierProgram.sampleChallenges 7 >>= fun rr ↦ pure (rowTarget rr sv, rowWeight z rr)

/-- **The slice claims at `E2`**: `s_i = Σ_u [bit i of col(u)]·eq(z, u)` for the 64 bits. -/
def SlicesTrueE2 (col : ℕ → K) (z sv : List E2) : Prop :=
  sv.length = 64 ∧ ∀ i < 64,
    sv.getD i 0 = ∑ n ∈ range (2 ^ z.length),
      if (col n).toBitVec.getLsbD i then eqAtF z n else 0

/-- **The switched claim on the column**: `value = Σ_u W(u)·col(u)` over the `m` variables. -/
def RowColTrue (m : ℕ) (col : ℕ → K) (res : E × (List E → E)) : Prop :=
  res.1 = ∑ n ∈ range (2 ^ m), res.2 (boolPoint m n) * ofK (col n)

/-! ### The fold of `tensorStep` -/

private theorem getD_map_range (f : ℕ → E) {N k : ℕ} (hk : k < N) :
    ((List.range N).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hk]

theorem getD_tensorStep (v : List E) (zr : E2 × E) {k : ℕ} (hk : k < 128) :
    (tensorStep v zr).getD k 0 = (1 + zr.2) * v.getD k 0 +
      ∑ k' ∈ range 128, if bitE2 (basisE2 k' * zr.1) k then v.getD k' 0 else 0 :=
  getD_map_range _ hk

/-- The `M_z` part of a step on coordinates: `Σ_k (M_z v)_k·(coordinate j of β_k y) =
Σ_k v_k·(coordinate j of β_k z y)`. -/
theorem sum_Mz (v : List E) (zl y : E2) (j : ℕ) :
    ∑ k ∈ range 128, (∑ k' ∈ range 128, if bitE2 (basisE2 k' * zl) k then v.getD k' 0 else 0) *
        bitE (bitE2 (basisE2 k * y) j) =
      ∑ k' ∈ range 128, v.getD k' 0 * bitE (bitE2 (basisE2 k' * (zl * y)) j) := by
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k' _ ↦ ?_
  rw [← mul_assoc, bitE_mul, mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  by_cases hb : bitE2 (basisE2 k' * zl) k
  · rw [ite_eq_left hb, hb]
    simp [bitE]
  · rw [ite_eq_right hb, Bool.eq_false_iff.2 hb]
    simp [bitE]

/-- **The fold of `tensorStep`** from any start vector `v`. -/
theorem foldl_tensorStep : ∀ (z : List E2) (r : List E) (v : List E), r.length = z.length →
    ∀ j < 128, ((List.zip z r).foldl tensorStep v).getD j 0 =
      ∑ n ∈ range (2 ^ z.length), eqAt r n *
        ∑ k ∈ range 128, v.getD k 0 * bitE (bitE2 (basisE2 k * eqAtF z n) j)
  | [], [], v, _, j, hj => by
    simp only [List.zip_nil_left, List.foldl_nil, List.length_nil, pow_zero, sum_range_one,
      LeanVM.Protocol.KeccakGkr.eqAt_nil, one_mul]
    have e : ∀ k ∈ range 128, v.getD k 0 * bitE (bitE2 (basisE2 k * eqAtF [] 0) j) =
        if k = j then v.getD k 0 else 0 := by
      intro k hk
      rw [show eqAtF ([] : List E2) 0 = 1 from rfl, mul_one, bitE_basisE2 (mem_range.1 hk) hj]
      split_ifs <;> simp
    rw [sum_congr rfl e, sum_ite_eq', ite_eq_left (mem_range.2 hj)]
  | zl :: z, rl :: r, v, h, j, hj => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_tensorStep z r _ (by simpa using h) j hj,
      List.length_cons, sum_range_pow_succ]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [eqAt_two_mul, eqAt_two_mul_add_one, eqAtF_two_mul, eqAtF_two_mul_add_one]
    have h1 : ∀ k, bitE (bitE2 (basisE2 k * ((1 + zl) * eqAtF z n)) j) =
        bitE (bitE2 (basisE2 k * eqAtF z n) j) + bitE (bitE2 (basisE2 k * (zl * eqAtF z n)) j) := by
      intro k
      rw [show basisE2 k * ((1 + zl) * eqAtF z n) = basisE2 k * eqAtF z n + basisE2 k * (zl * eqAtF z n)
        by ring, bitE_bitE2_add]
    have h2 : ∑ k ∈ range 128, (tensorStep v (zl, rl)).getD k 0 * bitE (bitE2 (basisE2 k * eqAtF z n) j) =
        (1 + rl) * ∑ k ∈ range 128, v.getD k 0 * bitE (bitE2 (basisE2 k * eqAtF z n) j) +
          ∑ k ∈ range 128, v.getD k 0 * bitE (bitE2 (basisE2 k * (zl * eqAtF z n)) j) := by
      rw [sum_congr rfl fun k hk ↦ by rw [getD_tensorStep v _ (mem_range.1 hk)], ← sum_Mz]
      simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
    simp only [h1, mul_add, sum_add_distrib]
    rw [h2]
    linear_combination (-eqAt r n * rl * ∑ k ∈ range 128, v.getD k 0 *
      bitE (bitE2 (basisE2 k * (zl * eqAtF z n)) j)) * LeanVM.Protocol.Whir.Complete.two_eq_zero_E
  | [], _ :: _, _, h, _, _ => absurd h (by simp)
  | _ :: _, [], _, h, _, _ => absurd h (by simp)

theorem basisE2_zero : basisE2 0 = 1 := by
  unfold basisE2
  rw [ite_eq_left (by norm_num)]
  rfl

/-- **Statement 9 (`tensorW_eq`), the row weight**: `V`'s tensor coordinates are `tensor_repr`'s
`Σ_u eq(r, u)·ε_j(u)`, `ε_j(u)` coordinate `j` of `eq(z, u)`. -/
theorem tensorW_eq (z : List E2) (r : List E) (hr : r.length = z.length) {j : ℕ} (hj : j < 128) :
    (tensorW z r).getD j 0 =
      ∑ n ∈ range (2 ^ z.length), eqAt r n * bitE (bitE2 (eqAtF z n) j) := by
  rw [tensorW, foldl_tensorStep z r _ hr j hj]
  refine sum_congr rfl fun n _ ↦ ?_
  congr 1
  have e : ∀ k ∈ range 128, ((List.range 128).map fun j ↦ if j = 0 then (1 : E) else 0).getD k 0 *
      bitE (bitE2 (basisE2 k * eqAtF z n) j) = if k = 0 then bitE (bitE2 (eqAtF z n) j) else 0 := by
    intro k hk
    rw [getD_map_range _ (mem_range.1 hk)]
    by_cases h0 : k = 0
    · rw [ite_eq_left h0, ite_eq_left h0, h0, basisE2_zero, one_mul, one_mul]
    · rw [ite_eq_right h0, ite_eq_right h0, zero_mul]
  rw [sum_congr rfl e, sum_ite_eq', ite_eq_left (mem_range.2 (by norm_num))]

/-- The row weight is multiaffine in the point. -/
theorem isMultiaffine_rowWeight (z : List E2) (rr : List E) :
    IsMultiaffine z.length (rowWeight z rr) := by
  refine isMultiaffine_congr (isMultiaffine_sum_eqAt _ (2 ^ z.length)
    fun n ↦ ∑ j ∈ range 128, eqAt rr j * bitE (bitE2 (eqAtF z n) j)) fun l hl ↦ ?_
  rw [rowWeight, sum_congr rfl fun j hj ↦ by rw [tensorW_eq z l hl (mem_range.1 hj)]]
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun n _ ↦ sum_congr rfl fun j _ ↦ by ring

/-! ### The row switch on the cube: transposition and the switched claim -/

/-- The bits of the word `Σ_{i < N, b i} 2^i`. -/
theorem testBit_foldl_bits (b : ℕ → Bool) : ∀ N : ℕ,
    (List.range N).foldl (fun acc i ↦ if b i then acc + 2 ^ i else acc) 0 < 2 ^ N ∧
      ∀ i, ((List.range N).foldl (fun acc i ↦ if b i then acc + 2 ^ i else acc) 0).testBit i =
        (decide (i < N) && b i)
  | 0 => ⟨by simp, fun i ↦ by simp⟩
  | N + 1 => by
    obtain ⟨hlt, hbit⟩ := testBit_foldl_bits b N
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set f := (List.range N).foldl (fun acc i ↦ if b i then acc + 2 ^ i else acc) 0
    by_cases hN : b N
    · rw [ite_eq_left hN]
      refine ⟨by rw [pow_succ]; omega, fun i ↦ ?_⟩
      rw [show f + 2 ^ N = 2 ^ N * 1 + f by ring, Nat.testBit_two_pow_mul_add 1 hlt]
      by_cases hi : i < N
      · rw [ite_eq_left hi, hbit i]
        simp [hi, show i < N + 1 by omega]
      · rw [ite_eq_right hi]
        by_cases hiN : i = N
        · subst hiN
          simp [hN]
        · rw [Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))]
          simp only [show ¬ i < N + 1 by omega, decide_false, Bool.false_and]
    · rw [ite_eq_right hN]
      refine ⟨lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)), fun i ↦ ?_⟩
      rw [hbit i]
      by_cases hi : i < N
      · simp [hi, show i < N + 1 by omega]
      · by_cases hiN : i = N
        · subst hiN
          simp [hN]
        · simp only [show ¬ i < N by omega, show ¬ i < N + 1 by omega, decide_false, Bool.false_and]

/-- Bit `i` of row `j` is coordinate `j` of `s_i`. -/
theorem rowWord_bit (sv : List E2) {i : ℕ} (hi : i < 64) (j : ℕ) :
    (rowWord sv j).toBitVec.getLsbD i = bitE2 (sv.getD i 0) j := by
  show (BitVec.ofNat 64 _).getLsbD i = _
  rw [BitVec.getLsbD_ofNat, (testBit_foldl_bits (fun i ↦ bitE2 (sv.getD i 0) j) 64).2 i]
  simp [hi]

/-- Bit `i` of a word of `K` as an additive map into `E`. -/
def bitKHom (i : ℕ) : K →+ E where
  toFun a := bitE (a.toBitVec.getLsbD i)
  map_zero' := by
    rw [toBitVec_zero_K]
    simp [bitE]
  map_add' a b := by
    simp only [BF64.add_def, BF64.toBitVec_ofBitVec, BitVec.getLsbD_xor, bitE_xor]

theorem bitE_getLsbD_sum (s : Finset ℕ) (f : ℕ → K) (i : ℕ) :
    bitE ((∑ n ∈ s, f n).toBitVec.getLsbD i) = ∑ n ∈ s, bitE ((f n).toBitVec.getLsbD i) :=
  map_sum (bitKHom i) f s

/-- **The true row `j`**: `Σ_u ε_j(u)·col(u)`, `ε_j(u)` coordinate `j` of `eq(z, u)`. -/
def trueRowE2 (col : ℕ → K) (z : List E2) (j : ℕ) : K :=
  ∑ n ∈ range (2 ^ z.length), if bitE2 (eqAtF z n) j then col n else 0

/-- The row errors, in `E`. -/
def rowErr (col : ℕ → K) (z sv : List E2) (j : ℕ) : E := ofK (rowWord sv j - trueRowE2 col z j)

/-- **Transposition**: rows equal to their true values make the slice claims true. -/
theorem slices_of_rows (col : ℕ → K) (z sv : List E2) (hsv : sv.length = 64)
    (h : ∀ j < 128, rowWord sv j = trueRowE2 col z j) : SlicesTrueE2 col z sv := by
  refine ⟨hsv, fun i hi ↦ ext_bitE2 fun j hj ↦ bitE_injective ?_⟩
  rw [← rowWord_bit sv hi j, h j hj, trueRowE2, bitE_getLsbD_sum, bitE_bitE2_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  cases hb : bitE2 (eqAtF z n) j <;> cases hc : (col n).toBitVec.getLsbD i <;>
    simp [hb, hc, bitE2_zero]

theorem slices_of_zeroOn (col : ℕ → K) (z sv : List E2) (hsv : sv.length = 64)
    (h : LeanVM.Protocol.KeccakGkr.ZeroOn (rowErr col z sv) [] 7) : SlicesTrueE2 col z sv := by
  rw [LeanVM.Protocol.KeccakGkr.zeroOn_nil] at h
  refine slices_of_rows col z sv hsv fun j hj ↦ ?_
  have h0 := h j (by norm_num; exact hj)
  rw [rowErr, show ofK (rowWord sv j - trueRowE2 col z j) =
    algebraMap K E (rowWord sv j - trueRowE2 col z j) from rfl, map_sub, sub_eq_zero] at h0
  exact (algebraMap K E).injective h0

/-- Equality weights at a cube point: the indicator of the index. -/
theorem eqAt_boolPoint : ∀ (m n n' : ℕ), n < 2 ^ m → n' < 2 ^ m →
    eqAt (boolPoint m n) n' = if n' = n then 1 else 0
  | 0, n, n', hn, hn' => by
    rw [show n = 0 by simpa using hn, show n' = 0 by simpa using hn']
    simp
  | m + 1, n, n', hn, hn' => by
    rw [pow_succ] at hn hn'
    rw [LeanVM.Protocol.Whir.Complete.boolPoint_succ, LeanVM.Protocol.KeccakGkr.eqAt_cons,
      eqAt_boolPoint m (n / 2) (n' / 2) (by omega) (by omega), Nat.testBit_zero]
    have e : (n' = n) ↔ (n' / 2 = n / 2 ∧ (n' % 2 = 1 ↔ n % 2 = 1)) := by omega
    by_cases hq : n' / 2 = n / 2 <;> by_cases ha : n % 2 = 1 <;> by_cases hb : n' % 2 = 1 <;>
      simp [e, ha, hb, hq, LeanVM.Protocol.Whir.Complete.one_add_one_E]

/-- The switched weight on the cube: `W(n) = Σ_j eq(r'', j)·ε_j(n)`. -/
theorem rowWeight_boolPoint (z : List E2) (rr : List E) {n : ℕ} (hn : n < 2 ^ z.length) :
    rowWeight z rr (boolPoint z.length n) =
      ∑ j ∈ range 128, eqAt rr j * bitE (bitE2 (eqAtF z n) j) := by
  unfold rowWeight
  refine sum_congr rfl fun j hj ↦ ?_
  rw [tensorW_eq z _ (LeanVM.Protocol.Whir.Complete.length_boolPoint _ _) (mem_range.1 hj)]
  congr 1
  rw [sum_congr rfl fun n' hn' ↦ by rw [eqAt_boolPoint _ _ _ hn (mem_range.1 hn')]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq', ite_eq_left (mem_range.2 hn)]

theorem ofK_trueRowE2 (col : ℕ → K) (z : List E2) (j : ℕ) :
    ofK (trueRowE2 col z j) = ∑ n ∈ range (2 ^ z.length), bitE (bitE2 (eqAtF z n) j) * ofK (col n) := by
  rw [trueRowE2, show ofK (∑ n ∈ range (2 ^ z.length), if bitE2 (eqAtF z n) j then col n else 0) =
    algebraMap K E (∑ n ∈ range (2 ^ z.length), if bitE2 (eqAtF z n) j then col n else 0) from rfl,
    map_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  by_cases hb : bitE2 (eqAtF z n) j
  · rw [ite_eq_left hb, hb, show bitE true = 1 from rfl, one_mul]
    rfl
  · rw [ite_eq_right hb, Bool.eq_false_iff.2 hb, show bitE false = 0 from rfl, zero_mul, map_zero]

/-- **The switched claim** on the column makes the batched row errors vanish at `r''`. -/
theorem zeroOn_of_rowCol (col : ℕ → K) (z sv : List E2) (rr : List E) (hrr : rr.length = 7)
    (h : RowColTrue z.length col (rowTarget rr sv, rowWeight z rr)) :
    LeanVM.Protocol.KeccakGkr.ZeroOn (rowErr col z sv) rr 7 := by
  rw [LeanVM.Protocol.KeccakGkr.zeroOn_full _ hrr]
  unfold RowColTrue at h
  dsimp only at h
  rw [sum_congr rfl fun n hn ↦ by rw [rowWeight_boolPoint z rr (mem_range.1 hn)]] at h
  have h2 : ∑ n ∈ range (2 ^ z.length),
      (∑ j ∈ range 128, eqAt rr j * bitE (bitE2 (eqAtF z n) j)) * ofK (col n) =
        ∑ j ∈ range 128, eqAt rr j * ofK (trueRowE2 col z j) := by
    simp only [ofK_trueRowE2, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun n _ ↦ by ring
  rw [h2, rowTarget] at h
  rw [show (2 : ℕ) ^ 7 = 128 from rfl]
  have e : ∀ j, rowErr col z sv j = ofK (rowWord sv j) - ofK (trueRowE2 col z j) := fun j ↦
    map_sub (algebraMap K E) _ _
  simp only [e, mul_sub, sum_sub_distrib]
  rw [h, sub_self]

section Doom

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **Statement 8 (`rowSwitchSpec`)**: the row switch, from doom of the slice claims at `z` to doom of
the switched claim on the column; the seven samples escape at `L₀/|E3|` each (one group), lead
`7·L₀/|E3| + T`. -/
theorem rowSwitchSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (col : β → ℕ → K)
    (R : β → Prop) (z sv : List E2) (hsv : sv.length = 64) :
    Nonempty (Spec (rowSwitch z sv) (Doomed C (fun q ↦ SlicesTrueE2 (col q) z sv ∧ R q))
      (fun res h ↦ Doomed C (fun q ↦ RowColTrue z.length (col q) res ∧ R q) h) εmax
      ((∑ _i ∈ range 7, (L₀ : ℝ≥0∞) * errE 1) + T) T) := by
  refine ⟨Spec.congr (p := VerifierProgram.sampleChallenges 7 >>= fun rr ↦
      VerifierProgram.ret (rowTarget rr sv, rowWeight z rr)) rfl ?_⟩
  refine ((Lvm.KG.zeroSpec (n := 7) (m := 7) (εmax := εmax) (T := T) hst hcard
      (fun q ↦ rowErr (col q) z sv) R le_rfl).mono
      (fun _ hd q hq ⟨hz, hR⟩ ↦ hd q hq ⟨slices_of_zeroOn (col q) z sv hsv hz, hR⟩)
      (fun _ _ h ↦ h) le_rfl (by rw [sum_const, card_range, nsmul_eq_mul]) le_rfl).bind'
    fun rr ↦ (Spec.ret _).mono (fun _ hd q hq ⟨hc, hR⟩ ↦ hd.2 q hq ⟨zeroOn_of_rowCol (col q) z sv rr hd.1 hc, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Doom

/-! ## Word claims -/

/-- **`V`'s word weight**: `Π_l (z_l·r_l + (1 + z_l)(1 + r_l))` in `Quad Ext3`. -/
def wordW (z : List E2) (r : List E) : E6 :=
  (List.zipWith (fun zl rl ↦ e2ToE6 zl * Quad.C rl + (1 + e2ToE6 zl) * (1 + Quad.C rl)) z r).foldl
    (· * ·) 1

/-- **The two block claims of an `E2` word claim** `f̃(z) = v` on the block `blk`: weights the
coordinates of `wordW z`, values the coordinates of `v`. -/
def wordClaimsE2 (blk : Lvm.VEq.VPlacement) (z : List E2) (v : E2) :
    Lvm.VEq.BClaim × Lvm.VEq.BClaim :=
  (⟨blk, fun x ↦ (wordW z x).re, ofK v.re⟩, ⟨blk, fun x ↦ (wordW z x).im, ofK v.im⟩)

/-- A block claim on a column given by its words: `Σ_n w(n)·col(index + n) = value`. -/
def BHolds (c : Lvm.VEq.BClaim) (col : ℕ → K) : Prop :=
  ∑ n ∈ range (2 ^ c.block.variableCount), c.weight (boolPoint c.block.variableCount n) *
    ofK (col (c.block.index + n)) = c.value

/-! ### Helpers for the word claims -/

theorem wordW_cons (zl : E2) (z : List E2) (rl : E) (r : List E) :
    wordW (zl :: z) (rl :: r) =
      (e2ToE6 zl * algebraMap E E6 rl + (1 + e2ToE6 zl) * (1 + algebraMap E E6 rl)) * wordW z r := by
  unfold wordW
  rw [List.zipWith_cons_cons, List.foldl_cons, foldl_mul_eq, one_mul]
  rfl

theorem wordW_nil (r : List E) : wordW [] r = 1 := by
  unfold wordW
  rw [List.zipWith_nil_left, List.foldl_nil]

theorem e2ToE6_re (y : E2) : (e2ToE6 y).re = ofK y.re := rfl

theorem e2ToE6_im (y : E2) : (e2ToE6 y).im = ofK y.im := rfl

/-- `Σ_n a_n·y_n` in `E6` (`a_n ∈ E3`, `y_n ∈ E2`) in coordinates. -/
theorem e6_sum_eq (a : ℕ → E) (y : ℕ → E2) (N : ℕ) :
    (∑ n ∈ range N, algebraMap E E6 (a n) * e2ToE6 (y n) : E6) =
      ⟨∑ n ∈ range N, a n * ofK (y n).re, ∑ n ∈ range N, a n * ofK (y n).im⟩ := by
  induction N with
  | zero => simp only [sum_range_zero]; rfl
  | succ N ih =>
    rw [sum_range_succ, ih]
    refine QuadraticAlgebra.ext ?_ ?_
    · simp only [sum_range_succ, QuadraticAlgebra.re_add]
      rw [mul_comm (algebraMap E E6 (a N)), ← Quad.C_eq_algebraMap, Quad.re_mul_C, mul_comm,
        e2ToE6_re]
    · simp only [sum_range_succ, QuadraticAlgebra.im_add]
      rw [mul_comm (algebraMap E E6 (a N)), ← Quad.C_eq_algebraMap, Quad.im_mul_C, mul_comm,
        e2ToE6_im]

theorem wordW_eq_sum : ∀ (z : List E2) (r : List E), r.length = z.length →
    wordW z r = ∑ n ∈ range (2 ^ z.length), algebraMap E E6 (eqAt r n) * e2ToE6 (eqAtF z n)
  | [], [], _ => by simp [wordW_nil, eqAtF]
  | zl :: z, rl :: r, h => by
    rw [wordW_cons, wordW_eq_sum z r (by simpa using h), List.length_cons, sum_range_pow_succ,
      mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [eqAt_two_mul, eqAt_two_mul_add_one, eqAtF_two_mul, eqAtF_two_mul_add_one]
    simp only [map_mul, map_add, map_one]
    ring
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

theorem one_add_one_E6 : (1 : E6) + 1 = 0 := by
  rw [← map_one (algebraMap E E6), ← map_add, LeanVM.Protocol.Whir.Complete.one_add_one_E, map_zero]

theorem wordW_boolPoint : ∀ (z : List E2) (n : ℕ),
    wordW z (boolPoint z.length n) = e2ToE6 (eqAtF z n)
  | [], n => by simp [wordW_nil, eqAtF]
  | zl :: z, n => by
    rw [List.length_cons, LeanVM.Protocol.Whir.Complete.boolPoint_succ, wordW_cons, wordW_boolPoint z,
      eqAtF_cons, map_mul]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [ite_eq_right (by simp [Nat.testBit_zero, h]),
        ite_eq_right (by omega)]
      simp
    · rw [ite_eq_left (by simp [Nat.testBit_zero, h]), ite_eq_left h,
        map_one, one_add_one_E6]
      simp

/-- **Statement 9 (`wordClaimE2`)**: an `E2` word claim on the block is its two block claims. -/
theorem wordClaimE2 (blk : Lvm.VEq.VPlacement) (z : List E2) (hz : z.length = blk.variableCount)
    (v : E2) (col : ℕ → K) :
    (∑ n ∈ range (2 ^ z.length), eqAtF z n * Quad.C (col (blk.index + n)) = v) ↔
      (BHolds (wordClaimsE2 blk z v).1 col ∧ BHolds (wordClaimsE2 blk z v).2 col) := by
  simp only [BHolds, wordClaimsE2]
  rw [← hz]
  simp only [wordW_boolPoint, e2ToE6_re, e2ToE6_im]
  have hre : (∑ n ∈ range (2 ^ z.length), eqAtF z n * Quad.C (col (blk.index + n))).re =
      ∑ n ∈ range (2 ^ z.length), (eqAtF z n).re * col (blk.index + n) := by
    rw [← QuadraticAlgebra.reₗ_apply (R := K), map_sum]
    exact sum_congr rfl fun n _ ↦ Quad.re_mul_C _ _
  have him : (∑ n ∈ range (2 ^ z.length), eqAtF z n * Quad.C (col (blk.index + n))).im =
      ∑ n ∈ range (2 ^ z.length), (eqAtF z n).im * col (blk.index + n) := by
    rw [← QuadraticAlgebra.imₗ_apply (R := K), map_sum]
    exact sum_congr rfl fun n _ ↦ Quad.im_mul_C _ _
  have hE : ∀ (f : ℕ → K) (w : K),
      (∑ n ∈ range (2 ^ z.length), ofK (f n) * ofK (col (blk.index + n)) = ofK w) ↔
        ∑ n ∈ range (2 ^ z.length), f n * col (blk.index + n) = w := by
    intro f w
    have e : ∑ n ∈ range (2 ^ z.length), ofK (f n) * ofK (col (blk.index + n)) =
        algebraMap K E (∑ n ∈ range (2 ^ z.length), f n * col (blk.index + n)) := by
      rw [map_sum]
      exact sum_congr rfl fun n _ ↦ (map_mul (algebraMap K E) _ _).symm
    rw [e]
    exact (algebraMap K E).injective.eq_iff
  rw [QuadraticAlgebra.ext_iff, hre, him, hE, hE]

/-- **Statement 9, the word weight** (`tensorSwitch_E2`): `wordW`'s coordinates are the extensions
of the two coordinates of `eq(z, ·)`. -/
theorem wordW_eq (z : List E2) (r : List E) (hr : r.length = z.length) :
    wordW z r = ⟨∑ n ∈ range (2 ^ z.length), eqAt r n * ofK (eqAtF z n).re,
      ∑ n ∈ range (2 ^ z.length), eqAt r n * ofK (eqAtF z n).im⟩ := by
  rw [wordW_eq_sum z r hr, e6_sum_eq]

/-- Both word weights are multiaffine. -/
theorem isMultiaffine_wordW (z : List E2) :
    IsMultiaffine z.length (fun x ↦ (wordW z x).re) ∧ IsMultiaffine z.length (fun x ↦ (wordW z x).im) := by
  refine ⟨isMultiaffine_congr (isMultiaffine_sum_eqAt _ (2 ^ z.length) fun n ↦ ofK (eqAtF z n).re) fun l hl ↦ ?_,
    isMultiaffine_congr (isMultiaffine_sum_eqAt _ (2 ^ z.length) fun n ↦ ofK (eqAtF z n).im) fun l hl ↦ ?_⟩
  · rw [wordW_eq z l hl]
  · rw [wordW_eq z l hl]

end Lvm.E2V
