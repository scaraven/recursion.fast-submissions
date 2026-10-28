-- Copied from `submissions/spartan-srom/lean/SpartanSromRingSwitch.lean` (this repository, branch
-- `v4/flock-recursive` at `783328c`), namespace `SpartanSrom` → `FR`; that file was ported from v3
-- `spartan-chain` (submissions repo, local `main` at `1f59b38`). Changes are listed in the module
-- docstring.
import FRSumcheck
import FRField128
import Mathlib.Algebra.CharP.Reduced
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius ring switching for `GF(2) ⊂ F` (BLUEPRINT §2.3 step 8, §5.2 rows R1–R2, A.7's pack)

The witness `z` is bits; `f = pack z` packs 128 consecutive bits into one F element (A.7: bit `i`
of the chunk is bit `i` of `c₀` for `i < 64`, bit `i − 64` of `c₁` above), i.e. along the
`GF(2)`-basis `bitBasis i = x^i y^⌊i/64⌋`-style words of F. The prover sends the 128 slice claims
`s_i = Q̃_i(r)` (`Q_i` the bit-plane `i`); the verifier draws `f_0 … f_6` (R1: 7 stages, one bad
value each) and applies the `F₂`-linear map `Φ(a) = a_7`, `a_{p+1} = a_p + f_p · a_p ^ 2 ^ M_p`,
`M_p = 2 ^ (6 − p)`; the switched claim `T = Σ_i b_i Φ(s_i)` is then the sum of `f · W` with
`W(u') = Φ(eq(r, u'))`, checked by the R2 sumcheck (degree 2) and the MBP evaluation
`W̃(r'') = Σ_k c_k eq(r^(2^k), r'')` (`weightEval`, the width-128 program of A.8's `mbp`).

* Copied from leanerVM (Mathlib-only): the staged map `frobMap`, `frobMap_eq_sum`, additivity,
  `frobPair` (`π_k(b) = Σ_i w_i · b_i ^ 2 ^ k`), `frobPair_stage`, `card_stage_zero_le_one`.
* From spartan-srom: `stages`, `Phi`, `phiApply`, `phiTable`, `target`, `weightTable`,
  `weightEval`, `weight_mle`, `mleEval_weightTable` (MBP = the extension of the prover's
  weights), `stage_bad_le_one`; `ring_complete` and `ring_final`, **generalised from the power
  basis `x^i` to any packing basis `b`, and from `eq(r, ·)` to any high weight `g`** (rev. 3.4: the
  lincheck's weighted claim with `W_β`'s block weight; `g = eq(r, ·)` gives `Q̃_i(r)` by `mle`'s
  definition).
* New: **`ring_inj_basis`** — for any `GF(2)`-independent family `b : Fin n → L` with `|L| = 2^n`
  (any field of characteristic two), a nonzero `δ ∈ L^n` has some `Σ_i b_i δ_i^(2^k) ≠ 0`, `k < n`
  (the Moore matrix of `b` kills no nonzero vector: a left kernel vector `c` gives the linearised
  polynomial `Σ_j c_j X^(2^j)` of degree `< 2^n` vanishing on all `2^n` subset sums of `b`).
  spartan-srom's cubic-extension `ring_inj`, `frob_sums_eq_zero`, `ybasis_of_period` are dropped.
* At F: `bitF`, `bitBasis` (A.7's pack), `bitBasis_indep`, **`ring_inj_F`** (`n = 128`),
  `unpack` with **`unpack_boolean`** (definitional, BP-C-m6) and `pack_unpack`.
* The doom chain of one claim (from spartan-srom's `SoundnessSpartan`, generalised to `b`):
  `rsDoom`, `rs_start`, `rs_escape_le` (≤ 1 bad `f_p`), `rs_end`.
* **Row RS1** (rev. 3.2, P1-D6: all `J_z` claims on `ẑ` switched together, then `κ`-batched into
  Ligerito's weight): `rs_column` (a false claim that passes the column check `Σ_i c_i s_i = v`
  has wrong partials; `c` is the claim's low weight: `eq(r_lo, ·)` for a multilinear claim,
  `ml_claim_split`, or the skip Lagrange weights for the quirky one, `FRSpartan.quirky_claim_split`),
  `rsJDoom`, `rsJ_escape_le`, and **`rs1_joint`**: at most `(7 + J − 1)·|F|^7` of the draws
  `(f_0 … f_6, κ) ∈ F^8` let the batched switched claim `Σ_j κ^j T_j` be true (`seq_bad_le` over the
  stages, then `batch_pow_bad_le` for `κ`).
-/

namespace FR

open Finset

/-! ## The staged map (copied)

Copied from leanerVM, https://github.com/Verified-zkEVM/leanerVM, commit
`532ebb457a6bc95e9e9f3b442e17bb7d5a03e372`, file
`LeanerVM/Protocol/ToArkLib/Flock/FrobeniusMap.lean` (Apache-2.0): `frobMap`, `frobTerms`,
`frobMap_eq_sum`, `frobMap_append`, `frobMap_add`, `frobMap_zero`, `frobMapHom`, `frobPair`,
`frobPair_stage`, `card_frob_root_le_one`, `card_stage_zero_le_one`. Changes: the namespace, no
`module`/`public` (this repository does not use the module system). -/

section Copied

variable {R : Type*} [CommRing R]

/-- The staged map: each stage `(s, f)` sends `a` to `a + f · a ^ 2 ^ s`, in order. -/
def frobMap : List (ℕ × R) → R → R
  | [], a => a
  | (s, f) :: st, a => frobMap st (a + f * a ^ 2 ^ s)

/-- The terms `(c, e)` of the staged map as a sum of Frobenius powers `c · a ^ 2 ^ e`. -/
def frobTerms : List (ℕ × R) → List (R × ℕ)
  | [] => [(1, 0)]
  | (s, f) :: st => (frobTerms st).flatMap fun t ↦ [(t.1, t.2), (t.1 * f ^ 2 ^ t.2, s + t.2)]

variable [CharP R 2]

/-- **L-R5.** The staged map is the sum of its terms: `frobMap st a = Σ_{(c, e)} c · a ^ 2 ^ e`. -/
theorem frobMap_eq_sum (st : List (ℕ × R)) (a : R) :
    frobMap st a = ((frobTerms st).map fun t ↦ t.1 * a ^ 2 ^ t.2).sum := by
  induction st generalizing a with
  | nil => simp [frobMap, frobTerms]
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    rw [frobMap, ih, frobTerms]
    generalize frobTerms st = L
    induction L with
    | nil => simp
    | cons t L ihL =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.map_nil, List.sum_nil, add_zero, ihL]
      rw [add_pow_char_pow, mul_pow, ← pow_mul, ← pow_add]
      ring

omit [CharP R 2] in
/-- Stages in sequence: the later list applies after the earlier. -/
theorem frobMap_append (st₁ st₂ : List (ℕ × R)) (a : R) :
    frobMap (st₁ ++ st₂) a = frobMap st₂ (frobMap st₁ a) := by
  induction st₁ generalizing a with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    exact ih _

/-- The staged map is additive. -/
theorem frobMap_add (st : List (ℕ × R)) (a b : R) :
    frobMap st (a + b) = frobMap st a + frobMap st b := by
  induction st generalizing a b with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    simp only [frobMap]
    rw [← ih, add_pow_char_pow]
    congr 1
    ring

omit [CharP R 2] in
/-- The staged map sends `0` to `0`. -/
theorem frobMap_zero (st : List (ℕ × R)) : frobMap st 0 = 0 := by
  induction st with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    simp only [frobMap]
    rw [zero_pow (pow_ne_zero _ two_ne_zero), mul_zero, add_zero, ih]

/-- The staged map as an additive homomorphism. -/
def frobMapHom (st : List (ℕ × R)) : R →+ R where
  toFun := frobMap st
  map_zero' := frobMap_zero st
  map_add' := frobMap_add st

omit [CharP R 2] in
/-- `π_k(b) = Σ_i w_i · b_i ^ 2 ^ k`. -/
def frobPair {ι : Type*} (s : Finset ι) (w b : ι → R) (k : ℕ) : R :=
  ∑ i ∈ s, w i * b i ^ 2 ^ k

/-- One stage with shift `M` and coefficient `f` sends `π_k` to `π_k + f ^ 2 ^ k · π_{M + k}`. -/
theorem frobPair_stage {ι : Type*} (s : Finset ι) (w b : ι → R) (M : ℕ) (f : R) (k : ℕ) :
    frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k =
      frobPair s w b k + f ^ 2 ^ k * frobPair s w b (M + k) := by
  simp only [frobPair, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [add_pow_char_pow, mul_pow, ← pow_mul, ← pow_add]
  ring

end Copied

section CopiedField

/-- `a + f ^ 2 ^ k · b = 0` with `(a, b) ≠ (0, 0)` has one root `f` at most, in a field of
characteristic two. -/
theorem card_frob_root_le_one {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    (k : ℕ) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    (Finset.univ.filter fun f : F ↦ a + f ^ 2 ^ k * b = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun f₁ h₁ f₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [mul_zero, add_zero] at h₁
    exact hab.elim (· h₁.2) (· rfl)
  have heq : f₁ ^ 2 ^ k = f₂ ^ 2 ^ k :=
    mul_right_cancel₀ hb (add_left_cancel (h₁.2.trans h₂.2.symm))
  exact iterateFrobenius_inj F 2 k heq

/-- **L-R2 (copied form). One bad coefficient at most.** If some `π_k`, `k < 2M`, of the family
is nonzero, then after one stage with shift `M` every `π_k`, `k < M`, vanishes for one coefficient
at most. -/
theorem card_stage_zero_le_one {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    {ι : Type*} (s : Finset ι) (w b : ι → F) (M : ℕ) (h : ∃ k < 2 * M, frobPair s w b k ≠ 0) :
    (Finset.univ.filter fun f : F ↦
      ∀ k < M, frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k = 0).card ≤ 1 := by
  obtain ⟨k₀, hk₀, hne⟩ := h
  -- The index below `M` whose pair of values is nonzero.
  obtain ⟨k, hk, hab⟩ : ∃ k < M, frobPair s w b k ≠ 0 ∨ frobPair s w b (M + k) ≠ 0 := by
    by_cases hlt : k₀ < M
    · exact ⟨k₀, hlt, Or.inl hne⟩
    · refine ⟨k₀ - M, by omega, Or.inr ?_⟩
      rwa [show M + (k₀ - M) = k₀ by omega]
  refine (Finset.card_le_card fun f hf ↦ ?_).trans (card_frob_root_le_one k hab)
  rw [Finset.mem_filter] at hf ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← frobPair_stage]
  exact hf.2 k hk

end CopiedField

/-! ## The stages of `Φ` -/

variable {R : Type*} [CommRing R]

/-- The stages for the coefficients `fs`: stage `p` is `(2 ^ (s' - p), f_p)`. -/
def stages (s' : ℕ) (fs : List R) : List (ℕ × R) := fs.mapIdx fun p f ↦ (2 ^ (s' - p), f)

omit [CommRing R] in
theorem stages_cons (s' : ℕ) (f : R) (fs : List R) :
    stages s' (f :: fs) = (2 ^ s', f) :: stages (s' - 1) fs := by
  rw [stages, List.mapIdx_cons, stages]
  congr 1
  refine List.mapIdx_eq_mapIdx_iff.mpr fun i h ↦ ?_
  simp only [Prod.mk.injEq, and_true]
  rw [show s' - (i + 1) = s' - 1 - i by omega]

omit [CommRing R] in
/-- One more coefficient is one more stage, with shift `2 ^ (s' - p)`. -/
theorem stages_append (s' : ℕ) (fs : List R) (f : R) :
    stages s' (fs ++ [f]) = stages s' fs ++ [(2 ^ (s' - fs.length), f)] := by
  simp [stages, List.mapIdx_append]

/-- `Φ` for the coefficients `fs`: all `|fs|` stages, shifts `2 ^ (|fs| - 1), …, 2, 1`. -/
def Phi (fs : List R) : R → R := frobMap (stages (fs.length - 1) fs)

/-- With every coefficient zero, `Φ` is the identity (§10.1 positive control). -/
theorem frobMap_stages_zeros (s' m : ℕ) (a : R) :
    frobMap (stages s' (List.replicate m (0 : R))) a = a := by
  induction m generalizing s' with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, stages_cons, frobMap, zero_mul, add_zero, ih]

/-! ## Computable code -/

/-- `n` squarings: `a ^ 2 ^ n`. -/
@[specialize]
def sqIter : ℕ → R → R
  | 0, a => a
  | n + 1, a => sqIter n (a * a)

theorem sqIter_eq (n : ℕ) (a : R) : sqIter n a = a ^ 2 ^ n := by
  induction n generalizing a with
  | zero => simp [sqIter]
  | succ n ih => rw [sqIter, ih, ← sq, ← pow_mul, pow_succ']

theorem sqIter_succ' (n : ℕ) (a : R) : sqIter (n + 1) a = sqIter n a * sqIter n a := by
  rw [sqIter_eq, sqIter_eq, ← sq, ← pow_mul, pow_succ]

/-- The staged map with squarings. -/
@[specialize]
def frobMapC : List (ℕ × R) → R → R
  | [], a => a
  | (s, f) :: st, a => frobMapC st (a + f * sqIter s a)

theorem frobMapC_eq (st : List (ℕ × R)) (a : R) : frobMapC st a = frobMap st a := by
  induction st generalizing a with
  | nil => rfl
  | cons p st ih => obtain ⟨s, f⟩ := p; rw [frobMapC, frobMap, ih, sqIter_eq]

/-- `Φ(a)`, computed: `63` squarings and `6` multiplications for six stages. -/
@[specialize]
def phiApply (fs : List R) (a : R) : R := frobMapC (stages (fs.length - 1) fs) a

theorem phiApply_eq (fs : List R) (a : R) : phiApply fs a = Phi fs a := frobMapC_eq _ _

/-- The coefficients `c_k` of `Φ(a) = Σ_k c_k · a ^ 2 ^ k`, `2 ^ |fs|` of them: the table of the
later stages, then the same table times `f ^ 2 ^ e`. -/
@[specialize]
def phiTable : List R → Array R
  | [] => #[1]
  | f :: fs =>
    let t := phiTable fs
    t ++ Array.ofFn (n := t.size) fun e ↦ t[e] * sqIter e.val f

theorem phiTable_size (fs : List R) : (phiTable fs).size = 2 ^ fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [phiTable, ih, pow_succ, mul_two]

theorem getD_append (xs ys : Array R) (i : ℕ) :
    (xs ++ ys).getD i 0 = if i < xs.size then xs.getD i 0 else ys.getD (i - xs.size) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split_ifs <;> rfl

/-- **L-R5, dense form.** `Φ(a) = Σ_{k < 2^|fs|} c_k · a ^ 2 ^ k`. -/
theorem Phi_eq_table [CharP R 2] (fs : List R) (a : R) :
    Phi fs a = ∑ k ∈ range (2 ^ fs.length), (phiTable fs).getD k 0 * a ^ 2 ^ k := by
  induction fs generalizing a with
  | nil => simp [Phi, stages, frobMap, phiTable]
  | cons f fs ih =>
    have hs := phiTable_size fs
    rw [Phi, List.length_cons, Nat.add_sub_cancel, stages_cons, frobMap, ← Phi, ih,
      pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    have hk' : k < (phiTable fs).size := hs ▸ hk
    rw [phiTable, getD_append, ite_eq_left hk', getD_append, ite_eq_right (by omega),
      Nat.sub_eq_of_eq_add (by omega : 2 ^ fs.length + k = k + (phiTable fs).size), getD_ofFn,
      dite_eq_left (by omega), add_pow_char_pow, mul_add, mul_pow,
      ← pow_mul, ← pow_add, sqIter_eq]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk', Option.getD_some,
      Fin.getElem_fin]
    ring

/-- The target `T = Σ_i x^i · Φ(s_i)` (Horner in `x`). -/
@[specialize]
def target (x : R) (fs : List R) (s : Array R) : R := peval (s.map (phiApply fs)) x

theorem target_eq (x : R) (fs : List R) (s : Array R) :
    target x fs s = ∑ i ∈ range s.size, x ^ i * Phi fs (s.getD i 0) := by
  rw [target, peval_eq_sum, Array.size_map]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, phiApply_eq, mul_comm]

/-- The prover's weight table `W(u') = Φ(eq(r, u'))`. -/
@[specialize]
def weightTable (fs r : List R) : Array R := (eqTable r).map (phiApply fs)

/-- `W̃(r'') = Σ_k c_k · eq(r ^ 2 ^ k, r'')`, the point squared once per `k`. -/
@[specialize]
def weightEval (fs r r'' : List R) : R :=
  let c := phiTable fs
  (Nat.fold c.size (fun k _ (p : R × List R) ↦
    (p.1 + c.getD k 0 * eqPts p.2 r'', p.2.map fun a ↦ a * a)) (0, r)).1

theorem weightEval_fold (c : Array R) (r r'' : List R) (n : ℕ) :
    Nat.fold n (fun k _ (p : R × List R) ↦
      (p.1 + c.getD k 0 * eqPts p.2 r'', p.2.map fun a ↦ a * a)) (0, r) =
    (∑ k ∈ range n, c.getD k 0 * eqPts (r.map (sqIter k)) r'', r.map (sqIter n)) := by
  induction n with
  | zero => simp [sqIter]
  | succ n ih =>
    rw [Nat.fold_succ, ih, Finset.sum_range_succ, List.map_map]
    congr 2
    funext a
    simp [sqIter_succ']

theorem weightEval_eq (fs r r'' : List R) :
    weightEval fs r r'' =
      ∑ k ∈ range (2 ^ fs.length), (phiTable fs).getD k 0 * eqPts (r.map (sqIter k)) r'' := by
  rw [weightEval, weightEval_fold, phiTable_size]

/-! ## L-R4: the weight's extension -/

/-- **L-R4.** `W̃(r'') = Σ_k c_k · eq(r ^ 2 ^ k, r'')` for `W(u) = Φ(eq(r, u))`. -/
theorem weight_mle [CharP R 2] {ℓ : ℕ} (fs : List R) (r r'' : Fin ℓ → R) :
    mle (fun u ↦ Phi fs (eq r (cube u))) r'' =
      ∑ k ∈ range (2 ^ fs.length), (phiTable fs).getD k 0 * eq (fun l ↦ r l ^ 2 ^ k) r'' := by
  simp only [mle, Phi_eq_table, eq_frob, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [eq_swap _ r'', ← eq_mle r'' (fun l ↦ r l ^ 2 ^ k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [eq_swap (cube u) (fun l ↦ r l ^ 2 ^ k)]
  ring

/-- **The verifier's `W̃` is the extension of the prover's table** (points of length `ℓ`). -/
theorem mleEval_weightTable [CharP R 2] {ℓ : ℕ} (fs r r'' : List R) (hr : r.length = ℓ)
    (hr'' : r''.length = ℓ) : mleEval (weightTable fs r) r'' = weightEval fs r r'' := by
  have htbl : tbl ℓ (weightTable fs r) = fun u ↦ Phi fs (eq (ptOf ℓ r) (cube u)) := by
    funext u
    rw [← congrFun (tbl_eqTable' r hr) u, ← phiApply_eq]
    have hu : u.val < (eqTable r).size := by rw [eqTable_size, hr]; exact u.isLt
    simp [tbl, weightTable, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu]
  rw [mleEval_eq' _ _ hr'', htbl, weight_mle, weightEval_eq]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [eqPts_eq _ _ (by simp [hr]) hr'']
  congr 2
  funext l
  simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases r[l.val]? <;> simp [sqIter_eq]

/-! ## Revision 3.16 (R-V-M1): the kind-weighted claim's weight

RS claim 2 (Lc, node) has the outer weight `g(y) = eq(p, y)·B_β(t(y))`, `t(y)` the block bits of
`y` and `B_β = Σ_κ β^κ Ind_κ` (§2.3 step 3's `W_β`). `rsWeight_kind_eq` is A.8's Φ form of its
extension: `Φ` is `F₂`-linear, `eq(p, u)^(2^k) = eq(p^(2^k), u)` on the cube and, for 0/1
indicators, `B_β^(2^k) = Σ_κ β^(κ·2^k) Ind_κ` in characteristic two. -/

/-- The high `b` bits of an index of `Fin (2 ^ (a + b))` (`join`'s second argument). -/
def hiIdx {a b : ℕ} (y : Fin (2 ^ (a + b))) : Fin (2 ^ b) :=
  ⟨y.val / 2 ^ a, Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact y.isLt)⟩

theorem hiIdx_join {a b : ℕ} (u₁ : Fin (2 ^ a)) (u₂ : Fin (2 ^ b)) : hiIdx (join u₁ u₂) = u₂ := by
  ext
  simp only [hiIdx, join]
  rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt u₁.isLt, add_zero]

/-- **The kind factor** `B_β(t) = Σ_κ β^κ Ind_κ(t)` (§2.3 step 3). -/
def kindFac {b n : ℕ} (Ind : Fin n → Fin (2 ^ b) → R) (β : R) (t : Fin (2 ^ b)) : R :=
  ∑ κ, β ^ κ.val * Ind κ t

theorem kindFac_frob [CharP R 2] {b n : ℕ} (Ind : Fin n → Fin (2 ^ b) → R)
    (hInd : ∀ κ t, Ind κ t = 0 ∨ Ind κ t = 1) (β : R) (t : Fin (2 ^ b)) (k : ℕ) :
    kindFac Ind β t ^ 2 ^ k = ∑ κ, β ^ (κ.val * 2 ^ k) * Ind κ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [kindFac, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [mul_pow, ← pow_mul]
  rcases hInd κ t with h | h <;> rw [h]
  · rw [zero_pow (pow_ne_zero _ two_ne_zero)]
  · rw [one_pow]

/-- **`rsWeight_kind_eq`** (revision 3.16, R-V-M1 (a)): the extension at `ρ = (ρ₁, ρ₂)` of the
weight table `y ↦ Φ(eq(p, y)·B_β(t(y)))`, `p = (p₁, p₂)` (`p₂`, `ρ₂`: the block coordinates), is
A.8's pattern-interval sum `Σ_k c_k Σ_κ β^(κ·2^k) eq(p₁^(2^k), ρ₁) Σ_{t ∈ I_κ} eq(p₂^(2^k), t)
eq(ρ₂, t)`, for any 0/1 indicators `Ind_κ` (disjointness is not needed). -/
theorem rsWeight_kind_eq [CharP R 2] {a b n : ℕ} (fs : List R) (Ind : Fin n → Fin (2 ^ b) → R)
    (hInd : ∀ κ t, Ind κ t = 0 ∨ Ind κ t = 1) (β : R) (p₁ ρ₁ : Fin a → R) (p₂ ρ₂ : Fin b → R) :
    mle (fun y ↦ Phi fs (eq (Fin.append p₁ p₂) (cube y) * kindFac Ind β (hiIdx y)))
        (Fin.append ρ₁ ρ₂) =
      ∑ k ∈ range (2 ^ fs.length), (phiTable fs).getD k 0 * ∑ κ, β ^ (κ.val * 2 ^ k) *
        eq (fun l ↦ p₁ l ^ 2 ^ k) ρ₁ *
          ∑ t, Ind κ t * eq (fun l ↦ p₂ l ^ 2 ^ k) (cube t) * eq ρ₂ (cube t) := by
  have hE : ∀ k : ℕ, eq (fun l ↦ p₁ l ^ 2 ^ k) ρ₁ =
      ∑ u₁ : Fin (2 ^ a), eq ρ₁ (cube u₁) * eq (fun l ↦ p₁ l ^ 2 ^ k) (cube u₁) := fun k ↦ by
    rw [← eq_mle (fun l ↦ p₁ l ^ 2 ^ k) ρ₁]
    exact Finset.sum_congr rfl fun u _ ↦ by rw [eq_swap (cube u) ρ₁]; ring
  rw [mle_split]
  simp only [eq_append_join, hiIdx_join, mle, Phi_eq_table, mul_pow, eq_frob,
    kindFac_frob Ind hInd]
  conv_rhs => simp only [hE, Finset.mul_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun u₁ _ ↦ Finset.sum_comm.trans
    (Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm)).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u₂ _ ↦ Finset.sum_congr rfl fun u₁ _ ↦ by ring

/-! ## L-R3: completeness, and the error of the switched claim -/

section Switch

variable {K E : Type*} [CommRing K] [CommRing E] [Algebra K E]

/-- **Completeness.** For Boolean bit-planes `Q_i` packed as `q(u) = Σ_i Q_i(u) · b_i ∈ K`, any
additive `Φ` and any high weight `g` (`eq(r, ·)` for an evaluation claim, so the partials are
`Q̃_i(r)`; `W_β`'s block weight for the lincheck's weighted claim, rev. 3.4),
`Σ_u Φ(g(u)) · q(u) = Σ_i b_i · Φ(Σ_u g(u) Q_i(u))`. -/
theorem ring_complete {n ℓ : ℕ} (Φ : E →+ E) (b : Fin n → K) (Q : Fin n → Fin (2 ^ ℓ) → K)
    (hQ : ∀ i u, Q i u = 0 ∨ Q i u = 1) (g : Fin (2 ^ ℓ) → E) :
    ∑ u, Φ (g u) * algebraMap K E (∑ i : Fin n, Q i u * b i) =
      ∑ i : Fin n, algebraMap K E (b i) * Φ (∑ u, g u * algebraMap K E (Q i u)) := by
  have hbit : ∀ i u, Φ (g u * algebraMap K E (Q i u)) =
      algebraMap K E (Q i u) * Φ (g u) := fun i u ↦ by
    rcases hQ i u with h | h <;> simp [h]
  simp only [map_sum, hbit, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **The switched claim's error.** `T - Σ_u Φ(g(u)) · q(u)` is `π_0` of the family
`Φ(s_i - Σ_u g(u) Q_i(u))` with weights `b_i`: the claim handed on is true exactly when this `π_0`
vanishes (the end of the stages). -/
theorem ring_final {n ℓ : ℕ} (Φ : E →+ E) (b : Fin n → K) (Q : Fin n → Fin (2 ^ ℓ) → K)
    (hQ : ∀ i u, Q i u = 0 ∨ Q i u = 1) (g : Fin (2 ^ ℓ) → E) (s : Fin n → E) :
    (∑ i : Fin n, algebraMap K E (b i) * Φ (s i)) -
        ∑ u, Φ (g u) * algebraMap K E (∑ i : Fin n, Q i u * b i) =
      frobPair univ (fun i : Fin n ↦ algebraMap K E (b i))
        (fun i ↦ Φ (s i - ∑ u, g u * algebraMap K E (Q i u))) 0 := by
  rw [ring_complete Φ b Q hQ g, ← Finset.sum_sub_distrib, frobPair]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pow_zero, pow_one, map_sub, mul_sub]

end Switch

/-! ## L-R2: one stage at a time -/

/-- **L-R2 (protocol form).** After `p = |fs| ≤ s'` coefficients, a family with some
`π_k ≠ 0`, `k < 2 ^ (s' + 1 - p)`, keeps some `π_k ≠ 0`, `k < 2 ^ (s' - p)`, after the next
coefficient `f`, for every `f` but at most one. -/
theorem stage_bad_le_one {E : Type*} [Field E] [Fintype E] [DecidableEq E] [CharP E 2]
    {ι : Type*} (s : Finset ι) (w δ : ι → E) (s' : ℕ) (fs : List E) (hp : fs.length ≤ s')
    (h : ∃ k < 2 ^ (s' + 1 - fs.length),
      frobPair s w (fun i ↦ frobMap (stages s' fs) (δ i)) k ≠ 0) :
    (univ.filter fun f ↦ ∀ k < 2 ^ (s' - fs.length),
      frobPair s w (fun i ↦ frobMap (stages s' (fs ++ [f])) (δ i)) k = 0).card ≤ 1 := by
  have h2 : 2 ^ (s' + 1 - fs.length) = 2 * 2 ^ (s' - fs.length) := by
    rw [show s' + 1 - fs.length = (s' - fs.length) + 1 by omega, pow_succ, mul_comm]
  rw [h2] at h
  refine le_of_eq_of_le ?_ (card_stage_zero_le_one s w _ _ h)
  congr 1
  refine Finset.filter_congr fun f _ ↦ ?_
  simp only [stages_append, frobMap_append, frobMap]

/-! ## Injectivity of ring switching over `GF(2)` -/

section Inj

open Polynomial

/-- `GF(2)`-independence of a family: no nonempty subfamily sums to zero. -/
def GF2Indep {L : Type*} [AddCommMonoid L] {n : ℕ} (b : Fin n → L) : Prop :=
  ∀ T : Finset (Fin n), ∑ i ∈ T, b i = 0 → T = ∅

/-- In characteristic two, independent families have injective subset sums. -/
theorem subsetSum_injective {L : Type*} [CommRing L] [CharP L 2] {n : ℕ} {b : Fin n → L}
    (hb : GF2Indep b) : Function.Injective fun T : Finset (Fin n) ↦ ∑ i ∈ T, b i := by
  intro T T' h
  simp only at h
  have h1 := Finset.sum_sdiff (f := b) (Finset.inter_subset_left (s₁ := T) (s₂ := T'))
  have h2 := Finset.sum_sdiff (f := b) (Finset.inter_subset_right (s₁ := T) (s₂ := T'))
  rw [Finset.sdiff_inter_self_left] at h1
  rw [Finset.sdiff_inter_self_right] at h2
  have hd : ∑ i ∈ (T \ T') ∪ (T' \ T), b i = 0 := by
    rw [Finset.sum_union disjoint_sdiff_sdiff]
    have : ∑ i ∈ T \ T', b i = ∑ i ∈ T' \ T, b i := by
      have := h1.trans (h.trans h2.symm); exact add_right_cancel this
    rw [this, CharTwo.add_self_eq_zero]
  have he := hb _ hd
  rw [Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset,
    Finset.sdiff_eq_empty_iff_subset] at he
  exact Finset.Subset.antisymm he.1 he.2

/-- **Ring-switching injectivity for `GF(2) ⊂ L`**, any `GF(2)`-basis `b` of `L` (`|L| = 2^n`):
a nonzero family `δ ∈ L^n` has `Σ_i b_i δ_i^(2^k) ≠ 0` for some `k < n`. -/
theorem ring_inj_basis {L : Type*} [Field L] [Fintype L] [CharP L 2] {n : ℕ}
    (hcard : Fintype.card L = 2 ^ n) (b : Fin n → L) (hb : GF2Indep b) (δ : Fin n → L)
    (hδ : δ ≠ 0) : ∃ k < n, ∑ i, b i * δ i ^ 2 ^ k ≠ 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  have hpow : ∀ a : L, a ^ 2 ^ n = a := fun a ↦ by
    have := FiniteField.pow_card a; rwa [hcard] at this
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (_root_.funext fun i : Fin 0 ↦ i.elim0) hδ
    · exact h
  -- the Moore matrix `M j i = b_i ^ 2^j` kills `δ`
  set M : Matrix (Fin n) (Fin n) L := fun j i ↦ b i ^ 2 ^ (j : ℕ) with hM
  have hMδ : M.mulVec δ = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, hM, Pi.zero_apply]
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
    · simpa [hj] using hall 0 hn
    · have h := congrArg (· ^ 2 ^ (j : ℕ)) (hall (n - j) (by omega))
      simp only [zero_pow (pow_ne_zero _ two_ne_zero), sum_pow_char_pow] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel j.isLt.le, hpow]
  obtain ⟨c, hc, hcM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr
    (Matrix.exists_mulVec_eq_zero_iff.mp ⟨δ, hδ, hMδ⟩)
  -- the linearised polynomial `P = Σ_j c_j X^(2^j)` vanishes on all subset sums of `b`
  set P : L[X] := ∑ j : Fin n, C (c j) * X ^ 2 ^ (j : ℕ) with hP
  have hPb : ∀ i, P.eval (b i) = 0 := fun i ↦ by
    have := congrFun hcM i
    simpa [hP, eval_finsetSum, Matrix.vecMul, dotProduct, hM] using this
  have hPT : ∀ T : Finset (Fin n), P.eval (∑ i ∈ T, b i) = 0 := fun T ↦ by
    simp only [hP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, sum_pow_char_pow,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have := hPb i
    simpa [hP, eval_finsetSum] using this
  have hdeg : P.natDegree < Fintype.card (Finset (Fin n)) := by
    rw [Fintype.card_finset, Fintype.card_fin]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := 2 ^ (n - 1)) fun j _ ↦ ?_) ?_
    · refine (natDegree_C_mul_X_pow_le _ _).trans (Nat.pow_le_pow_right two_pos (by omega))
    · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hP0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (subsetSum_injective hb) hPT hdeg
  refine hc (funext fun j ↦ ?_)
  have := congrArg (fun p : L[X] ↦ p.coeff (2 ^ (j : ℕ))) hP0
  simp only [hP, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single j (fun j' _ hj' ↦ ite_eq_right fun h ↦ hj' (Fin.ext
    (Nat.pow_right_injective le_rfl h).symm)) (by simp), ite_eq_left rfl] at this
  exact this

end Inj

/-! ## The R1 doom chain (spartan-srom's `SoundnessSpartan` R5, generalised to the basis `b`) -/

section Doom

variable {E : Type*} [Field E]

/-- The ring-switching doom after the coefficients `fs`: some `π_k ≠ 0`, `k < 2 ^ (s' + 1 - p)`,
of the family `δ` after the first `p = |fs|` stages. -/
def rsDoom {n : ℕ} (w δ : Fin n → E) (s' : ℕ) (fs : List E) : Prop :=
  ∃ k < 2 ^ (s' + 1 - fs.length), frobPair univ w (fun i ↦ frobMap (stages s' fs) (δ i)) k ≠ 0

/-- **Start of R5.** L-R1's conclusion (`ring_inj`, `ring_inj_EF`) is the doom before any
coefficient. -/
theorem rs_start {n : ℕ} (w δ : Fin n → E) (s' : ℕ)
    (h : ∃ k < 2 ^ (s' + 1), ∑ i, w i * δ i ^ 2 ^ k ≠ 0) : rsDoom w δ s' [] := h

open scoped Classical in
/-- **R5, one coefficient.** From a doomed state at most one coefficient escapes. -/
theorem rs_escape_le [CharP E 2] [Fintype E] [DecidableEq E] {n : ℕ} (w δ : Fin n → E)
    (s' : ℕ) (fs : List E) (hp : fs.length ≤ s') (h : rsDoom w δ s' fs) :
    (univ.filter fun f ↦ ¬rsDoom w δ s' (fs ++ [f])).card ≤ 1 := by
  convert stage_bad_le_one univ w δ s' fs hp h using 2
  ext f
  simp only [rsDoom, List.length_append, List.length_singleton, not_exists, not_and, not_not,
    Nat.add_sub_add_right, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **End of R5.** Doom after all `s' + 1` coefficients means the switched claim is false:
`T = Σ_i b_i Φ(s_i) ≠ Σ_u Φ(g(u)) · q(u)` for the slices' errors `δ_i = s_i - Σ_u g(u) Q_i(u)`. -/
theorem rs_end [CharP E 2] {K : Type*} [CommRing K] [Algebra K E] {n ℓ : ℕ} (b : Fin n → K)
    (Q : Fin n → Fin (2 ^ ℓ) → K) (hQ : ∀ i u, Q i u = 0 ∨ Q i u = 1) (g : Fin (2 ^ ℓ) → E)
    (s : Fin n → E) (s' : ℕ) (fs : List E) (hlen : fs.length = s' + 1)
    (h : rsDoom (fun i ↦ algebraMap K E (b i))
      (fun i ↦ s i - ∑ u, g u * algebraMap K E (Q i u)) s' fs) :
    ∑ i : Fin n, algebraMap K E (b i) * Phi fs (s i) ≠
      ∑ u, Phi fs (g u) * algebraMap K E (∑ i : Fin n, Q i u * b i) := by
  obtain ⟨k, hk, hne⟩ := h
  rw [hlen, Nat.sub_self, pow_zero, Nat.lt_one_iff] at hk
  subst hk
  have hPhi : Phi fs = frobMap (stages s' fs) := by rw [Phi, hlen, Nat.add_sub_cancel]
  intro heq
  apply hne
  have := ring_final (frobMapHom (stages s' fs)) b Q hQ g s
  simp only [frobMapHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ← hPhi] at this ⊢
  rw [← this, heq, sub_self]

end Doom

/-! ## At F: the pack of BLUEPRINT A.7 -/

/-- Bit `j < 128` of an F element in A.7's pack order: bit `j` of `c₀` for `j < 64`, bit `j − 64`
of `c₁` above. -/
def bitF (a : F) (j : Fin 128) : Bool :=
  if j.val < 64 then a.c₀.val.toBitVec.getLsbD j.val else a.c₁.val.toBitVec.getLsbD (j.val - 64)

/-- The packing basis (A.7): `bitBasis i` has the one bit `i` set, i.e. `x^i` for `i < 64` and
`x^(i − 64) y` above. -/
def bitBasis (i : Fin 128) : F :=
  if i.val < 64 then ⟨⟨UInt64.ofNat (2 ^ i.val)⟩, 0⟩ else ⟨0, ⟨UInt64.ofNat (2 ^ (i.val - 64))⟩⟩

theorem bitF_add (a b : F) (j : Fin 128) : bitF (a + b) j = (bitF a j ^^ bitF b j) := by
  have h0 : (a + b).c₀.val = a.c₀.val ^^^ b.c₀.val := rfl
  have h1 : (a + b).c₁.val = a.c₁.val ^^^ b.c₁.val := rfl
  simp only [bitF, h0, h1, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  split_ifs <;> rfl

theorem bitF_zero (j : Fin 128) : bitF 0 j = false := by
  have h0 : (0 : F).c₀.val = 0 := rfl
  have h1 : (0 : F).c₁.val = 0 := rfl
  simp only [bitF, h0, h1, UInt64.toBitVec_zero, BitVec.getLsbD_zero]
  split_ifs <;> rfl

theorem bitF_bitBasis (i j : Fin 128) : bitF (bitBasis i) j = decide (i = j) := by
  have h0 : (0 : B64).val = 0 := rfl
  have hj := j.isLt; have hi := i.isLt
  simp only [bitF, bitBasis, Fin.ext_iff]
  split_ifs with h1 h2 h2 <;>
    simp only [h0, UInt64.toBitVec_ofNat', BitVec.getLsbD_ofNat, Nat.testBit_two_pow,
      UInt64.toBitVec_zero]
  all_goals
    try simp only [Nat.zero_testBit, Bool.and_false]
    apply Bool.eq_iff_iff.mpr
    try simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, false_iff]
    omega

theorem bitF_sum (T : Finset (Fin 128)) (j : Fin 128) :
    bitF (∑ i ∈ T, bitBasis i) j = decide (j ∈ T) := by
  induction T using Finset.induction_on with
  | empty => simp [bitF_zero]
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, bitF_add, ih, bitF_bitBasis]
    by_cases h : j = i
    · subst h; simp [hi]
    · simp [h, Ne.symm h]

/-- Two F elements with the same bits are equal. -/
theorem eq_of_bitF {a b : F} (h : ∀ j, bitF a j = bitF b j) : a = b := by
  obtain ⟨⟨a₀⟩, ⟨a₁⟩⟩ := a
  obtain ⟨⟨b₀⟩, ⟨b₁⟩⟩ := b
  have e₀ : a₀ = b₀ := UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun k hk ↦ by
    have := h ⟨k, by omega⟩; simpa [bitF, hk] using this)
  have e₁ : a₁ = b₁ := UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun k hk ↦ by
    have := h ⟨k + 64, by omega⟩; simpa [bitF] using this)
  rw [e₀, e₁]

/-- **The packing basis is `GF(2)`-independent.** -/
theorem bitBasis_indep : GF2Indep bitBasis := fun T hT ↦ by
  ext j
  have := bitF_sum T j
  rw [hT, bitF_zero] at this
  simpa using this.symm

/-- **`ring_inj` for `GF(2) ⊂ F` with 128 limbs** (row R1): a nonzero family of slice errors has
some Frobenius-twisted sum `Σ_i b_i δ_i^(2^k) ≠ 0`, `k < 128`. -/
theorem ring_inj_F (δ : Fin 128 → F) (hδ : δ ≠ 0) :
    ∃ k < 128, ∑ i, bitBasis i * δ i ^ 2 ^ k ≠ 0 :=
  ring_inj_basis F.card_F bitBasis bitBasis_indep δ hδ

/-- The bit `i` of `a` as an element of F: the unpacked witness. -/
def unpack (a : F) (i : Fin 128) : F := if bitF a i then 1 else 0

/-- **The unpacked witness is Boolean by definition** (BP-C-m6). -/
theorem unpack_boolean (a : F) (i : Fin 128) : unpack a i = 0 ∨ unpack a i = 1 := by
  unfold unpack; split_ifs <;> simp

/-- **Packing the unpacked bits gives the element back.** -/
theorem pack_unpack (a : F) : ∑ i, unpack a i * bitBasis i = a := by
  have hs : ∑ i, unpack a i * bitBasis i = ∑ i ∈ univ.filter (fun i ↦ bitF a i), bitBasis i := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ ↦ by unfold unpack; split_ifs <;> simp
  rw [hs]
  exact eq_of_bitF fun j ↦ by rw [bitF_sum]; simp

/-- **Start of R1 at F.** A wrong slice claim (`δ ≠ 0`) is a doomed state before the first of
the seven stage coefficients. -/
theorem rs_start_F (δ : Fin 128 → F) (hδ : δ ≠ 0) : rsDoom bitBasis δ 6 [] := by
  obtain ⟨k, hk, hne⟩ := ring_inj_F δ hδ
  exact rs_start _ _ _ ⟨k, by simpa using hk, hne⟩

/-! ## Row RS1: all `J` claims switched together, the joint bound -/

section RS1

variable {J ℓ : ℕ}

/-- **The column check** of one claim: the partials `s` pass `Σ_i c_i s_i = v` while the true
partials `Q̃_i(r)` do not; then the slice errors `δ = s − Q̃(r)` are nonzero. -/
theorem rs_column {c s t : Fin 128 → F} {v : F} (hchk : ∑ i, c i * s i = v)
    (hfalse : ∑ i, c i * t i ≠ v) : (fun i ↦ s i - t i) ≠ 0 := fun h ↦ hfalse (by
  rw [← hchk]; exact Finset.sum_congr rfl fun i _ ↦ by
    rw [sub_eq_zero.mp (congrFun h i)])

/-- A multilinear claim on `z` at `(r_lo, r_hi)` is the `eq(r_lo, ·)`-weighted sum of the bit-plane
claims `Q̃_i(r_hi)`, `Q_i(u) = z(i, u)` (the pack of A.7: the low 7 bits are the bit index). -/
theorem ml_claim_split (z : Fin (2 ^ (7 + ℓ)) → F) (rlo : Fin 7 → F) (rhi : Fin ℓ → F) :
    mle z (Fin.append rlo rhi) = ∑ i : Fin 128, eq rlo (cube (ℓ := 7) i) * mle (fun u ↦ z (join i u)) rhi :=
  mle_split z rlo rhi

/-- The joint doom after a prefix of stage coefficients: some claim's slice errors are doomed. -/
def rsJDoom (δ : Fin J → Fin 128 → F) (fs : List F) : Prop :=
  ∃ j, rsDoom (fun i ↦ algebraMap F F (bitBasis i)) (δ j) 6 fs

open scoped Classical in
/-- One stage coefficient escapes the joint doom for at most one value. -/
theorem rsJ_escape_le (δ : Fin J → Fin 128 → F) (fs : List F) (hp : fs.length ≤ 6)
    (h : rsJDoom δ fs) : (univ.filter fun f ↦ ¬rsJDoom δ (fs ++ [f])).card ≤ 1 := by
  obtain ⟨j, hj⟩ := h
  refine (Finset.card_le_card fun f hf ↦ ?_).trans (rs_escape_le _ (δ j) 6 fs hp hj)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rsJDoom, not_exists] at hf ⊢
  exact hf j

/-- The switched claim `T_j = Σ_i b_i Φ(s_{j,i})` after the stage coefficients `fs`. -/
def rsT (s : Fin J → Fin 128 → F) (fs : Fin 7 → F) (j : Fin J) : F :=
  ∑ i, algebraMap F F (bitBasis i) * Phi (List.ofFn fs) (s j i)

/-- Its true value `Σ_u Φ(eq(r_j, u)) · q(u)`, `q = pack Q`. -/
def rsTruth (Q : Fin 128 → Fin (2 ^ ℓ) → F) (g : Fin J → Fin (2 ^ ℓ) → F) (fs : Fin 7 → F)
    (j : Fin J) : F :=
  ∑ u, Phi (List.ofFn fs) (g j u) * algebraMap F F (∑ i, Q i u * bitBasis i)

open scoped Classical in
/-- **Row RS1, the joint bound** (rev. 3.2: `(7 + J_z − 1)/2^128`, one phase). If some claim's
partials are wrong (`δ_j ≠ 0`), then of the `|F|^8` draws `(f_0 … f_6, κ)` at most
`(7 + J − 1)·|F|^7` leave the batched switched claim `Σ_j κ^j T_j` equal to its true value. -/
theorem rs1_joint {J' : ℕ} (Q : Fin 128 → Fin (2 ^ ℓ) → F) (hQ : ∀ i u, Q i u = 0 ∨ Q i u = 1)
    (g : Fin (J' + 1) → Fin (2 ^ ℓ) → F) (s : Fin (J' + 1) → Fin 128 → F)
    (hδ : ∃ j, (fun i ↦ s j i - ∑ u, g j u * algebraMap F F (Q i u)) ≠ 0) :
    (univ.filter fun p : (Fin 7 → F) × F ↦
      ∑ j, p.2 ^ j.val * rsT s p.1 j = ∑ j, p.2 ^ j.val * rsTruth Q g p.1 j).card ≤
      (7 + J') * Fintype.card F ^ 7 := by
  set δ : Fin (J' + 1) → Fin 128 → F := fun j i ↦ s j i - ∑ u, g j u * algebraMap F F (Q i u)
  have hN : 0 < Fintype.card F := Fintype.card_pos
  -- the seven stages
  have hstart : rsJDoom δ [] := by
    obtain ⟨j, hj⟩ := hδ
    exact ⟨j, rs_start_F (δ j) hj⟩
  set N := Fintype.card F
  have hseq := seq_bad_le (rsJDoom δ) (fun n ↦ if n ≤ 6 then 1 else N) (fun l hl ↦ by
    by_cases hp : l.length ≤ 6
    · rw [ite_eq_left hp]; exact rsJ_escape_le δ l hp hl
    · rw [ite_eq_right hp]; exact Finset.card_le_univ _) 7 [] hstart
  simp only [List.nil_append, List.length_nil, zero_add] at hseq
  have h7 : ∑ i ∈ range 7, (if i ≤ 6 then 1 else N) = 7 := by decide
  rw [h7] at hseq
  have hA : (univ.filter fun fs : Fin 7 → F ↦ ¬rsJDoom δ (List.ofFn fs)).card ≤ 7 * N ^ 6 := by
    have : (univ.filter fun fs : Fin 7 → F ↦ ¬rsJDoom δ (List.ofFn fs)).card * N ≤ 7 * N ^ 6 * N := by
      rw [mul_assoc, ← pow_succ]; exact hseq
    exact Nat.le_of_mul_le_mul_right this hN
  have hB : ∀ fs : Fin 7 → F, ¬¬rsJDoom δ (List.ofFn fs) →
      (univ.filter fun κ : F ↦ ∑ j, κ ^ j.val * rsT s fs j = ∑ j, κ ^ j.val * rsTruth Q g fs j).card
        ≤ J' := fun fs hd ↦ by
    obtain ⟨j, hj⟩ := not_not.mp hd
    refine batch_pow_bad_le fun h ↦ ?_
    exact rs_end bitBasis Q hQ (g j) (s j) 6 (List.ofFn fs) (by simp) hj (congrFun h j)
  have hP := pair_bad_le (fun fs : Fin 7 → F ↦ ¬rsJDoom δ (List.ofFn fs))
    (fun fs κ ↦ ∑ j, κ ^ j.val * rsT s fs j = ∑ j, κ ^ j.val * rsTruth Q g fs j) hA hB
  refine (Finset.card_le_card fun p hp ↦ ?_).trans (hP.trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact Or.inr hp
  · simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show N ^ 7 = N ^ 6 * N by ring]
    nlinarith [Nat.zero_le N]

/-- **RS1 at `J_z = 4`** (rev. 3.8: the Z claim `ẑ(r, λ)` first, then Lc's `⟨W_β, z⟩`, Sh's and
Lr's claims; the order does not enter the bound): at most `10 · |F|^7` escaping draws. -/
theorem rs1_four (Q : Fin 128 → Fin (2 ^ ℓ) → F) (hQ : ∀ i u, Q i u = 0 ∨ Q i u = 1)
    (g : Fin 4 → Fin (2 ^ ℓ) → F) (s : Fin 4 → Fin 128 → F)
    (hδ : ∃ j, (fun i ↦ s j i - ∑ u, g j u * algebraMap F F (Q i u)) ≠ 0) :
    (univ.filter fun p : (Fin 7 → F) × F ↦
      ∑ j, p.2 ^ j.val * rsT s p.1 j = ∑ j, p.2 ^ j.val * rsTruth Q g p.1 j).card ≤
      10 * Fintype.card F ^ 7 :=
  rs1_joint (J' := 3) Q hQ g s hδ

end RS1

end FR
