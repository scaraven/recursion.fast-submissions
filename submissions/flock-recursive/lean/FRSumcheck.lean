-- Copied from `submissions/spartan-srom/lean/SpartanSromSumcheck.lean` (this repository, branch
-- `v4/flock-recursive` at `783328c`), namespace `SpartanSrom` → `FR`; that file was ported from v3
-- `spartan-chain` (submissions repo, local `main` at `1f59b38`). Changes are listed in the module
-- docstring.
import FRMLE
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.CharP.Two

/-!
# Sumcheck: the verifier's rounds, the honest rounds, and the counting lemmas (BLUEPRINT §7
`FRSumcheck`, §5.2; spartan-srom's L-S1 … L-S4)

Generic over a commutative ring `R` (a field with `Fintype` for the counting lemmas).

A round polynomial of degree `≤ d` travels as its `d + 1` coefficients `c_0 … c_d` (ascending,
an `Array R`), evaluated by Horner (`peval`). The verifier's round (`verifyRounds`) checks the
size and `g(0) + g(1) = claim` (literally `peval g 0 + peval g 1`; in characteristic two that is
`c_1 + … + c_d = claim`, `peval_zero_add_one`, since `c_0` cancels), and moves the claim to
`g(r)`; the challenges come from outside (the transcript), so the rounds are a function of the
`(g, r)` pairs.

The honest prover's summand is an expression (`Expr`: variables, sums, products) in multilinear
tables bound variable `0` first. In a round each table is linear in the round variable on every
pair `2j, 2j + 1`, and the round polynomial is the sum over `j` of the expression evaluated in
coefficient arithmetic (`roundPoly`): no interpolation and no inversion. Spartan's outer summand
is `eq · (A · B + C)`, the inner and ring-switching summands are `M · z` and `W · q`.

* **L-S1** `round_bad_le` (and `round_bad_le_arr` on coefficient arrays): two different round
  polynomials of degree `≤ d` agree on at most `d` challenges (`Polynomial.card_roots'`);
  `round_bad_le_of_check` is the form the verifier's check gives (`g` passes, `g*` does not).
* **L-S2** `zerocheck_bad_le`: fixing variable `0` of a nonzero table to `c` gives the zero table
  for at most one `c`.
* **L-S3** `batch_bad_le`: two different triples `(v_A, v_B, v_C)` agree under `ρ ↦ Σ ρ^i v_i`
  for at most two `ρ`.
* `batch_pow_bad_le` (the §5.2 rows L1, Lr2, E2, B1, B′): two different families of `k + 1`
  claims agree under `κ ↦ Σ_i κ^i v_i` for at most `k` values of `κ`; `batch2_bad_le` is `k = 1`.
* `pair_bad_le`: one squeeze answer carries two F coordinates (BLUEPRINT A.2); if the first
  coordinate escapes for at most `a` values and, after a non-escaping first coordinate, the second
  escapes for at most `b`, the pairs that escape number at most `a·|R| + |R|·b`.
* `innerExpr` (`t₀ · t₁`, degree 2) with `prod_trueSum`, `tbl_ofFn` (moved here from
  spartan-srom's `SoundnessSpartan`, used by every degree-2 sumcheck).
* `seq_bad_le`: a phase drawing `k` coordinates in sequence, each escaping a doomed prefix for at
  most `b_i` values, has at most `(Σ_i b_i)·|R|^(k−1)` escaping tuples (the joint row RS1, and Z1's
  free coordinates); `pair_bad_le` combines a first draw with a second (`α × β`).
* **L-S4** `sumcheck_complete`: the honest round polynomials pass every check for every
  challenge, and the final claim is the expression at the tables' extensions.

Changes from spartan-srom: the namespace; `trueSum_bindAll'`, `innerExpr`/`prod_trueSum`/`tbl_ofFn`
(moved from `SoundnessSpartan`), `batch_pow_bad_le`, `batch2_bad_le`, `pair_bad_le`,
`seq_bad_le` added.
-/

namespace FR

open Finset Polynomial

variable {R : Type*} [CommRing R]

/-! ## Coefficient arrays -/

/-- Horner: `Σ_i p[i] · x^i`. -/
@[specialize]
def peval (p : Array R) (x : R) : R := p.foldr (fun c acc ↦ c + x * acc) 0

theorem peval_eq_sum (p : Array R) (x : R) :
    peval p x = ∑ i ∈ range p.size, p.getD i 0 * x ^ i := by
  rw [peval, ← Array.foldr_toList, ← Array.length_toList]
  have hget : ∀ i, p.getD i 0 = p.toList.getD i 0 := fun i ↦ by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  simp only [hget]
  generalize p.toList = l
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.foldr_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Past the size the coefficients are zero, so a longer range gives the same sum. -/
theorem peval_eq_sum_of_le (p : Array R) (x : R) {n : ℕ} (h : p.size ≤ n) :
    peval p x = ∑ i ∈ range n, p.getD i 0 * x ^ i := by
  rw [peval_eq_sum]
  refine Finset.sum_subset (Finset.range_mono h) fun i _ hi ↦ ?_
  simp only [Finset.mem_range, not_lt] at hi
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi]

theorem peval_three (a b c x : R) : peval #[a, b, c] x = a + x * b + x ^ 2 * c := by
  simp [peval_eq_sum, Finset.sum_range_succ]
  ring

/-- Coefficientwise sum. -/
@[specialize]
def pAdd (p q : Array R) : Array R :=
  Array.ofFn (n := max p.size q.size) fun i ↦ p.getD i 0 + q.getD i 0

theorem pAdd_size (p q : Array R) : (pAdd p q).size = max p.size q.size := Array.size_ofFn

theorem getD_ofFn {n : ℕ} (f : Fin n → R) (i : ℕ) :
    (Array.ofFn f).getD i 0 = if h : i < n then f ⟨i, h⟩ else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split_ifs <;> rfl

theorem peval_pAdd (p q : Array R) (x : R) : peval (pAdd p q) x = peval p x + peval q x := by
  rw [peval_eq_sum, peval_eq_sum_of_le p x (le_max_left p.size q.size),
    peval_eq_sum_of_le q x (le_max_right p.size q.size), pAdd_size, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [pAdd, getD_ofFn, dite_eq_left hi, add_mul]

/-- `a · X^i · q`. -/
@[specialize]
def pShiftScale (i : ℕ) (a : R) (q : Array R) : Array R :=
  Array.ofFn (n := i + q.size) fun k ↦ if k.val < i then 0 else a * q.getD (k.val - i) 0

theorem peval_pShiftScale (i : ℕ) (a : R) (q : Array R) (x : R) :
    peval (pShiftScale i a q) x = a * x ^ i * peval q x := by
  rw [peval_eq_sum, pShiftScale, Array.size_ofFn, Finset.sum_range_add, peval_eq_sum,
    Finset.mul_sum]
  rw [Finset.sum_eq_zero fun k hk ↦ by
    rw [Finset.mem_range] at hk
    rw [getD_ofFn, dite_eq_left (by omega), ite_eq_left hk, zero_mul], zero_add]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [getD_ofFn, dite_eq_left (by omega)]
  simp only [add_lt_iff_neg_left, not_lt_zero, ite_false, Nat.add_sub_cancel_left, pow_add]
  ring

/-- Product: `Σ_i p[i] · X^i · q`. -/
@[specialize]
def pMul (p q : Array R) : Array R :=
  Nat.fold p.size (fun i _ acc ↦ pAdd acc (pShiftScale i (p.getD i 0) q)) #[]

theorem pMul_fold (p q : Array R) (n : ℕ) (x : R) :
    peval (Nat.fold n (fun i _ acc ↦ pAdd acc (pShiftScale i (p.getD i 0) q)) #[]) x =
      (∑ i ∈ range n, p.getD i 0 * x ^ i) * peval q x ∧
    (Nat.fold n (fun i _ acc ↦ pAdd acc (pShiftScale i (p.getD i 0) q)) #[]).size =
      if n = 0 then 0 else n - 1 + q.size := by
  induction n with
  | zero => simp [peval]
  | succ n ih =>
    rw [Nat.fold_succ, peval_pAdd, ih.1, peval_pShiftScale, Finset.sum_range_succ, pAdd_size,
      ih.2, pShiftScale, Array.size_ofFn]
    refine ⟨by ring, ?_⟩
    by_cases hn : n = 0 <;> simp [hn]

theorem peval_pMul (p q : Array R) (x : R) : peval (pMul p q) x = peval p x * peval q x := by
  rw [pMul, (pMul_fold p q p.size x).1, peval_eq_sum p]

theorem pMul_size (p q : Array R) (hp : p.size ≠ 0) : (pMul p q).size = p.size - 1 + q.size := by
  rw [pMul, (pMul_fold p q p.size 0).2, ite_eq_right hp]

/-- The polynomial of a coefficient array. -/
noncomputable def toPoly (p : Array R) : R[X] := ∑ i ∈ range p.size, C (p.getD i 0) * X ^ i

theorem coeff_toPoly (p : Array R) (k : ℕ) : (toPoly p).coeff k = p.getD k 0 := by
  rw [toPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · simp

theorem eval_toPoly (p : Array R) (x : R) : (toPoly p).eval x = peval p x := by
  simp [toPoly, eval_finsetSum, peval_eq_sum]

theorem natDegree_toPoly_le (p : Array R) {d : ℕ} (h : p.size ≤ d + 1) :
    (toPoly p).natDegree ≤ d :=
  natDegree_sum_le_of_forall_le _ _ fun i hi ↦
    (natDegree_C_mul_X_pow_le _ _).trans (by rw [Finset.mem_range] at hi; omega)

theorem toPoly_injective {p q : Array R} (hs : p.size = q.size) (h : toPoly p = toPoly q) :
    p = q := by
  refine Array.ext hs fun i hp hq ↦ ?_
  have := congrArg (fun P ↦ P.coeff i) h
  simp only [coeff_toPoly, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp,
    Array.getElem?_eq_getElem hq, Option.getD_some] at this
  exact this

/-! ## Expressions in the tables -/

/-- A summand: a polynomial expression in the tables `0, 1, …`. -/
inductive Expr
  | var (i : ℕ)
  | add (a b : Expr)
  | mul (a b : Expr)

namespace Expr

/-- The value at the table values `v i`. -/
@[specialize]
def eval (v : ℕ → R) : Expr → R
  | var i => v i
  | add a b => a.eval v + b.eval v
  | mul a b => a.eval v * b.eval v

/-- The degree in the round variable when every table is linear in it. -/
def deg : Expr → ℕ
  | var _ => 1
  | add a b => max a.deg b.deg
  | mul a b => a.deg + b.deg

/-- The value in coefficient arithmetic, the tables being the polynomials `v i`. -/
@[specialize]
def evalPoly (v : ℕ → Array R) : Expr → Array R
  | var i => v i
  | add a b => pAdd (a.evalPoly v) (b.evalPoly v)
  | mul a b => pMul (a.evalPoly v) (b.evalPoly v)

theorem peval_evalPoly (v : ℕ → Array R) (x : R) (e : Expr) :
    peval (e.evalPoly v) x = e.eval fun i ↦ peval (v i) x := by
  induction e with
  | var i => rfl
  | add a b iha ihb => simp only [evalPoly, eval, peval_pAdd, iha, ihb]
  | mul a b iha ihb => simp only [evalPoly, eval, peval_pMul, iha, ihb]

theorem evalPoly_size (v : ℕ → Array R) (hv : ∀ i, (v i).size = 2) (e : Expr) :
    (e.evalPoly v).size = e.deg + 1 := by
  induction e with
  | var i => exact hv i
  | add a b iha ihb => simp only [evalPoly, deg, pAdd_size, iha, ihb]; omega
  | mul a b iha ihb => rw [evalPoly, deg, pMul_size _ _ (by omega), iha, ihb]; omega

end Expr

/-! ## The honest prover -/

/-- Table `t` on the pair `2j, 2j + 1` as a polynomial in the round variable:
`t[2j] + X · (t[2j + 1] - t[2j])`. -/
@[specialize]
def linAt (t : Array R) (j : ℕ) : Array R :=
  #[t.getD (2 * j) 0, t.getD (2 * j + 1) 0 - t.getD (2 * j) 0]

/-- The honest round polynomial, `half` pairs: `Σ_{j < half} e(linAt t_i j)`, `deg e + 1`
coefficients. -/
@[specialize]
def roundPoly (e : Expr) (ts : Array (Array R)) (half : ℕ) : Array R :=
  Nat.fold half (fun j _ acc ↦ pAdd acc (e.evalPoly fun i ↦ linAt (ts.getD i #[]) j))
    (Array.replicate (e.deg + 1) 0)

/-- The honest round polynomials for the challenges `rs`, the tables bound after each round. -/
def honest (e : Expr) : Array (Array R) → List R → List (Array R)
  | _, [] => []
  | ts, r :: rs => roundPoly e ts (2 ^ rs.length) :: honest e (ts.map (bind0 · r)) rs

theorem roundPoly_spec (e : Expr) (ts : Array (Array R)) (n : ℕ) (x : R) :
    peval (roundPoly e ts n) x =
        ∑ j ∈ range n, e.eval (fun i ↦ peval (linAt (ts.getD i #[]) j) x) ∧
      (roundPoly e ts n).size = e.deg + 1 := by
  induction n with
  | zero =>
    refine ⟨?_, by simp [roundPoly]⟩
    rw [roundPoly, Nat.fold_zero, peval_eq_sum]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Finset.mem_range, Array.size_replicate] at hi
    simp [Array.getD_eq_getD_getElem?, hi]
  | succ n ih =>
    rw [roundPoly, Nat.fold_succ, ← roundPoly, peval_pAdd, ih.1, Expr.peval_evalPoly,
      Finset.sum_range_succ, pAdd_size, ih.2,
      Expr.evalPoly_size _ (fun i ↦ by simp [linAt]), max_self]
    exact ⟨rfl, rfl⟩

theorem peval_linAt (t : Array R) (ℓ : ℕ) (j : Fin (2 ^ ℓ)) (x : R) :
    peval (linAt t j) x = fix0 (tbl (ℓ + 1) t) x j := by
  simp [peval, linAt, fix0, tbl, dbl]

/-- **The honest round polynomial at `x`** is the sum with variable `0` fixed to `x`. -/
theorem peval_roundPoly (e : Expr) (ts : Array (Array R)) (ℓ : ℕ) (x : R) :
    peval (roundPoly e ts (2 ^ ℓ)) x =
      ∑ u : Fin (2 ^ ℓ), e.eval fun i ↦ fix0 (tbl (ℓ + 1) (ts.getD i #[])) x u := by
  rw [(roundPoly_spec e ts _ x).1, ← Fin.sum_univ_eq_sum_range]
  simp only [peval_linAt]

/-! ## The verifier -/

/-- The verifier's rounds from `claim`: each `(g, r)` must have `d + 1` coefficients with
`g(0) + g(1) = claim`, and the claim moves to `g(r)`. The final claim, or `none`. -/
def verifyRounds [DecidableEq R] (d : ℕ) : R → List (Array R × R) → Option R
  | claim, [] => some claim
  | claim, (g, r) :: rest =>
    if g.size = d + 1 ∧ peval g 0 + peval g 1 = claim then verifyRounds d (peval g r) rest
    else none

/-- **The check in characteristic two** (BLUEPRINT-R1 review BP-m4): `g(0) + g(1)` is
`c_1 + … + c_d`; `c_0` cancels, so the check constrains only `c_1 … c_d`, and `c_0` enters only the
next claim `g(r)`. `verifyRounds` checks `g(0) + g(1)` literally (`peval g 0 + peval g 1`). -/
theorem peval_zero_add_one [CharP R 2] (g : Array R) :
    peval g 0 + peval g 1 = ∑ i ∈ Ico 1 g.size, g.getD i 0 := by
  rw [peval_eq_sum, peval_eq_sum, Finset.sum_Ico_eq_sum_range]
  obtain h | ⟨m, hm⟩ : g.size = 0 ∨ ∃ m, g.size = m + 1 :=
    (Nat.eq_zero_or_pos g.size).imp id fun h ↦ ⟨g.size - 1, by omega⟩
  · simp [h]
  · rw [hm, Finset.sum_range_succ', Finset.sum_range_succ', Nat.add_sub_cancel]
    simp only [one_pow, mul_one, pow_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero, zero_add]
    rw [add_comm, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [add_comm]

theorem getD_map_bind0 (ts : Array (Array R)) (r : R) (i : ℕ) :
    (ts.map (bind0 · r)).getD i #[] = bind0 (ts.getD i #[]) r := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases ts[i]? <;> simp [bind0]

/-- The true sum of the summand over tables of size `2 ^ m`. -/
def trueSum (e : Expr) (ts : Array (Array R)) (m : ℕ) : R :=
  ∑ u : Fin (2 ^ m), e.eval fun i ↦ tbl m (ts.getD i #[]) u

/-- Binding variable `0` of every table (of size `2 ^ (m + 1)`) is fixing it. -/
theorem tbl_map_bind0 (ts : Array (Array R)) (r : R) {m : ℕ}
    (hts : ∀ t ∈ ts, t.size = 2 ^ (m + 1)) (i : ℕ) :
    tbl m ((ts.map (bind0 · r)).getD i #[]) = fix0 (tbl (m + 1) (ts.getD i #[])) r := by
  rw [getD_map_bind0]
  simp only [Array.getD_eq_getD_getElem?]
  cases h : ts[i]? with
  | none => funext u; simp [bind0, tbl, fix0]
  | some t => exact tbl_bind0 t r (hts t (Array.mem_of_getElem? h))

theorem map_bind0_size (ts : Array (Array R)) (r : R) {m : ℕ}
    (hts : ∀ t ∈ ts, t.size = 2 ^ (m + 1)) : ∀ t ∈ ts.map (bind0 · r), t.size = 2 ^ m := by
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := Array.mem_map.mp ht
  rw [bind0_size, hts t₀ h₀, pow_succ, Nat.mul_div_cancel _ two_pos]

/-- The honest round polynomial passes the check from the true sum. -/
theorem roundPoly_check (e : Expr) (ts : Array (Array R)) (m : ℕ) :
    peval (roundPoly e ts (2 ^ m)) 0 + peval (roundPoly e ts (2 ^ m)) 1 = trueSum e ts (m + 1) := by
  rw [peval_roundPoly, peval_roundPoly, ← Finset.sum_add_distrib, trueSum, sum_cube_succ]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  congr 1 <;> congr 1 <;> funext i <;> simp [fix0]

/-- The honest round polynomial at `r` is the true sum of the tables bound at `r`. -/
theorem roundPoly_next (e : Expr) (ts : Array (Array R)) {m : ℕ}
    (hts : ∀ t ∈ ts, t.size = 2 ^ (m + 1)) (r : R) :
    peval (roundPoly e ts (2 ^ m)) r = trueSum e (ts.map (bind0 · r)) m := by
  simp only [peval_roundPoly, trueSum, tbl_map_bind0 ts r hts]

/-- The tables bound at the challenges `rs`, in order. -/
def bindAll (ts : Array (Array R)) : List R → Array (Array R)
  | [] => ts
  | r :: rs => bindAll (ts.map (bind0 · r)) rs

/-- After every variable is bound, the true sum is the summand at the tables' extensions. -/
theorem trueSum_bindAll (e : Expr) (rs : List R) (ts : Array (Array R))
    (hts : ∀ t ∈ ts, t.size = 2 ^ rs.length) :
    trueSum e (bindAll ts rs) 0 = e.eval fun i ↦ mle (tbl rs.length (ts.getD i #[])) (pt rs) := by
  induction rs generalizing ts with
  | nil =>
    rw [bindAll, trueSum, sum_cube_zero]
    congr 1
    funext i
    rw [mle_zero]
    rfl
  | cons r rs ih =>
    rw [bindAll, ih _ (map_bind0_size ts r hts)]
    congr 1
    funext i
    rw [tbl_map_bind0 ts r hts]
    symm
    rw [mle_fix0, pt_cons]
    rfl

/-- `trueSum_bindAll` at a length given by an equation: the extensions at `ptOf ℓ rs`. -/
theorem trueSum_bindAll' (e : Expr) (rs : List R) (ts : Array (Array R)) {ℓ : ℕ}
    (hℓ : rs.length = ℓ) (hts : ∀ t ∈ ts, t.size = 2 ^ ℓ) :
    trueSum e (bindAll ts rs) 0 = e.eval fun i ↦ mle (tbl ℓ (ts.getD i #[])) (ptOf ℓ rs) := by
  subst hℓ
  rw [trueSum_bindAll e rs ts hts, pt_eq_ptOf]

/-! ## Tables from functions; the product summand -/

theorem tbl_ofFn {ℓ : ℕ} (f : Fin (2 ^ ℓ) → R) : tbl ℓ (Array.ofFn f) = f := by
  funext u
  simp [tbl]

/-- One table bound at `cs`, in order. -/
def bindT (t : Array R) : List R → Array R
  | [] => t
  | c :: cs => bindT (bind0 t c) cs

theorem bindT_size (t : Array R) (cs : List R) {m : ℕ} (ht : t.size = 2 ^ (cs.length + m)) :
    (bindT t cs).size = 2 ^ m := by
  induction cs generalizing t with
  | nil => simpa [bindT] using ht
  | cons c cs ih =>
    refine ih _ ?_
    rw [bind0_size, ht, List.length_cons, show cs.length + 1 + m = (cs.length + m) + 1 by omega,
      pow_succ, Nat.mul_div_cancel _ two_pos]

/-- All variables bound: the one entry is the extension at `cs`. -/
theorem tbl_bindT (t : Array R) (cs : List R) (ht : t.size = 2 ^ cs.length) (u : Fin (2 ^ 0)) :
    tbl 0 (bindT t cs) u = mle (tbl cs.length t) (pt cs) := by
  induction cs generalizing t with
  | nil => rw [bindT, mle_zero]; congr 1; exact Fin.ext (by simp)
  | cons c cs ih =>
    have hs : (bind0 t c).size = 2 ^ cs.length := by
      rw [bind0_size, ht, List.length_cons, pow_succ, Nat.mul_div_cancel _ two_pos]
    rw [bindT, ih _ hs, tbl_bind0 t c ht]
    symm
    rw [mle_fix0, pt_cons]
    rfl

/-- A summand of two tables: `t₀ · t₁` (inner, ring-switching). -/
def innerExpr : Expr := .mul (.var 0) (.var 1)

theorem innerExpr_deg : innerExpr.deg = 2 := rfl

/-- The true sum of `t₀ · t₁` over two tables given as functions. -/
theorem prod_trueSum {ℓ : ℕ} (f g : Fin (2 ^ ℓ) → R) :
    trueSum innerExpr #[Array.ofFn f, Array.ofFn g] ℓ = ∑ u, f u * g u := by
  simp [trueSum, innerExpr, Expr.eval, tbl_ofFn]

omit [CommRing R] in
theorem prod_sizes {ℓ : ℕ} (f g : Fin (2 ^ ℓ) → R) :
    ∀ t ∈ #[Array.ofFn f, Array.ofFn g], t.size = 2 ^ ℓ := by
  simp

/-- The honest rounds pass from the true sum, and end at the true sum of the bound tables. -/
theorem verifyRounds_honest [DecidableEq R] (e : Expr) (rs : List R) (ts : Array (Array R))
    (hts : ∀ t ∈ ts, t.size = 2 ^ rs.length) :
    verifyRounds e.deg (trueSum e ts rs.length) ((honest e ts rs).zip rs) =
      some (trueSum e (bindAll ts rs) 0) := by
  induction rs generalizing ts with
  | nil => rfl
  | cons r rs ih =>
    simp only [honest, List.zip_cons_cons, verifyRounds, List.length_cons]
    rw [ite_eq_left ⟨(roundPoly_spec e ts _ 0).2, roundPoly_check e ts _⟩,
      roundPoly_next e ts hts, ih _ (map_bind0_size ts r hts), bindAll]

/-- **L-S4 (completeness).** For tables of size `2 ^ |rs|` and the claim their true sum, the
honest round polynomials pass every round for the challenges `rs`, whatever they are, and the
final claim is the summand at the tables' extensions at `rs`. -/
theorem sumcheck_complete [DecidableEq R] (e : Expr) (rs : List R) (ts : Array (Array R))
    (hts : ∀ t ∈ ts, t.size = 2 ^ rs.length) :
    verifyRounds e.deg (∑ u : Fin (2 ^ rs.length), e.eval fun i ↦ tbl rs.length (ts.getD i #[]) u)
        ((honest e ts rs).zip rs) =
      some (e.eval fun i ↦ mle (tbl rs.length (ts.getD i #[])) (pt rs)) := by
  rw [← trueSum_bindAll e rs ts hts]
  exact verifyRounds_honest e rs ts hts

/-! ## Counting lemmas -/

section Counting

variable [IsDomain R] [Fintype R] [DecidableEq R]

/-- **L-S1.** Two different polynomials of degree `≤ d` agree on at most `d` points. (The
blueprint also assumes `g(0) + g(1) = g*(0) + g*(1)`; the bound does not need it.) -/
theorem round_bad_le {d : ℕ} {g gs : R[X]} (hne : g ≠ gs) (hg : g.natDegree ≤ d)
    (hgs : gs.natDegree ≤ d) : (univ.filter fun r ↦ g.eval r = gs.eval r).card ≤ d := by
  have h0 : g - gs ≠ 0 := sub_ne_zero.mpr hne
  calc (univ.filter fun r ↦ g.eval r = gs.eval r).card ≤ (g - gs).roots.toFinset.card := by
        refine Finset.card_le_card fun r hr ↦ ?_
        rw [Finset.mem_filter] at hr
        rw [Multiset.mem_toFinset, mem_roots h0, IsRoot, eval_sub, hr.2, sub_self]
    _ ≤ (g - gs).roots.card := Multiset.toFinset_card_le _
    _ ≤ (g - gs).natDegree := card_roots' _
    _ ≤ d := (natDegree_sub_le _ _).trans (max_le hg hgs)

/-- **L-S1 on coefficient arrays.** Two different round polynomials of `d + 1` coefficients agree
on at most `d` challenges. -/
theorem round_bad_le_arr {d : ℕ} {g gs : Array R} (hne : g ≠ gs) (hg : g.size = d + 1)
    (hgs : gs.size = d + 1) : (univ.filter fun r ↦ peval g r = peval gs r).card ≤ d := by
  simp only [← eval_toPoly]
  exact round_bad_le (fun h ↦ hne (toPoly_injective (hg.trans hgs.symm) h))
    (natDegree_toPoly_le g hg.le) (natDegree_toPoly_le gs hgs.le)

/-- **L-S1 as the verifier uses it.** A round polynomial `g` that passes the check
`g(0) + g(1) = claim` while the true round polynomial `g*` does not (the claim is false) differs
from `g*`, so the next claim `g(r)` is true (`= g*(r)`) for at most `d` challenges. -/
theorem round_bad_le_of_check {d : ℕ} {g gs : Array R} {claim : R} (hg : g.size = d + 1)
    (hgs : gs.size = d + 1) (hcheck : peval g 0 + peval g 1 = claim)
    (hfalse : peval gs 0 + peval gs 1 ≠ claim) :
    (univ.filter fun r ↦ peval g r = peval gs r).card ≤ d :=
  round_bad_le_arr (fun h ↦ hfalse (h ▸ hcheck)) hg hgs

/-- **A sumcheck round from a false claim** (L-S1 as rounds R2, R4 and R6 of §9.2 use it). If the
claim is not the true sum of the tables, then for any round polynomial `g` the challenges `r` at
which the round passes and the next claim `g(r)` is the true sum of the bound tables number at
most `deg e`. -/
theorem round_escape_le (e : Expr) (ts : Array (Array R)) {m : ℕ}
    (hts : ∀ t ∈ ts, t.size = 2 ^ (m + 1)) {claim : R} (hfalse : claim ≠ trueSum e ts (m + 1))
    (g : Array R) :
    (univ.filter fun r ↦ (g.size = e.deg + 1 ∧ peval g 0 + peval g 1 = claim) ∧
      peval g r = trueSum e (ts.map (bind0 · r)) m).card ≤ e.deg := by
  by_cases hg : g.size = e.deg + 1 ∧ peval g 0 + peval g 1 = claim
  · refine (Finset.card_le_card fun r hr ↦ ?_).trans (round_bad_le_of_check hg.1
      (roundPoly_spec e ts (2 ^ m) 0).2 hg.2 (by rw [roundPoly_check]; exact hfalse.symm))
    rw [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, hr.2.2.trans (roundPoly_next e ts hts r).symm⟩
  · rw [Finset.filter_false_of_mem fun r _ h ↦ hg h.1, Finset.card_empty]
    exact Nat.zero_le _

/-- **L-S2.** A nonzero table has its variable `0` fixed to a value giving the zero table for at
most one value. Iterated coordinate by coordinate (each restriction is again a nonzero table
except for at most one value), and with `mle_cube`/`eq_zero_of_mle` (a table is zero iff its
extension is), this is the zerocheck's per-coordinate bound. -/
theorem zerocheck_bad_le {ℓ : ℕ} (f : Fin (2 ^ (ℓ + 1)) → R) (hf : f ≠ 0) :
    (univ.filter fun c ↦ fix0 f c = 0).card ≤ 1 := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  obtain ⟨⟨u, b⟩, rfl⟩ := (dblEquiv ℓ).surjective v
  refine Finset.card_le_one.mpr fun c₁ h₁ c₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  have e₁ := congrFun h₁.2 u
  have e₂ := congrFun h₂.2 u
  simp only [fix0, Pi.zero_apply] at e₁ e₂
  have hδ : f (dbl u true) - f (dbl u false) ≠ 0 := by
    intro hδ
    rw [hδ, mul_zero, add_zero] at e₁
    rw [sub_eq_zero, e₁] at hδ
    cases b <;> exact hv (by simpa [dblEquiv] using (by assumption : _ = _))
  have : (c₁ - c₂) * (f (dbl u true) - f (dbl u false)) = 0 := by
    linear_combination e₁ - e₂
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hδ)

/-- **L-S3.** Two different triples agree under `ρ ↦ v_A + ρ v_B + ρ² v_C` for at most two
`ρ`. -/
theorem batch_bad_le {vA vB vC tA tB tC : R} (h : (vA, vB, vC) ≠ (tA, tB, tC)) :
    (univ.filter fun ρ ↦ vA + ρ * vB + ρ ^ 2 * vC = tA + ρ * tB + ρ ^ 2 * tC).card ≤ 2 := by
  have hne : #[vA, vB, vC] ≠ #[tA, tB, tC] := fun he ↦ h (by simp_all)
  convert round_bad_le_arr hne rfl rfl using 3 with ρ
  simp only [peval_three]

/-- **Power batching** (rows L1, Lr2, E2, B1, B′ of BLUEPRINT §5.2). Two different families of
`k + 1` claims agree under `κ ↦ Σ_{i ≤ k} κ^i v_i` for at most `k` values of `κ`. -/
theorem batch_pow_bad_le {k : ℕ} {v t : Fin (k + 1) → R} (h : v ≠ t) :
    (univ.filter fun κ ↦ ∑ i, κ ^ i.val * v i = ∑ i, κ ^ i.val * t i).card ≤ k := by
  have hne : Array.ofFn v ≠ Array.ofFn t := fun he ↦ h (funext fun i ↦ by
    have := congrArg (fun a : Array R ↦ a.getD i 0) he
    simpa only [getD_ofFn, dite_eq_left i.isLt] using this)
  have hp : ∀ (w : Fin (k + 1) → R) (κ : R), peval (Array.ofFn w) κ = ∑ i, κ ^ i.val * w i := by
    intro w κ
    rw [peval_eq_sum, Array.size_ofFn, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [getD_ofFn, dite_eq_left i.isLt, mul_comm]
  convert round_bad_le_arr (d := k) hne (by simp) (by simp) using 3 with κ
  rw [hp, hp]

/-- **Batching two claims** (row L1: the lincheck's `α`; the two-claim batchings). Two different
pairs agree under `α ↦ v₀ + α v₁` for at most one `α`. -/
theorem batch2_bad_le {v₀ v₁ t₀ t₁ : R} (h : (v₀, v₁) ≠ (t₀, t₁)) :
    (univ.filter fun α ↦ v₀ + α * v₁ = t₀ + α * t₁).card ≤ 1 := by
  have hne : ![v₀, v₁] ≠ ![t₀, t₁] := fun he ↦ h (by
    have h0 := congrFun he 0; have h1 := congrFun he 1; simp_all)
  convert batch_pow_bad_le hne using 3 with α
  simp [Fin.sum_univ_two]

end Counting

/-! ## Two coordinates per squeeze -/

/-- **Two draws in sequence** (e.g. the two F coordinates of one answer, BLUEPRINT A.2). If the
first escapes (`B₁`) for at most `a` values and, after a first draw that does not escape, the second
escapes (`B₂ c₁`) for at most `b`, then at most `a·|β| + |α|·b` pairs escape. -/
theorem pair_bad_le {α β : Type*} [Fintype α] [Fintype β] (B₁ : α → Prop) [DecidablePred B₁]
    (B₂ : α → β → Prop) [∀ c, DecidablePred (B₂ c)] {a b : ℕ}
    (h₁ : (univ.filter B₁).card ≤ a) (h₂ : ∀ c, ¬B₁ c → (univ.filter (B₂ c)).card ≤ b) :
    (univ.filter fun p : α × β ↦ B₁ p.1 ∨ B₂ p.1 p.2).card ≤ a * Fintype.card β +
      Fintype.card α * b := by
  classical
  have hsplit : (univ.filter fun p : α × β ↦ B₁ p.1 ∨ B₂ p.1 p.2) ⊆
      (univ.filter B₁) ×ˢ univ ∪ (univ.filter fun c ↦ ¬B₁ c).biUnion
        (fun c ↦ (univ.filter (B₂ c)).map ⟨fun d ↦ (c, d), fun _ _ h ↦ (Prod.mk.inj h).2⟩) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h : B₁ p.1
    · exact Finset.mem_union_left _ (by simp [h])
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p.1, by simp [h], ?_⟩)
      exact Finset.mem_map.mpr ⟨p.2, by simp [hp.resolve_left h], rfl⟩
  refine (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_product, Finset.card_univ]
  refine Nat.add_le_add (Nat.mul_le_mul_right _ h₁) (Finset.card_biUnion_le.trans ?_)
  calc ∑ c ∈ univ.filter fun c ↦ ¬B₁ c, ((univ.filter (B₂ c)).map _).card
      ≤ ∑ _c ∈ univ.filter fun c ↦ ¬B₁ c, b := Finset.sum_le_sum fun c hc ↦ by
        rw [Finset.card_map]; exact h₂ c (Finset.mem_filter.mp hc).2
    _ ≤ Fintype.card α * b := by
      rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_le_univ _)

/-- **Sequential coordinates** (a phase that draws `k` coordinates one after another, e.g. RS1's
stage coefficients): if from every doomed prefix `l` the next coordinate escapes for at most
`b |l|` values, then the `k`-tuples drawn after a doomed `l` that escape number at most
`(Σ_{i<k} b (|l| + i)) · |R|^(k−1)` (stated times `|R|` to avoid the subtraction). -/
theorem seq_bad_le {R : Type*} [Fintype R] [DecidableEq R] (Doom : List R → Prop)
    [DecidablePred Doom] (b : ℕ → ℕ)
    (hb : ∀ l, Doom l → (univ.filter fun c ↦ ¬Doom (l ++ [c])).card ≤ b l.length) :
    ∀ (k : ℕ) (l : List R), Doom l →
      (univ.filter fun v : Fin k → R ↦ ¬Doom (l ++ List.ofFn v)).card * Fintype.card R ≤
        (∑ i ∈ range k, b (l.length + i)) * Fintype.card R ^ k := by
  intro k
  induction k with
  | zero =>
    intro l hl
    simp [hl]
  | succ k ih =>
    intro l hl
    set N := Fintype.card R
    have hcount : (univ.filter fun v : Fin (k + 1) → R ↦ ¬Doom (l ++ List.ofFn v)).card =
        ∑ c : R, (univ.filter fun v : Fin k → R ↦ ¬Doom ((l ++ [c]) ++ List.ofFn v)).card := by
      rw [Finset.card_filter, ← (Fin.consEquiv (fun _ : Fin (k + 1) ↦ R)).sum_comp,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp [Fin.consEquiv, List.ofFn_succ]
    rw [hcount, Finset.sum_mul, Finset.sum_range_succ', pow_succ]
    have hsplit : ∀ c : R,
        (univ.filter fun v : Fin k → R ↦ ¬Doom ((l ++ [c]) ++ List.ofFn v)).card * N ≤
          (if Doom (l ++ [c]) then 0 else N ^ k * N) +
            (∑ i ∈ range k, b (l.length + (i + 1))) * N ^ k := fun c ↦ by
      by_cases hc : Doom (l ++ [c])
      · rw [ite_eq_left hc, zero_add]
        have := ih (l ++ [c]) hc
        simpa [Nat.add_assoc, Nat.add_comm 1] using this
      · rw [ite_eq_right hc]
        refine le_add_right (Nat.mul_le_mul_right _ ?_)
        exact (Finset.card_le_univ _).trans (by simp [N])
    calc ∑ c : R, (univ.filter fun v : Fin k → R ↦ ¬Doom ((l ++ [c]) ++ List.ofFn v)).card * N
        ≤ ∑ c : R, ((if Doom (l ++ [c]) then 0 else N ^ k * N) +
            (∑ i ∈ range k, b (l.length + (i + 1))) * N ^ k) := Finset.sum_le_sum fun c _ ↦ hsplit c
      _ = (univ.filter fun c ↦ ¬Doom (l ++ [c])).card * (N ^ k * N) +
            N * ((∑ i ∈ range k, b (l.length + (i + 1))) * N ^ k) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
          ← Finset.sum_filter_add_sum_filter_not univ (fun c ↦ Doom (l ++ [c]))]
        simp only [Finset.sum_ite_of_true (fun c hc ↦ (Finset.mem_filter.mp hc).2),
          Finset.sum_ite_of_false (fun c hc ↦ (Finset.mem_filter.mp hc).2), Finset.sum_const_zero,
          zero_add, Finset.sum_const, smul_eq_mul]
        rfl
      _ ≤ b l.length * (N ^ k * N) + N * ((∑ i ∈ range k, b (l.length + (i + 1))) * N ^ k) :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ (hb l hl)) _
      _ = _ := by simp only [add_zero]; ring

end FR
