-- G6: this module also holds the former modules `FRVIREval`, `FRKindWeight`, `FRPubTarget` (one section each, in import order).
import FRSpartan
import FRBlake2sWalk
import FRVIRFinalsCoreSG
import FRSoundnessCoreTruths
import FRBlockKinds

section G6_FRVIREval

-- New for `flock-recursive` (BLUEPRINT §4.4, §7, A.8, stage S-E2).

/-!
# The op implementations owned by L-circ: `walkA`, `walkB`, `kindInd`

BLUEPRINT A.8 and S-0-m2's owner table: S-E1/S-E2 own `walkA/B`, `evalM/L` and `kindInd`. This
module gives each op its **specification** (the mathematical definition) and its computable
**implementation**, and proves them equal (the S-E2 part of `impl ⊨ OpSpec`):

* `walkA`, `walkB` (`walkA_eq`, `walkB_eq`): the circuit walk `walkAB` at row weights `rowW` and
  column weights `colW` is `Σ_k rowW[k] · (A₀ colW)_k` (resp. `B₀`), `A₀`, `B₀` the BLAKE2s
  circuit's matrices (S-E1's `walk_eq_sum`); the per-kind masking is `maskRows`'s, before the walk;
* `kindInd` (`kindInd_eq`): the indicator MLE `Ĩnd_κ(r′) = Σ_t eq(r′, t) Ind_κ(t)` over the node's
  `2^16` blocks is a sum over `κ`'s intervals (`Layout.kindIvs`) of differences of prefix sums,
  `O(intervals · 16²)`.

* `evalM`, `evalL` (`evalM_eq`, `evalL_eq`): the MLE of a sparse matrix given by R1CS rows —
  `Σ_{x,y} eq(τ, x) eq(σ, y) M[x][y]` over the cube — is the sum over its entries of
  `coef · eq(τ, row) · eq(σ, cell)` (`sparse_eq`); `evalM`'s rows are `compileMux (gen fin .mux)`'s
  for both slots (`nodeRows`), `evalL`'s the Lr rows (a parameter until L's row list is fixed).
-/

namespace FR
namespace Eval
open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-! ## `walkA`, `walkB` -/

/-- An array as a function on the circuit's positions. -/
def onPos (a : Array F) (k : Pos Blake2sCircuit.m) : F := a.getD k.val 0

/-- The input positions of the block (`k < 256 ∨ 512 ≤ k < 1152`: `h`, the message, the counter). -/
def inPos : List ℕ := List.range 256 ++ List.range' 512 640

/-- **`walkAB` with the input rows summed over the 896 input positions** (S-E4: `walkAB`'s two
`Finset` sums over all `2^14` positions took 5.5 ms of its 14.5 ms; `walkABF_eq`). -/
def walkABF (e wt : Pos Blake2sCircuit.m → F) : F × F :=
  let o := walkOps e wt
  let c := wt constPos
  let r := o.compressW.run ⟨gateBase, (0, 0)⟩
  let s₂ := (outPairs r.1).foldl (fun s p ↦ o.upd s p.1 p.2 c) r.2.acc
  let se := inPos.foldl (fun a k => a + e (pos k) * wt (pos k)) 0
  let sc := inPos.foldl (fun a k => a + e (pos k)) 0
  (s₂.1 + se + e constPos * c, s₂.2 + sc * c + e constPos * c)

theorem foldl_add_eq {α : Type*} (f : α → F) (l : List α) (a : F) :
    l.foldl (fun x k => x + f k) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons k l ih => simp [ih, add_assoc]

theorem sum_range_list (h : ℕ → F) (N : ℕ) :
    ∑ n ∈ Finset.range N, h n = ((List.range N).map h).sum := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

/-- The input rows' summand at position `n`. -/
def inSum (f : Pos Blake2sCircuit.m → F) (n : ℕ) : F :=
  if n < 256 ∨ (512 ≤ n ∧ n < 1152) then f (pos n) else 0

/-- A sum over the input positions of the block. -/
theorem sum_inPos (f : Pos Blake2sCircuit.m → F) :
    (∑ k : Pos Blake2sCircuit.m, if k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152) then f k else 0) =
      (inPos.map fun k => f (pos k)).sum := by
  have hf : ∀ k : Pos Blake2sCircuit.m,
      (if k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152) then f k else 0) = inSum f k.val := fun k => by
    have : pos (m := Blake2sCircuit.m) k.val = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
    simp only [inSum, this]
  rw [Finset.sum_congr rfl (fun k _ => hf k), Fin.sum_univ_eq_sum_range (inSum f) (2 ^ 14)]
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (show 0 ≤ 256 by norm_num)
    (show 256 ≤ 2 ^ 14 by norm_num), ← Finset.sum_Ico_consecutive _ (show 256 ≤ 512 by norm_num)
    (show 512 ≤ 2 ^ 14 by norm_num), ← Finset.sum_Ico_consecutive _ (show 512 ≤ 1152 by norm_num)
    (show 1152 ≤ 2 ^ 14 by norm_num)]
  have h1 : ∑ n ∈ Finset.Ico 0 256, inSum f n = ∑ n ∈ Finset.range 256, f (pos n) := by
    rw [← Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun n hn => ?_
    have := Finset.mem_range.1 hn
    simp only [inSum, show n < 256 ∨ (512 ≤ n ∧ n < 1152) from Or.inl this, if_true]
  have h2 : ∑ n ∈ Finset.Ico 256 512, inSum f n = 0 := Finset.sum_eq_zero fun n hn => by
    have := Finset.mem_Ico.1 hn
    simp only [inSum, show ¬ (n < 256 ∨ (512 ≤ n ∧ n < 1152)) by omega, if_false]
  have h3 : ∑ n ∈ Finset.Ico 512 1152, inSum f n = ∑ i ∈ Finset.range 640, f (pos (512 + i)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    simp only [inSum, show 512 + i < 256 ∨ (512 ≤ 512 + i ∧ 512 + i < 1152) by omega, if_true]
  have h4 : ∑ n ∈ Finset.Ico 1152 (2 ^ 14), inSum f n = 0 := Finset.sum_eq_zero fun n hn => by
    have := Finset.mem_Ico.1 hn
    simp only [inSum, show ¬ (n < 256 ∨ (512 ≤ n ∧ n < 1152)) by omega, if_false]
  rw [h1, h2, h3, h4, inPos, List.map_append, List.sum_append, List.range'_eq_map_range,
    List.map_map, sum_range_list, sum_range_list, zero_add, add_zero]
  rfl

theorem walkABF_eq (e wt : Pos Blake2sCircuit.m → F) : walkABF e wt = walkAB e wt := by
  unfold walkABF walkAB
  dsimp only
  rw [foldl_add_eq, foldl_add_eq, zero_add, zero_add]
  simp only [sum_inPos, List.sum_map_mul_right]

/-- The walk (implementation). -/
def walkImpl (rowW colW : Array F) : F × F := walkABF (onPos rowW) (onPos colW)

/-- **`walkA`'s specification**: `Σ_k rowW[k] · (A₀ colW)_k`. -/
noncomputable def walkSpecA (rowW colW : Array F) : F :=
  ∑ k, onPos rowW k * BlockR1CS.mulVec blake2sCircuit.toBlockR1CS.A (onPos colW) k

/-- **`walkB`'s specification**. -/
noncomputable def walkSpecB (rowW colW : Array F) : F :=
  ∑ k, onPos rowW k * BlockR1CS.mulVec blake2sCircuit.toBlockR1CS.B (onPos colW) k

theorem walkA_eq (rowW colW : Array F) : (walkImpl rowW colW).1 = walkSpecA rowW colW := by
  simp only [walkImpl, walkABF_eq, walk_eq_sum, walkSpecA]

theorem walkB_eq (rowW colW : Array F) : (walkImpl rowW colW).2 = walkSpecB rowW colW := by
  simp only [walkImpl, walkABF_eq, walk_eq_sum, walkSpecB]

/-! ## `kindInd` -/

/-- The bit weight of `eq(r′, x)`. -/
def eS {n : ℕ} (r' : Fin n → F) (l : Fin n) (b : Bool) : F := if b then r' l else 1 - r' l

/-- **The indicator MLE as prefix sums** (single-`eq` form of `selWeight_eq`). -/
theorem ind_mle_eq {n : ℕ} (r' : Fin n → F) (ivs : List (ℕ × ℕ)) (h : ∀ p ∈ ivs, p.1 ≤ p.2) :
    mle (fun x ↦ selOf ivs x) r' =
      (ivs.map fun p ↦ prefixP n (eS r') p.2 - prefixP n (eS r') p.1).sum := by
  induction ivs with
  | nil => simp [selOf, mle]
  | cons p ps ih =>
    have hp := h p (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ← ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq),
      prefixP_eq, prefixP_eq, ← Finset.sum_sub_distrib]
    simp only [selOf, List.map_cons, List.sum_cons, mle, mul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [eq_cube]
    simp only [eS]
    split_ifs <;> first | ring1 | (exfalso; omega)

/-- The point as a function (`r′`'s 16 block coordinates). -/
def pt16 (r : Array F) (l : Fin 16) : F := r.getD l.val 0

/-- **`kindInd`'s specification**: the indicator MLEs of the kinds at `r′`, in `blockKinds` order. -/
noncomputable def kindIndSpec (r : Array F) : Array F :=
  (blockKinds.map fun κ ↦ mle (fun x : Fin (2 ^ 16) ↦ selOf (Layout.kindIvs κ) x) (pt16 r)).toArray

/-- **`kindInd`'s implementation**: prefix sums over the kind's intervals. -/
def kindIndImpl (r : Array F) : Array F :=
  (blockKinds.map fun κ ↦ ((Layout.kindIvs κ).map fun p ↦
    prefixP 16 (eS (pt16 r)) p.2 - prefixP 16 (eS (pt16 r)) p.1).sum).toArray

/-- Every kind interval is ordered. -/
theorem chained_lt : ∀ (l : List Layout.Iv), Layout.chained l = true → ∀ iv ∈ l, iv.lo < iv.hi
  | [], _, _, h => by simp at h
  | [a], hc, iv, h => by simp_all [Layout.chained]
  | a :: b :: t, hc, iv, h => by
    simp only [Layout.chained, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases List.mem_cons.1 h with rfl | h
    · exact hc.1.1
    · exact chained_lt (b :: t) hc.2 iv h

theorem kindIvs_le (κ : BlockKind) : ∀ p ∈ Layout.kindIvs κ, p.1 ≤ p.2 := by
  intro p hp
  simp only [Layout.kindIvs, List.mem_map, List.mem_filter] at hp
  obtain ⟨iv, ⟨hiv, -⟩, rfl⟩ := hp
  exact (chained_lt _ Layout.nodeLayout_chained iv hiv).le

theorem kindInd_eq (r : Array F) : kindIndImpl r = kindIndSpec r := by
  unfold kindIndImpl kindIndSpec
  exact congrArg List.toArray
    (List.map_congr_left fun κ _ ↦ (ind_mle_eq (pt16 r) _ (kindIvs_le κ)).symm)

/-! ## `evalM`, `evalL`: sparse matrix MLEs -/

/-- A sparse matrix: `(row, column, coefficient)` entries. -/
abbrev Entries := List (ℕ × ℕ × F)

/-- Entry `(x, y)`. -/
def entry (E : Entries) (x y : ℕ) : F :=
  ((E.filter fun e => e.1 = x ∧ e.2.1 = y).map (·.2.2)).sum

/-- **The matrix MLE** (specification): `Σ_{x,y} eq(τ, x) eq(σ, y) M[x][y]`. -/
noncomputable def matMLE {a b : ℕ} (E : Entries) (τ : Fin a → F) (σ : Fin b → F) : F :=
  ∑ x : Fin (2 ^ a), ∑ y : Fin (2 ^ b), eq τ (cube x) * eq σ (cube y) * entry E x y

/-- `eq(τ, i)` by the bits of `i`. -/
def eqAt {n : ℕ} (τ : Fin n → F) (i : ℕ) : F := ∏ l : Fin n, if i.testBit l then τ l else 1 - τ l

/-- **The sparse evaluation** (implementation): one product per entry. -/
def sparseEval {a b : ℕ} (E : Entries) (τ : Fin a → F) (σ : Fin b → F) : F :=
  (E.map fun e => if e.1 < 2 ^ a ∧ e.2.1 < 2 ^ b then e.2.2 * eqAt τ e.1 * eqAt σ e.2.1 else 0).sum

private theorem sum_fin_ite {n : ℕ} (c : ℕ) (g : Fin n → F) :
    ∑ y : Fin n, (if y.val = c then g y else 0) = if h : c < n then g ⟨c, h⟩ else 0 := by
  split_ifs with hc
  · rw [Finset.sum_eq_single ⟨c, hc⟩ (fun u _ hu => ite_eq_right fun h => hu (Fin.ext h))
      (by simp), ite_eq_left rfl]
  · exact Finset.sum_eq_zero fun u _ => by
      simp only [ite_eq_right_iff]; intro h; exact absurd (h ▸ u.isLt) hc

theorem sparse_eq {a b : ℕ} (E : Entries) (τ : Fin a → F) (σ : Fin b → F) :
    sparseEval E τ σ = matMLE E τ σ := by
  induction E with
  | nil => simp [sparseEval, matMLE, entry]
  | cons e E ih =>
    have he : ∀ x y, entry (e :: E) x y = (if x = e.1 then
        (if y = e.2.1 then e.2.2 else 0) else 0) + entry E x y := fun x y => by
      simp only [entry, List.filter_cons]
      by_cases h1 : e.1 = x <;> by_cases h2 : e.2.1 = y <;> simp [h1, h2, eq_comm] <;>
        intro h <;> simp_all
    simp only [sparseEval, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [matMLE, he, mul_add, Finset.sum_add_distrib]
    congr 1
    have : ∀ x : Fin (2 ^ a), ∑ y : Fin (2 ^ b), eq τ (cube x) * eq σ (cube y) *
        (if x.val = e.1 then (if y.val = e.2.1 then e.2.2 else 0) else 0) =
        if x.val = e.1 then (if h : e.2.1 < 2 ^ b then
          eq τ (cube x) * eq σ (cube (⟨e.2.1, h⟩ : Fin (2 ^ b))) * e.2.2 else 0) else 0 := by
      intro x
      by_cases hx : x.val = e.1
      · simp only [hx, ↓reduceIte]
        rw [← sum_fin_ite e.2.1 (fun y : Fin (2 ^ b) => eq τ (cube x) * eq σ (cube y) * e.2.2)]
        exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
      · simp [hx]
    simp only [this, sum_fin_ite]
    by_cases ha : e.1 < 2 ^ a <;> by_cases hb : e.2.1 < 2 ^ b <;> simp [ha, hb, eq_cube, eqAt]
    ring

/-- The entries of a row list's `A`, `B`, `C` (row number, cell, coefficient). -/
def entriesOf (sel : Circ.Row → Circ.Lin) (rows : List Circ.Row) : Entries :=
  rows.zipIdx.flatMap fun p => (sel p.1).map fun t => (p.2, t.1, t.2)

/-- A point as a function. -/
def ptOf (n : ℕ) (r : Array F) (l : Fin n) : F := r.getD l.val 0

/-- **The row matrices' evaluation** (implementation) and its specification. -/
def evalRows (a b : ℕ) (rows : List Circ.Row) (τ σ : Array F) : F × F × F :=
  (sparseEval (entriesOf Circ.Row.a rows) (ptOf a τ) (ptOf b σ),
   sparseEval (entriesOf Circ.Row.b rows) (ptOf a τ) (ptOf b σ),
   sparseEval (entriesOf Circ.Row.c rows) (ptOf a τ) (ptOf b σ))

noncomputable def evalRowsSpec (a b : ℕ) (rows : List Circ.Row) (τ σ : Array F) : F × F × F :=
  (matMLE (entriesOf Circ.Row.a rows) (ptOf a τ) (ptOf b σ),
   matMLE (entriesOf Circ.Row.b rows) (ptOf a τ) (ptOf b σ),
   matMLE (entriesOf Circ.Row.c rows) (ptOf a τ) (ptOf b σ))

theorem evalRows_eq (a b : ℕ) (rows : List Circ.Row) (τ σ : Array F) :
    evalRows a b rows τ σ = evalRowsSpec a b rows τ σ := by
  simp only [evalRows, evalRowsSpec, sparse_eq]

/-- **`evalM`** (A.8: `τ` 21 row coordinates, `σ` 23 cell coordinates). -/
def evalMImpl (fin : Finals) (τ σ : Array F) : F × F × F := evalRows 21 23 (Layout.nodeRows fin) τ σ

/-- **`evalM_eq`**: the implementation is the MLE of the node's M matrices. -/
theorem evalM_eq (fin : Finals) (τ σ : Array F) :
    evalMImpl fin τ σ = evalRowsSpec 21 23 (Layout.nodeRows fin) τ σ := evalRows_eq _ _ _ _ _

/-- **`evalL`** over L's rows `lRows` (A.7: `τ` 15, `σ` 23). -/
def evalLImpl (lRows : List Circ.Row) (τ σ : Array F) : F × F × F := evalRows 15 23 lRows τ σ

theorem evalL_eq (lRows : List Circ.Row) (τ σ : Array F) :
    evalLImpl lRows τ σ = evalRowsSpec 15 23 lRows τ σ := evalRows_eq _ _ _ _ _

end Eval
end FR

end G6_FRVIREval

section G6_FRKindWeight

-- New for `flock-recursive` (BLUEPRINT §2.3 step 3, A.8 `rsWeight`, A.11; revision 3.16, R-V-M1 (a);
-- stage INT-5).

/-!
# RS claim 2's kind factor on the node layout (`rsWeight`, revision 3.16)

R-V-M1, ruling (a): the Lc claim's ring-switching weight carries `W_β`'s kind factor. At Frobenius
stage `k` (`q = p^(2^k)` the claim point's block coordinates, `ρ` the final point's, `β_k =
β^(2^k)`), A.8's pattern-interval sum is

`kwS n β_k q ρ = Σ_{i<8} β_k^i Σ_{t < 2^n} Ind_{κ_i}(t) · eq(q, t) · eq(ρ, t)`,

`κ_i` the node kinds in `blockKinds` order after `chain` (`v_i`'s kind in `finLc`), `Ind_κ` the
union of the kind's intervals in `Layout.nodeLayout`, with `free` extended to `[wmBase, 2^n)`
(`ivsQ`; the complement of the hash blocks). `FRRingSwitch.rsWeight_kind_eq` is the statement that
the Φ form of `eq(p, ·)·B_β` has this extension.

* **Specification** `kwS` (above, over `Fin n` points and `FRSpartan.selOf`).
* **Implementation** `kwI`: per-bit weights `e_l(1) = q_l ρ_l`, `e_l(0) = (1 − q_l)(1 − ρ_l)`, the
  prefix products `Π_{l'<l} (e_{l'}(0) + e_{l'}(1))`, and the prefix sums `pfx` (high bit first,
  one product per bit); each kind is a short list of **items** (`plan`): intervals, single blocks
  and the path runs as a **bit pattern** (the `hashB1` / `hashB2` path blocks alternate, so they
  are the even / odd blocks of a 32-block run: bit 0's weight times a 15-bit range sum). 23 items.
* **`kwI_eq`**: `kwI = kwS` for `n ≥ 16`. The items are checked against `Layout.kindIvs` by
  `planFix_ivs` (a kernel `decide` on the concrete interval lists).
* **`kwS_one`**: `β = 1` gives the plain `eq(q, ρ)`: the kinds partition `[0, 2^n)` (`part_one`).
  A leaf passes `β = 1`, so its claim 2 is unchanged.
* Controls: `kwS_cube` (at a Boolean point the factor is `β^i` of the block's kind), `kwS_hashA`
  (+: `β^3` at `hashStmt`'s block A; −: not the plain weight `1`).
-/

namespace FR
namespace KW
open Finset

/-! ## Product weights and prefix sums -/

section Prefix
variable {R : Type*} [CommRing R]

/-- `Π_{l<n} e_l(bit l of t)`. -/
def prodE (e : ℕ → Bool → R) (n t : ℕ) : R := ∏ l ∈ range n, e l (t.testBit l)

/-- The prefix sum `Σ_{t < x, t < 2^n} Π_l e_l(t_l)`. -/
def psum (e : ℕ → Bool → R) (n x : ℕ) : R :=
  ∑ t ∈ range (2 ^ n), if t < x then prodE e n t else 0

theorem prodE_lo {e : ℕ → Bool → R} {n t : ℕ} (ht : t < 2 ^ n) :
    prodE e (n + 1) t = prodE e n t * e n false := by
  rw [prodE, prod_range_succ, Nat.testBit_lt_two_pow ht]; rfl

theorem prodE_hi {e : ℕ → Bool → R} {n t : ℕ} (ht : t < 2 ^ n) :
    prodE e (n + 1) (2 ^ n + t) = prodE e n t * e n true := by
  rw [prodE, prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ht,
    Bool.not_false]
  refine congrArg (· * e n true) ?_
  exact prod_congr rfl fun l hl ↦ by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hl)]

theorem sum_range_pow_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ t ∈ range (2 ^ (n + 1)), f t =
      ∑ t ∈ range (2 ^ n), f t + ∑ t ∈ range (2 ^ n), f (2 ^ n + t) := by
  rw [pow_succ, mul_two, sum_range_add]

theorem sum_prodE (e : ℕ → Bool → R) (n : ℕ) :
    ∑ t ∈ range (2 ^ n), prodE e n t = ∏ l ∈ range n, (e l false + e l true) := by
  induction n with
  | zero => simp [prodE]
  | succ n ih =>
    rw [sum_range_pow_succ, prod_range_succ, ← ih, mul_add, sum_mul, sum_mul]
    refine congrArg₂ (· + ·) ?_ ?_ <;> refine sum_congr rfl fun t ht ↦ ?_
    · rw [prodE_lo (mem_range.1 ht)]
    · rw [prodE_hi (mem_range.1 ht)]

theorem psum_succ (e : ℕ → Bool → R) (n x : ℕ) :
    psum e (n + 1) x = (∑ t ∈ range (2 ^ n), if t < x then prodE e n t * e n false else 0) +
      ∑ t ∈ range (2 ^ n), if 2 ^ n + t < x then prodE e n t * e n true else 0 := by
  rw [psum, sum_range_pow_succ]
  refine congrArg₂ (· + ·) ?_ ?_ <;> refine sum_congr rfl fun t ht ↦ ?_
  · rw [prodE_lo (mem_range.1 ht)]
  · rw [prodE_hi (mem_range.1 ht)]

/-- **The prefix sum, high bit first**, from the tables `e0 l = e_l(0)`, `e1 l = e_l(1)`,
`sp l = Π_{l'<l} (e_{l'}(0) + e_{l'}(1))`, `lw l = sp l · e_l(0)`: one product per bit. -/
def pfx (e0 e1 lw sp : ℕ → R) : ℕ → ℕ → R
  | 0, x => if 0 < x then 1 else 0
  | n + 1, x =>
    if 2 ^ (n + 1) ≤ x then sp (n + 1)
    else if x.testBit n then lw n + e1 n * pfx e0 e1 lw sp n (x - 2 ^ n)
    else e0 n * pfx e0 e1 lw sp n x

theorem pfx_eq (e : ℕ → Bool → R) (e0 e1 lw sp : ℕ → R) (n : ℕ)
    (h0 : ∀ l < n, e0 l = e l false) (h1 : ∀ l < n, e1 l = e l true)
    (hs : ∀ l ≤ n, sp l = ∏ l' ∈ range l, (e l' false + e l' true))
    (hl : ∀ l < n, lw l = sp l * e l false) (x : ℕ) :
    pfx e0 e1 lw sp n x = psum e n x := by
  induction n generalizing x with
  | zero => rw [psum, pow_zero, sum_range_one]; simp [prodE, pfx]
  | succ n ih =>
    have ih' := ih (fun l h ↦ h0 l (by omega)) (fun l h ↦ h1 l (by omega))
      (fun l h ↦ hs l (by omega)) (fun l h ↦ hl l (by omega))
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ, mul_two]
    rw [pfx, psum_succ]
    split_ifs with hx hb
    · rw [hs _ le_rfl, ← sum_prodE, sum_range_pow_succ]
      refine congrArg₂ (· + ·) ?_ ?_ <;> refine sum_congr rfl fun t ht ↦ ?_
      · rw [if_pos (by have := mem_range.1 ht; omega), prodE_lo (mem_range.1 ht)]
      · rw [if_pos (by have := mem_range.1 ht; omega), prodE_hi (mem_range.1 ht)]
    · have hge : 2 ^ n ≤ x := by
        by_contra h
        rw [Nat.testBit_lt_two_pow (by omega)] at hb
        exact absurd hb (by simp)
      rw [hl n (by omega), hs n (by omega), ← sum_prodE, ih', psum, sum_mul, mul_sum,
        h1 n (by omega)]
      refine congrArg₂ (· + ·) ?_ ?_ <;> refine sum_congr rfl fun t ht ↦ ?_
      · rw [if_pos (by have := mem_range.1 ht; omega)]
      · by_cases h : t < x - 2 ^ n
        · rw [if_pos h, if_pos (by omega)]; ring
        · rw [if_neg h, if_neg (by omega), mul_zero]
    · have hlt : x < 2 ^ n := by
        by_contra h
        have e : x = 2 ^ n + (x - 2 ^ n) := by omega
        rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)] at hb
        exact hb rfl
      rw [ih', psum, mul_sum, h0 n (by omega),
        show (∑ t ∈ range (2 ^ n), if 2 ^ n + t < x then prodE e n t * e n true else 0) = 0 from
          sum_eq_zero fun t _ ↦ if_neg (by omega), add_zero]
      refine sum_congr rfl fun t _ ↦ ?_
      split_ifs <;> ring

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ t ∈ range (2 * m), f t = ∑ u ∈ range m, (f (2 * u) + f (2 * u + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

theorem prodE_even (e : ℕ → Bool → R) (n u : ℕ) :
    prodE e (n + 1) (2 * u) = prodE (fun l ↦ e (l + 1)) n u * e 0 false := by
  rw [prodE, prod_range_succ']
  refine congrArg₂ (· * ·) ?_ ?_
  · exact prod_congr rfl fun l _ ↦ by rw [Nat.testBit_add_one, Nat.mul_div_cancel_left _ two_pos]
  · simp [Nat.testBit_zero]

theorem prodE_odd (e : ℕ → Bool → R) (n u : ℕ) :
    prodE e (n + 1) (2 * u + 1) = prodE (fun l ↦ e (l + 1)) n u * e 0 true := by
  rw [prodE, prod_range_succ']
  refine congrArg₂ (· * ·) ?_ ?_
  · refine prod_congr rfl fun l _ ↦ ?_
    rw [Nat.testBit_add_one, show (2 * u + 1) / 2 = u by omega]
  · simp [Nat.testBit_zero, Nat.add_mod]

end Prefix

/-! ## Items: intervals, single blocks, bit patterns -/

/-- A set of blocks: the interval `[lo, hi)`, the block `c`, or the blocks `t` with bit 0 equal to
`c` and `⌊t/2⌋ ∈ [a, b)` (a run of alternating kinds). -/
inductive Item where
  | iv (lo hi : ℕ)
  | one (c : ℕ)
  | pat (c : Bool) (a b : ℕ)
  deriving DecidableEq, Repr

section Items
variable {R : Type*} [CommRing R]

theorem lsum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, sum_range_succ, ih]

/-- The item's indicator. -/
def Item.ind : Item → ℕ → R
  | .iv lo hi, t => if lo ≤ t ∧ t < hi then 1 else 0
  | .one c, t => if t = c then 1 else 0
  | .pat c a b, t => if t.testBit 0 = c ∧ a ≤ t / 2 ∧ t / 2 < b then 1 else 0

/-- The item as intervals (a pattern as its single blocks). -/
def Item.ivs : Item → List (ℕ × ℕ)
  | .iv lo hi => [(lo, hi)]
  | .one c => [(c, c + 1)]
  | .pat c a b => (List.range (b - a)).map fun u =>
      (2 * (a + u) + c.toNat, 2 * (a + u) + c.toNat + 1)

/-- Ordered bounds. -/
def Item.WF : Item → Prop
  | .iv lo hi => lo ≤ hi
  | .one _ => True
  | .pat _ a b => a ≤ b

instance (it : Item) : Decidable it.WF := by cases it <;> unfold Item.WF <;> infer_instance

/-- **The item's sum, fast**: `P` the prefix sum, `P'` the prefix sum over the bits above bit 0,
`pr` the product at a block, `z0`, `z1` bit 0's weights. -/
def Item.val (P P' pr : ℕ → R) (z0 z1 : R) (n : ℕ) : Item → R
  | .iv lo hi => P hi - P lo
  | .one c => if c < 2 ^ n then pr c else 0
  | .pat c a b => (if c then z1 else z0) * (P' b - P' a)

theorem ind_ivs (it : Item) (t : ℕ) :
    (it.ind t : R) = (it.ivs.map fun p ↦ if p.1 ≤ t ∧ t < p.2 then (1 : R) else 0).sum := by
  cases it with
  | iv lo hi => simp [Item.ind, Item.ivs]
  | one c =>
    simp only [Item.ind, Item.ivs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    split_ifs <;> first | rfl | omega
  | pat c a b =>
    simp only [Item.ind, Item.ivs, List.map_map, Function.comp_def, lsum_range]
    have key : ∀ u ∈ range (b - a),
        (if 2 * (a + u) + c.toNat ≤ t ∧ t < 2 * (a + u) + c.toNat + 1 then (1 : R) else 0) =
          if t / 2 - a = u then (if t.testBit 0 = c ∧ a ≤ t / 2 then 1 else 0) else 0 := by
      intro u _
      cases c <;> simp only [Nat.testBit_zero, Bool.toNat_false, Bool.toNat_true,
        decide_eq_false_iff_not, decide_eq_true_eq] <;> split_ifs <;> first | rfl | omega
    rw [sum_congr rfl key, sum_ite_eq]
    by_cases hP : t.testBit 0 = c <;>
      simp only [mem_range, hP, true_and, false_and, if_false, ite_self] <;>
      split_ifs <;> first | rfl | omega

/-- **Each item's fast value is its sum** (`n ≥ 1`; the pattern's `P'` is over `n − 1` bits). -/
theorem item_val (e : ℕ → Bool → R) (n : ℕ) (it : Item) (hw : it.WF) :
    (∑ t ∈ range (2 ^ (n + 1)), it.ind t * prodE e (n + 1) t) =
      it.val (psum e (n + 1)) (psum (fun l ↦ e (l + 1)) n) (prodE e (n + 1)) (e 0 false)
        (e 0 true) (n + 1) := by
  cases it with
  | iv lo hi =>
    simp only [Item.val, psum, ← sum_sub_distrib]
    refine sum_congr rfl fun t _ ↦ ?_
    simp only [Item.ind]
    have : lo ≤ hi := hw
    split_ifs <;> first | (exfalso; omega) | ring
  | one c =>
    simp only [Item.ind, Item.val, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
  | pat c a b =>
    have : a ≤ b := hw
    rw [pow_succ', sum_range_two_mul]
    simp only [Item.val, psum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    have h0 : (2 * u).testBit 0 = false := by simp [Nat.testBit_zero]
    have h1 : (2 * u + 1).testBit 0 = true := by simp [Nat.testBit_zero, Nat.add_mod]
    have d0 : 2 * u / 2 = u := by omega
    have d1 : (2 * u + 1) / 2 = u := by omega
    simp only [Item.ind, h0, h1, d0, d1, prodE_even, prodE_odd]
    cases c <;> simp only [Bool.false_eq_true, true_and, false_and, if_false, if_true,
      Bool.true_eq_false] <;> split_ifs <;> first | (exfalso; omega) | ring

end Items

/-! ## The node kinds' items -/

/-- The node kinds in `finLc`'s order `v_0 … v_7` (`blockKinds` without `chain`). -/
def nodeKinds : List BlockKind := blockKinds.tail

/-- Kind `κ`'s block intervals among `2^n` blocks: `Layout.kindIvs`, `free` extended to `2^n`. -/
def ivsQ (n : ℕ) (κ : BlockKind) : List (ℕ × ℕ) :=
  if κ = .free then [(Layout.wmBase, 2 ^ n)] else Layout.kindIvs κ

/-- WOTS slot `σ`'s first block. -/
def wB (σ : ℕ) : ℕ := Layout.wotsBase + Layout.wotsSlot * σ

/-- Slot `σ`'s path run: blocks `2·pathH σ … 2·pathH σ + 31` (`hashB1` even, `hashB2` odd). -/
def pathH (σ : ℕ) : ℕ := (wB σ + 466) / 2

open Layout in
/-- **The items of node kind `i < 7`** (`nodeKinds` order), in `nodeLayout`'s order. -/
def planFix : ℕ → List Item
  | 0 => [.iv 1 chainN, .iv (chainN + 1) (2 * chainN), .iv (wB 0 + 400) (wB 0 + 465),
      .iv (wB 1 + 400) (wB 1 + 465)]
  | 1 => [.one 0, .one chainN]
  | 2 => [.one (wB 0 + 465), .one (wB 1 + 465)]
  | 3 => [.one stmtBase, .one (stmtBase + 3)]
  | 4 => [.one (stmtBase + 1), .one (stmtBase + 4), .one (wB 0 + 399),
      .pat false (pathH 0) (pathH 0 + 16), .one (wB 1 + 399), .pat false (pathH 1) (pathH 1 + 16)]
  | 5 => [.one (stmtBase + 2), .one (stmtBase + 5), .pat true (pathH 0) (pathH 0 + 16),
      .pat true (pathH 1) (pathH 1 + 16)]
  | 6 => [.iv (wB 0) (wB 0 + 399), .iv (wB 1) (wB 1 + 399)]
  | _ => []

/-- **The items of node kind `i`** over `2^n` blocks (`free`: `[wmBase, 2^n)`). -/
def plan (n i : ℕ) : List Item := if i = 7 then [.iv Layout.wmBase (2 ^ n)] else planFix i

/-- **The items are the layout** (kernel-checked on the concrete lists). -/
theorem planFix_ivs : ∀ i < 7,
    (planFix i).flatMap Item.ivs = Layout.kindIvs (nodeKinds.getD i .free) := by decide +kernel

theorem planFix_wf : ∀ i < 7, ∀ it ∈ planFix i, it.WF := by decide +kernel

theorem nodeKinds_ne_free : ∀ i < 7, nodeKinds.getD i .free ≠ .free := by decide

theorem plan_ivs (n i : ℕ) (hi : i < 8) :
    (plan n i).flatMap Item.ivs = ivsQ n (nodeKinds.getD i .free) := by
  unfold plan ivsQ
  by_cases h7 : i = 7
  · subst h7; rfl
  · rw [if_neg h7, if_neg (nodeKinds_ne_free i (by omega)), planFix_ivs i (by omega)]

theorem wmBase_le {n : ℕ} (hn : 16 ≤ n) : Layout.wmBase ≤ 2 ^ n :=
  le_trans (by decide) (Nat.pow_le_pow_right (by norm_num) hn)

theorem plan_wf {n i : ℕ} (hn : 16 ≤ n) (hi : i < 8) : ∀ it ∈ plan n i, it.WF := by
  unfold plan
  split_ifs with h
  · simp only [List.mem_singleton]; rintro _ rfl; exact wmBase_le hn
  · exact planFix_wf i (by omega)

theorem sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (g : β → M) :
    ((L.flatMap f).map g).sum = (L.map fun x ↦ ((f x).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [List.flatMap_cons, ih]

theorem selOf_flatMap {R : Type*} [CommRing R] {n : ℕ} (L : List Item) (x : Fin (2 ^ n)) :
    (selOf (L.flatMap Item.ivs) x : R) = (L.map fun it ↦ (it.ind x.val : R)).sum := by
  simp only [selOf, sum_flatMap, ← ind_ivs]

theorem sum_lsum {M : Type*} [AddCommMonoid M] {α : Type*} (s : Finset ℕ) (L : List α)
    (f : α → ℕ → M) : ∑ t ∈ s, (L.map fun a ↦ f a t).sum = (L.map fun a ↦ ∑ t ∈ s, f a t).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [sum_add_distrib, ih]

theorem lprod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, prod_range_succ, ih]

/-! ## Specification -/

/-- The per-bit weight of `eq(q, t)·eq(ρ, t)`. -/
def ew (q ρ : ℕ → K) (l : ℕ) (b : Bool) : K :=
  (if b then q l else 1 - q l) * (if b then ρ l else 1 - ρ l)

/-- **The kind-weighted block weight** (A.8 `rsWeight`, claim 2, at one Frobenius stage):
`Σ_{i<8} β^i Σ_t Ind_{κ_i}(t) eq(q, t) eq(ρ, t)` over the `2^n` blocks. -/
def kwS (n : ℕ) (β : K) (q ρ : Fin n → K) : K :=
  ∑ i ∈ range 8, β ^ i * ∑ t : Fin (2 ^ n),
    selOf (ivsQ n (nodeKinds.getD i .free)) t * eq q (cube t) * eq ρ (cube t)

theorem eq_mul_eq (n : ℕ) (qf ρf : ℕ → K) (t : Fin (2 ^ n)) :
    eq (fun l : Fin n ↦ qf l) (cube t) * eq (fun l : Fin n ↦ ρf l) (cube t) =
      prodE (ew qf ρf) n t.val := by
  rw [eq_cube, eq_cube, ← prod_mul_distrib, prodE]
  exact Fin.prod_univ_eq_prod_range (fun l ↦ ew qf ρf l (t.val.testBit l)) n

/-! ## Implementation -/

/-- Prefix products `[1, s 0, s 0 · s 1, …]` (`m + 1` entries). -/
def spArr (s : ℕ → K) : ℕ → Array K
  | 0 => #[1]
  | m + 1 => let a := spArr s m; a.push (a.getD m 0 * s m)

theorem spArr_size (s : ℕ → K) (m : ℕ) : (spArr s m).size = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [spArr, ih]

theorem spArr_getD (s : ℕ → K) (m : ℕ) : ∀ l ≤ m, (spArr s m).getD l 0 = ∏ l' ∈ range l, s l' := by
  induction m with
  | zero => intro l hl; obtain rfl : l = 0 := by omega
            rfl
  | succ m ih =>
    intro l hl
    simp only [spArr, Array.getD_eq_getD_getElem?, Array.getElem?_push, spArr_size]
    split_ifs with h
    · subst h
      rw [Option.getD_some, prod_range_succ, ← ih m le_rfl, Array.getD_eq_getD_getElem?]
    · rw [← Array.getD_eq_getD_getElem?, ih l (by omega)]

theorem pfx_fun {R : Type*} [CommRing R] (e : ℕ → Bool → R) (e0 e1 lw sp : ℕ → R) (n : ℕ)
    (h0 : ∀ l < n, e0 l = e l false) (h1 : ∀ l < n, e1 l = e l true)
    (hs : ∀ l ≤ n, sp l = ∏ l' ∈ range l, (e l' false + e l' true))
    (hl : ∀ l < n, lw l = sp l * e l false) : pfx e0 e1 lw sp n = psum e n :=
  funext (pfx_eq e e0 e1 lw sp n h0 h1 hs hl)

/-- The items' values from the bit tables `g0 l = e_l(0)`, `g1 l = e_l(1)`. -/
def kwCore (n : ℕ) (β : K) (g0 g1 : ℕ → K) : K :=
  let sp := spArr (fun l ↦ g0 l + g1 l) n
  let lw : Array K := Array.ofFn fun l : Fin n ↦ sp.getD l 0 * g0 l
  let sp' := spArr (fun l ↦ g0 (l + 1) + g1 (l + 1)) (n - 1)
  let lw' : Array K := Array.ofFn fun l : Fin (n - 1) ↦ sp'.getD l 0 * g0 (l + 1)
  let P := pfx g0 g1 (fun l ↦ lw.getD l 0) (fun l ↦ sp.getD l 0) n
  let P' := pfx (fun l ↦ g0 (l + 1)) (fun l ↦ g1 (l + 1)) (fun l ↦ lw'.getD l 0)
    (fun l ↦ sp'.getD l 0) (n - 1)
  let pr : ℕ → K := fun c ↦ ((List.range n).map fun l ↦ if c.testBit l then g1 l else g0 l).prod
  ((List.range 8).map fun i ↦
    β ^ i * ((plan n i).map (Item.val P P' pr (g0 0) (g1 0) n)).sum).sum

/-- **The kind-weighted block weight, computed** (`kwI_eq`): per-bit tables `q_l ρ_l`,
`(1 − q_l)(1 − ρ_l)`, prefix products, then each kind's items by prefix sums (`pfx`), single
products and bit patterns. -/
def kwI (n : ℕ) (β : K) (qf ρf : ℕ → K) : K :=
  let a1 : Array K := Array.ofFn fun l : Fin n ↦ qf l * ρf l
  let a0 : Array K := Array.ofFn fun l : Fin n ↦ 1 - qf l - ρf l + a1.getD l 0
  kwCore n β (fun l ↦ a0.getD l 0) (fun l ↦ a1.getD l 0)

theorem kwCore_eq {n : ℕ} (hn : 16 ≤ n) (β : K) (e : ℕ → Bool → K) (g0 g1 : ℕ → K)
    (h0 : ∀ l < n, g0 l = e l false) (h1 : ∀ l < n, g1 l = e l true) :
    kwCore n β g0 g1 = ∑ i ∈ range 8, β ^ i *
      ((plan n i).map fun it ↦ ∑ t ∈ range (2 ^ n), it.ind t * prodE e n t).sum := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpr : (fun c : ℕ ↦ ((List.range (m + 1)).map fun l ↦
      if c.testBit l then g1 l else g0 l).prod) = prodE e (m + 1) := by
    funext c
    rw [lprod_range, prodE]
    refine prod_congr rfl fun l hl ↦ ?_
    have := mem_range.1 hl
    cases c.testBit l
    · exact h0 l this
    · exact h1 l this
  simp only [kwCore, Nat.add_sub_cancel]
  rw [pfx_fun e _ _ _ _ (m + 1) h0 h1 ?hs ?hl,
    pfx_fun (fun l ↦ e (l + 1)) _ _ _ _ m (fun l hl ↦ h0 (l + 1) (by omega))
      (fun l hl ↦ h1 (l + 1) (by omega)) ?hs' ?hl', lsum_range, hpr, h0 0 (by omega),
    h1 0 (by omega)]
  · refine sum_congr rfl fun i hi ↦ congrArg _ (congrArg List.sum
      (List.map_congr_left fun it hit ↦ ?_))
    exact (item_val e m it (plan_wf hn (mem_range.1 hi) it hit)).symm
  case hs =>
    intro l hl
    rw [spArr_getD _ _ l hl]
    exact prod_congr rfl fun l' hl' ↦ by
      have := mem_range.1 hl'
      rw [h0 l' (by omega), h1 l' (by omega)]
  case hl =>
    intro l hl
    rw [getD_ofFn, dif_pos hl, h0 l hl]
  case hs' =>
    intro l hl
    rw [spArr_getD _ _ l hl]
    exact prod_congr rfl fun l' hl' ↦ by
      have := mem_range.1 hl'
      rw [h0 (l' + 1) (by omega), h1 (l' + 1) (by omega)]
  case hl' =>
    intro l hl
    rw [getD_ofFn, dif_pos (by omega)]
    exact congrArg _ (h0 (l + 1) (by omega))

/-- The kind-weighted block weight as the items' sums (`kwI_eq`'s and `kwS_keys`' first step). -/
theorem kwS_items (n : ℕ) (β : K) (qf ρf : ℕ → K) :
    ∑ i ∈ range 8, β ^ i *
      ((plan n i).map fun it ↦ ∑ t ∈ range (2 ^ n), it.ind t * prodE (ew qf ρf) n t).sum =
    kwS n β (fun l ↦ qf l) (fun l ↦ ρf l) := by
  rw [kwS]
  refine sum_congr rfl fun i hi ↦ congrArg _ ?_
  rw [← plan_ivs n i (mem_range.1 hi)]
  simp only [mul_assoc, eq_mul_eq, selOf_flatMap]
  rw [Fin.sum_univ_eq_sum_range (fun t ↦ ((plan n i).map fun it ↦ (it.ind t : K)).sum *
    prodE (ew qf ρf) n t) (2 ^ n)]
  simp only [← List.sum_map_mul_right]
  rw [sum_lsum]

/-- **`kwI` meets `kwS`** on at least 16 block coordinates. -/
theorem kwI_eq {n : ℕ} (hn : 16 ≤ n) (β : K) (qf ρf : ℕ → K) :
    kwI n β qf ρf = kwS n β (fun l ↦ qf l) (fun l ↦ ρf l) := by
  have g1e : ∀ l < n, (Array.ofFn fun l : Fin n ↦ qf l * ρf l).getD l 0 = ew qf ρf l true :=
    fun l hl ↦ by rw [getD_ofFn, dif_pos hl]; simp [ew]
  have g0e : ∀ l < n, (Array.ofFn fun l : Fin n ↦ 1 - qf l - ρf l +
      (Array.ofFn fun l : Fin n ↦ qf l * ρf l).getD l 0).getD l 0 = ew qf ρf l false :=
    fun l hl ↦ by rw [getD_ofFn, dif_pos hl, g1e l hl]; simp only [ew, if_true, Bool.false_eq_true, if_false]; ring
  rw [kwI, kwCore_eq hn β (ew qf ρf) _ _ g0e g1e, kwS_items]

/-! ## A leaf's factor is trivial: the kinds partition the blocks -/

/-- `[lo, hi)` intervals chained from `a` to `b`, in order and without gaps. -/
def chainFrom : ℕ → List (ℕ × ℕ) → ℕ → Bool
  | a, [], b => a == b
  | a, p :: ps, b => p.1 == a && decide (p.1 ≤ p.2) && chainFrom p.2 ps b

theorem chainFrom_le : ∀ {a b : ℕ} {L : List (ℕ × ℕ)}, chainFrom a L b = true → a ≤ b
  | a, b, [], h => by simp [chainFrom] at h; omega
  | a, b, p :: ps, h => by
    simp only [chainFrom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have := chainFrom_le h.2; omega

theorem chainFrom_sum {R : Type*} [CommRing R] (t : ℕ) :
    ∀ {a b : ℕ} {L : List (ℕ × ℕ)}, chainFrom a L b = true →
      (L.map fun p ↦ if p.1 ≤ t ∧ t < p.2 then (1 : R) else 0).sum =
        if a ≤ t ∧ t < b then 1 else 0
  | a, b, [], h => by
    simp only [chainFrom, beq_iff_eq] at h; subst h; simp
  | a, b, p :: ps, h => by
    simp only [chainFrom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have hb := chainFrom_le h.2
    rw [List.map_cons, List.sum_cons, chainFrom_sum t h.2]
    obtain ⟨⟨h1, h2⟩, -⟩ := h
    split_ifs <;> first | (exfalso; omega) | simp

/-- The layout's intervals below `wmBase` (every kind but `free`), in address order. -/
def fixL : List (ℕ × ℕ) := Layout.nodeLayout.dropLast.map fun iv ↦ (iv.lo, iv.hi)

theorem fixL_chain : chainFrom 0 fixL Layout.wmBase = true := by decide +kernel

/-- The seven non-`free` node kinds' intervals are the layout's below `wmBase`, regrouped. -/
theorem kinds_perm :
    ((List.range 7).flatMap fun i ↦ Layout.kindIvs (nodeKinds.getD i .free)).Perm fixL := by
  decide +kernel

/-- **The kinds partition the blocks** (`Sel ≡ 1`, `free` the complement up to `2^n`). -/
theorem part_one {R : Type*} [CommRing R] {n : ℕ} (hn : 16 ≤ n) (t : Fin (2 ^ n)) :
    ∑ i ∈ range 8, (selOf (ivsQ n (nodeKinds.getD i .free)) t : R) = 1 := by
  rw [sum_range_succ, ← lsum_range]
  have h7 : ∀ i ∈ List.range 7, (selOf (ivsQ n (nodeKinds.getD i .free)) t : R) =
      selOf (Layout.kindIvs (nodeKinds.getD i .free)) t := fun i hi ↦ by
    rw [ivsQ, if_neg (nodeKinds_ne_free i (List.mem_range.1 hi))]
  rw [List.map_congr_left h7]
  simp only [selOf]
  rw [← sum_flatMap, (kinds_perm.map _).sum_eq, chainFrom_sum t.val fixL_chain]
  simp only [ivsQ, show nodeKinds.getD 7 .free = .free from rfl, if_true, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have := t.isLt
  have := wmBase_le hn
  split_ifs <;> first | (exfalso; omega) | simp

/-- **A leaf's claim 2 is the plain `eq`** (`β = 1`): `kwS n 1 q ρ = eq(q, ρ)`. -/
theorem kwS_one {n : ℕ} (hn : 16 ≤ n) (q ρ : Fin n → K) : kwS n 1 q ρ = eq q ρ := by
  rw [kwS, ← eq_mle q ρ]
  simp only [one_pow, one_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [← sum_mul, ← sum_mul, part_one hn t, one_mul, eq_swap (cube t) ρ]

/-! ## Controls -/

/-- At a Boolean point the factor is `Σ_i β^i Ind_{κ_i}(t₀)`: `β^i` of the block's kind. -/
theorem kwS_cube (n : ℕ) (β : K) (t₀ : Fin (2 ^ n)) :
    kwS n β (cube t₀) (cube t₀) = ∑ i ∈ range 8, β ^ i * selOf (ivsQ n (nodeKinds.getD i .free)) t₀ := by
  refine sum_congr rfl fun i _ ↦ congrArg _ ?_
  simp only [eq_cube_cube, ← ite_and, and_self, mul_ite, mul_one, mul_zero]
  simp

/-- `hashStmt`'s block A of slot 1. -/
def tA : Fin (2 ^ 16) := ⟨Layout.stmtBase, by decide⟩

theorem selOf_tA : ∀ i < 8, (selOf (ivsQ 16 (nodeKinds.getD i .free)) tA : ℤ) =
    if i = 3 then 1 else 0 := by decide +kernel

theorem selOf_cast {n : ℕ} (ivs : List (ℕ × ℕ)) (x : Fin (2 ^ n)) :
    (selOf ivs x : K) = ((selOf ivs x : ℤ) : K) := by
  simp only [selOf, Int.cast_list_sum, List.map_map, Function.comp_def, Int.cast_ite,
    Int.cast_one, Int.cast_zero]

/-- (+) **The factor at `hashStmt`'s block A is `β^3`** (`hashA` is `v_3`'s kind). -/
theorem kwS_hashA (β : K) : kwS 16 β (cube tA) (cube tA) = β ^ 3 := by
  rw [kwS_cube, sum_eq_single 3]
  · rw [selOf_cast, selOf_tA 3 (by norm_num), if_pos rfl, Int.cast_one, mul_one]
  · intro i hi h3
    rw [selOf_cast, selOf_tA i (mem_range.1 hi), if_neg h3, Int.cast_zero, mul_zero]
  · simp

/-- (−) **… so it is not the plain weight** (R-V-M1's defect): at `β = 0` the kind-weighted value
at block A is `0`, the plain `eq` is `1`. -/
theorem kwS_hashA_ne_plain : kwS 16 0 (cube tA) (cube tA) ≠ eq (cube tA) (cube tA) := by
  rw [kwS_hashA, eq_cube_cube, if_pos rfl]
  simp

/-! ## The fast form (S-T1): dyadic blocks, merged keys, the `F` side

Per stage the value is a sum over **blocks**: `[0, x)` is the union of the dyadic blocks
`{t : t >>> (j+1) = x >>> (j+1), bit j of t = 0}` over the set bits `j` of `x` (`cubesOf`), each
with weight (fixed bits' product) · `Π_{l<j} s_l`, `s_l = e_l(0) + e_l(1)` (`cubeW`). An item is two
signed prefix sums (characteristic two: the signs drop), a pattern two prefix sums over bits
`1…n-1` times bit 0's weight. The blocks of all items, merged by key (`grpM`, `grpP`), are a closed
constant. The fixed bits' product splits as an `F` part (the claim point's side, `q ∈ F`) times a
`K` part (`ρ`'s, the same at every stage), and the `F` part of stage `k` is the `2^k`-th power of
stage 0's: per stage only squarings, one `smulF` per block and two Horner sums over the levels. -/

/-- The dyadic blocks of `[0, x)` over `n` bits: `(j, x >>> (j+1))` for each set bit `j` of `x`;
all of `[0, 2^n)` (the key `(n, 0)`) once `2^n ≤ x`. -/
def cubesOf (n x : ℕ) : List (ℕ × ℕ) :=
  if 2 ^ n ≤ x then [(n, 0)] else
    (List.range n).flatMap fun j => if x.testBit j then [(j, x >>> (j + 1))] else []

/-- Block `(j, u)`'s fixed bits: bit `j` is `0` and bit `j + 1 + l` is `u`'s bit `l`; none for
`j ≥ n` (the whole cube). -/
def fixB (n j u : ℕ) : List (ℕ × Bool) :=
  if j < n then (j, false) :: (List.range (n - j - 1)).map fun l => (j + 1 + l, u.testBit l) else []

/-- A block key: `none` a block of the `n` bits, `some c` a pattern block (bit 0 is `c`, the block
over bits `1 … n-1`); then the level and the high part. -/
abbrev Key := Option Bool × ℕ × ℕ

/-- A key's fixed bits. -/
def fixK (n : ℕ) : Key → List (ℕ × Bool)
  | (none, j, u) => fixB n j u
  | (some c, j, u) => (0, c) :: (fixB (n - 1) j u).map fun p => (p.1 + 1, p.2)

/-- An item's signed prefix-sum endpoints `(exponent, side, x)`. An even pattern is the run
`[2a, 2b)` minus the odd pattern, so every pattern block is on the odd side. -/
def itemTerms (i : ℕ) : Item → List (ℕ × Option Bool × ℕ)
  | .iv lo hi => [(i, none, hi), (i, none, lo)]
  | .one c => [(i, none, c + 1), (i, none, c)]
  | .pat true a b => [(i, some true, b), (i, some true, a)]
  | .pat false a b => [(i, none, 2 * b), (i, none, 2 * a), (i, some true, b), (i, some true, a)]

/-- An endpoint's blocks. -/
def termKeys (n : ℕ) : ℕ × Option Bool × ℕ → List (ℕ × Key)
  | (i, none, x) => (cubesOf n x).map fun c => (i, none, c.1, c.2)
  | (i, some b, x) => (cubesOf (n - 1) x).map fun c => (i, some b, c.1, c.2)

/-- Every item's blocks, with the kind's exponent. -/
def allKeys (n : ℕ) : List (ℕ × Key) :=
  ((List.range 8).flatMap fun i => (plan n i).flatMap (itemTerms i)).flatMap (termKeys n)

/-- Merge neighbours with equal keys (their exponent lists appended). -/
def mergeAdj {α : Type} [DecidableEq α] : List (α × List ℕ) → List (α × List ℕ)
  | [] => []
  | p :: rest =>
    match mergeAdj rest with
    | [] => [p]
    | q :: rest' => if p.1 = q.1 then (p.1, p.2 ++ q.2) :: rest' else p :: q :: rest'

/-- A block of level `j` on side `none`, as `(u, [exponent])`. -/
def selM (j : ℕ) (p : ℕ × Key) : Option (ℕ × List ℕ) :=
  if p.2.1 = none ∧ p.2.2.1 = j then some (p.2.2.2, [p.1]) else none

/-- A pattern block of level `j`, as `((c, u), [exponent])`. -/
def selP (j : ℕ) (p : ℕ × Key) : Option ((Bool × ℕ) × List ℕ) :=
  match p.2 with
  | (some c, j', u) => if j' = j then some ((c, u), [p.1]) else none
  | _ => none

/-- Level `j`'s blocks on side `none`, merged: `(u, exponents)`. -/
def grpM (n j : ℕ) : List (ℕ × List ℕ) :=
  mergeAdj (((allKeys n).filterMap (selM j)).mergeSort fun a b => decide (a.1 ≤ b.1))

/-- Level `j`'s pattern blocks, merged: `((c, u), exponents)`. -/
def grpP (n j : ℕ) : List ((Bool × ℕ) × List ℕ) :=
  mergeAdj (((allKeys n).filterMap (selP j)).mergeSort
    fun a b => decide (2 * a.1.2 + a.1.1.toNat ≤ 2 * b.1.2 + b.1.1.toNat))

/-- **The node layout's merged blocks** (16 block bits), level by level, as fixed-bit lists with
exponents: a closed constant. -/
def skelM : List (List (List (ℕ × Bool) × List ℕ)) :=
  (List.range 17).map fun j => (grpM 16 j).map fun p => (fixK 16 (none, j, p.1), p.2)

/-- The pattern blocks, level by level (levels `0 … 15` of the 15 bits above bit 0). -/
def skelP : List (List (List (ℕ × Bool) × List ℕ)) :=
  (List.range 16).map fun j => (grpP 16 j).map fun p => (fixK 16 (some p.1.1, j, p.1.2), p.2)

/-- A block's two factors at the claim point's side `fF` (`F`) and `ρ`'s side `gK` (`K`), its
coefficient `Σ_{i ∈ E} β^i` from the powers `bp`. -/
def mkEnt (bp : ℕ → F) (fF : ℕ → Bool → F) (gK : ℕ → Bool → K) (g : List (List (ℕ × Bool) × List ℕ)) :
    List (F × K) :=
  (g.map fun p => ((p.2.map bp).sum * (p.1.map fun b => fF b.1 b.2).prod,
    (p.1.map fun b => gK b.1 b.2).prod)).filter fun p => p.1 != 0

/-- A level's sum `Σ a • G`. -/
def gsum (g : List (F × K)) : K := (g.map fun p => K.smulF p.1 p.2).sum

/-- `Σ_j (Π_{l<j} s (o + l)) y_j`, by Horner. -/
def hornerK (s : ℕ → K) : ℕ → List K → K
  | _, [] => 0
  | o, y :: ys => y + s o * hornerK s (o + 1) ys

/-- The next stage's levels: each `F` factor squared. -/
def sqG (g : List (List (F × K))) : List (List (F × K)) := g.map fun l => l.map fun p => (F.sq p.1, p.2)

section P
variable {R : Type*} [CommRing R]

/-- Block `(j, u)`'s weight: its fixed bits' product times `Π_{l < min j n} (e_l(0) + e_l(1))`. -/
def cubeW (e : ℕ → Bool → R) (n j u : ℕ) : R :=
  ((fixB n j u).map fun p => e p.1 p.2).prod * ∏ l ∈ range (min j n), (e l false + e l true)

theorem cubes_sum {M : Type*} [AddCommMonoid M] (W : ℕ × ℕ → M) {n x : ℕ} (hx : x < 2 ^ n) :
    ((cubesOf n x).map W).sum = ∑ j ∈ range n, if x.testBit j then W (j, x >>> (j + 1)) else 0 := by
  rw [cubesOf, if_neg (by omega), sum_flatMap, ← lsum_range]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  split_ifs <;> simp

theorem fixB_succ {n j : ℕ} (hj : j < n) (u : ℕ) :
    fixB (n + 1) j u = fixB n j u ++ [(n, u.testBit (n - j - 1))] := by
  rw [fixB, fixB, if_pos (by omega), if_pos hj, show n + 1 - j - 1 = (n - j - 1) + 1 by omega,
    List.range_succ, List.map_append, List.cons_append]
  simp only [List.map_cons, List.map_nil]
  rw [show j + 1 + (n - j - 1) = n by omega]

theorem cubeW_congr (e : ℕ → Bool → R) (n j : ℕ) {u u' : ℕ}
    (h : ∀ l < n - j - 1, u.testBit l = u'.testBit l) : cubeW e n j u = cubeW e n j u' := by
  unfold cubeW fixB
  split_ifs
  · congr 2
    simp only [List.map_cons, List.map_map]
    congr 1
    exact List.map_congr_left fun l hl => by
      simp only [Function.comp_apply, h l (List.mem_range.1 hl)]
  · rfl

theorem cubeW_succ (e : ℕ → Bool → R) {n j : ℕ} (hj : j < n) (u : ℕ) :
    cubeW e (n + 1) j u = cubeW e n j u * e n (u.testBit (n - j - 1)) := by
  rw [cubeW, cubeW, fixB_succ hj, List.map_append, List.prod_append,
    show min j (n + 1) = min j n by omega]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- **The prefix sum is the sum over its dyadic blocks.** -/
theorem psum_cubes (e : ℕ → Bool → R) (n x : ℕ) :
    psum e n x = ((cubesOf n x).map fun c => cubeW e n c.1 c.2).sum := by
  by_cases hx : 2 ^ n ≤ x
  · rw [cubesOf, if_pos hx]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, cubeW, fixB,
      lt_irrefl, if_false, List.map_nil, List.prod_nil, one_mul, min_self]
    rw [psum, ← sum_prodE]
    exact sum_congr rfl fun t ht => if_pos (by have := mem_range.1 ht; omega)
  rw [cubes_sum _ (by omega)]
  push_neg at hx
  induction n generalizing x with
  | zero =>
    obtain rfl : x = 0 := by simpa using hx
    simp [psum]
  | succ n ih =>
    rw [psum_succ, sum_range_succ]
    by_cases hn : x < 2 ^ n
    · rw [Nat.testBit_lt_two_pow hn, if_neg (by simp), add_zero,
        show (∑ t ∈ range (2 ^ n), if 2 ^ n + t < x then prodE e n t * e n true else 0) = 0 from
          sum_eq_zero fun t _ => if_neg (by omega), add_zero]
      have h1 : (∑ t ∈ range (2 ^ n), if t < x then prodE e n t * e n false else 0) =
          psum e n x * e n false := by
        rw [psum, sum_mul]; exact sum_congr rfl fun t _ => by split_ifs <;> simp
      rw [h1, ih x hn, sum_mul]
      refine sum_congr rfl fun j hj => ?_
      have hj := mem_range.1 hj
      split_ifs
      · rw [cubeW_succ e hj, Nat.testBit_shiftRight, show j + 1 + (n - j - 1) = n by omega,
          Nat.testBit_lt_two_pow hn]
      · simp
    · push_neg at hn
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ n + y := ⟨x - 2 ^ n, by omega⟩
      have hy : y < 2 ^ n := by rw [pow_succ] at hx; omega
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy, Bool.not_false, if_pos rfl]
      have h1 : (∑ t ∈ range (2 ^ n), if t < 2 ^ n + y then prodE e n t * e n false else 0) =
          (∏ l ∈ range n, (e l false + e l true)) * e n false := by
        rw [← sum_prodE, sum_mul]
        exact sum_congr rfl fun t ht => if_pos (by have := mem_range.1 ht; omega)
      have h2 : (∑ t ∈ range (2 ^ n), if 2 ^ n + t < 2 ^ n + y then prodE e n t * e n true else 0) =
          psum e n y * e n true := by
        rw [psum, sum_mul]
        exact sum_congr rfl fun t _ => by split_ifs <;> first | rfl | (exfalso; omega) | simp
      rw [h1, h2, ih y hy, sum_mul, add_comm]
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        have hj := mem_range.1 hj
        rw [Nat.testBit_two_pow_add_gt hj]
        split_ifs
        · rw [cubeW_succ e hj, Nat.testBit_shiftRight, show j + 1 + (n - j - 1) = n by omega,
            Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy, Bool.not_false]
          congr 1
          refine cubeW_congr e n j fun l hl => ?_
          rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_two_pow_add_gt (by omega)]
        · simp
      · rw [cubeW, fixB, if_pos (by omega), show n + 1 - n - 1 = 0 by omega, min_eq_left (by omega)]
        simp only [List.range_zero, List.map_nil, List.map_cons, List.prod_cons, List.prod_nil,
          mul_one]
        ring

theorem psum_succ_one (e : ℕ → Bool → R) (n c : ℕ) :
    psum e n (c + 1) = psum e n c + if c < 2 ^ n then prodE e n c else 0 := by
  have : psum e n (c + 1) = psum e n c +
      ∑ t ∈ range (2 ^ n), if t = c then prodE e n t else 0 := by
    rw [psum, psum, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by split_ifs <;> first | rfl | (exfalso; omega) | simp
  rw [this, sum_ite_eq' (range (2 ^ n)) c]
  simp only [mem_range]

theorem psum_two_mul (e : ℕ → Bool → R) (m y : ℕ) :
    psum e (m + 1) (2 * y) = (e 0 false + e 0 true) * psum (fun l => e (l + 1)) m y := by
  rw [psum, psum, pow_succ', sum_range_two_mul, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [prodE_even, prodE_odd]
  by_cases h : u < y
  · rw [if_pos (by omega), if_pos (by omega), if_pos h]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg h]; ring

/-- A block key's weight: a block of the `n` bits, or bit 0's weight times a block of bits `1…`. -/
def keyW (e : ℕ → Bool → R) (n : ℕ) : Key → R
  | (none, j, u) => cubeW e n j u
  | (some c, j, u) => e 0 c * cubeW (fun l => e (l + 1)) (n - 1) j u

/-- An endpoint's value: `β^i` times the prefix sum; a pattern endpoint: times bit 0's weight, the
prefix sum over bits `1 … m`. -/
def termV (e : ℕ → Bool → R) (β : R) (m : ℕ) : ℕ × Option Bool × ℕ → R
  | (i, none, x) => β ^ i * psum e (m + 1) x
  | (i, some c, x) => β ^ i * (e 0 c * psum (fun l => e (l + 1)) m x)

/-- **An endpoint's value is the sum over its blocks.** -/
theorem termV_keys (e : ℕ → Bool → R) (β : R) (m : ℕ) (t : ℕ × Option Bool × ℕ) :
    termV e β m t = ((termKeys (m + 1) t).map fun p => β ^ p.1 * keyW e (m + 1) p.2).sum := by
  obtain ⟨i, s, x⟩ := t
  cases s with
  | none =>
    simp only [termV, termKeys, List.map_map, Function.comp_def, keyW, psum_cubes,
      List.sum_map_mul_left]
  | some c =>
    simp only [termV, termKeys, List.map_map, Function.comp_def, keyW, psum_cubes,
      Nat.add_sub_cancel, List.sum_map_mul_left]

end P

section C2
variable {R : Type*} [CommRing R] [CharP R 2]

/-- **An item's fast value is the sum of its endpoints' values** (characteristic two). -/
theorem item_terms (e : ℕ → Bool → R) (β : R) (m i : ℕ) (it : Item) :
    β ^ i * it.val (psum e (m + 1)) (psum (fun l => e (l + 1)) m) (prodE e (m + 1)) (e 0 false)
      (e 0 true) (m + 1) = ((itemTerms i it).map (termV e β m)).sum := by
  have h2 := CharTwo.two_eq_zero (R := R)
  cases it with
  | iv lo hi =>
    simp only [Item.val, itemTerms, termV, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, CharTwo.sub_eq_add, mul_add]
  | one c =>
    simp only [Item.val, itemTerms, termV, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, psum_succ_one]
    linear_combination (-(β ^ i * psum e (m + 1) c)) * h2
  | pat c a b =>
    cases c with
    | true =>
      simp only [Item.val, itemTerms, termV, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, CharTwo.sub_eq_add, if_true]
      ring
    | false =>
      simp only [Item.val, itemTerms, termV, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, CharTwo.sub_eq_add, Bool.false_eq_true, if_false, psum_two_mul]
      linear_combination (-(β ^ i * e 0 true * (psum (fun l => e (l + 1)) m b +
        psum (fun l => e (l + 1)) m a))) * h2

/-- **The kind-weighted block weight is the sum over all items' blocks** (`n = m + 1 ≥ 16`). -/
theorem kwS_keys {m : ℕ} (hn : 16 ≤ m + 1) (β : K) (qf ρf : ℕ → K) :
    kwS (m + 1) β (fun l ↦ qf l) (fun l ↦ ρf l) =
      ((allKeys (m + 1)).map fun p => β ^ p.1 * keyW (ew qf ρf) (m + 1) p.2).sum := by
  rw [← kwS_items, allKeys, sum_flatMap]
  simp only [← termV_keys, sum_flatMap, ← item_terms, ← lsum_range, ← List.sum_map_mul_left]
  refine congrArg List.sum ?_
  refine List.map_congr_left fun i hi => congrArg _ (List.map_congr_left fun it hit => ?_)
  rw [List.sum_map_mul_left, lsum_range, item_val _ m it (plan_wf hn (List.mem_range.1 hi) it hit)]

end C2
section Grp
variable {R : Type*} [CommRing R]

theorem sum_filterMap {α β : Type*} (L : List α) (φ : α → Option β) (F : β → R) :
    ((L.filterMap φ).map F).sum = (L.map fun a => (φ a).elim 0 F).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases φ a <;> simp [ih]

theorem mergeAdj_sum {α : Type} [DecidableEq α] (w : ℕ → R) (V : α → R) :
    ∀ L : List (α × List ℕ), ((mergeAdj L).map fun p => (p.2.map w).sum * V p.1).sum =
      (L.map fun p => (p.2.map w).sum * V p.1).sum
  | [] => rfl
  | p :: rest => by
    have ih := mergeAdj_sum w V rest
    rw [List.map_cons, List.sum_cons, ← ih, mergeAdj]
    split
    · next h => simp [h]
    · next q rest' h =>
      rw [h] at ih ⊢
      split_ifs with hk
      · simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, hk]
        ring
      · rfl

theorem cubesOf_le {n x : ℕ} {c : ℕ × ℕ} (h : c ∈ cubesOf n x) : c.1 ≤ n := by
  unfold cubesOf at h
  split_ifs at h
  · simp at h; simp [h]
  · simp only [List.mem_flatMap, List.mem_range] at h
    obtain ⟨j, hj, hc⟩ := h
    split_ifs at hc <;> simp at hc
    rw [hc]; exact hj.le

theorem allKeys_lvl {m : ℕ} {p : ℕ × Key} (h : p ∈ allKeys (m + 1)) :
    (p.2.1 = none → p.2.2.1 < m + 2) ∧ (p.2.1 ≠ none → p.2.2.1 < m + 1) := by
  simp only [allKeys, List.mem_flatMap] at h
  obtain ⟨⟨i, s, x⟩, -, hp⟩ := h
  cases s with
  | none =>
    simp only [termKeys, List.mem_map] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    have := cubesOf_le hc
    exact ⟨fun _ => by simp; omega, fun h => absurd rfl h⟩
  | some b =>
    simp only [termKeys, List.mem_map] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    have := cubesOf_le hc
    exact ⟨fun h => by simp at h, fun _ => by simp; omega⟩

/-- **The blocks regrouped by level and merged by key.** -/
theorem keys_grp (m : ℕ) (w : ℕ → R) (V : Key → R) :
    ((allKeys (m + 1)).map fun p => w p.1 * V p.2).sum =
      ∑ j ∈ range (m + 2), ((grpM (m + 1) j).map fun p => (p.2.map w).sum * V (none, j, p.1)).sum +
      ∑ j ∈ range (m + 1),
        ((grpP (m + 1) j).map fun p => (p.2.map w).sum * V (some p.1.1, j, p.1.2)).sum := by
  have hM : ∀ j, ((grpM (m + 1) j).map fun p => (p.2.map w).sum * V (none, j, p.1)).sum =
      ((allKeys (m + 1)).map fun p =>
        (selM j p).elim 0 fun q => (q.2.map w).sum * V (none, j, q.1)).sum := fun j => by
    rw [grpM, mergeAdj_sum w (fun u => V (none, j, u)),
      ((List.mergeSort_perm _ _).map _).sum_eq, sum_filterMap]
  have hP : ∀ j, ((grpP (m + 1) j).map fun p => (p.2.map w).sum * V (some p.1.1, j, p.1.2)).sum =
      ((allKeys (m + 1)).map fun p =>
        (selP j p).elim 0 fun q => (q.2.map w).sum * V (some q.1.1, j, q.1.2)).sum := fun j => by
    rw [grpP]
    refine (mergeAdj_sum w (fun cu : Bool × ℕ => V (some cu.1, j, cu.2)) _).trans ?_
    rw [((List.mergeSort_perm _ _).map _).sum_eq, sum_filterMap]
  simp only [hM, hP, sum_lsum, ← List.sum_map_add]
  refine congrArg _ (List.map_congr_left fun p hp => ?_)
  obtain ⟨h1, h2⟩ := allKeys_lvl hp
  obtain ⟨i, s, j0, u⟩ := p
  cases s with
  | none =>
    have := h1 rfl
    have hz : ∀ t, (selP t (i, none, j0, u)).elim (0 : R)
        (fun p => (List.map w p.2).sum * V (some p.1.1, t, p.1.2)) = 0 := fun t => by simp [selP]
    simp only [hz, sum_const_zero, add_zero]
    rw [sum_eq_single j0]
    · simp [selM, selP]
    · intro j _ hj; simp [selM, selP, Ne.symm hj]
    · intro h; exact absurd (mem_range.2 this) h
  | some c =>
    simp only at h2
    have := h2 (by simp)
    have hz : ∀ t, (selM t (i, some c, j0, u)).elim (0 : R)
        (fun q => (List.map w q.2).sum * V (none, t, q.1)) = 0 := fun t => by simp [selM]
    simp only [hz, sum_const_zero, zero_add]
    rw [sum_eq_single j0]
    · simp [selM, selP]
    · intro j _ hj; simp [selM, selP, Ne.symm hj]
    · intro h; exact absurd (mem_range.2 this) h

end Grp

section Stage

/-- The free bits' product of a key (`s_l = e_l(0) + e_l(1)`). -/
def freeP (e : ℕ → Bool → K) (n : ℕ) : Key → K
  | (none, j, _) => ∏ l ∈ range (min j n), (e l false + e l true)
  | (some _, j, _) => ∏ l ∈ range (min j (n - 1)), (e (l + 1) false + e (l + 1) true)

theorem keyW_split (e : ℕ → Bool → K) (n : ℕ) (k : Key) :
    keyW e n k = ((fixK n k).map fun p => e p.1 p.2).prod * freeP e n k := by
  obtain ⟨s, j, u⟩ := k
  cases s with
  | none => rfl
  | some c =>
    simp only [keyW, cubeW, fixK, freeP, List.map_cons, List.prod_cons, List.map_map,
      Function.comp_def]
    ring

theorem prod_fix_ofF (qF : ℕ → F) (ρf : ℕ → K) (L : List (ℕ × Bool)) :
    (L.map fun p => ew (fun l => K.ofF (qF l)) ρf p.1 p.2).prod =
      K.ofF ((L.map fun p => if p.2 then qF p.1 else 1 - qF p.1).prod) *
        (L.map fun p => if p.2 then ρf p.1 else 1 - ρf p.1).prod := by
  induction L with
  | nil => simp; rfl
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    have hm : ∀ a b : F, K.ofF (a * b) = K.ofF a * K.ofF b := map_mul K.ofFRingHom
    rw [hm]
    have h1 : K.ofF (if p.2 then qF p.1 else 1 - qF p.1) =
        if p.2 then K.ofF (qF p.1) else 1 - K.ofF (qF p.1) := by
      split_ifs
      · rfl
      · exact (map_sub K.ofFRingHom 1 (qF p.1)).trans (by rw [map_one]; rfl)
    rw [h1, ew]
    ring

theorem gsum_mkEnt (bp : ℕ → F) (fF : ℕ → Bool → F) (gK : ℕ → Bool → K)
    (g : List (List (ℕ × Bool) × List ℕ)) :
    gsum (mkEnt bp fF gK g) = (g.map fun p => K.ofF ((p.2.map bp).sum) *
      (K.ofF ((p.1.map fun b => fF b.1 b.2).prod) * (p.1.map fun b => gK b.1 b.2).prod)).sum := by
  have hm : ∀ a b : F, K.ofF (a * b) = K.ofF a * K.ofF b := map_mul K.ofFRingHom
  rw [gsum, mkEnt]
  induction g with
  | nil => rfl
  | cons p g ih =>
    simp only [List.map_cons, List.filter_cons, List.sum_cons]
    split_ifs with h
    · rw [List.map_cons, List.sum_cons, ih, K.smulF_eq_mul, hm, mul_assoc]
    · rw [ih]
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
      rw [← mul_assoc, ← hm, h, show K.ofF 0 = 0 from rfl, zero_mul, zero_add]

theorem hornerK_eq (s : ℕ → K) : ∀ (o : ℕ) (Y : List K),
    hornerK s o Y = ∑ j ∈ range Y.length, (∏ l ∈ range j, s (o + l)) * Y.getD j 0
  | _, [] => by simp [hornerK]
  | o, y :: ys => by
    rw [hornerK, hornerK_eq s (o + 1) ys, List.length_cons, sum_range_succ', mul_sum, add_comm]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine sum_congr rfl fun j _ => ?_
      rw [prod_range_succ', List.getD_cons_succ, add_zero,
        prod_congr rfl fun l _ => congrArg s (show o + (l + 1) = o + 1 + l by omega)]
      ring
    · simp

theorem getD_range_map {α : Type*} {n j : ℕ} (g : ℕ → α) (d : α) (hj : j < n) :
    ((List.range n).map g).getD j d = g j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem ofF_lsum (L : List F) : K.ofF L.sum = (L.map K.ofF).sum := map_list_sum K.ofFRingHom L

theorem ofF_pow (a : F) (i : ℕ) : K.ofF (a ^ i) = K.ofF a ^ i := map_pow K.ofFRingHom a i

/-- **One stage, fast** (16 block bits; the claim point's block coordinates in `F`). -/
theorem kwS_fast (β : F) (qF : ℕ → F) (ρf : ℕ → K) (s : ℕ → K)
    (hs : ∀ l < 16, s l = K.ofF (qF l) + (1 + ρf l)) :
    kwS 16 (K.ofF β) (fun l => K.ofF (qF l)) (fun l => ρf l) =
      hornerK s 0 (skelM.map fun g => gsum (mkEnt (β ^ ·) (fun l b => if b then qF l else 1 - qF l)
        (fun l b => if b then ρf l else 1 - ρf l) g)) +
      hornerK s 1 (skelP.map fun g => gsum (mkEnt (β ^ ·) (fun l b => if b then qF l else 1 - qF l)
        (fun l b => if b then ρf l else 1 - ρf l) g)) := by
  set e := ew (fun l => K.ofF (qF l)) ρf
  have h2 := CharTwo.two_eq_zero (R := K)
  have hse : ∀ l < 16, e l false + e l true = s l := fun l hl => by
    rw [hs l hl]
    simp only [e, ew, if_true, Bool.false_eq_true, if_false]
    linear_combination (K.ofF (qF l) * ρf l - K.ofF (qF l) - ρf l) * h2
  refine (kwS_keys (m := 15) (by norm_num) (K.ofF β) (fun l => K.ofF (qF l)) ρf).trans ?_
  rw [keys_grp 15 (K.ofF β ^ ·) (keyW e (15 + 1)), hornerK_eq,
    hornerK_eq, skelM, skelP, List.map_map, List.map_map, List.length_map, List.length_map,
    List.length_range, List.length_range, show (15 : ℕ) + 1 = 16 from rfl]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl fun j hj => ?_
    have hj := mem_range.1 hj
    rw [getD_range_map _ _ hj, Function.comp_apply, gsum_mkEnt, List.map_map,
      ← List.sum_map_mul_left]
    refine congrArg _ (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply]
    rw [keyW_split, ← prod_fix_ofF, ofF_lsum, List.map_map]
    simp only [Function.comp_def, ofF_pow, freeP, min_eq_left (show j ≤ 16 by omega)]
    rw [prod_congr rfl fun l hl => hse l (by have := mem_range.1 hl; omega)]
    simp only [zero_add]
    ring
  · refine sum_congr rfl fun j hj => ?_
    have hj := mem_range.1 hj
    rw [getD_range_map _ _ hj, Function.comp_apply, gsum_mkEnt, List.map_map,
      ← List.sum_map_mul_left]
    refine congrArg _ (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply]
    rw [keyW_split, ← prod_fix_ofF, ofF_lsum, List.map_map]
    simp only [Function.comp_def, ofF_pow, freeP, show 16 - 1 = 15 from rfl,
      min_eq_left (show j ≤ 15 by omega)]
    rw [prod_congr rfl fun l hl => hse (l + 1) (by have := mem_range.1 hl; omega)]
    simp only [show ∀ l, 1 + l = l + 1 from fun l => by omega]
    ring

end Stage


/-! ### Controls of the fast form -/

/-- (+) The blocks of `[0, 11)` over 4 bits: `{10}`, `{8, 9}`, `[0, 8)`; `[0, 16)` is one block. -/
theorem cubesOf_pos : cubesOf 4 11 = [(0, 5), (1, 2), (3, 0)] ∧ cubesOf 4 16 = [(4, 0)] := by
  decide

/-- (−) The key is the part above bit `j` (`x >>> (j+1)`): keyed by `x >>> j`, the blocks differ. -/
theorem cubesOf_neg : cubesOf 4 11 ≠ [(0, 11), (1, 5), (3, 1)] := by decide

/-- (+) The node layout's items give 417 blocks (`skelM`, `skelP` merge them to 58 + 23 keys:
`logs/S-T1`, the probe's `kf` run), and **no pattern block is on the even side** (an even pattern is
a run minus the odd one, `itemTerms`). -/
theorem allKeys_counts : (allKeys 16).length = 417 ∧
    (allKeys 16).all (fun p => p.2.1 != some false) = true := by decide +kernel

/-- (−) … while the plan itself has even patterns (`hashB1`'s path blocks). -/
theorem plan_even : (plan 16 4).any (fun it => it == .pat false (pathH 0) (pathH 0 + 16)) = true := by
  decide +kernel

end KW
end FR

end G6_FRKindWeight

section G6_FRPubTarget

-- New for `flock-recursive` (BLUEPRINT rev. 3.8 §2.3 step 2, A.8 `targetS`; owner S-C).

/-!
# The public target on the skip set (`targetS`)

The zerocheck's Z2 rebuilds `P^{ab}|_S = P^z|_S + P^e|_S` from the public target `E`
(rev. 3.8, skip-c): `P^e(σ) = Σ_{x′} eq(r, x′) E(x′, σ)` for the 64 skip points `σ`
(`targetS`). The verifier computes it per kind and per pinned position: with the layout `x′ =
(hi, blk)` (high position bits low, blocks high) and `E(σ, hi, t) = Σ_κ Ind_κ(t) E_κ(σ, hi)` (the
kinds are public block intervals, a pinned position's value is constant on its kind),
**`targetS_eq`** gives `P^e(σ) = Σ_hi eq(r_hi, hi) Σ_κ E_κ(σ, hi) · Ĩnd_κ(r_blk)`, and
**`intervalMle_eq`** computes each `Ĩnd_κ(r_blk)` as differences of prefix sums over the kind's
intervals (`prefixP`, `O(n²)` each). Per-block affine patterns (`t_lo`) are not covered here.
-/

namespace FR

open Finset

variable {R : Type*} [CommRing R]

/-- `P^e(σ) = Σ_{x′} eq(r, x′) E(σ, x′)`, the public target on the skip point `σ`. -/
def targetS {ℓ : ℕ} (r : Fin ℓ → R) (E : Fin 64 → Fin (2 ^ ℓ) → R) (σ : Fin 64) : R :=
  ∑ u, eq r (cube u) * E σ u

/-- The weight of `eq(r, x)`, bit by bit. -/
def e1 {n : ℕ} (r : Fin n → R) (l : Fin n) (b : Bool) : R := if b then r l else 1 - r l

/-- **An interval indicator's extension** (`Ĩnd_κ`): differences of prefix sums. -/
theorem intervalMle_eq {n : ℕ} (r : Fin n → R) (ivs : List (ℕ × ℕ))
    (h : ∀ p ∈ ivs, p.1 ≤ p.2) :
    mle (selOf ivs) r = (ivs.map fun p ↦ prefixP n (e1 r) p.2 - prefixP n (e1 r) p.1).sum := by
  induction ivs with
  | nil => simp [selOf, mle]
  | cons p ps ih =>
    have hp := h p (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ← ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq),
      prefixP_eq, prefixP_eq, ← Finset.sum_sub_distrib]
    simp only [selOf, List.map_cons, List.sum_cons, mle, mul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hx : eq r (cube x) = ∏ l : Fin n, e1 r l (x.val.testBit l) := by
      rw [eq_cube]; exact Finset.prod_congr rfl fun l _ ↦ by unfold e1; split_ifs <;> rfl
    rw [hx]
    split_ifs <;> first | ring1 | (exfalso; omega)

/-- **`targetS_eq`** (A.8 `targetS`): per kind and position, `P^e(σ) = Σ_hi eq(r_hi, hi)
Σ_κ E_κ(σ, hi) · Ĩnd_κ(r_blk)`. -/
theorem targetS_eq {p q K : ℕ} (rhi : Fin p → R) (rb : Fin q → R) (Ind : Fin K → Fin (2 ^ q) → R)
    (Ek : Fin K → Fin 64 → Fin (2 ^ p) → R) (E : Fin 64 → Fin (2 ^ (p + q)) → R)
    (hE : ∀ σ hi t, E σ (join hi t) = ∑ κ, Ind κ t * Ek κ σ hi) (σ : Fin 64) :
    targetS (Fin.append rhi rb) E σ =
      ∑ hi, eq rhi (cube hi) * ∑ κ, Ek κ σ hi * mle (Ind κ) rb := by
  rw [targetS, ← (joinEquiv p q).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun hi _ ↦ ?_
  simp only [show ∀ t, (joinEquiv p q) (hi, t) = join hi t from fun _ ↦ rfl, eq_append_join, hE,
    mle, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

end FR

end G6_FRPubTarget

section G6_FRVerifierImplOps

-- New for `flock-recursive` (BLUEPRINT §3, A.8, A.9; stage S-F2, track L-cert).
-- Split from `FRVerifierImpl` by S-E3 (mechanical: the op implementations, specifications and
-- `Meets` lemmas that do not depend on the node's M rows, so that `FRVIRTemplates` can use them).

/-!
# The concrete op implementations (`implC`), their specification (`specC`) and `Meets`

BLUEPRINT §3 and A.8: `V` runs the IR with an `OpImpl`. This module gives, per op of `OpImpl`'s
`Array` signature,

* a **specification** `…S`: an adapter from the arrays to the owner's definition over `Fin n → R`
  (S-C: `FRSkip.lagrangeWeight`/`interpolateAt`/`z2Vals`, `FRSpartan.rowW`, `FRShift`'s
  `succT`/`shiftTarget`/the slot weight's extension, `FRRingSwitch.Phi`/`weightEval`; S-D:
  `FRRSEval.tensorTwin`; S-E2: `FRVIREval`'s `walkSpecA/B`, `kindIndSpec`, `evalRowsSpec`);
* a computable **implementation** `…I` on the fast fields `F`, `K`, with the constants an op needs
  (Lagrange denominators, Lagrange weights at fixed nodes, the novel-basis table) as closed
  definitions, computed once per process;
* the equality `…_meets` under the operand lengths `gen` produces (`OpImpl.Meets`' preconditions).

`specC`/`implC` assemble them and **`implC_meets : (implC …).Meets (specC …)`**.

**Interface gaps** (the RESULT's open questions; `FRVIR` is S-0's): `targetS`, `slotW` (slot map 1)
and `linkW` depend on the proof's kind, which `OpImpl`'s fields do not receive, and `shiftTarget`
needs `κ_s` (S1's coordinate 28), which its op does not pass. This module gives the kind-explicit
forms (`targetSLeaf`, `slotWI`, `shiftTargetI κs`) and fills the `OpImpl` fields at a fixed kind;
the fields become exact once `evalOp` passes `κ` (and `κ_s`).
-/

namespace FR
namespace Impl
open Finset RecursionFast RecursionFast.Blake2s

/-! ## Points and `eq` at an index -/

/-- An array read as a point with `n` coordinates (`0` past the end). -/
def ptA (n : ℕ) (r : Array F) : Fin n → F := fun l => r.getD l 0

/-- `eq(r, i)` at the Boolean point of the index `i` (bit `l` of `i` ↔ coordinate `l`). -/
def eqAtR {R : Type*} [CommRing R] {n : ℕ} (r : Fin n → R) (i : ℕ) : R :=
  ∏ l : Fin n, if i.testBit l then r l else 1 - r l

theorem eqTable_getD {R : Type*} [CommRing R] (r : List R) {i : ℕ} (hi : i < 2 ^ r.length) :
    (eqTable r).getD i 0 = eqAtR (ptOf r.length r) i := by
  have := congrFun (tbl_eqTable' r rfl) ⟨i, hi⟩
  simp only [tbl] at this
  rw [this, eq_cube]; rfl

/-! ## Lagrange weights at `ℕ`-indexed nodes -/

/-- The indices `0 … N−1` other than `i`. -/
def othersN (N i : ℕ) : List ℕ := (List.range N).filter (· ≠ i)

/-- `Π_{j < N, j ≠ i} (z − x_j)`. -/
def numL (x : ℕ → F) (N i : ℕ) (z : F) : F := (othersN N i).foldl (fun a j => a * (z - x j)) 1

/-- The inverted Lagrange denominators `(Π_{j ≠ i} (x_i − x_j))⁻¹`, `i < N`. -/
def lagTab (x : ℕ → F) (N : ℕ) : Array F := Array.ofFn (n := N) fun i => (numL x N i (x i))⁻¹

/-- The `N` Lagrange weights at `z`, from the inverted denominators `den`. -/
def lagW (x : ℕ → F) (N : ℕ) (den : Array F) (z : F) : Array F :=
  Array.ofFn (n := N) fun i => numL x N i z * den.getD i 0

/-- The 128 skip nodes `S ∪ Λ` as a table (computed once). -/
def skipTab : Array F := Array.ofFn (n := 128) skipNode

/-- Node `j mod 128` from the table (`xS`). -/
def xT (j : ℕ) : F := skipTab.getD (j % 128) 0

/-- The nodes of `Λ` (`Λ_k = skipNode (64 + k)`). -/
def lamX (k : ℕ) : F := xT (64 + k)

/-- Denominators of `S` (64 nodes), of `Λ` (64), and of `S ∪ Λ₀…₆₂` (127). -/
def denS : Array F := lagTab xT 64
def denL : Array F := lagTab lamX 64
def den127 : Array F := lagTab xT 127

/-- `P^z`'s Lagrange weights on `Λ` at each node of `S` (constants, `64 × 64`). -/
def lamAtS : Array (Array F) := Array.ofFn (n := 64) fun b => lagW lamX 64 denL (xT b)

/-! ## The implementations -/

/-- **`lagrangeS`** (A.8, revision 3.8): `(P^{ab}*(λ), P^z*(λ))`, `vals[0…63]` `P^z` on `Λ`,
`vals[64…126]` `P^{ab}` on `Λ₀…₆₂`, `pe` the 64 values of `P^e` on `S`. -/
def lagrangeSI (v : Array F) (l : F) (pe : Array F) : F × F :=
  let pz := Array.ofFn (n := 64) fun k => v.getD k 0
  let vals := Array.ofFn (n := 127) fun b =>
    if b.val < 64 then dot (lamAtS.getD b #[]) pz + pe.getD b 0 else v.getD b 0
  (dot (lagW xT 127 den127 l) vals, dot (lagW lamX 64 denL l) pz)

/-- **`eqZ`** (A.8, revision 3.9): `L_{i mod 64}(λ) · eq(ρ₁, bit 6 of i)`, `i < 128`. -/
def eqZI (l ρ : F) : Array F :=
  let L := lagW xT 64 denS l
  Array.ofFn (n := 128) fun i => L.getD (i % 64) 0 * if i.val.testBit 6 then ρ else 1 - ρ

/-- **`rowW`** (A.8): `L_{k mod 64}(λ) · eq(r′_hi, ⌊k/64⌋)`, `k < 2^14`. -/
def rowWI (l : F) (rhi : Array F) : Array F :=
  let L := lagW xT 64 denS l
  let E := eqTable (List.ofFn (ptA 8 rhi))
  Array.ofFn (n := 2 ^ (6 + 8)) fun k => L.getD (k % 64) 0 * E.getD (k / 64) 0

/-- **`phiRS`**: `Φ_{r″}(a)` by 127 squarings and the stage products (`FRRingSwitch.phiApply`). -/
def phiRSI (r : Array F) (a : F) : F := phiApply r.toList a

/-- **`shiftEq`**: `shift(τ, r)` in one pass (`FRShift.shiftPair`). -/
def shiftEqI (a b : Array F) : F := (shiftPair a.toList b.toList).2

/-- The novel-basis table `Ŵ_v(D[2^i])`, `v, i < 20` (S-D's `wRow`, computed once). -/
def wTab : Array (Array F) := Array.ofFn (n := logNMax) fun v => (wRow D logNMax v).toArray

/-- `Π_{i<n} f i` by a fold (the product twin of `FRMLE.sumTo`). -/
def prodTo {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) : M :=
  Nat.fold n (fun i _ acc => acc * f i) 1

/-- `Ŵ_v(D[j])` from the table (`wAtD` past the table). -/
def wAtT (v j : ℕ) : F :=
  if v < logNMax then
    sumTo logNMax fun i => if j.testBit i then (wTab.getD v #[]).getD i 0 else 0
  else wAtD v j

/-- **`tensorW`** (A.8): `Π_{v < |r|} (1 − r_v + r_v Ŵ_v(D[j]))`. -/
def tensorWI (j : ℕ) (r : Array K) : K :=
  prodTo r.size fun v => 1 - r.getD v 0 + r.getD v 0 * algebraMap F K (wAtT v j)

/-- `eq(a, b) = Π (1 + a_v + b_v)` (characteristic two). -/
def eqPtsC (a b : List K) : K := (List.zipWith (fun x y => 1 + x + y) a b).prod

/-- `Σ_{k < |c|} c_k eq(r^{2^k}, ρ)`, the point squared once per `k` (`weightEval`'s fold). -/
def wEvalC (c : Array K) (r ρ : List K) : K :=
  (Nat.fold c.size (fun k _ (p : K × List K) =>
    (p.1 + c.getD k 0 * eqPtsC p.2 ρ, p.2.map fun a => a * a)) (0, r)).1

/-- **`wEvalC` at a point in `F`** (S-T1; `wEvalCF_eq`): the point squared in `F` per stage. -/
def wEvalCF (c : Array K) (r : Array F) (ρ : List K) : K :=
  (Nat.fold c.size (fun k _ (p : K × Array F) =>
    (p.1 + c.getD k 0 * eqPtsC (p.2.toList.map K.ofF) ρ, p.2.map F.sq)) (0, r)).1

/-- Claim 2's stage fold (revision 3.16): `Σ_{k<|c|} c_k eq(q_hi, ρ_hi)·kwI(β^(2^k), q_blk, ρ_blk)`,
`q = r^(2^k)` (hi: the first 7 coordinates; blk: the `|ρ| − 7` block coordinates). -/
def wEvalKC (c : Array K) (β : K) (r ρ : List K) : K :=
  let ρh := ρ.take 7
  let ρb := (ρ.drop 7).toArray
  (Nat.fold c.size (fun k _ (p : K × List K × K) =>
    (p.1 + c.getD k 0 * (eqPtsC (p.2.1.take 7) ρh *
        KW.kwI ρb.size p.2.2 (fun l => (p.2.1.drop 7).toArray.getD l 0) (fun l => ρb.getD l 0)),
     p.2.1.map fun a => a * a, p.2.2 * p.2.2)) (0, r, β)).1

/-- One stage of `wEvalKF`: add `c_k eq(q_hi, ρ_hi) T_k` (`T_k` the two Horner sums over the levels,
`s_l = 1 + q_l + ρ_l`), then square the point and the blocks' `F` factors. -/
def kfStep (c : Array K) (ρh : List K) (oρ : Array K) (k : ℕ)
    (st : K × Array F × List (List (F × K)) × List (List (F × K))) :
    K × Array F × List (List (F × K)) × List (List (F × K)) :=
  let q := st.2.1
  let s : ℕ → K := fun l => K.ofF (q.getD (7 + l) 0) + oρ.getD l 0
  (st.1 + c.getD k 0 * (eqPtsC ((q.toList.take 7).map K.ofF) ρh *
      (KW.hornerK s 0 (st.2.2.1.map KW.gsum) + KW.hornerK s 1 (st.2.2.2.map KW.gsum))),
    q.map F.sq, KW.sqG st.2.2.1, KW.sqG st.2.2.2)

/-- **Claim 2's stage fold, fast** (S-T1; `wEvalKF_eq`): the claim point `r` in `F` (23
coordinates), `ρ` of 23. The blocks' factors (`KW.mkEnt`: the point's side in `F`, `ρ`'s in `K`) are
made once; per stage the `F` factors are squared (`KW.sqG`), one `smulF` per block. -/
def wEvalKF (c : Array K) (β : F) (r : Array F) (ρ : List K) : K :=
  let ρb := (ρ.drop 7).toArray
  let gK : ℕ → Bool → K := fun l b => if b then ρb.getD l 0 else 1 - ρb.getD l 0
  let fF : ℕ → Bool → F := fun l b => if b then r.getD (7 + l) 0 else 1 - r.getD (7 + l) 0
  (Nat.fold c.size (fun k _ => kfStep c (ρ.take 7) (ρb.map (1 + ·)) k)
    (0, r, KW.skelM.map (KW.mkEnt (β ^ ·) fF gK), KW.skelP.map (KW.mkEnt (β ^ ·) fF gK))).1

/-- **`rsWeight`, fast** (S-T1; `rsWeightF_eq`): a claim point in `F` (every coordinate's `f₁` is
`0`) runs `wEvalKF` (claim 2, at 23 coordinates and `|ρ| = 23`) or `wEvalCF`; otherwise as
`rsWeightI`. -/
def rsWeightF (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  let c := (phiTable r.toList).map K.ofF
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 *
    (if p.1.all (·.f₁ == 0) then
      (if p.2 = 1 then
        (if p.1.size = 23 ∧ ρ.size = 23 then wEvalKF c β (p.1.map (·.f₀)) ρ.toList
         else wEvalKC c (K.ofF β) p.1.toList ρ.toList)
       else wEvalCF c (p.1.map (·.f₀)) ρ.toList)
     else
      (if p.2 = 1 then wEvalKC c (K.ofF β) p.1.toList ρ.toList else wEvalC c p.1.toList ρ.toList))).sum

/-- **`rsWeight`** (A.8, revisions 3.9, 3.16): `Σ_j κ^j Ŵ_j(ρ)`, `Ŵ_j = Σ_{k<128} c_k(r″)
eq(r_j^{2^k}, ρ)` except claim 2 (index 1), weighted by the kind factor (`wEvalKC`); the
coefficients `c_k(r″)` (`FRRingSwitch.phiTable`) computed once over F. -/
def rsWeightI (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  let c := (phiTable r.toList).map K.ofF
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 *
    (if p.2 = 1 then wEvalKC c (K.ofF β) p.1.toList ρ.toList
     else wEvalC c p.1.toList ρ.toList)).sum

/-- The slot maps' bases (A.6, P2 §7.5 (4)): `0` the `h_out` slot `256 + σ`, `1` the chain
block's `d` slot `520 + σ` (a leaf's `In`), `2` the `h_in` slot `σ`. -/
def slotBase : ℕ → ℕ
  | 0 => 256 | 1 => 520 | _ => 0

/-- **`slotW`** (A.8, `slotW_mle`): `Σ_{σ<256} eq(θ, σ) eq(r, base + σ)` over 10 coordinates. -/
def slotWI (s : ℕ) (θ r : Array F) : F :=
  let Eθ := eqTable (List.ofFn (ptA 10 θ)); let Er := eqTable (List.ofFn (ptA 10 r))
  sumTo 256 fun σ => Eθ.getD σ 0 * Er.getD (slotBase s + σ) 0

/-- Bit `σ < 256` of a digest given as its two F halves (A.7's pack: bytes LE, bits LE). -/
def digBit (e₀ e₁ : F) (σ : ℕ) : Bool :=
  if h : σ < 128 then bitF e₀ ⟨σ, h⟩ else bitF e₁ ⟨(σ - 128) % 128, Nat.mod_lt _ (by decide)⟩

/-- `Σ_{σ<256} eq(θ, σ) · bit_σ(d)` from the table `Eθ = eq(θ, ·)`. -/
def digestMle (Eθ : Array F) (e₀ e₁ : F) : F :=
  sumTo 256 fun σ => if digBit e₀ e₁ σ then Eθ.getD σ 0 else 0

/-- The last block of `shiftTarget`'s `bnd` as an 18-coordinate point (entries `4 … 21`; revision
3.15: `1^(m−14) ‖ 0^(32−m)`, `finSh`'s `bndOps`). -/
def lastOf (bnd : Array F) : Fin 18 → F := fun l => bnd.getD (4 + l.val) 0

/-- **`shiftTarget`** with `κ_s` (A.9 `finSh` (i); the leaf's native reading, P2 §7.5 (4);
revision 3.15: on 18 coordinates): `eq(τ, last) · h̃(θ) + κ_s · s̃(θ)`, `bnd = [s_lo, s_hi, h_lo,
h_hi] ‖ last`. -/
def shiftTargetI (κs : F) (τ θ bnd : Array F) : F :=
  let Eθ := eqTable (List.ofFn (ptA 10 θ))
  prodTo 18 (fun l => τ.getD l 0 * bnd.getD (4 + l) 0 + (1 - τ.getD l 0) * (1 - bnd.getD (4 + l) 0)) *
      digestMle Eθ (bnd.getD 2 0) (bnd.getD 3 0) +
    κs * digestMle Eθ (bnd.getD 0 0) (bnd.getD 1 0)

/-- The chain block's public target `E_chain` as 0/1 (A.6, `Chain.chainTarget`; `none` reads `0`). -/
def chainE (p : ℕ) : F := if Chain.chainTarget (ProductCircuit.pos p) = some true then 1 else 0

/-- `E_chain` on the `2^14` positions (computed once). -/
def chainTab : Array F := Array.ofFn (n := 2 ^ 14) fun p => chainE p

/-- The 8 position coordinates of the Z point (A.2): the pinned `ρ₁ … ρ₇`, then Z1's first. -/
def zLo (r : Array F) : Fin 8 → F := fun l => if h : l.val < 7 then pinnedRho ⟨l, h⟩ else r.getD 0 0

/-- **`targetS` of a leaf kind** (A.8; every block a `chain` block): `P^e(σ) = Σ_hi eq(r_lo, hi)
E_chain(σ + 64 hi)`, `r_lo = zLo r`. -/
def targetSLeafI (r : Array F) : Array F :=
  let H := eqTable (List.ofFn (zLo r))
  Array.ofFn (n := 64) fun σ => sumTo 256 fun hi => chainTab.getD (σ + 64 * hi) 0 * H.getD hi 0

/-! ## Specifications (adapters to the owners' definitions) -/

/-- **`lagrangeS`'s specification** (`FRSkip.z2Vals`, `interpolateAt`): `P^{ab}*(λ)` through
`S ∪ Λ₀…₆₂` from `z2Vals`, and `P^z*(λ)` through `Λ`. -/
def lagrangeSS (v : Array F) (l : F) (pe : Array F) : F × F :=
  (interpolateAt node127 (z2Vals (fun k => v.getD k 0) (fun k => v.getD (64 + k.val) 0)
    (fun σ => pe.getD σ 0)) l, interpolateAt lNode (fun k => v.getD k 0) l)

/-- **`eqZ`'s specification**: `lagrangeWeight` on `S` at `λ` for the low 6 bits, `eq(ρ₁, ·)` on
bit 6. -/
def eqZS (l ρ : F) : Array F :=
  Array.ofFn (n := 128) fun i => lagrangeWeight sNodeF l ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩ *
    if i.val.testBit 6 then ρ else 1 - ρ

/-- **`rowW`'s specification** (`FRSpartan.rowW` with 8 high position bits). -/
def rowWS (l : F) (rhi : Array F) : Array F :=
  Array.ofFn (n := 2 ^ (6 + 8)) fun k => rowW l (ptA 8 rhi) k

/-- **`phiRS`'s specification** (`FRRingSwitch.Phi`). -/
def phiRSS (r : Array F) (a : F) : F := Phi r.toList a

/-- **`shiftEq`'s specification**: `Σ_{u,v} eq(τ, u) [v = u + 1] eq(v, r)` (`FRShift.succT`). -/
def shiftEqS (a b : Array F) : F :=
  ∑ u : Fin (2 ^ a.size), ∑ v : Fin (2 ^ a.size),
    eq (ptOf a.size a.toList) (cube u) * succT u v * eq (cube v) (ptOf a.size b.toList)

/-- **`tensorW`'s specification** (`FRRSEval.tensorTwin` on `D`, S-D's verifier tensor weight). -/
def tensorWS (j : ℕ) (r : Array K) : K := tensorTwin D logNMax r.size (fun v => r.getD v 0) j

/-- Claim 2's weight at one Frobenius stage (`KW.kwS`, revision 3.16): `eq(q_hi, ρ_hi)` on the 7 high
position coordinates times the kind-weighted block weight on the `|ρ| − 7` block coordinates. -/
def kwSL (β : K) (q ρ : List K) : K :=
  eqPts (q.take 7) (ρ.take 7) *
    KW.kwS (ρ.length - 7) β (ptOf (ρ.length - 7) (q.drop 7)) (ptOf (ρ.length - 7) (ρ.drop 7))

/-- **`rsWeight`'s specification** (A.8, L-R4 `weight_mle`'s right side; revision 3.16):
`Σ_j κ^j Σ_{k<128} c_k(r″) w_{j,k}` with `w_{j,k} = eq(r_j^{2^k}, ρ)`, except claim 2 (index 1):
`w_{1,k} = kwSL(β^(2^k), r_1^{2^k}, ρ)` (`FRRingSwitch.rsWeight_kind_eq` is its Φ form);
`c_k(r″)` the coefficients of `Φ_{r″}` (`FRRingSwitch.phiTable`). -/
def rsWeightS (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 * ∑ k ∈ range 128,
    K.ofF ((phiTable r.toList).getD k 0) *
      (if p.2 = 1 then kwSL (sqIter k (K.ofF β)) (p.1.toList.map (sqIter k)) ρ.toList
       else eqPts (p.1.toList.map (sqIter k)) ρ.toList)).sum

/-- A digest's bits as a table over the 10-bit slot index (`0` from `σ = 256` on). -/
def digTbl (e₀ e₁ : F) : Fin (2 ^ 10) → F := fun u => if u.val < 256 ∧ digBit e₀ e₁ u then 1 else 0

/-- **`shiftTarget`'s specification** with `κ_s` (`FRShift.shiftTargetAt`, revision 3.15: on 18
coordinates): `eq(τ, last) h̃V(θ) + κ_s s̃V(θ)`, `sV`, `hV` the boundary digests `bnd[0,1]`,
`bnd[2,3]` as bit tables, `last = bnd[4 … 21]` (`shiftTargetS_pad`: at a zero-padded `τ` and the
kind's padded last block, `FRShift.shiftTarget` on `m − 14` coordinates). -/
def shiftTargetS (κs : F) (τ θ bnd : Array F) : F :=
  shiftTargetAt (ptA 10 θ) (ptA 18 τ) (lastOf bnd) κs (digTbl (bnd.getD 0 0) (bnd.getD 1 0))
    (digTbl (bnd.getD 2 0) (bnd.getD 3 0))

/-- **The leaf kinds' `targetS` specification** (`FRPubTarget.targetS` over the `8 + b` variables
of the quirky polynomial, `b = m − 14` block bits, with the leaf's `E(σ, (hi, t)) = E_chain(σ +
64 hi)` for every block `t`). -/
def targetSLeafS (b : ℕ) (r : Array F) : Array F :=
  Array.ofFn (n := 64) fun σ => FR.targetS (ℓ := 8 + b) (Fin.append (zLo r) fun l => r.getD (1 + l) 0)
    (fun σ u => chainE (σ + 64 * (u.val % 256))) σ

/-- **`slotW`'s specification** (`FRShift.slotW_mle`'s right side for the map `σ ↦ base + σ`,
`σ < 256`): `Σ_{σ<256} eq(θ, σ) eq(r, base + σ)`. -/
def slotWS (s : ℕ) (θ r : Array F) : F :=
  ∑ σ ∈ range 256, eqAtR (ptA 10 θ) σ * eqAtR (ptA 10 r) (slotBase s + σ)

/-! ## `Meets`, per op -/

section Lagrange

theorem prod_othersN (g : ℕ → F) {N i : ℕ} (hi : i < N) :
    ((othersN N i).map g).prod = ∏ j ∈ (univ : Finset (Fin N)).erase ⟨i, hi⟩, g j := by
  rw [othersN, ← List.prod_toFinset _ (List.nodup_range.filter _)]
  have : ((List.range N).filter (· ≠ i)).toFinset = ((univ : Finset (Fin N)).erase ⟨i, hi⟩).map Fin.valEmbedding := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, ne_eq,
      decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Finset.mem_map,
      Finset.mem_erase, Finset.mem_univ, and_true, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨hj, hne⟩; exact ⟨⟨j, hj⟩, fun h => hne (congrArg Fin.val h), rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, fun h => ha (Fin.ext h)⟩
  rw [this, Finset.prod_map]; rfl

theorem lagW_getD (x : ℕ → F) (N : ℕ) (den : Array F) (z : F) {i : ℕ} (hi : i < N) :
    (lagW x N den z).getD i 0 = numL x N i z * den.getD i 0 := by
  simp [lagW, Array.getD_eq_getD_getElem?, hi]

theorem lagTab_getD (x : ℕ → F) {N i : ℕ} (hi : i < N) :
    (lagTab x N).getD i 0 = (numL x N i (x i))⁻¹ := by
  simp [lagTab, Array.getD_eq_getD_getElem?, hi]

/-- The computed weight is `FRSkip.lagrangeWeight` at the nodes `x_0 … x_{N−1}`. -/
theorem lagW_eq (x : ℕ → F) (N : ℕ) (z : F) {i : ℕ} (hi : i < N) :
    (lagW x N (lagTab x N) z).getD i 0 = lagrangeWeight (fun b : Fin N => x b) z ⟨i, hi⟩ := by
  rw [lagW_getD _ _ _ _ hi, lagTab_getD _ hi, numL, numL, foldl_mul_eq, foldl_mul_eq, one_mul,
    one_mul, prod_othersN _ hi, prod_othersN _ hi, lagrangeWeight]

/-- A dot product with the weights is the interpolant's sum. -/
theorem dot_lagW (x : ℕ → F) (N : ℕ) (z : F) (w : Array F) :
    dot (lagW x N (lagTab x N) z) w =
      ∑ i : Fin N, lagrangeWeight (fun b : Fin N => x b) z i * w.getD i 0 := by
  rw [dot, sumTo_eq, show (lagW x N (lagTab x N) z).size = N from Array.size_ofFn,
    Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [lagW_eq _ _ _ i.isLt]

theorem xT_eq (j : ℕ) : xT j = xS j := by
  simp [xT, xS, skipTab, Array.getD_eq_getD_getElem?, Nat.mod_lt]

theorem xS_node127 : (fun b : Fin 127 => xT b) = node127 := by
  funext b; simp only [xT_eq, xS, node127]; congr 1; ext; simp; omega

theorem xS_sNode : (fun b : Fin 64 => xT b) = sNodeF := by
  funext b; rw [xT_eq]; exact xS_of_lt b.isLt

theorem lamX_lNode : (fun b : Fin 64 => lamX b) = lNode := by
  funext b; simp only [lamX, xT_eq, xS, lNode]; congr 1; ext; simp; omega

private theorem hzL (v : Array F) (z : F) : dot (lagW lamX 64 denL z) (Array.ofFn (n := 64) fun k => v.getD k 0) =
      interpolateAt lNode (fun k => v.getD k 0) z := by
  rewrite [denL, dot_lagW, lamX_lNode, interpolateAt]
  exact Finset.sum_congr rfl fun k _ => by simp [Array.getD_eq_getD_getElem?]

/-- **`lagrangeS` meets its specification.** -/
theorem lagrangeS_meets (v : Array F) (l : F) (pe : Array F) :
    lagrangeSI v l pe = lagrangeSS v l pe := by
  unfold lagrangeSI lagrangeSS
  dsimp only
  rewrite [den127, dot_lagW, xS_node127, hzL, interpolateAt]
  refine Prod.ext ?_ rfl
  dsimp only
  refine Finset.sum_congr rfl fun b _ => congrArg _ ?_
  rewrite [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [b.isLt, dite_true, Option.getD_some, z2Vals]
  split_ifs with h
  · have hl : lamAtS[b.val]? = some (lagW lamX 64 denL (xT b)) := by
      rewrite [lamAtS, Array.getElem?_ofFn]
      simp only [show b.val < 64 from h, dite_true]
    rewrite [Array.getD_eq_getD_getElem? (xs := lamAtS), hl, Option.getD_some, hzL]
    refine congrArg (· + _) (congrArg _ ?_)
    simp only [xT_eq, xS, Nat.mod_eq_of_lt (show b.val < 128 by omega)]
    rfl
  · show v.getD b 0 = v.getD (64 + (b.val - 64)) 0
    rewrite [Nat.add_sub_cancel' (by omega)]; rfl
end Lagrange

section Tables

theorem eqTable_ofFn_getD {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → R) {i : ℕ}
    (hi : i < 2 ^ n) : (eqTable (List.ofFn f)).getD i 0 = eqAtR f i := by
  have h1 := congrFun (tbl_eqTable' (List.ofFn f) List.length_ofFn) ⟨i, hi⟩
  have h2 : ptOf n (List.ofFn f) = f := funext fun l => by
    simp [ptOf, List.getD_eq_getElem?_getD]
  simp only [tbl] at h1
  rw [h1, h2, eq_cube]; rfl

theorem prodTo_eq {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    prodTo n f = ∏ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prodTo, Nat.fold_succ, ← prodTo, ih, Finset.prod_range_succ]

/-- **`eqZ` meets its specification.** -/
theorem eqZ_meets (l ρ : F) : eqZI l ρ = eqZS l ρ := by
  unfold eqZI eqZS
  refine congrArg (Array.ofFn (n := 128)) (funext fun i => ?_)
  rewrite [denS, lagW_eq _ _ _ (Nat.mod_lt _ (by decide)), xS_sNode]
  rfl

/-- **`rowW` meets its specification.** -/
theorem rowW_meets (l : F) (rhi : Array F) : rowWI l rhi = rowWS l rhi := by
  unfold rowWI rowWS
  refine congrArg (Array.ofFn (n := 2 ^ (6 + 8))) (funext fun k => ?_)
  have hk : k.val / 64 < 2 ^ 8 := by have := k.isLt; omega
  rewrite [denS, lagW_eq _ _ _ (Nat.mod_lt _ (by decide)), xS_sNode, eqTable_ofFn_getD _ hk]
  simp only [rowW, joinEquiv, Equiv.coe_fn_symm_mk, eq_cube, eqAtR]
  rfl

/-- `n` squarings in `F` by `F.sq` (≈ 20 ns, against ≈ 100 ns for `a * a`). -/
def sqItF : ℕ → F → F
  | 0, a => a
  | n + 1, a => sqItF n (F.sq a)

theorem sqItF_eq : ∀ (n : ℕ) (a : F), sqItF n a = sqIter n a
  | 0, _ => rfl
  | n + 1, a => by rw [sqItF, sqItF_eq n, F.sq_eq_mul]; rfl

/-- `FRRingSwitch.frobMapC` with `F.sq`. -/
def frobMapF : List (ℕ × F) → F → F
  | [], a => a
  | (s, f) :: st, a => frobMapF st (a + f * sqItF s a)

theorem frobMapF_eq : ∀ (st : List (ℕ × F)) (a : F), frobMapF st a = frobMapC st a
  | [], _ => rfl
  | (s, f) :: st, a => by rw [frobMapF, frobMapC, sqItF_eq, frobMapF_eq st]

/-- **`phiRS`, fast** (S-T1; `phiRSF_eq`): `phiRSI` with its 127 squarings by `F.sq`. -/
def phiRSF (r : Array F) (a : F) : F := frobMapF (stages (r.toList.length - 1) r.toList) a

theorem phiRSF_eq (r : Array F) (a : F) : phiRSF r a = phiRSI r a := frobMapF_eq _ _

/-- (+) One squaring stage: `sqItF 1 a = a * a`. (−) `sqItF` is not the identity: `sqItF 1 u ≠ u`
for `F`'s `u = ⟨0, 1⟩` (`u^2 = u + β`). -/
theorem sqItF_ctrl : sqItF 1 (⟨0, 1⟩ : F) = ⟨0, 1⟩ * ⟨0, 1⟩ ∧ sqItF 1 (⟨0, 1⟩ : F) ≠ ⟨0, 1⟩ := by
  decide +kernel

/-- **`phiRS` meets its specification** (`FRRingSwitch.phiApply_eq`). -/
theorem phiRS_meets (r : Array F) (a : F) : phiRSI r a = phiRSS r a := phiApply_eq _ _

/-- **`shiftEq` meets its specification** on points of equal length (`FRShift.shiftEq_eq`). -/
theorem shiftEq_meets (a b : Array F) (h : a.size = b.size) : shiftEqI a b = shiftEqS a b :=
  shiftEq_eq a.size a.toList b.toList (by simp) (by simp [h])

/-- **`tensorW` meets its specification.** -/
theorem tensorW_meets (j : ℕ) (r : Array K) : tensorWI j r = tensorWS j r := by
  unfold tensorWI tensorWS tensorTwin
  rewrite [prodTo_eq]
  refine Finset.prod_congr rfl fun v _ => ?_
  congr 3
  unfold wAtT
  split_ifs with hv
  · rw [sumTo_eq, wAt]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [wTab, Array.getD_eq_getD_getElem?, hv, List.getD_eq_getElem?_getD]
  · rfl

/-! ### `tensorW`'s fast twin (S-E8) -/

/-- `Ŵ_v(D[x ⋅ 2^{8b}])` for a byte `x`, `v < 20`, `b < 3`: entry `x` of table `3v + b`. -/
def wByte : Array (Array F) := Array.ofFn (n := 3 * logNMax) fun vb =>
  Array.ofFn (n := 256) fun x => sumTo 8 fun i =>
    if x.val.testBit i && 8 * (vb.val % 3) + i < logNMax then
      (wTab.getD (vb.val / 3) #[]).getD (8 * (vb.val % 3) + i) 0 else 0

/-- Byte `b` of `j`'s contribution to `Ŵ_v(D[j])`, by table (`wAtF`'s terms, as the proof reads them). -/
def wB (v b j : ℕ) : F := (wByte.getD (3 * v + b) #[]).getD (j / 2 ^ (8 * b) % 2 ^ 8) 0

/-- **`wAtT` by three byte tables** (S-E8): three lookups instead of a 20-term sum (`wAtF_eq`); it is
`wB v 0 j + wB v 1 j + wB v 2 j` with the powers as literals (`2 ^ k` runs as a loop here). -/
def wAtF (v j : ℕ) : F :=
  if v < logNMax then
    (wByte.getD (3 * v) #[]).getD (j % 256) 0 + (wByte.getD (3 * v + 1) #[]).getD (j / 256 % 256) 0 +
      (wByte.getD (3 * v + 2) #[]).getD (j / 65536 % 256) 0
  else wAtD v j

theorem wB_eq (v b j : ℕ) (hv : v < logNMax) (hb : b < 3) :
    wB v b j =
      ∑ i ∈ range 8, if j.testBit (8 * b + i) && 8 * b + i < logNMax then
        (wTab.getD v #[]).getD (8 * b + i) 0 else 0 := by
  have h1 : 3 * v + b < 3 * logNMax := by omega
  have h2 : j / 2 ^ (8 * b) % 2 ^ 8 < 256 := Nat.mod_lt _ (by norm_num)
  have e1 : (3 * v + b) % 3 = b := by omega
  have e2 : (3 * v + b) / 3 = v := by omega
  simp only [wB, wByte, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h1, h2, dite_true,
    Option.getD_some, e1, e2, sumTo_eq]
  refine sum_congr rfl fun i hi => ?_
  have hi8 : i < 8 := mem_range.1 hi
  have ht : (j / 2 ^ (8 * b) % 2 ^ 8).testBit i = j.testBit (8 * b + i) := by
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp [hi8, add_comm]
  rw [ht]

theorem wAtF_eq (v j : ℕ) : wAtF v j = wAtT v j := by
  unfold wAtF wAtT
  split_ifs with hv
  · rw [show j % 256 = j / 2 ^ (8 * 0) % 2 ^ 8 by norm_num, show j / 256 % 256 = j / 2 ^ (8 * 1) % 2 ^ 8 by
      norm_num, show j / 65536 % 256 = j / 2 ^ (8 * 2) % 2 ^ 8 by norm_num]
    change wB v 0 j + wB v 1 j + wB v 2 j = _
    rw [wB_eq v 0 j hv (by norm_num), wB_eq v 1 j hv (by norm_num), wB_eq v 2 j hv (by norm_num),
      sumTo_eq]
    set g : ℕ → F := fun i => if j.testBit i && i < logNMax then (wTab.getD v #[]).getD i 0 else 0
    have hz : ∑ x ∈ range 4, g (20 + x) = 0 := sum_eq_zero fun x _ => by simp [g, logNMax]
    have h20 : ∑ i ∈ range 20, g i = ∑ i ∈ range logNMax, if j.testBit i then (wTab.getD v #[]).getD i 0 else 0 :=
      sum_congr rfl fun i hi => by simp [g, mem_range.1 hi, logNMax]
    have hs : ∑ i ∈ range 20, g i = ∑ x ∈ range 8, g x + ∑ x ∈ range 8, g (8 + x) + ∑ x ∈ range 8, g (16 + x) := by
      rw [← add_zero (∑ i ∈ range 20, g i), ← hz, ← sum_range_add, show 20 + 4 = (8 + 8) + 8 from rfl,
        sum_range_add g (8 + 8) 8, sum_range_add g 8 8]
    rw [← h20, hs]
    rfl
  · rfl
/-- **`tensorW`'s fast twin** (S-E8): `wAtF`, and `r_v · Ŵ` as `smulF` (two `F` products instead
of a `K` product); `tensorWF_eq`. -/
def tensorWF (j : ℕ) (r : Array K) : K :=
  prodTo r.size fun v => 1 - r.getD v 0 + K.smulF (wAtF v j) (r.getD v 0)

theorem tensorWF_eq (j : ℕ) (r : Array K) : tensorWF j r = tensorWI j r :=
  congrArg (prodTo r.size) (funext fun v => by
    rw [wAtF_eq, K.smulF_eq_mul, ← K.algebraMap_eq_ofF, mul_comm])
/-- **`tensorW` at a point in `F`** (S-T1; `tensorWG_eq`): every factor in `F` (two F products
instead of a K product and a `smulF`); otherwise `tensorWF`. -/
def tensorWG (j : ℕ) (r : Array K) : K :=
  if r.all (·.f₁ == 0) then
    K.ofF (prodTo r.size fun v => 1 - (r.getD v 0).f₀ + wAtF v j * (r.getD v 0).f₀)
  else tensorWF j r

theorem prodTo_ofF (n : ℕ) (f : ℕ → F) : K.ofF (prodTo n f) = prodTo n fun v => K.ofF (f v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show K.ofF (prodTo n f * f n) = prodTo n (fun v => K.ofF (f v)) * K.ofF (f n)
    rw [← ih]; exact map_mul K.ofFRingHom _ _

theorem K_ofF_f0 : ∀ x : K, x.f₁ = 0 → x = K.ofF x.f₀
  | ⟨_, _⟩, h => by subst h; rfl

theorem getD_inF {r : Array K} (h : r.all (·.f₁ == 0) = true) (v : ℕ) :
    r.getD v 0 = K.ofF (r.getD v 0).f₀ := by
  rw [Array.all_eq_true] at h
  rw [Array.getD_eq_getD_getElem?]
  by_cases hv : v < r.size
  · rw [Array.getElem?_eq_getElem hv, Option.getD_some]
    have h1 : (r[v]).f₁ = 0 := by simpa using h v hv
    exact K_ofF_f0 _ h1
  · rw [Array.getElem?_eq_none (by omega)]; rfl

theorem tensorWG_eq (j : ℕ) (r : Array K) : tensorWG j r = tensorWF j r := by
  unfold tensorWG
  split_ifs with h
  · rw [prodTo_ofF, tensorWF]
    refine congrArg (prodTo r.size) (funext fun v => ?_)
    set x := (r.getD v 0).f₀
    rw [getD_inF h v, K.smulF_eq_mul]
    change K.ofFRingHom (1 - x + wAtF v j * x) = _
    simp only [map_add, map_sub, map_mul, map_one]
    rfl
  · rfl

/-- (+) The F path's reading of a point in `F` is exact (`K_ofF_f0`): `ofF 3` is `ofF 3`'s `f₀`. -/
theorem inF_pos : (#[K.ofF 3]).all (·.f₁ == 0) = true ∧ K.ofF 3 = K.ofF (K.ofF 3).f₀ := by
  decide +kernel

/-- (−) Outside `F` the projection to `f₀` loses `u`, so the guard of `tensorWG` and `rsWeightF` is
load-bearing: `u ≠ ofF u.f₀`, and the guard rejects it. -/
theorem inF_neg : K.u ≠ K.ofF K.u.f₀ ∧ (#[K.u]).all (·.f₁ == 0) = false := by decide +kernel

/-! #### Controls (S-E8) -/

/-- (+) `tensorW` at `j = 0`: `Π (1 + r_v)`; the twin agrees (`tensorWF_eq`). -/
theorem tensorW_pos : tensorWI 0 #[K.u] = 1 + K.u := by decide +kernel

theorem tensorWF_pos : tensorWF 0 #[K.u] = 1 + K.u := (tensorWF_eq 0 _).trans tensorW_pos

/-- (−) The third byte table is needed: its entry for `j = 2^16` is `Ŵ_0(D[2^16]) ≠ 0`, so a twin
reading only bits `0 … 15` is wrong at `j = 2^16`. -/
theorem wByte_neg : (wByte.getD 2 #[]).getD 1 0 ≠ 0 := by decide +kernel

/-- **`slotW` meets its specification.** -/
theorem slotW_meets (s : ℕ) (θ r : Array F) : slotWI s θ r = slotWS s θ r := by
  unfold slotWI slotWS
  rewrite [sumTo_eq]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h1 : σ < 2 ^ 10 := by simp at hσ; omega
  have h2 : slotBase s + σ < 2 ^ 10 := by
    simp at hσ; unfold slotBase; split <;> omega
  rw [eqTable_ofFn_getD _ h1, eqTable_ofFn_getD _ h2]

theorem eqPtsC_eq : ∀ (a b : List K), eqPtsC a b = eqPts a b
  | [], _ => by simp [eqPtsC, eqPts]
  | _ :: _, [] => by simp [eqPtsC, eqPts]
  | x :: a, y :: b => by
    have h := eqPtsC_eq a b
    simp only [eqPtsC, eqPts, List.zipWith_cons_cons, List.prod_cons] at h ⊢
    rw [h]; congr 1
    linear_combination (x + y - x * y) * CharTwo.two_eq_zero (R := K)

theorem wEvalC_eq (c : Array K) (r ρ : List K) :
    wEvalC c r ρ = ∑ k ∈ range c.size, c.getD k 0 * eqPts (r.map (sqIter k)) ρ := by
  unfold wEvalC
  simp only [eqPtsC_eq]
  rw [weightEval_fold]

theorem wEvalKC_fold (c : Array K) (β : K) (r ρ : List K) (n : ℕ) :
    Nat.fold n (fun k _ (p : K × List K × K) =>
      (p.1 + c.getD k 0 * (eqPtsC (p.2.1.take 7) (ρ.take 7) *
          KW.kwI (ρ.drop 7).toArray.size p.2.2 (fun l => (p.2.1.drop 7).toArray.getD l 0)
            (fun l => (ρ.drop 7).toArray.getD l 0)),
       p.2.1.map fun a => a * a, p.2.2 * p.2.2)) (0, r, β) =
    (∑ k ∈ range n, c.getD k 0 * (eqPtsC ((r.map (sqIter k)).take 7) (ρ.take 7) *
        KW.kwI (ρ.drop 7).toArray.size (sqIter k β)
          (fun l => ((r.map (sqIter k)).drop 7).toArray.getD l 0)
          (fun l => (ρ.drop 7).toArray.getD l 0)),
      r.map (sqIter n), sqIter n β) := by
  induction n with
  | zero => simp [sqIter]
  | succ n ih =>
    rw [Nat.fold_succ, ih, Finset.sum_range_succ, List.map_map]
    congr 2
    · exact List.map_congr_left fun a _ => by simp [sqIter_succ']
    · rw [sqIter_succ']

theorem toArray_getD_list (L : List K) (l : ℕ) : L.toArray.getD l 0 = L.getD l 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- **Claim 2's fold meets `kwSL`** (at least 16 block coordinates). -/
theorem wEvalKC_eq (c : Array K) (β : K) (r ρ : List K) (hρ : 23 ≤ ρ.length) :
    wEvalKC c β r ρ = ∑ k ∈ range c.size, c.getD k 0 * kwSL (sqIter k β) (r.map (sqIter k)) ρ := by
  dsimp only [wEvalKC]
  rw [wEvalKC_fold]
  dsimp only
  refine Finset.sum_congr rfl fun k _ => ?_
  have hn : (ρ.drop 7).toArray.size = ρ.length - 7 := by simp
  rw [kwSL, hn, KW.kwI_eq (by omega), eqPtsC_eq]
  congr 3 <;> funext l <;> simp only [ptOf, toArray_getD_list]

/-! ## S-T1: the fast folds meet the reference folds -/

/-- A fold that commutes with a map of states. -/
theorem fold_sim {σ τ : Type*} (g : σ → τ) (f1 : ℕ → σ → σ) (f2 : ℕ → τ → τ)
    (h : ∀ k s, f2 k (g s) = g (f1 k s)) (s : σ) :
    ∀ n, Nat.fold n (fun k _ => f2 k) (g s) = g (Nat.fold n (fun k _ => f1 k) s)
  | 0 => rfl
  | n + 1 => by rw [Nat.fold_succ, Nat.fold_succ, fold_sim g f1 f2 h s n, h]

theorem ofF_mul' (a b : F) : K.ofF (a * b) = K.ofF a * K.ofF b := map_mul K.ofFRingHom a b

theorem ofF_sq (a : F) : K.ofF (F.sq a) = K.ofF a * K.ofF a := by rw [F.sq_eq_mul, ofF_mul']

/-- **`wEvalCF` is `wEvalC` at the embedded point.** -/
theorem wEvalCF_eq (c : Array K) (r : Array F) (ρ : List K) :
    wEvalCF c r ρ = wEvalC c (r.toList.map K.ofF) ρ := by
  unfold wEvalCF wEvalC
  have := fold_sim (fun p : K × Array F => (p.1, p.2.toList.map K.ofF))
    (fun k (p : K × Array F) => (p.1 + c.getD k 0 * eqPtsC (p.2.toList.map K.ofF) ρ, p.2.map F.sq))
    (fun k (p : K × List K) => (p.1 + c.getD k 0 * eqPtsC p.2 ρ, p.2.map fun a => a * a))
    (fun k p => by simp [Array.toList_map, List.map_map, Function.comp_def, ofF_sq]) (0, r) c.size
  exact (congrArg Prod.fst this).symm

theorem sqIter_ofF (k : ℕ) (a : F) : sqIter k (K.ofF a) = K.ofF (sqIter k a) := by
  rw [sqIter_eq, sqIter_eq]; exact (map_pow K.ofFRingHom a _).symm

theorem sqIter_zeroF (k : ℕ) : sqIter k (0 : F) = 0 := by rw [sqIter_eq]; simp

theorem sq_ne_zero_iff (a : F) : (F.sq a != 0) = (a != 0) := by
  rw [F.sq_eq_mul, Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, mul_self_eq_zero]

theorem filter_map_comm {α : Type*} (P : α → Bool) (f : α → α) (hP : ∀ x, P (f x) = P x) :
    ∀ L : List α, (L.filter P).map f = (L.map f).filter P
  | [] => rfl
  | x :: L => by
    simp only [List.filter_cons, List.map_cons, hP]
    split <;> simp [filter_map_comm P f hP L]

/-- **The next stage's blocks are the squares** (Frobenius on `F`). -/
theorem mkEnt_sq (β : F) (q : ℕ → F) (gK : ℕ → Bool → K) (g : List (List (ℕ × Bool) × List ℕ)) :
    (KW.mkEnt (β ^ ·) (fun l b => if b then q l else 1 - q l) gK g).map (fun p => (F.sq p.1, p.2)) =
      KW.mkEnt (F.sq β ^ ·) (fun l b => if b then F.sq (q l) else 1 - F.sq (q l)) gK g := by
  let φ : F →+* F := frobenius F 2
  have hφ : ∀ a : F, F.sq a = φ a := fun a => by rw [F.sq_eq_mul, frobenius_def, pow_two]
  unfold KW.mkEnt
  rw [filter_map_comm _ _ (fun x => sq_ne_zero_iff x.1), List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, hφ, map_mul, map_list_sum, map_list_prod, List.map_map,
    Function.comp_def, map_pow]
  congr 3
  exact List.map_congr_left fun b _ => by split_ifs <;> simp [map_sub, map_one]

/-- Stage `k`'s blocks: the point's coordinates and `β` raised to `2^k`. -/
def gmK (sk : List (List (List (ℕ × Bool) × List ℕ))) (β : F) (r : Array F) (gK : ℕ → Bool → K)
    (k : ℕ) : List (List (F × K)) :=
  sk.map (KW.mkEnt (sqIter k β ^ ·)
    (fun l b => if b then sqIter k (r.getD (7 + l) 0) else 1 - sqIter k (r.getD (7 + l) 0)) gK)

theorem sqG_gmK (sk : List (List (List (ℕ × Bool) × List ℕ))) (β : F) (r : Array F)
    (gK : ℕ → Bool → K) (k : ℕ) : KW.sqG (gmK sk β r gK k) = gmK sk β r gK (k + 1) := by
  unfold KW.sqG gmK
  rw [List.map_map]
  refine List.map_congr_left fun g _ => ?_
  rw [Function.comp_apply, mkEnt_sq]
  simp only [F.sq_eq_mul, ← sqIter_succ']

/-- **The fast fold's invariant**: after `n` stages, the sum of the stage values, the point and
the blocks at `2^n`. -/
theorem kf_fold (c : Array K) (ρh : List K) (oρ : Array K) (β : F) (r : Array F)
    (gK : ℕ → Bool → K) : ∀ n,
    Nat.fold n (fun k _ => kfStep c ρh oρ k) (0, r, gmK KW.skelM β r gK 0, gmK KW.skelP β r gK 0) =
    (∑ k ∈ range n, c.getD k 0 * (eqPtsC (((r.map (sqIter k)).toList.take 7).map K.ofF) ρh *
        (KW.hornerK (fun l => K.ofF ((r.map (sqIter k)).getD (7 + l) 0) + oρ.getD l 0) 0
            ((gmK KW.skelM β r gK k).map KW.gsum) +
          KW.hornerK (fun l => K.ofF ((r.map (sqIter k)).getD (7 + l) 0) + oρ.getD l 0) 1
            ((gmK KW.skelP β r gK k).map KW.gsum))),
      r.map (sqIter n), gmK KW.skelM β r gK n, gmK KW.skelP β r gK n)
  | 0 => by simp [sqIter]
  | n + 1 => by
    rw [Nat.fold_succ, kf_fold c ρh oρ β r gK n, kfStep]
    simp only [sum_range_succ, sqG_gmK, Array.map_map, Function.comp_def, F.sq_eq_mul,
      ← sqIter_succ']

theorem getD_map_lt {α : Type*} (A : Array α) (f : α → α) (d : α) {i : ℕ} (hi : i < A.size) :
    (A.map f).getD i d = f (A.getD i d) := by
  simp [Array.getD_eq_getD_getElem?, hi]

/-- **`wEvalKF` meets claim 2's stage sum** (`wEvalKC_eq`'s right side) at a point in `F`. -/
theorem wEvalKF_eq (c : Array K) (β : F) (r : Array F) (ρ : List K) (hr : r.size = 23)
    (hρ : ρ.length = 23) : wEvalKF c β r ρ = ∑ k ∈ range c.size,
      c.getD k 0 * kwSL (sqIter k (K.ofF β)) ((r.toList.map K.ofF).map (sqIter k)) ρ := by
  unfold wEvalKF
  refine (congrArg Prod.fst (kf_fold c (ρ.take 7) ((ρ.drop 7).toArray.map (1 + ·)) β r
    (fun l b => if b then (ρ.drop 7).toArray.getD l 0 else 1 - (ρ.drop 7).toArray.getD l 0)
      c.size)).trans ?_
  dsimp only
  refine sum_congr rfl fun k _ => congrArg _ ?_
  have h16 : ρ.length - 7 = 16 := by omega
  rw [kwSL, h16, eqPtsC_eq]
  congr 1
  · simp [Array.toList_map, List.map_take, List.map_map, Function.comp_def, sqIter_ofF]
  · have hq : ptOf 16 (((r.toList.map K.ofF).map (sqIter k)).drop 7) =
        fun l : Fin 16 => K.ofF (sqIter k (r.getD (7 + l) 0)) := by
      funext l
      have := l.isLt
      simp [ptOf, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hr, sqIter_ofF,
        show 7 + l.val < 23 by omega]
    have hρ' : ptOf 16 (ρ.drop 7) = fun l : Fin 16 => (ρ.drop 7).toArray.getD l 0 := by
      funext l; simp only [ptOf, toArray_getD_list]
    rw [hq, hρ', sqIter_ofF]
    refine (KW.kwS_fast _ _ _ _ fun l hl => ?_).symm
    have hb : ((ρ.drop 7).toArray).size = 16 := by simp; omega
    rw [getD_map_lt _ _ _ (by rw [hr]; omega), getD_map_lt _ _ _ (by rw [hb]; exact hl)]

theorem ofF_f0 (a : Array K) (h : a.all (·.f₁ == 0) = true) :
    (a.map (·.f₀)).toList.map K.ofF = a.toList := by
  rw [Array.toList_map, List.map_map]
  conv_rhs => rw [← List.map_id a.toList]
  refine List.map_congr_left fun x hx => ?_
  rw [← Array.all_toList, List.all_eq_true] at h
  have h1 : x.f₁ = 0 := by simpa using h x hx
  obtain ⟨x0, x1⟩ := x
  simp only at h1
  subst h1
  rfl

/-- **`rsWeightF` is `rsWeightI`**, for every input. -/
theorem rsWeightF_eq (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) :
    rsWeightF r ps κ β ρ = rsWeightI r ps κ β ρ := by
  unfold rsWeightF rsWeightI
  refine congrArg List.sum (List.map_congr_left fun p _ => congrArg _ ?_)
  split_ifs with hF h1 h23
  · rw [wEvalKF_eq _ _ _ _ (by simp [h23.1]) (by simp [h23.2]),
      wEvalKC_eq _ _ _ _ (by simp [h23.2]), ofF_f0 _ hF]
  · rfl
  · rw [wEvalCF_eq, ofF_f0 _ hF]
  · rfl
  · rfl

/-- (+) The guard takes the fast path at a point in `F`. -/
theorem rsF_guard_pos : (#[K.ofF 1, K.ofF 0]).all (·.f₁ == 0) = true := by decide +kernel

/-- (−) … and falls back at a point outside `F` (`u`). -/
theorem rsF_guard_neg : (#[K.ofF 1, K.u]).all (·.f₁ == 0) = false := by decide +kernel

/-- **`rsWeight` meets its specification** (`r″` of 7 coordinates, `ρ` of at least 23: the block
coordinates cover the node layout's `2^16` blocks). -/
theorem rsWeight_meets (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) (hr : r.size = 7)
    (hρ : 23 ≤ ρ.size) : rsWeightI r ps κ β ρ = rsWeightS r ps κ β ρ := by
  unfold rsWeightI rsWeightS
  refine congrArg List.sum (List.map_congr_left fun p _ => congrArg _ ?_)
  have hc : ((phiTable r.toList).map K.ofF).size = 128 := by
    rw [Array.size_map, phiTable_size, Array.length_toList, hr]; norm_num
  have hg : ∀ k, ((phiTable r.toList).map K.ofF).getD k 0 = K.ofF ((phiTable r.toList).getD k 0) :=
    fun k => by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
      cases (phiTable r.toList)[k]? <;> rfl
  split_ifs
  · rw [wEvalKC_eq _ _ _ _ (by simpa using hρ), hc]
    exact Finset.sum_congr rfl fun k _ => by rw [hg]
  · rw [wEvalC_eq, hc]
    exact Finset.sum_congr rfl fun k _ => by rw [hg]

theorem digestMle_eq (θ : Array F) (e₀ e₁ : F) :
    digestMle (eqTable (List.ofFn (ptA 10 θ))) e₀ e₁ = mle (digTbl e₀ e₁) (ptA 10 θ) := by
  set g : ℕ → F := fun σ => eqAtR (ptA 10 θ) σ * if σ < 256 ∧ digBit e₀ e₁ σ then 1 else 0
  have hR : mle (digTbl e₀ e₁) (ptA 10 θ) = ∑ σ ∈ range (2 ^ 10), g σ := by
    rw [mle, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [eq_cube]; rfl
  have hs : ∑ σ ∈ range 256, g σ = ∑ σ ∈ range (2 ^ 10), g σ :=
    Finset.sum_subset (Finset.range_subset_range.2 (by norm_num)) fun σ _ hσ => by
      have : ¬σ < 256 := fun h => hσ (Finset.mem_range.2 h)
      simp only [g, this, false_and, ite_false, mul_zero]
  rw [hR, ← hs, digestMle, sumTo_eq]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hσ' : σ < 256 := Finset.mem_range.1 hσ
  rewrite [eqTable_ofFn_getD _ (show σ < 2 ^ 10 by omega)]
  simp only [g, hσ', true_and]
  split_ifs <;> simp

/-- **`shiftTarget` meets its specification** (at the same `κ_s`). -/
theorem shiftTarget_meets (κs : F) (τ θ bnd : Array F) :
    shiftTargetI κs τ θ bnd = shiftTargetS κs τ θ bnd := by
  unfold shiftTargetI shiftTargetS shiftTargetAt
  dsimp only
  rw [digestMle_eq, digestMle_eq, prodTo_eq, ← Fin.prod_univ_eq_prod_range]
  rfl

/-! ## Zero-padded `τ` (revision 3.15, ruling (c))

`finSh` gives `τ` and S2's block point `r_blk` 18 coordinates for every kind, P30's and N30's
padded with `0` in coordinates 16–17 (`FRVIRFinals.padB`). On such operands `eqPt`, `shiftEq` and
`shiftTarget` are their `m − 14`-coordinate forms (`eqPoint_pad`, `shiftEqS_pad`,
`shiftTargetS_pad`; `FRShift.eq_pad_zero`, `shiftPair_pad`, `shiftTarget_pad`). -/

theorem foldl_prod_range (g : ℕ → F) (n : ℕ) :
    (List.range n).foldl (fun acc v => acc * g v) 1 = ∏ v ∈ range n, g v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.prod_range_succ]; rfl

/-- `eqPoint` is `eq` at the arrays' points (over `a`'s length). -/
theorem eqPoint_eq (a b : Array F) : eqPoint a b = eq (ptA a.size a) (ptA a.size b) := by
  simp only [eqPoint]
  rw [foldl_prod_range, eq, ← Fin.prod_univ_eq_prod_range (fun v => a.getD v 0 * b.getD v 0 +
    (1 - a.getD v 0) * (1 - b.getD v 0))]
  rfl

theorem ptA_toArray (n : ℕ) (xs : List F) : ptA n xs.toArray = ptOf n xs := by
  funext l; simp [ptA, ptOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- `eqPoint` on points of one length is `shiftPair`'s first component. -/
theorem eqPoint_shiftPair (xs ys : List F) (h : xs.length = ys.length) :
    eqPoint xs.toArray ys.toArray = (shiftPair xs ys).1 := by
  rw [shiftPair_eq xs.length xs ys rfl h.symm, eqPoint_eq, List.size_toArray, ptA_toArray,
    ptA_toArray]

/-- **`eqPt` on zero-padded points** (`eq_pad_zero`). -/
theorem eqPoint_pad (k : ℕ) (xs ys : List F) (h : xs.length = ys.length) :
    eqPoint (xs ++ List.replicate k 0).toArray (ys ++ List.replicate k 0).toArray =
      eqPoint xs.toArray ys.toArray := by
  rw [eqPoint_shiftPair _ _ (by simp [h]), eqPoint_shiftPair _ _ h, shiftPair_pad k xs ys h]

/-- **`shiftEq`'s specification on zero-padded points** (`shiftPair_pad`). -/
theorem shiftEqS_pad (k : ℕ) (xs ys : List F) (h : xs.length = ys.length) :
    shiftEqS (xs ++ List.replicate k 0).toArray (ys ++ List.replicate k 0).toArray =
      shiftEqS xs.toArray ys.toArray := by
  rw [← shiftEq_meets _ _ (by simp [h]), ← shiftEq_meets _ _ (by simp [h]), shiftEqI, shiftEqI,
    List.toList_toArray, List.toList_toArray, shiftPair_pad k xs ys h]

/-- The last block's padded point: `1^n ‖ 0^k` (`finSh`'s `bnd[4 … 21]`). -/
def lastPad (n k : ℕ) : List F := List.replicate n 1 ++ List.replicate k 0

theorem getD_pad (xs : List F) (k i : ℕ) :
    (xs ++ List.replicate k 0).getD i 0 = xs.getD i 0 := by
  rcases lt_or_ge i xs.length with hi | hi
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi, List.getElem?_replicate,
      List.getElem?_eq_none hi]
    split_ifs <;> rfl

/-- **`shiftTarget`'s specification at a zero-padded `τ`** and the kind's padded last block
`1^n ‖ 0^k` (`n + k = 18`): `FRShift.shiftTarget` on the `n` block coordinates. -/
theorem shiftTargetS_pad (κs : F) (θ : Array F) {n k : ℕ} (hnk : n + k = 18) (τ b4 : List F)
    (hτ : τ.length = n) (hb : b4.length = 4) :
    shiftTargetS κs (τ ++ List.replicate k 0).toArray θ (b4 ++ lastPad n k).toArray =
      shiftTarget (ptA 10 θ) (ptOf n τ) κs (digTbl (b4.getD 0 0) (b4.getD 1 0))
        (digTbl (b4.getD 2 0) (b4.getD 3 0)) := by
  have hb' : ∀ j, j < 4 → (b4 ++ lastPad n k).toArray.getD j 0 = b4.getD j 0 := fun j hj => by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show j < b4.length by omega)]
  have hl : ∀ l, (b4 ++ lastPad n k).toArray.getD (4 + l) 0 = if l < n then 1 else 0 := fun l => by
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, lastPad,
      List.getElem?_append_right (show b4.length ≤ 4 + l by omega), hb, Nat.add_sub_cancel_left]
    rcases lt_or_ge l n with h | h
    · simp [List.getElem?_append_left (show l < (List.replicate n (1 : F)).length by simpa), h]
    · simp only [List.getElem?_append_right (show (List.replicate n (1 : F)).length ≤ l by simpa),
        List.getElem?_replicate, List.length_replicate, show ¬ l < n by omega, ite_false]
      split_ifs <;> rfl
  unfold shiftTargetS shiftTargetAt shiftTarget
  rw [hb' 0 (by omega), hb' 1 (by omega), hb' 2 (by omega), hb' 3 (by omega)]
  congr 2
  rw [eq_cube, eq]
  simp only [ptA, lastOf, ptOf]
  have e18 := Fin.prod_univ_eq_prod_range (fun l : ℕ => (τ ++ List.replicate k (0 : F)).toArray.getD l 0 *
      (b4 ++ lastPad n k).toArray.getD (4 + l) 0 + (1 - (τ ++ List.replicate k (0 : F)).toArray.getD l 0) *
      (1 - (b4 ++ lastPad n k).toArray.getD (4 + l) 0)) 18
  have en := Fin.prod_univ_eq_prod_range
    (fun l : ℕ => if (lastBlk n).val.testBit l then τ.getD l 0 else 1 - τ.getD l (0 : F)) n
  rw [e18, en]
  · rw [← hnk, Finset.prod_range_add]
    have h2 : ∀ x ∈ range k, (τ ++ List.replicate k 0).toArray.getD (n + x) 0 *
        (b4 ++ lastPad n k).toArray.getD (4 + (n + x)) 0 +
        (1 - (τ ++ List.replicate k 0).toArray.getD (n + x) 0) *
        (1 - (b4 ++ lastPad n k).toArray.getD (4 + (n + x)) 0) = 1 := fun x _ => by
      rw [hl, if_neg (by omega)]
      simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right (show τ.length ≤ n + x by omega),
        hτ]
    rw [Finset.prod_eq_one h2, mul_one]
    refine Finset.prod_congr rfl fun l hl' => ?_
    have hln : l < n := Finset.mem_range.1 hl'
    rw [hl, if_pos hln, show (lastBlk n).val = 2 ^ n - 1 from rfl, Nat.testBit_two_pow_sub_one,
      decide_eq_true hln, if_pos rfl]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l < τ.length by omega)]

/-- **`targetS` meets the leaf kinds' specification**, for every number `b` of block bits. -/
theorem targetSLeaf_meets (b : ℕ) (r : Array F) : targetSLeafI r = targetSLeafS b r := by
  unfold targetSLeafI targetSLeafS
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [FR.targetS, ← (joinEquiv 8 b).sum_comp, Fintype.sum_prod_type, sumTo_eq,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun hi _ => ?_
  have hj : ∀ t : Fin (2 ^ b), (join hi t).val % 256 = hi.val := fun t => by
    show (2 ^ 8 * t.val + hi.val) % 256 = hi.val
    have := hi.isLt; omega
  have hc : chainTab.getD (σ.val + 64 * hi.val) 0 = chainE (σ.val + 64 * hi.val) := by
    have : σ.val + 64 * hi.val < 2 ^ 14 := by have := σ.isLt; have := hi.isLt; omega
    simp only [chainTab, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, this, dite_true,
      Option.getD_some]
  simp only [show ∀ t, (joinEquiv 8 b) (hi, t) = join hi t from fun _ => rfl, eq_append_join, hj]
  set e₁ := eq (zLo r) (cube hi)
  set C := chainE (σ.val + 64 * hi.val)
  rw [show ∑ x : Fin (2 ^ b), e₁ * eq (fun l : Fin b => r.getD (1 + l) 0) (cube x) * C =
      e₁ * C * ∑ x : Fin (2 ^ b), eq (fun l : Fin b => r.getD (1 + l) 0) (cube x) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring,
    eq_sum_one, mul_one, hc, eqTable_ofFn_getD _ hi.isLt, mul_comm]
  simp only [e₁, eq_cube, eqAtR]

end Tables

/-! ## Controls (§5.6) -/

theorem skipNode_injOn (N : ℕ) (hN : N ≤ 128) :
    Set.InjOn (fun b : Fin N => xT b) (Finset.univ : Finset (Fin N)) := fun a _ b _ h => by
  have ha := a.isLt; have hb := b.isLt
  dsimp only at h
  rw [xT_eq, xT_eq] at h
  unfold xS at h
  have := congrArg Fin.val (skipNode_injective h)
  simp only [Nat.mod_eq_of_lt (show a.val < 128 by omega),
    Nat.mod_eq_of_lt (show b.val < 128 by omega)] at this
  exact Fin.ext this

set_option maxRecDepth 4000 in
/-- (+) The computed Lagrange weights are the Lagrange basis: weight `i` at node `i` is `1`. -/
theorem ctrl_lag_self {i : ℕ} (hi : i < 64) : (lagW xT 64 denS (xT i)).getD i 0 = 1 := by
  rewrite [denS, lagW_eq _ _ _ hi, lagrangeWeight_eq]
  exact Lagrange.eval_basis_self (i := (⟨i, hi⟩ : Fin 64)) (skipNode_injOn 64 (by norm_num))
    (Finset.mem_univ _)

/-- (−) … and weight `i` at another node `j` is `0`. -/
theorem ctrl_lag_other {i j : ℕ} (hi : i < 64) (hj : j < 64) (hij : i ≠ j) :
    (lagW xT 64 denS (xT j)).getD i 0 = 0 := by
  rewrite [denS, lagW_eq _ _ _ hi, lagrangeWeight_eq]
  exact Lagrange.eval_basis_of_ne (s := Finset.univ) (v := fun b : Fin 64 => xT b)
    (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (fun h => hij (congrArg Fin.val h)) (Finset.mem_univ _)

/-- A Boolean point as an array (10 coordinates). -/
def cubeA (u : Fin (2 ^ 10)) : Array F := Array.ofFn (cube (R := F) u)

theorem eqAtR_cubeA (u : Fin (2 ^ 10)) {σ : ℕ} (hσ : σ < 2 ^ 10) :
    eqAtR (ptA 10 (cubeA u)) σ = if u.val = σ then 1 else 0 := by
  have : ptA 10 (cubeA u) = cube u := funext fun l => by
    simp [ptA, cubeA, Array.getD_eq_getD_getElem?]
  rw [this, show eqAtR (cube (R := F) u) σ = eq (cube u) (cube (⟨σ, hσ⟩ : Fin (2 ^ 10))) by
    rw [eq_cube]; rfl, eq_cube_cube]
  simp [Fin.ext_iff]

/-- (+) The slot weight at the Boolean points `θ = σ₀`, `r = base + σ₀` is `1`. -/
theorem ctrl_slotW_hit (s : ℕ) (σ₀ : Fin 256) :
    slotWI s (cubeA ⟨σ₀, by omega⟩) (cubeA ⟨slotBase s + σ₀, by unfold slotBase; split <;> omega⟩)
      = 1 := by
  rw [slotW_meets, slotWS, Finset.sum_eq_single σ₀.val]
  · rw [eqAtR_cubeA _ (by omega), eqAtR_cubeA _ (by unfold slotBase; split <;> omega)]; simp
  · intro σ hσ hne
    rw [eqAtR_cubeA _ (by simp at hσ; omega)]
    simp [Ne.symm hne]
  · simp

/-- (−) … and `0` when `r` is the position of another slot index. -/
theorem ctrl_slotW_miss (s : ℕ) (σ₀ σ₁ : Fin 256) (h : σ₀ ≠ σ₁) :
    slotWI s (cubeA ⟨σ₀, by omega⟩) (cubeA ⟨slotBase s + σ₁, by unfold slotBase; split <;> omega⟩)
      = 0 := by
  rw [slotW_meets, slotWS]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  have hσ' : σ < 256 := Finset.mem_range.1 hσ
  rw [eqAtR_cubeA _ (by omega), eqAtR_cubeA _ (by unfold slotBase; split <;> omega)]
  by_cases h0 : σ₀.val = σ
  · have : ¬(σ₁.val = σ) := fun h' => h (Fin.ext (by omega))
    simp [h0, this]
  · simp [h0]

end Impl
end FR

end G6_FRVerifierImplOps
