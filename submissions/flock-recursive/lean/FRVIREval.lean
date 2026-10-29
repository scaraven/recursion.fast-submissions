-- New for `flock-recursive` (BLUEPRINT §4.4, §7, A.8, stage S-E2).
import FRSpartan
import FRBlake2sWalk
import FRVIRFinalsCoreSG

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
