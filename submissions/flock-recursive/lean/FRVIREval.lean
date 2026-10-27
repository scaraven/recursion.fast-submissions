-- New for `flock-recursive` (BLUEPRINT §4.4, §7, A.8, stage S-E2).
import FRSpartan
import FRBlake2sWalk
import FRNodeLayout

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

`evalM`, `evalL` (the node's M and L matrices' MLEs) are the matrices of `compileMux (gen fin)`'s
rows, so they wait for S-0's `gen fin` (RESULT §6).
-/

namespace FR
namespace Eval
open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-! ## `walkA`, `walkB` -/

/-- An array as a function on the circuit's positions. -/
def onPos (a : Array F) (k : Pos Blake2sCircuit.m) : F := a.getD k.val 0

/-- The walk (implementation). -/
def walkImpl (rowW colW : Array F) : F × F := walkAB (onPos rowW) (onPos colW)

/-- **`walkA`'s specification**: `Σ_k rowW[k] · (A₀ colW)_k`. -/
noncomputable def walkSpecA (rowW colW : Array F) : F :=
  ∑ k, onPos rowW k * BlockR1CS.mulVec blake2sCircuit.toBlockR1CS.A (onPos colW) k

/-- **`walkB`'s specification**. -/
noncomputable def walkSpecB (rowW colW : Array F) : F :=
  ∑ k, onPos rowW k * BlockR1CS.mulVec blake2sCircuit.toBlockR1CS.B (onPos colW) k

theorem walkA_eq (rowW colW : Array F) : (walkImpl rowW colW).1 = walkSpecA rowW colW := by
  simp only [walkImpl, walk_eq_sum, walkSpecA]

theorem walkB_eq (rowW colW : Array F) : (walkImpl rowW colW).2 = walkSpecB rowW colW := by
  simp only [walkImpl, walk_eq_sum, walkSpecB]

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

end Eval
end FR
