/-
# The data root at `n = 2^k` as a heap-indexed complete binary tree (lvm6, work package T1)

The contract's `dataRoot xs` (`RecursionFast/Contract/Relation.lean`) pairs adjacent digests level
by level, an odd last one carried up. At `n = |xs| = 2^k` no level carries, and the tree is the
complete binary tree in heap order (BLUEPRINT §2.3): row `1` is the root, row `i ∈ [1, n)` has
children `2i` and `2i + 1`, rows `n … 2n − 1` are the leaf items `leafItem xs[i]` in order, and
row `0` is spare (the blueprint uses it for the root check).

* `HeapOk xs H`: a heap array `H` (rows indexed by `ℕ`; only rows `1 … 2n − 1` are read) satisfies
  the leaf-item and node relations.
* **`tree_sound`**: at `n = 2^k`, any such `H` has `H 1 = dataRoot xs` (what the extractor needs).
* `heapOf xs`: the heap computed by its own rule; **`heapOf_ok`** (it satisfies the relations) and
  **`heap_unique`** (the relations fix rows `1 … 2n − 1`) say that the relations determine a heap,
  and `heapOf_one` that its row 1 is the root.
-/
import RecursionFast.Library.Tree

namespace Lvm6

open RecursionFast

/-! ## Specification -/

/-- **The heap relations** over the blocks `xs` (`n = |xs|`): rows `n + i` are the leaf items,
row `i ∈ [1, n)` is the data node of rows `2i` and `2i + 1`. -/
structure HeapOk (xs : List Digest) (H : ℕ → Digest) : Prop where
  /-- Rows `n … 2n − 1`: the leaf items, in order. -/
  leaf : ∀ i (hi : i < xs.length), H (xs.length + i) = leafItem xs[i]
  /-- Rows `1 … n − 1`: the node of the two rows below. -/
  node : ∀ i, 1 ≤ i → i < xs.length → H i = dataNode (H (2 * i)) (H (2 * i + 1))

/-- The heap of `xs` computed by its own rule (rows `≥ 2n` and row `0` are the zero digest). -/
def heapOf (xs : List Digest) (i : ℕ) : Digest :=
  if h : xs.length ≤ i then (xs.map leafItem).getD (i - xs.length) (Vector.replicate 32 0)
  else if i = 0 then Vector.replicate 32 0
  else dataNode (heapOf xs (2 * i)) (heapOf xs (2 * i + 1))
termination_by xs.length - i
decreasing_by all_goals omega

/-! ## Proof helpers -/

/-- The zero digest, the default of `getD` below. -/
abbrev d0 : Digest := Vector.replicate 32 0

theorem getD_dataLevel : ∀ (cs : List Digest) (j : ℕ), 2 * j + 1 < cs.length →
    (dataLevel cs).getD j d0 = dataNode (cs.getD (2 * j) d0) (cs.getD (2 * j + 1) d0)
  | a :: b :: t, 0, _ => by simp [dataLevel]
  | a :: b :: t, j + 1, h => by
    rw [dataLevel, List.getD_cons_succ,
      getD_dataLevel t j (by simp only [List.length_cons] at h; omega)]
    simp only [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, List.getD_cons_succ]
  | [], _, h | [_], _, h => by simp at h

/-- Level `d` of the tree: `k − d` data levels above the leaf items. -/
theorem heap_level {k : ℕ} {xs : List Digest} (hn : xs.length = 2 ^ k) {H : ℕ → Digest}
    (hH : HeapOk xs H) : ∀ e ≤ k,
      (dataLevel^[e] (xs.map leafItem)).length = 2 ^ (k - e) ∧
      ∀ j < 2 ^ (k - e), H (2 ^ (k - e) + j) = (dataLevel^[e] (xs.map leafItem)).getD j d0
  | 0, _ => by
    refine ⟨by simp [hn], fun j hj => ?_⟩
    rw [Nat.sub_zero, ← hn] at *
    rw [hH.leaf j hj]
    simp [List.getD_eq_getElem?_getD, hj]
  | e + 1, he => by
    obtain ⟨hl, hr⟩ := heap_level hn hH e (by omega)
    have hp : 2 ^ (k - e) = 2 * 2 ^ (k - (e + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    rw [Function.iterate_succ_apply']
    refine ⟨by rw [length_dataLevel, hl, hp]; omega, fun j hj => ?_⟩
    have hk : 2 ^ (k - e) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hH.node _ (by have := Nat.one_le_two_pow (n := k - (e + 1)); omega) (by omega),
      getD_dataLevel _ _ (by omega), ← hr _ (by omega), ← hr _ (by omega)]
    congr 2 <;> omega

/-! ## Load-bearing lemmas -/

/-- **Tree soundness**: at `n = 2^k`, row 1 of any heap satisfying the relations is the root. -/
theorem tree_sound {k : ℕ} {xs : List Digest} (hn : xs.length = 2 ^ k) {H : ℕ → Digest}
    (hH : HeapOk xs H) : H 1 = dataRoot xs := by
  obtain ⟨hl, hr⟩ := heap_level hn hH k (Nat.le_refl k)
  rw [Nat.sub_self, Nat.pow_zero] at hl hr
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
  have h1 := hr 0 Nat.one_pos
  rw [hx] at h1
  rw [dataRoot_eq, root_of_iterate dataNode k (by rw [← dataLevel_eq]; exact hx)]
  exact h1

/-- The computed heap satisfies the relations. -/
theorem heapOf_ok (xs : List Digest) : HeapOk xs (heapOf xs) where
  leaf i hi := by
    rw [heapOf, dite_eq_left (by omega), Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, hi]
  node i h1 h2 := by
    rw [heapOf, dite_eq_right (by omega), ite_eq_right (by omega)]

/-- The relations determine rows `1 … 2n − 1`. -/
theorem heap_unique {xs : List Digest} {H H' : ℕ → Digest} (hH : HeapOk xs H) (hH' : HeapOk xs H')
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i < 2 * xs.length) : H i = H' i := by
  induction h : 2 * xs.length - i using Nat.strongRecOn generalizing i with
  | _ m ih =>
    by_cases hi : xs.length ≤ i
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
      rw [hH.leaf j (by omega), hH'.leaf j (by omega)]
    · rw [hH.node i h1 (by omega), hH'.node i h1 (by omega),
        ih _ (by omega) (2 * i) (by omega) (by omega) rfl,
        ih _ (by omega) (2 * i + 1) (by omega) (by omega) rfl]

/-- Row 1 of the computed heap is the root. -/
theorem heapOf_one {k : ℕ} {xs : List Digest} (hn : xs.length = 2 ^ k) :
    heapOf xs 1 = dataRoot xs :=
  tree_sound hn (heapOf_ok xs)

end Lvm6
