/-
# The data tree as rows of permutations, in lanes (lvm6, work package T1)

The tree batch of BLUEPRINT §2.3 has one Keccak row per heap row `κ ∈ [1, 2n)`: an input state
`In κ` and an output state `Out κ`. This module states what its relations give, in the lane form
the Keccak GKR proves them in (`Lvm6LeafBlock`):

* `RowsOk xs In Out`: (G) every row's output is `keccakF` of its input; (W) a parent row's input
  is `nodeLanes` of its two children's output lanes `0 … 3`; (L) leaf row `n + i`'s input is
  `itemLanes` of the words of block `xs[i]`.
* **`rows_sound`**: at `n = 2^k`, row 1's digest is `dataRoot xs`; **`rows_root`**: if row 1's
  output lanes `0 … 3` are the words of `h`, then `dataRoot xs = h`.
* `rowsIn`, **`rowsIn_ok`**: the honest rows (built from `heapOf`) satisfy `RowsOk`, so the
  relation is not vacuous.

The root check on row 0 and the random-point form of (W) are the next work package's (K1).
-/
import Lvm6LeafBlock
import Lvm6LeafTree

namespace Lvm6

open RecursionFast RecursionFast.Keccak

/-! ## Specification -/

/-- Lane `j` of a state (`0` past 25). -/
def laneOf (a : State) (j : ℕ) : UInt64 := a.toArray.getD j 0

/-- **The tree rows' relations** over the blocks `xs` (`n = |xs|`), rows `1 … 2n − 1` in heap
order. -/
structure RowsOk (xs : List Digest) (In Out : ℕ → State) : Prop where
  /-- (G) Every row is one permutation. -/
  perm : ∀ κ, 1 ≤ κ → κ < 2 * xs.length → Out κ = keccakF (In κ)
  /-- (W) A parent's input lanes are its children's output lanes `0 … 3`, tagged and shifted. -/
  node : ∀ k, 1 ≤ k → k < xs.length →
    In k = nodeLanes (laneOf (Out (2 * k))) (laneOf (Out (2 * k + 1)))
  /-- (L) Leaf row `n + i`'s input lanes are the words of block `i`, tagged and shifted. -/
  leaf : ∀ i (hi : i < xs.length), In (xs.length + i) = itemLanes (dLane xs[i])

/-! ## Proof helpers -/

theorem nodeLanes_congr {l l' r r' : ℕ → UInt64} (hl : ∀ j < 4, l j = l' j)
    (hr : ∀ j < 4, r j = r' j) : nodeLanes l r = nodeLanes l' r' := by
  simp only [nodeLanes, hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide),
    hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide)]

theorem laneOf_eq (a : State) {j : ℕ} (hj : j < 4) : laneOf a j = dLane (outDigest a) j := by
  rw [dLane_outDigest _ hj, laneOf]
  simp [Array.getD_eq_getD_getElem?, show j < 25 by omega]

/-- The rows' digests satisfy the heap relations. -/
theorem heapOk_of_rows {xs : List Digest} {In Out : ℕ → State} (h : RowsOk xs In Out) :
    HeapOk xs (fun κ => outDigest (Out κ)) where
  leaf i hi := by
    rw [h.perm _ (by omega) (by omega), h.leaf i hi, ← leafItem_block]
  node k h1 h2 := by
    rw [h.perm _ h1 (by omega), h.node k h1 h2, dataNode_block]
    exact congrArg (fun s => outDigest (keccakF s))
      (nodeLanes_congr (fun j hj => laneOf_eq _ hj) (fun j hj => laneOf_eq _ hj))

/-! ## Load-bearing lemmas -/

/-- **Rows soundness**: at `n = 2^k`, row 1's digest is the data root. -/
theorem rows_sound {k : ℕ} {xs : List Digest} (hn : xs.length = 2 ^ k) {In Out : ℕ → State}
    (h : RowsOk xs In Out) : outDigest (Out 1) = dataRoot xs :=
  tree_sound hn (heapOk_of_rows h)

/-- **The root check**: if row 1's output lanes `0 … 3` are the words of `h`, the root is `h`. -/
theorem rows_root {k : ℕ} {xs : List Digest} (hn : xs.length = 2 ^ k) {In Out : ℕ → State}
    (h : RowsOk xs In Out) {d : Digest} (hd : ∀ j < 4, laneOf (Out 1) j = dLane d j) :
    dataRoot xs = d := by
  rw [← rows_sound hn h]
  exact digest_ext_dLane fun j hj => by rw [← laneOf_eq _ hj, hd j hj]

/-- The honest input rows: node rows from the computed heap's children, leaf rows from the
blocks. -/
def rowsIn (xs : List Digest) (κ : ℕ) : State :=
  if κ < xs.length then nodeLanes (dLane (heapOf xs (2 * κ))) (dLane (heapOf xs (2 * κ + 1)))
  else itemLanes (dLane (xs.getD (κ - xs.length) d0))

theorem heapOf_eq_rows (xs : List Digest) {κ : ℕ} (h1 : 1 ≤ κ) (h2 : κ < 2 * xs.length) :
    heapOf xs κ = outDigest (keccakF (rowsIn xs κ)) := by
  rw [heapOf, rowsIn]
  by_cases h : xs.length ≤ κ
  · rw [dite_eq_left h, ite_eq_right (by omega), ← leafItem_block]
    simp [List.getD_eq_getElem?_getD, show κ - xs.length < xs.length by omega]
  · rw [dite_eq_right h, ite_eq_right (by omega), ite_eq_left (by omega), dataNode_block]

/-- **Non-vacuity**: the honest rows satisfy `RowsOk` (for every `xs`). -/
theorem rowsIn_ok (xs : List Digest) :
    RowsOk xs (rowsIn xs) (fun κ => keccakF (rowsIn xs κ)) where
  perm _ _ _ := rfl
  node k h1 h2 := by
    rw [rowsIn, ite_eq_left h2]
    refine nodeLanes_congr (fun j hj => ?_) (fun j hj => ?_) <;>
      rw [laneOf_eq _ hj, ← heapOf_eq_rows _ (by omega) (by omega)]
  leaf i hi := by
    rw [rowsIn, ite_eq_right (by omega), Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, hi]

end Lvm6
