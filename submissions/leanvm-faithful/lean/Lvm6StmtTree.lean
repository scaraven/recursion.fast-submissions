/-
# The tree relation on the committed stack (WP S; BLUEPRINT §2.2–§2.3, statement T1)

The stack `q` is the committed polynomial on the Boolean cube, index `r + 2^(k+1)·slot` (slot
high; `k = logN`, so `2^(k+1)` heap rows). Row `r` has an input state `rowIn q r`: a parent row
(`r < 2^k`) hashes its slots 0–3 and 4–7 as the raw words of its two children's digests
(`nodeLanes`), a leaf row (`r ≥ 2^k`) its slots 0–3 as one block (`itemLanes`). Its outputs are
**virtual**: `rowOut q r m` is lane `m` of `keccakF (rowIn q r)` (relation (G) of §2.3 is the
definition; the middle-state slots 8–32 are mechanism of the Keccak GKR and do not appear).

* **`TreeOkAt k q h`**, relation `TreeOk(q, h)` of §2.3: (W) the left words of every parent row
  but row 0 are its left child's output, the right words of every parent row (row 0 included)
  are its right child's output; (R) row 0's right words are `h`. With (W) at row 0 this says
  `D(1) = h`.
* `blocksOfAt k q`: the leaf rows' slots 0–3 as digests (what the extractor outputs).
* **`treeOk_sound`** (§S's `tree_sound`, a name T1's heap lemma already has):
  `TreeOk q h → dataRoot (blocksOf q) = h`, from T1's `rows_root`.
* **`honest_treeOk`** (non-vacuity): the honest stack of any `2^k` blocks satisfies
  `TreeOkAt k · (dataRoot xs)`, and its blocks are `xs` (`blocksOf_honest`).

Slots 4–7 of leaf rows and slots 0–3 of row 0 are unconstrained (no weight reads them; §2.2).
-/
import Lvm6LeafRows
import LvmFields

set_option autoImplicit false

namespace Lvm6

open RecursionFast RecursionFast.Keccak LeanVM.Parameters

/-! ## Specification -/

/-- **The stack**: the committed words on the Boolean cube (only indices below `2^M` are read). -/
abbrev Stack : Type := ℕ → K

variable (k : ℕ)

/-- Word `s` (the slot) of heap row `r`, as a lane. -/
def slot (q : Stack) (r s : ℕ) : UInt64 := K.lane (q (r + 2 ^ (k + 1) * s))

/-- **The input state of row `r`**: a parent row (`r < 2^k`) hashes its two children's raw
digests (slots 0–3, 4–7), a leaf row its block (slots 0–3). -/
def rowIn (q : Stack) (r : ℕ) : State :=
  if r < 2 ^ k then nodeLanes (fun m => slot k q r m) (fun m => slot k q r (4 + m))
  else itemLanes (fun m => slot k q r m)

/-- Output lane `m` of row `r`: `Keccak-f` of its input (virtual, not committed). -/
def rowOut (q : Stack) (r m : ℕ) : UInt64 := laneOf (keccakF (rowIn k q r)) m

/-- **The tree relation** `TreeOk(q, h)` (BLUEPRINT §2.3) at `2^k` blocks. -/
structure TreeOkAt (q : Stack) (h : Digest) : Prop where
  /-- (W) A parent row other than row 0 carries its left child's output in slots 0–3. -/
  left : ∀ r, 1 ≤ r → r < 2 ^ k → ∀ m < 4, slot k q r m = rowOut k q (2 * r) m
  /-- (W) Every parent row carries its right child's output in slots 4–7. -/
  right : ∀ r < 2 ^ k, ∀ m < 4, slot k q r (4 + m) = rowOut k q (2 * r + 1) m
  /-- (R) Row 0's slots 4–7 are the words of `h`. -/
  root : ∀ m < 4, slot k q 0 (4 + m) = dLane h m

/-- **The blocks** of a stack: the leaf rows' slots 0–3, in order. -/
def blocksOfAt (q : Stack) : List Digest :=
  (List.range (2 ^ k)).map fun i => ofWords fun m => slot k q (2 ^ k + i) m

/-- The tree relation at the season's `N★ = 2^18`. -/
abbrev TreeOk : Stack → Digest → Prop := TreeOkAt 18

/-- The blocks at `N★ = 2^18`. -/
abbrev blocksOf : Stack → List Digest := blocksOfAt 18

/-! ## Proof helpers -/

theorem itemLanes_congr {w w' : ℕ → UInt64} (hw : ∀ j < 4, w j = w' j) :
    itemLanes w = itemLanes w' := by
  simp only [itemLanes, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]

theorem length_blocksOfAt (q : Stack) : (blocksOfAt k q).length = 2 ^ k := by simp [blocksOfAt]

theorem getElem_blocksOfAt (q : Stack) {i : ℕ} (hi : i < (blocksOfAt k q).length) :
    (blocksOfAt k q)[i] = ofWords fun m => slot k q (2 ^ k + i) m := by
  simp [blocksOfAt]

/-- The heap rows of a stack satisfy T1's `RowsOk` over its blocks. -/
theorem rowsOk_of_treeOk {q : Stack} {h : Digest} (hT : TreeOkAt k q h) :
    RowsOk (blocksOfAt k q) (rowIn k q) (fun r => keccakF (rowIn k q r)) where
  perm _ _ _ := rfl
  node r h1 h2 := by
    rw [length_blocksOfAt] at h2
    rw [rowIn, ite_eq_left h2]
    exact nodeLanes_congr (fun j hj => hT.left r h1 h2 j hj) (fun j hj => hT.right r h2 j hj)
  leaf i hi := by
    have hi' : i < 2 ^ k := by rwa [length_blocksOfAt] at hi
    rw [getElem_blocksOfAt, length_blocksOfAt, rowIn, ite_eq_right (by omega)]
    exact itemLanes_congr fun j hj => (dLane_ofWords _ hj).symm

/-! ## Load-bearing lemmas -/

/-- **Tree soundness** at `2^k` blocks. -/
theorem TreeOkAt.sound {q : Stack} {h : Digest} (hT : TreeOkAt k q h) :
    dataRoot (blocksOfAt k q) = h :=
  rows_root (length_blocksOfAt k q) (rowsOk_of_treeOk k hT) fun j hj => by
    have := hT.right 0 (by positivity) j hj
    rw [hT.root j hj] at this
    exact this.symm

/-- **Tree soundness** (BLUEPRINT T1, `FORMAT6.md` §S's `tree_sound`; the name `tree_sound` is T1's
heap form in `Lvm6LeafTree`): the tree relation gives `dataRoot (blocksOf q) = h`. -/
theorem treeOk_sound {q : Stack} {h : Digest} : TreeOk q h → dataRoot (blocksOf q) = h :=
  TreeOkAt.sound 18

/-! ## Non-vacuity: the honest stack -/

/-- The honest words of row `r`, slot `s`, for the blocks `xs` (`2^k` of them): parent rows carry
their children's digests (row 0: zero, then the root), leaf rows their block. -/
def honestSlot (xs : List Digest) (r s : ℕ) : UInt64 :=
  if r < 2 ^ k then
    if s < 4 then (if r = 0 then 0 else dLane (heapOf xs (2 * r)) s)
    else if s < 8 then dLane (heapOf xs (2 * r + 1)) (s - 4) else 0
  else if s < 4 then dLane (xs.getD (r - 2 ^ k) d0) s else 0

/-- **The honest stack** of the blocks `xs`. -/
def honestStack (xs : List Digest) : Stack := fun i =>
  K.ofLane (honestSlot k xs (i % 2 ^ (k + 1)) (i / 2 ^ (k + 1)))

theorem slot_honest (xs : List Digest) {r : ℕ} (hr : r < 2 ^ (k + 1)) (s : ℕ) :
    slot k (honestStack k xs) r s = honestSlot k xs r s := by
  have hp : 0 < 2 ^ (k + 1) := by positivity
  have h1 : (r + 2 ^ (k + 1) * s) % 2 ^ (k + 1) = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have h2 : (r + 2 ^ (k + 1) * s) / 2 ^ (k + 1) = s := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, zero_add]
  simp only [slot, honestStack, h1, h2]
  rfl

theorem rowIn_honest {xs : List Digest} (hn : xs.length = 2 ^ k) {r : ℕ} (h1 : 1 ≤ r)
    (h2 : r < 2 ^ (k + 1)) : rowIn k (honestStack k xs) r = rowsIn xs r := by
  rw [rowIn, rowsIn, hn]
  by_cases hr : r < 2 ^ k
  · rw [ite_eq_left hr, ite_eq_left hr]
    refine nodeLanes_congr (fun j hj => ?_) (fun j hj => ?_)
    · rw [slot_honest k xs h2, honestSlot, ite_eq_left hr, ite_eq_left hj, ite_eq_right (by omega)]
    · rw [slot_honest k xs h2, honestSlot, ite_eq_left hr, ite_eq_right (by omega), ite_eq_left (by omega),
        Nat.add_sub_cancel_left]
  · rw [ite_eq_right hr, ite_eq_right hr]
    exact itemLanes_congr fun j hj => by rw [slot_honest k xs h2, honestSlot, ite_eq_right hr, ite_eq_left hj]

theorem rowOut_honest {xs : List Digest} (hn : xs.length = 2 ^ k) {r : ℕ} (h1 : 1 ≤ r)
    (h2 : r < 2 ^ (k + 1)) {m : ℕ} (hm : m < 4) :
    rowOut k (honestStack k xs) r m = dLane (heapOf xs r) m := by
  rw [rowOut, rowIn_honest k hn h1 h2, laneOf_eq _ hm,
    ← heapOf_eq_rows xs h1 (by rw [hn, ← pow_succ']; exact h2)]

/-- **Non-vacuity of `TreeOk`**: the honest stack of `2^k` blocks satisfies the tree relation
for their data root. -/
theorem honest_treeOk {xs : List Digest} (hn : xs.length = 2 ^ k) :
    TreeOkAt k (honestStack k xs) (dataRoot xs) where
  left r h1 h2 m hm := by
    rw [slot_honest k xs (by rw [pow_succ]; omega), honestSlot, ite_eq_left h2, ite_eq_left hm,
      ite_eq_right (by omega), rowOut_honest k hn (by omega) (by rw [pow_succ]; omega) hm]
  right r h2 m hm := by
    rw [slot_honest k xs (by rw [pow_succ]; omega), honestSlot, ite_eq_left h2, ite_eq_right (by omega),
      ite_eq_left (by omega), Nat.add_sub_cancel_left,
      rowOut_honest k hn (by omega) (by rw [pow_succ]; omega) hm]
  root m hm := by
    rw [slot_honest k xs (by positivity), honestSlot, ite_eq_left (by positivity), ite_eq_right (by omega),
      ite_eq_left (by omega), Nat.add_sub_cancel_left, Nat.mul_zero, Nat.zero_add, heapOf_one hn]

/-- The honest stack's blocks are `xs`. -/
theorem blocksOf_honest {xs : List Digest} (hn : xs.length = 2 ^ k) :
    blocksOfAt k (honestStack k xs) = xs := by
  refine List.ext_getElem (by rw [length_blocksOfAt, hn]) fun i hi _ => ?_
  have hi' : i < 2 ^ k := by rwa [length_blocksOfAt] at hi
  rw [getElem_blocksOfAt]
  refine digest_ext_dLane fun j hj => ?_
  rw [dLane_ofWords _ hj, slot_honest k xs (by rw [pow_succ]; omega), honestSlot,
    ite_eq_right (by omega), ite_eq_left hj, Nat.add_sub_cancel_left]
  simp [List.getD_eq_getElem?_getD, hn ▸ hi']

end Lvm6
