-- lvm6 X2 (part 2): RV3 M5, the extractor's tree relation is WP S's. New.
import Lvm6XLeaf
import Lvm6StmtTree

/-!
# The extractor's columns and S's stack (RV3 M5)

`colsOf k q` reads S's stack `q` as the decoded columns `Cols` the extractor's outputs use (slot `s`'s word at heap
row `r` is `slot k q r s`). Then

* **`xs6_colsOf`**: the extracted leaf data is S's `blocksOfAt k q` (at `k = 18`: `blocksOf q`, `xs6_blocksOf`);
* **`colTreeOk_iff`**: the extractor's `ColTreeOk (2^k)` on the columns is S's `TreeOkAt k` (so K1's `TreeOkG`
  gives it through `treeOkG_treeOkAt`), and `colTree_sound` agrees with S's `treeOk_sound`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast RecursionFast.Keccak Lvm.X LeanVM.Parameters

/-- **S's stack as columns**: slot `s`'s word at heap row `r`. -/
def colsOf (k : ℕ) (q : Stack) : Cols := fun s r => (slot k q r s).toBitVec

theorem u64_colsOf (k : ℕ) (q : Stack) (s r : ℕ) : u64 (colsOf k q s r) = slot k q r s := rfl

/-- **The extracted leaf data is S's blocks.** -/
theorem xs6_colsOf (k : ℕ) (q : Stack) : xs6 (2 ^ k) (colsOf k q) = blocksOfAt k q := by
  simp only [xs6, blocksOfAt]
  refine List.map_congr_left fun i _ => digest_ext_dLane fun j hj => ?_
  rw [dLane_digW (by simp [blkW]) hj, dLane_ofWords _ hj]
  interval_cases j <;> rfl

/-- At `N★ = 2^18`, RV3 M5's form. -/
theorem xs6_blocksOf (q : Stack) :
    xs6 (2 ^ 18) (fun s r => (K.lane (q (r + 2 ^ 19 * s))).toBitVec) = blocksOf q :=
  xs6_colsOf 18 q

theorem inLanes6_colsOf (k : ℕ) (q : Stack) (κ : ℕ) : inLanes6 (2 ^ k) (colsOf k q) κ = rowIn k q κ := by
  simp only [inLanes6, rowIn, u64_colsOf]

theorem dLane_outD6 (k : ℕ) (q : Stack) (κ : ℕ) {m : ℕ} (hm : m < 4) :
    dLane (outD6 (2 ^ k) (colsOf k q) κ) m = rowOut k q κ m := by
  rw [outD6, dLane_outDigest _ hm, inLanes6_colsOf, rowOut, laneOf]
  simp [Array.getD, show m < 25 by omega]

/-- **The extractor's tree relation is S's.** -/
theorem colTreeOk_iff (k : ℕ) (q : Stack) (h : Digest) : ColTreeOk (2 ^ k) (colsOf k q) h ↔ TreeOkAt k q h := by
  constructor
  · intro H
    exact ⟨fun r h1 h2 m hm => (H.wl r h1 h2 m hm).trans (dLane_outD6 k q _ hm),
      fun r h2 m hm => (H.wr r h2 m hm).trans (dLane_outD6 k q _ hm), H.root⟩
  · intro H
    exact ⟨fun r h1 h2 m hm => (H.left r h1 h2 m hm).trans (dLane_outD6 k q _ hm).symm,
      fun r h2 m hm => (H.right r h2 m hm).trans (dLane_outD6 k q _ hm).symm, H.root⟩

/-- `colTree_sound` on S's stack: the blocks of a stack satisfying `TreeOkAt` have root `h`. -/
theorem dataRoot_blocksOfAt {k : ℕ} {q : Stack} {h : Digest} (hT : TreeOkAt k q h) :
    dataRoot (blocksOfAt k q) = h := by
  rw [← xs6_colsOf]; exact colTree_sound rfl ((colTreeOk_iff k q h).2 hT)

end Lvm6.X
