-- New for lvm6 K1: the tree relation with the committed middle state implies WP S's `TreeOkAt`.
import Lvm6KStmt

/-!
# `TreeOkG` implies `TreeOkAt`

* **`treeOkG_treeOkAt : TreeOkGStmt`**: under (G) a row's virtual output (12 rounds of its middle
  state) is `keccakF` of its input lanes (`keccakF_eq`, `keccakF1600_eq`), so (W) and (R) of `TreeOkG`
  are those of S's `TreeOkAt`. With S's `TreeOkAt.sound`: **`treeOkG_sound`**,
  `TreeOkG (k+1) q h → dataRoot (blocksOfAt k q) = h`.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics
open LeanVM.Protocol.KeccakGkr (roundsFrom laneWord keccakF_eq)
open RecursionFast RecursionFast.Keccak

/-! ## Proof helpers -/

theorem inTree_eq_rowIn (k : ℕ) (q : Stack) (x : ℕ) : inTree (k + 1) q x = rowIn k q x := by
  have e0 : wordsAt (k + 1) q x 0 = fun m ↦ slot k q x m := funext fun j ↦ by
    simp [wordsAt, slot]
  have e4 : wordsAt (k + 1) q x 4 = fun m ↦ slot k q x (4 + m) := funext fun j ↦ rfl
  rw [inTree, rowIn, Nat.add_sub_cancel, e0, e4]

/-- Under (G) a row's output lane is a lane of `keccakF` of its input. -/
theorem outW_eq {k : ℕ} {q : Stack} {x : ℕ}
    (hp : midTree (k + 1) q x = roundsFrom 0 12 (inTree (k + 1) q x)) (m : ℕ) :
    K.lane (outW (k + 1) q x m) = rowOut k q x m := by
  rw [outW, hp, ← keccakF_eq, Lvm.KSponge.keccakF1600_eq, inTree_eq_rowIn]
  rfl

/-! ## The statements -/

/-- **`TreeOkG` implies WP S's `TreeOkAt`.** -/
theorem treeOkG_treeOkAt : TreeOkGStmt := by
  intro k q h ht
  have hk : 2 ^ (k + 1 - 1) = 2 ^ k := by rw [Nat.add_sub_cancel]
  have h2 : ∀ r < 2 ^ k, 2 * r + 1 < 2 ^ (k + 1) := fun r hr ↦ by rw [pow_succ]; omega
  refine ⟨fun r h1 hr m hm ↦ ?_, fun r hr m hm ↦ ?_, fun m hm ↦ ?_⟩
  · rw [slot, ht.wl r h1 (hk ▸ hr) m hm, outW_eq (ht.perm _ (by have := h2 r hr; omega))]
  · rw [slot, ht.wr r (hk ▸ hr) m hm, outW_eq (ht.perm _ (h2 r hr))]
  · rw [slot, zero_add, ht.root m hm]
    rfl

/-- **Tree soundness for `TreeOkG`** (S's `TreeOkAt.sound` after `treeOkG_treeOkAt`). -/
theorem treeOkG_sound {k : ℕ} {q : Stack} {h : Digest} (ht : TreeOkG (k + 1) q h) :
    dataRoot (blocksOfAt k q) = h :=
  TreeOkAt.sound k (treeOkG_treeOkAt k q h ht)

end Lvm6.K
