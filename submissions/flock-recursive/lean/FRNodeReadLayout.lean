-- New for `flock-recursive` (BLUEPRINT A.7; stage S-H2, track L-ext, S-H2k).
import FRNodeReadCore
import FRNodeCircuit

/-!
# `FRNodeRead`'s cells are the node layout's

`FRNodeRead` does not import `FRNodeLayout` (the extractor's modules would then depend on the
verifier's compiler), so it restates two constants. This module checks them against the layout:
the stream's cells are `Node.seedCell`'s (A.7's public cells), and the L base and the chain
length are `Layout.lBase` and `Layout.chainN`.
-/

namespace FR.Read

/-- **The constants are the layout's.** -/
theorem consts_eq : lBlk = Layout.lBase ∧ chainLen = Layout.chainN := by
  rw [chainLen_eq]; exact ⟨rfl, rfl⟩

/-- **Slot `σ`'s seed payload element `e` is the public cell `Node.seedCell`** (0-based slots
there, `σ ∈ {1, 2}` here). -/
theorem streamCell_seedCell (σ e : ℕ) : streamCell (σ + 1) (1 + e) = Node.seedCell σ e := by
  simp only [streamCell, Node.seedCell, Nat.add_sub_cancel, consts_eq.2]

/-- **The child statement is `PubCells`' `cᵢ`**: its cells are slot `σ`'s public cells 3 and 4
(payload elements 2–3). -/
theorem readStmt_cells (w : ℕ → F) (σ : ℕ) :
    readStmt w (σ + 1) = digestOf w (Node.seedCell σ 2) (Node.seedCell σ 3) := by
  rw [readStmt, ← streamCell_seedCell, ← streamCell_seedCell]

end FR.Read
