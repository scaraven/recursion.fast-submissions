-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, B-13; A.6, A.7; stage S-0′).
import FRShape4

/-!
# The `N2`/`N4`/`N8` node layouts: regions H, L, M, tightly packed (B-13, revision 4.1)

Blocks of `2^14` positions; a node of kind `κ` has `2^(m − 14)` blocks (`N2`: `2^17`, `N4`/`N8`:
`2^18`) and `2^(m − 7)` F cells. B-13 (4.1): a node is sized by its **total** witness bits, not by
a power-of-two H.

* **Slots.** A node has **two signed children** (`N2`/`N4`: the previous node and the aggregate
  leaf; `N8`: the two aggregate leaves of step 1) and **verifier slots** (`vslots`): `N2` the
  previous node and `≤ 2` segments (3), `N4` the previous node and `≤ 4` segments (5), `N8` `≤ 8`
  segments. Per signed child: one digest chain of its trace in H, one WOTS run (`wotsSlot4`); per
  verifier slot: the `hashStmt` blocks of its statement (3), the mirror `WM` (146), a `2^14`-element
  L stride and `2^20` M cells.
* **H** from block 0, used `hUsed` blocks at full occupancy. One trace of `seq4` hashes to
  `chainLenOf seq4 = 23,168` blocks; the aggregate leaf's chain hashes `0x54 ‖ tr₁ ‖ … ‖ tr_k`:
  `aggChainLen k = ⌈(1 + k · (streamBytesOf seq4 − 1)) / 64⌉` (`k = 2`: 46,336 with 63 bytes in
  its last block; `k = 4`: 92,672 with 61: **not** multiples of 64, so the last block needs the
  padding claim; S-0′ RESULT I-5).
* **L** at the first multiple of 256 after H (3.x's rule), `N_L = 2^logL` elements.
* **M** in the last `N_M / 128` blocks (`N_M = 2^logM` cells: `N2` `2^22`, `N4`/`N8` `2^23`); slot
  `σ`'s rows at `oneCell + (σ − 1) · 2^20`; M's `one` cell is `mBase · 128`.
* **Coordinates**: `τ` (M rows) `logM` = 22 / 23 / 23, `σ` (`f`'s cells) `m − 7` = 24 / 25 / 25
  (S-0′ issue I-3).

`hUsed_eq`, `regions_fit`, `mSlots_fit` are the closed-form checks (`decide` on numbers).
-/

namespace FR
namespace Rev4

/-- Blocks of a node. -/
def NodeKind.blocks (κ : NodeKind) : ℕ := 2 ^ (κ.m - 14)
/-- F cells of a node's `f`. -/
def NodeKind.cells (κ : NodeKind) : ℕ := 2 ^ (κ.m - 7)
/-- Verifier slots: the previous node (if any) and the segment sub-slots. -/
def NodeKind.vslots (κ : NodeKind) : ℕ := (if κ.hasPrev then 1 else 0) + κ.segSlots
/-- Segment sub-slots of the aggregate child(ren) (`N8`: two aggregates of `≤ 4`). -/
def NodeKind.aggSegs (κ : NodeKind) : ℕ := if κ.hasPrev then κ.segSlots else 4

/-- The aggregate leaf's digest-chain compressions with `k` segments. -/
def aggChainLen (k : ℕ) : ℕ := (1 + k * (streamBytesOf seq4 - 1) + 63) / 64
/-- WOTS blocks per signed child (3.x's `Layout.wotsSlot`). -/
def wotsSlot4 : ℕ := 133 * 3 + 67 + 2 * 16
/-- The mirror sub-region per verifier slot (3.x's `Layout.wmSlot`). -/
def wmSlot4 : ℕ := 146

/-- H's used blocks at full occupancy: the children's chains, `hashStmt` (3 per verifier slot),
WOTS (per signed child), `WM` (per verifier slot), 8 spare. -/
def NodeKind.hUsed (κ : NodeKind) : ℕ :=
  (if κ.hasPrev then chainLenOf seq4 + aggChainLen κ.segSlots else 2 * aggChainLen 4) +
    3 * κ.vslots + 2 * wotsSlot4 + wmSlot4 * κ.vslots + 8

/-- L's base block (the first multiple of 256 after H) and elements. -/
def NodeKind.lBase (κ : NodeKind) : ℕ := (κ.hUsed + 255) / 256 * 256
def NodeKind.nL (κ : NodeKind) : ℕ := 2 ^ κ.dims.logL
/-- M's cells, base block (the last `N_M / 128` blocks), `one` cell, slot `σ`'s first cell. -/
def NodeKind.nM (κ : NodeKind) : ℕ := 2 ^ κ.dims.logM
def NodeKind.mBase (κ : NodeKind) : ℕ := κ.blocks - κ.nM / 128
def NodeKind.oneCell (κ : NodeKind) : ℕ := κ.mBase * 128
/-- Per-slot M cells (3.x's `slotM`). -/
def slotM4 : ℕ := 2 ^ 20
def NodeKind.mSlot (κ : NodeKind) (σ : ℕ) : ℕ := κ.oneCell + (σ - 1) * slotM4
/-- The coordinates of `evalM`'s row point `τ` and cell point `σ`. -/
def NodeKind.tauCoords (κ : NodeKind) : ℕ := κ.dims.logM
def NodeKind.sigmaCoords (κ : NodeKind) : ℕ := κ.m - 7

theorem aggChainLen_eq : aggChainLen 2 = 46336 ∧ aggChainLen 4 = 92672 ∧
    (1 + 2 * (streamBytesOf seq4 - 1)) % 64 = 63 ∧ (1 + 4 * (streamBytesOf seq4 - 1)) % 64 = 61 := by
  simp only [aggChainLen, streamBytesOf_seq4]; decide

theorem hUsed_eq : NodeKind.N2.hUsed = 70955 ∧ NodeKind.N4.hUsed = 117589 ∧
    NodeKind.N8.hUsed = 187540 := by
  simp only [NodeKind.hUsed, NodeKind.vslots, NodeKind.hasPrev, NodeKind.segSlots, chainLenOf_seq4.1,
    aggChainLen_eq.1, aggChainLen_eq.2.1, wotsSlot4, wmSlot4]; decide

/-- **The regions are disjoint and inside the node** (tight packing): H `[0, hUsed)`, L
`[lBase, lBase + N_L/128)`, M `[mBase, blocks)`; `f` has `blocks · 128` cells. Slack before M:
`N2` 26,624 blocks, `N4` 77,824, `N8` 7,936 (1.04×). -/
theorem regions_fit (κ : NodeKind) :
    κ.hUsed ≤ κ.lBase ∧ κ.lBase + κ.nL / 128 ≤ κ.mBase ∧ κ.mBase + κ.nM / 128 = κ.blocks ∧
      κ.cells = κ.blocks * 128 := by
  have h := hUsed_eq
  cases κ <;> simp only [NodeKind.lBase, NodeKind.mBase, NodeKind.nL, NodeKind.nM, NodeKind.blocks,
    NodeKind.cells, NodeKind.dims, NodeKind.m, h] <;> decide

/-- **The verifier slots' M rows fit** `N_M` (`N2`: 3 of 4 slots of `2^20`; `N4`: 5 of 8; `N8`: 8
of 8). -/
theorem mSlots_fit (κ : NodeKind) : κ.vslots * slotM4 ≤ κ.nM := by cases κ <;> decide

/-- `τ`/`σ`: 22/24, 23/25, 23/25; `f`'s cells are `2^σ`, M's rows `2^τ`. -/
theorem coords_eq : (NodeKind.N2.tauCoords, NodeKind.N2.sigmaCoords) = (22, 24) ∧
    (NodeKind.N4.tauCoords, NodeKind.N4.sigmaCoords) = (23, 25) ∧
    (NodeKind.N8.tauCoords, NodeKind.N8.sigmaCoords) = (23, 25) ∧
    ∀ κ : NodeKind, κ.cells = 2 ^ κ.sigmaCoords ∧ κ.nM = 2 ^ κ.tauCoords :=
  ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- Negative (why `N2` is `m = 31` and `N8` cannot be `m = 31`): `N8`'s H alone exceeds `2^17`
blocks, and the 3.x M (`2^21` cells) does not hold `N2`'s three slots. -/
theorem sizes_neg : ¬ NodeKind.N8.hUsed ≤ 2 ^ 17 ∧ ¬ NodeKind.N2.vslots * slotM4 ≤ 2 ^ 21 := by
  rw [hUsed_eq.2.2]; decide

end Rev4
end FR
