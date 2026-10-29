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
  verifier slot: the `hashStmt` blocks of its statement (3), a `2^14`-element L stride and `2^20` M
  cells; per signed child (revision 4.4.1, PACK-4.4 §11.2 lever L1), the mirror `WM` (146): only the
  two signed children have WOTS runs and mirrors.
* **H** from block 0, used `hUsed` blocks at full occupancy. One trace of `seq4` hashes to
  `chainLenOf seq4 = 24,220` blocks (revision 4.4.1, the (β′) cap check and level 4's cap at depth 8); the aggregate leaf's chain hashes `0x54 ‖ tr₁ ‖ … ‖ tr_k`:
  `aggChainLen k = ⌈(1 + k · (streamBytesOf seq4 − 1)) / 64⌉` (`k = 2`: 48,440 with 63 bytes in
  its last block; `k = 3`: 72,660 with 62; `k = 4`: 96,880 with 61: **not** multiples of 64 for any
  `k ∈ {2, 3, 4}`, so the last block needs the `k`-gated padding, counter and final flag; S-0′ RESULT
  I-5, R-4-m2). H holds the chain of an aggregate child of at most `maxK` segments (`N2`: 2,
  `N4`/`N8`: 4); `FRVerifier4.childOk4` is the check that refuses a larger one (R-4-m2).
* **L** at the first multiple of 256 after H (3.x's rule), `N_L = 2^logL` elements: a `2^14`
  stride per verifier slot (`lSlots_fit`; `N8` exactly full).
* **M** in the last `N_M / 128` blocks (`N_M = 2^logM` cells: `N2` `2^22`, `N4`/`N8` `2^23`); slot
  `σ`'s rows at `oneCell + (σ − 1) · 2^20`; M's `one` cell is `mBase · 128`.
* **Coordinates**: `τ` (M rows) `logM` = 22 / 23 / 23, `σ` (`f`'s cells) `m − 7` = 24 / 25 / 25
  (S-0′ issue I-3).

`hUsed_eq`, `regions_fit`, `mSlots_fit`, `lSlots_fit` are the closed-form checks (`decide` on
numbers).
-/

namespace FR
namespace Rev4

/-- Blocks of a node. -/
def NodeKind.blocks (κ : NodeKind) : ℕ := 2 ^ (κ.m - 14)
/-- F cells of a node's `f`. -/
def NodeKind.cells (κ : NodeKind) : ℕ := 2 ^ (κ.m - 7)
/-- Verifier slots: the previous node (if any) and the segment sub-slots. -/
def NodeKind.vslots (κ : NodeKind) : ℕ := (if κ.hasPrev then 1 else 0) + κ.segSlots
/-- **The most segments of one aggregate child** (H holds its chain): `N2` 2, `N4` 4, `N8` 4 (two
aggregates of `≤ 4`). -/
def NodeKind.maxK (κ : NodeKind) : ℕ := if κ.hasPrev then κ.segSlots else 4

/-- The aggregate leaf's digest-chain compressions with `k` segments. -/
def aggChainLen (k : ℕ) : ℕ := (1 + k * (streamBytesOf seq4 - 1) + 63) / 64
/-- WOTS blocks per signed child (3.x's `Layout.wotsSlot`). -/
def wotsSlot4 : ℕ := 133 * 3 + 67 + 2 * 16
/-- The mirror sub-region per signed child (3.x's `Layout.wmSlot`). -/
def wmSlot4 : ℕ := 146

/-- H's used blocks at full occupancy: the children's chains, `hashStmt` (3 per verifier slot),
WOTS and `WM` (per signed child: revision 4.4.1's lever L1, PACK-4.4 §11.2), 8 spare. -/
def NodeKind.hUsed (κ : NodeKind) : ℕ :=
  (if κ.hasPrev then chainLenOf seq4 + aggChainLen κ.segSlots else 2 * aggChainLen 4) +
    3 * κ.vslots + 2 * wotsSlot4 + wmSlot4 * 2 + 8

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

theorem aggChainLen_eq : aggChainLen 2 = 48440 ∧ aggChainLen 4 = 96880 ∧
    (1 + 2 * (streamBytesOf seq4 - 1)) % 64 = 63 ∧ (1 + 4 * (streamBytesOf seq4 - 1)) % 64 = 61 := by
  simp only [aggChainLen, streamBytesOf_seq4]; decide

/-- `k = 3` is unaligned too (R-4-m2). -/
theorem aggChainLen_k3 : aggChainLen 3 = 72660 ∧ (1 + 3 * (streamBytesOf seq4 - 1)) % 64 = 62 := by
  simp only [aggChainLen, streamBytesOf_seq4]; decide

/-- `aggChainLen` is monotone: a child of `k ≤ maxK` segments has a chain no longer than H's
`aggChainLen maxK` blocks. -/
theorem aggChainLen_le {k k' : ℕ} (h : k ≤ k') : aggChainLen k ≤ aggChainLen k' :=
  Nat.div_le_div_right (by have := Nat.mul_le_mul_right (streamBytesOf seq4 - 1) h; omega)

/-- H's aggregate chains are `aggChainLen maxK` blocks. -/
theorem maxK_eq : NodeKind.N2.maxK = 2 ∧ NodeKind.N4.maxK = 4 ∧ NodeKind.N8.maxK = 4 := ⟨rfl, rfl, rfl⟩

theorem hUsed_eq : NodeKind.N2.hUsed = 73965 ∧ NodeKind.N4.hUsed = 122411 ∧
    NodeKind.N8.hUsed = 195080 := by
  simp only [NodeKind.hUsed, NodeKind.vslots, NodeKind.hasPrev, NodeKind.segSlots, chainLenOf_seq4.1,
    aggChainLen_eq.1, aggChainLen_eq.2.1, wotsSlot4, wmSlot4]; decide

/-- **The regions are disjoint and inside the node** (tight packing): H `[0, hUsed)`, L
`[lBase, lBase + N_L/128)`, M `[mBase, blocks)`; `f` has `blocks · 128` cells. Slack before M:
`N2` 23,808 blocks, `N4` 72,960, `N8` 256 (revision 4.4.1 (β′) with levers L1 and L2, before R-A′'s
spacers; neither lever alone fits `N8`: `regions_need_levers`). -/
theorem regions_fit (κ : NodeKind) :
    κ.hUsed ≤ κ.lBase ∧ κ.lBase + κ.nL / 128 ≤ κ.mBase ∧ κ.mBase + κ.nM / 128 = κ.blocks ∧
      κ.cells = κ.blocks * 128 := by
  have h := hUsed_eq
  cases κ <;> simp only [NodeKind.lBase, NodeKind.mBase, NodeKind.nL, NodeKind.nM, NodeKind.blocks,
    NodeKind.cells, NodeKind.dims, NodeKind.m, h] <;> decide

/-- **The verifier slots' M rows fit** `N_M` (`N2`: 3 of 4 slots of `2^20`; `N4`: 5 of 8; `N8`: 8
of 8). -/
theorem mSlots_fit (κ : NodeKind) : κ.vslots * slotM4 ≤ κ.nM := by cases κ <;> decide

/-- **The L region holds the verifier slots** (S-0′ I-4's `2^14` stride; R-4-m4): `N2` 3 of 4,
`N4` 5 of 8, `N8` 8 of 8 (`lSlots_N8_full`). -/
theorem lSlots_fit (κ : NodeKind) : κ.vslots * 2 ^ 14 ≤ κ.nL := by cases κ <;> decide
theorem lSlots_N8_full : NodeKind.N8.vslots * 2 ^ 14 = NodeKind.N8.nL := by decide

/-- `τ`/`σ`: 22/24, 23/25, 23/25; `f`'s cells are `2^σ`, M's rows `2^τ`. -/
theorem coords_eq : (NodeKind.N2.tauCoords, NodeKind.N2.sigmaCoords) = (22, 24) ∧
    (NodeKind.N4.tauCoords, NodeKind.N4.sigmaCoords) = (23, 25) ∧
    (NodeKind.N8.tauCoords, NodeKind.N8.sigmaCoords) = (23, 25) ∧
    ∀ κ : NodeKind, κ.cells = 2 ^ κ.sigmaCoords ∧ κ.nM = 2 ^ κ.tauCoords :=
  ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- `N8`'s H at a segment stream of `sb` bytes with `wm` mirror sub-regions (`NodeKind.hUsed`'s
`N8` case as a function of the two levers' quantities). -/
def hUsedN8At (sb wm : ℕ) : ℕ := 2 * ((1 + 4 * (sb - 1) + 63) / 64) + 3 * 8 + 2 * wotsSlot4 + wmSlot4 * wm + 8

/-- **Both levers are needed** (PACK-4.4 §11.2, PB-m5): (+) with L1 (2 mirror sub-regions) and L2
(`seq4`'s stream) `N8`'s L fits before M; (−) without L1 (8 sub-regions, one per verifier slot) it
does not, nor (−) without L2 (the (β′) stream at level 4's cap depth 7: 1,556,032 bytes). -/
theorem regions_need_levers :
    hUsedN8At (streamBytesOf seq4) 2 = NodeKind.N8.hUsed ∧
    (hUsedN8At (streamBytesOf seq4) 2 + 255) / 256 * 256 + 1024 ≤ NodeKind.N8.mBase ∧
    ¬ (hUsedN8At (streamBytesOf seq4) 8 + 255) / 256 * 256 + 1024 ≤ NodeKind.N8.mBase ∧
    ¬ (hUsedN8At 1556032 2 + 255) / 256 * 256 + 1024 ≤ NodeKind.N8.mBase := by
  rw [hUsed_eq.2.2, streamBytesOf_seq4]; decide

/-- Negative (why `N2` is `m = 31` and `N8` cannot be `m = 31`): `N8`'s H alone exceeds `2^17`
blocks, and the 3.x M (`2^21` cells) does not hold `N2`'s three slots. -/
theorem sizes_neg : ¬ NodeKind.N8.hUsed ≤ 2 ^ 17 ∧ ¬ NodeKind.N2.vslots * slotM4 ≤ 2 ^ 21 := by
  rw [hUsed_eq.2.2]; decide

end Rev4
end FR
