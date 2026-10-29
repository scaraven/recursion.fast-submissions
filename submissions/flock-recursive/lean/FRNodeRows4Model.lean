-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4, A.11's row model per kind; stage S-E12c,
-- track L-circ). 3.x's analogue: `FRNodeLayout.mRowModel`.
import FRNodeRows4

/-!
# The 4.1 nodes' M row model (`mRowModel4`) and `mRows4_le`

Per slot region (`2^20` rows, the last `2^15` for the link region: S-E12c's link rows and
S-E13a's pack rows), the rows of the slot's prototype as
**measured** (S-E12b, `logs/S-E12b/nodedump4-run.log`: the layout's last row `551,804` in both
prototypes' regions; unchanged at the S-E12c layouts, `logs/S-E12c/laydump4.log`) plus the
imports still unbound, at their **estimated** sizes (S-E12b RESULT §5 and 3.x's `mRowModel`):

* the previous-node slot: the replay `R` with the levers (S-E12b §4: ≈ 240 k), `rsWeight` with 4
  claims and its claim-2 kind factor (A.11, R-V-M1), `tplTargetSNode`, `tplLinkWAll`, `evalL`'s
  replay over the child's L rows, `shiftTarget`;
* a segment slot: `rsWeight`, `shiftTarget`, the segment's `targetS`/`shiftMask` (S-F4 §6; an
  allowance);
* per node: S-E13b's node rows (WOTS, `aggPad`) at slot 1, in its link region.

**`mRows4_le`**: each slot's rows fit one region below its link rows; every kind's M rows fit
`N_M / 1.05` (the kill rule at the kind's own M size, the orchestrator's ruling). (−) Without `R`'s
levers (S-E9's sized replay, ≈ 500 k) the previous-node slot does not fit one region.
-/

namespace FR
namespace Rev4

/-- The rows a prototype's region holds (measured: last row `551,804`). -/
def protoRowsN : ℕ := 551805

/-- **The previous-node slot's rows** (measured prototype + estimated imports). -/
def nodeSlotModel : List ℕ :=
  [protoRowsN,  -- the node mux prototype: skeleton, templates, walk DAG, phiRS split (measured)
   240000,      -- the replay R, two prototype structures, with the levers (S-E12b §4)
   45604,       -- rsWeight, 4 claims (A.11)
   68473,       -- rsWeight's claim-2 kind factor (R-V-M1)
   16000,       -- tplTargetSNode
   15000,       -- tplLinkWAll
   10000,       -- evalL's replay over the child's L rows
   1300]        -- shiftTarget

/-- **A segment slot's rows.** -/
def segSlotModel : List ℕ :=
  [protoRowsN,  -- the segment mux prototype (measured)
   45604,       -- rsWeight, 4 claims
   1300,        -- shiftTarget
   2000]        -- the segment's targetS and shiftMask (S-F4 §6; an allowance)

/-- **S-E13b's node rows** (both signed children's WOTS rows and the aggregates' `aggPad` rows, at
slot 1; `W4.xRows_length`): `N2` 7,992, `N4` 8,266, `N8` 8,680. -/
def wotsRows4 (κ : NodeKind) : ℕ := if κ = .N2 then 7992 else if κ = .N4 then 8266 else 8680

/-- **The pack rows** (S-E13a, `packRows4`): the kind tie and one trace's 8,905 pinned elements,
in two slots per kind (the previous node's and the first aggregate sub-slot, or `N8`'s two first
sub-slots). -/
def packRows4N : ℕ := 2 * 8906

/-- **The node's M rows** per kind: its slots, their link rows, the pack rows, WOTS. -/
def mRowModel4 (κ : NodeKind) : ℕ :=
  (if κ.hasPrev then nodeSlotModel.sum else 0) + κ.segSlots * segSlotModel.sum + κ.vslots * 8 + packRows4N +
    wotsRows4 κ

theorem slotModels_sum : nodeSlotModel.sum = 948182 ∧ segSlotModel.sum = 600709 := by
  norm_num [nodeSlotModel, segSlotModel, protoRowsN]

/-- **The M rows fit**: each slot's rows (and a segment slot's with WOTS in its slack) in its
region below the link region; every kind's rows in `N_M / 1.05`. -/
theorem mRows4_le :
    nodeSlotModel.sum + linkN ≤ slotM4 ∧ segSlotModel.sum + linkN ≤ slotM4 ∧
      ∀ κ : NodeKind, 105 * mRowModel4 κ ≤ 100 * κ.nM := by
  obtain ⟨h1, h2⟩ := slotModels_sum
  refine ⟨by rw [h1]; decide, by rw [h2]; decide, fun κ => ?_⟩
  cases κ <;> simp only [mRowModel4, h1, h2, NodeKind.hasPrev, NodeKind.segSlots, NodeKind.vslots,
    NodeKind.nM, NodeKind.dims, wotsRows4, packRows4N] <;> decide

/-- The per-kind totals: `N2` 2,175,428 of `2^22` (1.93×), `N4` 3,377,136 of `2^23` (2.48×), `N8`
4,832,228 of `2^23` (1.74×). -/
theorem mRowModel4_eq : mRowModel4 .N2 = 2175428 ∧ mRowModel4 .N4 = 3377136 ∧ mRowModel4 .N8 = 4832228 := by
  obtain ⟨h1, h2⟩ := slotModels_sum
  simp only [mRowModel4, h1, h2, NodeKind.hasPrev, NodeKind.segSlots, NodeKind.vslots, wotsRows4, packRows4N]
  decide

/-- (−) Not vacuous: with S-E9's sized replay (≈ 500 k rows) instead of `R`'s levers, the
previous-node slot does not fit one region (it would take two: `N2` 4 regions for 3 slots, `N4` 8
for 5). -/
theorem mRows4_neg : ¬ (nodeSlotModel.sum - 240000 + 500000 + linkN ≤ slotM4) := by
  rw [slotModels_sum.1]; decide

end Rev4
end FR
