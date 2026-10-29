-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4, A.11's row model per kind; stage S-E12c,
-- track L-circ; re-based by B0 on PACK-4.4.1 §6.1, by B2′ on its measured prototypes). 3.x's analogue: `FRNodeLayout.mRowModel`.
import FRNodeRows4

/-!
# The 4.x nodes' M row model (`mRowModel4`) and `mRows4_le`

PACK-4.4.1 §6.1's budget per `2^20`-row slot region, re-based by B2′ on the prototypes **as measured**
with the cap check compiled as keyed blocks (`logs/B2p/nodedump4-run.log`: the last row of prototype
0's region `699,647`, of prototype 1's `686,079`; the prototypes now contain the cap check, so §11.7's
separate 52,400-row line is gone) and the rest at the memo's sizes:

* a slot's own region: its prototype, the pack map's rows in the region (PACK-4.4.1 §5.2 at today's
  stream: the two arenas, the FS links, pins, bit rows, the cap bits' kind mux, the sibling rows,
  `input`/`stmt`) and the reserved link region (`linkN`); a segment slot also holds its `R` without
  `evalM` (S-E14: the segment's `evalM`/`evalL` are dropped by C2);
* the previous-node slot has a second, spare region (N2: region 3, N4: region 5) for `R` without
  `evalM` and the `evalM` replay (§6.2, the upper ends).

**`mRows4_le`**: every region fits `2^20` rows, and every kind's regions fit `N_M / 1.05` (the kill
rule at the kind's own M size). (−) `mRows4_neg`: with the segment prototype as A2″ compiled it
(the cap check as sparse skeleton rows, before B0's policies reached it: `791,421` rows,
`logs/A2pp/nodedump4-run.log`) the segment region does not fit `2^20` and `N8` does not fit
`N_M / 1.05`. This is a model (sizes, not a statement of the soundness chain): the rows' fit as
compiled is `ProtoFit`, checked at process start. **Cells** are not modelled here; a slot region's
cells are at `≈ 99 %` (B2′'s RESULT), which the arenas' placement must solve.
-/

namespace FR
namespace Rev4

/-- The rows prototype 0's region holds (measured by B2′: last row `699,647`). -/
def protoRowsN : ℕ := 699648

/-- The rows prototype 1's region holds (measured by B2′: last row `686,079`). -/
def protoRowsS : ℕ := 686080

/-- The pack map's rows in a slot's own region (PACK-4.4.1 §6.1 at today's stream): arena₁ 96,880
(`64·24,220 / 16` elements) + arena₂ 85,946 + FS links 934 + pins 8,783 + bit rows 8,320 + 372 +
cap-bit kind mux 7,839 + sibling rows 3,484 + `input`/`stmt` 18. -/
def packMapN : ℕ := 212576

/-- **The previous-node slot's own region**: prototype (with its cap check), pack map, link region. -/
def nodeRegion : List ℕ := [protoRowsN, packMapN, linkN]

/-- **A segment slot's region**: prototype, pack map, link region, and its `R` without `evalM`
(S-E14: 49,000). -/
def segRegion : List ℕ := [protoRowsS, packMapN, linkN, 49000]

/-- **The previous-node slot's spare region**: `R` without `evalM` (221,000) and the `evalM` replay
at its upper estimate (400,000; PACK-4.4.1 §6.2). -/
def spareRegion : List ℕ := [221000, 400000]

/-- **The node's M rows** per kind: the previous-node slot's two regions, then the segment slots'. -/
def mRowModel4 (κ : NodeKind) : ℕ :=
  (if κ.hasPrev then nodeRegion.sum + spareRegion.sum else 0) + κ.segSlots * segRegion.sum

theorem regions_sum : nodeRegion.sum = 944992 ∧ segRegion.sum = 980424 ∧ spareRegion.sum = 621000 := by
  norm_num [nodeRegion, segRegion, spareRegion, protoRowsN, protoRowsS, packMapN, linkN]

/-- **The M rows fit**: each region in `2^20` rows; every kind's rows in `N_M / 1.05`. -/
theorem mRows4_le :
    nodeRegion.sum ≤ slotM4 ∧ segRegion.sum ≤ slotM4 ∧ spareRegion.sum ≤ slotM4 ∧
      ∀ κ : NodeKind, 105 * mRowModel4 κ ≤ 100 * κ.nM := by
  obtain ⟨h1, h2, h3⟩ := regions_sum
  refine ⟨by rw [h1]; decide, by rw [h2]; decide, by rw [h3]; decide, fun κ => ?_⟩
  cases κ <;> simp only [mRowModel4, h1, h2, h3, NodeKind.hasPrev, NodeKind.segSlots, NodeKind.nM,
    NodeKind.dims] <;> decide

/-- The per-kind totals: `N2` 3,526,840 of `2^22` (1.19×; 1.13× under `N_M / 1.05`), `N4` 5,487,688
of `2^23` (1.53×; 1.46×), `N8` 7,843,392 of `2^23` (1.07×; **1.019× under `N_M / 1.05` = 7,989,150**:
18,220 more rows in each segment region and `N8` no longer fits). -/
theorem mRowModel4_eq : mRowModel4 .N2 = 3526840 ∧ mRowModel4 .N4 = 5487688 ∧ mRowModel4 .N8 = 7843392 := by
  obtain ⟨h1, h2, h3⟩ := regions_sum
  simp only [mRowModel4, h1, h2, h3, NodeKind.hasPrev, NodeKind.segSlots]
  decide

/-- (−) Not vacuous: with the segment prototype as A2″ compiled it (791,421 rows), a segment region
holds 1,085,765 rows (> `2^20`) and `N8`'s eight hold 8,686,120 (> `N_M / 1.05`). -/
theorem mRows4_neg :
    ¬ (segRegion.sum - protoRowsS + 791421 ≤ slotM4) ∧
      ¬ (105 * (8 * (segRegion.sum - protoRowsS + 791421)) ≤ 100 * NodeKind.N8.nM) := by
  rw [regions_sum.2.1]
  simp only [protoRowsS, NodeKind.nM, NodeKind.dims]
  decide

end Rev4
end FR
