-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4, A.11's row model per kind; stage S-E12c,
-- track L-circ; re-based by B0 on PACK-4.4.1 §6.1). 3.x's analogue: `FRNodeLayout.mRowModel`.
import FRNodeRows4

/-!
# The 4.x nodes' M row model (`mRowModel4`) and `mRows4_le`

PACK-4.4.1 §6.1's budget per `2^20`-row slot region, with the two prototypes **as measured** after
B0's levers (`logs/B0/nodedump4-B4.log`: the last row of prototype 0's region `630,015`, of
prototype 1's `618,495`) and the rest at the memo's sizes:

* a slot's own region: its prototype, the pack map's rows in the region (PACK-4.4.1 §5.2: the two
  arenas, the FS links, pins, bit rows, the cap bits' kind mux, the sibling rows, `input`/`stmt`),
  the cap-check templates (§3.3) and the reserved link region (`linkN`); a segment slot also holds
  its `R` without `evalM` (S-E14: the segment's `evalM`/`evalL` are dropped by C2);
* the previous-node slot has a second, spare region (N2: region 3, N4: region 5) for `R` without
  `evalM` and the `evalM` replay (§6.2, the upper ends).

**`mRows4_le`**: every region fits `2^20` rows, and every kind's regions fit `N_M / 1.05` (the kill
rule at the kind's own M size). (−) `mRows4_neg`: with the prototypes as they were before B0
(`730,493` / `725,885` rows) the segment region does not fit `2^20` and `N8` does not fit `N_M / 1.05`.
This is a model (sizes, not a statement of the soundness chain): the rows' fit as compiled is
`ProtoFit`, checked at process start.
-/

namespace FR
namespace Rev4

/-- The rows prototype 0's region holds (measured after B0: last row `630,015`). -/
def protoRowsN : ℕ := 630016

/-- The rows prototype 1's region holds (measured after B0: last row `618,495`). -/
def protoRowsS : ℕ := 618496

/-- The pack map's rows in a slot's own region (PACK-4.4.1 §6.1): arena₁ 96,524 + arena₂ 85,946 +
FS links 934 + pins 8,907 + bit rows 8,320 + 372 + cap-bit kind mux 7,839 + sibling rows 3,484 +
`input`/`stmt` 18. -/
def packMapN : ℕ := 212344

/-- The cap-check templates (PACK-4.4.1 §3.3). -/
def capChkN : ℕ := 40000

/-- **The previous-node slot's own region**: prototype, pack map, cap check, link region. -/
def nodeRegion : List ℕ := [protoRowsN, packMapN, capChkN, linkN]

/-- **A segment slot's region**: prototype, pack map, cap check, link region, and its `R` without
`evalM` (S-E14: 49,000). -/
def segRegion : List ℕ := [protoRowsS, packMapN, capChkN, linkN, 49000]

/-- **The previous-node slot's spare region**: `R` without `evalM` (221,000) and the `evalM` replay
at its upper estimate (400,000; PACK-4.4.1 §6.2). -/
def spareRegion : List ℕ := [221000, 400000]

/-- **The node's M rows** per kind: the previous-node slot's two regions, then the segment slots'. -/
def mRowModel4 (κ : NodeKind) : ℕ :=
  (if κ.hasPrev then nodeRegion.sum + spareRegion.sum else 0) + κ.segSlots * segRegion.sum

theorem regions_sum : nodeRegion.sum = 915128 ∧ segRegion.sum = 952608 ∧ spareRegion.sum = 621000 := by
  norm_num [nodeRegion, segRegion, spareRegion, protoRowsN, protoRowsS, packMapN, capChkN, linkN]

/-- **The M rows fit**: each region in `2^20` rows; every kind's rows in `N_M / 1.05`. -/
theorem mRows4_le :
    nodeRegion.sum ≤ slotM4 ∧ segRegion.sum ≤ slotM4 ∧ spareRegion.sum ≤ slotM4 ∧
      ∀ κ : NodeKind, 105 * mRowModel4 κ ≤ 100 * κ.nM := by
  obtain ⟨h1, h2, h3⟩ := regions_sum
  refine ⟨by rw [h1]; decide, by rw [h2]; decide, by rw [h3]; decide, fun κ => ?_⟩
  cases κ <;> simp only [mRowModel4, h1, h2, h3, NodeKind.hasPrev, NodeKind.segSlots, NodeKind.nM,
    NodeKind.dims] <;> decide

/-- The per-kind totals: `N2` 3,441,344 of `2^22` (1.22×; 1.16× under `N_M / 1.05`), `N4` 5,346,560
of `2^23` (1.57×; 1.49×), `N8` 7,620,864 of `2^23` (1.10×; 1.048× under `N_M / 1.05` = 7,989,150). -/
theorem mRowModel4_eq : mRowModel4 .N2 = 3441344 ∧ mRowModel4 .N4 = 5346560 ∧ mRowModel4 .N8 = 7620864 := by
  obtain ⟨h1, h2, h3⟩ := regions_sum
  simp only [mRowModel4, h1, h2, h3, NodeKind.hasPrev, NodeKind.segSlots]
  decide

/-- (−) Not vacuous: with the prototypes as before B0 (730,493 / 725,885 rows), a segment region
holds 1,059,997 rows (> `2^20`) and `N8`'s eight hold 8,479,976 (> `N_M / 1.05`). -/
theorem mRows4_neg :
    ¬ (segRegion.sum - protoRowsS + 725885 ≤ slotM4) ∧
      ¬ (105 * (8 * (segRegion.sum - protoRowsS + 725885)) ≤ 100 * NodeKind.N8.nM) := by
  rw [regions_sum.2.1]
  simp only [protoRowsS, NodeKind.nM, NodeKind.dims]
  decide

end Rev4
end FR
