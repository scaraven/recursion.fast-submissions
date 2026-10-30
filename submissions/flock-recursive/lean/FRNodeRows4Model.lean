-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4, A.11's row model per kind; stage S-E12c,
-- track L-circ; re-based by B0 on PACK-4.4.1 §6.1, by B2′ and B2″ on their measured prototypes; CK: prototype 0's rows). 3.x's analogue: `FRNodeLayout.mRowModel`.
import FRNodeRows4
import FRNodeRows4ArenaPlace

/-!
# The 4.x nodes' M row model (`mRowModel4`) and `mRows4_le`

PACK-4.4.1 §6.1's budget per `2^20`-row slot region, re-based by B2″ on the prototypes **as measured**
at RSV-V's programs with B2″'s packed cells (`logs/B2pp/nodedump4-run.log`: the last row of prototype
1's region `686,079`; the packing moves cells, not rows; the prototypes contain the cap check), prototype
0 re-measured by CK (`logs/CK/arenafit.log`: last row `706,303`, `finPf`'s `getK` of the kind-muxed `P₀`
and the 4,392 registers after it now in the rows) and the rest at the memo's sizes (arena₁ at RSV-V's stream):

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
compiled is `ProtoFit`, checked at process start. **Cells** are not modelled here: the arenas'
placement is `FRNodeRows4ArenaPlace` (B2″), checked on the dump (`logs/B2pp/arenafit.log`).
-/

namespace FR
namespace Rev4

/-- The rows prototype 0's region holds (measured by CK: last row `706,303`; B2″: `700,159`). -/
def protoRowsN : ℕ := 706304

/-- The rows prototype 1's region holds (measured by B2″: last row `686,079`). -/
def protoRowsS : ℕ := 686080

/-- The pack map's rows in a slot's own region (PACK-4.4.1 §6.1 at today's stream): arena₁ 96,944
(`64·24,236 / 16` elements, `arN`) + the binding 85,946 (B2″: arena₂'s rows, now into the consumers'
import cells) + FS links 934 + pins 8,783 + bit rows 8,320 + 372 + cap-bit kind mux 7,839 + sibling
rows 3,484 + `input`/`stmt` 18 (`packMapN_arN`: arena₁ is `FRNodeRows4ArenaPlace.arN`, from the
format; a literal here, so that the model's theorems do not make the kernel evaluate the format). -/
def packMapN : ℕ := 212640

/-- The pack map's arena₁ is the placed arena₁ (`arN = 4·chainLenOf seq4`): a format change fails here
first. -/
theorem packMapN_arN : packMapN = arN + 115696 := by rw [arN_eq]; rfl

/-- **The previous-node slot's own region**: prototype (with its cap check), pack map, link region. -/
def nodeRegion : List ℕ := [protoRowsN, packMapN, linkN]

/-- **A segment slot's region**: prototype, pack map, link region, and its `R` without `evalM`
(S-E14: 49,000; SEG-R2: measured, `repRowsP (rtC1d 1) 1` = 38,805 rows, `logs/SEGR2/segstat-stat.log`). -/
def segRegion : List ℕ := [protoRowsS, packMapN, linkN, 38805]

/-- **The previous-node slot's spare region**: `R` without `evalM` (221,000) and the `evalM` replay
at its upper estimate (400,000; PACK-4.4.1 §6.2). -/
def spareRegion : List ℕ := [221000, 400000]

/-- **The node's M rows** per kind: the previous-node slot's two regions, then the segment slots'. -/
def mRowModel4 (κ : NodeKind) : ℕ :=
  (if κ.hasPrev then nodeRegion.sum + spareRegion.sum else 0) + κ.segSlots * segRegion.sum

theorem regions_sum : nodeRegion.sum = 951712 ∧ segRegion.sum = 970293 ∧ spareRegion.sum = 621000 := by
  norm_num [nodeRegion, segRegion, spareRegion, protoRowsN, protoRowsS, packMapN, linkN]

/-- **The M rows fit**: each region in `2^20` rows; every kind's rows in `N_M / 1.05`. -/
theorem mRows4_le :
    nodeRegion.sum ≤ slotM4 ∧ segRegion.sum ≤ slotM4 ∧ spareRegion.sum ≤ slotM4 ∧
      ∀ κ : NodeKind, 105 * mRowModel4 κ ≤ 100 * κ.nM := by
  obtain ⟨h1, h2, h3⟩ := regions_sum
  refine ⟨by rw [h1]; decide, by rw [h2]; decide, by rw [h3]; decide, fun κ => ?_⟩
  cases κ <;> simp only [mRowModel4, h1, h2, h3, NodeKind.hasPrev, NodeKind.segSlots, NodeKind.nM,
    NodeKind.dims] <;> decide

/-- The per-kind totals (SEG-R2: the segment's measured `R`): `N2` 3,513,298 of `2^22`, `N4` 5,453,884 of
`2^23`, `N8` 7,762,344 of `2^23` (**fits, 1.029× under `N_M / 1.05` = 7,989,150**; the margin is 226,806 rows,
so `N8` would stop fitting only if each of its 8 segment regions grew by more than 28,350 rows). -/
theorem mRowModel4_eq : mRowModel4 .N2 = 3513298 ∧ mRowModel4 .N4 = 5453884 ∧ mRowModel4 .N8 = 7762344 := by
  obtain ⟨h1, h2, h3⟩ := regions_sum
  simp only [mRowModel4, h1, h2, h3, NodeKind.hasPrev, NodeKind.segSlots]
  decide

/-- (−) Not vacuous: with the segment prototype as A2″ compiled it (791,421 rows), a segment region
holds 1,085,829 rows (> `2^20`) and `N8`'s eight hold 8,686,632 (> `N_M / 1.05`). -/
theorem mRows4_neg :
    ¬ (segRegion.sum - protoRowsS + 791421 ≤ slotM4) ∧
      ¬ (105 * (8 * (segRegion.sum - protoRowsS + 791421)) ≤ 100 * NodeKind.N8.nM) := by
  rw [regions_sum.2.1]
  simp only [protoRowsS, NodeKind.nM, NodeKind.dims]
  decide

end Rev4
end FR
