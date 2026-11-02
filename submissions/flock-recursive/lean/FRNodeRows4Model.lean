-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4, A.11's row model per kind; stage S-E12c,
-- track L-circ; re-based by B0 on PACK-4.4.1 §6.1, by B2′ and B2″ on their measured prototypes; CK: prototype 0's rows;
-- flock-128 I6: both prototypes, the pack map and the segment's `R` re-measured, `logs/I6/nodedump4-run.log`, `nodedumpx-run.log`). 3.x's analogue: `FRNodeLayout.mRowModel`.
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

/-- The rows prototype 0's region holds (measured by I6 at `flock-128`: last row `708,351`, the PoW's
1,232 gated rows and the skeleton-computed initial claims; CK: `706,303`). -/
def protoRowsN : ℕ := 708352

/-- The rows prototype 1's region holds (measured by I6 at `flock-128`: last row `688,127`; B2″: `686,079`). -/
def protoRowsS : ℕ := 688128

/-- The pack map's rows in a slot's own region (PACK-4.4.1 §6.1 at the `flock-128` stream): arena₁ 97,096
(`64·24,274 / 16` elements, `arN`) + the binding 85,946 (B2″: arena₂'s rows, now into the consumers'
import cells) + FS links 958 (498 FS items) + pins 8,795 + bit rows 8,320 + 372 + cap-bit kind mux 7,839 +
sibling rows 3,484 + `input`/`stmt` 18 + (I6b) the proof of work's trace rows 1,232 and bit ties 1,232, less the
closure's former failing row 1 (`packMapN_arN`: arena₁ is `FRNodeRows4ArenaPlace.arN`, from the
format; a literal here, so that the model's theorems do not make the kernel evaluate the format). -/
def packMapN : ℕ := 215291

/-- The pack map's arena₁ is the placed arena₁ (`arN = 4·chainLenOf seq4`): a format change fails here
first. -/
theorem packMapN_arN : packMapN = arN + 118195 := by rw [arN_eq]; rfl

/-- **The previous-node slot's own region**: prototype (with its cap check), pack map, link region. -/
def nodeRegion : List ℕ := [protoRowsN, packMapN, linkN]

/-- **A segment slot's region**: prototype, pack map, link region, and its `R` without `evalM`
(S-E14: 49,000; SEG-R2: 38,805; measured by I6 at `flock-128`, `repRowsP (rtC1d 1) 1` = 40,111 rows,
`logs/I6/nodedumpx-run.log`). -/
def segRegion : List ℕ := [protoRowsS, packMapN, linkN, 40111]

/-- **The previous-node slot's spare region**: `R` without `evalM` (221,000) and the `evalM` replay
at its upper estimate (400,000; PACK-4.4.1 §6.2). -/
def spareRegion : List ℕ := [221000, 400000]

/-- **The node's M rows** per kind: the previous-node slot's two regions, then the segment slots'. -/
def mRowModel4 (κ : NodeKind) : ℕ :=
  (if κ.hasPrev then nodeRegion.sum + spareRegion.sum else 0) + κ.segSlots * segRegion.sum

theorem regions_sum : nodeRegion.sum = 956411 ∧ segRegion.sum = 976298 ∧ spareRegion.sum = 621000 := by
  norm_num [nodeRegion, segRegion, spareRegion, protoRowsN, protoRowsS, packMapN, linkN]

/-- **The M rows fit**: each region in `2^20` rows; every kind's rows in `N_M / 1.05`. -/
theorem mRows4_le :
    nodeRegion.sum ≤ slotM4 ∧ segRegion.sum ≤ slotM4 ∧ spareRegion.sum ≤ slotM4 ∧
      ∀ κ : NodeKind, 105 * mRowModel4 κ ≤ 100 * κ.nM := by
  obtain ⟨h1, h2, h3⟩ := regions_sum
  refine ⟨by rw [h1]; decide, by rw [h2]; decide, by rw [h3]; decide, fun κ => ?_⟩
  cases κ <;> simp only [mRowModel4, h1, h2, h3, NodeKind.hasPrev, NodeKind.segSlots, NodeKind.nM,
    NodeKind.dims] <;> decide

/-- The per-kind totals (I6 at `flock-128`: the prototypes, the pack map and the segment's `R` re-measured;
I6b: the proof of work's trace rows and ties, `+2,463` per region): `N2` 3,530,007 of `2^22`, `N4` 5,482,603
of `2^23`, `N8` 7,810,384 of `2^23` (**fits, 1.023× under `N_M / 1.05` = 7,989,150**; the margin is 178,766
rows, so `N8` would stop fitting only if each of its 8 segment regions grew by more than 22,345 rows; I6's
margin was 198,470, SEG-R2's 226,806). -/
theorem mRowModel4_eq : mRowModel4 .N2 = 3530007 ∧ mRowModel4 .N4 = 5482603 ∧ mRowModel4 .N8 = 7810384 := by
  obtain ⟨h1, h2, h3⟩ := regions_sum
  simp only [mRowModel4, h1, h2, h3, NodeKind.hasPrev, NodeKind.segSlots]
  decide

/-- (−) Not vacuous: with the segment prototype as A2″ compiled it (791,421 rows), a segment region
holds 1,079,591 rows (> `2^20`) and `N8`'s eight hold 8,636,728 (> `N_M / 1.05`). -/
theorem mRows4_neg :
    ¬ (segRegion.sum - protoRowsS + 791421 ≤ slotM4) ∧
      ¬ (105 * (8 * (segRegion.sum - protoRowsS + 791421)) ≤ 100 * NodeKind.N8.nM) := by
  rw [regions_sum.2.1]
  simp only [protoRowsS, NodeKind.nM, NodeKind.dims]
  decide

end Rev4
end FR
