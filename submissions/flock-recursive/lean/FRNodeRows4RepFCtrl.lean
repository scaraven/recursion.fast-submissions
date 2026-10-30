-- New for `flock-recursive` (track REPF): controls of the replay fold's definitions.
import FRNodeRows4RepF
import FRInitFuse

/-!
# Controls of the replay fold

| Definition | (+) | (−) |
|---|---|---|
| `repCellOk` | a frame cell of prototype 0, a local, a frame cell of prototype 1 | prototype 0's cell `2^20` (neither frame nor local), prototype 1's cell in region 0 |
| `repFitB` | the empty list; one row on frame cells; a segment local in its bands | a row on a cell outside the frame; prototype 1 past `segRN` rows; a segment local past `segCap` |
| `repRow0` / `repRowI` / `repSegB` | `N4`'s slot 0 in the spare region 5, its slot 1 at `2^20 + repSegB` (band B), its row `segBN` at `2^20 + repA` (band A); `N8`'s slot 0 (a segment) at `repSegB` | `repSegB` is the bits' end (`arRb + arNb`), band B ends at the link region, band A at `arR2` |
| `segCell` | a segment's locals `0`, `2^12`, `39,744` in bands 2, 1, 3 | — |
| `repAllRows` | `repFold`: every slot's `repIRows4 rtC1d` rows are rows of `nodeIRows4` | `repFit_of`: if the rows did not fit, the rejecting row would be a row of `nodeIRows4` |
| `linFr`, `linLoc` | `FRNodeRows4RepFD.linFr_ctl` | |
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval

theorem repCellOk_ctl : repCellOk 0 5 = true ∧ repCellOk 0 (N4s.repB + 3) = true ∧ repCellOk 1 (slotM4 + 2) = true ∧
    repCellOk 1 (N4s.repB + 52461) = true ∧ repCellOk 0 slotM4 = false ∧ repCellOk 1 3 = false ∧
    repCellOk 1 (N4s.repB + 52462) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [repCellOk, inSB] <;> decide

theorem repFitB_ctl : repFitB 1 [] = true ∧ repFitB 0 [⟨[(3, 1)], [(N4s.repB, 2)], []⟩] = true ∧
    repFitB 0 [⟨[(slotM4 + 1, 1)], [], []⟩] = false := by
  simp only [repFitB, repCellOk, N4s.repB, slotM4, inSB]; decide

theorem repFitB_len {rows : List Row} (h : N4s.segRN < rows.length) : repFitB 1 rows = false := by
  rw [repFitB, if_neg one_ne_zero, Bool.and_eq_false_iff]
  exact Or.inl (decide_eq_false (by omega))

theorem repRow0_ctl : N4s.repRow0 .N4 0 = 5 * 2 ^ 20 ∧ N4s.repRowI .N4 1 0 = 2 ^ 20 + N4s.repSegB ∧
    N4s.repRowI .N4 1 N4s.segBN = 2 ^ 20 + N4s.repA ∧ N4s.repRowI .N8 0 0 = N4s.repSegB ∧
    arRb + arNb = N4s.repSegB ∧ N4s.repSegB + N4s.segBN = slotM4 - linkN ∧ N4s.repA + 2 ^ 15 = arR2 := by
  simp only [N4s.repRow0, N4s.repRowI, N4s.segRow, protoOf, isPrevSlot, N4s.repSegB, N4s.segBN, N4s.repA, slotM4,
    arRb, arNb, linkN, arR2]; decide

/-- (+) A segment slot's locals `0`, `2^12`, `39,744` are the first cells of bands 2, 1, 3; (−) none lands in
the skeleton or arena₁/the bits (`[277,402, 290,816)`, `[405,504, 441,152)` and `[1,003,010, 1,015,728)` only). -/
theorem segCell_ctl : N4s.segCell 0 = 277402 ∧ N4s.segCell (2 ^ 12) = 405504 ∧ N4s.segCell 39744 = 1003010 ∧
    N4s.segCell (2 ^ 12 - 1) < arA1 ∧ arBt + arNb ≤ N4s.segCell (2 ^ 12) ∧ N4s.segCell 52461 = 1015727 := by
  simp only [N4s.segCell, arA1, arBt, arNb]; decide

end Rev4
end FR
