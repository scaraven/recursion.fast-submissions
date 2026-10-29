-- New for `flock-recursive` (track REPF): controls of the replay fold's definitions.
import FRNodeRows4RepF
import FRNodeRows4RepFD

/-!
# Controls of the replay fold

| Definition | (+) | (−) |
|---|---|---|
| `repCellOk` | a frame cell of prototype 0, a local, a frame cell of prototype 1 | prototype 0's cell `2^20` (neither frame nor local), prototype 1's cell in region 0 |
| `repFitB` | the empty list; one row on frame cells | a row on a cell outside the frame; prototype 1 past `2^10` rows |
| `repRow0` / `repSegB` | `N4`'s slot 0 in the spare region 5, its slot 1 at `2^20 + repSegB`; `N8`'s slot 0 (a segment) at `repSegB` | `repSegB` is past the bits (`arRb + arNb`) and before the link region |
| `repAllRows` | `repFold`: every slot's `repIRows4 rtC1c` rows are rows of `nodeIRows4` | `repFit_of`: if the rows did not fit, the rejecting row would be a row of `nodeIRows4` |
| `linFr`, `linLoc` | `FRNodeRows4RepFD.linFr_ctl` | |
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval

theorem repCellOk_ctl : repCellOk 0 5 = true ∧ repCellOk 0 (N4s.repB + 3) = true ∧ repCellOk 1 (slotM4 + 2) = true ∧
    repCellOk 0 slotM4 = false ∧ repCellOk 1 3 = false := by
  simp only [repCellOk, N4s.repB, slotM4, inSB]; decide

theorem repFitB_ctl : repFitB 1 [] = true ∧ repFitB 0 [⟨[(3, 1)], [(N4s.repB, 2)], []⟩] = true ∧
    repFitB 0 [⟨[(slotM4 + 1, 1)], [], []⟩] = false := by
  simp only [repFitB, repCellOk, N4s.repB, slotM4, inSB]; decide

theorem repFitB_len {rows : List Row} (h : 2 ^ 10 < rows.length) : repFitB 1 rows = false := by
  rw [repFitB, if_neg one_ne_zero, Bool.and_eq_false_iff]
  exact Or.inl (decide_eq_false (by omega))

theorem repRow0_ctl : N4s.repRow0 .N4 0 = 5 * 2 ^ 20 ∧ N4s.repRow0 .N4 1 = 2 ^ 20 + N4s.repSegB ∧
    N4s.repRow0 .N8 0 = N4s.repSegB ∧ arRb + arNb < N4s.repSegB ∧ N4s.repSegB + 2 ^ 10 = slotM4 - linkN := by
  simp only [N4s.repRow0, protoOf, isPrevSlot, N4s.repSegB, slotM4, arRb, arNb, linkN]; decide

end Rev4
end FR
