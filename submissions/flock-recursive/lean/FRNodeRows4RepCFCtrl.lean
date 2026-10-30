-- New for `flock-recursive` (track CF2): controls for the plan's structural fit and the automaton.
import FRNodeRows4RepCFW
import FRVIRTplRepLG

/-!
# Controls (CF2)

| Definition | (+) | (−) |
|---|---|---|
| `linCellOk`, `cb_cellOk` | a frame cell; the last local in the room | a cell between the frame and `repB`; the first local past the room |
| `kpFit`, `repFitS` | a row block / failed op whose cells fit | the same with one cell past the frame |
| `GS` | two bits' sum at `A = B = 0` (both `j`) | `A = 1`: the second index leaves the bits |
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

theorem linCellOk_ctl : linCellOk [(5, 1)] = true ∧ linCellOk [(2 ^ 20 + 3, 1)] = false := by
  constructor <;> decide

theorem cb_cellOk_ctl : repCellOk 0 (N4s.cbRS + (lRoom - 1)) = true ∧ repCellOk 0 (N4s.cbRS + lRoom) = false := by
  unfold N4s.cbRS N4s.repB lRoom; constructor <;> decide

theorem kpFit_ctl :
    kpFit ⟨false, [⟨[(5, 1)], [], []⟩], [], [], [], [], [], []⟩ = true ∧
      kpFit ⟨false, [⟨[(2 ^ 20 + 3, 1)], [], []⟩], [], [], [], [], [], []⟩ = false := by
  constructor <;> decide

theorem repFitS_ctl :
    repFitS ([(⟨[(5, 1)], [], []⟩, 0)], []) = true ∧ repFitS ([(⟨[(2 ^ 20 + 3, 1)], [], []⟩, 0)], []) = false := by
  unfold repFitS; constructor <;> decide

theorem GS_ctl (fa fb : ℕ → Bool → F) :
    GS fa fb 1 2 0 0 = fa 0 false * fb 0 false + fa 0 true * fb 0 true ∧
      GS fa fb 1 2 1 0 = fa 0 true * fb 0 false := by
  constructor <;> simp [GS, shF]

end Rev4
end FR
