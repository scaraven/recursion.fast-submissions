-- New for lvm6 Y1 (2026-11-22): the typed phases at `E = GF(2^128)` with the mini-bus at `E`, proved: BLUEPRINT §5
-- T4 (`typedSpecE`), from `typedSpecE_of_mini` (Lvm6TySpecP) and `miniSpecL6` (Lvm6MbMid).
import Lvm6TySpecP
import Lvm6MbMid

/-!
# `typedSpecE`

The frozen statement `TypedSpecEStmt` (Lvm6TyProg), with the mini-bus's frozen statement `MiniSpecL6Stmt`
(Lvm6MbProg) discharged by `Lvm6.Mb.miniSpecL6`.
-/

set_option autoImplicit false

namespace Lvm6.Ty

/-- **T4: the typed phases at `E2`** (zerocheck, wiring, relayout, A23 at `Φ_Q` in 43 variables, the mini-bus). -/
theorem typedSpecE : TypedSpecEStmt := typedSpecE_of_mini Lvm6.Mb.miniSpecL6

end Lvm6.Ty
