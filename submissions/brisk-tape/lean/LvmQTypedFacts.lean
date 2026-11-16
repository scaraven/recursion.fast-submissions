-- New for lvm2 (roll 8 = B1, B1-IX): the B program's static facts the kernel decides (the rest are the typed guard's,
-- `LvmQTypedInst.staticOkTOf`): the mini-bus's read blocks are the cap regions' (`capBlocksOk`, for L-D's balance of
-- the mini-bus), the typed phases end where the schedule's tape phase starts (B1-Q's assumption 7, B1-V's INT item 7),
-- and the accumulator's variables are `Φ_Q`'s.
import LvmQTypedInst
import LvmQTypedInst8

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.QAsm

set_option maxRecDepth 200000 in
/-- **The mini-bus's read blocks are the cap regions' at `P20`** (`capBlocksOk`, B1-Q: with `capRead_seeded` and
`mbBlocks_disjoint`, every cap read targets a seeded cell, each seeded once). Kernel-decided. -/
theorem capBlocksOk_P20 : capBlocksOk cfg20 = true := by decide +kernel

set_option maxRecDepth 200000 in
/-- **The typed phases end where the tape starts** at `P20` (B1-Q's assumption 7): the circuit's `typedEnd` from
`typedPos` (the bus phase's old start) is the schedule's tape entry plus the mini-bus's `tableEvals` pending
scalars, so phases 4–7 (`phases47`) read the child's stream at the schedule's positions. Kernel-decided. -/
theorem typedEnd_P20 : typedEnd tdata20 (typedPos P20) = phaseByte P20 .tape + 24 * P20.tableEvals := by
  decide +kernel

/-- `arithPos`'s first position is the tape entry plus the table phase's `tableEvals` pending scalars. -/
theorem arithPos_head (p : Params) : (Lvm.Har.arithPos p).getD 0 0 = Lvm.Har.phaseByte p .tape + 24 * p.tableEvals :=
  rfl

/-- `Q_arith`'s two copies of `phaseByte` agree. -/
theorem phaseByte_har (p : Params) (ph : Phase) : Lvm.Har.phaseByte p ph = phaseByte p ph := rfl

/-- **Phases 4–7 read from the typed phases' end** at `P20`: `arithPos`'s first position (the tape's `r`, `aLane 0`)
is `typedEnd` (B1-IX, the S,1 node-step replay: `arithPos` had the bus path's `+ 24`, A23's one pending scalar, so the
tape gadget read 2,805 lanes early and its GKR, the wire's input and the final claim failed). -/
theorem tapeStart_P20 : (Lvm.Har.arithPos P20).getD 0 0 = typedEnd tdata20 (typedPos P20) := by
  rw [arithPos_head, phaseByte_har, typedEnd_P20]

set_option maxRecDepth 200000 in
/-- **The typed phases end where the tape starts** at `P8` (as `typedEnd_P20`). Kernel-decided. -/
theorem typedEnd_P8 : typedEnd tdata8 (typedPos P8) = phaseByte P8 .tape + 24 * P8.tableEvals := by
  decide +kernel

/-- **Phases 4–7 read from the typed phases' end** at `P8` (as `tapeStart_P20`). -/
theorem tapeStart_P8 : (Lvm.Har.arithPos P8).getD 0 0 = typedEnd tdata8 (typedPos P8) := by
  rw [arithPos_head, phaseByte_har, typedEnd_P8]

/-- `acc_in` has `Φ_Q`'s 43 coordinates (B1-V's `dAccT`, B1-Q's `qaccT`). -/
theorem accVars_phiVars : accVars = TypedV.phiVarsN := rfl

end Lvm.QTyped
