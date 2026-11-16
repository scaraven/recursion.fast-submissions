-- New for lvm2 E2F (E2F-L, 2026-11-13): the node output generic in the stage (`outIR` of `LvmXNodeIR` with the
-- stage's trace blocks, entry count and `|π|`). Definitions; the facts go to `LvmXSOut*`.
import LvmXSLayout
import LvmXTop

/-!
# The node output at a stage

`pSegS`, `trSegS`: the proof's and the trace's segments over `blocksS st`; **`outIRS st mB`**: `outIR mB` with them
and `|π| = st.pz`.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-! ## The node output -/

/-- **The proof's segment**: `'S' ‖ 0⁷`, then the blocks' contributions. -/
def pSegS (st : XStage) : Seg := .cat (.wd (toWord 0x53)) (blkPSegs 6 (blocksS st))

/-- **The trace's segment**: the count, `q₀`'s entry, the blocks from lane 6. -/
def trSegS (st : XStage) : Seg :=
  .cat (.wd (toWord (qSS st))) (.cat (.wd (toWord 7)) (.cat (.sh8 1) (.cat (.cp 2 4) (blkTSegs 6 (blocksS st)))))

/-- **The node output at a stage** (`outIR`). -/
def outIRS (st : XStage) (mB : ℕ) : XIR :=
  .seq (emitIR (toWord 1)) (.seq (tcpIR 11 4) (.seq (leafStmtIR 20 19)
  (.seq (emitIR (toWord st.pz)) (.seq (copyIR mB)
  (.seq (setR sgB) (.seq (segIR apC 0 (pSegS st)) (.seq (segIR apC 0 (trSegS st))
  (.seq (setR (sigB mB)) (.seq (segIR apC 0 (.cp 0 597))
  (.seq (emitIR (toWord 48)) (.seq (emitIR (toWord 0)) (.seq (tcpIR 15 5)
  (.seq (emitIR (toWord 0)) (tcpIR 24 597))))))))))))))

end Lvm.XS
