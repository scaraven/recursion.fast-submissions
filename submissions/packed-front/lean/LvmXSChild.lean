-- New for lvm2 E2F (E2F-L, 2026-11-13): S2GF's child, read from the decoded window as M′'s (`childM20`), at S2GF's
-- stage (`stF20`: the child is an S2GF proof of `piSizeF P20F 44` bytes).
import LvmXSLayout
import LvmCertM20

/-!
# S2GF's child

`childF20 x w`: the left child of the stream block read from the window `w` at the statement's shape (`sIdx`, M′'s
layout of `C_main`), reassembled at S2GF's stage (`childWS stF20`). E2F-C states `nodeF20` against it.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.XS

/-- **S2GF's left child read from the stream window** (`childM20` at `stF20`). -/
def childF20 (x : List UInt8) (w : List BF64) : Signed :=
  childWS stF20 fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (w.getD (sIdx x i) 0) else BF64.toBitVec 0

end Lvm.CT
