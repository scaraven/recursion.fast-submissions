-- New for lvm2 E2F (E2F-L, 2026-11-13): S2GF's child, read from the decoded window as M′'s (`childM20`), at S2GF's
-- stage (`stF20`: the child is an S2GF proof of `piSizeF P20F 44` bytes).
import LvmXSLayout
import LvmCertM20

-- (GOLF2: 1 declarations that `certified` does not use moved verbatim to `LvmXSChildOff`, outside its import closure.)

/-!
# S2GF's child

`childF20 x w`: the left child of the stream block read from the window `w` at the statement's shape (`sIdx`, M′'s
layout of `C_main`), reassembled at S2GF's stage (`childWS stF20`). E2F-C states `nodeF20` against it.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.XS

end Lvm.CT
