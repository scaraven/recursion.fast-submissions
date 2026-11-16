-- New for lvm2 (CR-Q, roll 7 SH2-Z): glue between Q_arith's cells and `V_S`'s roll-7 phases: the ring
-- coefficients `dWireC` also returns are the wire gadget's coefficient cells (`dWireC_snd`, from T-W's
-- `wire_spec` reading and `wire_core`), and the tails' closed forms agree (`tailD`/`tailDF`, `tailR`/`ringTailN`).
import LvmQWireSound
import LvmQAsmHarTop
import LvmQShapeB
import LvmShapeVT

-- (GOLF2: 8 declarations that `certified` does not use moved verbatim to `LvmQTypedHarCOff`, outside its import closure.)

set_option autoImplicit false

namespace Lvm.Q1

open Lvm DM Lvm.VEq Lvm.VEq.Wr Lvm.Loop Lvm.Loop.Build Lvm.Har

end Lvm.Q1

namespace Lvm.Har

open Lvm DM

end Lvm.Har

namespace Lvm.QShape

open Lvm Lvm.Shape Lvm.Har

end Lvm.QShape
