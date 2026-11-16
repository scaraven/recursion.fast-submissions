-- Moved out of `LvmVerifierS` (lvm2 roll 8, wave L, L-W; a pure move): the typed `V_S`, so that the bus `V_S`'s
-- consumers (`LvmReplay`, `LvmCertSQ`, …) do not import `LvmTypedV` (a shorter build critical path).
import LvmVerifierS
import LvmTypedV

-- (GOLF2: 2 declarations that `certified` does not use moved verbatim to `LvmVerifierSTOff`, outside its import closure.)

/-!
# The typed `V_S`

**`VST p N`** (lvm2 roll 8, B1: B-DES §1.2): parse, then drive the schedule and decide with `TypedV.decideFT` on the
native typed instance `N`; **`VST_reject`**: a rejected header asks no query.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

end Lvm
