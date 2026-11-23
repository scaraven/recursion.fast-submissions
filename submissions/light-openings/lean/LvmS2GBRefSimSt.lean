-- New for lvm2 MP-B cap pruning (CAP-VS, 2026-11-17): S2GB's schedule meets the static check `stAB` (one kernel
-- evaluation over the items). Proof help for `refinesB_of`.
import LvmS2GBRefSimDrive

/-!
# S2GB's schedule meets the static check

`stAB_P20B`: every Fiat–Shamir query of `schedule P20B` is within `queryCap`, nothing is pending at an opening or
at the end, the caps come in `idxS` order (each oracle once) and send `2^capOfB` nodes, every opening's level
geometry is the commitment table's (`geomOkB`: the cap layer `capS`, the sent cap `capOfB`), its `t` positions of
the commitment's height.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm

/-- **The static check at S2GB** [decide] (`stIB` over the items, `stAB_atomsOf`). -/
theorem stAB_P20B : stAB P20B Lvm.CT.occOfU (atomsOf P20B (schedule P20B)) 0 [] [] 0 = true := by
  rw [stAB_atomsOf, schedule_P20B_litA]
  decide +kernel

end Lvm.VEq
