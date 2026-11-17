-- New for lvm2 MP-B cap pruning (CAP-V, 2026-11-17; lead RE-FREEZE R3 (a)): `TRefHypTB` at the S2GB instance from the
-- S2GB guard's facts (`trefS20`'s twin).
import LvmS2GBStmtC
import LvmS2GBFill

/-!
# `TRefHypTB` at the S2GB instance (owner V)

* **`trefB20`**: `TRefHypTB NTB20 QB20 layB20` from `SFB20` (`trefS20`'s twin: the mini-bus record fits `P20B`).
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.Typed Lvm.E2Q
open Lvm.E2T (TRefHypTB)

/-- **`TRefHypTB` at the S2GB instance** from the guard's facts (`trefS20`'s twin). -/
theorem trefB20 (S : SFB20) : TRefHypTB NTB20 QB20 layB20 where
  ok := S.1.st.regs
  hlay := S.1.st.hlayOk
  mini := S.1.st.mini
  sc := by
    show Lvm.M3.AllSc NTB20.toN.mbT
    rw [S.1.mb]
    exact Lvm.M3.allSc_of_B (tabsOkB_mbT _ _ _ _)
  phiT := fun pt hpt ↦ by
    show Lvm.Typed.KT.PhiQGCKT cacheB20 (Lvm.Typed.KT.phiPre cacheB20) pt = _
    have hc : cacheB20 = Lvm.Typed.cacheWX QB20 layB20 := cacheWXF_eq QB20 layB20 S.1.st.hlay
    rw [Lvm.Typed.KT.PhiQGCKT_eq, hc]
    exact Lvm.Typed.KT.PhiQGC_eqW QB20 layB20 S.1.st.hlay S.1.st.cache (hc ▸ S.2.2.2.1) pt hpt

end Lvm.CT
