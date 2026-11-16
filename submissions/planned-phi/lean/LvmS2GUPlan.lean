-- New for lvm2 U-TAPE (UT-L, 2026-11-16): the plan's and Q_link's static stream facts at S2GU (`P20U`): one decision
-- each, as S2GT's `LvmS2GTPlan` (the node soundness and the `KS` bridge read them).
import LvmE2QPlanF
import LvmS2GUSched

/-!
# The S2GU plan's facts

* **`passR_P20U`**: the one-pass decision at `P20U` (3,649 entries, `Σ clen = 283,952`, `Σ (40 + len) = 538,655`; the
  cap queries at entries 2, 1,004 and 2,423 [measured, a probe evaluation of the plan; the same probe gives S2GT's
  2, 1,316, 2,735]).
* **`planSt_P20U`**: `PlanOk P20U`; **`streamOk_P20U`**.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.QLink Lvm.Replay Lvm.PlanChk

/-- The cap entries at `P20U` and their lengths (the FS queries that absorb the caps). -/
def tblU20 : List (ℕ × ℕ) := [(2, 8224), (1004, 4176), (2423, 4176)]

set_option maxRecDepth 200000 in
/-- **The one decision at `P20U`.** -/
theorem passR_P20U : passR (capLk tblU20) 3649 283952 538655 (plan P20U) tblU20 0 0 0 = true := by
  unfold P20U P20T; rw [P20_eq]; decide +kernel

set_option maxRecDepth 200000 in
/-- `PlanOk P20U` and the walk's last entry. -/
theorem planSt_P20U : PlanOk P20U ∧ (planAll P20U).2.i = 3649 := by
  unfold P20U P20T; rw [P20_eq]; decide +kernel

/-- **Q_link's stream facts at `P20U`.** -/
theorem streamOk_P20U : StreamOk P20U := streamOk_ofR passR_P20U sizes_P20U.1.2.2.1

end Lvm.E2Q
