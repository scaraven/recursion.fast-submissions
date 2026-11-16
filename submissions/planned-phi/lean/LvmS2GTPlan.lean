-- New for lvm2 S2GT (GT-L2, 2026-11-15): the plan's and Q_link's static facts at S2GT (`P20T`, `cfgG20`) that the
-- node soundness reads (S2GT-STMT 11): one decision each, as S2GF's `LvmE2QPlanF`/`LvmE2QNodeFacts`.
import LvmE2QNodeG
import LvmE2QInstT
import LvmS2GTSched

/-!
# The S2GT plan's facts

* **`passR_P20T`**: the one-pass decision at `P20T` (3,961 entries, `Σ clen = 305,984`, `Σ (40 + len) = 583,151`;
  the cap queries at entries 2, 1,316 and 2,735 [measured, a probe evaluation of the plan]).
* **`planSt_P20T`**: `PlanOk P20T`; **`streamOk_P20T`**, **`hQT20`** (`QOk P20T (lay cfgG20)`), **`planC_P20T`**.
* **`nodeStG20`**: `NodeStC cfgG20`, what `nodeSoundC` reads at S2GT.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay Lvm.PlanChk

/-- The cap entries at `P20T` and their lengths (the FS queries that absorb the caps). -/
def tblT20 : List (ℕ × ℕ) := [(2, 8224), (1316, 4176), (2735, 4176)]

set_option maxRecDepth 200000 in
/-- **The one decision at `P20T`.** -/
theorem passR_P20T : passR (capLk tblT20) 3961 305984 583151 (plan P20T) tblT20 0 0 0 = true := by
  unfold P20T; rw [P20_eq]; decide +kernel

set_option maxRecDepth 200000 in
/-- `PlanOk P20T` and the walk's last entry. -/
theorem planSt_P20T : PlanOk P20T ∧ (planAll P20T).2.i = 3961 := by
  unfold P20T; rw [P20_eq]; decide +kernel

/-- **Q_link's stream facts at `P20T`.** -/
theorem streamOk_P20T : StreamOk P20T := streamOk_ofR passR_P20T sizes_P20T.1.2.2.1

set_option maxRecDepth 200000 in
/-- **Q_link's static checks at S2GT** (`qOkB` decided as `qOkF`, as `hQF20`). -/
theorem hQT20 : QOk P20T (lay cfgG20) :=
  qOk_of streamOk_P20T (by rw [← qOkF_eq]; unfold P20T; rw [P20_eq]; decide +kernel)

/-- S2GT's plan facts. -/
theorem planC_P20T : PlanC P20T :=
  planC_ofR passR_P20T planSt_P20T.1 (by decide) sizes_P20T.1.1 (by norm_num) sizes_P20T.1.2.2.1 (by norm_num)
    (by norm_num) rfl

/-- S2GT's node statics. -/
theorem nodeStG20 : NodeStC cfgG20 :=
  ⟨streamOk_P20T, hQT20, by decide,
    by rw [show cfgG20.p = P20T from rfl, sizes_P20T.1.2.2.2.2.1]; norm_num,
    by rw [show cfgG20.p = P20T from rfl, sizes_P20T.1.2.2.2.2.1, sizes_P20T.1.2.2.1]; rfl, rfl,
    by decide, by decide, planC_P20T⟩

end Lvm.E2Q
