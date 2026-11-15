-- New for lvm2 E2-FT (E2F-C): the plan's static facts at S2GF (`P20F`): `PlanOk`, Q_link's `StreamOk`, the entry
-- count and every query within `queryCap`, from one decision each (`LvmPlanP20`'s generic consequences of `passR`;
-- roll 11's `planSt_P20`).
import LvmPlanP20
import LvmScheduleF
import LvmReplay

/-!
# The S2GF plan's facts

* **`passR_P20F`**: the one-pass decision at `P20F` (3,959 entries, `Σ clenC = 306,984`, `Σ (40 + len) = 584,007`;
  the cap queries at entries 2, 1,314 and 2,733).
* **`planSt_P20F`**: `PlanOk P20F` and the walk's last entry.
* **`streamOk_P20F`**, **`plan_P20F`**, **`planCap_P20F`**: what the node soundness asks of the schedule.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.Replay Lvm.PlanChk Lvm.QLink

/-- The cap entries at `P20F` and their lengths (the FS queries that absorb the caps). -/
def tblF20 : List (ℕ × ℕ) := [(2, 8224), (1314, 4176), (2733, 4176)]

set_option maxRecDepth 200000 in
/-- **The one decision at `P20F`.** -/
theorem passR_P20F : passR (capLk tblF20) 3959 306984 584007 (plan P20F) tblF20 0 0 0 = true := by
  unfold P20F; rw [P20_eq]; decide +kernel

set_option maxRecDepth 200000 in
/-- `PlanOk P20F` and the walk's last entry. -/
theorem planSt_P20F : PlanOk P20F ∧ (planAll P20F).2.i = 3959 := by
  unfold P20F; rw [P20_eq]; decide +kernel

theorem planOk_P20F : PlanOk P20F := planSt_P20F.1

/-- The plan has 3,959 entries. -/
theorem plan_P20F : (plan P20F).length = 3959 := (sound_of passR_P20F).2.2.1

/-- **Q_link's stream facts at `P20F`.** -/
theorem streamOk_P20F : StreamOk P20F := by
  refine ⟨streamOkL_of passR_P20F, ?_⟩
  have hs : slenS (lens P20F) = 584007 := by
    rw [slenS, lens, List.map_map]
    exact (sound_of passR_P20F).2.2.2.2
  have hh : hashedLen P20F = 584008 := checks_P20F.1.2.2.1
  rw [hh, hs]

/-- Every planned query at `P20F` is within `queryCap`. -/
theorem planCap_P20F : ∀ i < (plan P20F).length, ((plan P20F).getD i default).len ≤ queryCap := by
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact cap_of passR_P20F _ (List.getElem_mem hi)

end Lvm.E2Q
