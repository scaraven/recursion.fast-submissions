-- New for lvm2 E2-FT (E2F-C): the plan's static facts at S2GF (`P20F`): `PlanOk`, Q_link's `StreamOk`, the entry
-- count and every query within `queryCap`, from one decision each (`LvmPlanP20`'s generic consequences of `passR`;
-- roll 11's `planSt_P20`).
import LvmPlanP20
import LvmScheduleF
import LvmReplay

-- (GOLF2: 2 declarations that `certified` does not use moved verbatim to `LvmE2QHarFrontOff`, outside its import closure.)

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

/-- **Q_link's stream facts** at a stage whose one-pass decision holds, with `hashedLen p = t₂ + 1`. -/
theorem streamOk_ofR {p : Params} {tbl : List (ℕ × ℕ)} {n t1 t2 : ℕ}
    (h : passR (capLk tbl) n t1 t2 (plan p) tbl 0 0 0 = true) (hh : hashedLen p = t2 + 1) : StreamOk p := by
  refine ⟨streamOkL_of h, ?_⟩
  have hs : slenS (lens p) = t2 := by
    rw [slenS, lens, List.map_map]
    exact (sound_of h).2.2.2.2
  rw [hh, hs, Nat.add_comm]

/-- Every planned query is within `queryCap` at a stage whose one-pass decision holds. -/
theorem planCap_ofR {p : Params} {tbl : List (ℕ × ℕ)} {n t1 t2 : ℕ}
    (h : passR (capLk tbl) n t1 t2 (plan p) tbl 0 0 0 = true) :
    ∀ i < (plan p).length, ((plan p).getD i default).len ≤ queryCap := by
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact cap_of h _ (List.getElem_mem hi)

/-- **Q_link's stream facts at `P20F`.** -/
theorem streamOk_P20F : StreamOk P20F := streamOk_ofR passR_P20F checks_P20F.1.2.2.1

end Lvm.E2Q
