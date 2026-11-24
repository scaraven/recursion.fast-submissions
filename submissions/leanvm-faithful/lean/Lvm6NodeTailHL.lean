-- New for lvm6 (WP N4-tail phase 2, RV4 M4 (c)). CC's stream inputs (`Inp`: the ring phase's lane, the levels'
-- lanes, claim 0's point and value cells) are at the lanes of N4-split's simulation (`partLane`), at `inp18`.
import Lvm6NodeSplit
import Lvm6NodeSplitOpen
import Lvm6NodeDeploy

/-!
# CC's lanes are the simulation's (WP N4-tail, RV4 M4 (c))

`Inp`'s lanes come from `lanes18` (`walkA` over `sched6 P18`); N4-split's simulation places each part at
`partLane pre` (`Split.split6`'s last conjunct: the state after `preR` sits at `partLane preR`).
**`CCLanes I`** names the agreement, one field per input: `ring` (CC-5′'s lane), `lev` (level `j`'s first lane,
after the ring part and the levels before it), `z0` (claim 0's point: the answers of §6.1's group `G, D`), `y0`
(claim 0's value: §6.1's `E 1`). **`inp18_lanes : CCLanes Dep.inp18`**, by kernel evaluation of closed numbers
(KDN: one `decide +kernel` of the Boolean `ccLanesB`, which also checks N4-split's opening lanes `aO` for
`TailHS.aO_eq`, so the kernel evaluates `lanes18`, the plan and the schedule once, not once per field).
-/

set_option autoImplicit false

namespace Lvm6.Node.Split

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.E2V Lvm6.QK

/-- §6.1's items (`cap, B, G, D, E`): the OOD group's ground draw `G` and the value `E 1`. -/
def iOodG : ℕ := 2
def iY0 : ℕ := 4

/-- **CC's inputs at the simulation's lanes.** -/
structure CCLanes (I : Dep.Inp) : Prop where
  ring : I.aRing = partLane preR
  lev : ∀ j < P18.levels.length, I.aL j = partLane (preO ++ (List.range j).flatMap P18.levelPart)
  z0 : I.z0 = (List.range P18.M).map (QC.ansAt (partLane (P18.commitPart.take iOodG)))
  y0 : I.y0 = [ld2 (partLane (P18.commitPart.take iY0))]

/-- **`CCLanes inp18` and the opening lanes `aO j = inp18.aL j` (`j ≤ jF18`) as one Boolean** (KDN). -/
def ccLanesB : Bool :=
  (Dep.inp18.aRing == partLane preR) &&
    (List.range P18.levels.length).all (fun j ↦
      Dep.inp18.aL j == partLane (preO ++ (List.range j).flatMap P18.levelPart)) &&
    decide (Dep.inp18.z0 = (List.range P18.M).map (QC.ansAt (partLane (P18.commitPart.take iOodG)))) &&
    decide (Dep.inp18.y0 = [ld2 (partLane (P18.commitPart.take iY0))]) &&
    (List.range (jF18 + 1)).all (fun j ↦ aO j == Dep.inp18.aL j)

/-- The one kernel evaluation. -/
theorem ccLanesB_true : ccLanesB = true := by decide +kernel

theorem ccLanesB_spec : CCLanes Dep.inp18 ∧ ∀ j < jF18 + 1, aO j = Dep.inp18.aL j := by
  have h := ccLanesB_true
  simp only [ccLanesB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩, h.2⟩

theorem inp18_lanes : CCLanes Dep.inp18 := ccLanesB_spec.1

end Lvm6.Node.Split
