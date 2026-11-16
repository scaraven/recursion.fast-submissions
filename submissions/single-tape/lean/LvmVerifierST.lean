-- Moved out of `LvmVerifierS` (lvm2 roll 8, wave L, L-W; a pure move): the typed `V_S`, so that the bus `V_S`'s
-- consumers (`LvmReplay`, `LvmCertSQ`, …) do not import `LvmTypedV` (a shorter build critical path).
import LvmVerifierS
import LvmTypedV

/-!
# The typed `V_S`

**`VST p N`** (lvm2 roll 8, B1: B-DES §1.2): parse, then drive the schedule and decide with `TypedV.decideFT` on the
native typed instance `N`; **`VST_reject`**: a rejected header asks no query.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **The typed `V_S`** (lvm2 roll 8, B1: B-DES §1.2, the typed bus-free backend): parse, then drive the schedule
(`LvmSchedule.phases`, the typed phases: `LvmTypedVSched.scheduleT_eq`) and decide with `TypedV.decideFT` on the
native typed instance `N` (the regions with their targets, `Φ_Q`, the mini-bus's tables). -/
def VST (p : Params) (N : TypedV.TNat) (vk c : Digest) (π : Proof) : OProg Bool :=
  if parseOk p vk c π then drive p π (TypedV.decideFT p N vk c) else .ret false

/-- A rejected header asks no query (typed). -/
theorem VST_reject {p : Params} {N : TypedV.TNat} {vk c : Digest} {π : Proof} (h : parseOk p vk c π = false) :
    VST p N vk c π = .ret false := by
  simp [VST, h]

end Lvm
