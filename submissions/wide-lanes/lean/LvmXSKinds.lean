-- New for lvm2 E2F (E2F-L, 2026-11-13): the middle phases' shape over a stage's items (`MidFollows` over `ItemF`).
import LvmCertSExqKinds
import LvmScheduleF

/-!
# The kinds of a stage's items

`itemKindsS` (`itemKinds` over `ItemF`: `readW m w` is `m` reads) and **`MidFollowsS its mid`**: every accepted run
of `mid x` has the kinds of the items `its`.
-/

set_option autoImplicit false

namespace Lvm.XS

open Lvm Lvm.ASM LeanVM.Protocol.Compile

/-- The kinds the items stand for (`itemKinds` over `ItemF`). -/
def itemKindsS : List Item → List EvK
  | [] => []
  | .readW m _ :: its => List.replicate m .read ++ itemKindsS its
  | .read m :: its => List.replicate m .read ++ itemKindsS its
  | .sample :: its => .sample :: itemKindsS its
  | _ :: its => .other :: itemKindsS its

/-- **The middle phases' shape at a stage**: every accepted run of `mid x` has the kinds of `its`. -/
def MidFollowsS {α : Type} (its : List Item) (mid : List UInt8 → VerifierProgram α) : Prop :=
  ∀ x l a, (mid x).after l = some (.ret a) → l.map kindOf = itemKindsS its

end Lvm.XS
