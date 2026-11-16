-- Moved out of `LvmCertF20X` (lvm2 U-TAPE, UT-L, 2026-11-16; text unchanged): the extractor's item kinds are the
-- specification's, and a replay-safe item list has no positions (any stage).
import LvmXSKinds
import LvmCertSExqKinds
import LvmXSExtRun

/-!
# Item kinds at any stage (`itemKindsS_eq`, `noPos_of_rs`)
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.XS

theorem itemKindsS_eq : ∀ its : List Item, itemKindsS its = Lvm.ASM.itemKinds its
  | [] => rfl
  | it :: its => by
    have ih := itemKindsS_eq its
    cases it <;> simp only [itemKindsS, Lvm.ASM.itemKinds, ih]

theorem noPos_of_rs : ∀ its : List Item, Lvm.ASM.RSItemsF its = true → ∀ it ∈ its, ∀ r, it ≠ .positions r
  | [], _ => by simp
  | .readW _ _ :: its, h | .read _ :: its, h | .sample :: its, h => fun it hit r ↦ by
    rcases List.mem_cons.mp hit with rfl | hit
    · exact fun e ↦ Item.noConfusion e
    · exact noPos_of_rs its h it hit r
  | .cap _ _ :: _, h | .positions _ :: _, h | .opening _ :: _, h => by simp [Lvm.ASM.RSItemsF] at h

end Lvm.CT
