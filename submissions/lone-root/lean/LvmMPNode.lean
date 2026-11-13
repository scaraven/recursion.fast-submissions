-- New for lvm2 roll 11 (M′, R11-LEAD): `NodeSoundM` from a pair-form `NodeSound`, given that M′'s child reads
-- from the stream window what the pair form's child reads from the relocated `C_rec` column.
import LvmMPCert
import LvmMPMid

/-!
# `NodeSoundM` by transfer

`nodeSoundM_of`: if `childM x (winOf q) = childS (recOf x q)` for every statement and `C_main` column (the layout's
window fact), `NodeSound VS vk G childS` gives `NodeSoundM VS vk (GoodOfM recOf G) childM`. The node program's own
soundness (`NodeSound` for M′'s `V_S`) is the instance's obligation.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast LeanVM.Protocol

theorem nodeSoundM_of {VS : Lvm.T.SProg} {vk : RecursionFast.Digest} {G : GoodRel}
    {recOf : List UInt8 → Column CMain.nu20 → Column 19} {childS : Column 19 → RecursionFast.Signed}
    {childM : List UInt8 → List BF64 → RecursionFast.Signed}
    (hch : ∀ x q, childM x (Lvm.X.winOf q) = childS (recOf x q)) (h : NodeSound VS vk G childS) :
    NodeSoundM VS vk (GoodOfM recOf G) childM := fun c x q hok hG ↦ by
  rw [hch]
  exact h c x q (recOf x q) hok hG

end Lvm.ASM
