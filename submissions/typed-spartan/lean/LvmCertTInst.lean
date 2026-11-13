-- New for lvm2 (roll 8 = B1, wave L, L-W): the typed certificate's instance at `P20`, the objects the wave-L
-- obligations are stated on (`LvmCertT20`'s stubs; L-B, L-C, L-D import this module to prove them).
import LvmSubmissionST

/-!
# The typed instance at `P20`

* **`Ti20`**: the specification's typed instance (`TNat.inst`: the regions' maps are `NT20`'s, the program `QB20`,
  the layout `layT20`, the mini-bus's tables `mbT20`).
* **`SF20`**: the typed guard's facts at `P20` (`sf20 : staticOkB20 = true → SF20`: `StaticFactsT` and wave L's extra
  native checks).
-/

set_option autoImplicit false

namespace Lvm.CT

open Lvm.Typed Lvm.QTyped

/-- **The specification's typed instance at `P20`.** -/
noncomputable def Ti20 : TInst := NT20.inst QB20 layT20

/-- **The typed guard's facts at `P20`** (`staticOkB20`): `StaticFactsT`'s (`staticOkT20`), then wave L's native
checks, one field each (the word `1`'s region; L-D's/L-H's checks join here). Field access `S.wf`, `S.regs`, … is
`StaticFactsT`'s. -/
structure SF20 : Prop extends StaticFactsT Lvm.QAsm.cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20 where
  /-- The layout's word `1` lies in a `1` region (`Lvm.T.oneOkB`). -/
  one : Lvm.T.oneOkB layT20 = true
  /-- The layout checks the typed `NodeSound` reads (`nodeChkB`, L-D's `LvmQTypedChk`). -/
  chk : nodeChkB Lvm.QAsm.cfg20 frz20 QB20 layT20 NT20 = true
  /-- The typed HAR's checks (`harChkB`, L-H's `LvmQTypedHarChk`). -/
  har : harChkB Lvm.QAsm.cfg20 tdata20 NT20 = true

/-- **The guard's facts** from `staticOkB20 = true`. -/
theorem sf20 (h : Lvm.T.staticOkB20 = true) : SF20 :=
  have h' : ((staticOkT20 = true ∧ Lvm.T.oneOkB layT20 = true) ∧
      nodeChkB Lvm.QAsm.cfg20 frz20 QB20 layT20 NT20 = true) ∧ harChkB Lvm.QAsm.cfg20 tdata20 NT20 = true := by
    simpa only [Lvm.T.staticOkB20, Bool.and_eq_true] using h
  { staticFactsT20 h'.1.1.1 with one := h'.1.1.2, chk := h'.1.2, har := h'.2 }

end Lvm.CT
