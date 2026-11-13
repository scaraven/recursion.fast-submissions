-- New for lvm2 (roll 8 = B1, B1-IX): the submission of the typed backend. `V_S` is `VST P20 NT20` (`LvmVerifierS`,
-- `TypedV.decideFT` on the B program's typed instance, `LvmQTypedInst`) behind the typed static guard
-- `staticOkB20` (A24, as roll 7's `subG staticOkB`; wave L adds `oneOkB`); the extractor is WP-13a's, as before.
import LvmFinGuard
import LvmQTypedInst
import LvmQTypedChk
import LvmQTypedHarChk
import LvmVerifierST
import LvmTypedVInst
import LvmMPSig

/-!
# The typed submission

* **`VSB20`**: `V_S` at `P20` on the typed instance `NT20` (the frozen regions, `Φ_Q`'s cache, the mini-bus's
  tables); `P8`'s in `LvmSubmissionST8`.
* **`submissionB20 := subG staticOkB20 VSB20`**: the guarded submission (`staticOkB20 = staticOkT20 && oneOkB
  layT20 && nodeChkB … && harChkB …`). With the guard off the `S` branch accepts nothing (`LvmFinGuard.certificateR_reject`); with it on,
  the typed certificate is wave L's (`LvmCertT20.certificateT20`: the refinement of `decideFT` to `typedProg`, L-C;
  `typedSpecR`, L-B; `NodeSound` on `GoodT`, L-D, reading the guard's facts `LvmCertTInst.SF20`).
-/

set_option autoImplicit false

namespace Lvm.T

open RecursionFast

/-- The guard's region check is B1-V's `TNat.layOk`. -/
theorem layOkN_eq : Lvm.QTyped.layOkN = Lvm.TypedV.TNat.layOk := rfl

/-- **V_S of the typed backend at `P20`.** -/
def VSB20 : SProg := Lvm.VST Lvm.P20 Lvm.QTyped.NT20

/-- **The layout's word `1` lies in a `1` region** of its word space (the specification's `TInst.Ok`, second half;
`mkLayD` places it so, the guard checks it natively: lvm2 roll 8, wave L). -/
def oneOkB (lay : Lvm.Typed.Lay) : Bool :=
  (lay.yregs.find? fun r => decide (r.base ≤ lay.one ∧ lay.one < r.base + 2 ^ r.log)).map (·.src) == some .one

/-- **The typed guard at `P20`**: `staticOkT20`, the word `1`'s region, `σ′`'s regions in the stream block `S` (M′,
R11: `Lvm.TypedV.sigInSB`), the layout checks the typed `NodeSound` reads (`nodeChkB`: the input map's cells, the
`readd` targets, the mini-bus's seed blocks) and the typed HAR's (`harChkB`: Q_arith's claim list in both shapes,
the circuit's regions are V_S's) (wave L). -/
def staticOkB20 : Bool :=
  Lvm.QTyped.staticOkT20 && oneOkB Lvm.QTyped.layT20 && Lvm.TypedV.sigInSB Lvm.QTyped.NT20 &&
    Lvm.QTyped.nodeChkB Lvm.QAsm.cfg20 Lvm.QTyped.frz20 Lvm.QTyped.QB20 Lvm.QTyped.layT20 Lvm.QTyped.NT20 &&
    Lvm.QTyped.harChkB Lvm.QAsm.cfg20 Lvm.QTyped.tdata20 Lvm.QTyped.NT20

/-- **The typed submission**: `V_S` at `P20` behind the typed static guard, M′'s extractor (lvm2 roll 11, R11-X:
`subGM`, `EXM`, `extXM`). -/
def submissionB20 : Submission := Lvm.Fin.subGM staticOkB20 VSB20

end Lvm.T
