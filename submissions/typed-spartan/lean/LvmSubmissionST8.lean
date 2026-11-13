-- New for lvm2 (roll 8 = B1, B1-IX): the typed test submission at `P8` (tools only; the badge reads `P20`'s).
import LvmFinGuard
import LvmVerifierST
import LvmQTypedInst8

set_option autoImplicit false

namespace Lvm.T

open RecursionFast

/-- V_S of the typed backend at `P8` (the test set). -/
def VSB8 : SProg := Lvm.VST Lvm.P8 Lvm.QTyped.NT8

/-- The typed test submission at `P8`. -/
def submissionB8 : Submission := Lvm.Fin.subG Lvm.QTyped.staticOkT8 VSB8

end Lvm.T
