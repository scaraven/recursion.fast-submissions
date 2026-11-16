-- WP-14d (EXQ), lvm2 X-REC2 / S4-S2 (helper XA): O5c for `EXt tabs`. The proof is
-- `LvmCertSExq2.ext_eq_gen` (two `C_rec` levels on S2J, generic in `V_S`); here `V_S := VSt tabs`,
-- and the search's bounds from the contract (`sFits_of_acc` on the submission). WP-14d's helpers
-- moved to `LvmCertSExq2`.
import LvmSubmissionS
import LvmCertSExq2

/-!
# O5c: `EX = S.Ex K.ext` on good logs (removed at M′)

B1's `ext_eq_S` (`ext_eq_gen` at `VSt tabs`) is removed at M′ (R11-IS): it replayed `C_rec`'s opening.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

-- (R11-IS, M′: `ext_eq_S` is removed: B1's `ext_eq_gen` at `VSt tabs`, dead, through `C_rec`.)

end Lvm.ASM
