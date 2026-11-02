-- New for `flock-recursive` (BLUEPRINT §3, A.8, A.9; stage S-F2, track L-cert).
-- RET-3: the declarations revision 4 reads moved to `FRVerifierImplCore`.
import FRVerifierImplOps
import FRVIRTplFast
import FRVIRFinalsSG
import FRSoundnessCoreTruths
import FRVerifier
import FRBlockKinds
import FRVerifierImplNode
import FRSegTarget4

/-!
# `implC`, `specC`, `implC_meets`, `V` (with the node's M rows)

The op implementations and specifications are in `FRVerifierImplOps` (split by S-E3); this module
assembles them with the M-row ops (`evalM`, `evalL`; revision 3.12 removed `evalMK`). Since
revision 3.13 both are called once, by `finE`, at E4's 23-coordinate cell point `r′` (`evalL`'s
cell point is no longer Lr4's 15 challenges zero-padded: `FRVIRFinalsSF.finE_evalL_point`).
-/

namespace FR
namespace Impl
open Finset RecursionFast RecursionFast.Blake2s

/-! ## The assembled record, `Meets`, `V` -/

theorem implC_implT (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    Circ.ImplT (implC fin lRows κs₀) := implCWith_implT _ _

/-- **The verifier** (§3) with the concrete ops: `Vwith implC finC`. Parametric in `finPf`, the
L rows and the stand-in `κs₀` until S-G1d, S-E2 and S-0 supply them. -/
def VC (pf : FinField) (lRows : List Circ.Row) (κs₀ : F) : Digest → Digest → Proof → OProg Bool :=
  Vwith (implC (finC pf) lRows κs₀) (finC pf)

end Impl
end FR
