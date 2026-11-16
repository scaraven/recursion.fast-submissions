-- New for lvm2 E2-FT (E2F-C2, from E2F-QH3's draft): the typed phases at S2GF in the circuit replay V_S's
-- (`typedGX` replays `LvmTypedVX.dTypedX`), the port of roll 11's `typedG_replays` (LvmQTypedHarZ/R/A/M/G) to
-- transcript amendment 1.
import LvmQTypedHarS
import LvmE2QTypedX
import LvmE2VPub
import LvmE2QHarFacts

-- (GOLF2: 17 declarations that `certified` does not use moved verbatim to `LvmE2QNodeFOff`, outside its import closure.)

/-!
# `typedGX` replays `dTypedX`

* **`zeroGX_replays`**: `zeroGX z g P` (gate on) replays `dZeroX` from `P` to `wGPX P`: `r_x` is the run's challenge
  cells, the six values its loaded cells.
* **`wireGX_replays`**: `wireGX` replays `dWiringX` from `wGPX P` to `rRPX P` (`virtGX`'s value is V_S's `virtEF`
  on the child's `PUB` at `acc_in` of `accV` coordinates, `virtGX_spec`).
* **`qaccTX_replays`**: `qaccTX` replays `dAccX` from `aPX P` to `mbPX P`, folding to the current proof's `acc_in`
  (`accCA accVF M pb`, its `PUB` cells).
* **`typedGX_replays`**, **`typed_phaseX`**: the composition (the relayout and the mini-bus are roll 11's
  `relayG_replays`, `miniG_replays`), as `Replays` and in the `PhaseAt` form `core_of_phasesF` takes.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM Lvm.Har
open Lvm.TypedV (TNat)


/-! ## The child's `PUB` lanes at `accV` variables (`pubOfA`, `pubLanesX`) -/

section Pub

open Lvm.QAcc

end Pub

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

end

/-! ## `PUB` and `acc_in` of the child at `acc_in` of `accV` coordinates -/

section PubEval

open Lvm.QAcc Lvm.QSig

end PubEval

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-! ## The wiring over the six values -/

/-! ## A23 at `Φ_Q` in 44 variables -/

section helpers
open Lvm.QAcc Lvm.QSig

end helpers

/-! ## The typed phases -/

end

end Lvm.E2Q
