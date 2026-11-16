-- New for lvm2 (WP T-V, stage S2): V_S's tape phase (`dTape`: T1, T2) refines the tape caller's
-- first three binds (`LvmKeccakCallerTape.tapeProg`) on the stream.
import LvmVEqKec
import LvmDecideTape
import LvmKeccakGkr

-- (GOLF2: 17 declarations that `certified` does not use moved verbatim to `LvmVEqTapeOff`, outside its import closure.)

/-!
# The tape phase: V_S refines the verifier language

`Lvm.verifyKeccakLayerG depth segs` and `keccakLayersG` (over `FE`, on the reader `DM`) refine T-G's
`verifyKeccakLayerS ⟨depth, segs⟩` and `keccakLayersS` (over `E`) for every shape, as v1's layer
refines VCore's in `LvmVEqKec`; only the round constant's share changes (`toExt3_iotaG`). The tape's
first claim maps to T-G's (`kcE_tapeFirstClaimF`), `tapeGkrF` refines `tapeGkr` (through its flat
form `tapeGkr_eq`), and each native function never clears a failed check (`MonoD`).

Headline: **`ref_dTape w`**, V_S's `dTape w` refines
`sampleChallenges w >>= fun r ↦ readScalars 25 >>= fun v ↦ tapeGkr w r v >>= fun claim ↦ ret (r, v, claim)`
(the first three binds of `tapeProg`) with `TapeRel w`: the point and the scalars mapped, their
lengths, the claim by `kcE`, and the claim's weights' and point's lengths (`RetD`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (tE_add tE_mul tE_zero tE_one FE_eq_of_beq)

/-! ## The generic layer's round constant -/

/-! ## Returns -/

/-! ## `MonoD` -/

/-! ## The tape's first claim -/

/-! ## Refinement -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

end Ref

end Lvm.VEq
