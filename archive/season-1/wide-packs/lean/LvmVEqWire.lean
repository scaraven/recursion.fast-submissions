-- New for lvm2 (WP T-V, stage S2): V_S's wire phase (LvmDecideTape `dWire`, over `FE`) refines T-W's
-- chain wiring program (`Lvm.KG.wireChProg`, over `E`) on the stream; the `FE` twins of T-K's kernels
-- and T-W's dot products are their originals through `FE.toExt3`.
import LvmVEqKec
import LvmWireSpec
import LvmDecideTape
-- (GOLF2 import pruning: dropped LvmChainTablePad: unused by this module.)

-- (GOLF2: 32 declarations that `certified` does not use moved verbatim to `LvmVEqWireOff`, outside its import closure.)

/-!
# The wire phase: V_S refines the verifier language

* **The twins** (`LvmDecideTape` against `LvmWireKernel`, `LvmWireSpec`): `toExt3_eqAtF`,
  `toExt3_iotaF`, `ms4E_msTailF` (T-K's automaton, entry by entry), `toExt3_msEvalF`,
  `p2E_thrTailF`, `toExt3_thrEvalF`, `toExt3_c43DotF`, `toExt3_padDotF` (the digest's lanes
  `digestLanes d` carry the bits `digestBits d`, `digestLanes_bit`), `toExt3_wireTargetF`,
  `toExt3_slotWF` and its dot form `toExt3_slotDot`.
* **`ref_dWire`**: wherever V_S's wire phase ends with its checks held, `wireChProg p.logN
  (dSelBits p) (dSel p) d pub.n (kcE claim)` read off the stream returns at the same cursor an output
  related by `WireRel`, provided the header's `s` lanes are the digest's (`pub.s = digestLanes d`).
  Read for read: the wiring sumcheck (`ref_sumcheck`), `g_D`, the check against `msEval`, then
  `D`'s slot reduction (`ref_dSlotD`: two rounds, 64 slices, the slot check, the ring switch). The
  native slot block is reassociated (`dWire_eq`) to the language's `slotProg` bind.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Finset
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_cons bitE)
open Lvm.M3 (tE_add tE_mul tE_zero tE_one FE_eq_of_beq)

/-! ## Helpers -/

namespace Wr

end Wr

/-! ## T-K's kernels -/

/-! ## T-W's dot products -/

/-! ## The native slot block -/

/-! ## `MonoD` -/

/-! ## Refinement -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

end Ref

end Lvm.VEq
