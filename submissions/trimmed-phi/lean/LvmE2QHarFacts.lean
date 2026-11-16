-- New for lvm2 E2-FT (E2F-QH6): the facts S2GF's typed HAR (`harithF20`, E2F-C) reads besides the gadgets' phase
-- lemmas: the child's stream on the node memory (`Streamed`), `Σ'`'s size, the incoming accumulator from `PUB` at
-- `acc_in` of 44 coordinates, and V's proof-of-work checks on the ground answers from the PoW blocks (`powBlk_ok`).
import LvmE2QHarGen
import LvmE2QNodeG
import LvmE2QWPhase
import LvmQAsmHarTails
import LvmQTypedHarS
import LvmQAccSoundOff

-- (GOLF2: 9 declarations that `certified` does not use moved verbatim to `LvmE2QNodeFOff`, outside its import closure.)

/-!
# The HAR's facts at S2GF

* **`sigCF qr`**: the child's trace bytes `Σ'` at S2GF; **`sigCF_size`**: `|Σ'| = hashedLen P20F`.
* **`streamedF`**: the node memory's stream cells are `Σ'`'s lanes (`Streamed … (streamLanes P20F)`).
* **`accCA n M pb`**: `acc_in` read off its `PUB` cells at `n` coordinates (`accC` at `accVars`, `accCA_accVars`);
  **`accCA_pubXF`**: at `accVF = 44` it is the statement's `(pubXF x).accIn`.
* **`powOk_of_blks`**: on a layout built with `specQF … pw`, where the coordinate-split relation holds, every
  answer `(q, g)` of `pw` whose lanes are streamed has V's check `powOKR g (feAt Σ (8q))`; so `PowOkV (feAt Σ) L` for
  every challenge list `L ⊆ pw`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.NS Lvm.Typed Lvm.QTyped
open Lvm.VEq (pubXF)
open LeanVM.Protocol (Column)

/-! ## `Σ'` and the stream -/

/-! ## `acc_in` from `PUB` at 44 coordinates -/

-- `powRecRows_mem`, `boolRuns_cover`, `auxRow_mem`, `powOk_of_blks` are in `LvmE2QHarGen` (moved, lvm2 U-TAPE).

end Lvm.E2Q
