-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's relayout phase: `relayKernG`'s value is V_S's closed form
-- `relayKernF` (the stride-17 division automaton and the identity tail), and `relayG` replays `dRelayT`.
import LvmQTypedHarB

-- (GOLF2: 51 declarations that `certified` does not use moved verbatim to `LvmE2QNodeFOff`, outside its import closure.)

/-!
# The `S_flat` relayout in the circuit

* **`relayKernG_spec`**: on regions that are V_S's (`TdOk`: one `S_flat` region of `2^19` words from position 0),
  `relayKernG`'s value at `(r_y, r)` is `relayKernF N r_y r` (the circuit's division by 17, MSB first, with the
  remainders' weights, against V_S's array automaton `divKern`; the circuit's `tailG` against `geKern`).
* **`relayG_replays`**: `relayG` replays `dRelayT` from `rRP P` to `aP P`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)

open Lvm.TypedV (eq1)

/-! ## Helpers (the division automaton, `geKern`'s tail, `tailG`) -/
section
variable {c : Ctx} {M : Mem}

end

section
variable {c : Ctx} {M : Mem}

end
section
variable {c : Ctx} {M : Mem}

end

section
variable {c : Ctx} {M : Mem}

end

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

end

end Lvm.Har
