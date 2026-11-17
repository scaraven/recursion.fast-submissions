-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's zerocheck and wiring phases: `zeroG` replays V_S's `dZeroT`,
-- `wireG` replays `dWiringT` (with `virtG`'s value: V_S's closed form `virtEF` on the circuit's regions).
import LvmQTypedHarB

-- (GOLF2: 29 declarations that `certified` does not use moved verbatim to `LvmQTypedHarZOff`, outside its import closure.)

/-!
# The zerocheck and the wiring sumcheck in the circuit

* **`zeroG_replays`**: `zeroG z g P` (gate on) replays `dZeroT` from `P` to `wGP P`: `r_x` is the run's challenge
  cells, `a*, b*, c*` its three loaded cells.
* **`virtG_spec`**: `virtG`'s value is V_S's `virtEF` (the `PUB` region's extension at `r_y` times its selector,
  plus the word `1`'s selector), on regions that are V_S's (`TdOk`).
* **`wireG_replays`**: `wireG` replays `dWiringT` from `wGP P` to `rRP P`: `r_y`, the matrix values `v_o` and the
  region values are its cells.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)

section
variable {c : Ctx} {M : Mem}

end

/-! The `DM` run lemmas restated with a non-`rfl` proof, so that `simp` rewrites with them by `Eq.mpr` steps: as
`rfl` lemmas, the kernel re-checked the rewritten run against `dZeroT`/`dWiringT` through `DM`'s `bind`. -/

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-! ## Values without assertions -/

end

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

end

end Lvm.Har
