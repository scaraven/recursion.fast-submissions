-- New for `flock-recursive` (BLUEPRINT §5.4 step 2, A.2; stage S-G).
-- RET-1: position-free declarations moved to `FRSoundnessCoreHide`.
import FRRS
import FRSumcheck
import FRSoundness4TailStep

/-!
# Ligerito's walk (BLUEPRINT §5.4 step 2): the bit-order bridge

* **`eqBits_eq_eq`** (A.2, S-D-m4): `FRRS.eqBits r ℓ x` (bit `v` of `x` against `r_v`,
  little-endian) is `FRMLE.eq` of the first `ℓ` coordinates of `r` and the cube point of `x`, in
  the same order (no reversal). The fold rounds bind bit `0` first, so the Ligerito point's
  coordinate `v` is the challenge of the round that folded bit `v`.

`ligerito_final` is in `FRSoundnessLigFinal` (stage S-G2): it needs the tail's dooms, which import
`FRSoundnessHide`, which imports this module.
-/

namespace FR

variable {R : Type*} [CommRing R]

end FR
