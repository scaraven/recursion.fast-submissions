-- New for `flock-recursive` (BLUEPRINT §5.4 step 2, A.2; stage S-G).
import FRRS
import FRMLE

/-!
# Ligerito's walk (BLUEPRINT §5.4 step 2): the bit-order bridge

* **`eqBits_eq_eq`** (A.2, S-D-m4): `FRRS.eqBits r ℓ x` (bit `v` of `x` against `r_v`,
  little-endian) is `FRMLE.eq` of the first `ℓ` coordinates of `r` and the cube point of `x`, in
  the same order (no reversal). The fold rounds bind bit `0` first, so the Ligerito point's
  coordinate `v` is the challenge of the round that folded bit `v`.

`ligerito_final` (the per-level induction) is not in this module yet (S-G RESULT, open items).
-/

namespace FR

variable {R : Type*} [CommRing R]

/-- **`eqBits_eq_eq`**: `eqBits` is `eq` at the cube point, coordinate `v` against bit `v`. -/
theorem eqBits_eq_eq (r : ℕ → R) (ℓ : ℕ) (u : Fin (2 ^ ℓ)) :
    eqBits r ℓ u = eq (fun v : Fin ℓ => r v) (cube u) := by
  rw [eq_cube, eqBits, bitSel,
    Finset.prod_range (fun i => if (u : ℕ).testBit i then r i else 1 - r i)]

end FR
