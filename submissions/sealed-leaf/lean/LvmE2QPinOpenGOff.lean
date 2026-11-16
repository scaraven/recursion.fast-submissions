/- `LvmE2QPinOpenGOff` (GOLF2 off-path move, group 48 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmE2QPinOpenG,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmE2QPinOpenG
import LvmQShapeC

-- ===== from `LvmE2QPinOpenG` =====

section
set_option autoImplicit false
namespace Lvm.Q2
open Lvm Lvm.Har Lvm.Shape Lvm.QShape
section Gen
variable {R : Type} [CommRing R] [Algebra FE R]

theorem fR_one (a : R) : fR a 1 = a := by
  rw [fR, map_one, add_comm (1 : R) a, add_assoc, ← two_mul, two_R, zero_mul, add_zero]

theorem eqEval_two (u v a b : FE) : eqEval [u, v] [a, b] = (1 + u + a) * (1 + v + b) := by
  simp [eqEval]

end Gen
end Lvm.Q2
end

section
set_option autoImplicit false
namespace Lvm.Q2
open Lvm Lvm.Har Lvm.Shape Lvm.QShape
section Gen
variable {R : Type} [CommRing R] [Algebra FE R]

theorem eOfNat_bit (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n

end Gen
end Lvm.Q2
end
