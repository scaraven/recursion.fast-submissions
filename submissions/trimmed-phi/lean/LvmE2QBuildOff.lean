/- `LvmE2QBuildOff` (GOLF2 off-path move, group 43 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmE2QBuild,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmE2QBuild

-- ===== from `LvmE2QBuild` =====

section
set_option autoImplicit false
namespace Lvm.Loop.Build
open Lvm.Loop

/-- `k·a` for a constant `k ∈ K` (`a + (k + 1)·a`). -/
def scale2 (k : FK) (a : C2) : BM C2 := gE2lin (k + 1) 0 a a

end Lvm.Loop.Build
end

section
set_option autoImplicit false
namespace Lvm.Loop.Build
open Lvm.Loop

/-- A copy of `a` (`a + 0·a`). -/
def copy2 (a : C2) : BM C2 := gE2lin 0 0 a a

end Lvm.Loop.Build
end

section
set_option autoImplicit false
namespace Lvm.Loop.Build
open Lvm.Loop

theorem scale2_sem (c : Ctx) (M : Mem) (p : Ptr) (k : FK) (a : C2) (h : SegsHold c M p (scale2 k a p).2) :
    (scale2 k a p).1.val M = FE2.ofK k * a.val M := by
  rw [scale2, gE2lin_sem c M p (k + 1) 0 a a h, add_zero]
  have hk : FE2.ofK (k + 1) = FE2.ofK k + 1 := by
    apply FE2.ext_coord <;> simp [FE2.ofK, FE2.add_def] <;> rfl
  rw [hk]
  have h2 : (a.val M) + a.val M = 0 := by
    apply FE2.ext_coord <;> simp only [FE2.add_def, FE2.coord_false, FE2.coord_true] <;>
      exact fk_add_self _
  linear_combination h2

end Lvm.Loop.Build
end

section
set_option autoImplicit false
namespace Lvm.Loop.Build
open Lvm.Loop

theorem copy2_sem (c : Ctx) (M : Mem) (p : Ptr) (a : C2) (h : SegsHold c M p (copy2 a p).2) :
    (copy2 a p).1.val M = a.val M := by
  rw [copy2, gE2lin_sem c M p 0 0 a a h, show FE2.ofK 0 = 0 from rfl, zero_mul, add_zero, add_zero]

end Lvm.Loop.Build
end
