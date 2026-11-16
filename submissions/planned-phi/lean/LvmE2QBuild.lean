-- New for lvm2 E2F (slice S1, E2F-Q): the `E2` builder primitives the front gadgets use, with their semantics.
import LvmE2QGad
import LvmE2QFieldCorrect

/-!
# `E2` builder primitives

On `C2` values (two `K` cells, `LvmE2QGad`), from the twin rows `gE2mul`/`gE2lin` and `K` rows:

* `add2 a b = a + b`, `scale2 k a = k·a` (`k ∈ K` constant), `const2 k x = k` (`k ∈ E2` constant, from any
  `C2` value `x`), `copy2 a = a`: one twin pair each (`gE2lin`'s characteristic-2 tricks, as `LvmQBuild`'s `add`,
  `scale`, `const`, `copy`).

Each has its `_sem` lemma on a memory where the segments hold.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

theorem fk_add_self (a : FK) : a + a = 0 := by
  cases a with
  | mk v => show FK.mk (v ^^^ v) = FK.mk 0; rw [UInt64.xor_self]

/-- `a + b`. -/
def add2 (a b : C2) : BM C2 := gE2lin 1 0 a b

/-- `k·a` for a constant `k ∈ K` (`a + (k + 1)·a`). -/
def scale2 (k : FK) (a : C2) : BM C2 := gE2lin (k + 1) 0 a a

/-- The constant `k ∈ E2`, from any value `x` (`x + x + k`). -/
def const2 (k : FE2) (x : C2) : BM C2 := gE2lin 1 k x x

/-- A copy of `a` (`a + 0·a`). -/
def copy2 (a : C2) : BM C2 := gE2lin 0 0 a a

theorem add2_sem (c : Ctx) (M : Mem) (p : Ptr) (a b : C2) (h : SegsHold c M p (add2 a b p).2) :
    (add2 a b p).1.val M = a.val M + b.val M := by
  rw [add2, gE2lin_sem c M p 1 0 a b h]
  rw [show FE2.ofK 1 = 1 from rfl, one_mul, add_zero]

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

theorem const2_sem (c : Ctx) (M : Mem) (p : Ptr) (k : FE2) (x : C2) (h : SegsHold c M p (const2 k x p).2) :
    (const2 k x p).1.val M = k := by
  rw [const2, gE2lin_sem c M p 1 k x x h, show FE2.ofK 1 = 1 from rfl, one_mul]
  have h2 : (x.val M) + x.val M = 0 := by
    apply FE2.ext_coord <;> simp only [FE2.add_def, FE2.coord_false, FE2.coord_true] <;>
      exact fk_add_self _
  rw [h2, zero_add]

theorem copy2_sem (c : Ctx) (M : Mem) (p : Ptr) (a : C2) (h : SegsHold c M p (copy2 a p).2) :
    (copy2 a p).1.val M = a.val M := by
  rw [copy2, gE2lin_sem c M p 0 0 a a h, show FE2.ofK 0 = 0 from rfl, zero_mul, add_zero, add_zero]

end Lvm.Loop.Build
