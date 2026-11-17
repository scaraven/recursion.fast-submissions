-- New for lvm2 E2F (slice S1, E2F-Q): the `E2` builder primitives the front gadgets use, with their semantics.
import LvmE2QGad
import LvmE2QFieldCorrect

-- (GOLF2: 4 declarations that `certified` does not use moved verbatim to `LvmE2QBuildOff`, outside its import closure.)

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

/-- The constant `k ∈ E2`, from any value `x` (`x + x + k`). -/
def const2 (k : FE2) (x : C2) : BM C2 := gE2lin 1 k x x

theorem add2_sem (c : Ctx) (M : Mem) (p : Ptr) (a b : C2) (h : SegsHold c M p (add2 a b p).2) :
    (add2 a b p).1.val M = a.val M + b.val M := by
  rw [add2, gE2lin_sem c M p 1 0 a b h]
  rw [show FE2.ofK 1 = 1 from rfl, one_mul, add_zero]

theorem const2_sem (c : Ctx) (M : Mem) (p : Ptr) (k : FE2) (x : C2) (h : SegsHold c M p (const2 k x p).2) :
    (const2 k x p).1.val M = k := by
  rw [const2, gE2lin_sem c M p 1 k x x h, show FE2.ofK 1 = 1 from rfl, one_mul]
  have h2 : (x.val M) + x.val M = 0 := by
    apply FE2.ext_coord <;> simp only [FE2.add_def, FE2.coord_false, FE2.coord_true] <;>
      exact fk_add_self _
  rw [h2, zero_add]

end Lvm.Loop.Build
