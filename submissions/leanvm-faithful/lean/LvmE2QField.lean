-- New for lvm2 E2F (slice S1, E2F-Q; E2AC-DES §1.2): coordinates of the front field `E2 = K[X]/(X² + xX + 1)` on
-- machine words for LoopIR's `E2` rows. The field itself is E2F-V's `FE2` (LvmFieldE2Fast, canonical per
-- E2F-LEAD 2026-11-13); its ring and the bridge to Mathlib's `E2` are LvmFieldE2Correct.
import LvmFieldE2Fast

/-!
# Coordinates of `FE2`

`FE2` (E2F-V's `LvmFieldE2Fast`) is `re + im·X` with `X² = 1 + x·X`. LoopIR's `E2` rows write one coordinate each
(`coord`); `ext_coord` rebuilds a value from its two coordinates. Nothing here imports Mathlib: LoopIR's
interpreter runs this code.
-/

namespace Lvm

namespace FE2

/-- Coordinate `h` (`false`: `re`, `true`: `im`). -/
def coord (v : FE2) (h : Bool) : FK := if h then v.im else v.re

theorem add_def (a b : FE2) : a + b = ⟨a.re + b.re, a.im + b.im⟩ := rfl

@[simp] theorem coord_false (v : FE2) : v.coord false = v.re := rfl
@[simp] theorem coord_true (v : FE2) : v.coord true = v.im := rfl

theorem ext_coord {a b : FE2} (h0 : a.coord false = b.coord false) (h1 : a.coord true = b.coord true) :
    a = b := by
  cases a; cases b; simp only [coord_false, coord_true] at h0 h1; subst h0; subst h1; rfl

end FE2

end Lvm
