-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's claims and openings: the circuit's typed claims
-- (`typedClaimsC`: `regClaimG`'s sum claims, the relayout's point claim, the mini-bus's table claims) are V_S's
-- (`typedClaimsN` and `tableClaimsR`), and the openings at ν = 23 in both shapes (`dOpenT`) read only the claims and
-- `C_main`'s tails. lvm2 roll 11 (M′ `S2GM`, R11-N): every claim is on `C_main`, which `dOpenT` opens alone.
import LvmQTypedHarB
import LvmQAsmHarTails

-- (GOLF2: 15 declarations that `certified` does not use moved verbatim to `LvmQTypedHarCOff`, outside its import closure.)

/-!
# The typed claims and the openings

* **`regClaimG_val`**: `regClaimG`'s sum claim, on regions that are V_S's, is V_S's region claim
  `⟨⟨ν, 0⟩, affW N s r_y, v⟩` (the selector `eq(r_y^{≥ log}, base ≫ log)` is `hiW`, a block's `eqAbove` is
  `eqAtF` of its target, `eqConstG`'s value is `eqAtF`).
* **`typedClaimsC_val`**: the circuit's typed claims are V_S's: first the relayout point claim on `S`, `σ′`'s region
  claim (and the mini-bus's `C_rec` table claims, none at S2GM); then the committed regions' and `KS`'s claims and the
  mini-bus's `C_main` table claims (M′: all on `C_main`).
* **`dOpenT_congr`**: `dOpenT` reads only the claims (commitment and claim) and `C_main`'s tails in the small shape.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped DM
open Lvm.TypedV (TNat NReg)

section
variable {c : Ctx} {M : Mem}

/-- `eqAtF` is `eqW` (characteristic 2). -/
theorem eqAtF_eqW : ∀ (r : List FE) (w : Nat), eqAtF r w = Loop.eqW r w
  | [], _ => rfl
  | a :: r, w => by
    rw [eqAtF, Loop.eqW, eqAtF_eqW r (w / 2), sub_eq_add_neg, CharTwo.neg_eq]

/-- A block's `eqAbove` is `eqAtF` of the point above it at its target's high bits. -/
theorem eqAbove_eqAtF (log off : Nat) (X : List FE) :
    (⟨log, off⟩ : Placement).eqAbove X = eqAtF (X.drop log) (off >>> log) := by
  rw [Placement.eqAbove, eqAtF_eqW, ← eqEval_selector, List.length_drop]

end

/-! ## The openings read each commitment's claims -/

-- (M′ `S2GM`, R11-N: B1's `dOpenT_P20` (`dOpenT P20 = Shape.dOpenZ P20`) is removed: `dOpenZ` still opens `C_rec`.)

/-! ## V_S's claim list against the circuit's -/

section
variable {M : Mem}

end

end Lvm.Har
