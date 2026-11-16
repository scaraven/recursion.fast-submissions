-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Spine/Errors.lean` (formal rev 40f877dc) as `LvmSpineErrors` for lvm (WP-2).
/-
  LeanVM.Protocol.Spine.Errors

  Knowledge errors as fractions of the challenge field's size.
-/


import LvmSpineInstance

-- (GOLF2: 4 declarations that `certified` does not use moved verbatim to `LvmM3MidOff`, outside its import closure.)

/-!
# Errors as fractions of `|E|`

Every knowledge error of the protocol is a count of bad challenges over the size of the challenge
field `E`: `overE c = c / |E|`, with the arithmetic the slots' bounds use. The slots, their
schedules and the errors charged to each challenge are in `LeanVM.Protocol.Spine.Slots`.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters
open scoped NNReal

section

/-! ## Errors as fractions of `|E|` -/

/-- `c / |E|`. -/
noncomputable def overE (c : ℕ) : ℝ≥0 := (c : ℝ≥0) / (Fintype.card E : ℝ≥0)

end
end LeanVM.Protocol
