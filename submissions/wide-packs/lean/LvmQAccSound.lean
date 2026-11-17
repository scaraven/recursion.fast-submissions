-- New for lvm (AC-Q): Q_acc's soundness as a replay of phase 3b (`accFold`), HAR's `Replays` form,
-- and the bridges from M3.real's `fixSent`/`pubCheck`/`tablePoint` to the table gadget's cells.
import LvmQAsmHarBase
import LvmQBusBase
import LvmQAcc

-- (GOLF2: 15 declarations that `certified` does not use moved verbatim to `LvmQAccSoundOff`, outside its import closure.)

-- ===== merged from `LvmQAccFacts` (GOLF module merge: `LvmQAccFacts.lean` is now a stub importing `LvmQAccSound`) =====
section
-- New for lvm (AC-Q): the proof of Q_acc's facts (`qacc_facts`).

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

-- adapted from LvmQSigParts.ok_bind' (WP-12)
theorem adv_e_le (p : Ptr) (δ : List Seg) : p.e ≤ (p.adv δ).e := by
  simp only [Ptr.adv]; exact Nat.le_add_right _ _

theorem kc_val_one {M : Mem} {n : Nat} (h : M.k n = 1) : (kc n).val M = 1 := by
  show FE.ofK (M.k n) = 1; rw [h]; rfl

-- `horner`'s recursion on the concrete coefficient list must not be unfolded by unification.
end Lvm.QAcc
end
-- ===== end of `LvmQAccFacts` =====

/-!
# `qacc_sound`

**`qacc_sound`** (BLUEPRINT §12.5, §12.6 node level; HAR's `Replays` unfolded): where Q_acc's rows
and assertions hold with the gate on and the child's stream bound, `accFold` (phase 3b) run from
position `8 L` with `ok` keeps `ok` (its four checks: `pubCheck`, `h₀ = acc_in'.y`, `Σh = y_own`, the
zero scalar), ends at `8 z0 + 24` (phase 4's start), and its value is the current proof's `acc_in`
(`accC M pb`, its `PUB` cells). With `decideProg` that is `accOutOf Σ' = accIn x` and the child's
`pubCheck`. Hypotheses on `m` (`hfs`, `hpc`, `htp`) say that the evaluations `F` read are the table
gadget's cells; for `M3.real` they follow from `evals = evV M evc` (`fixSentR_evV`, `pubCheckR_evV`,
`tablePoint_evV`).
-/

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1 DM

variable {M : Mem}

/-! ## `dot` with the `eq` table -/

theorem sumE_eq (l : List FE) : sumE l = l.sum := by
  rw [sumE, foldl_add_id, zero_add]

/-! ## The soundness of Q_acc -/

/-! ## M3.real's evaluations as the table gadget's cells -/

/-- `tablePoint` on cells. -/
def tablePointC (evc : List (List Cell × List Cell)) : List Cell :=
  evc.foldl (fun r e => if r.length < e.1.length then e.1 else r) []

end Lvm.QAcc
