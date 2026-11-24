-- New for lvm6 (WP CA, Q_link; WP CA3: on CA2's `planOf` at FORMAT6 v2.5.3). `Q_link`'s static checks at
-- `P18`, decided.
import Lvm6QLink
import Lvm6QFormat
import Lvm6P18Memo
import Lvm6QFast

/-!
# `Q_link`'s static checks at `P18` (FORMAT6 v2.5.3, CA2's `planOf`)

The plan of `P18`'s schedule (`planOf`, `phiVars = 43`, `|HDR| = 824`, the seed `a₀ ‖ HDR` of 856 bytes)
passes the bridge's stream facts (`streamOkL6`), its openings `opens6` match it (`opensOK`), and `qOk6`
holds at **every** layout with `m ≥ 17`, `K ≥ 6`, `aQ ≥ 11`, whatever its cells (`sb`, `fg`, `qt`, `bb`,
`cp`): CD's `STREAM` is one slot of `2^19` words (`m = 19`), `sb` is the generator's cell of stream word 0.
`qOk6` is reached through `qOkS6` (`qOk6_of_S`), which skips the per-entry lane sums (quadratic in the
plan's length; the direct `decide` was killed after ≈ 4.5 min in WP CA).

**KDQ**: each check rewrites `planOf P18` and `opensP18` to their literals (`Lvm6P18Memo`) and decides the
kernel-friendly copy of the check (`Lvm6QFast`), so no check rebuilds the plan.

**`cdConsts_P18`**: CD's constants (CD-circuit §0) against the plan: the trace and its sponge padding end
below `σ'` (stream word `sB = 2^18`), `σ'` and `σ_leaf` (`2 · 597` words from `sB`) end inside the slot,
and `childLink6`'s static hypotheses (`q₀` of 7 bytes, a seed of `≥ 152` bytes inside the window).
-/

set_option autoImplicit false

namespace Lvm6.Q

open Lvm.QLink

/-- The openings of `P18`'s plan. -/
def opensP18 : List Open6Q := opens6 (lvOf Lvm6.P18) (itsOf Lvm6.P18)

/-- **`opensP18` is the literal `opensTabP18`** (KDQ's memo, `Lvm6P18Memo`). -/
theorem opensP18_eq : opensP18 = Lvm6.opensTabP18 := Lvm6.opens6_P18

theorem streamOkP18 : streamOkL6 (planOf Lvm6.P18) = true := by
  rw [Lvm6.planOf_P18_eq, streamOkL6_eq_F]
  decide +kernel

theorem opensOKP18 : opensOK (planOf Lvm6.P18) opensP18 = true := by
  rw [Lvm6.planOf_P18_eq, opensP18_eq, opensOK_eq_F]
  decide +kernel

theorem qOkSP18 : qOkS6 (planOf Lvm6.P18) opensP18 17 6 11 = true := by
  rw [Lvm6.planOf_P18_eq, opensP18_eq, qOkS6_eq_F]
  decide +kernel

/-- **`qOk6` at `P18`**, for every layout with `m ≥ 17`, `K ≥ 6`, `aQ ≥ 11` (CD: `m = 19`). -/
theorem qOkP18 (lay : Layout6) (hm : 17 ≤ lay.m) (hK : 6 ≤ lay.K) (haQ : 11 ≤ lay.aQ) :
    qOk6 (planOf Lvm6.P18) opensP18 lay = true :=
  qOk6_of_S streamOkP18 (qOkS6_mono qOkSP18 hm hK haQ)

/-- **CD's constants against the plan** (CD-circuit §0; `sB = 2^18`, slot `2^19`). -/
theorem cdConsts_P18 :
    Lvm6.P18.phiVars = 43 ∧ Lvm6.hdrLen Lvm6.P18 = 824 ∧ ((planOf Lvm6.P18).getD 0 default).len = 7 ∧
      ((planOf Lvm6.P18).getD 1 default).len = 856 ∧ 2 ≤ (planOf Lvm6.P18).length ∧
      17 * nBlk (hashedLen6 (planOf Lvm6.P18)) ≤ 2 ^ 18 ∧ 2 ^ 18 + 2 * 597 ≤ 2 ^ 19 := by
  rw [Lvm6.planOf_P18_eq]
  decide +kernel

end Lvm6.Q
