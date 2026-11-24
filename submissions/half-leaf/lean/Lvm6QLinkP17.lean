-- New for lvm6 (PORT17 L1): `Q_link`'s static checks at `P17` (`Lvm6QLinkP18`'s form, KDQ's memo pattern), the
-- openings' literal (`Lvm6QFast.opensTabP18`'s form) and the simulation's static facts (`Lvm6QDriveV.simOK_P18`'s).
import Lvm6QLink
import Lvm6QFast
import Lvm6QDriveV
import Lvm6P17Memo

/-!
# `Q_link`'s static checks at `P17` (FORMAT6 v2.6)

The plan of `P17`'s schedule (`planOf`, `phiVars = 43`, `|HDR| = 824`, the seed `a₀ ‖ HDR` of 856 bytes, 4106
entries) passes the bridge's stream facts (`streamOkL6`), its openings `opens6` match it (`opensOK`), and `qOk6`
holds at **every** layout with `m ≥ 17`, `K ≥ 6`, `aQ ≥ 11` (CD's `STREAM` at `P17` is one slot of `2^18` words,
`m = 18`). Each check rewrites `planOf P17` and `opensP17` to their literals (`planP17`, `opensTabP17`) and decides
the kernel-friendly copy of the check (`Lvm6QFast`), so no check rebuilds the plan.

**`cdConsts_P17`**: CD's constants at `P17` (P17-freeze §2.4) against the plan: the trace and its sponge padding
end below `σ'` (stream word `sB = 2^17`), `σ'` and `σ_leaf` (`2 · 597` words from `sB`) end inside the slot of
`2^18` words, and `childLink6`'s static hypotheses (`q₀` of 7 bytes, a seed of 856 bytes).

**`simOK_P17`**: the static facts of `V_S`'s simulation (`Lvm6QDriveV.simOK`) hold at `P17`.
-/

set_option autoImplicit false

namespace Lvm6

open Q

/-- **The openings of `P17`'s plan**, written out. -/
noncomputable def opensTabP17 : List Open6Q :=
  ([
    ⟨967, 110, 368, 13, 20, 947, 6, 2, 32⟩,
    ⟨2539, 45, 256, 13, 19, 2530, 6, 928, 128⟩,
    ⟨3193, 28, 256, 13, 18, 3188, 7, 2515, 96⟩,
    ⟨3604, 21, 256, 12, 17, 3600, 7, 3177, 96⟩,
    ⟨3888, 18, 256, 11, 16, 3885, 8, 3593, 96⟩] : List Open6Q)

/-- **The openings of `P17`'s plan are `opensTabP17`.** -/
theorem opens6_P17 : opens6 (lvOf P17) (itsOf P17) = opensTabP17 := by
  unfold itsOf
  rw [sched6_P17_eq]
  decide +kernel

end Lvm6

namespace Lvm6.Q

open Lvm.QLink

/-- The openings of `P17`'s plan. -/
def opensP17 : List Open6Q := opens6 (lvOf Lvm6.P17) (itsOf Lvm6.P17)

/-- **`opensP17` is the literal `opensTabP17`.** -/
theorem opensP17_eq : opensP17 = Lvm6.opensTabP17 := Lvm6.opens6_P17

theorem streamOkP17 : streamOkL6 (planOf Lvm6.P17) = true := by
  rw [Lvm6.planOf_P17_eq, streamOkL6_eq_F]
  decide +kernel

theorem opensOKP17 : opensOK (planOf Lvm6.P17) opensP17 = true := by
  rw [Lvm6.planOf_P17_eq, opensP17_eq, opensOK_eq_F]
  decide +kernel

theorem qOkSP17 : qOkS6 (planOf Lvm6.P17) opensP17 17 6 11 = true := by
  rw [Lvm6.planOf_P17_eq, opensP17_eq, qOkS6_eq_F]
  decide +kernel

/-- **`qOk6` at `P17`**, for every layout with `m ≥ 17`, `K ≥ 6`, `aQ ≥ 11` (CD at `P17`: `m = 18`). -/
theorem qOkP17 (lay : Layout6) (hm : 17 ≤ lay.m) (hK : 6 ≤ lay.K) (haQ : 11 ≤ lay.aQ) :
    qOk6 (planOf Lvm6.P17) opensP17 lay = true :=
  qOk6_of_S streamOkP17 (qOkS6_mono qOkSP17 hm hK haQ)

/-- **CD's constants against the plan at `P17`** (P17-freeze §2.4; `sB = 2^17`, slot `2^18`). -/
theorem cdConsts_P17 :
    Lvm6.P17.phiVars = 43 ∧ Lvm6.hdrLen Lvm6.P17 = 824 ∧ ((planOf Lvm6.P17).getD 0 default).len = 7 ∧
      ((planOf Lvm6.P17).getD 1 default).len = 856 ∧ 2 ≤ (planOf Lvm6.P17).length ∧
      17 * nBlk (hashedLen6 (planOf Lvm6.P17)) ≤ 2 ^ 17 ∧ 2 ^ 17 + 2 * 597 ≤ 2 ^ 18 := by
  rw [Lvm6.planOf_P17_eq]
  decide +kernel

/-- **The static facts hold at `P17`.** -/
theorem simOK_P17 : simOK Lvm6.P17 = true := by
  unfold simOK
  rw [planOf_P17.1, Lvm6.planOf_P17_eq, Lvm6.sched6_P17_eq]
  decide +kernel

end Lvm6.Q
