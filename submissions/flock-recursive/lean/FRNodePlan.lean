-- New for `flock-recursive` (BLUEPRINT §10 changes 22 (e) and the plan-time ruling of 2026-10-28;
-- stage S-E11, track L-circ).
import FRVerifierImpl

/-!
# The node's plans as closed constants

The orchestrator's plan-time ruling (2026-10-28): the badge's `NS` times only the parse and `acc`
(`.contract/harness/badge/Verify.lean.in`, `timedCheck`), so the node's M plan is built **at process
start**, outside every check. A nullary definition is such a constant: the compiled module
initializes it once, when the process starts, before `main` (measured: `probe/PlanT.lean` reads the
walk template's closed constants in 1.8 ms; `probe/ColdWarm.lean` compares a cold process's first
check with its warm checks).

`implCN` is `implC` at these constants (`implCN_eq`, definitional): the certificate's `acc` (S-I)
should be stated with `implCN`, so that no check builds a plan.
-/

namespace FR
namespace Impl

/-- **The node's M plan** (`TEval.planOf` of the node's finals), built once at process start. -/
def nodePlan : TEval.Plan := TEval.planOf (finC finPf)

/-- **L's plan**, built once at process start. -/
def lPlan : TEval.LPlan := TEval.planL Layout.lRows

/-- **`implC` at the closed plans.** -/
def implCN : OpImpl := implCWith nodePlan lPlan

/-- `implCN` is `implC` of the node's finals and L's rows (any `κs₀`). -/
theorem implCN_eq (κs₀ : F) : implCN = implC (finC finPf) Layout.lRows κs₀ := rfl

end Impl
end FR
