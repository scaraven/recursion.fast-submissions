-- New for `flock-recursive` (BLUEPRINT revision 4.1, §3; stage S-I, item 2): the badge's verifier
-- `V4F` on closed constants, and the knowledge error as a compiled number.
import FRVerifierC4
import FRVerifierImplNode4F
import FRNodePlan
import FRSoundnessCoreSteps

/-!
# The revision 4.1 verifier on closed constants (`V4F`), and `epsRQ`

`V4F := V4with VsegF VnodeF` is `VC4 implB (NI4F.implN4F fun _ => implB) N4c.cells4`
(**`V4F_eq`**, definitional per kind) with `implB := Impl.implCN` (the ops at the closed plans
`nodePlan`, `lPlan`, S-E13) and every kind's program and op implementation a **closed constant**
(`progS30` … `implNN8`): the compiled module builds them once, at process start, outside every
timed check (S-E13's ruling). `epsRQ` is `epsR` as the cast of a rational, which has compiled code
(**`epsRQ_eq`**). This module is the badge path's part of `FRSubmission4`; it does not import the
extractor (`FRX4Ext`).
-/

namespace FR.Sub4
open RecursionFast FR.Rev4
open scoped NNReal

/-! ## The ops and programs, as closed constants -/

/-- **The base ops**: `implC` at the closed plans (`Impl.implCN_eq`). -/
def implB : OpImpl := Impl.implCN

/-- The segment ops (`implSeg`). -/
def implS : OpImpl := implSeg implB

/-- The node ops of each kind (INT-9's `implN4F` over `implB`). -/
def implNN2 : OpImpl := NI4F.implN4F (fun _ => implB) .N2
def implNN4 : OpImpl := NI4F.implN4F (fun _ => implB) .N4
def implNN8 : OpImpl := NI4F.implN4F (fun _ => implB) .N8

/-- The segment programs. -/
def progS30 : VProg := progSeg .L30
def progS31 : VProg := progSeg .L31
def progS32 : VProg := progSeg .L32

/-- The node programs at their public cells. -/
def progNN2 : VProg := progNode .N2 (N4c.cells4 .N2)
def progNN4 : VProg := progNode .N4 (N4c.cells4 .N4)
def progNN8 : VProg := progNode .N8 (N4c.cells4 .N8)

/-- A segment kind's program. -/
def progSK : SegKind → VProg
  | .L30 => progS30 | .L31 => progS31 | .L32 => progS32

/-- A node kind's program. -/
def progNK : NodeKind → VProg
  | .N2 => progNN2 | .N4 => progNN4 | .N8 => progNN8

/-- A node kind's ops. -/
def implNK : NodeKind → OpImpl
  | .N2 => implNN2 | .N4 => implNN4 | .N8 => implNN8

/-- **The segment verifiers** on the closed constants. -/
def VsegF : SegProgs := fun κ vk c π => runStmt implS (progSK κ) (.ofSeg κ) ⟨vk, c, π⟩

/-- **The node verifiers** on the closed constants. -/
def VnodeF : NodeProgs := fun κ vk c π => runStmt (implNK κ) (progNK κ) (.ofNode κ) ⟨vk, c, π⟩

/-- **The verifier** the badge runs. -/
def V4F : Digest → Digest → Proof → OProg Bool := V4with VsegF VnodeF

theorem VsegF_eq : VsegF = VsegC implB := by
  funext κ vk c π; cases κ <;> rfl

theorem VnodeF_eq : VnodeF = VnodeC (NI4F.implN4F fun _ => implB) N4c.cells4 := by
  funext κ vk c π; cases κ <;> rfl

/-- **`V4F` is X4's verifier** `VC4 implB (implN4F (fun _ => implB)) cells4`. -/
theorem V4F_eq : V4F = VC4 implB (NI4F.implN4F fun _ => implB) N4c.cells4 := by
  rw [V4F, VC4, VsegF_eq, VnodeF_eq]

/-! ## The numbers -/

/-- **The knowledge error as a rational cast** (compiled; `epsRQ_eq`). -/
def epsRQ : ℝ≥0 := ((15 / 2 ^ 124 : ℚ≥0) : ℝ≥0)

theorem epsRQ_eq : epsRQ = Snd.epsR := by
  unfold epsRQ Snd.epsR; push_cast; rfl

end FR.Sub4
