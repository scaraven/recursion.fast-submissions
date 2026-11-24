-- New for lvm6 K2: the tree phase as `prog6` runs it (`Lvm6AsmProg.phases6`): `treeProgS29` with a guard
-- that also checks the four shape constants `Shape.treePart` reads (`κ`, `layers`, `prodLen`, `posRounds`).
import Lvm6KStmt

/-!
# The tree phase of `prog6`: `treeProgS6`

`treeProgS29` (`Lvm6KTreeSpec`) runs `treeProg (logN + 1)` when `M = logN + 7` and `4 ≤ logN ≤ 28`.
Its operations are those of `Shape.treePart` only when the shape's `κ`, `layers`, `prodLen` and
`posRounds` are `logN + 1`, `12`, `47` and `11` (true at `P18`), so the phase used by `prog6`
checks these too, and fails otherwise:

* **`treeProgS6 sh x`**: `treeProgS29 sh x` under the four shape facts (`treeProgS6_eq`, in
  `Lvm6KS6`), else a rejection. Proved in `Lvm6KS6`: `treeSpecS6 : Stmt.treeSpec treeProgS6`,
  `treeProgS6_follows` (ASM's `PhasesFollow.tree`), `treeProgS6_noCommit`.

A fast twin of the verifier (WP V1b) replays this guard: it rejects every shape where one of the
seven facts fails.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- The four shape constants `Shape.treePart` reads, at their `treeProg` values (`P18`: `κ = 19`,
`logN = 18`, 12 layers, a 47-scalar product, 11 position rounds). -/
def TreeShapeOK (sh : Lvm6.Shape) : Prop :=
  sh.κ = sh.logN + 1 ∧ sh.layers = 12 ∧ sh.prodLen = 47 ∧ sh.posRounds = 11

instance (sh : Lvm6.Shape) : Decidable (TreeShapeOK sh) := by
  unfold TreeShapeOK; infer_instance

/-- **The tree phase of `prog6`**: `treeProgS29`'s guard (`M = logN + 7`, `4 ≤ logN ≤ 28`) and the
four shape constants of `Shape.treePart`; then `treeProg (logN + 1)`, its output mapped by `toS`. -/
def treeProgS6 (sh : Lvm6.Shape) (x : Lvm6.Hdr) : VerifierProgram Lvm6.TreeOut :=
  if TreeShapeOK sh then
    if sh.M = sh.logN + 7 ∧ 4 ≤ sh.logN ∧ sh.logN ≤ 28 then
      treeProg (sh.logN + 1) >>= fun out ↦ pure (toS (sh.logN + 1) x.h out)
    else VerifierProgram.fail
  else VerifierProgram.fail

end Lvm6.K
