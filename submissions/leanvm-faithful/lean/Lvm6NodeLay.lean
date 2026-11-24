-- New for lvm6 (WP MBT, item 3; ST-1 since STARTUP-decision): the deployed layout `layQ6`, decoded from the
-- exporter's data (`Lvm6DataLay`, `LayP`'s lowercase hex), with the auxiliary blocks and constants by construction
-- (`auxOf6`, `cstOf6`). The solver that produced the data is `Lvm6NodeLaySolve` (exporter-only).
import Lvm6LayP
import Lvm6NodeAux
import Lvm6DataLay
import Lvm6NodeLayF

/-!
# The deployed layout (`layQ6`, ST-1)

* **`layP6`**: the layout's parameters, decoded from `Lvm6.Data.layHex` (`none` on a malformed string).
* **`layR6`**: the layout without its auxiliary blocks (`layOfP p [] cstOf6`); **`soR6`**: `qsig6`'s outputs at
  `pS layR6 ⟨nK, 0⟩`, the `BITS` rows' cells (the program before `Q_sig` does not read `lay.aux`).
* **`layQ6`** `= layOfP p (auxOf6 soR6 (auxBaseOfP p)) cstOf6` (built by SU2's
  equal fast forms, `layQOf_eq`) (`default` on a decode failure, which the guard's
  `lay.okB Q` rejects).

Nothing is proved about `layQ6`: every fact goes through the guard's Booleans (`staticOk6`) and NODE3's
construction lemmas (`auxFacts_of_constr`).
-/

set_option autoImplicit false

namespace Lvm6.Node.LayQ

open Lvm Lvm.Loop Lvm.Typed Lvm.QSig Lvm6.Node.Dep Lvm6.LayData
open Lvm6.Q (qsig6)

/-- **The deployed layout's parameters**, decoded. -/
def layP6 : Option LayP := LayP.ofHex Lvm6.Data.layHex

/-- The decoded layout without its auxiliary blocks. -/
def layR6 : Lay := match layP6 with
  | some p => layOfP p [] cstOf6
  | none => default

/-- `Q_sig`'s pointer on the decoded layout (SU2: by `pSF`, once per process; with `layR6`, the guard's pointer
cache, `nodeLayB3C layR6 pS0`). -/
def pS0 : Lvm.Loop.Build.Ptr := pSF layR6 ⟨nK, 0⟩

theorem pS0_eq : pS0 = pS layR6 ⟨nK, 0⟩ := by
  rw [pS0, pSF_eq]

/-- `qsig6`'s outputs on the decoded layout (the `BITS` rows' cells; SU2: at `pS0`). -/
def soR6 : SigOut × WalkC := (qsig6 sigI sigIl sbC pS0).1

theorem soR6_eq : soR6 = (qsig6 sigI sigIl sbC (pS layR6 ⟨nK, 0⟩)).1 := by
  rw [soR6, pS0_eq]

/-- The deployed layout of decoded parameters, from `r` (meant: `layR6`, whose fields other than `aux` it keeps, so
the blocks are converted once; SU2: `auxOf6F`, the bases' array built once). -/
def layQOf (r : Lay) : Option LayP → Lay
  | some p => { r with aux := auxOf6F soR6 (auxBaseArr p.auxBase.toArray) }
  | none => default

/-- `layQOf` at the layout without aux blocks is the reference construction (`auxOf6`, `auxBaseOfP`, `qsig6` at
`pS`, `qltData6`). -/
theorem layQOf_eq (o : Option LayP) : layQOf (match o with | some p => layOfP p [] cstOf6 | none => default) o =
    match o with
    | some p => layOfP p (auxOf6 (qsig6 sigI sigIl sbC (pS layR6 ⟨nK, 0⟩)).1 (auxBaseOfP p))
        [(zC, [0]), (qtC, Lvm6.Q.qltData6 P6 lay6)]
    | none => default := by
  cases o with
  | none => rfl
  | some p =>
    simp only [layQOf]
    rw [auxOf6F_eq, soR6_eq, cstOf6_eq]
    rfl

/-- **The deployed layout**: decoded, the auxiliary blocks and the constants by construction (`layQOf_eq`). -/
def layQ6 : Lay := layQOf layR6 layP6

end Lvm6.Node.LayQ
