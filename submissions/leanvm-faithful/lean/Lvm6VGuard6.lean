-- New for lvm6 (ST-6): the deployed guard. NODE3's layout `layQ6` and ST-4's embedded class table `phiP6`, built
-- through INT5's `tyBaseOfQ` (the fast builds as fields; INT7: `tyBaseOfQM` on the shared prefix build `progMb6`);
-- `guard6` is evaluated once per process.
import Lvm6NodeTiQ
import Lvm6NodeFinal
import Lvm6VPhiP6

/-!
# The deployed guard (ST-6)

* **`base6`** = `tyBaseOfQ layQ6 phiP6` on the shared load-time prefix build `progMb6` (`tyBaseOfQM`, INT7);
  **`base6_eq`**: it is `tiOf6 phiP6`.
* **`guard6`** = `staticOk6 base6`. `VSF6 base6 sh = VSspec6 base6 sh` is `VSF6_eq base6 sh`.
* **`node6V_base6`**: NODE6's `node6V_tiOf6` at `base6`, from `guard6 = true`.
-/

set_option autoImplicit false

namespace Lvm6.V

/-- **The deployed `TyBase6`**: NODE3's layout and ST-4's embedded class table (untrusted, checked by `phiChk`). -/
def base6 : TyBase6 := Lvm6.Node.Ti.tyBaseOfQM Lvm6.Node.LayQ.layQ6 Lvm6.Node.Ti.progMb6 rfl phiP6

theorem base6_eq : base6 = Lvm6.Node.Ti.tiOf6 phiP6 := Lvm6.Node.Ti.tyBaseOfQM_eq _ _ _

/-- **The deployed guard.** -/
def guard6 : Bool := staticOk6 base6

end Lvm6.V

namespace Lvm6.Node.Asm

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm.Har Lvm.E2V LeanVM.Protocol
open Lvm6.QK Lvm6.QD Lvm6.Node Lvm.QSig Lvm.QLink
open Lvm6.Node.Dep Lvm6.Node.Mb
open Lvm6.Node.Ti (tiOf6)
open Lvm6.V (TyBase6 staticOk6 inst6 phasesV base6 guard6 base6_eq)
open LeanVM.Parameters

/-- `node6V_tiOf6` at any base equal to `tiOf6 P`. -/
theorem node6V_of_eq {B : TyBase6} {P : Lvm6.V.PT} (e : B = tiOf6 P) (h : staticOk6 B = true) :
    Stmt.node6V (VSasm (phasesV (inst6 B h))) (rest6 B h) (childOf6 trOfS σOfS) σlOfS := by
  subst e
  exact node6V_tiOf6 P h

/-- **`node6V` on the deployed circuit, from the deployed guard.** -/
theorem node6V_base6 (h : guard6 = true) :
    Stmt.node6V (VSasm (phasesV (inst6 base6 h))) (rest6 base6 h) (childOf6 trOfS σOfS) σlOfS :=
  node6V_of_eq base6_eq h

end Lvm6.Node.Asm
