-- New for lvm6 (WP C3 of CERT, link 11's transport and the fit with C4's `open6X18D`): NODE6's `node6V` moved from
-- `phasesV` to the certificate's phases `Φ6` along `VSasm_whirAt18`, and `open6X18D` applied to C3's terms.
import Lvm6CertPhases
import Lvm6NodeFinal
import Lvm6XDom

/-!
# `node6V` at `Φ6`, and `open6X18D` at `Φ6`

* **`Stmt.node6V_of_eq`**: `Stmt.node6V` reads its verifier only at `P18`, so it moves along `VS P18 = VS' P18`.
* **`node6V_phasesW`** (any layout `lay` and class table `P`), **`node6V_Φ6`** (the deployed `tiOf6 P`): NODE6's
  `node6V_final` / `node6V_tiOf6` for `VSasm (phasesV …)`, transported along `VSasm_whirAt18`.
* **`open6X18D_Φ6`**: `open6X18D` with `H := phaseSpecs6 B h`, `HG := openGood6 B h`, `hPF := phasesFollow6 B h`,
  `hw := rfl`; left as hypotheses: C5's `Xe` and its extraction map `hX`.
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast Lvm.T

/-- **`node6V` reads its verifier only at `P18`**: it moves along an equality of the verifiers at `P18`. -/
theorem Stmt.node6V_of_eq {VS VS' : Shape → SProg} (e : VS P18 = VS' P18) {rest : Hdr → Stack → Prop}
    {childOf : Stack → Signed} {sigLeafOf : Stack → Sig} (H : Stmt.node6V VS rest childOf sigLeafOf) :
    Stmt.node6V VS' rest childOf sigLeafOf := fun vk => e ▸ H vk

end Lvm6

namespace Lvm6.V

open RecursionFast Lvm.T Lvm6.Node Lvm6.Node.Asm Lvm6.Node.Ti

/-- **`node6V` at the shape-keyed phases** for any layout and class table (`node6V_final` along `VSasm_whirAt18`). -/
theorem node6V_phasesW (lay : Lvm.Typed.Lay) (P : PT) (h : staticOk6 (tyBaseOf lay P) = true) :
    Stmt.node6V (VSasm (phasesW (inst6 (tyBaseOf lay P) h))) (Node.Asm.rest6 (tyBaseOf lay P) h)
      (childOf6 trOfS σOfS) σlOfS :=
  Stmt.node6V_of_eq (VSasm_whirAt18 _) (node6V_final lay P h)

/-- **`node6V` at `Φ6`** for the deployed base `tiOf6 P` (`node6V_tiOf6` along `VSasm_Φ6`). -/
theorem node6V_Φ6 (P : PT) (h : staticOk6 (tiOf6 P) = true) :
    Stmt.node6V (VSasm (Φ6 (tiOf6 P) h)) (Node.Asm.rest6 (tiOf6 P) h) (childOf6 trOfS σOfS) σlOfS :=
  Stmt.node6V_of_eq (VSasm_Φ6 _ h) (node6V_tiOf6 P h)

end Lvm6.V

namespace Lvm6.X

open RecursionFast Lvm.T Lvm.X Lvm.FS Lvm6.V

/-- **`open6X18D` at `Φ6`**: C3's phase inputs fill `H`, `HG`, `hPF` and `hw`; what is left is C5's `Xe` with its
extraction map `hX`. -/
theorem open6X18D_Φ6 (B : TyBase6) (h : staticOk6 B = true) {VS : Shape → SProg}
    (Xe : ∀ vk, Ext6 (schemeOf (prog6 (Φ6 B h)) P18 vk) (Rel (accV (VS P18) vk))
      (G6 (fun _ q => SP.SGood6 q) (fun x q => Ty.TGood6 (inst6 B h x) q)))
    (hX : ∀ vk, (Xe vk).ext = ExtSpec6 (Whir.I6 P18)) :
    XOpen6D (VS P18) (prog6 (Φ6 B h)) (EX6D (accV (VS P18)) (.seq fillIR18 (descX6 (Lv18 F18) finX18)))
      (extX6 (.seq fillIR18 (descX6 (Lv18 F18) finX18))) :=
  open6X18D (phaseSpecs6 B h) (openGood6 B h) (phasesFollow6 B h) Xe rfl hX

end Lvm6.X
