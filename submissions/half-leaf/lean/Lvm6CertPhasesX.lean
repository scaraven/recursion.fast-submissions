-- New for lvm6 (WP C3 of CERT, link 11's transport): NODE6's `node6V` moved from `phasesV` to the certificate's
-- phases `Φ6` along `VSasm_whirAtD`. (`open6XD_Φ6`, C4's `open6XD` at C3's terms, is in `Lvm6Cert` since
-- PORT17 C1, so that this module and `Lvm6CertExt` do not import the extractor's `Lvm6XDom`.)
import Lvm6CertPhases
import Lvm6NodeFinal

/-!
# `node6V` at `Φ6`

* **`Stmt.node6V_of_eq`**: `Stmt.node6V` reads its verifier only at `P17`, so it moves along `VS P17 = VS' P17`.
* **`node6V_phasesW`** (any layout `lay` and class table `P`), **`node6V_Φ6`** (the deployed `tiOf6 P`): NODE6's
  `node6V_final` / `node6V_tiOf6` for `VSasm (phasesV …)`, transported along `VSasm_whirAtD`.

`open6XD_Φ6` (`open6XD` at C3's terms) moved to `Lvm6Cert` (PORT17 C1).
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast Lvm.T

/-- **`node6V` reads its verifier only at `P17`**: it moves along an equality of the verifiers at `P17`. -/
theorem Stmt.node6V_of_eq {VS VS' : Shape → SProg} (e : VS P17 = VS' P17) {rest : Hdr → Stack → Prop}
    {childOf : Stack → Signed} {sigLeafOf : Stack → Sig} (H : Stmt.node6V VS rest childOf sigLeafOf) :
    Stmt.node6V VS' rest childOf sigLeafOf := fun vk => e ▸ H vk

end Lvm6

namespace Lvm6.V

open RecursionFast Lvm.T Lvm6.Node Lvm6.Node.Asm Lvm6.Node.Ti

/-- **`node6V` at the shape-keyed phases** for any layout and class table (`node6V_final` along `VSasm_whirAtD`). -/
theorem node6V_phasesW (lay : Lvm.Typed.Lay) (P : PT) (h : staticOk6 (tyBaseOf lay P) = true) :
    Stmt.node6V (VSasm (phasesW (inst6 (tyBaseOf lay P) h))) (Node.Asm.rest6 (tyBaseOf lay P) h)
      (childOf6 trOfS σOfS) σlOfS :=
  Stmt.node6V_of_eq (VSasm_whirAtD _) (node6V_final lay P h)

/-- **`node6V` at `Φ6`** for the deployed base `tiOf6 P` (`node6V_tiOf6` along `VSasm_Φ6`). -/
theorem node6V_Φ6 (P : PT) (h : staticOk6 (tiOf6 P) = true) :
    Stmt.node6V (VSasm (Φ6 (tiOf6 P) h)) (Node.Asm.rest6 (tiOf6 P) h) (childOf6 trOfS σOfS) σlOfS :=
  Stmt.node6V_of_eq (VSasm_Φ6 _ h) (node6V_tiOf6 P h)

end Lvm6.V
