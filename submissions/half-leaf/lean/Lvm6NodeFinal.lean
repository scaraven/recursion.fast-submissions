-- New for lvm6 (WP NODE6). The node theorem on the deployed circuit: NODE5a's decision (`dec_of_node_deployed`)
-- with its residuals discharged (`OutShape` by `Lvm6NodeFinS`, the tables by construction, the accumulator by the
-- relation and the header's well-formedness) and NODE5b's `NodeFacts6` (`nodeFacts6_static`).
import Lvm6NodeAsm
import Lvm6NodeFinD
import Lvm6NodeFinS

/-!
# `node6V` on the deployed circuit (WP NODE6)

For a layout `lay`, a class table `P` and `B = tyBaseOf lay P` (the deployed `tiOf6 P = tyBaseOf layQ6 P`):
* **`mbT_tyBaseOf`** (NODE5a's residual 2): the instance's mini-bus tables are `mbTD` of its layout, by
  construction (`tiOfL`).
* **`decAt_deployed`**: NODE5a's decision `DecAt (phasesV (inst6 B h)) B x q` from the guard, node mode, the
  header's point length (`HdrWF.pt_len`) and `rest6`; the rows by `segs_of_tgoodE`, `childLink6`'s inputs and the
  PoW rows as in `nodeFacts6_deployed`, `AccOkE` from `TGood6`, `OutShape` by `outShape_n6`.
* **`node6V_final`**: `Stmt.node6V (VSasm (phasesV (inst6 B h))) (rest6 B h) (childOf6 trOfS σOfS) σlOfS` from the
  guard `staticOk6 B = true` alone. **`node6V_tiOf6`**: the same at the deployed `tiOf6 P`.
-/

set_option autoImplicit false

namespace Lvm6.Node.Asm

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm.Har Lvm.E2V LeanVM.Protocol
open Lvm6.QK Lvm6.QD Lvm6.Node Lvm.QSig Lvm.QLink
open Lvm6.Ty (TInst6 TGoodE NoE3 toPair L6)
open Lvm6.Node.Dep Lvm6.Node.Mb
open Lvm6.Node.Ti (tyBaseOf tiOfL tiOfL_τ tiOf6)
open Lvm6.V (TyBase6 staticOk6 staticOk6_ok StaticOk6 inst6 phasesV)
open LeanVM.Parameters

/-- **NODE5a's residual 2 at the deployed instance**: the instance's mini-bus tables are the circuit's. -/
theorem mbT_tyBaseOf (lay : Lay) (P : Lvm6.V.PT) :
    (tyBaseOf lay P).Ti.mbT = mbTD (tyBaseOf lay P).Ti.lay := rfl

section Deployed

variable (lay : Lay) (P : Lvm6.V.PT) (h : staticOk6 (tyBaseOf lay P) = true)
include h

/-- **The decision on the deployed circuit**: from the guard, node mode, the header's point length and `rest6`. -/
theorem decAt_deployed (x : Hdr) (q : Stack) (hb : x.b = 1) (hx : x.accIn.1.length = Ty.phiVarsE)
    (hr : rest6 (tyBaseOf lay P) h x q) : DecAt (phasesV (inst6 (tyBaseOf lay P) h)) (tyBaseOf lay P) x q := by
  have hS := staticOk6_ok h
  have hok : (tiOfL lay).Ok := ⟨hS.lay, hS.one⟩
  have hA := hS.asm
  have hg : TGoodE (tiOfL lay) L6 (tiOfL_τ lay) (pwOf (tiOfL lay) (hdrBytes x)) (toPair q) := hr.2.1
  have hrow : ∀ blk ∈ (tiOfL lay).lay.aux, ∀ r ∈ blk.rows,
      ARowHolds (tiOfL lay).lay ((tiOfL lay).zOf L6 (pwOf (tiOfL lay) (hdrBytes x)) (toPair q).1 (toPair q).2) 0 r :=
    fun _ hblk ↦ blkRows_of_tgoodE (tiOfL lay) L6 (tiOfL_τ lay) _ (toPair q) hok hS.node.grd.noE3 hg hblk
  have hrd := readdOk6 lay P h hA _ q hg
  have hQ : (tiOfL lay).Q = progQ6 (tiOfL lay).lay := rfl
  have hQ' : (tiOfL lay).Q = Lvm.VF.toProgramF nK 0 (famQ6 (tiOfL lay).lay) := hQ
  have hOk := segs_of_tgoodE (famQ6 (tiOfL lay).lay) nK 0 (tiOfL lay) L6 (tiOfL_τ lay) _ (toPair q) hQ'
    hS.node.grd.wf hS.node.grd.twinsOk hS.node.grd.noE3 hok hrd hg
  set M := memTi (tiOfL lay) L6 (pwOf (tiOfL lay) (hdrBytes x)) (toPair q) with hMdef
  have hfl : M.k (pbC + 1) = 1 := flag_cell hS.node.pub L6 x (toPair q) hb
  have hgate : gateC.val M = 1 := by
    show FE.ofK (M.k (pbC + 1)) = 1
    rw [hfl]
    rfl
  have hks := sigKS_of_alias (outRel6 hr.1) (spongeLink6 hr.1) (ksAlias6 h (pwOf (tiOfL lay) (hdrBytes x)) q)
  have hin : QIn6 P6 opensP17 lay6 (wsOf M) M :=
    ⟨hfl, fun j hj ↦ (laneK_wsOf M hj).symm, fun _ hx ↦ qlt_of_cst hS.node.cst _ hx,
      posBits6_of hS.node.bits hrow⟩
  exact Fin.dec_of_node_deployed h rfl hOk hin (wsOf_length M) (ginj6 hA) (le_max_left _ _) (le_max_right _ _)
    pow_inj1024 hfl hks.1 (sigBits6P hS.node.bits hrow) hfl hks.2 (sigBitsC6P hS.node.bits hrow)
    (powRowsHold_of_tgoodE (tiOfL lay) L6 (tiOfL_τ lay) _ (toPair q) hok hS.node.grd.noE3 hg hS.node.pow)
    hx hr.2.2 (Fin.outShape_n6 hOk hgate) (mbT_tyBaseOf lay P)

/-- **`node6V` on the deployed circuit**, from the guard alone: the phases are V's (`phasesV` at the instance
the guard builds), the relation `rest6`, the readers read the stack's `STREAM` slot. -/
theorem node6V_final :
    Stmt.node6V (VSasm (phasesV (inst6 (tyBaseOf lay P) h))) (rest6 (tyBaseOf lay P) h)
      (childOf6 trOfS σOfS) σlOfS := by
  have H := node6V_Q (phasesV (inst6 (tyBaseOf lay P) h)) (fun x q ↦ HdrWF P17 x ∧ rest6 (tyBaseOf lay P) h x q)
    trOfS σOfS σlOfS fun x q hb ht hr ↦ nodeFacts6_static lay P h _ x q hb ht hr.2
      (decAt_deployed lay P h x q hb (hr.1.pt_len.trans (cdConsts_P17.1 : P17.phiVars = Ty.phiVarsE)) hr.2)
  intro vk c x q hwf hok hvk hg
  exact H vk c x q hwf hok hvk ⟨hg.1, hwf, hg.2⟩

end Deployed

/-- **`node6V_final` at the deployed `tiOf6 P`** (`tyBaseOf layQ6 P`). -/
theorem node6V_tiOf6 (P : Lvm6.V.PT) (h : staticOk6 (tiOf6 P) = true) :
    Stmt.node6V (VSasm (phasesV (inst6 (tiOf6 P) h))) (rest6 (tiOf6 P) h) (childOf6 trOfS σOfS) σlOfS :=
  node6V_final Lvm6.Node.LayQ.layQ6 P h

end Lvm6.Node.Asm
