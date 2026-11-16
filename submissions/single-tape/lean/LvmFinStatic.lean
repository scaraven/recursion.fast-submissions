-- New for lvm (WP-16a2, BLUEPRINT A24): the static facts of the P20 node program that the kernel
-- cannot evaluate (they run the builder through HAR's table gadget), as one closed Bool `staticOkB`
-- that the compiled `V` checks once per process (`LvmFinGuard`), and their soundness lemmas.
import LvmQAsmV
import LvmQAsmInbCore
import LvmQAsmHarMain
import LvmM3Check
import LvmFinSegs

/-!
# `staticOkB` (A24)

Bundled (natively evaluated, never in the kernel): Q_arith has no `readd` (`hna`), the program check
(`AuxStatic.wf`, through QL's one-pass `segsOk`), the groups' tiling (`AuxStatic.grp`), the cell bound
(`AuxStatic.inj`), and `harith_core`'s claim checks `hwr`/`hwm` (`ClaimsWF`) and, roll 7, `hwz`
(`zChk`: the claims in both shapes, every regular block `RegP`, the small layout's fit). Each is read on the
linear-time builders of V-PERF (`VF.qprogF`, `VF.qarithF`, `VF.phases47F`, equal to the node
program's, `qprogF_eq`, `qarithF_eq`, `phases47F_eq`). The claim lists are built once (`parts20`) for
both `ClaimsWF` and `zChk` (`qarithCs_parts`, `qarithZ_parts`). Every other static fact stays a kernel
proof.
-/

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.M3 Lvm.Har

theorem phases47F_eq (C : QCfg) : VF.phases47F C = phases47 C := by
  unfold VF.phases47F phases47
  rw [VF.tapeGadgetF_eq, VF.gkrGadgetF_eq]

theorem qarithF_eq (C : QCfg) : VF.qarithF C = qarith C := by
  unfold VF.qarithF qarith
  rw [phases47F_eq]

theorem qprogF_eq (C : QCfg) : VF.qprogF C = qprogC C := by
  unfold VF.qprogF qprogC
  rw [qarithF_eq]

/-! The builder runs once (closed constants, evaluated at start-up, shared by the checks):
Q_link's and Q_sig's segments, the pointer `p2C cfg20`, phases 4–7 (`VF.phases47F`), the rest. -/

/-- Q_link's segments at `P20`. -/
def segL20 : List Seg := (Lvm.QLink.qlink cfg20.p (lay cfg20) ⟨nK cfg20, 0⟩).2
/-- Q_sig's segments at `P20`. -/
def segS20 : List Seg := (Lvm.QSig.qsig (sigIn cfg20) (p1C cfg20)).2
/-- Q_arith's pointer. -/
def p2F : Ptr := p2C cfg20
/-- Phases 4–7 (linear-time GKR builder). -/
def ph47F : P47Out × List Seg := VF.phases47F cfg20 p2F
/-- The rest of Q_arith. -/
def restF : Unit × List Seg := qarithRest cfg20 ph47F.1 (p2F.adv ph47F.2)

theorem arith_segs : ph47F.2 ++ restF.2 = (VF.qarithF cfg20 (p2C cfg20)).2 := rfl

theorem prog_segs : segL20 ++ (segS20 ++ (ph47F.2 ++ restF.2)) = (VF.qprogF cfg20 ⟨nK cfg20, 0⟩).2 := rfl

/-- Q_arith has no `readd`. -/
def okNoRd20 : Bool := noReaddSegs (ph47F.2 ++ restF.2)

/-- The program check, in one pass over the segments. -/
def okWf20 : Bool := segsOkF ⟨nK cfg20, 0⟩ (segL20 ++ (segS20 ++ (ph47F.2 ++ restF.2)))

/-- The placement record's groups tile the program's pieces (`VF.piecesF`, linear time). -/
def okGrp20 : Bool := grpOkCore ((VF.piecesF M3.Q20).map (pinfo M3.Q20)) data20.groups

/-- Fewer than `2^64 − 1` cells of each type. -/
def okInj20 : Bool := decide (max (M3.Q20.cells .K) (M3.Q20.cells .E) < 2 ^ 64 - 1)

section Parts

open Lvm.Q1 DM

/-- The zero cell and `claimsC`'s five lists (tables, tape, `KS`, `KS`'s outputs, the `KS` link). -/
abbrev Parts : Type := Cell × List CClaim × List CClaim × List CClaim × List CClaim × List CClaim

/-- **Q_arith's claim lists up to phase 8**, as `qarithCs` and `qarithZ` build them (the same builder,
returning the parts both read). -/
def qarithParts (C : QCfg) (D : QData) (o : P47Out) : BM Parts := do
  let g := kc (pbB C)
  let p := C.p
  let S := shapesOf C D
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let _zK ← const .K 0 (kc 0)
  let ksB : Placement := ⟨p.ksLog + slotLog, (layout0 p).ks⟩
  let bus ← busG p z one g (busPos p)
  let tab ← tabG S p.tableRounds (tabPos p) z one g bus
  Lvm.QAcc.qacc (accInOf C S tab z)
  let rgK ← ringGkr (p.ksLog - 4) (Har.aLane p 6) z.n
  let clK ← ksLinkG p (Har.aLane p 7) z.n one.n
  pure (z, tabClaims S tab z, tapeClaimsC p z.n one.n o, kClaimsC ksB o.kko rgK,
    ksOutC p o.rk o.vk z.n one.n, clK)

/-- `qarithCs`' list from the parts. -/
def csOf (r : Parts) : List CClaim := claimsC r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2

/-- `qarithZ`'s check from the parts. -/
def zOf (r : Parts) : Bool := zChk r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2

theorem qarithCs_parts (C : QCfg) (D : QData) (o : P47Out) (q : Ptr) :
    (qarithCs C D o q).1 = csOf (qarithParts C D o q).1 := rfl

theorem qarithZ_parts (C : QCfg) (D : QData) (o : P47Out) (q : Ptr) :
    (qarithZ C D o q).1 = zOf (qarithParts C D o q).1 := by
  -- not `rfl`: the elaborator's unifier spends 20 s unfolding `zChk` there
  simp only [qarithZ, qarithParts, zOf, bind_apply, pure_apply]

end Parts

/-- Q_arith's claim lists at `P20`, built once for `okClaims20` and `okZ20`. -/
def parts20 : Parts := (qarithParts cfg20 data20 ph47F.1 (p2F.adv ph47F.2)).1

/-- Q_arith's claim lists (`harith_core`'s `hwr`, `hwm`). -/
def okClaims20 : Bool :=
  let cs := csOf parts20
  ClaimsWF P20.nuRec (onCom cs .crec) && ClaimsWF P20.nuMain (onCom cs .main)

/-- Q_arith's claims in both shapes (roll 7, CR-Q: `harith_core`'s `hwz`). -/
def okZ20 : Bool := zOf parts20

/-- **The static guard** (A24): every bundled check. -/
def staticOkB : Bool := okNoRd20 && okWf20 && okGrp20 && okInj20 && okClaims20 && okZ20

/-! ## Soundness of the guard -/

/-- The bundled facts, in their consumers' forms. -/
structure StaticFacts : Prop where
  hna : noReaddSegs (qarith cfg20 (p2C cfg20)).2 = true
  wf : (Q cfg20).wf = true
  grp : GrpOk (Q cfg20) data20.groups
  inj : GInj (max ((Q cfg20).cells .K) ((Q cfg20).cells .E))
  hwr : ClaimsWF cfg20.p.nuRec
    (onCom (qarithCs cfg20 data20 (phases47 cfg20 (p2C cfg20)).1
      ((p2C cfg20).adv (phases47 cfg20 (p2C cfg20)).2)).1 .crec) = true
  hwm : ClaimsWF cfg20.p.nuMain
    (onCom (qarithCs cfg20 data20 (phases47 cfg20 (p2C cfg20)).1
      ((p2C cfg20).adv (phases47 cfg20 (p2C cfg20)).2)).1 .main) = true
  hwz : (qarithZ cfg20 data20 (phases47 cfg20 (p2C cfg20)).1 ((p2C cfg20).adv (phases47 cfg20 (p2C cfg20)).2)).1 = true

/-- **What `staticOkB = true` gives.** -/
theorem staticFacts (h : staticOkB = true) : StaticFacts := by
  simp only [staticOkB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hn, hw⟩, hg⟩, hi⟩, hc⟩, hz⟩ := h
  have hQ : M3.Q20 = Q cfg20 := M3.Q20_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← qarithF_eq, ← arith_segs]; exact hn
  · exact toProgram_wf _ _ _ (by rw [← qprogF_eq, ← prog_segs, ← segsOkF_eq]; exact hw)
  · rw [← hQ]; exact grpOk_of_B (by rw [grpOkB, ← VF.piecesF_eq]; exact hg)
  · have hm : max ((Q cfg20).cells .K) ((Q cfg20).cells .E) < 2 ^ 64 - 1 := by
      rw [← hQ]; exact of_decide_eq_true hi
    intro a b ha hb hab
    exact FK.FKx_pow_inj (by omega) (by omega) hab
  · simp only [okClaims20, parts20, ph47F, p2F, Bool.and_eq_true, phases47F_eq, ← qarithCs_parts] at hc
    exact hc.1
  · simp only [okClaims20, parts20, ph47F, p2F, Bool.and_eq_true, phases47F_eq, ← qarithCs_parts] at hc
    exact hc.2
  · simp only [okZ20, parts20, ph47F, p2F, phases47F_eq, ← qarithZ_parts] at hz; exact hz

end Lvm.Fin
