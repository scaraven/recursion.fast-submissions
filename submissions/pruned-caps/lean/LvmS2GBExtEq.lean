-- New for lvm2 MP-B cap pruning (CAP-X2, 2026-11-17; RE-FREEZE R3(c)): O5c at S2GB instantiated with S2GB's middle
-- phases (`midP (midMk 4 relocU20 (midGB Ti))`, L's `midSpecPinB20`/`midShapeB20`) and `kcertSFWBτ`.
-- DAY-0 STATEMENT: the `sorry` is tagged `-- CAP-FRZ X`; a proof never changes its statement.
import LvmS2GBMid
import LvmS2GBExt
import LvmS2GBExtProg
import LvmS2GBRefDec

/-!
# O5c at S2GB, instantiated

**`ext_eqB20`** (`ext_eqS20`'s twin): on proofs in the size range `SzB` whose expansion `fillB P20B π w` (any `w`)
S2GB's scheme `schemeSWB fmtB20` over S2GB's pinned middle phases accepts on a log of potential below `1`, `EXB20`
decodes a witness of the relation, or is the scheme's extractor (`kcertSFWBτ` with `midSpecPinB20`) on the
expansion; the left child is `childB20` (static part `‖` tail), the right leaf signs with `sigLeafS20` of the window.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q Lvm.E2U Lvm.E2S
  Lvm.XB
open Lvm.E2T (TNatT)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- `stB20`'s middle items are `midItemsL P20B` (`midItemsS_stS20`'s proof). -/
theorem midItemsS_stB20 : Lvm.XS.midItemsS stB20 = Lvm.VEq.midItemsL P20B := by
  have h4 : ((phases P20B).take 4).flatMap (·.2) = Lvm.VEq.commitI P20B ++ Lvm.VEq.midItemsL P20B := by
    rw [Lvm.VEq.phasesL_eq P20B rfl rfl]
    simp only [List.take_succ_cons, List.take_zero, Lvm.VEq.midItemsL, Lvm.VEq.typedIL, List.flatMap_cons,
      List.flatMap_nil, List.append_assoc, List.append_nil]
  have hn : stB20.nOpen = (Lvm.VEq.commitI P20B ++ Lvm.VEq.midItemsL P20B).length := by
    rw [← h4]; rfl
  unfold Lvm.XS.midItemsS
  rw [hn, show stB20.items = schedule P20B from rfl, Lvm.VEq.scheduleL_eq P20B rfl rfl,
    show Lvm.VEq.commitI P20B ++ (Lvm.VEq.midItemsL P20B ++ (Lvm.VEq.openMainI P20B ++ [])) =
      (Lvm.VEq.commitI P20B ++ Lvm.VEq.midItemsL P20B) ++ (Lvm.VEq.openMainI P20B ++ []) from
      (List.append_assoc _ _ _).symm, List.take_left, Lvm.VEq.commitI, List.singleton_append, List.drop_succ_cons,
    List.drop_zero]

/-- S2GB's middle items read, sample and commit nothing else (`RSItemsF`; the replay record's). -/
theorem rs_midItemsB : Lvm.ASM.RSItemsF (Lvm.VEq.midItemsL P20B) = true := by
  rw [← midItemsS_stB20]
  exact Lvm.ASM.replayOKB_stB20.rs

/-- **The pinned S2GB middle phases follow `stB20`'s middle items** (`midFollowsPS20`'s twin over `midGB`: the tape
over `contIvSB aSP`, the mini-bus at depth 13, `folP_midPB`). -/
theorem midFollowsPB20 (Ti : TInst) :
    Lvm.XS.MidFollowsS (Lvm.XS.midItemsS stB20) (midP (midMk 4 relocU20 (midGB Ti))) := fun x l a h ↦ by
  rw [(Lvm.VEq.fol_after (@Lvm.VEq.FolP.fol Lvm.VEq.capS Lvm.VEq.shpS Lvm.VEq.idxS _ _ _ _
    (Lvm.VEq.folP_midPB relocU20 Ti x) []) h).1, Lvm.CT.itemKindsS_eq, midItemsS_stB20]
  exact Lvm.VEq.atomKinds_atomsOf _ _ (Lvm.CT.noPos_of_rs _ rs_midItemsB)

/-- **CAP-FRZ X** (RE-FREEZE R3(c)): **`ext_eqB20`**: O5c at S2GB with S2GB's pinned middle phases. -/
theorem ext_eqB20 (VS : SProg) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : THypSB (N.inst Q lay))
    (hnode : ∀ vk, NodeSoundMLS loU VS vk (GoodSMB (N.inst Q lay) H) childB20 sigLeafS20) :
    ∀ vk L c π w, SzB π →
      Lvm.FS.Scheme.μ (kcertSFWBτ fmtB20 (midSpecPinB20 (N.inst Q lay) H) leadOpenM_le_τU
        (midShapeB20 (N.inst Q lay)) leadP_six
        (extJMLS loU loU_le (midShapeP_of (midShapeB20 (N.inst Q lay))) (hnode vk))) L < 1 →
      ((schemeSWB fmtB20 vk (PSWithM (midP (midMk 4 relocU20 (midGB (N.inst Q lay)))))).V c
        (fillB P20B π w)).runLog L = some true →
      (∃ wt, EXB20 (accV VS) c π L = some wt ∧ Rel (accV VS vk) c wt) ∨
        EXB20 (accV VS) c π L = (schemeSWB fmtB20 vk (PSWithM (midP (midMk 4 relocU20 (midGB (N.inst Q lay)))))).Ex
          (kcertSFWBτ fmtB20 (midSpecPinB20 (N.inst Q lay) H) leadOpenM_le_τU (midShapeB20 (N.inst Q lay)) leadP_six
            (extJMLS loU loU_le (midShapeP_of (midShapeB20 (N.inst Q lay))) (hnode vk))).ext c (fillB P20B π w) L := by
  intro vk L c π w hsz hμ hacc
  exact ext_eqB_gen (midSpecP_ofτ (midSpecPinB20 (N.inst Q lay) H) (midShapeB20 (N.inst Q lay)) leadP_six)
    leadOpenM_le_τU leadP_six (midShapeP_of (midShapeB20 (N.inst Q lay))) hnode (midFollowsPB20 (N.inst Q lay))
    (fun _ _ _ hp => Lvm.X.sFits_of_acc (S := subWith VS (EXB20 (accV VS)) extXB20)
      (by show qVlvm ≤ Lvm.X.qMax; decide) (by rw [subWith_acc]; exact hp))
    vk L c π w hsz hμ hacc

end Lvm.CT
