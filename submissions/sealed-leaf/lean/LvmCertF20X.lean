-- New for lvm2 slice S1 (E2-F, E2F-L, 2026-11-13): S2GF's executable extractor and its agreement (`ext_eqF20`), the
-- instance at `stF20` of the stage-generic extractor (`LvmXS*`). The `sorry`s are frozen statements tagged with their
-- owner; a proof never changes its statement, a needed change is reported old → new.
import LvmCertF20
import LvmXSTop
import LvmXSKinds
import LvmXSExtEq
import LvmNodeSoundTr
import LvmFinGuard
import LvmXSKindsEq
import LvmXSChild
import LvmE2VRefinesF
import LvmXSChildOff
import LvmXSComputesOff
import LvmE2VWidthsFOff

/-!
# S2GF's extractor

* `extXF20`, `EXF20 A`: the stage-generic program and specification at `stF20`; **`computesXF20`**,
  `extXF20_size`, `EXF20_W`; `extF20 VS : ExtF20`;
* `replayOK_stF20` (one kernel evaluation of `replayOkB stF20`), `midItemsS_stF20` (the middle items are V's
  `midItemsF`), **`midFollowsPF20`** (from V's `folP_midPF`);
* **`ext_eqF20`**: `OpenF20`'s `ext_eq` at `E = EXF20 (accV VS)` and `child = childF20`, from V's pair form and the
  node soundness.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-! ## The program -/

/-- **S2GF's extractor program.** -/
def extXF20 : XProg := extXS stF20

/-- **S2GF's extractor specification** (`A`: the certificate's `S.acc`). -/
def EXF20 (A : RecursionFast.Digest → RecursionFast.Digest → Signed → Bool) :
    RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit :=
  EXS stF20 A

/-! ## The middle phases' shape -/

theorem P20F_withF : P20F.withF accVF = P20F := rfl

set_option maxRecDepth 200000 in
/-- **S2GF's replay facts**: one kernel evaluation of the run-length checker `replayOkR` at the split of `P20F`'s
phases after the seventh (the root cap and the middle phases, then `openMain`). -/
theorem replayOK_stF20 : Lvm.ASM.ReplayOK stF20 :=
  Lvm.ASM.replayOK_ofR (pre := ((phases P20F).take 7).flatMap (·.2)) (rest := ((phases P20F).drop 7).flatMap (·.2))
    (by show schedule P20F = _; rw [schedule, ← List.flatMap_append, List.take_append_drop]) rfl
    (by decide +kernel)

/-- `stF20`'s middle items are V's (`midItemsF`: the pin, the typed phases, the `E2` front). -/
theorem midItemsS_stF20 : midItemsS stF20 = Lvm.VEq.midItemsF P20F := by
  have h7 : ((phases P20F).take 7).flatMap (·.2) = Lvm.VEq.commitI P20F ++ Lvm.VEq.midItemsF P20F := by
    rw [Lvm.VEq.phasesF_eq P20F rfl]
    simp only [List.take_succ_cons, List.take_zero, Lvm.VEq.midItemsF, Lvm.VEq.typedIX, List.flatMap_cons,
      List.flatMap_nil, List.append_assoc, List.append_nil]
  have hn : stF20.nOpen = (Lvm.VEq.commitI P20F ++ Lvm.VEq.midItemsF P20F).length := by
    rw [← h7]; rfl
  unfold midItemsS
  rw [hn, show stF20.items = schedule P20F from rfl, Lvm.VEq.scheduleF_eq P20F rfl,
    show Lvm.VEq.commitI P20F ++ (Lvm.VEq.midItemsF P20F ++ (Lvm.VEq.openMainI P20F ++ [])) =
      (Lvm.VEq.commitI P20F ++ Lvm.VEq.midItemsF P20F) ++ (Lvm.VEq.openMainI P20F ++ []) from
      (List.append_assoc _ _ _).symm, List.take_left, Lvm.VEq.commitI, List.singleton_append, List.drop_succ_cons,
    List.drop_zero]

/-- **The pinned middle phases follow `stF20`'s middle items** (V's `folP_midPF`, the mini-bus's numbers from
`TRefHypX`). -/
theorem midFollowsPF20 (N : TypedV.TNat) (Q : Lvm.Loop.Program) (lay : Lay) (HR : Lvm.VEq.TRefHypX N Q lay) :
    MidFollowsS (midItemsS stF20) (midP (midM reloc20 (midF₂ (N.inst Q lay)))) := fun x l a h ↦ by
  obtain ⟨hl, hr, he, -, -⟩ := HR.toT.fits
  have hrs := replayOK_stF20.rs
  rw [midItemsS_stF20] at hrs
  rw [(Lvm.VEq.fol_after (@Lvm.VEq.FolP.fol Lvm.VEq.capS Lvm.VEq.shpS Lvm.VEq.idxS _ _ _ _
    (Lvm.VEq.folP_midPF reloc20 (N.inst Q lay) hl Lvm.VEq.busDepth_P20 hr he x) []) h).1, itemKindsS_eq,
    midItemsS_stF20, P20F_withF]
  exact Lvm.VEq.atomKinds_atomsOf _ _ (noPos_of_rs _ hrs)

-- `itemKindsS_eq`, `noPos_of_rs` are in `LvmXSKindsEq` (moved, lvm2 U-TAPE).

/-! ## The agreement -/

/-- `stF20`'s read widths are S2GF's (`readWidthsF`). -/
theorem readWidthsS_stF20 : readWidthsS stF20 = readWidthsF P20F accVF := by
  unfold readWidthsS readWidthsF
  rw [scheduleF, P20F_withF]
  exact List.flatMap_congr fun it _ => by cases it <;> rfl

/-- **S2GF's format agrees with its stage.** -/
theorem fmtOK_stF20 : Lvm.ASM.FmtOK stF20 fmtF20 :=
  ⟨fun n => by show rwF20 n = _; rw [rwF20, readWidthsS_stF20], rfl, rfl, rfl, rfl, rfl⟩

/-- **The stream block `EXS` reads is `childF20`'s** (`childW_stream20` at `stF20`). -/
theorem childWS_stream20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) (hl : out.length = 2 ^ 20) :
    childWS stF20 (Lvm.X.wStreamM π out) = childF20 x out := by
  unfold childF20
  congr 1
  funext i
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    omega
  unfold Lvm.X.wStreamM sIdx
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi]
    by_cases hs : Lvm.Shape.small x = true
    · rw [ite_eq_left (hc.2 hs), ite_eq_left hs,
        show 2 * (CMain.sOff20s + i) - Lvm.X.winLo * 2 ^ 17 = 2 * i by simp only [CMain.sOff20s, Lvm.X.winLo]; omega]
    · rw [ite_eq_right (fun h => hs (hc.1 h)), ite_eq_right hs,
        show CMain.sOff20 + i - Lvm.X.winLo * 2 ^ 17 = 2 ^ 19 + i by simp only [CMain.sOff20, Lvm.X.winLo]; omega]
  · rw [ite_eq_right hi]
    rw [List.getD_eq_default _ _ (by split_ifs <;> omega)]

/-- **`ext_eqF20`**: on accepted `S` proofs over good logs, S2GF's extractor decodes or is the specification
extractor of the certificate (`OpenF20`'s `ext_eq` at `EXF20 (accV VS)`, `child = childF20`), at the typed instance
`N.inst Q lay`. -/
theorem ext_eqF20 (VS : SProg) (N : TypedV.TNat) (Q : Lvm.Loop.Program) (lay : Lay)
    (H : THypX (N.inst Q lay)) (HR : Lvm.VEq.TRefHypX N Q lay)
    (hnode : ∀ vk, NodeSoundM VS vk (GoodFM (N.inst Q lay) H) childF20) :
    ∀ vk L c π, isS π = true → L.length ≤ logCap →
      Lvm.FS.Scheme.μ (kcertSFW fmtF20 (midSpecPinF20 (N.inst Q lay) H) (midShapeF₂ (N.inst Q lay)) leadP_six
        (extJM (midShapeP_of (midShapeF₂ (N.inst Q lay))) (hnode vk))) L < 1 →
      ((schemeSW fmtF20 vk (PSWithM (midP (midM reloc20 (midF₂ (N.inst Q lay)))))).V c π).runLog L = some true →
      (∃ w, EXF20 (accV VS) c π L = some w ∧ Rel (accV VS vk) c w) ∨
        EXF20 (accV VS) c π L = (schemeSW fmtF20 vk (PSWithM (midP (midM reloc20 (midF₂ (N.inst Q lay)))))).Ex
          (kcertSFW fmtF20 (midSpecPinF20 (N.inst Q lay) H) (midShapeF₂ (N.inst Q lay)) leadP_six
            (extJM (midShapeP_of (midShapeF₂ (N.inst Q lay))) (hnode vk))).ext c π L :=
  fun vk L c π _ _ hμ hacc =>
    Lvm.ASM.ext_eqS_gen stF20 fmtF20 fmtOK_stF20 replayOK_stF20 progOK_stF20 outOK_stF20
      (midSpecP_of (midSpecPinF20 (N.inst Q lay) H) (midShapeF₂ (N.inst Q lay)) leadP_six) leadOpenM_le_εS leadP_six
      (midShapeP_of (midShapeF₂ (N.inst Q lay))) (fun _ ↦ Lvm.X.winLo) (fun _ ↦ by decide)
      (fun π _ _ ↦ (Lvm.XS.loP_ne3 (by decide) π).symm) hnode
      (fun π x out hn hl => by rw [Lvm.XS.wStreamS_ne3 (by decide)]; exact childWS_stream20 π x out hn hl)
      (midFollowsPF20 N Q lay HR)
      (fun _ _ _ hp => Lvm.X.sFits_of_acc (S := subWith VS (EXF20 (accV VS)) extXF20)
        (by show qVlvm ≤ Lvm.X.qMax; decide) (by rw [subWith_acc]; exact hp))
      vk L c π hμ hacc

/-! ## The child at S2GF -/

/-! ## The certificate at S2GF -/

/-! ## The guard -/

end Lvm.CT
