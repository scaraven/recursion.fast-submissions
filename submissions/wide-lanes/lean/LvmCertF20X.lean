-- New for lvm2 slice S1 (E2-F, E2F-L, 2026-11-13): S2GF's executable extractor and its agreement (`ext_eqF20`), the
-- instance at `stF20` of the stage-generic extractor (`LvmXS*`). The `sorry`s are frozen statements tagged with their
-- owner; a proof never changes its statement, a needed change is reported old → new.
import LvmCertF20
import LvmXSChild
import LvmXSTop
import LvmXSKinds
import LvmXSExtEq
import LvmE2VRefinesF
import LvmNodeSoundTr
import LvmFinGuard

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

/-- **`Computes extXF20 (EXF20 A) fuel`** with the declared fuel. -/
theorem computesXF20 (A : RecursionFast.Digest → RecursionFast.Digest → Signed → Bool) :
    Computes extXF20 (EXF20 A) Lvm.X.fuel :=
  computesXS stF20 progOK_stF20 outOK_stF20 A

/-- The program within `progCap`. -/
theorem extXF20_size : extXF20.body.size ≤ progCap :=
  extXS_size stF20 progOK_stF20 outOK_stF20

/-- Witness-sending proofs decode. -/
theorem EXF20_W (A : RecursionFast.Digest → RecursionFast.Digest → Signed → Bool) (c : RecursionFast.Digest)
    (π : RecursionFast.Proof) (L : Log) (h : isS π = false) :
    EXF20 A c π L = RecursionFast.WitnessSending.decode π := by
  refine EXS_W stF20 progOK_stF20 A c π L fun h0 ↦ ?_
  have : π.data.getD 0 0 = 0x53 := by
    rw [Array.getD_eq_getD_getElem?, h0]; rfl
  simp [isS, this, sByte] at h

/-- **S2GF's executable extractor** for a verifier `VS`. -/
def extF20 (VS : SProg) : ExtF20 :=
  ⟨EXF20 (accV VS), extXF20, computesXF20 _, extXF20_size, EXF20_W _⟩

/-! ## The middle phases' shape -/

theorem P20F_withF : P20F.withF accVF = P20F := rfl

set_option maxRecDepth 200000 in
/-- **S2GF's replay facts**: one kernel evaluation of the run-length checker `replayOkR` at the split of `P20F`'s
phases after the seventh (the root cap and the middle phases, then `openMain`). -/
theorem replayOK_stF20 : Lvm.ASM.ReplayOK stF20 :=
  Lvm.ASM.replayOK_ofR (pre := ((phases P20F).take 7).flatMap (·.2)) (rest := ((phases P20F).drop 7).flatMap (·.2))
    (by show schedule P20F = _; rw [schedule, ← List.flatMap_append, List.take_append_drop]) rfl
    (by decide +kernel)

theorem itemKindsS_eq : ∀ its : List Item, itemKindsS its = Lvm.ASM.itemKinds its
  | [] => rfl
  | it :: its => by
    have ih := itemKindsS_eq its
    cases it <;> simp only [itemKindsS, Lvm.ASM.itemKinds, ih]

theorem noPos_of_rs : ∀ its : List Item, Lvm.ASM.RSItemsF its = true → ∀ it ∈ its, ∀ r, it ≠ .positions r
  | [], _ => by simp
  | .readW _ _ :: its, h | .read _ :: its, h | .sample :: its, h => fun it hit r ↦ by
    rcases List.mem_cons.mp hit with rfl | hit
    · exact fun e ↦ Item.noConfusion e
    · exact noPos_of_rs its h it hit r
  | .cap _ _ :: _, h | .positions _ :: _, h | .opening _ :: _, h => by simp [Lvm.ASM.RSItemsF] at h

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
      (midSpecP_of (midSpecPinF20 (N.inst Q lay) H) (midShapeF₂ (N.inst Q lay)) leadP_six) leadP_six
      (midShapeP_of (midShapeF₂ (N.inst Q lay))) hnode
      (fun π x out hn hl => childWS_stream20 π x out hn hl) (midFollowsPF20 N Q lay HR)
      (fun _ _ _ hp => Lvm.X.sFits_of_acc (S := subWith VS (EXF20 (accV VS)) extXF20)
        (by show qVlvm ≤ Lvm.X.qMax; decide) (by rw [subWith_acc]; exact hp))
      vk L c π hμ hacc

/-! ## The child at S2GF -/

set_option maxRecDepth 100000 in
/-- `P20F`'s plan's lengths: `q₀`'s `7`, then `stF20`'s (`plan_lens`). -/
theorem lens_P20F : Lvm.QLink.lens P20F = 7 :: lensLS stF20 := by
  rw [Lvm.QLink.lens, show Replay.plan P20F = ⟨.q0, 7⟩ :: ⟨.fs 0, seedLenP P20F⟩ ::
      (Replay.planItems P20F Replay.w0 (schedule P20F)).1 from rfl, List.map_cons, List.map_cons,
    plan_lens P20F (schedule P20F) Replay.w0 outOK_stF20.planOk, show Replay.w0.pend = 0 from rfl, lensLS,
    show blocksS stF20 = .one .seed (seedLenP P20F) :: Lvm.X.itemBlks P20F (schedule P20F) 0 from rfl,
    List.flatMap_cons]
  simp only [Lvm.X.Blk.queries, List.map_cons, List.map_nil, List.cons_append, List.nil_append]

/-- The trace's lanes at a stage, as `lanesOf` (stated for every stage: no evaluation at `stF20`). -/
theorem lanesOf_lensLS (st : XStage) :
    Lvm.X.lanesOf ((blocksS st).flatMap Lvm.X.lensB) = ((lensLS st).map fun len => 5 + len / 8).sum := rfl

set_option maxRecDepth 100000 in
/-- **The trace bridge at S2GF**: the extractor's reader of the stream lanes is `Q_link`'s `decode P20F`. -/
theorem trBridgeF20 (W : ℕ → Word) : readTraceLS stF20 W = Lvm.QLink.decode P20F (Lvm.NS.wsOf W) := by
  have h8 : ∀ len ∈ lensLS stF20, len % 8 = 0 := fun len h ↦ by
    rw [lensLS_eq] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    exact (qryOk_qsLS stF20 outOK_stF20.blkOk q hq).1
  have hend : 6 + ((lensLS stF20).map fun len => 5 + len / 8).sum ≤ Lvm.NS.nLanes := by
    have h2 := outOK_stF20.lanes
    rw [← lanesOf_flatMapB, lanesOf_lensLS, Lvm.X.nCp_eq] at h2
    exact h2
  rw [readTraceLS, entLS, Lvm.QLink.decode, lens_P20F, Lvm.QLink.readEntries, Lvm.NS.entryAt_q0,
    show 1 + 40 + 7 = 8 * 6 from rfl, Lvm.NS.readEntries_walk W _ 6 h8 hend]

/-- **S2GF's child from the window is the stream block's, read with `P20F`'s schedule** (E2F-C's `childSP P20F`
of `recOf20 x q`, by its definition). -/
theorem childF20_win (x : List UInt8) (q : Column CMain.nu20) :
    childF20 x (Lvm.X.winOf q) =
      ⟨Replay.reassemble P20F (Lvm.QLink.decode P20F (Lvm.NS.wsOf (Lvm.X.laneOf (Lvm.NS.wOfCol (recOf20 x q))))),
        Lvm.QLink.decode P20F (Lvm.NS.wsOf (Lvm.X.laneOf (Lvm.NS.wOfCol (recOf20 x q)))),
        Lvm.X.sigOfF (Lvm.X.sigCol (Lvm.NS.wOfCol (recOf20 x q)))⟩ := by
  rw [childF20, winW20, childWS, trBridgeF20]
  rfl

/-- `NodeSoundM` at S2GF from the pair form on stream-block pairs (`nodeF20`'s shape) and the child bridge. -/
theorem nodeMF20 {VS : SProg} {vk : RecursionFast.Digest} {Ti : TInst} {H : THypX Ti}
    {child : Column 19 → Signed} (hch : ∀ x q, childF20 x (Lvm.X.winOf q) = child (recOf20 x q))
    (hnode : NodeSound VS vk (fun x qm qr ↦ GoodTF Ti H x qm qr ∧ Lvm.NS.SBlk qm qr) child) :
    NodeSoundM VS vk (GoodFM Ti H) childF20 := fun c x q hok hG ↦ by
  rw [hch]
  exact hnode c x (Lvm.Shape.view x q) (recB20 (Lvm.Shape.view x q)) hok ⟨hG, sBlk_recB20 _⟩

/-! ## The certificate at S2GF -/

set_option maxRecDepth 100000 in
/-- S2GF's query bound (one kernel evaluation of the schedule's query count). -/
theorem qcItems_P20F : 2 + qcItems P20F (schedule P20F) 0 ≤ 16384 := by decide +kernel

/-- **O1 for S2GF's `V_S`**, any typed record. -/
theorem hq_VSFX (N : TypedV.TNat) (H : ByteArray → RecursionFast.Digest) (vk c : RecursionFast.Digest)
    (π : RecursionFast.Proof) : ((VSFX N vk c π).queries H).length ≤ qVlvm := by
  unfold VSFX VSF
  split
  · simp only [driveF, drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π (P20F.withF accVF) _ 0
      (fun s ↦ by simp [OProg.queries]) (schedule (P20F.withF accVF)) 0 _ (by simp)) 1) 1).trans ?_
    have := qcItems_P20F
    rw [P20F_withF]
    show _ ≤ 16384
    omega
  · simp [OProg.queries]

/-- **S2GF's certificate at a typed instance** `N.inst Q lay`: from `THypX`, the refinement's facts (`TRefHypX`,
`SigInS`: E2F-V's `refinesF20`), a child `child` the window bridges to (`hch`; S2GF: E2F-C's `childSP P20F`,
`childF20_win`), and the node soundness in `nodeF20`'s pair form. -/
theorem certificateSF20 (N : TypedV.TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : THypX (N.inst Q lay))
    (HR : Lvm.VEq.TRefHypX N Q lay) (hσ : Lvm.TypedV.SigInS N) (child : Column 19 → Signed)
    (hch : ∀ x q, childF20 x (Lvm.X.winOf q) = child (recOf20 x q))
    (hnode : ∀ vk, NodeSound (VSFX N) vk
      (fun x qm qr ↦ GoodTF (N.inst Q lay) H x qm qr ∧ Lvm.NS.SBlk qm qr) child) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith (VSFX N) (EXF20 (accV (VSFX N))) extXF20) :=
  certificateF20 (VSFX N) (hq_VSFX N) (extF20 (VSFX N))
    ⟨childF20, fun vk ↦ nodeMF20 hch (hnode vk), refinesF20 N Q lay HR hσ,
      ext_eqF20 (VSFX N) N Q lay H HR fun vk ↦ nodeMF20 hch (hnode vk)⟩

/-! ## The guard -/

/-- **The guarded S2GF submission**: `V_S` behind the static guard `b`, S2GF's extractor. -/
def subGF (b : Bool) (VS : SProg) : Submission :=
  subWith (Lvm.Fin.VSg b VS) (EXF20 (accV (Lvm.Fin.VSg b VS))) extXF20

/-- **The certificate with the guard off.** -/
theorem certificateR_rejectF (VS : SProg) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subGF false VS) :=
  certificateR_claim _ _ _
    ⟨fun H vk c π _ => by simp [Lvm.Fin.VSg, OProg.queries], computesXF20 _, extXF20_size, EXF20_W _,
      fun vk => Lvm.Fin.sSound_reject VS _ vk⟩

/-- **The guarded certificate**: the guard off rejects; on, the certificate of the unguarded submission. -/
theorem certificateR_guardF {b : Bool} {VS : SProg}
    (h : b = true → CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (EXF20 (accV VS)) extXF20)) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subGF b VS) := by
  cases b with
  | false => exact certificateR_rejectF VS
  | true => exact h rfl

end Lvm.CT
