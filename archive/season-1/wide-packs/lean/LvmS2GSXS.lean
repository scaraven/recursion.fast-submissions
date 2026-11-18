-- New for lvm2 σ_LEAF (SLF-L, 2026-11-16): S2GS's extractor stage, the node's own `σ_leaf` read from the window, and
-- `ext_eqS20`. DAY-0 STATEMENTS: every `sorry` is tagged `-- SLF-STMT <n>`. A proof never changes its statement; a
-- needed change goes to the lead old → new.
import LvmS2GSStmtV
import LvmXSWinU
import LvmCertStage
import LvmQSigLeafPerm
import LvmXSExtEqS
import LvmXSKindsEq

/-!
# S2GS's extractor (day-0 statements)

* **`stS20`**: `P20S`'s schedule, the 888-B header, `|π| = piSize P20S` (284,872), `openMain` after the fourth phase,
  the root's 46 occupied words (S2GL's but the header).
* **`σ_leaf` in the window** (SLF-STMT 3, with C): stream-block word `slWP` (layout D6: column 17
  from row 1024, `CMain.sW20 17 1024`; the σ region `2^11`), `sigLeafS20 x w` reads its 597 words from the window at
  the statement's shape (`sIdxU`); `sigLeafWin`.
* **`ext_eqS20`** (SLF-STMT 8): on accepted `S` proofs over good logs, `EXS stS20` decodes or is the specification
  extractor of `schemeSWS fmtS20` whose right leaf signs with `sigLeafS20` of the window. The executable side:
  `computesXS stS20` (generic) once `decXS` copies `σ_leaf` from the window when `st.p.leafOut` (D1 of the inventory)
  and `progOK_stS20`, `outOK_stS20` (SLF-STMT 8a, 8b).
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-- **S2GS's stage**: `P20S`'s schedule, the 888-B header, `|π| = piSize P20S`, `openMain` after the fourth phase, the
root's 46 occupied words. -/
def stS20 : XStage :=
  ⟨P20S, headerBytesP P20S, piSize P20S, leafLensU, (((phases P20S).take 4).flatMap (·.2)).length, 46⟩

/-- S2GS's `|π|`. -/
theorem stS20_pz : stS20.pz = 284872 := sizes_P20S.1.1

set_option maxRecDepth 200000 in
/-- S2GS's output facts, in one kernel evaluation (`outOK_allL`'s at `stS20`). -/
theorem outOK_allS :
    (Replay.planItems stS20.p Replay.w0 stS20.items).2.ok = true ∧
    (blocksS stS20).all (fun b => blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b)) = true ∧
    8 + 8 * ((blocksS stS20).map blkPOutsL).sum = stS20.pz ∧ 4928 ≤ stS20.pz ∧ stS20.pz < 2 ^ 64 ∧
    6 + ((blocksS stS20).map Blk.lanes).sum ≤ nCp ∧ qSS stS20 < 2 ^ 64 ∧
    ((blocksS stS20).map blkPCostL).sum + ((blocksS stS20).map blkTCostL).sum ≤ 7100000 ∧
    ((blocksS stS20).map blkPOutsL).sum + ((blocksS stS20).map blkTOutsL).sum ≤ 163533 ∧
    ((blocksS stS20).map blkPSizeL).sum + ((blocksS stS20).map blkTSizeL).sum ≤ 240000 := by
  rw [stS20_pz]
  decide +kernel

/-- **SLF-STMT 8b** (owner L): S2GS's extractor output facts (one kernel evaluation, `outOK_stL20`'s). -/
theorem outOK_stS20 : OutOK stS20 :=
  let h := outOK_allS
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- S2GS's static facts (`progFacts_stL20`'s at `stS20`, one `decide +kernel`, `|π|` as its value). -/
theorem progFacts_stS20 : stS20.occ0 ≤ 64 ∧ 284872 < 2 ^ 32 ∧ nChainS stS20 < 2 ^ 11 ∧
    nChainS stS20 ≤ (fsMsgsS stS20).length ∧
    ((fsMsgsS stS20).take (nChainS stS20)).all (msgOkP 284872) = true ∧
    (fsMsgsS stS20).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    (∀ k < 14, foldPosKS stS20 k < nChainS stS20) ∧
    capOffS stS20 0 / 8 + 4 * 2 ^ 8 ≤ 284872 / 8 ∧ capOffS stS20 1 / 8 + 4 * 2 ^ 7 ≤ 284872 / 8 ∧
    capOffS stS20 2 / 8 + 4 * 2 ^ 7 ≤ 284872 / 8 ∧ resOffS stS20 / 8 + 3 * 2 ^ 9 ≤ 284872 / 8 ∧
    capWS stS20 0 + 4 * 2 ^ 8 < 2 ^ 62 ∧ capWS stS20 1 + 4 * 2 ^ 7 < 2 ^ 62 ∧ capWS stS20 2 + 4 * 2 ^ 7 < 2 ^ 62 ∧
    resWS stS20 + 3 * 2 ^ 9 < 2 ^ 63 ∧ posL 284872 ≤ 2 ^ 60 ∧ 15 ≤ 284872 / 8 := by
  decide +kernel

/-- **SLF-STMT 8a** (owner L): S2GS's extractor program facts (`progOK_stL20`'s proof). -/
theorem progOK_stS20 : ProgOK stS20 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := progFacts_stS20
  have e : msgOkS stS20 = msgOkP 284872 := by funext m; rw [msgOkS, stS20_pz]
  exact ⟨outOK_stS20, h1, stS20_pz ▸ h2, h3, h4, e ▸ h5, h6, h7, stS20_pz ▸ h8, stS20_pz ▸ h9, stS20_pz ▸ h10,
    stS20_pz ▸ h11, h12, h13, h14, h15, by show posL stS20.pz ≤ 2 ^ 60; rw [stS20_pz]; exact h16, stS20_pz ▸ h17⟩

set_option maxRecDepth 200000 in
/-- S2GS's replay facts (`replayOK_stL20`'s split after the fourth phase; `hdrFixS ≤ 888`). -/
theorem replayOK_stS20 : Lvm.ASM.ReplayOK stS20 :=
  Lvm.ASM.replayOK_ofR (pre := ((phases P20S).take 4).flatMap (·.2)) (rest := ((phases P20S).drop 4).flatMap (·.2))
    (by show schedule P20S = _; rw [schedule, ← List.flatMap_append, List.take_append_drop]) rfl
    (by
      -- `|π|` as its value (SLF-K's golfed pattern)
      rw [show stS20 = ⟨P20S, headerBytesP P20S, 284872, leafLensU, (((phases P20S).take 4).flatMap (·.2)).length, 46⟩
        by rw [stS20, sizes_P20S.1.1]]
      decide +kernel)

/-- `stS20`'s read widths are `readWidthsP P20S`. -/
theorem readWidthsS_stS20 : readWidthsS stS20 = readWidthsP P20S := by
  unfold readWidthsS readWidthsP
  exact List.flatMap_congr fun it _ => by cases it <;> rfl

/-- S2GS's format agrees with its stage. -/
theorem fmtOK_stS20 : Lvm.ASM.FmtOK stS20 Lvm.CT.fmtS20 :=
  ⟨fun n => by show rwS20 n = _; rw [rwS20, readWidthsS_stS20], rfl, rfl, rfl, rfl, rfl⟩

/-- `stS20`'s middle items are S2GL's at `P20S` (`midItemsL`). -/
theorem midItemsS_stS20 : midItemsS stS20 = Lvm.VEq.midItemsL P20S := by
  have h4 : ((phases P20S).take 4).flatMap (·.2) = Lvm.VEq.commitI P20S ++ Lvm.VEq.midItemsL P20S := by
    rw [Lvm.VEq.phasesL_eq P20S rfl rfl]
    simp only [List.take_succ_cons, List.take_zero, Lvm.VEq.midItemsL, Lvm.VEq.typedIL, List.flatMap_cons,
      List.flatMap_nil, List.append_assoc, List.append_nil]
  have hn : stS20.nOpen = (Lvm.VEq.commitI P20S ++ Lvm.VEq.midItemsL P20S).length := by
    rw [← h4]; rfl
  unfold midItemsS
  rw [hn, show stS20.items = schedule P20S from rfl, Lvm.VEq.scheduleL_eq P20S rfl rfl,
    show Lvm.VEq.commitI P20S ++ (Lvm.VEq.midItemsL P20S ++ (Lvm.VEq.openMainI P20S ++ [])) =
      (Lvm.VEq.commitI P20S ++ Lvm.VEq.midItemsL P20S) ++ (Lvm.VEq.openMainI P20S ++ []) from
      (List.append_assoc _ _ _).symm, List.take_left, Lvm.VEq.commitI, List.singleton_append, List.drop_succ_cons,
    List.drop_zero]

/-- The stream block `EXS` reads at S2GS, at the statement's shape (`childWS_streamL20`'s case split). -/
theorem wStreamS_S20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) (i : ℕ) :
    wStreamS stS20 π out i = if i < 2 ^ 19 then BF64.toBitVec (out.getD (Lvm.CT.sIdxU x i) 0) else BF64.toBitVec 0 := by
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    omega
  unfold wStreamS Lvm.CT.sIdxU
  rw [if_pos (show stS20.p.stage = 3 from rfl)]
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi, ite_eq_left hi]
    by_cases hs : Lvm.Shape.small x = true
    · rw [if_pos (hc.2 hs), if_pos hs]
    · rw [if_neg (fun h => hs (hc.1 h)), if_neg hs]
  · rw [ite_eq_right hi, ite_eq_right hi]

/-- `loU x` is the extractor's lane `loP stS20 π` when `x`'s `n` is π's word 14 (`loU_eqL` at `stS20`). -/
theorem loU_eqS (π : RecursionFast.Proof) (x : List UInt8) (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) :
    Lvm.CT.loU x = loP stS20 π := by
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    omega
  have h3 : stS20.p.stage = 3 := rfl
  unfold Lvm.CT.loU loP
  by_cases hs : Lvm.Shape.small x = true
  · rw [if_pos hs, if_pos ⟨h3, hc.2 hs⟩]
  · rw [if_neg hs, if_neg fun h => hs (hc.1 h.2)]

end Lvm.XS

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q Lvm.E2U Lvm.E2S
open Lvm.E2T (TNatT TRefHypT)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **`σ_leaf`'s first stream-block word** at S2GS (layout D6, frozen: column 17 from row 1024; the σ region `2^11`). -/
abbrev slWP : ℕ := 17 * 2 ^ 14 + 1024

/-- **`σ_leaf` from S2GS's window**: stream-block words `slWP … slWP + 596` at the statement's shape, the chains in
`permC` order (RE-FREEZE R1). -/
def sigLeafS20 (x : List UInt8) (w : List BF64) : Sig :=
  sigOfP fun j ↦ BF64.toBitVec (w.getD (sIdxU x (slWP + j)) 0)

/-- **`σ_leaf` read off a `C_main` candidate** (its stream block's words from `slWP`, `permC` order; SLF-C's
`nodeS20` argument). -/
def slM20 (_x : List UInt8) (qm : Column CMain.nu20) : Sig :=
  sigOfP fun j ↦ Lvm.NS.wOfCol (recBU20 qm) (slWP + j)

/-- **SLF-STMT 3** (owner C/L): `σ_leaf`'s 597 words lie in column 17's σ region `[2^10, 2^11)` past `σ'`'s 597, inside
the stream block's `2^19` words (so inside the window at both shapes, `sIdxU`). -/
theorem sigLeafWin : 17 * 2 ^ 14 + 597 ≤ slWP ∧ slWP + 597 ≤ 17 * 2 ^ 14 + 2 ^ 11 ∧ 17 * 2 ^ 14 + 2 ^ 11 ≤ 2 ^ 19 := by
  decide

/-- **S2GS's left child read from its stream window** (`childL20` at `stS20`). -/
def childS20 (x : List UInt8) (w : List BF64) : Signed :=
  childWS stS20 fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (w.getD (sIdxU x i) 0) else BF64.toBitVec 0

/-- **S2GS's good relation on `C_main` candidates** (S2GU's stream block). -/
def GoodSM (Ti : TInst) (H : THypS Ti) : GoodRelM := GoodOfM recOfU20 (Lvm.Shape.Good₂ (GoodTS Ti H))

/-- S2GS's middle phases commit nothing and ask no proof of work. -/
theorem cg_midGS (Ti : TInst) (x : List UInt8) : Lvm.M3.NoCG (midGS Ti x) :=
  Lvm.M3.NoCG.bind (Lvm.E2L.noCG_typedProgL Ti _) fun _ ↦ Lvm.M3.NoCG.bind (cg_tapeProgL _ _ _) fun _ ↦
    Lvm.M3.cg_ret _

/-- **S2GS's middle phases' claims are fewer than `2^40`** (`retOK_midGL_len`'s proof). -/
theorem retOK_midGS_len (Ti : TInst) (H : THypS Ti) (x : List UInt8) :
    LeanVM.Protocol.EndToEnd.Sound.RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40) (midGS Ti x) := by
  refine (Lvm.E2L.retOK_typedProgL Ti H.toL (pubXTS x)).bind fun a ha ↦
    LeanVM.Protocol.EndToEnd.Sound.RetOK.bind_true fun k ↦ LeanVM.Protocol.EndToEnd.Sound.RetOK.ret ?_
  have hz : ∀ l : List Lvm.VEq.VStackClaim, (Lvm.Shape.onStackZs x l).length = l.length := fun l ↦ by
    unfold Lvm.Shape.onStackZs
    split_ifs <;> simp only [List.length_map]
  simp only [assembleU₂, hz, List.length_append, List.length_map, length_tapeClaimsU]
  have := ha.2.2
  omega

/-- **SLF-STMT 8c** (owner L): S2GS's middle phases commit nothing and grind nothing. -/
theorem midShapeS20 (Ti : TInst) : MidShapeM (midMk 4 relocU20 (midGS Ti)) := midShapeMk_of 4 (cg_midGS Ti)

/-- **SLF-STMT 8d** (owner L): **the middle phases' obligation at S2GS** (from SLF-STMT 6m, as `midSpecPinL20`). -/
theorem midSpecPinS20 (Ti : TInst) (H : THypS Ti) :
    MidSpecPinτ (midMk 4 relocU20 (midGS Ti)) (GoodSM Ti H) εS leadF20 τU :=
  midSpecPinMk_ofτ 4 relocLawU20 (midSpecP_GS Ti H recOfU20) (retOK_midGS_len Ti H)

/-- **The pinned S2GS middle phases follow `stS20`'s middle items** (`midFollowsPL20`'s twin over `midGS`). -/
theorem midFollowsPS20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) :
    MidFollowsS (midItemsS stS20) (midP (midMk 4 relocU20 (midGS (N.inst Q lay)))) := fun x l a h ↦ by
  have hrs := replayOK_stS20.rs
  rw [midItemsS_stS20] at hrs
  rw [(Lvm.VEq.fol_after (@Lvm.VEq.FolP.fol Lvm.VEq.capS Lvm.VEq.shpS Lvm.VEq.idxS _ _ _ _
    (Lvm.VEq.folP_midPS relocU20 (N.inst Q lay) rfl Lvm.VEq.busDepth_P20 x) []) h).1, itemKindsS_eq,
    midItemsS_stS20]
  exact Lvm.VEq.atomKinds_atomsOf _ _ (noPos_of_rs _ hrs)

/-- **The stream block `EXS` reads at S2GS is `childS20`'s.** -/
theorem childWS_streamS20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) :
    childWS stS20 (wStreamS stS20 π out) = childS20 x out := by
  rw [childS20]
  congr 1
  funext i
  exact wStreamS_S20 π x out hn i

/-- **The right leaf's signature `EXS` outputs at S2GS is `sigLeafS20` of the window** (`sigOfP` reads words
`slWP … slWP + 596`, inside the stream block). -/
theorem sigLeaf_streamS20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) :
    sigOfP (fun j => wStreamS stS20 π out (17 * 2 ^ 14 + 1024 + j)) = sigLeafS20 x out := by
  rw [sigLeafS20]
  refine Lvm.ASM.sigOfP_congr fun j hj => ?_
  rw [wStreamS_S20 π x out hn, if_pos (by omega)]

/-- **SLF-STMT 8** (owner L): **`ext_eqS20`**: on accepted `S` proofs over good logs, S2GS's extractor decodes or is
the specification extractor of `schemeSWS fmtS20`, the right leaf signing with `sigLeafS20` of the window
(`ext_eqL20`'s twin). -/
theorem ext_eqS20 (VS : SProg) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)
    (H : THypS (N.inst Q lay)) (HR : TRefHypT N Q lay)
    (hnode : ∀ vk, NodeSoundMLS loU VS vk (GoodSM (N.inst Q lay) H) childS20 sigLeafS20) :
    ∀ vk L c π, isS π = true → L.length ≤ logCap →
      Lvm.FS.Scheme.μ (kcertSFWSτ fmtS20 (midSpecPinS20 (N.inst Q lay) H) leadOpenM_le_τU
        (midShapeS20 (N.inst Q lay)) leadP_six
        (extJMLS loU loU_le (midShapeP_of (midShapeS20 (N.inst Q lay))) (hnode vk))) L < 1 →
      ((schemeSWS fmtS20 vk (PSWithM (midP (midMk 4 relocU20 (midGS (N.inst Q lay)))))).V c π).runLog L =
        some true →
      (∃ w, EXS stS20 (accV VS) c π L = some w ∧ Rel (accV VS vk) c w) ∨
        EXS stS20 (accV VS) c π L = (schemeSWS fmtS20 vk (PSWithM (midP (midMk 4 relocU20 (midGS (N.inst Q lay)))))).Ex
          (kcertSFWSτ fmtS20 (midSpecPinS20 (N.inst Q lay) H) leadOpenM_le_τU (midShapeS20 (N.inst Q lay)) leadP_six
            (extJMLS loU loU_le (midShapeP_of (midShapeS20 (N.inst Q lay))) (hnode vk))).ext c π L := by
  intro vk L c π _ _ hμ hacc
  exact Lvm.ASM.ext_eqS_genS stS20 fmtS20 fmtOK_stS20 replayOK_stS20 progOK_stS20 outOK_stS20
    (midSpecP_ofτ (midSpecPinS20 (N.inst Q lay) H) (midShapeS20 (N.inst Q lay)) leadP_six) leadOpenM_le_τU leadP_six
    (midShapeP_of (midShapeS20 (N.inst Q lay))) loU loU_le (fun π x hn ↦ loU_eqS π x hn) hnode
    (fun π x out hn _ => childWS_streamS20 π x out hn) (fun π x out hn _ => sigLeaf_streamS20 π x out hn)
    (midFollowsPS20 N Q lay)
    (fun _ _ _ hp => Lvm.X.sFits_of_acc (S := subWith VS (EXS stS20 (accV VS)) (extXS stS20))
      (by show qVlvm ≤ Lvm.X.qMax; decide) (by rw [subWith_acc]; exact hp))
    vk L c π hμ hacc rfl

end Lvm.CT
