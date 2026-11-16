-- New for lvm2 MB-LIN (2026-11-16): S2GL's extractor stage and certificate (MBL-STMT 8, 9). The S2GL instance of
-- blob L (`NTL20`, `QL20`, `layL20`, the guard `staticOkBL20`, its facts `SFL20`/`sfL20`, `nodeL20`) is
-- `LvmS2GLStmtC`'s / `LvmE2QInstL`'s.
import LvmS2GLStmtV
import LvmS2GLStmtC
import LvmS2GUCert

/-!
# The S2GL certificate (day-0 statements)

S2GU's frame (`OpenSFW` at a format, `ext_eqS_gen` at a stage with the window `loU`, `certificateR_guardS`) at
`fmtL20`, `stL20`, `midMk 4 relocU20 (midGL _)`; the stream block, the window and the child's decoding are S2GU's
(stage `3`).

* `stL20` (MBL-STMT 8a–8d: `outOK_stL20`, `progOK_stL20`, `replayOK_stL20`, `fmtOK_stL20`, decided), `midItemsL`,
  `midFollowsPL20` (8e), `childL20`, `childL20_win` (8f), **`ext_eqL20`** (MBL-STMT 8).
* `GoodLM`, `midShapeL20`, `midSpecPinL20` (instances over MBL-STMT 4), `certificateSL20` (9a), `thypL20` (9b),
  `trefL20` (9c), `submissionL20`, **`certificateL20S`** (MBL-STMT 9).
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-- **S2GL's stage**: `P20L`'s schedule, S2GU's header (5,664), `|π| = piSize P20L` (268,336), `openMain` after the
fourth phase (commit, bus, tape, wire), the root's 46 occupied words. -/
def stL20 : XStage :=
  ⟨P20L, headerBytesP P20L, piSize P20L, leafLensU, (((phases P20L).take 4).flatMap (·.2)).length, 46⟩

/-- S2GL's `|π|`. -/
theorem stL20_pz : stL20.pz = 268336 := sizes_P20L.1.1

set_option maxRecDepth 200000 in
/-- S2GL's output facts, in one kernel evaluation (`outOK_allG`'s at `stL20`). -/
theorem outOK_allL :
    (Replay.planItems stL20.p Replay.w0 stL20.items).2.ok = true ∧
    (blocksS stL20).all (fun b => blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b)) = true ∧
    8 + 8 * ((blocksS stL20).map blkPOutsL).sum = stL20.pz ∧ 4928 ≤ stL20.pz ∧ stL20.pz < 2 ^ 64 ∧
    6 + ((blocksS stL20).map Blk.lanes).sum ≤ nCp ∧ qSS stL20 < 2 ^ 64 ∧
    ((blocksS stL20).map blkPCostL).sum + ((blocksS stL20).map blkTCostL).sum ≤ 7128485 ∧
    ((blocksS stL20).map blkPOutsL).sum + ((blocksS stL20).map blkTOutsL).sum ≤ 163533 ∧
    ((blocksS stL20).map blkPSizeL).sum + ((blocksS stL20).map blkTSizeL).sum ≤ 250000 := by
  rw [stL20_pz]
  decide +kernel

/-- **MBL-STMT 8a** (owner L): the node output's static facts at S2GL (one kernel evaluation, `outOK_stG20`'s). -/
theorem outOK_stL20 : OutOK stL20 :=
  let h := outOK_allL
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- S2GL's static facts (`progFacts_stG20`'s at `stL20`, one `decide +kernel`, `|π|` as its value). -/
theorem progFacts_stL20 : stL20.occ0 ≤ 64 ∧ 268336 < 2 ^ 32 ∧ nChainS stL20 < 2 ^ 11 ∧
    nChainS stL20 ≤ (fsMsgsS stL20).length ∧
    ((fsMsgsS stL20).take (nChainS stL20)).all (msgOkP 268336) = true ∧
    (fsMsgsS stL20).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    (∀ k < 14, foldPosKS stL20 k < nChainS stL20) ∧
    capOffS stL20 0 / 8 + 4 * 2 ^ 8 ≤ 268336 / 8 ∧ capOffS stL20 1 / 8 + 4 * 2 ^ 7 ≤ 268336 / 8 ∧
    capOffS stL20 2 / 8 + 4 * 2 ^ 7 ≤ 268336 / 8 ∧ resOffS stL20 / 8 + 3 * 2 ^ 9 ≤ 268336 / 8 ∧
    capWS stL20 0 + 4 * 2 ^ 8 < 2 ^ 62 ∧ capWS stL20 1 + 4 * 2 ^ 7 < 2 ^ 62 ∧ capWS stL20 2 + 4 * 2 ^ 7 < 2 ^ 62 ∧
    resWS stL20 + 3 * 2 ^ 9 < 2 ^ 63 ∧ posL 268336 ≤ 2 ^ 60 ∧ 15 ≤ 268336 / 8 := by
  decide +kernel

/-- **MBL-STMT 8b** (owner L): the extractor program's static facts at S2GL (`progOK_stG20`'s). -/
theorem progOK_stL20 : ProgOK stL20 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := progFacts_stL20
  have e : msgOkS stL20 = msgOkP 268336 := by funext m; rw [msgOkS, stL20_pz]
  exact ⟨outOK_stL20, h1, stL20_pz ▸ h2, h3, h4, e ▸ h5, h6, h7, stL20_pz ▸ h8, stL20_pz ▸ h9, stL20_pz ▸ h10,
    stL20_pz ▸ h11, h12, h13, h14, h15, by show posL stL20.pz ≤ 2 ^ 60; rw [stL20_pz]; exact h16, stL20_pz ▸ h17⟩

set_option maxRecDepth 200000 in
/-- **MBL-STMT 8c** (owner L): the replay's facts at S2GL (`replayOK_stG20`'s split after the fourth phase). -/
theorem replayOK_stL20 : Lvm.ASM.ReplayOK stL20 :=
  Lvm.ASM.replayOK_ofR (pre := ((phases P20L).take 4).flatMap (·.2)) (rest := ((phases P20L).drop 4).flatMap (·.2))
    (by show schedule P20L = _; rw [schedule, ← List.flatMap_append, List.take_append_drop]) rfl
    (by decide +kernel)

/-- `stL20`'s read widths are `readWidthsP P20L`. -/
theorem readWidthsS_stL20 : readWidthsS stL20 = readWidthsP P20L := by
  unfold readWidthsS readWidthsP
  exact List.flatMap_congr fun it _ => by cases it <;> rfl

/-- **MBL-STMT 8d** (owner L): S2GL's format agrees with its stage (`fmtOK_stG20`'s; `occOfU`'s 46 is `occ0`). -/
theorem fmtOK_stL20 : Lvm.ASM.FmtOK stL20 Lvm.CT.fmtL20 :=
  ⟨fun n => by show rwL20 n = _; rw [rwL20, readWidthsS_stL20], rfl, rfl, rfl, rfl, rfl⟩

end Lvm.XS

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q Lvm.E2U Lvm.E2L
open Lvm.E2T (TNatT TRefHypT)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-! ## The middle phases at S2GL -/

/-- **S2GL's good relation on `C_main` candidates** (S2GU's stream block). -/
def GoodLM (Ti : TInst) (H : THypL Ti) : GoodRelM := GoodOfM recOfU20 (Lvm.Shape.Good₂ (GoodTL Ti H))

/-- S2GL's middle phases commit nothing and grind nothing. -/
theorem midShapeL20 (Ti : TInst) : MidShapeM (midMk 4 relocU20 (midGL Ti)) := midShapeMk_of 4 (cg_midGL Ti)

/-- **The middle phases' obligation at S2GL** (MBL-STMT 4 at `leadF20`; followers lead at most `τU`). -/
theorem midSpecPinL20 (Ti : TInst) (H : THypL Ti) :
    MidSpecPinτ (midMk 4 relocU20 (midGL Ti)) (GoodLM Ti H) εS leadF20 τU :=
  midSpecPinMk_ofτ 4 relocLawU20 (midSpecP_GL Ti H recOfU20) (retOK_midGL_len Ti H)

/-- `stL20`'s middle items are S2GL's (`midItemsL`: the pin, the typed phases at `E2` without the table phase, the
merged tape, the wire). -/
theorem midItemsS_stL20 : midItemsS stL20 = Lvm.VEq.midItemsL P20L := by
  have h4 : ((phases P20L).take 4).flatMap (·.2) = Lvm.VEq.commitI P20L ++ Lvm.VEq.midItemsL P20L := by
    rw [Lvm.VEq.phasesL_eq P20L rfl rfl]
    simp only [List.take_succ_cons, List.take_zero, Lvm.VEq.midItemsL, Lvm.VEq.typedIL, List.flatMap_cons,
      List.flatMap_nil, List.append_assoc, List.append_nil]
  have hn : stL20.nOpen = (Lvm.VEq.commitI P20L ++ Lvm.VEq.midItemsL P20L).length := by
    rw [← h4]; rfl
  unfold midItemsS
  rw [hn, show stL20.items = schedule P20L from rfl, Lvm.VEq.scheduleL_eq P20L rfl rfl,
    show Lvm.VEq.commitI P20L ++ (Lvm.VEq.midItemsL P20L ++ (Lvm.VEq.openMainI P20L ++ [])) =
      (Lvm.VEq.commitI P20L ++ Lvm.VEq.midItemsL P20L) ++ (Lvm.VEq.openMainI P20L ++ []) from
      (List.append_assoc _ _ _).symm, List.take_left, Lvm.VEq.commitI, List.singleton_append, List.drop_succ_cons,
    List.drop_zero]

/-- **MBL-STMT 8e** (owner L): **the pinned S2GL middle phases follow `stL20`'s middle items** (`midFollowsPU20`'s
twin: S2GT's typed items without `miniTabI`, the merged tape, the wire). -/
theorem midFollowsPL20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (HR : TRefHypT N Q lay) :
    MidFollowsS (midItemsS stL20) (midP (midMk 4 relocU20 (midGL (N.inst Q lay)))) := fun x l a h ↦ by
  have hrs := replayOK_stL20.rs
  rw [midItemsS_stL20] at hrs
  rw [(Lvm.VEq.fol_after (@Lvm.VEq.FolP.fol Lvm.VEq.capS Lvm.VEq.shpS Lvm.VEq.idxS _ _ _ _
    (Lvm.VEq.folP_midPL relocU20 (N.inst Q lay) rfl Lvm.VEq.busDepth_P20 x) []) h).1, itemKindsS_eq,
    midItemsS_stL20]
  exact Lvm.VEq.atomKinds_atomsOf _ _ (noPos_of_rs _ hrs)

/-! ## The child at S2GL (S2GU's window `loU`) -/

/-- **S2GL's left child read from its stream window** (`childU20` at `stL20`). -/
def childL20 (x : List UInt8) (w : List BF64) : Signed :=
  childWS stL20 fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (w.getD (sIdxU x i) 0) else BF64.toBitVec 0

/-- **MBL-STMT 8f** (owner L): **S2GL's child from its window is the stream block's** (`childU20_win`'s twin). -/
theorem childL20_win (x : List UInt8) (q : Column CMain.nu20) :
    childL20 x (Lvm.X.winOfL (loU x) q) = Lvm.NS.childSP P20L (recOfU20 x q) := by
  rw [childL20, winWU20, childWS, trBridgeS stL20 outOK_stL20]
  rfl

/-- `loU x` is the extractor's lane `loP stL20 π` when `x`'s `n` is π's word 14 (`loU_eq` at `stL20`). -/
theorem loU_eqL (π : RecursionFast.Proof) (x : List UInt8) (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) :
    loU x = loP stL20 π := by
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    omega
  have h3 : stL20.p.stage = 3 := rfl
  unfold loU loP
  by_cases hs : Lvm.Shape.small x = true
  · rw [if_pos hs, if_pos ⟨h3, hc.2 hs⟩]
  · rw [if_neg hs, if_neg fun h => hs (hc.1 h.2)]

/-- **The stream block `EXS` reads at S2GL is `childL20`'s** (`childWS_streamU20` at `stL20`). -/
theorem childWS_streamL20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) (hl : out.length = 2 ^ 20) :
    childWS stL20 (wStreamS stL20 π out) = childL20 x out := by
  rw [childL20]
  congr 1
  funext i
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    omega
  unfold wStreamS sIdxU
  rw [if_pos (show stL20.p.stage = 3 from rfl)]
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi, ite_eq_left hi]
    by_cases hs : Lvm.Shape.small x = true
    · rw [if_pos (hc.2 hs), if_pos hs]
    · rw [if_neg (fun h => hs (hc.1 h)), if_neg hs]
  · rw [ite_eq_right hi, ite_eq_right hi]

/-- **MBL-STMT 8** (owner L): **`ext_eqL20`**: on accepted `S` proofs over good logs, S2GL's extractor decodes or is
the specification extractor of the certificate (`ext_eqU20`'s twin at `stL20`, `fmtL20`, `midGL`; an instance of
`ext_eqS_gen`). -/
theorem ext_eqL20 (VS : SProg) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)
    (H : THypL (N.inst Q lay)) (HR : TRefHypT N Q lay)
    (hnode : ∀ vk, NodeSoundML loU VS vk (GoodLM (N.inst Q lay) H) childL20) :
    ∀ vk L c π, isS π = true → L.length ≤ logCap →
      Lvm.FS.Scheme.μ (kcertSFWτ fmtL20 (midSpecPinL20 (N.inst Q lay) H) leadOpenM_le_τU (midShapeL20 (N.inst Q lay))
        leadP_six (extJML loU loU_le (midShapeP_of (midShapeL20 (N.inst Q lay))) (hnode vk))) L < 1 →
      ((schemeSW fmtL20 vk (PSWithM (midP (midMk 4 relocU20 (midGL (N.inst Q lay)))))).V c π).runLog L =
        some true →
      (∃ w, EXS stL20 (accV VS) c π L = some w ∧ Rel (accV VS vk) c w) ∨
        EXS stL20 (accV VS) c π L = (schemeSW fmtL20 vk (PSWithM (midP (midMk 4 relocU20 (midGL (N.inst Q lay)))))).Ex
          (kcertSFWτ fmtL20 (midSpecPinL20 (N.inst Q lay) H) leadOpenM_le_τU (midShapeL20 (N.inst Q lay)) leadP_six
            (extJML loU loU_le (midShapeP_of (midShapeL20 (N.inst Q lay))) (hnode vk))).ext c π L :=
  fun vk L c π _ _ hμ hacc =>
    Lvm.ASM.ext_eqS_gen stL20 fmtL20 fmtOK_stL20 replayOK_stL20 progOK_stL20 outOK_stL20
      (midSpecP_ofτ (midSpecPinL20 (N.inst Q lay) H) (midShapeL20 (N.inst Q lay)) leadP_six) leadOpenM_le_τU leadP_six
      (midShapeP_of (midShapeL20 (N.inst Q lay))) loU loU_le (fun π x hn ↦ loU_eqL π x hn) hnode
      (fun π x out hn hl => childWS_streamL20 π x out hn hl) (midFollowsPL20 N Q lay HR)
      (fun _ _ _ hp => Lvm.X.sFits_of_acc (S := subWith VS (EXS stL20 (accV VS)) (extXS stL20))
        (by show qVlvm ≤ Lvm.X.qMax; decide) (by rw [subWith_acc]; exact hp))
      vk L c π hμ hacc

/-- **MBL-STMT 9a** (owner L): **S2GL's certificate at a typed instance** `N.inst Q lay` (`certificateSU20`'s twin). -/
theorem certificateSL20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : THypL (N.inst Q lay))
    (HR : TRefHypT N Q lay) (hσ : Lvm.TypedV.SigInSL (layout0 P20L).s N.toN) (child : Column 19 → Signed)
    (hch : ∀ x q, childL20 x (Lvm.X.winOfL (loU x) q) = child (recOfU20 x q))
    (hnode : ∀ vk, NodeSound (VSLX N) vk (fun x qm qr ↦ GoodTL (N.inst Q lay) H x qm qr ∧ SBlkU qm qr) child) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith (VSLX N) (EXS stL20 (accV (VSLX N))) (extXS stL20)) :=
  certificateR_openW fmtL20 (VSLX N) (hq_VSLX N) (extS stL20 progOK_stL20 outOK_stL20 (VSLX N))
    (openSFW fmtL20
      { mid := midMk 4 relocU20 (midGL (N.inst Q lay))
        Good := GoodLM (N.inst Q lay) H
        Lm := leadF20
        τ := τU
        hτ := leadOpenM_le_τU
        hmid := midSpecPinL20 (N.inst Q lay) H
        hsh := midShapeL20 (N.inst Q lay)
        hL := leadP_six
        child := childL20
        lo := loU
        hlo := loU_le
        hnode := fun vk ↦ nodeML_of_pairU hch (hnode vk)
        refines := refinesL20 N Q lay HR hσ H.lin
        ext_eq := ext_eqL20 (VSLX N) N Q lay H HR fun vk ↦ nodeML_of_pairU hch (hnode vk) })

/-! ## The certificate at S2GL -/

/-- **`THypL` from `THypCore` and `mbLinB`** (`thypU20`'s fields; the errors `errsL_at`). -/
theorem thypL_ofCore {Ti : TInst} (c : THypCore Ti) (lin : Lvm.M3.mbLinB Ti.mbT = true) : THypL Ti :=
  { ok := c.ok, maps := c.maps, acc := fun x ↦ Lvm.VEq.length_pubXT x, accC2 := fun x ↦ Lvm.VEq.c₂_pubXT x,
    hτ := c.hτ, sc := c.sc, layOk := c.layOk, keys := c.keys, width := c.width, fix := c.fix, widths := c.widths,
    lin := lin, μBus := c.μBus, errs := fun h ↦ errsL_at _ (c.μBus h) }

/-- **MBL-STMT 9b** (owner L): **`THypL` of the S2GL typed instance** from the guard's facts (`thypU20`'s twin;
`lin` from the guard's `mbLinB`). -/
theorem thypL20 (S : SFL20) : THypL (NTL20.inst QL20 layL20) :=
  thypL_ofCore (thypCore_ofS S.1.st S.1.mb Pub.hdrLanesT S.2.2.1 p20_facts) S.2.2.2.2

/-- **MBL-STMT 9c** (owner L): **`TRefHypT` at the S2GL instance** from the guard's facts (`trefU20`'s twin). -/
theorem trefL20 (S : SFL20) : TRefHypT NTL20 QL20 layL20 where
  ok := S.1.st.regs
  hlay := S.1.st.hlayOk
  mini := S.1.st.mini
  sc := (thypL20 S).sc
  phiT := fun pt hpt ↦ by
    show Lvm.E2T.PhiQGC cacheL20 pt = _
    have hc : cacheL20 = Lvm.Typed.cacheWX QL20 layL20 := cacheWXF_eq QL20 layL20 S.1.st.hlay
    rw [hc]
    exact Lvm.Typed.KT.PhiQGC_eqW QL20 layL20 S.1.st.hlay S.1.st.cache (hc ▸ S.2.2.2.1) pt hpt

/-- **S2GL's static guard.** -/
def staticOkL20 : Bool := staticOkBL20

/-- **The S2GL submission**: `V_S` at S2GL behind the static guard, S2GL's extractor. -/
def submissionL20 : Submission := subGS stL20 staticOkL20 (VSLX NTL20)

/-- **MBL-STMT 9** (owner L): **statement 18 at S2GL: the certificate of the S2GL submission** against the declared
claim (`certificateR_guardS` ∘ `certificateSL20`). Release: `Solution.certified := Lvm.CT.certificateL20S`,
`Solution.submission := Lvm.CT.submissionL20`; axioms exactly `propext`, `Classical.choice`, `Quot.sound`. -/
theorem certificateL20S :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionL20 :=
  certificateR_guardS stL20 progOK_stL20 outOK_stL20 fun h ↦
    have S := sfL20 h
    have hσ : Lvm.TypedV.SigInSL (layout0 P20L).s NTL20.toN := Lvm.TypedV.sigInSL_of (by
      simp only [staticOkL20, staticOkBL20, Bool.and_eq_true] at h
      exact h.1.1.1.1.2)
    certificateSL20 NTL20 QL20 layL20 (thypL20 S) (trefL20 S) hσ (Lvm.NS.childSP P20L)
      (fun x q ↦ childL20_win x q) (nodeL20 S (thypL20 S))

end Lvm.CT
