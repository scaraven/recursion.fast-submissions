-- New for lvm2 S2GT (GT-L, 2026-11-15): DAY-0 STATEMENTS of S2GT's certificate: the middle phases (E2F-T's
-- `midSpecP_GT` pinned), the extractor at the stage `stG20`, the child, the instance facts, the guarded submission
-- and statement 18 at S2GT (`certificateG20S`). Every `sorry` is a day-0 statement tagged `-- S2GT-STMT <n>`.
import LvmS2GTStmtC
import LvmS2GTXS
import LvmCertF20Inst
import LvmS2GTFol
import LvmS2GTRef

/-!
# The S2GT certificate (day-0 statements)

The S2GT verifier runs the root pin, the middle phases `midMk 4 reloc20 (midGT Ti)` (E2F-T's `midGT`: the typed
phases at `E2`, the `E2` front with S2GT's continuation rows; four leading stream claims, re-freeze A4), then `C_main`'s opening, at S2GT's format `fmtG20`. The frame is
S2GF's (`OpenSFW` at a format, `ext_eqS_gen` at a stage), instantiated:

* proved here (instances, no proof work): `GoodGM`, **`midShapeG20`**, **`midSpecPinG20`** (`midSpecPinMk_of 4` with
  E2F-T's `midSpecP_GT` and `retOK_midGT_len`).
* `stG20` (the stage), `childG20` (the window child at `stG20`).
* Statements (owner L unless noted): `spongeBlocksGT_eq`, `outOK_stG20`, `progOK_stG20`, `replayOK_stG20`,
  `fmtOK_stG20`, `midFollowsPG20` (V), `childWS_streamG20`, `childG20_win`, **`ext_eqG20`**, `nodeM_of_pair`
  (generic), `certificateR_guardS` (generic), **`certificateSG20`**, `thypG20`, `trefG20`, **`certificateG20S`**.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q
open Lvm.E2T (TNatT VSGX GoodTT THypT TRefHypT midGT midSpecP_GT retOK_midGT_len cg_midGT spongeBlocksGT)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-! ## The middle phases at S2GT -/

/-- **S2GT's good relation on `C_main` candidates**: E2F-T's `GoodTT Ti H` on the viewed pair, the stream block
relocated by `recOf20`. -/
def GoodGM (Ti : TInst) (H : THypT Ti) : GoodRelM := GoodOfM recOf20 (Lvm.Shape.Good₂ (GoodTT Ti H))

/-- S2GT's middle phases commit nothing and grind nothing (E2F-T's `cg_midGT`). -/
theorem midShapeG20 (Ti : TInst) : MidShapeM (midMk 4 reloc20 (midGT Ti)) := midShapeMk_of 4 (cg_midGT Ti)

/-- **The middle phases' obligation at S2GT** (E2F-T's `midSpecP_GT` at the lead `leadF20`, `retOK_midGT_len`). -/
theorem midSpecPinG20 (Ti : TInst) (H : THypT Ti) :
    MidSpecPin (midMk 4 reloc20 (midGT Ti)) (GoodGM Ti H) εS leadF20 :=
  midSpecPinMk_of 4 relocLaw20 (midSpecP_GT Ti H recOf20) (retOK_midGT_len Ti H)

/-- **S2GT-STMT 12** (owner L): E2F-T's `KS` continuation literal is the S2GT trace's sponge-block count (the good
relation links `KS` rows `1 … blocks − 1`; #22's false-spec lesson): 4,288 at occupancy 47 (lead decision D1). -/
theorem spongeBlocksGT_eq : spongeBlocks P20T = spongeBlocksGT := sizes_P20T.1.2.2.2.2.1

/-! ## The extractor at S2GT -/

/-- **S2GT's left child read from the stream window** (`childF20` at `stG20`). -/
def childG20 (x : List UInt8) (w : List BF64) : Signed :=
  childWS stG20 fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (w.getD (sIdx x i) 0) else BF64.toBitVec 0

-- S2GT-STMT 13–15 (`outOK_stG20`, `progOK_stG20`, `replayOK_stG20`) and `stG20` are in `LvmS2GTXS`.

/-- **S2GT-STMT 16** (owner L): S2GT's format agrees with its stage. -/
theorem fmtOK_stG20 : Lvm.ASM.FmtOK stG20 fmtG20 :=
  ⟨fun n => by show rwG20 n = _; rw [rwG20, readWidthsS_stG20], rfl, rfl, rfl, rfl, rfl⟩

/-- `stG20`'s middle items are S2GT's (`midItemsT`: the pin, the typed phases at `E2`, the `E2` front). -/
theorem midItemsS_stG20 : midItemsS stG20 = Lvm.VEq.midItemsT P20T := by
  have h7 : ((phases P20T).take 7).flatMap (·.2) = Lvm.VEq.commitI P20T ++ Lvm.VEq.midItemsT P20T := by
    rw [Lvm.VEq.phasesT_eq P20T rfl]
    simp only [List.take_succ_cons, List.take_zero, Lvm.VEq.midItemsT, Lvm.VEq.typedIT, List.flatMap_cons,
      List.flatMap_nil, List.append_assoc, List.append_nil]
  have hn : stG20.nOpen = (Lvm.VEq.commitI P20T ++ Lvm.VEq.midItemsT P20T).length := by
    rw [← h7]; rfl
  unfold midItemsS
  rw [hn, show stG20.items = schedule P20T from rfl, Lvm.VEq.scheduleT_eq P20T rfl,
    show Lvm.VEq.commitI P20T ++ (Lvm.VEq.midItemsT P20T ++ (Lvm.VEq.openMainI P20T ++ [])) =
      (Lvm.VEq.commitI P20T ++ Lvm.VEq.midItemsT P20T) ++ (Lvm.VEq.openMainI P20T ++ []) from
      (List.append_assoc _ _ _).symm, List.take_left, Lvm.VEq.commitI, List.singleton_append, List.drop_succ_cons,
    List.drop_zero]

/-- **S2GT-STMT 17** (owner L since 19:50, from V): **the pinned S2GT middle phases follow `stG20`'s middle items**
(`midFollowsPF20`'s proof with `folP_midPT`: the pin, `typedProgT`'s atoms, the `E2` front). -/
theorem midFollowsPG20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (HR : TRefHypT N Q lay) :
    MidFollowsS (midItemsS stG20) (midP (midMk 4 reloc20 (midGT (N.inst Q lay)))) := fun x l a h ↦ by
  obtain ⟨hl, hr, he, -, -⟩ := HR.toT.fits
  have hrs := replayOK_stG20.rs
  rw [midItemsS_stG20] at hrs
  rw [(Lvm.VEq.fol_after (@Lvm.VEq.FolP.fol Lvm.VEq.capS Lvm.VEq.shpS Lvm.VEq.idxS _ _ _ _
    (Lvm.VEq.folP_midPT reloc20 (N.inst Q lay) hl Lvm.VEq.busDepth_P20 hr he x) []) h).1, itemKindsS_eq,
    midItemsS_stG20]
  exact Lvm.VEq.atomKinds_atomsOf _ _ (noPos_of_rs _ hrs)

/-- **The stream block `EXS` reads is the window's** (`childWS_stream20`'s body, for every stage: the window does not
depend on the schedule). -/
theorem wStreamM_win (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) (hl : out.length = 2 ^ 20) :
    Lvm.X.wStreamM π out = fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (out.getD (sIdx x i) 0) else BF64.toBitVec 0 := by
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

/-- **S2GT-STMT 18** (owner L): the stream block `EXS` reads at S2GT is `childG20`'s (`childWS_stream20` at
`stG20`; generic in the stage: the window does not depend on the schedule). -/
theorem childWS_streamG20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) (hl : out.length = 2 ^ 20) :
    childWS stG20 (Lvm.X.wStreamM π out) = childG20 x out := by
  rw [wStreamM_win π x out hn hl, childG20]

/-- **S2GT-STMT 19** (owner L): **S2GT's child from the window is the stream block's, read with `P20T`'s schedule**
(`childF20_win` through `trBridgeG20`: `readTraceLS stG20 W = decode P20T (wsOf W)`). -/
theorem childG20_win (x : List UInt8) (q : Column CMain.nu20) :
    childG20 x (Lvm.X.winOf q) = Lvm.NS.childSP P20T (recOf20 x q) := by
  rw [childG20, winW20, childWS, trBridgeS stG20 outOK_stG20]
  rfl

/-- **S2GT-STMT 20** (owner L): **`ext_eqG20`**: on accepted `S` proofs over good logs, S2GT's extractor decodes or is
the specification extractor of the certificate (`ext_eqF20` at `stG20`, `fmtG20`, `midGT`; an instance of
`ext_eqS_gen`). -/
theorem ext_eqG20 (VS : SProg) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)
    (H : THypT (N.inst Q lay)) (HR : TRefHypT N Q lay)
    (hnode : ∀ vk, NodeSoundM VS vk (GoodGM (N.inst Q lay) H) childG20) :
    ∀ vk L c π, isS π = true → L.length ≤ logCap →
      Lvm.FS.Scheme.μ (kcertSFW fmtG20 (midSpecPinG20 (N.inst Q lay) H) (midShapeG20 (N.inst Q lay))
        leadP_six (extJM (midShapeP_of (midShapeG20 (N.inst Q lay))) (hnode vk))) L < 1 →
      ((schemeSW fmtG20 vk (PSWithM (midP (midMk 4 reloc20 (midGT (N.inst Q lay)))))).V c π).runLog L =
        some true →
      (∃ w, EXS stG20 (accV VS) c π L = some w ∧ Rel (accV VS vk) c w) ∨
        EXS stG20 (accV VS) c π L = (schemeSW fmtG20 vk (PSWithM (midP (midMk 4 reloc20 (midGT (N.inst Q lay)))))).Ex
          (kcertSFW fmtG20 (midSpecPinG20 (N.inst Q lay) H) (midShapeG20 (N.inst Q lay)) leadP_six
            (extJM (midShapeP_of (midShapeG20 (N.inst Q lay))) (hnode vk))).ext c π L :=
  fun vk L c π _ _ hμ hacc =>
    Lvm.ASM.ext_eqS_gen stG20 fmtG20 fmtOK_stG20 replayOK_stG20 progOK_stG20 outOK_stG20
      (midSpecP_of (midSpecPinG20 (N.inst Q lay) H) (midShapeG20 (N.inst Q lay)) leadP_six) leadP_six
      (midShapeP_of (midShapeG20 (N.inst Q lay))) hnode
      (fun π x out hn hl => childWS_streamG20 π x out hn hl) (midFollowsPG20 N Q lay HR)
      (fun _ _ _ hp => Lvm.X.sFits_of_acc (S := subWith VS (EXS stG20 (accV VS)) (extXS stG20))
        (by show qVlvm ≤ Lvm.X.qMax; decide) (by rw [subWith_acc]; exact hp))
      vk L c π hμ hacc

/-- **S2GT-STMT 21** (owner L, generic): `NodeSoundM` from the pair form on stream-block pairs and a window bridge,
for any good relation (`nodeMF20` generalised from `GoodTF`; `nodeMF20` becomes its instance). -/
theorem nodeM_of_pair {VS : SProg} {vk : RecursionFast.Digest} {G : GoodRel}
    {childW : List UInt8 → List BF64 → Signed} {child : Column 19 → Signed}
    (hch : ∀ x q, childW x (Lvm.X.winOf q) = child (recOf20 x q))
    (hnode : NodeSound VS vk (fun x qm qr ↦ G x qm qr ∧ Lvm.NS.SBlk qm qr) child) :
    NodeSoundM VS vk (GoodOfM recOf20 (Lvm.Shape.Good₂ G)) childW := fun c x q hok hG ↦ by
  rw [hch]
  exact hnode c x (Lvm.Shape.view x q) (recB20 (Lvm.Shape.view x q)) hok ⟨hG, sBlk_recB20 _⟩

/-! ## The guard, generic in the stage -/

/-- **The guarded submission at a stage**: `V_S` behind the static guard `b`, the stage's extractor
(`subGF b VS = subGS stF20 b VS` by `rfl`). -/
def subGS (st : XStage) (b : Bool) (VS : SProg) : Submission :=
  subWith (Lvm.Fin.VSg b VS) (EXS st (accV (Lvm.Fin.VSg b VS))) (extXS st)

/-- **S2GT-STMT 22** (owner L, generic): **the guarded certificate at a stage** (`certificateR_guardF` with the
stage's `ProgOK`/`OutOK`): the guard off rejects; on, the certificate of the unguarded submission. -/
theorem certificateR_guardS (st : XStage) (hp : ProgOK st) (ho : OutOK st) {b : Bool} {VS : SProg}
    (h : b = true → CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (EXS st (accV VS)) (extXS st))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subGS st b VS) := by
  cases b with
  | false =>
    exact certificateR_claim _ _ _
      ⟨fun H vk c π _ => by simp [Lvm.Fin.VSg, OProg.queries], computesXS st hp ho _, extXS_size st hp ho,
        EXS_Wn st hp _, fun vk => Lvm.Fin.sSound_reject VS _ vk⟩
  | true => exact h rfl

/-- **The stage's executable extractor** for a verifier `VS` (`extF20` at a stage). -/
def extS (st : XStage) (hp : ProgOK st) (ho : OutOK st) (VS : SProg) : ExtF20 :=
  ⟨EXS st (accV VS), extXS st, computesXS st hp ho _, extXS_size st hp ho, EXS_Wn st hp _⟩

/-! ## The certificate at S2GT -/

/-- **S2GT-STMT 23** (owner L): **S2GT's certificate at a typed instance** `N.inst Q lay` (`certificateSF20`'s
shape): from `THypT`, the refinement's facts (`TRefHypT`, `SigInS`), a child the window bridges to, and the node
soundness in `nodeG20`'s pair form. -/
theorem certificateSG20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : THypT (N.inst Q lay))
    (HR : TRefHypT N Q lay) (hσ : Lvm.TypedV.SigInS N.toN) (child : Column 19 → Signed)
    (hch : ∀ x q, childG20 x (Lvm.X.winOf q) = child (recOf20 x q))
    (hnode : ∀ vk, NodeSound (VSGX N) vk
      (fun x qm qr ↦ GoodTT (N.inst Q lay) H x qm qr ∧ Lvm.NS.SBlk qm qr) child) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith (VSGX N) (EXS stG20 (accV (VSGX N))) (extXS stG20)) :=
  certificateR_openW fmtG20 (VSGX N) (Lvm.E2T.hq_VSGX N) (extS stG20 progOK_stG20 outOK_stG20 (VSGX N))
    (openSFW fmtG20
      { mid := midMk 4 reloc20 (midGT (N.inst Q lay))
        Good := GoodGM (N.inst Q lay) H
        Lm := leadF20
        hmid := midSpecPinG20 (N.inst Q lay) H
        hsh := midShapeG20 (N.inst Q lay)
        hL := leadP_six
        child := childG20
        hnode := fun vk ↦ nodeM_of_pair hch (hnode vk)
        refines := Lvm.E2T.refinesG20 N Q lay HR hσ
        ext_eq := ext_eqG20 (VSGX N) N Q lay H HR fun vk ↦ nodeM_of_pair hch (hnode vk) })

set_option maxRecDepth 100000 in
/-- **S2GT-STMT 24** (owner L, with C for `NodeGG`'s fields): **`THypT` of the S2GT typed instance** from the guard's
facts (`thypF20`'s proof; `accC2` from `c₂_pubXT`, `errs` from `errsT_at`). -/
theorem thypG20 (S : SFG20) : THypT TiG20 :=
  let c := thypCore_of S.1 Pub.hdrLanesT S.2.2.1 p20_facts
  { ok := c.ok, maps := c.maps, acc := fun x ↦ Lvm.VEq.length_pubXT x, accC2 := fun x ↦ Lvm.VEq.c₂_pubXT x,
    hτ := c.hτ, sc := c.sc, layOk := c.layOk, keys := c.keys, width := c.width, fix := c.fix, widths := c.widths,
    μBus := c.μBus, errs := fun h ↦ Lvm.E2T.errsT_at _ (c.μBus h) (c.B0 h) }

/-- **S2GT-STMT 25** (owner L): **`TRefHypT` at the S2GT instance** from the guard's facts (`phiT` through
`PhiQGC_eq` at `cacheG20`, `cacheWXF_eq`). -/
theorem trefG20 (S : SFG20) : TRefHypT NTG20 QG20 layG20 where
  ok := S.1.st.regs
  hlay := S.1.st.hlayOk
  mini := S.1.st.mini
  sc := (thypG20 S).sc
  phiT := fun pt hpt ↦ by
    show Lvm.E2T.PhiQGC cacheG20 pt = _
    have hc : cacheG20 = Lvm.Typed.cacheWX QG20 layG20 := cacheWXF_eq QG20 layG20 S.1.st.hlay
    rw [hc]
    exact Lvm.E2T.PhiQGC_eq QG20 layG20 S.1.st.hlay S.1.st.cache (hc ▸ S.2.2.2) pt hpt

/-- **S2GT's static guard** (`staticOkBG20`). -/
def staticOkG20 : Bool := staticOkBG20

/-- **The S2GT submission**: `V_S` at S2GT behind the static guard, S2GT's extractor. -/
def submissionG20 : Submission := subGS stG20 staticOkG20 (VSGX NTG20)

/-- **S2GT-STMT 26** (owner L): **statement 18 at S2GT: the certificate of the S2GT submission** against the declared
claim (`certificateR_guardS` ∘ `certificateSG20` at `NTG20 QG20 layG20`, the child `childSP P20T` by `childG20_win`,
`nodeG20`). `Solution.certified := Lvm.CT.certificateG20S`, `Solution.submission := Lvm.CT.submissionG20` (the switch,
at release). -/
theorem certificateG20S :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionG20 :=
  certificateR_guardS stG20 progOK_stG20 outOK_stG20 fun h ↦
    have S := sfG20 h
    have hσ : Lvm.TypedV.SigInS NTG20.toN := Lvm.TypedV.sigInS_of (by
      simp only [staticOkG20, staticOkBG20, Bool.and_eq_true] at h
      exact h.1.1.1.2)
    certificateSG20 NTG20 QG20 layG20 (thypG20 S) (trefG20 S) hσ (Lvm.NS.childSP P20T)
      (fun x q ↦ childG20_win x q) (nodeG20 S (thypG20 S))

end Lvm.CT
