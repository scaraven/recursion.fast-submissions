-- New for lvm2 U-TAPE (UT-L, 2026-11-16): DAY-0 STATEMENTS of S2GU's certificate: the middle phases pinned, the
-- extractor at the stage `stU20` (the shape-dependent window, decision D-WIN (B)), the child, the instance facts, the guarded
-- submission and statement 18 at S2GU (`certificateU20S`). Every `sorry` is a day-0 statement tagged
-- `-- UTAPE-STMT <n>`.
import LvmS2GUStmt
import LvmS2GUWin
import LvmS2GUXS
import LvmS2GUFol
import LvmCertStage
import LvmXSKindsEq
import LvmCertTHypCore
import LvmE2VPhiTEqC

/-!
# The S2GU certificate (day-0 statements)

The frame is S2GT's (`OpenSFW` at a format, `ext_eqS_gen` at a stage, `certificateR_guardS`), instantiated at
`fmtU20`, `stU20`, `midMk 4 relocU20 (midGU _)`, with one generalisation (D-WIN (B), UTAPE-STMT 32): the window's
first lane is a function of the statement (`OpenSFW.lo`, `NodeSoundML`, `extSML`/`extJML`, `decodeMP0L`, the stage's
`dec0S`/`streamS`, `ext_eqS_gen`'s `lo`); S2GF/S2GT take M′'s `winLo` (the field's default; their extractor programs
are unchanged), S2GU `loU x` (`32` small, `40` big).

* proved here (instances): `GoodUM`, **`midShapeU20`**, **`midSpecPinU20`** (over UT-V's `midSpecP_GU`).
* `loU`, `sIdxU`, `childU20`, `staticOkU20`, **`submissionU20`**.
* Statements (owner L unless noted): `outOK_stU20`, `progOK_stU20`, `replayOK_stU20`, `fmtOK_stU20`,
  `midFollowsPU20` (V + L), `childU20_win`, `ext_eqU20`, `certificateSU20`, `thypU20`, `trefU20`,
  **`certificateU20S`**.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q Lvm.E2U
open Lvm.E2T (TNatT GoodTT THypT TRefHypT)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-! ## The middle phases at S2GU -/

/-- **S2GU's good relation on `C_main` candidates**: `GoodTU Ti H` on the viewed pair, the stream block at S2GU's `S`. -/
def GoodUM (Ti : TInst) (H : THypT Ti) : GoodRelM := GoodOfM recOfU20 (Lvm.Shape.Good₂ (GoodTU Ti H))

/-- S2GU's middle phases commit nothing and grind nothing. -/
theorem midShapeU20 (Ti : TInst) : MidShapeM (midMk 4 relocU20 (midGU Ti)) := midShapeMk_of 4 (cg_midGU Ti)

/-- **The middle phases' obligation at S2GU** (UT-V's `midSpecP_GU` at the lead `leadF20`, `retOK_midGU_len`; followers
lead at most `τU`, re-freeze U-A3). -/
theorem midSpecPinU20 (Ti : TInst) (H : THypT Ti) :
    MidSpecPinτ (midMk 4 relocU20 (midGU Ti)) (GoodUM Ti H) εS leadF20 τU :=
  midSpecPinMk_ofτ 4 relocLawU20 (midSpecP_GU Ti H recOfU20) (retOK_midGU_len Ti H)

/-! ## The extractor at S2GU -/

-- `leafLensU`, `stU20` and UTAPE-STMT 27–30 are in `LvmS2GUXS`.

/-- `stU20`'s middle items are S2GU's (`midItemsU`: the pin, the typed phases at `E2`, the merged tape, the wire). -/
theorem midItemsS_stU20 : midItemsS stU20 = Lvm.VEq.midItemsU P20U := by
  have h5 : ((phases P20U).take 5).flatMap (·.2) = Lvm.VEq.commitI P20U ++ Lvm.VEq.midItemsU P20U := by
    rw [Lvm.VEq.phasesU_eq P20U rfl]
    simp only [List.take_succ_cons, List.take_zero, Lvm.VEq.midItemsU, Lvm.VEq.typedIT, List.flatMap_cons,
      List.flatMap_nil, List.append_assoc, List.append_nil]
  have hn : stU20.nOpen = (Lvm.VEq.commitI P20U ++ Lvm.VEq.midItemsU P20U).length := by
    rw [← h5]; rfl
  unfold midItemsS
  rw [hn, show stU20.items = schedule P20U from rfl, Lvm.VEq.scheduleU_eq P20U rfl,
    show Lvm.VEq.commitI P20U ++ (Lvm.VEq.midItemsU P20U ++ (Lvm.VEq.openMainI P20U ++ [])) =
      (Lvm.VEq.commitI P20U ++ Lvm.VEq.midItemsU P20U) ++ (Lvm.VEq.openMainI P20U ++ []) from
      (List.append_assoc _ _ _).symm, List.take_left, Lvm.VEq.commitI, List.singleton_append, List.drop_succ_cons,
    List.drop_zero]

/-- **UTAPE-STMT 31** (owner L, with V's `folP` of `tapeProgU`): **the pinned S2GU middle phases follow `stU20`'s
middle items** (`midFollowsPG20`'s twin). -/
theorem midFollowsPU20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (HR : TRefHypT N Q lay) :
    MidFollowsS (midItemsS stU20) (midP (midMk 4 relocU20 (midGU (N.inst Q lay)))) := fun x l a h ↦ by
  obtain ⟨hl, hr, he, -, -⟩ := HR.toT.fits
  have hrs := replayOK_stU20.rs
  rw [midItemsS_stU20] at hrs
  rw [(Lvm.VEq.fol_after (@Lvm.VEq.FolP.fol Lvm.VEq.capS Lvm.VEq.shpS Lvm.VEq.idxS _ _ _ _
    (Lvm.VEq.folP_midPU relocU20 (N.inst Q lay) hl Lvm.VEq.busDepth_P20 hr he x) []) h).1, itemKindsS_eq,
    midItemsS_stU20]
  exact Lvm.VEq.atomKinds_atomsOf _ _ (noPos_of_rs _ hrs)

/-! ## The window at S2GU (D-WIN (B)) -/

/-- **The window's first lane for the statement `x`** at S2GU: `32` when small (the stream at physical lane 32), M′'s
`winLo` (`40`) when big. -/
def loU (x : List UInt8) : ℕ := if Lvm.Shape.small x then 32 else Lvm.X.winLo

theorem loU_le (x : List UInt8) : loU x + Lvm.X.winC ≤ 64 := by unfold loU; split <;> decide

/-- `loU x` is the extractor's lane `loP stU20 π` when `x`'s `n` is π's word 14. -/
theorem loU_eq (π : RecursionFast.Proof) (x : List UInt8) (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) :
    loU x = loP stU20 π := by
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    omega
  have h3 : stU20.p.stage = 3 := rfl
  unfold loU loP
  by_cases hs : Lvm.Shape.small x = true
  · rw [if_pos hs, if_pos ⟨h3, hc.2 hs⟩]
  · rw [if_neg hs, if_neg fun h => hs (hc.1 h.2)]

/-- Stream word `i` (`i < 2^19`) of the statement's shape at S2GU, as an index into its window: the stream starts the
window (small: physical word `2i` from lane 32; big: word `i` from lane 40). -/
def sIdxU (x : List UInt8) (i : ℕ) : ℕ := if Lvm.Shape.small x then 2 * i else i

/-- **S2GU's left child read from its stream window.** -/
def childU20 (x : List UInt8) (w : List BF64) : Signed :=
  childWS stU20 fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (w.getD (sIdxU x i) 0) else BF64.toBitVec 0

/-- **The stream block `EXS` reads at S2GU is `childU20`'s** (`childWS_streamG20`'s twin: `wStreamS` at stage `3`). -/
theorem childWS_streamU20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) (hl : out.length = 2 ^ 20) :
    childWS stU20 (wStreamS stU20 π out) = childU20 x out := by
  rw [childU20]
  congr 1
  funext i
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    omega
  unfold wStreamS sIdxU
  rw [if_pos (show stU20.p.stage = 3 from rfl)]
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi, ite_eq_left hi]
    by_cases hs : Lvm.Shape.small x = true
    · rw [if_pos (hc.2 hs), if_pos hs]
    · rw [if_neg (fun h => hs (hc.1 h)), if_neg hs]
  · rw [ite_eq_right hi, ite_eq_right hi]

/-- The window from lane `loU x` holds the stream block (both shapes; `bigOf` in the small shape). -/
theorem winWU20 (x : List UInt8) (q : Column CMain.nu20) :
    (fun i ↦ if i < 2 ^ 19 then BF64.toBitVec ((Lvm.X.winOfL (loU x) q).getD (sIdxU x i) 0) else BF64.toBitVec 0) =
      Lvm.NS.wOfCol (recOfU20 x q) := funext fun i ↦ by
  rw [wOfCol_eq, show recOfU20 x q = recBU20 (Lvm.Shape.view x q) from rfl]
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi, getD_recBU20 _ hi]
    refine congrArg BF64.toBitVec ?_
    unfold sIdxU loU Lvm.Shape.view Lvm.X.winOfL Lvm.X.msgOfN
    cases hs : Lvm.Shape.small x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by simp only [Lvm.X.winC]; omega)]
      simp only [Option.map_some, Option.getD_some, CMain.sOffU20, Lvm.X.winLo]
      norm_num
    · simp only [↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by simp only [Lvm.X.winC]; omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [Lvm.Shape.getD_bigOf q (by simp only [CMain.sOffU20, CMain.nu20]; omega),
        show CMain.sOffU20 + i = 4 * 2 ^ 20 + (1 * 2 ^ 20 + i) by simp only [CMain.sOffU20]; omega,
        Lvm.Shape.bigWord_hi q (by norm_num) (by omega), Lvm.NS.wd]
      exact congrArg (fun k ↦ q.values.getD k 0) (by omega)
  · rw [ite_eq_right hi, getD_recBU20_ge _ (by omega)]

/-- **UTAPE-STMT 33** (owner L; D-WIN (B)): **S2GU's child from its window is the stream block's** (`childG20_win`'s
twin at the window `loU x`: `winWU20`, `trBridgeS stU20`). -/
theorem childU20_win (x : List UInt8) (q : Column CMain.nu20) :
    childU20 x (Lvm.X.winOfL (loU x) q) = Lvm.NS.childSP P20U (recOfU20 x q) := by
  rw [childU20, winWU20, childWS, trBridgeS stU20 outOK_stU20]
  rfl

/-- **UTAPE-STMT 34** (owner L): **`ext_eqU20`**: on accepted `S` proofs over good logs, S2GU's extractor decodes or is
the specification extractor of the certificate (`ext_eqG20` at `stU20`, `fmtU20`, `midGU`, the window `loU`; an
instance of `ext_eqS_gen`). -/
theorem ext_eqU20 (VS : SProg) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)
    (H : THypT (N.inst Q lay)) (HR : TRefHypT N Q lay)
    (hnode : ∀ vk, NodeSoundML loU VS vk (GoodUM (N.inst Q lay) H) childU20) :
    ∀ vk L c π, isS π = true → L.length ≤ logCap →
      Lvm.FS.Scheme.μ (kcertSFWτ fmtU20 (midSpecPinU20 (N.inst Q lay) H) leadOpenM_le_τU (midShapeU20 (N.inst Q lay))
        leadP_six (extJML loU loU_le (midShapeP_of (midShapeU20 (N.inst Q lay))) (hnode vk))) L < 1 →
      ((schemeSW fmtU20 vk (PSWithM (midP (midMk 4 relocU20 (midGU (N.inst Q lay)))))).V c π).runLog L =
        some true →
      (∃ w, EXS stU20 (accV VS) c π L = some w ∧ Rel (accV VS vk) c w) ∨
        EXS stU20 (accV VS) c π L = (schemeSW fmtU20 vk (PSWithM (midP (midMk 4 relocU20 (midGU (N.inst Q lay)))))).Ex
          (kcertSFWτ fmtU20 (midSpecPinU20 (N.inst Q lay) H) leadOpenM_le_τU (midShapeU20 (N.inst Q lay)) leadP_six
            (extJML loU loU_le (midShapeP_of (midShapeU20 (N.inst Q lay))) (hnode vk))).ext c π L :=
  fun vk L c π _ _ hμ hacc =>
    Lvm.ASM.ext_eqS_gen stU20 fmtU20 fmtOK_stU20 replayOK_stU20 progOK_stU20 outOK_stU20
      (midSpecP_ofτ (midSpecPinU20 (N.inst Q lay) H) (midShapeU20 (N.inst Q lay)) leadP_six) leadOpenM_le_τU leadP_six
      (midShapeP_of (midShapeU20 (N.inst Q lay))) loU loU_le (fun π x hn ↦ loU_eq π x hn) hnode
      (fun π x out hn hl => childWS_streamU20 π x out hn hl) (midFollowsPU20 N Q lay HR)
      (fun _ _ _ hp => Lvm.X.sFits_of_acc (S := subWith VS (EXS stU20 (accV VS)) (extXS stU20))
        (by show qVlvm ≤ Lvm.X.qMax; decide) (by rw [subWith_acc]; exact hp))
      vk L c π hμ hacc

/-- **`NodeSoundML` at S2GU from the pair form** (`nodeM_of_pair` at the stream block `recBU20` and the window
`loU`). -/
theorem nodeML_of_pairU {VS : SProg} {vk : RecursionFast.Digest} {G : GoodRel}
    {childW : List UInt8 → List BF64 → Signed} {child : Column 19 → Signed}
    (hch : ∀ x q, childW x (Lvm.X.winOfL (loU x) q) = child (recOfU20 x q))
    (hnode : NodeSound VS vk (fun x qm qr ↦ G x qm qr ∧ SBlkU qm qr) child) :
    NodeSoundML loU VS vk (GoodOfM recOfU20 (Lvm.Shape.Good₂ G)) childW := fun c x q hok hG ↦ by
  rw [hch]
  exact hnode c x (Lvm.Shape.view x q) (recBU20 (Lvm.Shape.view x q)) hok ⟨hG, sBlkU_recBU20 _⟩

/-- **UTAPE-STMT 35** (owner L): **S2GU's certificate at a typed instance** `N.inst Q lay` (`certificateSG20`'s
shape at the S2GU names, the window `loU`). -/
theorem certificateSU20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : THypT (N.inst Q lay))
    (HR : TRefHypT N Q lay) (hσ : Lvm.TypedV.SigInSL (layout0 P20U).s N.toN) (child : Column 19 → Signed)
    (hch : ∀ x q, childU20 x (Lvm.X.winOfL (loU x) q) = child (recOfU20 x q))
    (hnode : ∀ vk, NodeSound (VSUX N) vk (fun x qm qr ↦ GoodTU (N.inst Q lay) H x qm qr ∧ SBlkU qm qr) child) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith (VSUX N) (EXS stU20 (accV (VSUX N))) (extXS stU20)) :=
  certificateR_openW fmtU20 (VSUX N) (hq_VSUX N) (extS stU20 progOK_stU20 outOK_stU20 (VSUX N))
    (openSFW fmtU20
      { mid := midMk 4 relocU20 (midGU (N.inst Q lay))
        Good := GoodUM (N.inst Q lay) H
        Lm := leadF20
        τ := τU
        hτ := leadOpenM_le_τU
        hmid := midSpecPinU20 (N.inst Q lay) H
        hsh := midShapeU20 (N.inst Q lay)
        hL := leadP_six
        child := childU20
        lo := loU
        hlo := loU_le
        hnode := fun vk ↦ nodeML_of_pairU hch (hnode vk)
        refines := refinesU20 N Q lay HR hσ
        ext_eq := ext_eqU20 (VSUX N) N Q lay H HR fun vk ↦ nodeML_of_pairU hch (hnode vk) })

/-! ## The certificate at S2GU -/

set_option maxRecDepth 100000 in
/-- **UTAPE-STMT 36** (owner L): **`THypT` of the S2GU typed instance** from the guard's facts (`thypG20`'s). -/
theorem thypU20 (S : SFU20) : THypT TiU20 :=
  let c := thypCore_ofS S.1.st S.1.mb Pub.hdrLanesT S.2.2.1 p20_facts
  { ok := c.ok, maps := c.maps, acc := fun x ↦ Lvm.VEq.length_pubXT x, accC2 := fun x ↦ Lvm.VEq.c₂_pubXT x,
    hτ := c.hτ, sc := c.sc, layOk := c.layOk, keys := c.keys, width := c.width, fix := c.fix, widths := c.widths,
    μBus := c.μBus, errs := fun h ↦ Lvm.E2T.errsT_at _ (c.μBus h) (c.B0 h) }

/-- **UTAPE-STMT 37** (owner L): **`TRefHypT` at the S2GU instance** from the guard's facts (`trefG20`'s). -/
theorem trefU20 (S : SFU20) : TRefHypT NTU20 QU20 layU20 where
  ok := S.1.st.regs
  hlay := S.1.st.hlayOk
  mini := S.1.st.mini
  sc := (thypU20 S).sc
  phiT := fun pt hpt ↦ by
    show Lvm.E2T.PhiQGC cacheU20 pt = _
    have hc : cacheU20 = Lvm.Typed.cacheWX QU20 layU20 := cacheWXF_eq QU20 layU20 S.1.st.hlay
    rw [hc]
    exact Lvm.Typed.KT.PhiQGC_eqW QU20 layU20 S.1.st.hlay S.1.st.cache (hc ▸ S.2.2.2) pt hpt

/-- **S2GU's static guard.** -/
def staticOkU20 : Bool := staticOkBU20

/-- **The S2GU submission**: `V_S` at S2GU behind the static guard, S2GU's extractor. -/
def submissionU20 : Submission := subGS stU20 staticOkU20 (VSUX NTU20)

/-- **UTAPE-STMT 38** (owner L): **statement 18 at S2GU: the certificate of the S2GU submission** against the
declared claim (`certificateR_guardS` ∘ `certificateSU20` at `NTU20 QU20 layU20`, the child `childSP P20U` by
`childU20_win`, `nodeU20`). UTAPE-STMT 39: `Solution.certified := Lvm.CT.certificateU20S`,
`Solution.submission := Lvm.CT.submissionU20` (the switch, at release). -/
theorem certificateU20S :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionU20 :=
  certificateR_guardS stU20 progOK_stU20 outOK_stU20 fun h ↦
    have S := sfU20 h
    have hσ : Lvm.TypedV.SigInSL (layout0 P20U).s NTU20.toN := Lvm.TypedV.sigInSL_of (by
      simp only [staticOkU20, staticOkBU20, Bool.and_eq_true] at h
      exact h.1.1.1.2)
    certificateSU20 NTU20 QU20 layU20 (thypU20 S) (trefU20 S) hσ (Lvm.NS.childSP P20U)
      (fun x q ↦ childU20_win x q) (nodeU20 S (thypU20 S))

end Lvm.CT
