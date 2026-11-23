-- New for lvm2 MP-B cap pruning (CAP-L2, 2026-11-17): S2GB's certificate. DAY-0 STATEMENTS: every `sorry` is tagged
-- `-- CAP-FRZ L`. A proof never changes its statement; a needed change goes to the lead old → new.
import LvmS2GBDriveT
import LvmS2GBExt
import LvmS2GBExtEq
import LvmS2GBMid
import LvmS2GBRefT
import LvmS2GBRef
import LvmS2GBStmtC
import LvmS2GSCert

/-!
# The certificate at S2GB

`V_S` at S2GB reads a proof `π` whose compiled specification runs on an expansion `fillB P20B π w` (lead D-V1): the
siblings above each opened level's sent cap are taken from `w`, the π tail dropped. So the knowledge transfer goes
through an expansion:

* **`KState.congrX`**: a knowledge state transfers to a verifier `V'` and extractor `E'` when every proof `V'` accepts
  is extracted natively, or has an expansion `F π u` that `V` accepts with `E'` equal to `E` there;
* **`SSoundB`**, **`ks_subWithB`**, **`certificate_subWithB`**: `SSound`, `ks_subWith`, `certificate_subWith` through
  the expansion `F`;
* **`OpenSMWB`**, **`sSoundB_of_openSMWB`**, **`certificateR_openWB`**: `OpenSMWS`'s obligations at S2GB (V's
  `refinesB20` form, X's `ext_eqB_gen` form, the size range `SzB` from `V_S`);
* at S2GB: `szB_of_VSSB`, `driveItemsB_tail`, `piSizeB`, `hq_VSSB` (the middle phases' `midShapeB20`, `midSpecPinB20`
  are in `LvmS2GBMid`), `certificateSB20` (the typed instance, through V's `refinesB20` and X's `ext_eqB20`),
  `thypB20`, `certificateR_guardSB`, `submissionS20B`, **`certificateS20B`**.
-/

set_option autoImplicit false

namespace Lvm.FS

open RecursionFast
open scoped NNReal

/-- **Transfer through an expansion**: every proof `V'` accepts on a log of potential below `1` is either extracted
by `E'` directly, or has an expansion `F π u` accepted by `V` with `E'` agreeing with `E` on it. -/
def KState.congrX {R : Digest → Wit → Prop} {V V' : Digest → Proof → OProg Bool}
    {E E' : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} (k : KState R V E ε) (F : Proof → List UInt8 → Proof)
    (h : ∀ L c π, L.length ≤ logCap → k.μ L < 1 → (V' c π).runLog L = some true →
      (∃ w, E' c π L = some w ∧ R c w) ∨
        ∃ u, (V c (F π u)).runLog L = some true ∧ E' c π L = E c (F π u) L) :
    KState R V' E' ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L c π hl hμ hacc := by
    rcases h L c π hl hμ hacc with hw | ⟨u, hv, he⟩
    · exact hw
    · rw [he]; exact k.final L c (F π u) hl hμ hv

end Lvm.FS

namespace Lvm.T

open RecursionFast
open RecursionFast.WitnessSending (encode decode encodeF)
open scoped NNReal

/-- **The `S` branch's knowledge soundness through an expansion `F`** (`SSound` with the scheme run on `F π u`). -/
def SSoundB (F : Proof → List UInt8 → Proof) (VS : SProg) (E : Digest → Proof → Log → Option Wit) (vk : Digest) :
    Prop :=
  ∃ (Sc : Lvm.FS.Scheme) (K : Lvm.FS.KCert Sc (Rel (accV VS vk))),
    Lvm.FS.Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧
    ∀ L c π, isS π = true → L.length ≤ logCap → Lvm.FS.Scheme.μ K L < 1 → (VS vk c π).runLog L = some true →
      (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
        ∃ u, (Sc.V c (F π u)).runLog L = some true ∧ E c π L = Sc.Ex K.ext c (F π u) L

/-- **Knowledge soundness of `Vwith VS`** from `SSoundB` (`ks_subWith` through the expansion). -/
theorem ks_subWithB (F : Proof → List UInt8 → Proof) (VS : SProg) (E : Digest → Proof → Log → Option Wit)
    (ext : XProg) (hq : ∀ H vk c π, isS π = true → ((VS vk c π).queries H).length ≤ qVlvm)
    (hEW : ∀ c π L, isS π = false → E c π L = decode π) (vk : Digest) (hS : SSoundB F VS E vk) :
    KS (Rel ((subWith VS E ext).acc vk)) ((subWith VS E ext).V vk) (subWith VS E ext).E
      (subWith VS E ext).ε (subWith VS E ext).qV := by
  obtain ⟨Sc, K, hε, hE⟩ := hS
  rw [subWith_acc, subWith_ε]
  have k := (Lvm.FS.KState.congrX (Lvm.FS.Scheme.kstate_of_kcert K) F (V' := Vwith VS vk) (E' := E) (by
    intro L c π hl hμ hacc
    cases h : isS π
    · left
      obtain ⟨w, hw, hR⟩ := V_W_runLog VS vk c π h hacc
      exact ⟨w, by rw [hEW c π L h, hw], hR⟩
    · rw [V_S VS vk c π h] at hacc
      exact hE L c π h hl hμ hacc)).mono hε
  exact k.ks fun H c π => V_queries_le VS H (hq H) vk c π

/-- **The contract's `Certificate`** of `subWith VS E ext` from the five obligations, `SSoundB`'s form. -/
theorem certificate_subWithB (F : Proof → List UInt8 → Proof) (VS : SProg) (E : Digest → Proof → Log → Option Wit)
    (ext : XProg) (hq : ∀ H vk c π, isS π = true → ((VS vk c π).queries H).length ≤ qVlvm)
    (hc : Computes ext E Lvm.X.fuel) (hsz : ext.body.size ≤ progCap)
    (hEW : ∀ c π L, isS π = false → E c π L = decode π) (hS : ∀ vk, SSoundB F VS E vk) :
    Certificate (subWith VS E ext) where
  secure vk := ks_subWithB F VS E ext hq hEW vk (hS vk)
  complete vk := by
    rw [subWith_δ]; exact complete VS _ rfl rfl rfl vk
  computes := hc
  cap := ⟨by rw [subWith_ε]; rfl, by rw [subWith_δ]; exact zero_le, show qVlvm ≤ 2 ^ 16 by decide,
    Lvm.X.fuel_le_budget, hsz⟩

end Lvm.T

namespace Lvm.ASM

open RecursionFast Lvm Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped NNReal ENNReal

/-- **M′'s open obligations at a format, S2GB** (`OpenSMWS` over `schemeSWB` on the expansion `fillB P20B π w`):
`V_S` accepting gives an accepted expansion (V's `refinesB20` form) and the size range `SzB`; on an accepted expansion
of a proof in `SzB`, `E` decodes a witness or is the scheme's extractor there (X's `ext_eqB_gen` form). -/
structure OpenSMWB (f : SFmt) (VS : SProg) (E : Digest → Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  τ : ℝ≥0∞ := εS
  hτ : leadOpenM ≤ τ := by exact leadOpenM_le_εS
  hmid : MidSpecMτ mid Good εS Lm τ
  hLm : Lm ≤ εS
  hsh : MidShapeM mid
  child : List UInt8 → List BF64 → Signed
  sl : List UInt8 → List BF64 → Sig
  lo : List UInt8 → ℕ := fun _ ↦ Lvm.X.winLo
  hlo : ∀ x, lo x + Lvm.X.winC ≤ 64 := by intro; decide
  hnode : ∀ vk, NodeSoundMLS lo VS vk Good child sl
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ∃ w : List UInt8, ((schemeSWB f vk (PSWithM mid)).V c (fillB P20B π w)).runLog L = some true
  hsz : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true → Lvm.XB.SzB π
  ext_eq : ∀ vk L c π (w : List UInt8), isS π = true → Lvm.XB.SzB π → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSMWBτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))) L < 1 →
    ((schemeSWB f vk (PSWithM mid)).V c (fillB P20B π w)).runLog L = some true →
    (∃ wt, E c π L = some wt ∧ Rel (accV VS vk) c wt) ∨
      E c π L = (schemeSWB f vk (PSWithM mid)).Ex
        (kcertSMWBτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))).ext c (fillB P20B π w) L

/-- **`SSoundB` from M′'s open obligations at S2GB.** -/
theorem sSoundB_of_openSMWB (f : SFmt) {VS : SProg} {E : Digest → Proof → Log → Option Wit} (o : OpenSMWB f VS E)
    (vk : Digest) : SSoundB (fillB P20B) VS E vk :=
  ⟨schemeSWB f vk (PSWithM o.mid), kcertSMWBτ f o.hmid o.hτ o.hLm o.hsh (extJMLS o.lo o.hlo o.hsh (o.hnode vk)),
    εFS_kcertSMWBτ f o.hmid o.hτ o.hLm o.hsh _, fun L c π hS hl hμ hacc ↦ by
      obtain ⟨u, hu⟩ := o.refines vk L c π hS hacc
      rcases o.ext_eq vk L c π u hS (o.hsz vk L c π hS hacc) hl hμ hu with hw | he
      · exact .inl hw
      · exact .inr ⟨u, hu, he⟩⟩

end Lvm.ASM

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.E2F
open scoped NNReal ENNReal

/-- **The certificate from the open obligations at a format, S2GB** (`certificateR_openWS` over `OpenSMWB`). -/
theorem certificateR_openWB (f : SFmt) (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (X : ExtF20) (o : OpenSMWB f VS X.E) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS X.E X.ext) :=
  certificateR_of (certificate_subWithB (fillB P20B) VS X.E X.ext (fun H vk c π _ ↦ hq H vk c π) X.computes X.size
    X.W (sSoundB_of_openSMWB f o)) (boundsOK_claim VS X.E X.ext)

end Lvm.CT

/-! ## At S2GB -/

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q Lvm.E2U Lvm.E2S
open Lvm.E2T (TNatT TRefHypT)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **CAP-FRZ L** (D-X2): `V_S` at S2GB accepts only proofs in the size range `SzB` (`parseOkB`). -/
theorem szB_of_VSSB (N : TNatT) (vk c : RecursionFast.Digest) (π : RecursionFast.Proof) (L : Log)
    (h : (VSSB N vk c π).runLog L = some true) : Lvm.XB.SzB π := by
  unfold VSSB at h
  by_cases hp : parseOkB P20B vk c π = true
  · exact parseOkB_size hp
  · rw [ite_eq_right hp] at h
    simp [OProg.runLog] at h

/-- **CAP-FRZ L** (RE-FREEZE R4): **S2GB's certificate at a typed instance** `N.inst Q lay` (`certificateSS20`'s twin
over `OpenSMWB`: V's `refinesB20` at `TRefHypTB`, X's `ext_eqB20`, `szB_of_VSSB`, the window bridges and the node
relation in pair form). -/
theorem certificateSB20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : THypSB (N.inst Q lay))
    (HR : Lvm.E2T.TRefHypTB N Q lay) (hσ : Lvm.TypedV.SigInSL (layout0 P20B).s N.toN) (child : Column 19 → Signed)
    (sl : List UInt8 → Column CMain.nu20 → Sig)
    (hch : ∀ x q, Lvm.XB.childB20 x (Lvm.X.winOfL (loU x) q) = child (recOfU20 x q))
    (hsl : ∀ x q, sigLeafS20 x (Lvm.X.winOfL (loU x) q) = sl x (Lvm.Shape.view x q))
    (hnode : ∀ vk, NodeSoundS (VSSB N) vk
      (fun x qm qr ↦ GoodTSB (N.inst Q lay) H x qm qr ∧ SBlkU qm qr) child sl) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith (VSSB N) (Lvm.XB.EXB20 (accV (VSSB N))) Lvm.XB.extXB20) :=
  certificateR_openWB fmtB20 (VSSB N) (hq_VSSB N) (extB20 (VSSB N))
    { mid := midP (midMk 4 relocU20 (midGB (N.inst Q lay)))
      Good := GoodSMB (N.inst Q lay) H
      Lm := leadP leadF20
      τ := τU
      hτ := leadOpenM_le_τU
      hmid := midSpecP_ofτ (midSpecPinB20 (N.inst Q lay) H) (midShapeB20 (N.inst Q lay)) leadP_six
      hLm := leadP_six
      hsh := midShapeP_of (midShapeB20 (N.inst Q lay))
      child := Lvm.XB.childB20
      sl := sigLeafS20
      lo := loU
      hlo := loU_le
      hnode := fun vk ↦ nodeMLS_of_pairS hch hsl (hnode vk)
      refines := refinesB20 N Q lay HR hσ H.lin
      hsz := fun vk L c π _ h ↦ szB_of_VSSB N vk c π L h
      ext_eq := fun vk L c π w _ hsz _ hμ hacc ↦
        ext_eqB20 (VSSB N) N Q lay H (fun vk ↦ nodeMLS_of_pairS hch hsl (hnode vk)) vk L c π w hsz hμ hacc }

/-- **The S2GB submission behind a guard `b`**: `V_S` at S2GB, S2GB's extractor. -/
def subGB (b : Bool) (VS : SProg) : Submission :=
  subWith (Lvm.Fin.VSg b VS) (Lvm.XB.EXB20 (accV (Lvm.Fin.VSg b VS))) Lvm.XB.extXB20

/-- `THypSB` of a stage's typed instance with the mini-bus at depth 13 from the guard's static facts
(`thypCore_ofS`'s proof at `busDepth = 13`, `tableEvals = 888`). -/
theorem thypSB_ofS {C : Lvm.QAsm.QCfg} {F : TFrz} {Q : Lvm.Loop.Program} {tl : Lay} {N : TypedV.TNat}
    (st : StaticFactsTX C F Q tl N) (hmb0 : N.mbT = mbTOf C F) (hone : Lvm.T.oneOkB tl = true)
    (hC : C.p.nuMain = 23 ∧ C.p.nuRec = 19 ∧ C.p.busDepth = 13 ∧ C.p.tableEvals = 888)
    (hlin : Lvm.M3.mbLinB N.mbT = true) :
    THypSB (N.instL Pub.hdrLanesT Q tl) := by
  have hmb : (N.instL Pub.hdrLanesT Q tl).mbT = mbTOf C F := hmb0
  have hm : TypedV.fitsMiniB C.p (mbTOf C F) = true := hmb ▸ st.mini
  unfold TypedV.fitsMiniB at hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hb⟩, -⟩, -⟩, -⟩, hf⟩, hg⟩, hh⟩, -⟩ := hm
  have ht : Lvm.M3.tabsOkB (mbTOf C F) = true := tabsOkB_mbT _ _ _ _
  have hsc : Lvm.M3.AllSc (mbTOf C F) := Lvm.M3.allSc_of_B ht
  have hsum : Lvm.M3.sumcheckTabs (mbTOf C F) = mbTOf C F := sc_all _ hsc
  have hτ : ∀ t ∈ (N.instL Pub.hdrLanesT Q tl).mbT, t.τ ≤ Lvm.M3.lay26.μ :=
    hmb ▸ hτ_of_hi (com_mbT _ _ _ _ fun _ ↦ rfl) hh
  have hμ : ∀ (h : ∀ t ∈ (N.instL Pub.hdrLanesT Q tl).mbT, t.τ ≤ Lvm.M3.lay26.μ),
      (Lvm.M3.inst Lvm.M3.lay26 (N.instL Pub.hdrLanesT Q tl).mbT h).μBus = 13 := fun h ↦ by
    have e : (Lvm.M3.inst Lvm.M3.lay26 (N.instL Pub.hdrLanesT Q tl).mbT h).μBus = C.p.busDepth := by
      rw [LeanVM.Protocol.M3Instance.μBus, Lvm.VEq.pushLeaves_inst, hmb, hb, Lvm.VEq.log2Ceil_eq_clog,
        Lvm.M3.pushLeavesR, hsum]
    rw [e, hC.2.2.1]
  exact
    { ok := ⟨st.hlay, src_one_of N Q tl hone⟩
      maps := mapsFit_inst N Q tl st.hlayOk (by
        have h := st.regs
        rwa [hC.1, hC.2.1] at h)
      acc := fun x ↦ by simp only [pubXTS, pubOfWS, List.length_map, List.length_range]; rfl
      accC2 := fun x ↦ ⟨fun e he ↦ by
        simp only [pubXTS, pubOfWS, List.mem_map] at he
        obtain ⟨i, -, rfl⟩ := he
        rfl, rfl⟩
      hτ := hτ
      sc := hmb ▸ hsc
      layOk := hmb ▸ layOk_of_fit ⟨hC.1, hC.2.1⟩ hg
      keys := hmb ▸ Lvm.M3.keys_of_B ht
      width := hmb ▸ Lvm.M3.width_pos_of_B ht
      fix := hmb ▸ fixOk_mbT _ _ _ _
      widths := by
        rw [hmb]
        rw [hsum] at hf
        rw [← hf, hC.2.2.2]
        norm_num
      lin := hlin
      μBus := hμ
      errs := fun h ↦ Lvm.E2L.errsL_atB _ (hμ h) }

/-- **CAP-FRZ L** (RE-FREEZE R4): **`THypSB` of the S2GB typed instance** from the guard's facts (`thypS20`'s twin;
the errors at depth 13 by `errsL_atB`). -/
theorem thypB20 (S : SFB20) : THypSB (NTB20.inst Lvm.E2Q.QB20 layB20) :=
  thypSB_ofS S.1.st S.1.mb S.2.2.1 ⟨rfl, rfl, rfl, rfl⟩ S.2.2.2.2

/-- **CAP-FRZ L** (RE-FREEZE R4, proved): **the guarded certificate at S2GB** (`certificateR_guardS`'s twin for
`subGB`): the guard off rejects; on, the certificate of the unguarded submission. -/
theorem certificateR_guardSB {b : Bool} {VS : SProg}
    (h : b = true → CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (Lvm.XB.EXB20 (accV VS)) Lvm.XB.extXB20)) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subGB b VS) := by
  cases b with
  | false =>
    exact certificateR_claim _ _ _
      ⟨fun H vk c π _ => by simp [Lvm.Fin.VSg, OProg.queries], Lvm.XB.computesXB20 _, Lvm.XB.extXB20_size,
        Lvm.XB.EXB20_Wn _, fun vk => Lvm.Fin.sSound_reject VS _ vk⟩
  | true => exact h rfl

/-- **The S2GB submission**: `V_S` at S2GB behind the static guard `staticOkBB20`, S2GB's extractor. -/
def submissionS20B : Submission := subGB staticOkBB20 (VSSB NTB20)

/-- **CAP-FRZ L**: **the certificate of the S2GB submission** against the declared claim (the guard off rejects; on,
`certificateSB20` with `THypSB`/`TRefHypT` from the guard's facts, the window bridges and `nodeB20`).
`Solution.certified := Lvm.CT.certificateS20B`; axioms exactly `propext`, `Classical.choice`, `Quot.sound`. -/
theorem certificateS20B :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionS20B :=
  certificateR_guardSB fun h ↦
    have S := sfB20 h
    certificateSB20 NTB20 Lvm.E2Q.QB20 layB20 (thypB20 S) (trefB20 S) S.1.sig (Lvm.NS.childSPB P20B) slM20
      childB20_win sigLeafS20_win (nodeB20 S (thypB20 S))

end Lvm.CT
