-- New for lvm2 σ_LEAF (SLF-L, 2026-11-16; assembled at integration, SLF-I): S2GS's certificate. The guard's facts
-- (`sfS20`), the typed instance's hypotheses (`thypS20`, `trefS20`), the window bridges (`childS20_win`,
-- `sigLeafS20_win`) and the node relation (`nodeS20`) give `certificateS20S`.
import LvmS2GSXS
import LvmS2GSStmtC
import LvmCertTHypCore

/-!
# The certificate at S2GS

* **`nodeMLS_of_pairS`**: `NodeSoundMLS` at S2GS's window from the pair form `NodeSoundS` (`nodeML_of_pairU`'s twin; the
  right leaf's signature read from the window is the node relation's `sl x (view x q)`).
* **`certificateSS20`** (SLF-STMT 9a): the certificate at a typed instance from `THypS`, `TRefHypT`, the window bridges
  and the node relation (`NodeSoundS`: the right leaf's `SigOk` from the node circuit's second walk, SLF-C's
  `qSigLeaf_sound`).
* **`certificateS20S`** (SLF-STMT 9): the certificate of `submissionS20 = subGS stS20 staticOkS20 (VSSX NTS20)`; axioms
  exactly `propext`, `Classical.choice`, `Quot.sound` at release.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q Lvm.E2U Lvm.E2S
open Lvm.E2T (TNatT TRefHypT)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **`NodeSoundMLS` at S2GS from the pair form** (`nodeML_of_pairU`'s twin with the right leaf's signature). -/
theorem nodeMLS_of_pairS {VS : SProg} {vk : RecursionFast.Digest} {G : GoodRel}
    {childW : List UInt8 → List BF64 → Signed} {child : Column 19 → Signed}
    {slW : List UInt8 → List BF64 → Sig} {sl : List UInt8 → Column CMain.nu20 → Sig}
    (hch : ∀ x q, childW x (Lvm.X.winOfL (loU x) q) = child (recOfU20 x q))
    (hsl : ∀ x q, slW x (Lvm.X.winOfL (loU x) q) = sl x (Lvm.Shape.view x q))
    (hnode : NodeSoundS VS vk (fun x qm qr ↦ G x qm qr ∧ SBlkU qm qr) child sl) :
    NodeSoundMLS loU VS vk (GoodOfM recOfU20 (Lvm.Shape.Good₂ G)) childW slW := fun c x q hok hG ↦ by
  rw [hch, hsl]
  exact hnode c x (Lvm.Shape.view x q) (recBU20 (Lvm.Shape.view x q)) hok ⟨hG, sBlkU_recBU20 _⟩

/-- **SLF-STMT 9a** (owner L): **S2GS's certificate at a typed instance** `N.inst Q lay` (`certificateSL20`'s twin;
the right leaf's signature from the window, `sigLeafS20`). -/
theorem certificateSS20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : THypS (N.inst Q lay))
    (HR : TRefHypT N Q lay) (hσ : Lvm.TypedV.SigInSL (layout0 P20S).s N.toN) (child : Column 19 → Signed)
    (sl : List UInt8 → Column CMain.nu20 → Sig)
    (hch : ∀ x q, childS20 x (Lvm.X.winOfL (loU x) q) = child (recOfU20 x q))
    (hsl : ∀ x q, sigLeafS20 x (Lvm.X.winOfL (loU x) q) = sl x (Lvm.Shape.view x q))
    (hnode : ∀ vk, NodeSoundS (VSSX N) vk (fun x qm qr ↦ GoodTS (N.inst Q lay) H x qm qr ∧ SBlkU qm qr) child sl) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith (VSSX N) (EXS stS20 (accV (VSSX N))) (extXS stS20)) :=
  certificateR_openWS fmtS20 (VSSX N) (hq_VSSX N) (extS stS20 progOK_stS20 outOK_stS20 (VSSX N))
    (openSFWS fmtS20
      { mid := midMk 4 relocU20 (midGS (N.inst Q lay))
        Good := GoodSM (N.inst Q lay) H
        Lm := leadF20
        τ := τU
        hτ := leadOpenM_le_τU
        hmid := midSpecPinS20 (N.inst Q lay) H
        hsh := midShapeS20 (N.inst Q lay)
        hL := leadP_six
        child := childS20
        sl := sigLeafS20
        lo := loU
        hlo := loU_le
        hnode := fun vk ↦ nodeMLS_of_pairS hch hsl (hnode vk)
        refines := refinesS20 N Q lay HR hσ H.lin
        ext_eq := ext_eqS20 (VSSX N) N Q lay H HR fun vk ↦ nodeMLS_of_pairS hch hsl (hnode vk) })

/-! ## The certificate at S2GS -/

open Lvm.E2Q (NTS20 QS20 layS20 cfgS20 cacheS20 staticOkBS20 SFS20 sfS20 nodeS20)
open Lvm.E2L (errsL_at)

/-- **`THypS` of the S2GS typed instance** from the guard's facts (`thypL20`'s twin; `acc_in` read at `hdrFixS`). -/
theorem thypS20 (S : SFS20) : THypS (NTS20.inst QS20 layS20) :=
  have c := thypCore_ofS S.1.st S.1.mb Pub.hdrLanesT S.2.2.1 p20_facts
  { ok := c.ok, maps := c.maps,
    acc := fun x ↦ by simp only [pubXTS, pubOfWS, List.length_map, List.length_range]; rfl,
    accC2 := fun x ↦ ⟨fun e he ↦ by
      simp only [pubXTS, pubOfWS, List.mem_map] at he
      obtain ⟨i, -, rfl⟩ := he
      rfl, rfl⟩,
    hτ := c.hτ, sc := c.sc, layOk := c.layOk, keys := c.keys, width := c.width, fix := c.fix, widths := c.widths,
    lin := S.2.2.2.2, μBus := c.μBus, errs := fun h ↦ errsL_at _ (c.μBus h) }

/-- **`TRefHypT` at the S2GS instance** from the guard's facts (`trefL20`'s twin). -/
theorem trefS20 (S : SFS20) : TRefHypT NTS20 QS20 layS20 where
  ok := S.1.st.regs
  hlay := S.1.st.hlayOk
  mini := S.1.st.mini
  sc := (thypS20 S).sc
  phiT := fun pt hpt ↦ by
    show Lvm.E2T.PhiQGC cacheS20 pt = _
    have hc : cacheS20 = Lvm.Typed.cacheWX QS20 layS20 := cacheWXF_eq QS20 layS20 S.1.st.hlay
    rw [hc]
    exact Lvm.Typed.KT.PhiQGC_eqW QS20 layS20 S.1.st.hlay S.1.st.cache (hc ▸ S.2.2.2.1) pt hpt

/-- **S2GS's left child from its window is the stream block's** (`childL20_win`'s twin). -/
theorem childS20_win (x : List UInt8) (q : Column CMain.nu20) :
    childS20 x (Lvm.X.winOfL (loU x) q) = Lvm.NS.childSP P20S (recOfU20 x q) := by
  rw [childS20, winWU20, childWS, trBridgeS stS20 outOK_stS20]
  rfl

/-- **The right leaf's signature from S2GS's window is the candidate's** (`sigLeafS20` = `slM20` on the viewed
`C_main`: words `slWP … slWP + 596` lie in the stream block). -/
theorem sigLeafS20_win (x : List UInt8) (q : Column CMain.nu20) :
    sigLeafS20 x (Lvm.X.winOfL (loU x) q) = slM20 x (Lvm.Shape.view x q) := by
  rw [sigLeafS20, slM20]
  refine Lvm.ASM.sigOfP_congr fun j hj ↦ ?_
  have h := congrFun (winWU20 x q) (slWP + j)
  rw [if_pos (by unfold slWP; omega)] at h
  exact h

/-- **S2GS's static guard.** -/
def staticOkS20 : Bool := staticOkBS20

/-- **The S2GS submission**: `V_S` at S2GS behind the static guard, S2GS's extractor. -/
def submissionS20 : Submission := subGS stS20 staticOkS20 (VSSX NTS20)

/-- **SLF-STMT 9** (owner L): **the certificate of the S2GS submission** against the declared claim
(`certificateR_guardS` ∘ `certificateSS20` with `THypS`/`TRefHypT` from the guard, `childS20_win`, the window's
`σ_leaf` bridge `sigLeafS20_win` and `nodeS20`). `Solution.certified := Lvm.CT.certificateS20S`; axioms exactly
`propext`, `Classical.choice`, `Quot.sound`. -/
theorem certificateS20S :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionS20 :=
  certificateR_guardS stS20 progOK_stS20 outOK_stS20 fun h ↦
    have S := sfS20 h
    certificateSS20 NTS20 QS20 layS20 (thypS20 S) (trefS20 S) S.1.sig (Lvm.NS.childSP P20S) slM20
      childS20_win sigLeafS20_win (nodeS20 S (thypS20 S))

end Lvm.CT
