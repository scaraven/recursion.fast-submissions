-- lvm2 E2F-G (import pruning, a pure move out of `LvmCertM20`): roll 11's certificate `certificateM20` and the
-- node pieces only it uses (`posLanesKS20`/`posLanesS20`, `posOkMT`, `nodeT20B`, `nodeT20`, `nodeM20`, `ext_eqM20`,
-- `openM20`), which need roll 11's typed HAR at `P20` (`LvmQTypedHar20`). `LvmCertM20` keeps the parts the S2GF
-- certificate shares, so its import closure no longer holds roll 11's decisions. Text unchanged.
import LvmCertM20
import LvmQTypedHar20
import LvmFinPos
import LvmQAsmArith2WhirP
import LvmE2QNodeFOff
import LvmE2VWidthsFOff
import LvmFinPosOff
import LvmMPCertOff
import LvmMPMidTOff
import LvmNodeSoundTOff
import LvmQAsmArith2WhirPOff
import LvmXSChildOff

set_option autoImplicit false

-- New for lvm2 roll 11 (M′ `S2GM`, R11-N): FIN-BV's `PosLanes` for the child's one opening (`C_main`'s, openings
-- `0 … 2` from `openU P20 + 15`), as B1's `posLanesM20` (L-D's, in `LvmFinPos`; removed at M′) was for its second.

/-!
# The child's position lanes at `S2GM`

* **`posLanesKS20`** (`decide +kernel` on `posLanesKB`, the extractor's blocks): level `i` of `C_main`'s opening is
  Q_link's opening `i`; its first positions entry starts block `1268`, `1304`, `1322` [exact, evaluated].
* **`posLanesS20`**: `PosLanes P20 g ood mainLevels (openU P20 + 15) 0` (`posLanes_of`, `posLanesR_of_K`).
-/

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Har Lvm.QLink

set_option maxRecDepth 200000 in
/-- The child's opening's position lanes through the extractor's blocks (one decision). -/
theorem posLanesKS20 : PosLanesK P20.grind P20.mainOod P20.mainLevels (openU P20 + 15) 0 [1268, 1304, 1322] := by
  -- the openings and `openU` read off `opens_P20` and `phB20`, not evaluated again (GOLF-DEC3)
  have hU : openU P20 = 28873 := by rw [openU, phB20]
  have h : posLanesKB P20.grind P20.mainOod P20.mainLevels (28873 + 15) 0 [1268, 1304, 1322] = true := by
    rw [posLanesKB, Lvm.QAsm.opens_P20, Lvm.X.blocks, schedule, phases_P20_lit]
    decide +kernel
  rw [hU]
  exact posLanesK_of_B h

/-- **FIN-BV's `PosLanes` for the child's `C_main` opening** at `S2GM` (`BVT.posm`'s `hPL`). -/
theorem posLanesS20 : PosLanes P20 P20.grind P20.mainOod P20.mainLevels (openU P20 + 15) 0 :=
  posLanes_of Lvm.QAsm.hS20.1 (posLanesR_of_K posLanesKS20)

end Lvm.Fin

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.Bits Lvm.SigBits Lvm.Har LeanVM.Protocol
open Lvm.VEq (pubX)

/-- **`BVT`'s `posm`** (M′ `S2GM`: the child's one opening, `C_main`'s, openings `0 + i` from `openU P20 + 15`;
B1: `C_main`'s openings `2 + i` after `C_rec`'s): its position cells hold `F`'s positions. -/
theorem posOkMT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr)
    (hL : LaneLink P20 (wsC qr)) :
    PosOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) (memT x qm qr) (sigC qr) 0 P20.mainLevels
      (openU P20 + 15) :=
  Lvm.Fin.posOk_of _ 0 (fun i => by rw [Nat.zero_add]; rfl) Lvm.Fin.posLanesS20 hS20 hL hQ20
    (posCellsT S H hchk hok hb hG hSB)

/-- **`nodeT20`, the `BITS` facts discharged** (input: the guard's `nodeChkB`, `SF20.chk`; M′ `S2GM`: on
stream-block pairs, `nodeSoundTG` at `GoodT ∧ SBlk`). -/
theorem nodeT20B (S : Lvm.CT.SF20) (H : THyp Lvm.CT.Ti20) (vk : RecursionFast.Digest)
    (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true) :
    NodeSound VSB20 vk (fun x qm qr ↦ GoodT Lvm.CT.Ti20 H x qm qr ∧ SBlk qm qr) childS := by
  have hin : inMapB cfg20 QB20 layT20 NT20 = true := by
    simp only [nodeChkB, Bool.and_eq_true] at hchk; exact hchk.1.1
  refine nodeSoundTG vk H S _ (fun _ _ _ h ↦ h.1) (fun _ _ _ _ _ _ hG ↦ readdT S H hchk hG.1 hG.2)
    (fun _ _ qm qr hok hb hG ↦ inMapT S.toStaticFactsT hin S.sig qm qr hG.2 hok hb)
    (fun _ x qm qr _ _ _ ↦ hqltT S.toStaticFactsT x qm qr)
    (fun _ x qm qr hok hb hG ↦ hposT (outsOn_memT S H hG.1)
      (inMapT S.toStaticFactsT hin S.sig qm qr hG.2 hok hb).stream)
    (fun _ _ _ _ _ _ hG ↦ sigBitsT S H hG.1) ?_
  intro c x qm qr hok hb hG' hm hL hLk hrun
  obtain ⟨hG, hSB⟩ := hG'
  have hv := outsOn_memT S H hG
  have hn := nRange_on (childOkT S H hchk hok hb hG hSB) hm.hd hL vk (hdrOf x).cL
  have hbv : BVT vk x qm qr :=
    ⟨sBits_on hv, nBits_on (sigBitsT S H hG), hn.1, hn.2, posOkMT S H hchk hok hb hG hSB hL, pw_on hv (by decide)⟩
  obtain ⟨h1, h2⟩ := harithT20 S H hok hb hG hm hL hLk hrun hbv
  exact decideFT_of S H hG.1.2 h1 h2

end Lvm.NS

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26)
open Lvm.VEq (pubX)
open scoped NNReal ENNReal

/-- **O10, typed: `NodeSound` on `GoodT`** (the arithmetisation's soundness of the B program: `typed_sound` with
`Inputs` on the virtual regions, QLT's constants `S.cst`, `hwf`/`hlay`/`hinj` from `S`, the mini-bus's `ReaddOk`;
then roll 7's Q_link, Q_sig and Q_arith on any memory with `Holds`). Owner **L-D**. M′ (R11-IS, approved by
R11-LEAD): on stream-block pairs only (`SBlk qm qr`: `qr` is `qm`'s block `S`, as `recOf20` makes it; the mini-bus's
seeds are `S`'s `C_main` words while `zOf` reads the stream from `qr`). B1: every `GoodT` pair. -/
theorem nodeT20 (S : SF20) (H : THyp Ti20) (vk : RecursionFast.Digest) :
    NodeSound VSB20 vk (fun x qm qr ↦ GoodT Ti20 H x qm qr ∧ Lvm.NS.SBlk qm qr) Lvm.NS.childS :=
  Lvm.NS.nodeT20B S H vk S.chk

end Lvm.CT

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- `NodeSoundM` at `P20` from the pair form on stream-block pairs (`nodeT20`, L-D), `sBlk_recB20` and the window
fact. -/
theorem nodeM20 (S : SF20) (H : THyp Ti20) (vk : RecursionFast.Digest) :
    NodeSoundM VSB20 vk (GoodTM recOf20 Ti20 H) childM20 := fun c x q hok hG ↦ by
  rw [win20]
  exact nodeT20 S H vk c x (Lvm.Shape.view x q) (recB20 (Lvm.Shape.view x q)) hok
    ⟨hG, sBlk_recB20 _⟩

/-- **O5c at M′**: the executable extractor on good logs. -/
theorem ext_eqM20 (S : SF20) (H : THyp Ti20) :
    ∀ vk L c π, isS π = true → L.length ≤ logCap →
      Lvm.FS.Scheme.μ (kcertSM (midSpecM_T₂ H relocLaw20) le_rfl (midShapeM_T₂ Ti20 reloc20)
        (extJM (midShapeM_T₂ Ti20 reloc20) (nodeM20 S H vk))) L < 1 →
      ((schemeS vk (PSWithM (midM reloc20 (midT₂ Ti20)))).V c π).runLog L = some true →
      (∃ w, Lvm.X.EXM (accV VSB20) c π L = some w ∧ Rel (accV VSB20 vk) c w) ∨
        Lvm.X.EXM (accV VSB20) c π L = (schemeS vk (PSWithM (midM reloc20 (midT₂ Ti20)))).Ex
          (kcertSM (midSpecM_T₂ H relocLaw20) le_rfl (midShapeM_T₂ Ti20 reloc20)
            (extJM (midShapeM_T₂ Ti20 reloc20) (nodeM20 S H vk))).ext c π L := by
  exact fun vk L c π _ _ hμ hacc =>
    Lvm.ASM.ext_eqM_gen (midSpecM_T₂ H relocLaw20) le_rfl (midShapeM_T₂ Ti20 reloc20) (nodeM20 S H)
      (fun π x out hn hl => childW_stream20 π x out hn hl) (Lvm.VEq.midFollowsM20 S H reloc20)
      (fun _ _ _ hp => Lvm.X.sFits_of_acc (S := subWith VSB20 (Lvm.X.EXM (accV VSB20)) Lvm.X.extXM)
        (by show qVlvm ≤ Lvm.X.qMax; decide)
        (by rw [subWith_acc]; exact hp))
      vk L c π hμ hacc

/-- **M′'s open obligations** from the guard's facts. -/
noncomputable def openM20 (S : SF20) : OpenSM VSB20 (Lvm.X.EXM (accV VSB20)) :=
  have H := thyp20 S
  { mid := midM reloc20 (midT₂ Ti20)
    Good := GoodTM recOf20 Ti20 H
    Lm := εS
    hmid := midSpecM_T₂ H relocLaw20
    hLm := le_rfl
    hsh := midShapeM_T₂ Ti20 reloc20
    child := childM20
    hnode := nodeM20 S H
    refines := refinesM20 S H
    ext_eq := ext_eqM20 S H }

/-- **The certificate of the M′ submission** against the declared claim. -/
theorem certificateM20 :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionB20 := by
  unfold submissionB20
  cases h : staticOkB20 with
  | false => exact Lvm.Fin.certificateR_rejectM _
  | true => rw [Lvm.Fin.subGM_true]; exact certificateR_openVM VSB20 (hq_VST20 NT20) (openM20 (sf20 h))

end Lvm.CT
