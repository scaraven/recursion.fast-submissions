/- `LvmCertF20InstOff` (GOLF2 off-path move, group 30 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmScheduleF, LvmCertF20, LvmE2VTopF, LvmE2VRefinesF, LvmCertF20X, LvmCertF20Inst,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmScheduleF
import LvmCertF20
import LvmE2VTopF
import LvmE2VRefinesF
import LvmCertF20X
import LvmCertF20Inst
import LvmE2QInstOff
import LvmE2QNodeFOff
import LvmE2VMidSpecFOff
import LvmE2VWidthsFOff
import LvmMPCertOff
import LvmXSChildOff
import LvmXSComputesOff
import LvmChainTablePad
import LvmE2QNodeF
import LvmE2QTypedPhase
import LvmJBMutual
import LvmMlListLemmas
import LvmQAsmHar47
import LvmQAsmHarP47
import LvmQShapeC
import LvmQShapeH
import LvmQTypedHarR
import LvmQTypedHarZ
import LvmSpecRulesCert
import LvmTensorSwitch
import LvmVEqTape
import LvmVerifierF
import LvmVerifierST
import LvmXSChild

-- ===== from `LvmScheduleF` =====

section
set_option autoImplicit false
namespace Lvm

/-- **The phases of S2GF** (`phases` at `p.withF accV`). -/
abbrev phasesF (p : Params) (accV : Nat) : List (Phase × List Item) := phases (p.withF accV)

end Lvm
end

section
set_option autoImplicit false
namespace Lvm

/-- The seed's length. -/
def seedLenF (accV : Nat) : Nat := 32 + headerF accV - 8

/-- The tally of the S2GF schedule. -/
abbrev tallyF (p : Params) (accV : Nat) : Tally := tally (p.withF accV)

end Lvm
end

-- ===== from `LvmCertF20` =====

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **S2GF's sizes** (`s2gf.py` amendment 1): `|π| = 306,992`, `qS = 3,959`, `T = 73,001` lanes, `4,295` sponge
blocks (V's `checks_P20F`). -/
theorem sizes_P20F : piSizeF P20F accVF = 306992 ∧ qSF P20F accVF = 3959 ∧ streamLanesF P20F accVF = 73001 ∧
    spongeBlocksF P20F accVF = 4295 :=
  ⟨checks_P20F.1.1, checks_P20F.1.2.1, checks_P20F.1.2.2.2.1, checks_P20F.1.2.2.2.2.1⟩

end Lvm.CT
end

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **S2GF's open obligations** at the typed instance `Ti` (S2GF: `TiF20`) for a verifier `VS` (S2GF: `VSFX NTF20`)
and an extractor `E`, the lead's and V's middle phases fixed: the child and its node soundness, the refinement, and
the extractor's agreement (`ext_eq`: **`ext_eqF20`'s statement**). -/
structure OpenF20 (VS : SProg) (E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit) (Ti : TInst)
    (H : THypX Ti) : Type where
  child : List UInt8 → List BF64 → Signed
  hnode : ∀ vk, NodeSoundM VS vk (GoodFM Ti H) child
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeSW fmtF20 vk (PSWithM (midP (midM reloc20 (midF₂ Ti))))).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSFW fmtF20 (midSpecPinF20 Ti H) (midShapeF₂ Ti) leadP_six
      (extJM (midShapeP_of (midShapeF₂ Ti)) (hnode vk))) L < 1 →
    ((schemeSW fmtF20 vk (PSWithM (midP (midM reloc20 (midF₂ Ti))))).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeSW fmtF20 vk (PSWithM (midP (midM reloc20 (midF₂ Ti))))).Ex
        (kcertSFW fmtF20 (midSpecPinF20 Ti H) (midShapeF₂ Ti) leadP_six
          (extJM (midShapeP_of (midShapeF₂ Ti)) (hnode vk))).ext c π L

/-- **`OpenF20` is S1's `OpenSFW` at S2GF's format.** -/
noncomputable def openF20 {VS : SProg} {E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit}
    {Ti : TInst} {H : THypX Ti} (o : OpenF20 VS E Ti H) : OpenSFW fmtF20 VS E where
  mid := midM reloc20 (midF₂ Ti)
  Good := GoodFM Ti H
  Lm := leadF20
  hmid := midSpecPinF20 Ti H
  hsh := midShapeF₂ Ti
  hL := leadP_six
  child := o.child
  hnode := o.hnode
  refines := o.refines
  ext_eq := o.ext_eq

end Lvm.CT
end

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **Statement 18 (`certificateF20`)**: the certificate of `subWith VS X.E X.ext` against the declared claim from
O1 for `VS` and S2GF's open obligations (S2GF: `VS = VSFX NTF20`). -/
theorem certificateF20 (VS : SProg) (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) {Ti : TInst}
    {H : THypX Ti} (X : ExtF20) (o : OpenF20 VS X.E Ti H) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS X.E X.ext) :=
  certificateR_openW fmtF20 VS hq X (openSFW fmtF20 (openF20 o))

end Lvm.CT
end

-- ===== from `LvmE2VTopF` =====

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

/-- `decideFFX` holds: the run's checks held and its folded claim passes `Φ_Q` (`decideFT_ok` at a stage). -/
theorem decideFFX_ok {p : Params} {N : TypedV.TNat} {vk c : RecursionFast.Digest} {sig : ByteArray}
    (h : Lvm.E2V.decideFFX p N vk c sig = true) :
    (runD (decideProgF p (fun m pub ↦ TypedV.dTypedX p N m pub) N.m3 vk c) sig
        (RS.startH (headerBytesP p))).2.ok = true ∧
      N.phi (runD (decideProgF p (fun m pub ↦ TypedV.dTypedX p N m pub) N.m3 vk c) sig
        (RS.startH (headerBytesP p))).1.pt =
      (runD (decideProgF p (fun m pub ↦ TypedV.dTypedX p N m pub) N.m3 vk c) sig
        (RS.startH (headerBytesP p))).1.y := by
  unfold Lvm.E2V.decideFFX DM.runOnH at h
  rw [decideProgFF_eq] at h
  have e : (decideProgF p (fun m pub ↦ TypedV.dTypedX p N m pub) N.m3 vk c sig).run (RS.startH (headerBytesP p)) =
      runD (decideProgF p (fun m pub ↦ TypedV.dTypedX p N m pub) N.m3 vk c) sig (RS.startH (headerBytesP p)) := rfl
  rw [e] at h
  rcases hr : runD (decideProgF p (fun m pub ↦ TypedV.dTypedX p N m pub) N.m3 vk c) sig
    (RS.startH (headerBytesP p)) with ⟨a, s⟩
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, Lvm.M3.FE_eq_of_beq h.2⟩

/-- S2GF's header terms: V_S's decision runs at `P20F`, its driver at `P20F.withF accVF`. -/
theorem headerBytesP_withF : headerBytesP P20F = headerBytesP (P20F.withF accVF) := rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile
section Main
variable (N : TypedV.TNat) (PS : List UInt8 → VerifierProgram Bool) (nR : ℕ)

/-- **V_S's S2GF decision refines the IOP verifier `PS`** with read widths `rwF20` (reads `0 … nR - 1`) on every
stream whose public values are the statement's. -/
def RefDF : Prop :=
  ∀ (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8), pubOfA accVF vk c sig = pubXF x →
    RefAtPW capS occS shpS rwF20 sig 0 (decideProgF P20F (fun m pub ↦ TypedV.dTypedX P20F N m pub) N.m3 vk c)
      (PS x) (fun _ b ↦ b = true) (fun a ↦ N.phi a.pt = a.y) nR

end Main
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile
section Main
variable (N : TypedV.TNat) (PS : List UInt8 → VerifierProgram Bool) (nR : ℕ)

/-- **V_S ⇒ S.V on a trace at S2GF** (roll 11's `refines_seqOfT` for `VSFX`, with read widths; `refines_seqOfG` at
`P20F.withF accVF`). -/
theorem refines_seqOfF (href : RefDF N PS nR)
    (hfol : ∀ x, Fol capS shpS idxS (PS x) (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) []
      fun _ _ ↦ True)
    (hst : stA (P20F.withF accVF) (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) 0 [] [] = true)
    (hw : WAt rwF20 0 (widthsA (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF)))))
    (vk c : RecursionFast.Digest) (π : ByteArray) (tr : Trace)
    (h : (Lvm.E2V.VSFX N vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeSW Lvm.CT.fmtF20 vk PS).V c π).runSeq tr = some true :=
  refines_seqOfG PS nR (P20F.withF accVF) Lvm.CT.fmtF20 (Lvm.E2V.VSFX N) (Lvm.E2V.decideFFX P20F N)
    (fun vk c ↦ decideProgF P20F (fun m pub ↦ TypedV.dTypedX P20F N m pub) N.m3 vk c) (fun a ↦ N.phi a.pt = a.y)
    (fun sig vk c x ↦ pubOfA accVF vk c sig = pubXF x) (fun _ _ _ ↦ rfl)
    (fun _ _ _ hF ↦ by have h := decideFFX_ok hF; rw [headerBytesP_withF] at h; exact h)
    (fun _ _ _ _ hp hs ↦ pubOfA_eq_pubXF hp hs) href rfl (headerF_eq P20F (by decide)) rfl
    (by rw [headerBytesP_P20F]; decide)
    (fun _ _ _ hp ↦ okS_of_parseOkH hp (hdrFix_le_P _)) hfol hst hw vk c π tr h

end Main
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

open Lvm.CT Lvm.ASM Lvm.TypedV Lvm.E2V in
/-- **`refinesF20`'s conclusion** from V_S's S2GF decision refining the pinned compiled program (`RefDF`), the
program following the S2GF schedule's atoms, the schedule's static facts and its read widths. -/
theorem refinesF20_of (N : TNat) (Q : Lvm.Loop.Program) (lay : Lvm.Typed.Lay) (nR : ℕ)
    (href : RefDF N (PSWithM (Lvm.E2F.midP (midM reloc20 (midF₂ (N.inst Q lay))))) nR)
    (hfol : ∀ x, Fol capS shpS idxS (PSWithM (Lvm.E2F.midP (midM reloc20 (midF₂ (N.inst Q lay)))) x)
      (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) [] fun _ _ ↦ True)
    (hst : stA (P20F.withF accVF) (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) 0 [] [] = true)
    (hw : WAt rwF20 0 (widthsA (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))))) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof),
      Lvm.T.isS π = true → (Lvm.E2V.VSFX N vk c π).runLog L = some true →
      ((schemeSW fmtF20 vk (PSWithM (Lvm.E2F.midP (midM reloc20 (midF₂ (N.inst Q lay)))))).V c π).runLog L =
        some true :=
  fun vk L c π _ h ↦ runLog_of_seq (fun tr ht ↦ refines_seqOfF N _ nR href hfol hst hw vk c π tr ht) L h

end Lvm.VEq
end

-- ===== from `LvmE2VRefinesF` =====

section
set_option autoImplicit false
namespace Lvm.E2V
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.VEq Lvm.TypedV LeanVM.Parameters LeanVM.Protocol.Compile

/-- **Statement 15 (`refinesF20`)**: `VSFX N` refines the compiled verifier of the pinned middle phases at S2GF. -/
theorem refinesF20 (N : TNat) (Q : Lvm.Loop.Program) (lay : Lvm.Typed.Lay) (H : TRefHypX N Q lay)
    (hσ : SigInS N) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSFX N vk c π).runLog L = some true →
      ((schemeSW fmtF20 vk (PSWithM (Lvm.E2F.midP (midM reloc20 (midF₂ (N.inst Q lay)))))).V c π).runLog L =
        some true := by
  obtain ⟨hl, hr, he, -, -⟩ := H.toT.fits
  have hw : WAt rwF20 0 (wDecF (atomsOf (P20F.withF accVF) (typedIX (P20F.withF accVF)))
      (atomsOf P20 (openMainI P20))) := by
    have h := wAt_rwF20
    rw [widthsA_scheduleF] at h
    exact h
  have h24O : ∀ w ∈ widthsA (atomsOf P20 (openMainI P20)), w = 24 := fun w hw' ↦
    mem_widthsA_openF w (by rw [openMainI_F, atomsOf_F]; exact hw')
  exact refinesF20_of N Q lay _
    (fun sig vk c x hpub ↦ ref_decideFX N Q lay H hσ vk c x hpub _ _ (fun _ ↦ True)
      (folP_typedProgX (P20F.withF accVF) (N.inst Q lay) (pubXF x) rfl hl busDepth_P20 hr he)
      (fun cl pp ↦ fol_openMain cl pp) mem_widthsA_typedF h24O hw)
    (fol_PSOfF reloc20 (N.inst Q lay) hl busDepth_P20 hr he) stA_P20F wAt_rwF20

end Lvm.E2V
end

-- ===== from `LvmCertF20X` =====

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

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

end Lvm.CT
end

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

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
end

-- ===== from `LvmCertF20Inst` =====

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

end Lvm.CT
end

section
set_option autoImplicit false
namespace Lvm.CT
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **S2GF's static guard**: E2F-C's `staticOkBF20` (the typed guard, the node checks, `σ′` in `S`, the HAR's
checks, the layout's word `1` in a `1` region). -/
def staticOkF20 : Bool := staticOkBF20

/-- **The S2GF submission**: `V_S` at S2GF behind the static guard, S2GF's extractor. -/
def submissionF20 : Submission := subGF staticOkF20 (VSFX NTF20)

/-- **Statement 18: the certificate of the S2GF submission** against the declared claim. -/
theorem certificateF20S :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionF20 :=
  certificateR_guardF fun h ↦
    have S := sfF20 h
    have H := thypF20 S
    certificateSF20 NTF20 QF20 layF20 H (trefF20 S H) S.1.sig (Lvm.NS.childSP P20F)
      (fun x q ↦ childF20_win x q) (nodeF20 S H)

end Lvm.CT
end
