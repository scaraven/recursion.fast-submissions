-- New for lvm2 MB-LIN (MBL-V2, MBL-STMT 6b): V_S's S2GL decision (`decideProgLG P20L P20 3843`) refines the pinned S2GL
-- middle phases (`midMk 4 relocU20 (midGL _)`) on the stream with S2GL's read widths, at S2GU's occupied words `occOfU`
-- (`LvmE2URef`'s chain without the table phase, the three linear claims in the opening, the wire at `b = 3,842`).
import LvmE2URef
import LvmE2LDec
import LvmS2GLMid
import LvmE2VMidSpecFOff

/-!
# V_S's S2GL decision refines the pinned middle phases

* S2GL's schedule items and their `FolP` (`typedIL`, `midItemsL`, `folP_midPL`, ...; written by MBL-LA).
* **The three claims** from the bus phase's relation (`MbRel`, `mbClaims_relB`): V_S's `sumClaim`s are `mbClaimsL`'s.
* **The typed phases at S2GL** (`ref_dTypedLO`): `dTypedLG` refines `typedProgL` (`dMiniL` is `dBus`).
* The tape at the sponge intervals `contIvB b` (`wireUDb`, `tapeUDb`, `refW_tapeUDb`), the opening with the three
  claims (`dOpenFFL_eq`), the claims (`claimsL_rel`), the schedule's facts at `P20L` and **`refinesL20_of`**.
-/

set_option autoImplicit false

/-! ## S2GL's middle phases follow the schedule (proof help for MBL-STMT 8e) -/

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.E2V

section Items

variable (p : Params)

/-- **The typed phases' items at S2GL**: S2GT's without the mini-bus's table phase (`miniTabI`). -/
def typedIL : List Item := zeroIT ++ (wiringIT ++ (relayIT ++ (accIT p ++ miniBusI p)))

/-- **The pinned middle phases' items at S2GL**: the pin, the typed phases, the merged tape, the wire. -/
def midItemsL : List Item := pinI p ++ (typedIL p ++ (tapeU p ++ wireU p))

set_option maxRecDepth 10000 in
/-- **S2GL's schedule by phase** (`phasesU_eq` without the phase `tables`). -/
theorem phasesL_eq (h : p.stage = 3) (hl : p.mbLin = true) : phases p = [(.commit, commitI p ++ pinI p),
    (.bus, typedIL p), (.tape, tapeU p), (.wire, wireU p), (.openMain, openMainI p)] := by
  rw [phases, if_neg (by omega), if_neg (by omega), if_pos h, hl, if_pos rfl, phasesS2GL, phasesS2GT]
  rfl

/-- S2GL's schedule: the root, the pinned middle phases, `C_main`'s opening. -/
theorem scheduleL_eq (h : p.stage = 3) (hl : p.mbLin = true) :
    schedule p = commitI p ++ (midItemsL p ++ (openMainI p ++ [])) := by
  rw [schedule, phasesL_eq p h hl]
  simp only [midItemsL, typedIL, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil]

end Items

section Front

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- **The wire at any `b`** against `wireU` at a record with `logN = 20` (`folP_wireProgU`'s proof). -/
theorem folP_wireProgB (b : ℕ) (hN : p.logN = 20) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) :
    FolP cap shp idx (Lvm.E2U.wireProgB b s n claim) (atomsOf p (wireU p)) fun _ ↦ True := by
  have e : atomsOf p (wireU p) = atomsOf p (sumcheckE2I 20 2) ++ (List.replicate 3 (.rdw e2Bytes) ++
      (atomsOf p (slotRedI 2) ++ (atomsOf p (slotRedI laneBits) ++ atomsOf p (slotRedI laneBits)))) := by
    simp only [wireU, hN, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2]
  rw [e]
  unfold Lvm.E2U.wireProgB
  exact (folP_sumcheckE2 p _ rfl (by norm_num) _ 20 _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_e2Reads 3).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_slotRedU p 2 _ _ _ _ _).bind fun _ _ ↦ (folP_slotRedU p 5 _ _ _ _ _).bind fun _ _ ↦
    (folP_slotRedU p 5 _ _ _ _ _).bind_ret fun _ _ ↦ trivial

/-- **The merged tape at any `b`** against `tapeU ++ wireU` at a record with `logN = 20` (`folP_tapeProgU`'s
proof). -/
theorem folP_tapeProgB (b : ℕ) (hN : p.logN = 20) (s : RecursionFast.Digest) (n : ℕ) :
    FolP cap shp idx (Lvm.E2U.tapeProgB b s n) (atomsOf p (tapeU p) ++ atomsOf p (wireU p)) fun _ ↦ True := by
  have e : atomsOf p (tapeU p) ++ atomsOf p (wireU p) =
      [.sm] ++ ((List.replicate 20 [Atom.rdw nonceBytes, .sm]).flatten ++ (List.replicate 50 (.rdw e2Bytes) ++
        ((List.replicate 1 [Atom.rdw nonceBytes, .sm]).flatten ++
          (atomsOf p (tapeLayersE2I 21) ++ atomsOf p (wireU p))))) := by
    simp only [tapeU, hN, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2,
      atomsOf_sepI, atomsOf_gsmpN, atomsOf_gsmp, List.append_assoc]
    rfl
  rw [e]
  unfold Lvm.E2U.tapeProgB
  exact folP_e2Sep.bind fun _ _ ↦ (folP_e2Samples _ 20).bind fun r hr ↦ (folP_e2Reads 50).bind fun _ _ ↦
    (folP_e2Samples _ 1).bind fun r1 hr1 ↦
    (folP_tapeGkrE2 p 21 (r ++ r1) _ (by rw [List.length_append, hr, hr1])).bind fun _ _ ↦
    (folP_require _).bind fun _ _ ↦ (folP_wireProgB p b hN _ _ _).bind_ret fun _ _ ↦ trivial

/-- **The mini-bus at S2GL** (the bus phase, then the three claims) against `miniBusI`. -/
theorem folP_miniBusLProg (tabs : List Lvm.M3.Tab) (hl : p.leafdecReads = 1) (hd : p.busDepth = Typed.miniDepth) :
    FolP cap shp idx (Lvm.E2L.miniBusLProg tabs Typed.miniDepth) (atomsOf p (miniBusI p)) fun _ ↦ True := by
  have hb := folP_lvmBusProg (cap := cap) (shp := shp) (idx := idx) p hl
  rw [hd] at hb
  unfold Lvm.E2L.miniBusLProg
  exact hb.bind_ret fun _ _ ↦ trivial

/-- **The typed phases at S2GL** against `typedIL` (`folP_typedProgT`'s without the table phase). -/
theorem folP_typedProgL (Ti : Typed.TInst) (pub : Pub) (hacc : p.accV = Typed.phiVarsT)
    (hl : p.leafdecReads = 1) (hd : p.busDepth = Typed.miniDepth) :
    FolP cap shp idx (Lvm.E2L.typedProgL Ti pub) (atomsOf p (typedIL p)) fun _ ↦ True := by
  simp only [typedIL, atomsOf_append]
  unfold Lvm.E2L.typedProgL
  exact (folP_zeroProgT p).bind fun _ _ ↦ (folP_wireProgT p Ti pub _).bind fun _ _ ↦
    (folP_relayProgT p Ti _ _).bind fun _ _ ↦ (folP_accProgT p hacc _ _ _ _ _ _ _).bind fun _ _ ↦
    (folP_miniBusLProg p Ti.mbT hl hd).bind_ret fun _ _ ↦ trivial

end Front

section Mid

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **S2GL's middle phases** (`midGL Ti`) against the typed and the front items at `P20L`. -/
theorem folP_midGL (Ti : Typed.TInst) (hl : P20L.leafdecReads = 1) (hd : P20L.busDepth = Typed.miniDepth)
    (x : List UInt8) :
    FolP cap shp idx (Lvm.E2L.midGL Ti x) (atomsOf P20L (typedIL P20L ++ (tapeU P20L ++ wireU P20L)))
      fun _ ↦ True := by
  rw [atomsOf_append, atomsOf_append]
  unfold Lvm.E2L.midGL
  exact (folP_typedProgL _ Ti _ rfl hl hd).bind fun _ _ ↦
    (folP_tapeProgB _ _ rfl _ _).bind_ret fun _ _ ↦ trivial

theorem atomsOf_pinIL : atomsOf P20L (pinI P20L) = List.replicate CMain.nu20 .sm ++ [.rd] := by
  rw [pinI, atomsOf_append, atomsOf_smp, atomsOf_rd]
  rfl

/-- **S2GL's pinned middle phases follow `midItemsL`** at `P20L`, for every relocation. -/
theorem folP_midPL (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : P20L.leafdecReads = 1) (hd : P20L.busDepth = Typed.miniDepth) (x : List UInt8) :
    FolP cap shp idx (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2L.midGL Ti)) x) (atomsOf P20L (midItemsL P20L))
      fun _ ↦ True := by
  rw [midItemsL, atomsOf_append, atomsOf_pinIL]
  exact folP_midP _ x _ (folP_midMk 4 reloc _ x _ (folP_midGL Ti hl hd x))

end Mid

end Lvm.VEq


/-! ## The three claims from the bus phase -/

namespace Lvm.E2L

open RecursionFast Lvm Lvm.E2V Lvm.E2T Lvm.E2U

namespace MbRel

open Lvm.M3 (Tab formE formN formL coefN coefL constN constL mbPartsN mbPartsL mbValueN mbValueL busFinalR busFinalV
  tE_add tE_mul tE_zero tE_sumE)

theorem formE_default : formE default = default := rfl

theorem getD_map_formE (l : List Lvm.Form) (s : ℕ) : (l.map formE).getD s default = formE (l.getD s default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[s]? <;> rfl

/-- The language form of table `j` on side `s` is the native one's image. -/
theorem formL_eq (tabs : List Tab) (i : Lvm.BusIn) (j s : ℕ) :
    formL (busFinalV tabs (i.alphas.map FE.toExt3) (FE.toExt3 i.beta) (i.point.map FE.toExt3)
      (i.values.map FE.toExt3)) j s = formE (formN (busFinalR tabs i) j s) := by
  unfold formL formN
  rw [← Lvm.M3.busFinalR_forms, Lvm.M3.getD_map_nil, getD_map_formE]

theorem coefL_formE (f : Lvm.Form) (c : ℕ) : coefL (formE f) c = FE.toExt3 (coefN f c) := by
  unfold coefL coefN formE
  rw [tE_sumE, List.filter_map, List.map_map, List.map_map]
  rfl

theorem constL_formE (t : Tab) (f : Lvm.Form) (pt : List FE) :
    constL t (formE f) (pt.map FE.toExt3) = FE.toExt3 (constN t f pt) := by
  unfold constL constN formE
  rw [tE_sumE]
  simp only [List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  obtain ⟨mo, c⟩ := m
  simp only [Function.comp_apply]
  rcases mo with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rfl
  · have hid : List.map (FE.ofExt3 ∘ FE.toExt3) pt = pt := by
      simp only [Function.comp_def, FE.ofExt3_toExt3, List.map_id']
    simp only [hid]
    cases h : t.cols[a]? with
    | none => exact tE_zero.symm
    | some cs =>
      cases cs with
      | com _ _ => exact tE_zero.symm
      | fix _ _ => simp
  · exact tE_zero.symm

theorem parts_rel (tabs : List Tab) (i : Lvm.BusIn) (s : ℕ) :
    mbPartsL tabs (busFinalV tabs (i.alphas.map FE.toExt3) (FE.toExt3 i.beta) (i.point.map FE.toExt3)
      (i.values.map FE.toExt3)) s = (mbPartsN tabs (busFinalR tabs i) i.point s).map Lvm.VEq.Lk.partE := by
  unfold mbPartsL mbPartsN
  rw [List.map_flatMap]
  refine List.flatMap_congr fun tj _ => ?_
  rw [List.map_filterMap]
  refine List.filterMap_congr fun c _ => ?_
  rcases tj.1.cols[c]? with _ | (_ | _)
  · rfl
  · simp only [Option.map_some, Lvm.VEq.Lk.partE, formL_eq, coefL_formE, List.map_take]
    rfl
  · rfl

theorem value_rel (tabs : List Tab) (i : Lvm.BusIn) (s : ℕ) :
    mbValueL tabs (busFinalV tabs (i.alphas.map FE.toExt3) (FE.toExt3 i.beta) (i.point.map FE.toExt3)
      (i.values.map FE.toExt3)) s = FE.toExt3 (mbValueN tabs (busFinalR tabs i) i.point s) := by
  unfold mbValueL mbValueN
  rw [tE_add, tE_sumE, List.map_map, ← Lvm.M3.busFinalR_totals, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  congr 1
  · cases (busFinalR tabs i).totals[s]? <;> simp
  · congr 1
    refine List.map_congr_left fun tj _ => ?_
    obtain ⟨t, j⟩ := tj
    simp only [Function.comp_apply, formL_eq]
    show constL t _ ((i.point.map FE.toExt3).take t.τ) = _
    rw [← List.map_take, constL_formE]

end MbRel

namespace MbRel

open Lvm.M3 (Tab formE formN formL coefN coefL constN constL mbPartsN mbPartsL mbValueN mbValueL tE_add tE_sumE)

/-- A bus result whose forms are a native output's images has its forms. -/
theorem formL_eqB {r : LeanVM.Protocol.Verifier.BusResult} {o : Lvm.BusOut}
    (hf : r.forms = o.forms.map (·.map formE)) (j s : ℕ) : formL r j s = formE (formN o j s) := by
  unfold formL formN
  rw [hf, Lvm.M3.getD_map_nil, getD_map_formE]

theorem parts_relB (tabs : List Tab) {r : LeanVM.Protocol.Verifier.BusResult} {o : Lvm.BusOut} {pt : List FE}
    (hf : r.forms = o.forms.map (·.map formE)) (hp : r.point = pt.map FE.toExt3) (s : ℕ) :
    mbPartsL tabs r s = (mbPartsN tabs o pt s).map Lvm.VEq.Lk.partE := by
  unfold mbPartsL mbPartsN
  rw [List.map_flatMap, hp]
  refine List.flatMap_congr fun tj _ => ?_
  rw [List.map_filterMap]
  refine List.filterMap_congr fun c _ => ?_
  rcases tj.1.cols[c]? with _ | (_ | _)
  · rfl
  · simp only [Option.map_some, Lvm.VEq.Lk.partE, formL_eqB hf, coefL_formE, List.map_take]
    rfl
  · rfl

theorem value_relB (tabs : List Tab) {r : LeanVM.Protocol.Verifier.BusResult} {o : Lvm.BusOut} {pt : List FE}
    (hf : r.forms = o.forms.map (·.map formE)) (ht : r.totals = o.totals.map FE.toExt3)
    (hp : r.point = pt.map FE.toExt3) (s : ℕ) :
    mbValueL tabs r s = FE.toExt3 (mbValueN tabs o pt s) := by
  unfold mbValueL mbValueN
  rw [tE_add, tE_sumE, List.map_map, ht, hp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  congr 1
  · cases o.totals[s]? <;> simp
  · congr 1
    refine List.map_congr_left fun tj _ => ?_
    obtain ⟨t, j⟩ := tj
    simp only [Function.comp_apply, formL_eqB hf]
    show constL t _ ((pt.map FE.toExt3).take t.τ) = _
    rw [← List.map_take, constL_formE]

end MbRel

/-- **V_S's three claims** (the parts and values of the bus phase's native output at `ζ`). -/
def mbSumsN (tabs : List Lvm.M3.Tab) (pb : List FE × Lvm.BusOut) : List Lvm.BlockClaim :=
  (List.range 3).map fun s ↦ sumClaim CMain.nu20 (Lvm.M3.mbPartsN tabs pb.2 pb.1 s) (Lvm.M3.mbValueN tabs pb.2 pb.1 s)

/-- **The three claims of related bus phases are related** (`BusRel`: V_S's against `mbClaimsL`'s, claim for claim). -/
theorem mbClaims_relB (tabs : List Lvm.M3.Tab) (pb : List FE × Lvm.BusOut) (b : Lvm.M3.LBus)
    (h : Lvm.VEq.BusRel tabs pb b) :
    List.Forall₂ Lvm.VEq.BCRel (mbSumsN tabs pb) (Lvm.M3.mbClaimsL CMain.nu20 tabs b) := by
  obtain ⟨-, hp, hf, ht⟩ := h
  unfold mbSumsN Lvm.M3.mbClaimsL Lvm.M3.mbClaimL
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun s _ => ?_
  exact Lvm.VEq.Lk.sumClaim_rel _ _ _ (MbRel.parts_relB tabs hf hp s) (MbRel.value_relB tabs hf ht hp s)

/-- V_S's claims (`linClaims` of the sides' columns and values) are the three `sumClaim`s. -/
theorem linClaims_mb (tabs : List Lvm.M3.Tab) (pb : List FE × Lvm.BusOut) :
    linClaims CMain.nu20 pb.1 ((List.range 3).map (Lvm.M3.mbColsN tabs pb.2))
      ((List.range 3).map (Lvm.M3.mbValueN tabs pb.2 pb.1)) = (mbSumsN tabs pb).map fun c ↦ (Com.main, c, (0 : FE)) := by
  unfold linClaims mbSumsN
  rw [List.map_map]
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, Function.comp_apply, partsOf,
    Lvm.M3.mbPartsN_cols, List.getD_eq_getElem?_getD]
  simp at h1
  simp [h1]

end Lvm.E2L

/-! ## The typed phases at S2GL -/

namespace Lvm.E2T

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.VEq
open Lvm.TypedV (TNat fitsMiniB)
open Lvm.Typed (xVars yVars selBitsT phiVarsT relayRounds Lay)
open Lvm.M3 (Tab sumcheckTabs)
open Lvm.FE2 (toE2)
open Lvm.E2L (dMiniL dTypedLG typedProgL typedClaimsL miniBusLProg)

/-- The mini-bus's reads at S2GL (24 B each): its bus phase's (`miniBusI`). -/
def nMiniRdL : ℕ := atomReads (atomsOf P20 (miniBusI P20))

/-- **The typed phase's widths at S2GL** (`wTypedT` without the table phase's reads). -/
def wTypedL : List ℕ := wZeroT ++ (wWireT ++ (wRelayT ++ (wAccT ++ List.replicate nMiniRdL 24)))

theorem monoD_dMiniL (p : Params) (m : M3) (pub : Pub) : MonoD (dMiniL p m pub) := monoD_dBus p m pub

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **The mini-bus at S2GL** refines `miniBusLProg`: the bus phase's relation, and the spec's claims those of what it
read. -/
theorem ref_dMiniL (p : Params) (m : M3) (tabs : List Tab) (pub : Pub)
    (hm : m.busFinal = (M3.real p fun _ ↦ tabs).busFinal) (hsc : sumcheckTabs tabs = tabs)
    (hl : p.leafdecReads = 1) (hd : p.busDepth = Typed.miniDepth) :
    RefAt cap occ shp sig (dMiniL p m pub) (miniBusLProg tabs Typed.miniDepth)
      fun pb cl ↦ ∃ b, BusRel tabs pb b ∧ cl = Lvm.M3.mbClaimsL CMain.nu20 tabs b := by
  have e : dMiniL p m pub = dBus p (M3.real p fun _ ↦ tabs) pub >>= fun r ↦ Pure.pure r := by
    rw [bind_pure]
    unfold dMiniL dBus
    simp only [hm]
  have h := ref_dBus (cap := cap) (occ := occ) (shp := shp) (sig := sig) p (fun _ ↦ tabs) pub hl
  rw [hsc, hd] at h
  rw [e]
  unfold miniBusLProg
  exact RefAt.bind (fun _ ↦ MonoD.pure _) h fun pb b hb ↦ RefAt.pure ⟨b, hb, rfl⟩

/-- **The typed phases' native results at S2GL against the specification's claims** on the layout of `p`: the typed
claims as `TRelTTO`'s, the bus phase related to what the spec's read, the spec's mini-bus claims its three claims. -/
def TRelTL (p : Params) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)
    (r : Acc × List (Com × BlockClaim × FE) × List FE × BusOut) (a : Lvm.ASM.OpenClaims) : Prop :=
  ∃ ry rv rr : List FE2, ∃ vR : FE2, ∃ b : Lvm.M3.LBus, r.2.1 = typedClaimsND N p ry rv rr vR ∧
    ry.length = yVars ∧ rv.length = 4 ∧ rr.length = relayRounds ∧ BusRel N.mbT (r.2.2.1, r.2.2.2) b ∧
    a = typedClaimsL (N.inst Q lay) (ry.map toE2) (rv.map toE2) (rr.map toE2) (toE2 vR)
      (Lvm.M3.mbClaimsL CMain.nu20 N.mbT b)

/-- **The typed phases at S2GL refine `typedProgL`** on the width-aware stream, under the promise that the folded
claim holds natively, their claims formed on the layout of `p` (`ref_dTypedTO` with `dMiniL`). -/
theorem ref_dTypedLO (p : Params) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypT N Q lay) (m : M3)
    (hm : m.busFinal = (M3.real P20 fun _ ↦ N.mbT).busFinal) (pub : Pub)
    (hacc : pub.accIn.pt.length = phiVarsT) {i : ℕ} (hw : WAt rw i wTypedL) :
    RefAtWP cap occ shp rw sig i (dTypedLG P20 N m pub (typedClaimsND N p))
      (typedProgL (N.inst Q lay) pub) (TRelTL p N Q lay) (fun r ↦ N.phiT (r.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE r.1.y)
      (i + wTypedL.length) := by
  obtain ⟨hl, -, -, -, -⟩ := H.toT.fits
  simp only [wTypedL, WAt.append] at hw
  obtain ⟨hwz, hww, hwr, hwa, hwm⟩ := hw
  unfold dTypedLG typedProgL
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (E2T.monoD_dWiringT _ _ _).bind fun _ ↦
    (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦ (E2T.monoD_dAccT _ _ _).bind fun _ ↦
      (monoD_dMiniL _ _ _).bind fun _ ↦ MonoD.pure _) (RefAtW.toP (refW_dZeroT hwz) _)
    (fun _ _ _ ↦ trivial) ?_
  rintro z _ ⟨rfl, hz, -⟩ -
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦
    (E2T.monoD_dAccT _ _ _).bind fun _ ↦ (monoD_dMiniL _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.toP (refW_dWiringT N Q lay H.ok H.hlay pub z.2 hww) _) (fun _ _ _ ↦ trivial) ?_
  rintro w _ ⟨rfl, hry, -, hrv⟩ -
  have hR := refW_dRelayT2 (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) N Q lay H.ok H.hlay w.1
    hry (w.2.2.getD 1 0) hwr
  rw [kv_toE2_getD] at hR
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (E2T.monoD_dAccT _ _ _).bind fun _ ↦
    (monoD_dMiniL _ _ _).bind fun _ ↦ MonoD.pure _) (RefAtW.toP hR _) (fun _ _ _ ↦ trivial) ?_
  rintro r _ ⟨rfl, hrr⟩ -
  have hA := refW_dAccT (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) N Q lay H.phiT pub hacc
    (z.1 ++ w.1) w.2.1 (by rw [List.length_append, hz, hry]) hwa
  rw [List.map_append] at hA
  dsimp only
  refine RefAtWP.bind (Q := fun (a : Acc) ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y)
    (fun _ ↦ (monoD_dMiniL _ _ _).bind fun _ ↦ MonoD.pure _) hA
    (fun _ _ h ↦ by rw [runD_bind_pure_fst] at h; exact h) ?_
  intro acc _ _ _
  have hM := ref_dMiniL (cap := cap) (occ := occ) (shp := shp) (sig := sig) P20 m N.mbT pub hm H.toT.sc_eq hl
    busDepth_P20
  have hF := folP_miniBusLProg (cap := cap) (shp := shp) (idx := fun _ ↦ 0) P20 N.mbT hl busDepth_P20
  have hW := RefAt.toW (rw := rw) hM hF hwm
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) (RefAtW.toP hW _) (fun _ _ _ ↦ trivial) ?_
  rintro pb cl ⟨b, hb, rfl⟩ -
  refine RefAtWP.idx (RefAtW.toP (RefAtW.pure ⟨w.1, w.2.2, r.1, r.2, b, rfl, hry, hrv, hrr, hb, rfl⟩) _) ?_
  simp only [wTypedL, List.length_append, List.length_replicate, nMiniRdL]
  (clear * - i N Q lay pub z w r; omega)

end Ref

/-- The typed phases' claims at S2GL are their items' flattening. -/
theorem dTypedLG_items (pT p : Params) (N : TNatT) (m : M3) (pub : Pub) :
    dTypedLG pT N m pub (typedClaimsND N p) =
      (fun r ↦ (r.1, r.2.1.flatMap FItem.flat, r.2.2)) <$> dTypedLG pT N m pub (typedItemsND N p) := by
  unfold dTypedLG
  simp only [map_bind, map_pure, typedItemsND_flat]

theorem monoD_dTypedLG {α : Type} (p : Params) (N : TNatT) (m : M3) (pub : Pub)
    (mk : List FE2 → List FE2 → List FE2 → FE2 → α) : MonoD (dTypedLG p N m pub mk) :=
  E2T.monoD_dZeroT.bind fun _ ↦ (E2T.monoD_dWiringT _ _ _).bind fun _ ↦ (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦
    (E2T.monoD_dAccT _ _ _).bind fun _ ↦ (monoD_dMiniL _ _ _).bind fun _ ↦ MonoD.pure _

end Lvm.E2T

/-! ## The tape at the sponge intervals `contIvB b` (`LvmE2UEq`'s twins generic in `b`) -/

namespace Lvm

open DM Lvm.E2V Lvm.E2U

/-- **`wireProgB b` on `DM` at `FE2`** (`wireUD` with the sponge intervals `contIvB b`). -/
def wireUDb (b : Nat) (s : List FK) (n : Nat) (claim : E2V.KClaim FE2) :
    DM ((List FE2 × FE2) × List FE2 × SlotU ((FE × (List FE → FE)) × List FE) ×
      SlotU ((FE × (List FE → FE)) × List FE) × SlotU ((FE × (List FE → FE)) × List FE)) := do
  let sc ← sumcheckD gC2 (wireTargetD (sBitsD s) n claim) 3 (List.replicate 20 none)
  let g ← readE2s 3
  require (sc.2 == E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0 +
    eTailF 13 20 sc.1 * (kksF (contIvB b) claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 1 0 +
      E2V.ikEvalP claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 2 0))
  let d ← slotD 2 1 0 (E2V.dWF claim.weights) sc.1 (g.getD 0 0)
  let y ← slotD 5 5 22 (E2V.yWG claim.weights) (sc.1.take 13) (g.getD 1 0)
  let m ← slotD 5 4 10 (E2V.mWG claim.weights) (sc.1.take 13 ++ [0]) (g.getD 2 0)
  pure (sc, g, d, y, m)

/-- **`tapeProgB b` on `DM` at `FE2`** (`tapeUD` with the wire `wireUDb b`). -/
def tapeUDb (b : Nat) (s : List FK) (n : Nat) :
    DM (List FE2 × List FE2 × List FE2 × E2V.KClaim FE2 × ((List FE2 × FE2) × List FE2 ×
      SlotU ((FE × (List FE → FE)) × List FE) × SlotU ((FE × (List FE → FE)) × List FE) ×
      SlotU ((FE × (List FE → FE)) × List FE))) := do
  sepE2
  let r ← samplesG gC1 20
  let ab ← readE2s 50
  let r20 ← samplesG gC1 1
  let claim ← tapeGkrD 21 (r ++ r20) (t1ValsF 20 13 (r ++ r20) ab)
  require (decide (1 ≤ n ∧ n ≤ 2 ^ 20))
  let wo ← wireUDb b s n claim
  pure (r, r20, ab, claim, wo)

end Lvm

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U

theorem monoD_wireUDb (b : ℕ) (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) : MonoD (wireUDb b s n claim) :=
  (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
      (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _

theorem monoD_tapeUDb (b : ℕ) (s : List FK) (n : ℕ) : MonoD (tapeUDb b s n) :=
  monoD_sepE2.bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_wireUDb _ _ _ _).bind fun _ ↦ MonoD.pure _

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **The wire at `b`** (`refW_wireUD`'s proof with `contIvB b`). -/
theorem refW_wireUDb (b : ℕ) (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ)
    (claim : E2V.KClaim FE2) (hρ : 9 ≤ claim.point.length) {i : ℕ} (hw : WAt rw i wWireU) :
    RefAtW cap occ shp rw sig i (wireUDb b s n claim) (wireProgB b d n (cE2 claim)) WireURelW
      (i + wWireU.length) := by
  rw [wWireU, WAt.append, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩, hw5⟩ := hw
  unfold wireUDb wireProgB
  rw [hs]
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
      (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((refW_sumcheckD E2V.gC2 3 (by norm_num) (List.replicate 20 none)
      (wireTargetD (Lvm.KG.digestBits d) n claim) ?_).congr_prog ?_) ?_
  · simpa using hw1
  · rw [map_replicate_noneE2, E2V.toE2_wireTargetD]
  rintro sc sc' ⟨h1, h2, hl⟩
  have hl' : sc.1.length = 20 := by simpa using hl
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2s 3 (WAt.idx_eq hw2 (by simp))) ?_
  intro g g' hg
  subst hg
  refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _) (RefAtW.require fun h ↦ ?_) fun _ _ _ ↦ ?_
  · have h' := congrArg toE2 (beq_iff_eq.1 h)
    have h13 : 4 ≤ (sc.1.take 13).length := by simp [hl']
    rw [h2, h', Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq, Lvm.FE2.fe2_mul_eq, Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq,
      Lvm.FE2.fe2_mul_eq, E2V.toE2_msEvalF, toE2_getD, toE2_getD, toE2_getD, toE2_eTailF, toE2_kksF, toE2_ikEvalP,
      ikEvalP_eq _ _ _ _ (by simpa using h13) (by simp [hl']; omega), List.map_take, ← h1]
    rfl
  · have hD : (fun o z ↦ toE2 (E2V.dWF claim.weights o z)) = E2V.dWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ E2V.toE2_dWF _ _ _
    have hY : (fun o z ↦ toE2 (E2V.yWG claim.weights o z)) = yWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ (map_yWG E2V.toE2Hom _ _ _).trans rfl
    have hM : (fun o z ↦ toE2 (E2V.mWG claim.weights o z)) = mWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ (map_mWG E2V.toE2Hom _ _ _).trans rfl
    refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
      MonoD.pure _)
      ((refW_slotD 2 1 0 (E2V.dWF claim.weights) sc.1 (g.getD 0 0)
        (WAt.idx_eq hw3 (by simp [length_wReads]; omega))).congr_prog ?_) fun dd dd' hd ↦ ?_
    · rw [hD, toE2_getD, ← h1]
      rfl
    refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
      ((refW_slotD 5 5 22 (E2V.yWG claim.weights) (sc.1.take 13) (g.getD 1 0)
        (WAt.idx_eq hw4 (by simp [wSlot, length_wReads]; omega))).congr_prog ?_) fun yy yy' hy ↦ ?_
    · rw [hY, toE2_getD, List.map_take, ← h1]
      rfl
    refine RefAtW.bind (fun _ ↦ MonoD.pure _)
      ((refW_slotD 5 4 10 (E2V.mWG claim.weights) (sc.1.take 13 ++ [0]) (g.getD 2 0)
        (WAt.idx_eq hw5 (by simp [wSlot, length_wReads]; omega))).congr_prog ?_) fun mm mm' hm ↦ ?_
    · rw [hM, toE2_getD, List.map_append, List.map_take, ← h1, List.map_singleton, Lvm.FE2.toE2_zero]
      rfl
    exact (RefAtW.pure ⟨h1, h2, rfl, hd, hy, hm⟩).idx (by simp [wSlot, wWireU, length_wReads]; omega)

/-- **The tape at `b`** (`refW_tapeUD`'s proof with `wireUDb b`). -/
theorem refW_tapeUDb (b : ℕ) (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d)
    (n : ℕ) {i : ℕ} (hw : WAt rw i wTapeU) :
    RefAtW cap occ shp rw sig i (tapeUDb b s n) (tapeProgB b d n) TapeURelW (i + wTapeU.length) := by
  rw [wTapeU, WAt.append, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩, hw5⟩ := hw
  unfold tapeUDb tapeProgB
  refine RefAtW.bind (fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_wireUDb _ _ _ _).bind fun _ ↦ MonoD.pure _) refW_sepE2 fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦
    (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_wireUDb _ _ _ _).bind
      fun _ ↦ MonoD.pure _) (refW_samplesGL E2V.gC1 20 hw1) ?_
  rintro r r' ⟨hr, hrl⟩
  subst hr
  refine RefAtW.bind (fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ (monoD_wireUDb _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2s 50 (WAt.idx_eq hw2 (by simp only [List.length_replicate]))) ?_
  intro ab ab' hab
  subst hab
  refine RefAtW.bind (fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_wireUDb _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_samplesGL E2V.gC1 1
      (WAt.idx_eq hw3 (by simp only [List.length_append, List.length_replicate, length_wReads]))) ?_
  rintro r20 r20' ⟨h20, h20l⟩
  subst h20
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_wireUDb _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((refW_tapeGkrD 21 (r ++ r20) (t1ValsF 20 13 (r ++ r20) ab) (by simp [hrl, h20l])
      (WAt.idx_eq hw4 (by simp only [List.length_append, List.length_replicate, length_wReads]))).congr_prog ?_) ?_
  · rw [List.map_append, map_toE2_t1ValsF, List.map_append]
  rintro c c' ⟨hc, hcl⟩
  subst hc
  refine RefAtW.bind (fun _ ↦ (monoD_wireUDb _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.require fun h ↦ of_decide_eq_true h) fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ MonoD.pure _)
    (refW_wireUDb b s d hs n c (by omega)
      (WAt.idx_eq hw5 (by simp only [List.length_append, List.length_replicate, length_wReads]; omega))) ?_
  intro wo wo' hwo
  exact (RefAtW.pure ⟨by rw [List.map_append], hrl, h20l, rfl, rfl, hwo⟩).idx
    (by simp only [wTapeU, List.length_append, List.length_replicate, length_wReads]; omega)

end Ref

theorem retD_wireUDb (b : ℕ) (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) :
    RetD (fun wo : (List FE2 × FE2) × List FE2 × SlotC × SlotC × SlotC ↦
      wo.1.1.length = 20 ∧ wo.2.2.1.1.1.length = 2 ∧
        wo.2.2.1.2.2.1.2 = rowWD (wo.1.1 ++ wo.2.2.1.1.1 ++ E2V.selPtF 0 1) wo.2.2.1.2.2.2 ∧
        wo.2.2.2.1.1.1.length = 5 ∧
        wo.2.2.2.1.2.2.1.2 = rowWD (wo.1.1.take 13 ++ wo.2.2.2.1.1.1 ++ E2V.selPtF 22 5) wo.2.2.2.1.2.2.2 ∧
        wo.2.2.2.2.1.1.length = 5 ∧
        wo.2.2.2.2.2.2.1.2 = rowWD (wo.1.1.take 13 ++ [0] ++ wo.2.2.2.2.1.1 ++ E2V.selPtF 10 4) wo.2.2.2.2.2.2.2)
      (wireUDb b s n claim) :=
  (retD_sumcheckD _ _ _ _).bind fun _ hsc ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_slotD _ _ _ _ _ _).bind fun _ hd ↦ (retD_slotD _ _ _ _ _ _).bind fun _ hy ↦
      (retD_slotD _ _ _ _ _ _).bind fun _ hm ↦
        RetD.pure ⟨by simpa using hsc, hd.1, hd.2, hy.1, hy.2, hm.1, hm.2⟩

theorem retD_tapeUDb (b : ℕ) (s : List FK) (n : ℕ) : RetD TapeShapeU (tapeUDb b s n) :=
  RetD.bind_true fun _ ↦ (retD_samplesG _ _).bind fun _ hr ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ (retD_wireUDb _ _ _ _).bind fun _ hwo ↦
      RetD.pure ⟨hr, hwo⟩

end Lvm.VEq

namespace Lvm.E2U

open Lvm DM E2V
open Lvm.E2L (wireUDGc tapeUDGc)

theorem dSelBits_P20L : dSelBits P20L = 1 := rfl
theorem dSel_P20L : dSel P20L = 0 := by unfold dSel; rw [layout0_P20L, layout0_P20U]; rfl

/-- **V_S's merged tape at `P20L` with the intervals `contIvB b` is `tapeUDb b`** (`tapeUDG_R`'s proof). -/
theorem tapeUDGc_R (b : ℕ) (s : List FK) (n : ℕ) :
    mapTU <$> tapeUDGc (contIvB b) rowSwitchDR P20L s n = tapeUDb b s n := by
  have hy : (layout0 P20L).ks / 2 ^ (13 + 5) = 22 := by rw [layout0_P20L, layout0_P20U]; rfl
  have hm : (layout0 P20L).s / 2 ^ 19 = 10 := by rw [layout0_P20L, layout0_P20U]; rfl
  unfold tapeUDGc wireUDGc tapeUDb wireUDb
  simp only [slotDFW_yWG, slotDFW_mWG, dSelBits_P20L, dSel_P20L, ← slotDFG_R, ← tapeGkrDF_eq,
    ← wireTargetDF_eq, ← dWA_eq, samplesG_one, map_bind, bind_map_left, map_pure, bind_assoc, pure_bind,
    show P20L.logN = 20 from rfl, show P20L.ksLog = 13 from rfl, show P20L.nuMain = 23 from rfl,
    show P20L.nuRec = 19 from rfl, show (2 : ℕ) * 25 = 50 from rfl, slotBitsU, hy, hm,
    show (23 : ℕ) - (13 + 5) = 5 from rfl, show (23 : ℕ) - 19 = 4 from rfl, show (20 : ℕ) + 1 = 21 from rfl]
  rfl

end Lvm.E2U

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.E2U
open Lvm.E2L (wireUDGc tapeUDGc)

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **V_S's S2GL tape on the data** refines `tapeProgB b`, its value through `mapTU`. -/
theorem refW_tapeUDGc (b : ℕ) (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ)
    {i : ℕ} (hw : WAt rw i wTapeU) :
    RefAtW cap occ shp rw sig i (tapeUDGc (contIvB b) rowSwitchDR P20L s n) (tapeProgB b d n)
      (fun t o ↦ TapeURelW (mapTU t) o) (i + wTapeU.length) :=
  RefAtW.of_map (by rw [tapeUDGc_R]; exact refW_tapeUDb b s d hs n hw)

end Ref

theorem retD_wireUDGc (iv : List (ℕ × ℕ)) (p : Params) (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) :
    RetD (ColsW p) (wireUDGc iv rowSwitchDR p s n claim) := by
  unfold wireUDGc
  exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_slotDFW _ _ _ _ _ _).bind fun _ hy ↦ (retD_slotDFW _ _ _ _ _ _).bind fun _ hm ↦ RetD.pure ⟨hy, hm⟩

/-- **What V_S's S2GL tape on the data returns**: the closures' shape and the block rows' points. -/
theorem retD_tapeUDGc (b : ℕ) (s : List FK) (n : ℕ) :
    RetD (fun t : TapeU RowZ ↦ TapeShapeU (mapTU t) ∧ ColsW P20L t.wo)
      (tapeUDGc (contIvB b) rowSwitchDR P20L s n) := by
  refine RetD.and (RetD.of_map (f := mapTU) ?_) ?_
  · rw [tapeUDGc_R]; exact retD_tapeUDb b s n
  · unfold tapeUDGc
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
      RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ (retD_wireUDGc _ _ _ _ _).bind fun _ h ↦ RetD.pure h

theorem monoD_tapeUDGc (b : ℕ) (s : List FK) (n : ℕ) : MonoD (tapeUDGc (contIvB b) rowSwitchDR P20L s n) :=
  MonoD.of_map (f := mapTU) (by rw [tapeUDGc_R]; exact monoD_tapeUDb b s n)

end Lvm.VEq

/-! ## The opening with the three claims, the middle phases at S2GL, the claims -/

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2L (linClaims linGroup dOpenFFL mbSumsN typedClaimsL typedProgL midGL bL)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

theorem linClaims_main (nu : ℕ) (ζ : List FE) (css : List (List (FE × ℕ × ℕ))) (vs : List FE) :
    ∀ e ∈ linClaims nu ζ css vs, e.1 = .main := fun e he ↦ by
  unfold linClaims at he
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 he
  rfl

/-- **`dOpenFFL` is `dOpenF`** on the typed items' claims, the three claims, the front's (`dOpenFFI_eq`'s twin). -/
theorem dOpenFFL_eq (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (ζ : List FE)
    (css : List (List (FE × ℕ × ℕ))) (vs : List FE) (items : List FItem) :
    dOpenFFL p s pin ti ζ css vs items =
      dOpenF p s pin (ti.flatMap FItem.flat ++ linClaims p.nuMain ζ css vs ++ items.flatMap FItem.flat) := by
  have hL := linClaims_main p.nuMain ζ css vs
  have hLf : (linClaims p.nuMain ζ css vs).filter (·.1 == .main) = linClaims p.nuMain ζ css vs :=
    List.filter_eq_self.2 fun e he ↦ by simp [hL e he]
  have hLa : (linClaims p.nuMain ζ css vs).all (·.1 == .main) = true :=
    List.all_eq_true.2 fun e he ↦ by simp [hL e he]
  have hall : ((ti ++ items).flatMap FItem.flat).all (·.1 == .main) =
      (ti.flatMap FItem.flat ++ linClaims p.nuMain ζ css vs ++ items.flatMap FItem.flat).all (·.1 == .main) := by
    simp only [List.flatMap_append, List.all_append, hLa, Bool.and_true]
  unfold dOpenFFL dOpenF
  rw [hall, verifyStackedOpeningG_eq, List.flatMap_cons, List.flatMap_append, List.flatMap_cons,
    groups_flat, groups_flat, List.filter_append, List.filter_append, hLf,
    show (linGroup s p.nuMain ζ css vs).flat = (linClaims p.nuMain ζ css vs).map fun e ↦ toStk s p.nuMain e.2 from rfl]
  cases s <;> simp only [SGroup.one, toStk, List.map_map, List.map_append, Function.comp_def, Bool.false_eq_true,
    ↓reduceIte, List.singleton_append, List.append_assoc]

/-- **The pinned middle phases at S2GL as one chain** (`psU_eq`'s twin). -/
theorem psL_eq (Ti : Typed.TInst) (x : List UInt8) :
    Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGL Ti))) x =
      VerifierProgram.readCommitment 19 64 >>= fun _ ↦ Lvm.E2F.pinProg >>= fun za ↦
        typedProgL Ti (pubXT x) >>= fun a ↦ tapeProgB bL (hdX x).s (pubX x).n >>= fun k ↦
          LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) (Lvm.E2F.pinClaim za ::
            Lvm.ASM.ordMk 4 ((assembleU₂ x a k).1.map (relocU20 x)) (assembleU₂ x a k).2) >>= fun _ ↦
              pure true := by
  unfold Lvm.ASM.PSWithM Lvm.E2F.midP Lvm.ASM.midMk midGL
  rw [commitRootUd_mainT]
  simp only [bind_assoc, ret_bindM, pure_bind]

/-- A part of a side's native claim is a committed column's block. -/
theorem mem_mbPartsN {tabs : List Lvm.M3.Tab} {o : BusOut} {pt : List FE} {s : ℕ}
    {p : FE × Placement × List FE} (h : p ∈ Lvm.M3.mbPartsN tabs o pt s) :
    ∃ t ∈ tabs, ∃ (c : ℕ) (rec : Bool) (off : ℕ), t.cols[c]? = some (Lvm.M3.ColSrc.com rec off) ∧
      p.2.1 = ⟨t.τ, off⟩ := by
  unfold Lvm.M3.mbPartsN at h
  obtain ⟨tj, htj, hp⟩ := List.mem_flatMap.mp h
  obtain ⟨c, -, hc⟩ := List.mem_filterMap.mp hp
  have ht : tj.1 ∈ tabs := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp htj)
  split at hc
  · rename_i rec off hcol
    exact ⟨tj.1, ht, c, rec, off, hcol, by rw [← Option.some_inj.mp hc]⟩
  · exact absurd hc (by simp)

/-- **The three claims have no tail** (MB-LIN: every committed column on `C_main`, from word `2^22`, aligned in the
stack). -/
theorem tail_mbSumsN (tabs : List Lvm.M3.Tab) (hlin : Lvm.M3.mbLinB tabs = true)
    (hfc : M3.colsFitB P20 tabs = true) (hfh : M3.colsHiB tabs = true) (pb : List FE × BusOut) :
    ∀ c ∈ mbSumsN tabs pb, Shape.tailValueF c.onStack.1 = 0 := by
  intro c hc
  unfold mbSumsN at hc
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hc
  refine Shape.tailValueF_sum _ _ fun q hq ↦ ?_
  obtain ⟨t, ht, c, rec, off, hcol, hb⟩ := mem_mbPartsN hq
  have hcm : M3.ColSrc.com rec off ∈ t.cols := List.mem_of_getElem? hcol
  have hrec : rec = false := by
    unfold Lvm.M3.mbLinB at hlin
    have h1 := List.all_eq_true.1 hlin t ht
    simp only [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.1 h1.2 _ hcm
    simpa using h2
  subst hrec
  unfold M3.colsHiB at hfh
  unfold M3.colsFitB at hfc
  simp only [Bool.and_eq_true, List.all_eq_true] at hfc hfh
  have h1 := hfc.2 t ht _ hcm
  have h2 := hfh t ht _ hcm
  simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.false_eq_true,
    ite_false] at h1 h2
  rw [hb]
  refine ⟨h2.1, h2.2, ?_⟩
  have := Nat.one_le_two_pow (n := t.τ)
  have h3 : off + 2 ^ t.τ ≤ 2 ^ P20.nuMain := h1.2
  rw [Shape.nuMain_P20] at h3
  show off < 2 ^ CMain.nu20
  omega

theorem forall₂_imp_memL {α β : Type} {R S : α → β → Prop} {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂)
    (H : ∀ a ∈ l₁, ∀ b, R a b → S a b) : List.Forall₂ S l₁ l₂ := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons (H _ List.mem_cons_self _ hab) (ih fun a ha b hb ↦ H a (List.mem_cons_of_mem _ ha) b hb)

/-- **V_S's three claims against the spec's** on the shape's stack (tails `0`). -/
theorem vrel_mbSums {s : Bool} (tabs : List Lvm.M3.Tab) (hlin : Lvm.M3.mbLinB tabs = true)
    (hfc : M3.colsFitB P20 tabs = true) (hfh : M3.colsHiB tabs = true) (pb : List FE × BusOut) (b : Lvm.M3.LBus)
    (h : BusRel tabs pb b) :
    List.Forall₂ (VRel s) ((mbSumsN tabs pb).map fun c ↦ (Com.main, c, (0 : FE)))
      ((Lvm.M3.mbClaimsL CMain.nu20 tabs b).map (·.onStack)) := by
  have hr := Lvm.E2L.mbClaims_relB tabs pb b h
  have ht := tail_mbSumsN tabs hlin hfc hfh pb
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine forall₂_imp_memL hr fun c hc c' hcc ↦ ?_
  have htc := ht c hc
  unfold mbSumsN at hc
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hc
  exact vrel_of (onStack_rel hcc) fun _ ↦ ⟨inStack_full, htc.symm⟩

end Lvm.VEq

/-! ## The claims and the decision at S2GL -/

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.E2L (linClaims dOpenFFL mbSumsN typedClaimsL typedProgL midGL bL dTypedLG decideProgLG decideFLG)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **V_S's claim list at S2GL (after the pin) against `ordMk 4` of `assembleU₂`'s relocated pair** (both shapes;
`claimsU_rel`'s twin): the typed claims as S2GU's, the three claims (`vrel_mbSums`, tails `0` under `mbLinB`), the
front's (`front_relU`). -/
theorem claimsL_rel (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hlin : Lvm.M3.mbLinB N.mbT = true)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (x : List UInt8) (t : Acc × List (Com × BlockClaim × FE) × List FE × BusOut) (a : Lvm.ASM.OpenClaims)
    (hT : TRelTL P20L N Q lay t a) (tp : TapeVU) (k : TapeOutU) (hk : TapeURelW tp k) (hsh : TapeShapeU tp)
    (hall : (t.2.1 ++ (mbSumsN N.mbT (t.2.2.1, t.2.2.2)).map (fun c ↦ (Com.main, c, (0 : FE))) ++
      frontClaimsUD P20U (pubXT x) tp).all (·.1 == .main) = true) :
    List.Forall₂ SCRel (Shape.onStackZsF (Shape.small x)
        (((t.2.1 ++ (mbSumsN N.mbT (t.2.2.1, t.2.2.2)).map (fun c ↦ (Com.main, c, (0 : FE))) ++
          frontClaimsUD P20U (pubXT x) tp).filter (·.1 == .main)).map (·.2)))
      (Lvm.ASM.ordMk 4 ((assembleU₂ x a k).1.map (relocU20 x)) (assembleU₂ x a k).2) := by
  obtain ⟨ry, rv, rr, vR, b, ht1, hry, -, -, hbus, rfl⟩ := hT
  obtain ⟨-, -, -, hfc, hfh⟩ := H.toT.fits
  have hall' : ∀ e ∈ t.2.1 ++ (mbSumsN N.mbT (t.2.2.1, t.2.2.2)).map (fun c ↦ (Com.main, c, (0 : FE))) ++
      frontClaimsUD P20U (pubXT x) tp, e.1 = .main := fun e he ↦ by
    simpa using List.all_eq_true.1 hall e he
  rw [List.filter_eq_self.2 fun e he ↦ by simp [hall' e he]]
  have hok := H.ok
  rw [nuMain_P20] at hok
  have hS : (layout0 P20U).s = CMain.sOffU20 := by rw [layout0_P20U]
  -- the typed claims
  have hrelay := vrel_splitMAt (s := Shape.small x) CMain.sOffU20 [(1, ⟨P20U.nuRec, (layout0 P20U).s⟩, rr)]
    (by simpa using offOK_relayU) vR [(1, ⟨Typed.relayRounds, 0⟩, rr.map toE2)]
    (by simp [E2V.partE, shiftS2At, hS, Lvm.FE2.toE2_one]; rfl)
    (by simp only [List.mem_singleton, forall_eq]; exact relocOKAt_relayU _) (toE2 vR) rfl
  have hsg := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .sigma (.inr (.inr rfl)) ry hry
    (rv.getD 2 0)
  rw [regClaimT_relocSAt N Q lay 23 P20.nuRec hok H.hlay CMain.sOffU20 (by decide) (hS ▸ hσ)] at hsg
  have hcom := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .com (.inl rfl) ry hry (rv.getD 0 0)
  have hks := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .ks (.inr (.inl rfl)) ry hry
    (rv.getD 3 0)
  have hTV : List.Forall₂ (VRel (Shape.small x)) t.2.1
      ((E2V.splitE2 19 ⟨[(1, ⟨Typed.relayRounds, 0⟩, rr.map toE2)], toE2 vR⟩).map
          (fun c ↦ relocSAt CMain.sOffU20 c.onStack) ++
        (regClaimT (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map toE2) (toE2 (rv.getD 2 0))).map
          (relocSAt CMain.sOffU20) ++
        regClaimT (N.inst Q lay) .com N.toN.off (ry.map toE2) (toE2 (rv.getD 0 0)) ++
        regClaimT (N.inst Q lay) .ks N.toN.off (ry.map toE2) (toE2 (rv.getD 3 0))) := by
    rw [ht1, show typedClaimsND N P20L ry rv rr vR = typedClaimsND N P20U ry rv rr vR from rfl]
    unfold typedClaimsND
    exact Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append hrelay hsg) hcom) hks
  -- the three claims
  have hZV := vrel_mbSums (s := Shape.small x) N.mbT hlin hfc hfh (t.2.2.1, t.2.2.2) b hbus
  -- the front
  have hFV := front_relU (s := Shape.small x) x tp k hk hsh (fun hs ↦ of_decide_eq_true hs)
    (by simp [pubX, pubOf])
  have hV := forall₂_onStackZsF (Lk.forall₂_append (Lk.forall₂_append hTV hZV) hFV)
  -- the spec's list in V_S's order
  convert hV using 1
  set G : VStackClaim → VStackClaim := fun w ↦ if Shape.small x then Shape.onStackZ w else w with hG
  have hρ : ∀ l : List VStackClaim, l.map (relocU20 x) = (l.map (relocSAt CMain.sOffU20)).map G := fun l ↦ by
    rw [List.map_map]; rfl
  unfold assembleU₂ typedClaimsL
  dsimp only
  rw [onStackZs_eq_map, hρ, ordMk_of_length 4 _ _ (by simp [E2V.splitE2, regClaimT]), ← List.map_append]
  simp only [List.map_append, List.map_map, List.append_assoc, List.append_nil, Function.comp_def, List.map_nil,
    List.nil_append, E2V.pointE2, E2T.kv_toE2_getD]
  rfl

theorem monoD_dOpenFFL (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (ζ : List FE)
    (css : List (List (FE × ℕ × ℕ))) (vs : List FE) (items : List FItem) :
    MonoD (dOpenFFL p s pin ti ζ css vs items) := by
  rw [dOpenFFL_eq]; exact monoD_dOpenF _ _ _ _

theorem m3G_busFinal (N : TNatT) (p : Params) :
    (m3G N p).busFinal = fun i ↦ M3.busFinalR (M3.sumcheckTabs N.mbT) i := rfl

theorem real_busFinal (p : Params) (tabs : List M3.Tab) :
    (M3.real p fun _ ↦ tabs).busFinal = fun i ↦ M3.busFinalR (M3.sumcheckTabs tabs) i := rfl

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **V_S's typed phases at S2GL** (items on `P20L`'s layout) refine `typedProgL` (`ref_dTypedLO` at `P20L`). -/
theorem ref_dTypedLU (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = Typed.phiVarsT) {i : ℕ} (hw : WAt rw i wTypedL) :
    RefAtWP cap occ shp rw sig i (dTypedLG P20 N (m3G N P20L) pub (typedItemsND N P20L))
      (typedProgL (N.inst Q lay) pub) (fun r a ↦ TRelTL P20L N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun r ↦ N.phiT (r.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE r.1.y) (i + wTypedL.length) := by
  have h := ref_dTypedLO (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) P20L N Q lay H
    (m3G N P20L) ((m3G_busFinal N P20L).trans (real_busFinal P20 N.mbT).symm) pub hacc hw
  rw [dTypedLG_items] at h
  have h' := RefAtWP.of_map h
  exact h'

end Ref

/-- **V_S's read widths at S2GL** in the decision's order: the pin's read, the typed phases', the tape's, the
opening's (`asO`). -/
def wDecL (asO : List Atom) : List ℕ := [24] ++ wTypedL ++ wTapeU ++ widthsA asO

theorem skip_P20L : nodeBytes * 2 ^ (P20L.level ⟨.main, 0⟩).cap = 32 * 2 ^ capS 19 64 := by decide

/-- **V_S's S2GL decision refines the pinned S2GL middle phases** at `occOfU`, with read widths `wDecL asO` from
read `0`, under the promise that its value passes `Φ_Q` at `E2` (`ref_decideGU`'s twin with `claimsL_rel`). -/
theorem ref_decideGL (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hlin : Lvm.M3.mbLinB N.mbT = true)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (vk c : RecursionFast.Digest) (x : List UInt8) {sig : ByteArray} (hpub : pubG vk c sig = pubXT x)
    (asO : List Atom) {rw : ℕ → ℕ}
    (hFO : ∀ (cl : List VStackClaim) (pp : List ℕ),
      Fol capS shpS idxS (LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) cl) asO pp fun _ _ ↦ True)
    (h24O : ∀ w ∈ widthsA asO, w = 24) (hw : WAt rw 0 (wDecL asO))
    (hacc : (pubXT x).accIn.pt.length = Typed.phiVarsT) (hs : sBitsD (pubXT x).s = KG.digestBits (hdX x).s) :
    RefAtPW capS occOfU shpS rw sig 0 (decideProgLG P20L P20 3843 N vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGL (N.inst Q lay)))) x)
      (fun _ b ↦ b = true) (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (wDecL asO).length := by
  rw [wDecL, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨hw0, hwT⟩, hwF⟩, hwO⟩ := hw
  replace hwF := WAt.idx_eq hwF (j := 0 + [24].length + wTypedL.length)
    (by simp only [List.length_append]; omega)
  replace hwO := WAt.idx_eq hwO (j := 0 + [24].length + wTypedL.length + wTapeU.length)
    (by simp only [List.length_append]; omega)
  have hsc : M3.sumcheckTabs N.mbT = N.mbT := H.toT.sc_eq
  rw [psL_eq]
  unfold decideProgLG
  rw [Lvm.E2L.contIvOf_L]
  refine RefAtPW.read_left ?_
  dsimp only
  rw [hpub]
  -- the cap
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_
    ((refW_skip (n := nodeBytes * 2 ^ (P20L.level ⟨.main, 0⟩).cap) (ht := 19) (w := 64) skip_P20L).toPW _)
    (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro - - - -
  -- the pin
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ ((refW_pinD (WAt.cons.mp hw0).1).toPW _) (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro pin za ⟨z, a, rfl, rfl⟩ -
  -- the typed phases
  have hT0 : RefAtPW capS occOfU shpS rw sig (0 + [24].length)
      (dTypedLG P20 N (m3G N P20L) (pubXT x) (typedItemsND N P20L))
      (typedProgL (N.inst Q lay) (pubXT x)) (fun r a ↦ TRelTL P20L N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) (0 + [24].length + wTypedL.length) :=
    ref_dTypedLU N Q lay H (pubXT x) hacc hwT
  refine RefAtPW.bind (Q := fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) ?_ hT0 ?_ ?_
  rotate_left
  · intro b s hs'
    refine promise_of_retDG (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) ?_ hs'
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.pure rfl
  rintro ⟨acc, ti, ζ, bus⟩ a' hT -
  dsimp only
  -- the tape
  rw [show (pubXT x).n = (pubX x).n from rfl]
  have hTp1 := refW_tapeUDGc (cap := capS) (occ := occOfU) (shp := shpS) (sig := sig) bL (pubXT x).s (hdX x).s hs
    (pubX x).n hwF
  have hTp2 := hTp1.retD (retD_tapeUDGc bL (pubXT x).s (pubX x).n)
  have hTp := hTp2.toPW (fun _ ↦ True)
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ hTp (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro tp k ⟨hk, hsh, hcols⟩ -
  -- the opening, on the closures' claims
  have hsh' := hsh
  obtain ⟨-, hl20, -, -, hy5, -, hm5, -⟩ := hsh'
  have hlc : linClaims CMain.nu20 ζ ((List.range 3).map (M3.mbColsN N.mbT bus))
      ((List.range 3).map (M3.mbValueN N.mbT bus ζ)) =
      (mbSumsN N.mbT (ζ, bus)).map fun c ↦ (Com.main, c, (0 : FE)) := Lvm.E2L.linClaims_mb N.mbT (ζ, bus)
  have e : dOpenFFL P20L (TypedV.smallT P20L (pubXT x)) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) ti ζ
      ((List.range 3).map (M3.mbColsN (M3.sumcheckTabs N.mbT) bus))
      (M3.mbValsF (M3.sumcheckTabs N.mbT) bus ζ) (frontItemsU rowAccR P20L (pubXT x) tp) =
      dOpenF P20U (Shape.small x) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) (ti.flatMap FItem.flat ++
        (mbSumsN N.mbT (ζ, bus)).map (fun c ↦ (Com.main, c, (0 : FE))) ++ frontClaimsUD P20U (pubXT x) (mapTU tp)) := by
    rw [M3.mbValsF_eq, dOpenFFL_eq, hsc]
    show dOpenF P20U (TypedV.smallT P20U (pubXT x)) _ (ti.flatMap FItem.flat ++
      linClaims CMain.nu20 ζ ((List.range 3).map (M3.mbColsN N.mbT bus))
        ((List.range 3).map (M3.mbValueN N.mbT bus ζ)) ++
      (frontItemsU rowAccR P20U (pubXT x) tp).flatMap FItem.flat) = _
    rw [smallT_P20U, hlc]
    refine dOpenF_congr _ _ _ ?_
    rw [List.map_append, List.map_append, List.map_append, List.map_append,
      frontU_stk _ _ tp hcols hl20 hy5 hm5]
  rw [e]
  have hO := RefAtP.toPW (ref_dOpenFO (sig := sig) P20U rfl rfl rfl corrMainU _ _ (screl_pinW z a) (Shape.small x) _ _
    (claimsL_rel N Q lay H hlin hσ x (acc, ti.flatMap FItem.flat, ζ, bus) a' hT (mapTU tp) k hk hsh))
    (cap' := capS) (shp' := shpS) (idx := idxS) (hFO _) hwO h24O
  refine RefAtPW.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) hO (fun _ _ _ ↦ trivial) ?_
  rintro - - - -
  exact ((RefAtW.pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) rfl).idx
    (by simp only [wDecL, List.length_append, List.length_singleton])).toPW _
  all_goals repeat' (first
    | (with_reducible exact MonoD.pure _) | (with_reducible exact monoD_skip _)
    | (with_reducible exact monoD_pinD _) | (with_reducible exact monoD_dTypedLG _ _ _ _ _)
    | (with_reducible exact monoD_tapeUDGc _ _ _) | (with_reducible exact monoD_dOpenFFL _ _ _ _ _ _ _ _)
    | (with_reducible exact monoD_dOpenF _ _ _ _)
    | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

end Lvm.VEq

/-! ## The schedule at S2GL: atoms, follow, static check, read widths; the assembly -/

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.E2U Lvm.E2T
open Lvm.E2L (midGL decideProgLG decideFLG)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **S2GL's atoms are `P20`'s** (`P20L`'s levels are `P20U`'s). -/
theorem atomsOf_L (its : List Item) : atomsOf P20L its = atomsOf P20 its :=
  atomsOf_congrL P20L P20 (fun r ↦ by
    obtain ⟨c, lv⟩ := r
    cases c
    · exact withRow0_getD P20.mainLevels 46 lv
    · exact ⟨rfl, rfl⟩) its

theorem atomsOf_scheduleL : atomsOf P20L (schedule P20L) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf P20L (midItemsL P20L) ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [scheduleL_eq _ rfl rfl, atomsOf_append, atomsOf_append, atomsOf_append, atomsOf_nil,
    atomsOf_L (openMainI P20L), atomsOf_L (commitI P20L), show openMainI P20L = openMainI P20 from rfl,
    show commitI P20L = commitI P20 from rfl, atomsOf_commitI]

/-- **S2GL's `P_S` follows the schedule** at `P20L` (`fol_PSOfU`'s proof with `folP_midPL`). -/
theorem fol_PSOfL (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst) (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (midGL Ti))) x)
      (atomsOf P20L (schedule P20L)) [] fun _ _ ↦ True := by
  rw [atomsOf_scheduleL]
  unfold Lvm.ASM.PSWithM
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine @Fol.bindP capS shpS idxS _ _ (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (midGL Ti)) x) _
    (atomsOf P20L (midItemsL P20L)) (atomsOf P20 (openMainI P20) ++ []) _ [] _
    (folP_midPL reloc Ti rfl busDepth_P20 x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

set_option maxRecDepth 200000 in
/-- **The static check at S2GL** at the occupied words `occOfU` (one kernel evaluation over the items). -/
theorem stA_P20L : stA P20L (atomsOf P20L (schedule P20L)) 0 [] [] occOfU = true := by
  rw [stA_atomsOf]
  decide +kernel

/-- **`rwL20` is the S2GL schedule's read widths** from read `0`. -/
theorem wAt_rwL20 : WAt rwL20 0 (widthsA (atomsOf P20L (schedule P20L))) := by
  rw [← readWidthsP_eqAP]
  exact wAt_getD _ _

/-- **The S2GL schedule's read widths** in V_S's decision order (`wDecL`). -/
theorem widthsA_scheduleL : widthsA (atomsOf P20L (schedule P20L)) = wDecL (atomsOf P20 (openMainI P20)) := by
  have hp : widthsA (List.replicate CMain.nu20 Atom.sm) = [] := by
    generalize CMain.nu20 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ]; exact ih
  have hT : widthsA (atomsOf P20L (typedIL P20L)) = wTypedL := by
    have e : typedIL P20L = (zeroIT ++ (wiringIT ++ (relayIT ++ accIT P20L))) ++ miniBusI P20L := by
      simp only [typedIL, List.append_assoc]
    have hm : widthsA (atomsOf P20L (miniBusI P20L)) = List.replicate nMiniRdL 24 := by
      rw [widthsA_eq_replicate _ (mem_widthsA_atomsOf _ _ (by
        simp only [miniBusI, gpI, List.flatten_cons, List.flatten_nil, List.append_nil, noWB_append, noWB_smp,
          noWB_rd, noWB_gpLayersI, Bool.and_self]))]
      rw [atomsOf_L]
      rfl
    rw [e, atomsOf_append, widthsA_append, hm, widthsA_atomsOf]
    simp only [zeroIT, wiringIT, relayIT, accIT, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.flatMap_append, wI_rdE2, wI_gsmpN, wI_gsmp, wI_sumcheckE2I, show sepI.flatMap itemW = [] from rfl,
      wTypedL, wZeroT, wWireT, wRelayT, wAccT, List.append_assoc, List.nil_append]
    rfl
  have hF : widthsA (atomsOf P20L (tapeU P20L ++ wireU P20L)) = wTapeU := by
    rw [widthsA_atomsOf]
    simp only [tapeU, wireU, slotRedI, show P20L.logN = 20 from rfl, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.flatMap_append, wI_rdE2, wI_gsmpN, wI_gsmp, wI_sumcheckE2I, wI_tapeLayersE2I, wI_smp,
      show sepI.flatMap itemW = [] from rfl, wTapeU, wWireU, wTapeGkr, wSlot, List.nil_append, List.append_assoc]
    rfl
  rw [atomsOf_scheduleL, midItemsL, atomsOf_append P20L (pinI _), atomsOf_append P20L (typedIL _), atomsOf_pinIL]
  simp only [widthsA_append, hp, hT, hF, List.append_nil, List.nil_append, List.append_assoc, wDecL]
  rfl

/-- **V_S's S2GL decision refines the pinned S2GL middle phases on the stream with S2GL's read widths** under the
promise that its value passes `Φ_Q` at `E2` (`ref_decideGL` with the opening's atoms and widths). -/
theorem ref_decideGLX (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hlin : Lvm.M3.mbLinB N.mbT = true)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8) (hpub : pubG vk c sig = pubXT x) :
    RefAtPW capS occOfU shpS rwL20 sig 0 (decideProgLG P20L P20 3843 N vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGL (N.inst Q lay)))) x) (fun _ b ↦ b = true)
      (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (wDecL (atomsOf P20 (openMainI P20))).length := by
  have hw : WAt rwL20 0 (wDecL (atomsOf P20 (openMainI P20))) := by
    have h := wAt_rwL20
    rw [widthsA_scheduleL] at h
    exact h
  have hacc : (pubXT x).accIn.pt.length = Typed.phiVarsT := length_pubOfW _ _ _ _ _ _
  have hs : sBitsD (pubXT x).s = KG.digestBits (hdX x).s := by
    rw [show (pubXT x).s = (pubX x).s from rfl, pubX_s, E2V.sBitsD_digestLanes]
  exact ref_decideGL N Q lay H hlin hσ vk c x hpub _ (fun cl pp ↦ fol_openMain cl pp)
    (fun w hw' ↦ mem_widthsA_openF w (by rw [openMainI_F, atomsOf_F]; exact hw')) hw hacc hs

/-- **V_S's S2GL public values are the statement's** (`pubGU_eq` at `P20L`). -/
theorem pubGL_eq {vk c : RecursionFast.Digest} {π : ByteArray} (h : parseOk P20L vk c π = true) {sig : ByteArray}
    (hsig : ∀ t < headerBytesP P20L - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubG vk c sig = pubXT (xOfH (headerBytesP P20L) π) :=
  pubOfW_eq h fe16At 16 accVT (fun _ _ _ h ↦ fe16At_congr h) (hdrFix_le_P _)
    (by rw [headerBytesP_P20L.1]; decide) hsig

private theorem stRunLR {α : Type} (x : StateM RS α) (s : RS) : x.run s = x s := (rfl : x.run s = x s).trans rfl

/-- `decideFLG` at `P20L` holds: the run's checks held and its folded claim passes `Φ_Q` at `E2`. -/
theorem decideFLG_ok {N : TNatT} {vk c : RecursionFast.Digest} {sig : ByteArray}
    (h : decideFLG P20L P20 3843 N vk c sig = true) :
    (runD (decideProgLG P20L P20 3843 N vk c) sig (RS.startH (headerBytesP P20L))).2.ok = true ∧
      N.phiT ((runD (decideProgLG P20L P20 3843 N vk c) sig (RS.startH (headerBytesP P20L))).1.pt.map
        Lvm.e2OfFE) = Lvm.e2OfFE (runD (decideProgLG P20L P20 3843 N vk c) sig (RS.startH (headerBytesP P20L))).1.y := by
  -- SLF-K: `delta` and a non-rfl `run` step (GOLF3-U's lever): `unfold` and an `rfl` on the run made the kernel
  -- evaluate the program's defeq (6.5 M heartbeats)
  have eD : @decideFLG = @decideFLG := rfl
  conv at eD => rhs; delta decideFLG
  rw [eD] at h
  beta_reduce at h
  rw [DM.runOnH, stRunLR] at h
  rcases hr : runD (decideProgLG P20L P20 3843 N vk c) sig (RS.startH (headerBytesP P20L)) with ⟨a, s⟩
  rw [show decideProgLG P20L P20 3843 N vk c sig (RS.startH (headerBytesP P20L)) = (a, s) from hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, fe2_beq h.2⟩

/-- **MBL-STMT 6b's proof**: a `V_S` driving `decideFLG P20L P20 3843 N` after `parseOk P20L` refines the
specification's scheme at `fmtL20`, the middle phases `midMk 4 relocU20 (midGL _)` (`refines_seqOfGO` at `occOfU`
with `ref_decideGLX`, `fol_PSOfL`, `stA_P20L`, `wAt_rwL20`). -/
theorem refinesL20_of (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (hlin : Lvm.M3.mbLinB N.mbT = true) (VS : Lvm.T.SProg)
    (hVS : ∀ vk c π, VS vk c π =
      if parseOk P20L vk c π then drive P20L π (decideFLG P20L P20 3843 N vk c) else .ret false) :
    ∀ (vk : RecursionFast.Digest) (L : RecursionFast.Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof),
      Lvm.T.isS π = true → (VS vk c π).runLog L = some true →
      ((Lvm.ASM.schemeSW Lvm.CT.fmtL20 vk
        (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGL (N.inst Q lay)))))).V c π).runLog L =
        some true :=
  fun vk L c π _ h ↦ runLog_of_seq (fun tr ht ↦ refines_seqOfGO
    (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGL (N.inst Q lay)))))
    (wDecL (atomsOf P20 (openMainI P20))).length P20L Lvm.CT.fmtL20 VS
    (fun vk c ↦ decideFLG P20L P20 3843 N vk c) (decideProgLG P20L P20 3843 N)
    (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (fun sig vk c x ↦ pubG vk c sig = pubXT x) hVS
    (fun _ _ _ hF ↦ decideFLG_ok hF) (fun _ _ _ _ hp hs ↦ pubGL_eq hp hs)
    (fun sig vk c x hpub ↦ ref_decideGLX N Q lay H hlin hσ sig vk c x hpub) rfl rfl rfl
    (by rw [headerBytesP_P20L.1]; decide) (fun _ _ _ hp ↦ okS_of_parseOkH hp (hdrFix_le_P _))
    (fol_PSOfL relocU20 (N.inst Q lay)) stA_P20L wAt_rwL20 vk c π tr ht) L h

end Lvm.VEq
