-- New for lvm2 U-TAPE (UT-L, 2026-11-16): DAY-0 STATEMENTS of `V_S` at S2GU and of the S2GU circuit (the instance of
-- blob U, the guard `staticOkBU20`, `harithU20`, `nodeU20`). Every `sorry` is a day-0 statement tagged
-- `-- UTAPE-STMT <n>`; `opaque`s are PLACEHOLDERS tagged `-- UTAPE-PH <name> (owner)` (their values are S2GT's only so
-- that they elaborate), to be replaced by the owner's definition of the same name and type.
import LvmS2GUMid
import LvmE2VDecG
import LvmE2VPhiT
import LvmE2QTypedReg
import LvmE2QHarPos
import LvmE2QTypedT
import LvmE2QPlan
import LvmFinPos
import LvmQTypedHarB
import LvmQTypedHarChk
import LvmCertTInst
import LvmE2TVEq
import LvmE2UDec
import LvmE2QInstU
import LvmE2QNodeU
import LvmE2QFrontU
import LvmE2VPhiTEqC
import LvmE2URef

/-!
# `V_S` and the circuit at S2GU (day-0 statements)

* `decideFUX N` (UT-V, `LvmE2UDec`): V_S's S2GU decision on the stream (`decideFGX`'s with the S2GU front: the merged
  tape at `E2`, T1's region formula, the wire with `K̃_ks`/`Ĩ_ks`, three slot reductions, no `KS`/`KS` link, the new
  layout's claims); then `Φ_Q` at `E2` through `N.phiT` (`PhiQGC`, unchanged).
* **`VSUX N`**: `parseOk P20U`, then `drive P20U` with `decideFUX N`.
* Instance of blob U (PLACEHOLDERS, UT-C): `frzU20`, `QU20`, `layU20`, `qaU20`, `cacheU20`, `tdataU20`,
  `staticOkTU20`, `powU20`; here `cfgU20`, `NTU20`, `TiU20`, `harChkBU20`, `NodeGU`, **`staticOkBU20`**, `SFU20`.
* Statements: `hq_VSUX` (L), **`refinesU20`** (V), `sfU20` (C), **`harithU20`** (C), **`nodeU20`** (C/L).
-/

set_option autoImplicit false

namespace Lvm.E2U

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.E2F Lvm.E2V Lvm.E2T
open Lvm.Typed (Lay)
open LeanVM.Protocol.Compile

/-! ## `V_S` at S2GU -/

/-- **V_S's decision at S2GU** (UT-V, `LvmE2UDec.decideFUG` at `P20U`; the typed phases' mini-bus record `P20`, as
S2GT). -/
def decideFUX (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool := decideFUG P20U P20 N vk c sig

/-- **`V_S` at S2GU** for the native typed record `N`. -/
def VSUX (N : TNatT) : SProg := fun vk c π =>
  if parseOk P20U vk c π then drive P20U π (decideFUX N vk c) else .ret false

/-- **UTAPE-STMT 21** (owner L): **O1 for S2GU's `V_S`**, any record (`hq_VSGX`'s proof with `qcItems_P20U`). -/
theorem hq_VSUX (N : TNatT) (H : ByteArray → RecursionFast.Digest) (vk c : RecursionFast.Digest)
    (π : RecursionFast.Proof) : ((VSUX N vk c π).queries H).length ≤ qVlvm := by
  show ((if parseOk P20U vk c π then drive P20U π (decideFUX N vk c) else .ret false : OProg Bool).queries H).length ≤
    qVlvm
  split
  · simp only [drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π P20U _ 0
      (fun s ↦ by simp [OProg.queries]) (schedule P20U) 0 _ (by simp)) 1) 1).trans ?_
    have := qcItems_P20U
    show _ ≤ 16384
    omega
  · simp [OProg.queries]

/-- **UTAPE-STMT 22** (owner V; S2GT: GT-L3): **S2GU's `V_S` refines the specification's scheme** at `fmtU20`, the
middle phases `midMk 4 relocU20 (midGU _)` (the typed claims' order as S2GT; the front's claims all on `C_main`, in
`tapeClaimsU`'s order). -/
theorem refinesU20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypT N Q lay)
    (hσ : Lvm.TypedV.SigInSL (layout0 P20U).s N.toN) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSUX N vk c π).runLog L = some true →
      ((schemeSW fmtU20 vk (PSWithM (midP (midMk 4 relocU20 (midGU (N.inst Q lay)))))).V c π).runLog L =
        some true := by
  exact Lvm.VEq.refinesU20_of N Q lay H hσ (VSUX N) fun _ _ _ ↦ rfl

end Lvm.E2U

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped LeanVM.Protocol
open Lvm.E2T (TNatT PhiQGC THypT)
open Lvm.E2U (VSUX decideFUX GoodTU SBlkU)

/-! ## The instance of blob U -/

-- the instance of blob U (`cfgU20`, `frzU20`, `tdataU20`, `qaU20`, `QU20`, `powU20`, `layU20`, `cacheU20`,
-- `staticOkTU20`): UT-C's `LvmE2QInstU` (the placeholders of the day-0 list, replaced)

/-- **V_S's typed record at S2GU** (`phiT`: the fast `Φ_Q` at `E2`). -/
def NTU20 : TNatT := ⟨Lvm.QTyped.nregsOf layU20 frzU20, PhiQGC cacheU20, Lvm.QTyped.mbTOf cfgU20 frzU20⟩

/-- **The typed instance at S2GU.** -/
noncomputable def TiU20 : TInst := NTU20.inst QU20 layU20

/-- **The HAR's static checks at S2GU** (`harChkBG20` at the S2GU instance: the typed phases end where the merged tape
starts; the opening's layout facts at `P20U`). -/
def harChkBU20 : Bool :=
  Lvm.QTyped.tdMatchB tdataU20 NTU20.toN &&
    typedEndT tdataU20 P20U == posOf P20U (phaseItem0 P20U .tape) &&
    decide (typedEndT tdataU20 P20U + 40 ≤ 8 * streamLanes P20U) &&
    decide (posOf P20U (phaseItem0 P20U .openMain) + 48 ≤ 8 * streamLanes P20U) &&
    powU20.all (fun a => decide (a.1 + 2 < streamLanes P20U) && decide (a.2 ≤ 64)) &&
    posOf P20U (phaseItem0 P20U .openMain) == 8 * (phaseLane P20U .openMain 0 - 5) &&
    Lvm.Har.LayOk (cfgMainF P20U (fun _ => 0) (fun _ => 0)) (streamLanes P20U) &&
    8 * Lvm.Har.stackEndL P20U.grind P20U.mainOod P20U.mainLevels (phaseLane P20U .openMain 0 - 5 + 15) ==
      hashedLen P20U &&
    decide (P20U.mainLevels.length ≤ (Lvm.QLink.opens P20U).length) && decide (1 ≤ 64 - P20U.grind) &&
    decide (Lvm.Fin.PosLanes P20U P20U.grind P20U.mainOod P20U.mainLevels (phaseLane P20U .openMain 0 - 5 + 15) 0) &&
    typedRegB tdataU20 (layout0 P20U).s

/-- **The S2GU guard's circuit facts** (`NodeGC` at `cfgU20`, `spongeBlocks P20U`, `pubLanesT`). -/
abbrev NodeGU : Prop := NodeGCL cfgU20 (spongeBlocks P20U) pubLanesT frzU20 QU20 layU20 NTU20.toN

/-- **The S2GU guard** (S2GT's conjuncts at the S2GU instance; lead decision R2/R3: the input map and `σ′`'s block on
`layout0 P20U`'s targets, `nodeChkBGL`, `sigInSBL`). -/
def staticOkBU20 : Bool :=
  staticOkTU20 && Lvm.QTyped.nodeChkBGL (spongeBlocks P20U) pubLanesT cfgU20 frzU20 QU20 layU20 NTU20.toN &&
    Lvm.TypedV.sigInSBL (layout0 P20U).s NTU20.toN && harChkBU20 && Lvm.T.oneOkB layU20 && Lvm.Typed.KT.linOkX cacheU20

/-- **The S2GU guard's facts.** -/
abbrev SFU20 : Prop :=
  NodeGU ∧ harChkBU20 = true ∧ Lvm.T.oneOkB layU20 = true ∧ Lvm.Typed.KT.linOkX cacheU20 = true

/-- **UTAPE-STMT 23** (owner C): the guard's facts from `staticOkBU20 = true` (`sfG20`'s twin). -/
theorem sfU20 (h : staticOkBU20 = true) : SFU20 := by
  simp only [staticOkBU20, Bool.and_eq_true] at h
  exact ⟨nodeGCL_of QU20_eq rfl rfl rfl h.1.1.1.1.1 h.1.1.1.1.2 h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **UTAPE-STMT 24** (owner L): **the facts `harChkBU20` decides** (`harChkG20_sound` at S2GU). -/
theorem harChkU20_sound (h : harChkBU20 = true) :
    Lvm.Har.TdOk tdataU20 NTU20.toN ∧
      typedEndT tdataU20 P20U = posOf P20U (phaseItem0 P20U .tape) ∧
      typedEndT tdataU20 P20U + 40 ≤ 8 * streamLanes P20U ∧
      posOf P20U (phaseItem0 P20U .openMain) + 48 ≤ 8 * streamLanes P20U ∧
      (∀ a ∈ powU20, a.1 + 2 < streamLanes P20U ∧ a.2 ≤ 64) ∧
      posOf P20U (phaseItem0 P20U .openMain) = 8 * (phaseLane P20U .openMain 0 - 5) ∧
      Lvm.Har.LayOk (cfgMainF P20U (fun _ => 0) (fun _ => 0)) (streamLanes P20U) = true ∧
      8 * Lvm.Har.stackEndL P20U.grind P20U.mainOod P20U.mainLevels (phaseLane P20U .openMain 0 - 5 + 15) =
        hashedLen P20U ∧
      P20U.mainLevels.length ≤ (Lvm.QLink.opens P20U).length ∧ 1 ≤ 64 - P20U.grind ∧
      Lvm.Fin.PosLanes P20U P20U.grind P20U.mainOod P20U.mainLevels (phaseLane P20U .openMain 0 - 5 + 15) 0 ∧
      typedRegB tdataU20 (layout0 P20U).s = true := by
  simp only [harChkBU20, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨Lvm.Har.tdOk_of h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩


/-! ## Q_arith's inputs at S2GU (`harithG20`'s, at `cfgU20`) -/

section PairUH

variable {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}

/-- The trace bytes of the child at S2GU have `hashedLen P20U` bytes. -/
theorem sigU_size (hL : LaneLink P20U (wsC qr)) : (traceBytesB (decode P20U (wsC qr))).size = hashedLen P20U := by
  rw [traceBytesB_decode streamOk_P20U hL, Lvm.Har.sigma_sizeT hL.size]

/-- **The node memory streams the child's trace at S2GU** (`streamed_child` at `cfgU20`). -/
theorem streamedU {M : Mem} (hst : ∀ j < 2 ^ (lay cfgU20).m, M.k ((lay cfgU20).sb + j) = laneK (wsC qr) j)
    (hL : LaneLink P20U (wsC qr)) : Lvm.Q1.Streamed M (traceBytesB (decode P20U (wsC qr))) (streamLanes P20U) := by
  have hh : hashedLen P20U = 538656 := sizes_P20U.1.2.2.1
  have hw : (wsC qr).length = 17 * 2 ^ 14 := by rw [wsC, wsOf, List.length_map, List.length_range]
  exact Lvm.Har.streamed_child cfgU20 streamOk_P20U hL hst (T := streamLanes P20U)
    (by rw [streamLanes, hh]; decide) (by rw [show cfgU20.p = P20U from rfl, streamLanes]; omega)
    (by rw [streamLanes, hh, hw]; norm_num)

theorem hWU (S : NodeGU) (H : THypT TiU20) (hG : GoodTU TiU20 H x qm qr) :
    WiringRelX QU20 layU20 (zTX (NTU20.toN.instL Pub.hdrLanesT QU20 layU20) Lvm.VEq.pubXT x qm qr) :=
  (wiringRelT_iff QU20 layU20 S.st.hlay _).mp hG.1.1.1.1

/-- **The three row switches' words at S2GU** (the `rowAux` blocks of `specQU` on `tBu cfgU20 i`). -/
theorem rowWordsU (S : NodeGU) (H : THypT TiU20) (hG : GoodTU TiU20 H x qm qr) :
    (∀ j < 128, (memT TiU20 x qm qr).k (tBu cfgU20 0 + j) =
      rowWordD (Lvm.Q2.slicesOf (memT TiU20 x qm qr) wlU.slicesD) j) ∧
    (∀ j < 128, (memT TiU20 x qm qr).k (tBu cfgU20 1 + j) =
      rowWordD (Lvm.Q2.slicesOf (memT TiU20 x qm qr) wlU.slicesY) j) ∧
    (∀ j < 128, (memT TiU20 x qm qr).k (tBu cfgU20 2 + j) =
      rowWordD (Lvm.Q2.slicesOf (memT TiU20 x qm qr) wlU.slicesM) j) := by
  obtain ⟨f, hf⟩ := Lvm.QTyped.aux_mkLayD QU20 (specQU cfgU20 QU20 powU20) dintsU20
  have hmem : ∀ B, B ∈ Lvm.Q2.rowAuxL (f (specQ cfgU20 QU20).auxWords.length) (tBu cfgU20 0) wlU.slicesD ++
      Lvm.Q2.rowAuxL (f ((specQ cfgU20 QU20).auxWords.length + 1)) (tBu cfgU20 1) wlU.slicesY ++
      Lvm.Q2.rowAuxL (f ((specQ cfgU20 QU20).auxWords.length + 2)) (tBu cfgU20 2) wlU.slicesM →
      B ∈ layU20.aux := fun B hB => by
    show B ∈ (mkLayD QU20 (specQU cfgU20 QU20 powU20) dintsU20).1.aux
    rw [hf]
    show B ∈ (specQ cfgU20 QU20).auxOf f ++ _ ++ _
    exact List.mem_append_left _ (List.mem_append_right _ hB)
  have hone := zOf_one (NTU20.toN.instL Pub.hdrLanesT QU20 layU20) H.ok.2 Lvm.M3.lay26 (Lvm.VEq.pubXT x) qm qr
  exact ⟨fun j hj => rowWords_of_aux S.st.hlay hone (hWU S H hG)
      (fun B hB => hmem B (List.mem_append_left _ (List.mem_append_left _ hB))) hj,
    fun j hj => rowWords_of_aux S.st.hlay hone (hWU S H hG)
      (fun B hB => hmem B (List.mem_append_left _ (List.mem_append_right _ hB))) hj,
    fun j hj => rowWords_of_aux S.st.hlay hone (hWU S H hG) (fun B hB => hmem B (List.mem_append_right _ hB)) hj⟩

/-- **V's proof-of-work checks at S2GU** (`powOk_of_blksU` at `cfgU20`). -/
theorem powOkU (S : NodeGU) (H : THypT TiU20) (hG : GoodTU TiU20 H x qm qr) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memT TiU20 x qm qr) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ powU20)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L :=
  powOk_of_blksU cfgU20 (Q := QU20) (tl := layU20) (d := dintsU20) rfl S.st.hlay
    (zOf_one (NTU20.toN.instL Pub.hdrLanesT QU20 layU20) H.ok.2 Lvm.M3.lay26 (Lvm.VEq.pubXT x) qm qr) (hWU S H hG)
    hS hL hpw

/-- **Q_sig's `ChildOk` at S2GU** (`childOkG` at `cfgU20`, the `KS` facts from the merged tape, `sigKSin_of_GkU`). -/
theorem childOkU (S : NodeGU) (H : THypT TiU20) {vk c : RecursionFast.Digest} (hok : okS vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTU TiU20 H x qm qr ∧ SBlkU qm qr) :
    ChildOk (sigIn cfgU20) (memT TiU20 x qm qr).k := by
  have hone : (NTU20.toN.instL Pub.hdrLanesT QU20 layU20).src? layU20.one = some .one := H.ok.2
  obtain ⟨hH, hA⟩ := hholdsCU S Pub.hdrLanesT Lvm.VEq.pubXT hone (hWU S H hG.1) H.hτ H.layOk hG.1.1.1.1.2 hG.2
  have hH' : QU20.Holds (memT TiU20 x qm qr) := hH
  have hA' : QU20.Asserts (memT TiU20 x qm qr) := hA
  rw [QU20_eq] at hH' hA'
  have P := parts_of_holdsP hH' hA'
  have hB : spongeBlocks P20U ≤ 2 ^ 13 := by rw [sizes_P20U.1.2.2.2.2.1]; norm_num
  have mp := hmapCU S Pub.hdrLanesT Lvm.VEq.pubXT hB (by decide) (fun x _ hj ↦ pubXT_lane x hj) hok hb hG.2
  have hks := Lvm.E2U.sigKSin_of_GkU hG.1.2 mp.xs mp.ys mp.yc mp.yls mp.yns
  exact (qsig_sound_in (by rw [show (sigIn cfgU20).ln = 20 from rfl]; omega) P.2.1 mp.flag hks
    (hbitsCU S Pub.hdrLanesT Lvm.VEq.pubXT hone (hWU S H hG.1))
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h).2

/-- **Q_link's position cells at S2GU** (`posCellsG` at `cfgU20`). -/
theorem posCellsU (S : NodeGU) (H : THypT TiU20) {vk c : RecursionFast.Digest} (hok : okS vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTU TiU20 H x qm qr ∧ SBlkU qm qr) :
    ∀ k < (opens P20U).length, ((opens P20U).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20U).getD k default).L.t,
      (memT TiU20 x qm qr).k (nK cfgU20 + posIdx P20U k j) =
        kOf (posL P20U (wsC qr) (((opens P20U).getD k default).pe + j / 8)
          (j % 8 * ((opens P20U).getD k default).L.height) ((opens P20U).getD k default).L.height) := by
  intro k hk hH j hj
  have hone : (NTU20.toN.instL Pub.hdrLanesT QU20 layU20).src? layU20.one = some .one := H.ok.2
  obtain ⟨hH', hA⟩ := hholdsCU S Pub.hdrLanesT Lvm.VEq.pubXT hone (hWU S H hG.1) H.hτ H.layOk hG.1.1.1.1.2 hG.2
  have hH'' : QU20.Holds (memT TiU20 x qm qr) := hH'
  have hA' : QU20.Asserts (memT TiU20 x qm qr) := hA
  rw [QU20_eq] at hH'' hA'
  have P := parts_of_holdsP hH'' hA'
  have hB : spongeBlocks P20U ≤ 2 ^ 13 := by rw [sizes_P20U.1.2.2.2.2.1]; norm_num
  have mp := hmapCU S Pub.hdrLanesT Lvm.VEq.pubXT hB (by decide) (fun x _ hj ↦ pubXT_lane x hj) hok hb hG.2
  have hp : cfgU20.p = P20U := rfl
  have hk' : k < (opens cfgU20.p).length := by rw [hp]; exact hk
  have hH2 : ((opens cfgU20.p).getD k default).L.height ≤ 64 := by rw [hp]; exact hH
  have hj' : j < ((opens cfgU20.p).getD k default).L.t := by rw [hp]; exact hj
  have hv := posVal_onC (C := cfgU20) (outsOnCU S Pub.hdrLanesT Lvm.VEq.pubXT hone (hWU S H hG.1))
    (by rw [hp]; exact streamOk_P20U) (by rw [hp]; exact hQU20) mp.stream hk' hH2 hj'
  rw [hp] at hv
  have hq := qlink_pos (pt := p0 (nK cfgU20) 0) hQU20 P.1.1 hk hj
  exact hq.trans hv

/-- The current proof's `vk` cells at S2GU (`vk_cellsG` at `cfgU20`). -/
theorem vk_cellsU {M : Mem} {vk : RecursionFast.Digest}
    (hpub : ∀ j < pubLanesT, M.k ((sigIn cfgU20).flag + j) = hdrLane x j) (hvk : (hdrOf x).vk = vk) :
    ∀ i < 4, M.k (pbB cfgU20 + 1 + i) = (digestLanes vk).getD i 0 := by
  intro i hi
  have hj : 1 + i < pubLanes := by rw [pubLanes_eq]; omega
  have e1 : M.k (pbB cfgU20 + 1 + i) = (Lvm.NS.hdrLanes x).getD (1 + i) 0 := by
    rw [Nat.add_assoc, show pbB cfgU20 = (sigIn cfgU20).flag from rfl, hpub _ (by unfold pubLanesT; omega),
      Lvm.NS.hdrLanes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some]
  have hv : (Lvm.VEq.pubX x).vk = digestLanes vk := by rw [← hvk]; rfl
  have hl : i < (digestLanes vk).length := by simp only [digestLanes, List.length_map, List.length_range]; omega
  rw [e1, Lvm.NS.hdrLanes_eq_pubX, Pub.hdrLanes, hv]
  simp only [List.append_assoc, List.singleton_append]
  rw [Nat.add_comm, List.getD_append _ _ _ _ (by rw [List.length_cons]; omega), List.getD_cons_succ]

/-- **`Φ_Q` at `E2` holds at the folded accumulator at S2GU** (the good pair's `AccOkTT`, STMT 6 with `linOkX`). -/
theorem phiU20_acc (S : NodeGU) (hlin : Lvm.Typed.KT.linOkX cacheU20 = true) (H : THypT TiU20)
    (hG : GoodTU TiU20 H x qm qr) {M : Mem} (hpub : ∀ j < pubLanesT, M.k ((sigIn cfgU20).flag + j) = hdrLane x j) :
    NTU20.phiT ((accCT M (pbB cfgU20)).pt.map Lvm.e2OfFE) = Lvm.e2OfFE (accCT M (pbB cfgU20)).y := by
  have hacc : Lvm.E2T.AccOkTT TiU20 (Lvm.VEq.pubXT x) := hG.1.2
  have hl : ∀ j < 46, (Lvm.Q2.ld2 (pbB cfgU20 + 615 + 2 * j)).val M =
      Lvm.e2OfFE (fe16At (Lvm.VEq.sigOfX x) (headerAt (offAcc + 16 * j))) := by
    intro j hj
    have hpb : (sigIn cfgU20).flag = pbB cfgU20 := rfl
    have e1 := hpub (615 + 2 * j) (by show 615 + 2 * j < 615 + 2 * (45 + 1); omega)
    have e2 := hpub (615 + 2 * j + 1) (by show 615 + 2 * j + 1 < 615 + 2 * (45 + 1); omega)
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (615 + 2 * j) = headerAt (offAcc + 16 * j) by
      simp only [headerAt, offAcc, sigBytes]; omega] at e1
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (615 + 2 * j + 1) = headerAt (offAcc + 16 * j) + 8 by
      simp only [headerAt, offAcc, sigBytes]; omega] at e2
    show (⟨(FE.ofK (M.k (pbB cfgU20 + 615 + 2 * j))).c₀, (FE.ofK (M.k (pbB cfgU20 + 615 + 2 * j + 1))).c₀⟩ : FE2) = _
    rw [Nat.add_assoc (pbB cfgU20), e1, Nat.add_assoc (pbB cfgU20) (615 + 2 * j), e2]
    rfl
  have hpt : (accCT M (pbB cfgU20)).pt.map Lvm.e2OfFE = (Lvm.VEq.pubXT x).accIn.pt.map Lvm.e2OfFE := by
    simp only [accCT, Lvm.VEq.pubXT, pubOfW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 45 := List.mem_range.mp hj
    exact hl j (by omega)
  have hy : Lvm.e2OfFE (accCT M (pbB cfgU20)).y = Lvm.e2OfFE (Lvm.VEq.pubXT x).accIn.y := by
    simp only [accCT, Lvm.VEq.pubXT, pubOfW]
    exact hl Lvm.VEq.accVT (by decide)
  rw [hpt, hy]
  have hc : cacheU20 = Lvm.Typed.cacheWX QU20 layU20 := cacheWXF_eq QU20 layU20 S.st.hlay
  show Lvm.E2T.PhiQGC cacheU20 _ = _
  rw [hc, Lvm.E2T.PhiQGC, Lvm.Typed.KT.PhiQGC_eqW QU20 layU20 S.st.hlay S.st.cache (hc ▸ hlin) _
    (by rw [List.length_map]; exact H.acc x)]
  have hpt' : Lvm.E2T.accPtT (Lvm.VEq.pubXT x) = ((Lvm.VEq.pubXT x).accIn.pt.map Lvm.e2OfFE).map FE2.toE2 := by
    rw [Lvm.E2T.accPtT, List.map_map]; rfl
  have hy' : Lvm.E2T.accYT (Lvm.VEq.pubXT x) = FE2.toE2 (Lvm.e2OfFE (Lvm.VEq.pubXT x).accIn.y) := rfl
  have hof : ∀ z : FE2, Lvm.Typed.ofE2 (FE2.toE2 z) = z := fun _ => rfl
  rw [Lvm.E2T.AccOkTT, Lvm.Typed.PhiQT, hpt', hy', List.map_map] at hacc
  simp only [Function.comp_def, hof, List.map_id'] at hacc
  exact FE2.toE2_injective hacc

end PairUH

set_option maxRecDepth 100000 in
/-- The mini-bus record at S2GU (`miniC` at `cfgU20`). -/
theorem miniU20 (S : NodeGU) : Lvm.M3.sumcheckTabs NTU20.toN.mbT = NTU20.toN.mbT ∧
    (Lvm.QTyped.tdataOf cfgU20 frzU20).mbS = NTU20.toN.mbT.map Lvm.M3.Tab.shape ∧
    (Lvm.QTyped.tdataOf cfgU20 frzU20).mbR = cfgU20.p.tableRounds ∧
    (Lvm.QTyped.tdataOf cfgU20 frzU20).mbD = cfgU20.p.busDepth ∧
    Lvm.Har.FixListed NTU20.toN.mbT (Lvm.QTyped.tdataOf cfgU20 frzU20).mbFix := by
  have hsc : Lvm.M3.sumcheckTabs (mbTOf cfgU20 frzU20) = mbTOf cfgU20 frzU20 := Lvm.Har.mbT_sumcheck cfgU20 _ _ _
  have hm := S.st.mini
  rw [S.mb] at hm ⊢
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hD⟩, -⟩, -⟩, hR⟩, -⟩, -⟩, -⟩, -⟩ := hm
  rw [hsc] at hR
  obtain ⟨t1, t2, t3, t4⟩ := Lvm.Har.tdataOf_mb cfgU20 frzU20
  rw [t1, t2, t3, t4, hR, hD]
  exact ⟨hsc, rfl, rfl, rfl, Lvm.Har.mbT_fix cfgU20 _ _ _⟩

set_option maxHeartbeats 1000000 in
/-- **UTAPE-STMT 25** (owner C): **Q_arith is `V_S`'s decision at S2GU** (`harithG20`'s twin: the node program's
segments on a good S2GU pair whose `qr` is `qm`'s stream block at S2GU). Phase split (signatures fixed by the owners,
one-liners frozen): 25a pin at `P20U`'s positions; 25b the S2GU front's gadgets (`front_phasesU`: the 21-variable
tape, T1's region formula, the wire with `K_ks`/`I_ks` automata, three slot reductions, three row switches); 25c–25e
the typed phases, their claims and the mini-bus (S2GT's, at `cfgU20`); 25f the opening at `P20U`; 25g the
composition (`core_of_phasesU`, `decideFUX_of`); 25h `harChkU20_sound` (STMT 24). Re-freeze U-A1 (lead): the input map is
`InMapMBU` (`KS`'s fields on the merged tape's `MqU`/`YqU`; S2GT's `InMapMB` hard-wires the `KS` block and `X`). -/
theorem harithU20 (S : NodeGU) (hhar : harChkBU20 = true) (hlin : Lvm.Typed.KT.linOkX cacheU20 = true)
    (H : THypT TiU20) (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 →
      GoodTU TiU20 H x qm qr ∧ SBlkU qm qr →
      InMapMBU (spongeBlocks P20U) pubLanesT (lay cfgU20) (sigIn cfgU20) (memT TiU20 x qm qr) vk x qm qr →
      LaneLink P20U (wsC qr) → LinkOk P20U (decode P20U (wsC qr)) →
      Ok (ctxOf TiU20.Q) (memT TiU20 x qm qr) qaU20 (p2P (lay cfgU20) (sigIn cfgU20) (nK cfgU20) 0 P20U) →
      decideFUX NTU20 vk (hdrOf x).cL (traceBytesB (decode P20U (wsC qr))) = true := by
  intro c x qm qr hok hb hG hin hLL hlink hrun
  obtain ⟨sig, hsig⟩ : ∃ s, traceBytesB (decode P20U (wsC qr)) = s := ⟨_, rfl⟩
  rw [hsig]
  -- the program's three parts after Q_sig: the pin, the front, `qarithG`
  have hrun' : Lvm.QSig.Ok (ctxOf TiU20.Q) (memT TiU20 x qm qr)
      (pinF cfgU20.p >>= fun pin ↦ frontU cfgU20 >>= fun o ↦ qarithG cfgU20 tdataU20 pin o)
      (p2P (lay cfgU20) (sigIn cfgU20) (nK cfgU20) 0 P20U) := hrun
  obtain ⟨hPin, hR⟩ := Lvm.Har.okb hrun'
  obtain ⟨q1, hq1⟩ : ∃ q1, (p2P (lay cfgU20) (sigIn cfgU20) (nK cfgU20) 0 P20U).adv
      (pinF cfgU20.p (p2P (lay cfgU20) (sigIn cfgU20) (nK cfgU20) 0 P20U)).2 = q1 := ⟨_, rfl⟩
  obtain ⟨pin, hpinE⟩ : ∃ pin, (pinF cfgU20.p (p2P (lay cfgU20) (sigIn cfgU20) (nK cfgU20) 0 P20U)).1 = pin :=
    ⟨_, rfl⟩
  rw [hq1, hpinE] at hR
  obtain ⟨hFr, hQa⟩ := Lvm.Har.okb hR
  obtain ⟨o, hfr⟩ : ∃ o, (frontU cfgU20 q1).1 = o := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2, q1.adv (frontU cfgU20 q1).2 = q2 := ⟨_, rfl⟩
  rw [hfr, hq2] at hQa
  -- the static facts, the stream, the gate, `vk`
  obtain ⟨htd, hTE, hTT, hTO, hPW, hOU, hLY, hSE, hML, hGR, hPL, hTR⟩ := harChkU20_sound hhar
  have hS : Lvm.Q1.Streamed (memT TiU20 x qm qr) sig (streamLanes P20U) := hsig ▸ streamedU hin.stream hLL
  have hTl : streamLanes P20U = 67332 := sizes_P20U.1.2.2.2.1
  have hg : (memT TiU20 x qm qr).k (pbB cfgU20) = 1 := hin.flag
  have hvk := vk_cellsU hin.pub (okS_vk hok)
  -- `qarithG`: the constants
  unfold qarithG at hQa
  obtain ⟨hZ, hR⟩ := Lvm.Har.okb hQa
  have ez : (const .E 0 (kc 0) q2).1 = ec q2.e := rfl
  have hzv := (Lvm.Har.constE_val hZ.1).trans ofK_zero
  rw [ez] at hzv
  rw [ez, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hO, hR⟩ := Lvm.Har.okb hR
  have eo : (const .E 1 (kc 0) ⟨q2.k, q2.e + 1⟩).1 = ec (q2.e + 1) := rfl
  have hov := (Lvm.Har.constE_val hO.1).trans ofK_one
  rw [eo] at hov
  rw [eo, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hZK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, Lvm.Har.constK_adv] at hR
  obtain ⟨hOK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, Lvm.Har.constK_adv] at hR
  have hzkv : (kc q2.k).val (memT TiU20 x qm qr) = 0 := by
    have e := const_val hZK.1
    rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, ofK_zero] at e
    exact e
  have hokv : (kc (q2.k + 1)).val (memT TiU20 x qm qr) = 1 := by
    have e := const_val hOK.1
    rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, ofK_one] at e
    exact e
  -- the typed phases (`typed_phaseTG` at `P20U`), their claims, the shape cell (outputs and pointers opaque)
  obtain ⟨t, q3, ht, hq3e, hTy, hR⟩ := ok_bindV hR
  obtain ⟨tc, q4, htc, hq4e, hTC, hR⟩ := ok_bindV hR
  obtain ⟨ka, q5, hka, hq5e, hKA, hR⟩ := ok_bindV hR
  obtain ⟨kb, q6, hkb, hq6e, hKB, hR⟩ := ok_bindV hR
  obtain ⟨sK, q7, hsKe, hq7e, hSK, hOpen⟩ := ok_bindV hR
  obtain ⟨hsc, hSs, hRr, hDd, hfix⟩ := miniU20 S
  have hpowA := powOkU S H hG.1 hS (L := powU20) (fun a ha => ha) hPW
  have hpowT : Lvm.Q1.PowOkV (feAt sig) (typedChalsT P20U) := fun a ha =>
    hpowA a (List.mem_append_right _ ha)
  have hpowF : Lvm.Q1.PowOkV (feAt sig) (powFrontU P20U) := fun a ha => hpowA a (List.mem_append_left _ ha)
  have hP0 := pinEndU
  have htyped := typed_phaseTG P20U rfl (c := ctxOf TiU20.Q) vk (hdrOf x).cL hS hg hvk (z := ec q2.e)
    (o := ec (q2.e + 1)) (zk := kc q2.k) (ok := kc (q2.k + 1)) rfl rfl hzv hov rfl rfl hzkv hokv htd P20 rfl hsc hSs
    hRr hDd hfix (busLanes_of busLanesB_P20U) hpowT (by rw [hTl] at hTT ⊢; exact hTT) (by rw [hTl]; decide) _
    (by simp) hTy (Lvm.E2T.typedItemsND NTU20 P20U)
  have hle : typedPosF P20U ≤ typedEndT tdataU20 P20U := by
    have h1 := mbPT_le tdataU20 P20U
    have h2 := (busLanes_of busLanesB_P20U).mb
    have h3 : mbPT P20U = 8 * busL P20U iMB - 40 := rfl
    omega
  rw [show cfgU20.p = P20U from rfl] at ht
  -- the typed claims' inputs (the gadget's shape), before `ht` renames the output
  obtain ⟨⟨hry, hryK⟩, ⟨hrr, hrrK⟩, hvR, hrvK, htabl⟩ := typedGT_shape (c := ctxOf TiU20.Q)
    (M := memT TiU20 x qm qr) tdataU20 P20U (pbB cfgU20) (pubLanesTC P20U) (ec q2.e) (ec (q2.e + 1)) (kc q2.k)
    (kc (q2.k + 1)) _ hTy.1
  rw [ht] at hry hryK hrr hrrK hvR hrvK htabl
  rw [hTE, ht] at htyped
  -- the pin (`pin_phase`)
  have hnu : P20U.nuMain = 23 := rfl
  have hpb := pinHPU
  have hpe := pinEndU
  have hqa := pinQaU
  rw [hnu] at hpe hqa
  have epin : pinF cfgU20.p = Lvm.Q2.pinG 23 (phaseLane P20U .commit 1) (phaseLane P20U .commit (23 + 1)) := rfl
  rw [epin] at hPin hpinE
  obtain ⟨hpin, hpinV⟩ := Lvm.Q2.pin_phase hS (nu := 23) (by norm_num) hpb.symm hqa
    (by rw [hTl] at hTT ⊢; omega) (by rw [hqa]; rw [hTl] at hTT ⊢; omega) hPin.1
  rw [hpe] at hpin
  rw [hpinE] at hpinV
  obtain ⟨zP, aP, hzP, hzL⟩ := pinG_fst 23 (phaseLane P20U .commit 1) (phaseLane P20U .commit (23 + 1))
    (p2P (lay cfgU20) (sigIn cfgU20) (nK cfgU20) 0 P20U)
  rw [hpinE] at hzP
  have hpinB : (Lvm.pinD 23 sig ⟨posOf P20U 1, 0, true⟩).1 =
      BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memT TiU20 x qm qr) zP) (aP.val (memT TiU20 x qm qr)) := by
    rw [hzP, cclaim_point] at hpinV
    exact (Prod.mk.inj hpinV).2.symm
  rw [hpinB] at hpin
  -- the front's inputs and its phases
  have hT29 : 29 ≤ streamLanes P20U := by rw [hTl]; norm_num
  obtain ⟨hrD, hrY, hrM⟩ := rowWordsU S H hG.1
  have hch := childOkU S H hok hb hG
  have hon := outsOnCU S Pub.hdrLanesT Lvm.VEq.pubXT H.ok.2 (hWU S H hG.1)
  have hsb := sBits_onC hon
  obtain ⟨hnb, hn, hsbv⟩ := frontIns hS hT29 (hbitsCU S Pub.hdrLanesT Lvm.VEq.pubXT H.ok.2 (hWU S H hG.1))
    hch hsb Lvm.VEq.accVT vk (hdrOf x).cL rfl rfl
  have hh : (Lvm.E2T.pubG vk (hdrOf x).cL sig).h =
      (List.range 4).map fun l => (memT TiU20 x qm qr).k (Lvm.Har.hLane l) := Lvm.Har.pub_h hS hT29 vk (hdrOf x).cL
  have hsmE : TypedV.smallT P20U (Lvm.E2T.pubG vk (hdrOf x).cL sig) =
      decide ((Lvm.E2T.pubG vk (hdrOf x).cL sig).n ≤ 2 ^ 18) := rfl
  obtain ⟨tp, htape, hfrel, hmbv⟩ := front_phasesU hS hTO hg hpowF hrD hrY hrM
    (Lvm.E2T.pubG vk (hdrOf x).cL sig) hnb hn hsbv hh (ec q2.e)
    (TypedV.smallT P20U (Lvm.E2T.pubG vk (hdrOf x).cL sig))
    (fun h => by rw [hsmE] at h; exact of_decide_eq_true h) hFr
  rw [hfr] at hfrel hmbv
  -- the shape: `σ` from `n' − 1`'s bits 18, 19, the `K` cell `sK`
  have hσ := Lvm.Har.sigma_val o.mb _ hmbv hn.1 hn.2
  rw [← hsmE] at hσ
  have hsK : sK.val (memT TiU20 x qm qr) =
      if TypedV.smallT P20U (Lvm.E2T.pubG vk (hdrOf x).cL sig) then 1 else 0 := by
    rw [← hsKe, mulAdd_spec hSK.1, ← hka, ← hkb, Lvm.Har.addK_val hKA.1, Lvm.Har.addK_val hKB.1, hzkv, ofK_one,
      add_zero, ← hσ]
    ring
  -- the opening's context, the pin as `FRel`
  have hF : Lvm.Q2.FCtxOk (memT TiU20 x qm qr)
      ⟨ec q2.e, ec (q2.e + 1), kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc (q2.k + 1), kc q2.k⟩, true⟩ := by
    refine ⟨hzv, hov, hzkv, rfl, rfl, ?_, ⟨rfl, rfl⟩, ?_⟩
    · show (⟨((kc (q2.k + 1)).val (memT TiU20 x qm qr)).c₀, ((kc q2.k).val (memT TiU20 x qm qr)).c₀⟩ : FE2) = 1
      rw [hokv, hzkv]; rfl
    · show (⟨((kc q2.k).val (memT TiU20 x qm qr)).c₀, ((kc q2.k).val (memT TiU20 x qm qr)).c₀⟩ : FE2) = 0
      rw [hzkv]; rfl
  have hzl : zP.length = 23 := by
    rw [hzL]; simp
  have hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (Lvm.Q2.pinPt pin) := by rw [hzP]; rfl
  have hpinR : Lvm.Q2.FRel (memT TiU20 x qm qr) CMain.nu20 (.e3 pin)
      (BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memT TiU20 x qm qr) zP) (aP.val (memT TiU20 x qm qr))) := by
    refine ⟨?_, ?_⟩
    · rw [hzP]; simp [Lvm.Har.WF1, hzl]
    · rw [hzP, cclaim_point]
  -- the claims: the typed phases' (25d), then the front's
  have hz2 : (⟨kc q2.k, kc q2.k⟩ : C2).val (memT TiU20 x qm qr) = 0 := by
    show (⟨((kc q2.k).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 0; rw [hzkv]; rfl
  have ho2 : (⟨kc (q2.k + 1), kc q2.k⟩ : C2).val (memT TiU20 x qm qr) = 1 := by
    show (⟨((kc (q2.k + 1)).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 1; rw [hokv, hzkv]; rfl
  have htrel := typed_relT (c := ctxOf TiU20.Q) (M := memT TiU20 x qm qr) (zc := ec q2.e)
    (b := TypedV.smallT P20U (Lvm.E2T.pubG vk (hdrOf x).cL sig)) (N := NTU20) (p := P20U)
    (m := Lvm.E2T.m3G NTU20 P20U) (pub := Lvm.E2T.pubG vk (hdrOf x).cL sig) (T := tdataU20)
    (sOff := (layout0 cfgU20.p).s) (t := t) (z := ec q2.e) hzv hz2 ⟨rfl, rfl⟩ ho2 ⟨rfl, rfl⟩ htd hTR rfl rfl rfl
    hry hryK hrr hrrK hvR hrvK htabl
    (st := Lvm.M3.sumcheckTabs NTU20.mbT) (by rw [show NTU20.mbT = NTU20.toN.mbT from rfl, hsc]; exact hSs)
    (m3G_tableClaimsT _ _ _ _) _ hTC.1
  beta_reduce at htrel
  rw [htc, m3G_tableClaimsT] at htrel
  have hrel := List.rel_append htrel hfrel
  beta_reduce at hrel
  -- the opening's static inputs
  have hopenU : posOf P20U (phaseItem0 P20U .openMain) =
      8 * (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).U := by
    rw [cfgMainF_U]; exact hOU
  have hlayO : Lvm.Har.LayOk (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)) (streamLanes P20U) =
      true := by
    rw [layOkF_pb P20U _ _ (fun _ => 0) (fun _ => 0)]; exact hLY
  have hposO : Lvm.Har.PosOk (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)) (memT TiU20 x qm qr)
      sig 0 (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).levels
      ((cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).U + 15) := by
    have hPL' : Lvm.Fin.PosLanes P20U (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).g
        (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).ood
        (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).levels
        ((cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).U + 15) 0 := by
      rw [cfgMainF_g, cfgMainF_ood, cfgMainF_levels, cfgMainF_U]; exact hPL
    rw [← hsig]
    exact posOk_ofG P20U cfgU20 rfl _ 0 (fun i => by rw [Nat.zero_add, cfgMainF_pb]) hPL' streamOk_P20U hLL hQU20
      (posCellsU S H hok hb hG)
  have hpwO : Lvm.Har.PwOk (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)) (memT TiU20 x qm qr) 0
      (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).levels := by
    intro i hi _
    rw [cfgMainF_levels] at hi
    rw [cfgMainF_pw, cfgMainF_g, Nat.zero_add]
    exact pw_onC hon hGR i (lt_of_lt_of_le hi hML)
  have hendO : 8 * Lvm.Har.stackEndL (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).g
      (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).ood
      (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).levels
      ((cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)).U + 15) = sig.size := by
    rw [← hsig, sigU_size hLL, stackEnd_cfgMainF]; exact hSE
  have hq7 : 1 ≤ q7.e := by
    have h3 : 1 ≤ q3.e := le_trans (by simp) hq3e
    omega
  rw [show cfgU20.p = P20U from rfl] at hOpen
  -- `core_of_phasesU` (25g), the opening by `open_phase` (25f)
  have em : Lvm.E2T.dTypedTG P20 NTU20 (Lvm.E2T.m3G NTU20 P20U) (Lvm.E2T.pubG vk (hdrOf x).cL sig)
      (Lvm.E2T.typedItemsND NTU20 P20U) = Lvm.E2T.dTypedTG P20 NTU20 (NTU20.toN.m3 P20)
      (Lvm.E2T.pubG vk (hdrOf x).cL sig) (Lvm.E2T.typedItemsND NTU20 P20U) := by
    unfold Lvm.E2T.dTypedTG
    rw [Lvm.Har.dMiniT_congrU P20 P20 (Lvm.E2T.m3G NTU20 P20U) (NTU20.toN.m3 P20) NTU20.mbT _ rfl rfl rfl rfl rfl]
  rw [← em] at htyped
  refine Lvm.Har.decideFUG_of P20U P20 NTU20 vk (hdrOf x).cL sig ?_ (phiU20_acc S hlin H hG.1 hin.pub)
  refine Lvm.Har.core_of_phasesU P20U P20 NTU20 vk (hdrOf x).cL sig hbU hpin htyped htape ?_
  intro s hs hsok
  rw [List.flatMap_append, List.flatMap_append, Lvm.E2T.typedItemsND_flat, Lvm.E2T.tabItemsR_flat]
  have key := Lvm.Q2.open_phase P20U (cfgMainF P20U (Lvm.Har.posBase cfgU20) (Lvm.Har.pwBase cfgU20)) rfl rfl rfl
    rfl rfl hF pin hpt _ _ hpinR _ _ _ hrel o.mb hσ sK (kc (pbB cfgU20)) hsK hS hlayO
    (by rw [Cell.val_K, hg, ofK_one]) rfl hposO hpwO hendO hq7 hOpen s (hs.trans hopenU) hsok
  rw [hnu] at key
  exact key

/-- **UTAPE-STMT 26** (owner C, with L for the `KS` bridge, STMT 12–14): **`NodeSound` at S2GU** (`nodeG20`'s twin:
`nodeSoundC` at `cfgU20` with the `KS` facts from the merged tape's sponge half on the `Y` block and the stream
block). -/
theorem nodeU20 (S : SFU20) (H : THypT TiU20) (vk : RecursionFast.Digest) :
    NodeSound (VSUX NTU20) vk (fun x qm qr ↦ GoodTU TiU20 H x qm qr ∧ SBlkU qm qr) (childSP P20U) := by
  have hone : (NTU20.toN.instL Pub.hdrLanesT QU20 layU20).src? layU20.one = some .one := H.ok.2
  have hW : ∀ {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}, GoodTU TiU20 H x qm qr →
      WiringRelX QU20 layU20 (zTX (NTU20.toN.instL Pub.hdrLanesT QU20 layU20) Lvm.VEq.pubXT x qm qr) :=
    fun hG ↦ (wiringRelT_iff QU20 layU20 S.1.st.hlay _).mp hG.1.1.1.1
  have hB : spongeBlocks P20U ≤ 2 ^ 13 := by rw [sizes_P20U.1.2.2.2.2.1]; norm_num
  have hn : 615 ≤ pubLanesT := by decide
  exact nodeSoundCU (VSUX NTU20) (decideFUX NTU20) (fun _ _ _ ↦ rfl) pubLanesT Lvm.VEq.pubXT vk
    TiU20 qaU20 _ QU20_eq S.1.st.inj (fun _ _ _ _ _ hG ↦ ⟨hG.1.2, hG.1.1.1.2, hG.2⟩)
    (fun _ _ _ _ _ _ hG ↦ hholdsCU S.1 Pub.hdrLanesT Lvm.VEq.pubXT hone (hW hG.1) H.hτ H.layOk
      hG.1.1.1.1.2 hG.2)
    (fun _ _ _ _ hok hb hG ↦ hmapCU S.1 Pub.hdrLanesT Lvm.VEq.pubXT hB hn (fun x _ hj ↦ pubXT_lane x hj) hok hb
      hG.2)
    (fun _ _ _ _ _ _ _ ↦ hqltCU S.1 Lvm.VEq.pubXT _ rfl)
    (fun _ _ _ _ hok hb hG ↦ hposCU S.1 Pub.hdrLanesT Lvm.VEq.pubXT hB hn (fun x _ hj ↦ pubXT_lane x hj) hone
      (hW hG.1) hok hb hG.2)
    (fun _ _ _ _ _ _ hG ↦ hbitsCU S.1 Pub.hdrLanesT Lvm.VEq.pubXT hone (hW hG.1))
    (harithU20 S.1 S.2.1 S.2.2.2 H vk)

end Lvm.E2Q
