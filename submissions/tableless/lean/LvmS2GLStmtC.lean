-- New for lvm2 MB-LIN (MBL-C, 2026-11-16): DAY-0 STATEMENTS of the S2GL circuit (MBL-STMT 7: the instance of blob L,
-- the guard `staticOkBL20`, `mbLinG_sound`, `harithL20`, `nodeL20`). Every `sorry` is a day-0 statement tagged
-- `-- MBL-STMT 7<x>`; a proof never changes its statement (changes go to the lead, old → new).
import LvmE2QInstL
import LvmS2GLStmtV
import LvmS2GLLin
import LvmS2GUStmt
import LvmE2QTypedLSem
import LvmS2GLHar
import LvmS2GLMid

/-!
# The circuit at S2GL (day-0 statements; owner C)

* Instance of blob L (`LvmE2QInstL`): `cfgL20`, `frzL20`, `tdataL20`, `qaL20`, `QL20`, `powL20`, `layL20`,
  `cacheL20`, `staticOkTL20`; here `NTL20`, `TiL20`, `harChkBL20`, `NodeGL`, **`staticOkBL20`**, `SFL20`.
* Statements: `sfL20` (7a), `harChkL20_sound` (7b), **`mbLinG_sound`** (7c: the gadget's three claims are V_S's
  `mbClaimsN`), `miniL20` (7d), **`harithL20`** (7e: Q_arith is V_S's decision at S2GL), **`nodeL20`** (7f; MBL-L's `phNodeL20` text).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped LeanVM.Protocol
open Lvm.E2T (TNatT PhiQGC)
open Lvm.E2U (SBlkU)
open Lvm.E2L (VSLX decideFLX THypL GoodTL)

/-! ## The instance of blob L -/

/-- **V_S's typed record at S2GL** (`phiT`: the fast `Φ_Q` at `E2`). -/
def NTL20 : TNatT := ⟨Lvm.QTyped.nregsOf layL20 frzL20, PhiQGC cacheL20, Lvm.QTyped.mbTOf cfgL20 frzL20⟩

/-- **The typed instance at S2GL.** -/
noncomputable def TiL20 : TInst := NTL20.inst QL20 layL20

/-- **The HAR's static checks at S2GL** (`harChkBU20` at the S2GL instance; the typed phases end after the mini-bus's
GKR, `typedEndL`). `mbLinB` is a conjunct of `staticOkBL20` itself. -/
def harChkBL20 : Bool :=
  Lvm.QTyped.tdMatchB tdataL20 NTL20.toN &&
    typedEndL tdataL20 P20L == posOf P20L (phaseItem0 P20L .tape) &&
    decide (typedEndL tdataL20 P20L + 40 ≤ 8 * streamLanes P20L) &&
    decide (posOf P20L (phaseItem0 P20L .openMain) + 48 ≤ 8 * streamLanes P20L) &&
    powL20.all (fun a => decide (a.1 + 2 < streamLanes P20L) && decide (a.2 ≤ 64)) &&
    posOf P20L (phaseItem0 P20L .openMain) == 8 * (phaseLane P20L .openMain 0 - 5) &&
    Lvm.Har.LayOk (cfgMainF P20L (fun _ => 0) (fun _ => 0)) (streamLanes P20L) &&
    8 * Lvm.Har.stackEndL P20L.grind P20L.mainOod P20L.mainLevels (phaseLane P20L .openMain 0 - 5 + 15) ==
      hashedLen P20L &&
    decide (P20L.mainLevels.length ≤ (Lvm.QLink.opens P20L).length) && decide (1 ≤ 64 - P20L.grind) &&
    decide (Lvm.Fin.PosLanes P20L P20L.grind P20L.mainOod P20L.mainLevels (phaseLane P20L .openMain 0 - 5 + 15) 0) &&
    typedRegB tdataL20 (layout0 P20L).s

/-- **The S2GL guard's circuit facts** (`NodeGC` at `cfgL20`). -/
abbrev NodeGL : Prop := NodeGCL cfgL20 (spongeBlocks P20L) pubLanesT frzL20 QL20 layL20 NTL20.toN

/-- **The S2GL guard** (S2GU's conjuncts at the S2GL instance, and `mbLinB` of the mini-bus's tables). -/
def staticOkBL20 : Bool :=
  staticOkTL20 && Lvm.QTyped.nodeChkBGL (spongeBlocks P20L) pubLanesT cfgL20 frzL20 QL20 layL20 NTL20.toN &&
    Lvm.TypedV.sigInSBL (layout0 P20L).s NTL20.toN && harChkBL20 && Lvm.T.oneOkB layL20 &&
    Lvm.Typed.KT.linOkX cacheL20 && Lvm.M3.mbLinB NTL20.mbT

/-- **The S2GL guard's facts** (S2GU's, and the mini-bus MB-LIN: `THypL.lin`). -/
abbrev SFL20 : Prop :=
  NodeGL ∧ harChkBL20 = true ∧ Lvm.T.oneOkB layL20 = true ∧ Lvm.Typed.KT.linOkX cacheL20 = true ∧
    Lvm.M3.mbLinB NTL20.mbT = true

/-- **MBL-STMT 7a** (owner C): the guard's facts from `staticOkBL20 = true` (`sfU20`'s twin). -/
theorem sfL20 (h : staticOkBL20 = true) : SFL20 := by
  simp only [staticOkBL20, Bool.and_eq_true] at h
  exact ⟨nodeGCL_of QL20_eq rfl rfl rfl h.1.1.1.1.1.1 h.1.1.1.1.1.2 h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **MBL-STMT 7b** (owner C): **the facts `harChkBL20` decides** (`harChkU20_sound`'s twin). -/
theorem harChkL20_sound (h : harChkBL20 = true) :
    Lvm.Har.TdOk tdataL20 NTL20.toN ∧
      typedEndL tdataL20 P20L = posOf P20L (phaseItem0 P20L .tape) ∧
      typedEndL tdataL20 P20L + 40 ≤ 8 * streamLanes P20L ∧
      posOf P20L (phaseItem0 P20L .openMain) + 48 ≤ 8 * streamLanes P20L ∧
      (∀ a ∈ powL20, a.1 + 2 < streamLanes P20L ∧ a.2 ≤ 64) ∧
      posOf P20L (phaseItem0 P20L .openMain) = 8 * (phaseLane P20L .openMain 0 - 5) ∧
      Lvm.Har.LayOk (cfgMainF P20L (fun _ => 0) (fun _ => 0)) (streamLanes P20L) = true ∧
      8 * Lvm.Har.stackEndL P20L.grind P20L.mainOod P20L.mainLevels (phaseLane P20L .openMain 0 - 5 + 15) =
        hashedLen P20L ∧
      P20L.mainLevels.length ≤ (Lvm.QLink.opens P20L).length ∧ 1 ≤ 64 - P20L.grind ∧
      Lvm.Fin.PosLanes P20L P20L.grind P20L.mainOod P20L.mainLevels (phaseLane P20L .openMain 0 - 5 + 15) 0 ∧
      typedRegB tdataL20 (layout0 P20L).s = true := by
  simp only [harChkBL20, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨Lvm.Har.tdOk_of h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- **MBL-STMT 7c** (owner C; RE-FREEZE R3 adds `hslot`, `hcnt`, `hfx`): **`mbLinG`'s three claims are V_S's**
(`mbClaimsN` on the native bus decomposition at the GKR's outputs): on MB-LIN tables whose shapes the circuit holds,
with every fixed column's closed form listed, every key slot inside the eq table, the reads' counts committed and
every listed fixed column exact. Proof: `mbLinG_sound'` (`LvmE2QTypedLSem`). -/
theorem mbLinG_sound {c : Ctx} {M : Mem} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E)
    (hoE : o.ty = .E) (tabs : List Lvm.M3.Tab) (T : TData) (hsc : Lvm.M3.sumcheckTabs tabs = tabs)
    (hS : T.mbS = tabs.map Lvm.M3.Tab.shape) (hfix : Lvm.Har.FixListed tabs T.mbFix)
    (hlin : Lvm.M3.mbLinB tabs = true) (bc : Lvm.Har.BusC) (i : Lvm.BusIn) (hal : Lvm.Har.vs M bc.al = i.alphas)
    (hbe : bc.be.val M = i.beta) (hpt : Lvm.Har.vs M bc.pt = i.point) (hvals : Lvm.Har.vs M bc.vals = i.values)
    (hal2 : 2 ≤ i.alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E) (hptE : ∀ x ∈ bc.pt, x.ty = .E)
    (hbeE : bc.be.ty = .E) (hvE : ∀ x ∈ bc.vals, x.ty = .E)
    (hslot : ∀ t ∈ tabs, ∀ k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1), 3 + k.val.length ≤ 2 ^ i.alphas.length)
    (hcnt : ∀ t ∈ tabs, ∀ r ∈ t.reads, ∀ f e, t.cols[r.2]? ≠ some (Lvm.M3.ColSrc.fix f e))
    (hfx : ∀ f ∈ T.mbFix, ∃ t fn e, tabs[f.1]? = some t ∧ t.cols[f.2.1]? = some (Lvm.M3.ColSrc.fix fn e) ∧
      ∀ r, e r = FE.ofK (FK.x ^ f.2.2.1) * powEval r (FK.x ^ f.2.2.2)) :
    Lvm.Har.SoundG c M (mbLinG z o T bc) fun cs =>
      cs.map (Lvm.Har.CClaim.val M) = (Lvm.M3.mbClaimsN CMain.nu20 tabs i).map fun b => (Com.main, b) :=
  mbLinG_sound' hz ho hzE hoE tabs T hsc hS hfix hlin bc i hal hbe hpt hvals hal2 halE hptE hslot hcnt hfx

set_option maxRecDepth 100000 in
/-- **MBL-STMT 7d** (owner C): the mini-bus record at S2GL (`miniU20`'s twin; no table rounds). -/
theorem miniL20 (S : NodeGL) : Lvm.M3.sumcheckTabs NTL20.toN.mbT = NTL20.toN.mbT ∧
    (Lvm.QTyped.tdataOf cfgL20 frzL20).mbS = NTL20.toN.mbT.map Lvm.M3.Tab.shape ∧
    (Lvm.QTyped.tdataOf cfgL20 frzL20).mbD = cfgL20.p.busDepth ∧
    Lvm.Har.FixListed NTL20.toN.mbT (Lvm.QTyped.tdataOf cfgL20 frzL20).mbFix := by
  have hsc : Lvm.M3.sumcheckTabs (mbTOf cfgL20 frzL20) = mbTOf cfgL20 frzL20 := Lvm.Har.mbT_sumcheck cfgL20 _ _ _
  have hm := S.st.mini
  rw [S.mb] at hm ⊢
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hD⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hm
  obtain ⟨t1, -, t3, t4⟩ := Lvm.Har.tdataOf_mb cfgL20 frzL20
  rw [t1, t3, t4, hD]
  exact ⟨hsc, rfl, rfl, Lvm.Har.mbT_fix cfgL20 _ _ _⟩

/-! ## Q_arith's inputs at S2GL (`harithU20`'s, at `cfgL20`) -/

section PairLH

variable {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}

/-- The trace bytes of the child at S2GL have `hashedLen P20L` bytes. -/
theorem sigL_size (hL : LaneLink P20L (wsC qr)) : (traceBytesB (decode P20L (wsC qr))).size = hashedLen P20L := by
  rw [traceBytesB_decode streamOk_P20L hL, Lvm.Har.sigma_sizeT hL.size]

/-- **The node memory streams the child's trace at S2GL** (`streamed_child` at `cfgL20`). -/
theorem streamedL {M : Mem} (hst : ∀ j < 2 ^ (lay cfgL20).m, M.k ((lay cfgL20).sb + j) = laneK (wsC qr) j)
    (hL : LaneLink P20L (wsC qr)) : Lvm.Q1.Streamed M (traceBytesB (decode P20L (wsC qr))) (streamLanes P20L) := by
  have hh : hashedLen P20L = 522528 := sizes_P20L.1.2.2.1
  have hw : (wsC qr).length = 17 * 2 ^ 14 := by rw [wsC, wsOf, List.length_map, List.length_range]
  exact Lvm.Har.streamed_child cfgL20 streamOk_P20L hL hst (T := streamLanes P20L)
    (by rw [streamLanes, hh]; decide) (by rw [show cfgL20.p = P20L from rfl, streamLanes]; omega)
    (by rw [streamLanes, hh, hw]; norm_num)

theorem hWL (S : NodeGL) (H : THypL TiL20) (hG : GoodTL TiL20 H x qm qr) :
    WiringRelX QL20 layL20 (zTX (NTL20.toN.instL Pub.hdrLanesT QL20 layL20) Lvm.VEq.pubXT x qm qr) :=
  (wiringRelT_iff QL20 layL20 S.st.hlay _).mp hG.1.1.1.1

/-- **The three row switches' words at S2GL** (the `rowAux` blocks of `specQU` on `tBu cfgL20 i`). -/
theorem rowWordsL (S : NodeGL) (H : THypL TiL20) (hG : GoodTL TiL20 H x qm qr) :
    (∀ j < 128, (memT TiL20 x qm qr).k (tBu cfgL20 0 + j) =
      rowWordD (Lvm.Q2.slicesOf (memT TiL20 x qm qr) (wlUG P20L).slicesD) j) ∧
    (∀ j < 128, (memT TiL20 x qm qr).k (tBu cfgL20 1 + j) =
      rowWordD (Lvm.Q2.slicesOf (memT TiL20 x qm qr) (wlUG P20L).slicesY) j) ∧
    (∀ j < 128, (memT TiL20 x qm qr).k (tBu cfgL20 2 + j) =
      rowWordD (Lvm.Q2.slicesOf (memT TiL20 x qm qr) (wlUG P20L).slicesM) j) := by
  obtain ⟨f, hf⟩ := Lvm.QTyped.aux_mkLayD QL20 (specQU cfgL20 QL20 powL20) dintsL20
  have hmem : ∀ B, B ∈ Lvm.Q2.rowAuxL (f (specQ cfgL20 QL20).auxWords.length) (tBu cfgL20 0) (wlUG P20L).slicesD ++
      Lvm.Q2.rowAuxL (f ((specQ cfgL20 QL20).auxWords.length + 1)) (tBu cfgL20 1) (wlUG P20L).slicesY ++
      Lvm.Q2.rowAuxL (f ((specQ cfgL20 QL20).auxWords.length + 2)) (tBu cfgL20 2) (wlUG P20L).slicesM →
      B ∈ layL20.aux := fun B hB => by
    show B ∈ (mkLayD QL20 (specQU cfgL20 QL20 powL20) dintsL20).1.aux
    rw [hf]
    show B ∈ (specQ cfgL20 QL20).auxOf f ++ _ ++ _
    exact List.mem_append_left _ (List.mem_append_right _ hB)
  have hone := zOf_one (NTL20.toN.instL Pub.hdrLanesT QL20 layL20) H.ok.2 Lvm.M3.lay26 (Lvm.VEq.pubXT x) qm qr
  exact ⟨fun j hj => rowWords_of_aux S.st.hlay hone (hWL S H hG)
      (fun B hB => hmem B (List.mem_append_left _ (List.mem_append_left _ hB))) hj,
    fun j hj => rowWords_of_aux S.st.hlay hone (hWL S H hG)
      (fun B hB => hmem B (List.mem_append_left _ (List.mem_append_right _ hB))) hj,
    fun j hj => rowWords_of_aux S.st.hlay hone (hWL S H hG) (fun B hB => hmem B (List.mem_append_right _ hB)) hj⟩

/-- **V's proof-of-work checks at S2GL** (`powOk_of_blksU` at `cfgL20`). -/
theorem powOkL (S : NodeGL) (H : THypL TiL20) (hG : GoodTL TiL20 H x qm qr) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memT TiL20 x qm qr) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ powL20)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L :=
  powOk_of_blksU cfgL20 (Q := QL20) (tl := layL20) (d := dintsL20) rfl S.st.hlay
    (zOf_one (NTL20.toN.instL Pub.hdrLanesT QL20 layL20) H.ok.2 Lvm.M3.lay26 (Lvm.VEq.pubXT x) qm qr) (hWL S H hG)
    hS hL hpw

/-- **Q_sig's `ChildOk` at S2GL** (`childOkU`'s twin: the `KS` facts from the merged tape at `bL`). -/
theorem childOkL (S : NodeGL) (H : THypL TiL20) {vk c : RecursionFast.Digest} (hok : okS vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTL TiL20 H x qm qr ∧ SBlkU qm qr) :
    ChildOk (sigIn cfgL20) (memT TiL20 x qm qr).k := by
  have hone : (NTL20.toN.instL Pub.hdrLanesT QL20 layL20).src? layL20.one = some .one := H.ok.2
  obtain ⟨hH, hA⟩ := hholdsCB S Pub.hdrLanesT Lvm.VEq.pubXT cfgU_L20 hone (hWL S H hG.1) H.hτ H.layOk
    hG.1.1.1.1.2 hG.2
  have hH' : QL20.Holds (memT TiL20 x qm qr) := hH
  have hA' : QL20.Asserts (memT TiL20 x qm qr) := hA
  rw [QL20_eq] at hH' hA'
  have P := parts_of_holdsP hH' hA'
  have hB : spongeBlocks P20L ≤ 2 ^ 13 := by rw [sizes_P20L.1.2.2.2.2.1]; norm_num
  have mp := hmapCB S Pub.hdrLanesT Lvm.VEq.pubXT cfgU_L20 nodeStL20 hB (by decide) (fun x _ hj ↦ pubXT_lane x hj)
    hok hb hG.2
  have hks := Lvm.E2L.sigKSin_of_GkL hG.1.2 mp.xs mp.ys mp.yc mp.yls mp.yns
  exact (qsig_sound_in (by rw [show (sigIn cfgL20).ln = 20 from rfl]; omega) P.2.1 mp.flag hks
    (hbitsCB S Pub.hdrLanesT Lvm.VEq.pubXT nodeStL20 hone (hWL S H hG.1))
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h).2

/-- **Q_link's position cells at S2GL** (`posCellsU`'s twin). -/
theorem posCellsL (S : NodeGL) (H : THypL TiL20) {vk c : RecursionFast.Digest} (hok : okS vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTL TiL20 H x qm qr ∧ SBlkU qm qr) :
    ∀ k < (opens P20L).length, ((opens P20L).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20L).getD k default).L.t,
      (memT TiL20 x qm qr).k (nK cfgL20 + posIdx P20L k j) =
        kOf (posL P20L (wsC qr) (((opens P20L).getD k default).pe + j / 8)
          (j % 8 * ((opens P20L).getD k default).L.height) ((opens P20L).getD k default).L.height) := by
  intro k hk hH j hj
  have hone : (NTL20.toN.instL Pub.hdrLanesT QL20 layL20).src? layL20.one = some .one := H.ok.2
  obtain ⟨hH', hA⟩ := hholdsCB S Pub.hdrLanesT Lvm.VEq.pubXT cfgU_L20 hone (hWL S H hG.1) H.hτ H.layOk
    hG.1.1.1.1.2 hG.2
  have hH'' : QL20.Holds (memT TiL20 x qm qr) := hH'
  have hA' : QL20.Asserts (memT TiL20 x qm qr) := hA
  rw [QL20_eq] at hH'' hA'
  have P := parts_of_holdsP hH'' hA'
  have hB : spongeBlocks P20L ≤ 2 ^ 13 := by rw [sizes_P20L.1.2.2.2.2.1]; norm_num
  have mp := hmapCB S Pub.hdrLanesT Lvm.VEq.pubXT cfgU_L20 nodeStL20 hB (by decide) (fun x _ hj ↦ pubXT_lane x hj)
    hok hb hG.2
  have hp : cfgL20.p = P20L := rfl
  have hk' : k < (opens cfgL20.p).length := by rw [hp]; exact hk
  have hH2 : ((opens cfgL20.p).getD k default).L.height ≤ 64 := by rw [hp]; exact hH
  have hj' : j < ((opens cfgL20.p).getD k default).L.t := by rw [hp]; exact hj
  have hv := posVal_onC (C := cfgL20) (outsOnCB S Pub.hdrLanesT Lvm.VEq.pubXT hone (hWL S H hG.1))
    (by rw [hp]; exact streamOk_P20L) (by rw [hp]; exact hQL20) mp.stream hk' hH2 hj'
  rw [hp] at hv
  have hq := qlink_pos (pt := p0 (nK cfgL20) 0) hQL20 P.1.1 hk hj
  exact hq.trans hv

/-- The current proof's `vk` cells at S2GL (`vk_cellsU` at `cfgL20`). -/
theorem vk_cellsL {M : Mem} {vk : RecursionFast.Digest}
    (hpub : ∀ j < pubLanesT, M.k ((sigIn cfgL20).flag + j) = hdrLane x j) (hvk : (hdrOf x).vk = vk) :
    ∀ i < 4, M.k (pbB cfgL20 + 1 + i) = (digestLanes vk).getD i 0 := by
  intro i hi
  have hj : 1 + i < pubLanes := by rw [pubLanes_eq]; omega
  have e1 : M.k (pbB cfgL20 + 1 + i) = (Lvm.NS.hdrLanes x).getD (1 + i) 0 := by
    rw [Nat.add_assoc, show pbB cfgL20 = (sigIn cfgL20).flag from rfl, hpub _ (by unfold pubLanesT; omega),
      Lvm.NS.hdrLanes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some]
  have hv : (Lvm.VEq.pubX x).vk = digestLanes vk := by rw [← hvk]; rfl
  have hl : i < (digestLanes vk).length := by simp only [digestLanes, List.length_map, List.length_range]; omega
  rw [e1, Lvm.NS.hdrLanes_eq_pubX, Pub.hdrLanes, hv]
  simp only [List.append_assoc, List.singleton_append]
  rw [Nat.add_comm, List.getD_append _ _ _ _ (by rw [List.length_cons]; omega), List.getD_cons_succ]

/-- **`Φ_Q` at `E2` holds at the folded accumulator at S2GL** (`phiU20_acc`'s twin). -/
theorem phiL20_acc (S : NodeGL) (hlin : Lvm.Typed.KT.linOkX cacheL20 = true) (H : THypL TiL20)
    (hG : GoodTL TiL20 H x qm qr) {M : Mem} (hpub : ∀ j < pubLanesT, M.k ((sigIn cfgL20).flag + j) = hdrLane x j) :
    NTL20.phiT ((accCT M (pbB cfgL20)).pt.map Lvm.e2OfFE) = Lvm.e2OfFE (accCT M (pbB cfgL20)).y := by
  have hacc : Lvm.E2T.AccOkTT TiL20 (Lvm.VEq.pubXT x) := hG.1.2
  have hl : ∀ j < 46, (Lvm.Q2.ld2 (pbB cfgL20 + 615 + 2 * j)).val M =
      Lvm.e2OfFE (fe16At (Lvm.VEq.sigOfX x) (headerAt (offAcc + 16 * j))) := by
    intro j hj
    have hpb : (sigIn cfgL20).flag = pbB cfgL20 := rfl
    have e1 := hpub (615 + 2 * j) (by show 615 + 2 * j < 615 + 2 * (45 + 1); omega)
    have e2 := hpub (615 + 2 * j + 1) (by show 615 + 2 * j + 1 < 615 + 2 * (45 + 1); omega)
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (615 + 2 * j) = headerAt (offAcc + 16 * j) by
      simp only [headerAt, offAcc, sigBytes]; omega] at e1
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (615 + 2 * j + 1) = headerAt (offAcc + 16 * j) + 8 by
      simp only [headerAt, offAcc, sigBytes]; omega] at e2
    show (⟨(FE.ofK (M.k (pbB cfgL20 + 615 + 2 * j))).c₀, (FE.ofK (M.k (pbB cfgL20 + 615 + 2 * j + 1))).c₀⟩ : FE2) = _
    rw [Nat.add_assoc (pbB cfgL20), e1, Nat.add_assoc (pbB cfgL20) (615 + 2 * j), e2]
    rfl
  have hpt : (accCT M (pbB cfgL20)).pt.map Lvm.e2OfFE = (Lvm.VEq.pubXT x).accIn.pt.map Lvm.e2OfFE := by
    simp only [accCT, Lvm.VEq.pubXT, pubOfW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 45 := List.mem_range.mp hj
    exact hl j (by omega)
  have hy : Lvm.e2OfFE (accCT M (pbB cfgL20)).y = Lvm.e2OfFE (Lvm.VEq.pubXT x).accIn.y := by
    simp only [accCT, Lvm.VEq.pubXT, pubOfW]
    exact hl Lvm.VEq.accVT (by decide)
  rw [hpt, hy]
  have hc : cacheL20 = Lvm.Typed.cacheWX QL20 layL20 := cacheWXF_eq QL20 layL20 S.st.hlay
  show Lvm.E2T.PhiQGC cacheL20 _ = _
  rw [hc, Lvm.E2T.PhiQGC, Lvm.Typed.KT.PhiQGC_eqW QL20 layL20 S.st.hlay S.st.cache (hc ▸ hlin) _
    (by rw [List.length_map]; exact H.acc x)]
  have hpt' : Lvm.E2T.accPtT (Lvm.VEq.pubXT x) = ((Lvm.VEq.pubXT x).accIn.pt.map Lvm.e2OfFE).map FE2.toE2 := by
    rw [Lvm.E2T.accPtT, List.map_map]; rfl
  have hy' : Lvm.E2T.accYT (Lvm.VEq.pubXT x) = FE2.toE2 (Lvm.e2OfFE (Lvm.VEq.pubXT x).accIn.y) := rfl
  have hof : ∀ z : FE2, Lvm.Typed.ofE2 (FE2.toE2 z) = z := fun _ => rfl
  rw [Lvm.E2T.AccOkTT, Lvm.Typed.PhiQT, hpt', hy', List.map_map] at hacc
  simp only [Function.comp_def, hof, List.map_id'] at hacc
  exact FE2.toE2_injective hacc

end PairLH

/-- The mini-bus's table rounds at S2GL lie within the bus's point (`T.mbR = 6 ≤ 12`, `mbLinG_ok`'s `hpt`). -/
theorem mbR_leL20 (S : NodeGL) : tdataL20.mbR ≤ P20L.busDepth := by
  have hsc : Lvm.M3.sumcheckTabs (mbTOf cfgL20 frzL20) = mbTOf cfgL20 frzL20 := Lvm.Har.mbT_sumcheck cfgL20 _ _ _
  have hm := S.st.mini
  rw [S.mb] at hm
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hR⟩, -⟩, -⟩, -⟩, -⟩ := hm
  rw [hsc] at hR
  obtain ⟨-, t2, -, -⟩ := Lvm.Har.tdataOf_mb cfgL20 frzL20
  show (Lvm.QTyped.tdataOf cfgL20 frzL20).mbR ≤ _
  rw [t2, ← hR, show cfgL20.p = P20L from rfl, sizes_P20L.2.2.2.2.1, sizes_P20L.2.2.2.2.2.2.1]
  decide

/-- **MBL-STMT 7e** (owner C): **Q_arith is `V_S`'s decision at S2GL** (`harithU20`'s twin: the node program's
segments on a good S2GL pair whose `qr` is `qm`'s stream block). -/
theorem harithL20 (S : NodeGL) (hhar : harChkBL20 = true) (hlin : Lvm.Typed.KT.linOkX cacheL20 = true)
    (H : THypL TiL20) (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 →
      GoodTL TiL20 H x qm qr ∧ SBlkU qm qr →
      InMapMBU (spongeBlocks P20L) pubLanesT (lay cfgL20) (sigIn cfgL20) (memT TiL20 x qm qr) vk x qm qr →
      LaneLink P20L (wsC qr) → LinkOk P20L (decode P20L (wsC qr)) →
      Ok (ctxOf TiL20.Q) (memT TiL20 x qm qr) qaL20 (p2P (lay cfgL20) (sigIn cfgL20) (nK cfgL20) 0 P20L) →
      decideFLX NTL20 vk (hdrOf x).cL (traceBytesB (decode P20L (wsC qr))) = true := by
  intro c x qm qr hok hb hG hin hLL hlink hrun
  obtain ⟨sig, hsig⟩ : ∃ s, traceBytesB (decode P20L (wsC qr)) = s := ⟨_, rfl⟩
  rw [hsig]
  -- the program's three parts after Q_sig: the pin, the front, `qarithL`
  have hrun' : Lvm.QSig.Ok (ctxOf TiL20.Q) (memT TiL20 x qm qr)
      (pinF cfgL20.p >>= fun pin ↦ frontU cfgL20 >>= fun o ↦ qarithL cfgL20 tdataL20 pin o)
      (p2P (lay cfgL20) (sigIn cfgL20) (nK cfgL20) 0 P20L) := hrun
  obtain ⟨hPin, hR⟩ := Lvm.Har.okb hrun'
  obtain ⟨q1, hq1⟩ : ∃ q1, (p2P (lay cfgL20) (sigIn cfgL20) (nK cfgL20) 0 P20L).adv
      (pinF cfgL20.p (p2P (lay cfgL20) (sigIn cfgL20) (nK cfgL20) 0 P20L)).2 = q1 := ⟨_, rfl⟩
  obtain ⟨pin, hpinE⟩ : ∃ pin, (pinF cfgL20.p (p2P (lay cfgL20) (sigIn cfgL20) (nK cfgL20) 0 P20L)).1 = pin :=
    ⟨_, rfl⟩
  rw [hq1, hpinE] at hR
  obtain ⟨hFr, hQa⟩ := Lvm.Har.okb hR
  obtain ⟨o, hfr⟩ : ∃ o, (frontU cfgL20 q1).1 = o := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2, q1.adv (frontU cfgL20 q1).2 = q2 := ⟨_, rfl⟩
  rw [hfr, hq2] at hQa
  -- the static facts, the stream, the gate, `vk`
  obtain ⟨htd, hTE, hTT, hTO, hPW, hOU, hLY, hSE, hML, hGR, hPL, hTR⟩ := harChkL20_sound hhar
  have hS : Lvm.Q1.Streamed (memT TiL20 x qm qr) sig (streamLanes P20L) := hsig ▸ streamedL hin.stream hLL
  have hTl : streamLanes P20L = 65316 := sizes_P20L.1.2.2.2.1
  have hg : (memT TiL20 x qm qr).k (pbB cfgL20) = 1 := hin.flag
  have hvk := vk_cellsL hin.pub (okS_vk hok)
  -- `qarithL`: the constants
  unfold qarithL at hQa
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
  have hzkv : (kc q2.k).val (memT TiL20 x qm qr) = 0 := by
    have e := const_val hZK.1
    rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, ofK_zero] at e
    exact e
  have hokv : (kc (q2.k + 1)).val (memT TiL20 x qm qr) = 1 := by
    have e := const_val hOK.1
    rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, ofK_one] at e
    exact e
  -- the typed phases (`typed_phaseTL` at `P20L`), their claims, the shape cell
  obtain ⟨t, q3, ht, hq3e, hTy, hR⟩ := ok_bindV hR
  obtain ⟨tc, q4, htc, hq4e, hTC, hR⟩ := ok_bindV hR
  obtain ⟨ka, q5, hka, hq5e, hKA, hR⟩ := ok_bindV hR
  obtain ⟨kb, q6, hkb, hq6e, hKB, hR⟩ := ok_bindV hR
  obtain ⟨sK, q7, hsKe, hq7e, hSK, hOpen⟩ := ok_bindV hR
  obtain ⟨hsc, hSs, hDd, hfix⟩ := miniL20 S
  have hpowA := powOkL S H hG.1 hS (L := powL20) (fun a ha => ha) hPW
  have hpowT : Lvm.Q1.PowOkV (feAt sig) (typedChalsT P20L) := fun a ha =>
    hpowA a (List.mem_append_right _ ha)
  have hpowF : Lvm.Q1.PowOkV (feAt sig) (powFrontU P20L) := fun a ha => hpowA a (List.mem_append_left _ ha)
  have hDL : tdataL20.mbD = P20.busDepth := by
    rw [show tdataL20.mbD = cfgL20.p.busDepth from hDd, show cfgL20.p = P20L from rfl, sizes_P20L.2.2.2.2.1]
    rfl
  have htyped := typed_phaseTL P20L rfl (c := ctxOf TiL20.Q) vk (hdrOf x).cL hS hg hvk (z := ec q2.e)
    (o := ec (q2.e + 1)) (zk := kc q2.k) (ok := kc (q2.k + 1)) rfl rfl hzv hov rfl rfl hzkv hokv htd P20 rfl hDL
    (Lvm.E2T.m3G NTL20 P20L) (busLanes_of busLanesB_P20L) hpowT (by rw [hTl] at hTT ⊢; exact hTT)
    (by rw [hTl]; decide) _ (by simp) hTy (fun _ => rfl) (Lvm.E2T.typedItemsND NTL20 P20L)
  rw [show cfgL20.p = P20L from rfl] at ht
  -- the typed gadget's shape and its three claims (7c at the bus's outputs, `mbLinG_ok`)
  have hpbE : Lvm.E2T.pubG vk (hdrOf x).cL sig = Lvm.E2T.pubG vk (hdrOf x).cL sig := rfl
  have hfxL : tdataL20.mbFix = mbFixOf cfgL20 := (Lvm.Har.tdataOf_mb cfgL20 frzL20).2.2.2
  have hsh := Lvm.Har.soundG_ok (typedGL_shape (c := ctxOf TiL20.Q) (M := memT TiL20 x qm qr) tdataL20 P20L (pbB cfgL20)
    (pubLanesTC P20L) (ec q2.e) (ec (q2.e + 1)) (kc q2.k) (kc (q2.k + 1)) (hDd.trans rfl)
    (fun bc cs => cs.map (Lvm.Har.CClaim.val (memT TiL20 x qm qr)) = (Lvm.M3.mbClaimsN CMain.nu20 NTL20.toN.mbT
      ⟨Lvm.Har.vs (memT TiL20 x qm qr) bc.al, bc.be.val (memT TiL20 x qm qr), bc.cnt.val (memT TiL20 x qm qr),
        Lvm.Har.vs (memT TiL20 x qm qr) bc.pt, Lvm.Har.vs (memT TiL20 x qm qr) bc.vals, [0],
        Lvm.E2T.pubG vk (hdrOf x).cL sig⟩).map (fun b => (Com.main, b)) ∧
      ∀ cc ∈ cs, cOkB (ec q2.e) cc = true ∧ cc.com = .main)
    (fun bc h1 h2 h3 h4 => by
      have hal2 : 2 ≤ (Lvm.Har.vs (memT TiL20 x qm qr) bc.al).length := by
        show 2 ≤ (bc.al.map _).length
        rw [List.length_map, h1]; decide
      have hA := mbLinG_sound' (c := ctxOf TiL20.Q) hzv hov rfl rfl NTL20.toN.mbT tdataL20 hsc hSs hfix H.lin bc
        ⟨Lvm.Har.vs (memT TiL20 x qm qr) bc.al, bc.be.val (memT TiL20 x qm qr), bc.cnt.val (memT TiL20 x qm qr),
          Lvm.Har.vs (memT TiL20 x qm qr) bc.pt, Lvm.Har.vs (memT TiL20 x qm qr) bc.vals, [0],
          Lvm.E2T.pubG vk (hdrOf x).cL sig⟩ rfl rfl rfl rfl hal2 h2 h3
        (by rw [S.mb]; exact mbT_slots cfgL20 frzL20.wordK _ _ hal2)
        (by rw [S.mb]; exact mbT_cnt cfgL20 frzL20.wordK _ _)
        (by rw [S.mb, hfxL]; exact mbFixOf_exact cfgL20 frzL20.wordK _ _)
      have hB := mbLinG_ok (c := ctxOf TiL20.Q) (M := memT TiL20 x qm qr) (zc := ec q2.e) (z := ec q2.e)
        (o := ec (q2.e + 1)) (bc := bc) hTR (by rw [h4]; exact mbR_leL20 S)
      exact fun q hH hA' => ⟨hA q hH hA', hB q hH⟩)) hTy
  rw [ht] at hsh htyped
  obtain ⟨⟨⟨hry, hryK⟩, ⟨hrr, hrrK⟩, hvR, hrvK⟩, htab, hcs, hcok⟩ := hsh
  rw [hTE] at htyped
  have hle : typedPosF P20L ≤ typedEndL tdataL20 P20L := by
    have h1 := mbPT_leL tdataL20 P20L
    have h2 := (busLanes_of busLanesB_P20L).mb
    have h3 : mbPT P20L = 8 * busL P20L iMB - 40 := rfl
    omega
  -- the pin (`pin_phase`)
  have hnu : P20L.nuMain = 23 := rfl
  have hpb := pinHPL
  have hpe := pinEndL
  have hqa := pinQaL
  rw [hnu] at hpe hqa
  have epin : pinF cfgL20.p = Lvm.Q2.pinG 23 (phaseLane P20L .commit 1) (phaseLane P20L .commit (23 + 1)) := rfl
  rw [epin] at hPin hpinE
  obtain ⟨hpin, hpinV⟩ := Lvm.Q2.pin_phase hS (nu := 23) (by norm_num) hpb.symm hqa
    (by rw [hTl] at hTT ⊢; omega) (by rw [hqa]; rw [hTl] at hTT ⊢; omega) hPin.1
  rw [hpe] at hpin
  rw [hpinE] at hpinV
  obtain ⟨zP, aP, hzP, hzL⟩ := pinG_fst 23 (phaseLane P20L .commit 1) (phaseLane P20L .commit (23 + 1))
    (p2P (lay cfgL20) (sigIn cfgL20) (nK cfgL20) 0 P20L)
  rw [hpinE] at hzP
  have hpinB : (Lvm.pinD 23 sig ⟨posOf P20L 1, 0, true⟩).1 =
      BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memT TiL20 x qm qr) zP) (aP.val (memT TiL20 x qm qr)) := by
    rw [hzP, cclaim_point] at hpinV
    exact (Prod.mk.inj hpinV).2.symm
  rw [hpinB] at hpin
  -- the front's inputs and its phases (`front_phasesUG` at `cfgL20`, V_S's intervals `contIvOf 3843`)
  have hT29 : 29 ≤ streamLanes P20L := by rw [hTl]; norm_num
  obtain ⟨hrD, hrY, hrM⟩ := rowWordsL S H hG.1
  have hch := childOkL S H hok hb hG
  have hone : (NTL20.toN.instL Pub.hdrLanesT QL20 layL20).src? layL20.one = some .one := H.ok.2
  have hon := outsOnCB S Pub.hdrLanesT Lvm.VEq.pubXT hone (hWL S H hG.1)
  have hsb := sBits_onC hon
  obtain ⟨hnb, hn, hsbv⟩ := frontIns hS hT29 (hbitsCB S Pub.hdrLanesT Lvm.VEq.pubXT nodeStL20 hone (hWL S H hG.1))
    hch hsb Lvm.VEq.accVT vk (hdrOf x).cL rfl rfl
  have hh : (Lvm.E2T.pubG vk (hdrOf x).cL sig).h =
      (List.range 4).map fun l => (memT TiL20 x qm qr).k (Lvm.Har.hLane l) := Lvm.Har.pub_h hS hT29 vk (hdrOf x).cL
  have hsmE : TypedV.smallT P20L (Lvm.E2T.pubG vk (hdrOf x).cL sig) =
      decide ((Lvm.E2T.pubG vk (hdrOf x).cL sig).n ≤ 2 ^ 18) := rfl
  obtain ⟨tp, htape, hfrel, hmbv⟩ := front_phasesUG (p := P20L) cfgL20 rfl frontPF_P20L (Lvm.E2L.contIvOf 3843) ivsL20 hS hTO hg hpowF hrD hrY hrM
    (Lvm.E2T.pubG vk (hdrOf x).cL sig) hnb hn hsbv hh (ec q2.e)
    (TypedV.smallT P20L (Lvm.E2T.pubG vk (hdrOf x).cL sig))
    (fun h => by rw [hsmE] at h; exact of_decide_eq_true h) hFr
  rw [hfr] at hfrel hmbv
  -- the shape: `σ` from `n' − 1`'s bits 18, 19, the `K` cell `sK`
  have hσ := Lvm.Har.sigma_val o.mb _ hmbv hn.1 hn.2
  rw [← hsmE] at hσ
  have hsK : sK.val (memT TiL20 x qm qr) =
      if TypedV.smallT P20L (Lvm.E2T.pubG vk (hdrOf x).cL sig) then 1 else 0 := by
    rw [← hsKe, mulAdd_spec hSK.1, ← hka, ← hkb, Lvm.Har.addK_val hKA.1, Lvm.Har.addK_val hKB.1, hzkv, ofK_one,
      add_zero, ← hσ]
    ring
  -- the opening's context, the pin as `FRel`
  have hF : Lvm.Q2.FCtxOk (memT TiL20 x qm qr)
      ⟨ec q2.e, ec (q2.e + 1), kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc (q2.k + 1), kc q2.k⟩, true⟩ := by
    refine ⟨hzv, hov, hzkv, rfl, rfl, ?_, ⟨rfl, rfl⟩, ?_⟩
    · show (⟨((kc (q2.k + 1)).val (memT TiL20 x qm qr)).c₀, ((kc q2.k).val (memT TiL20 x qm qr)).c₀⟩ : FE2) = 1
      rw [hokv, hzkv]; rfl
    · show (⟨((kc q2.k).val (memT TiL20 x qm qr)).c₀, ((kc q2.k).val (memT TiL20 x qm qr)).c₀⟩ : FE2) = 0
      rw [hzkv]; rfl
  have hzl : zP.length = 23 := by
    rw [hzL]; simp
  have hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (Lvm.Q2.pinPt pin) := by rw [hzP]; rfl
  have hpinR : Lvm.Q2.FRel (memT TiL20 x qm qr) CMain.nu20 (.e3 pin)
      (BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memT TiL20 x qm qr) zP) (aP.val (memT TiL20 x qm qr))) := by
    refine ⟨?_, ?_⟩
    · rw [hzP]; simp [Lvm.Har.WF1, hzl]
    · rw [hzP, cclaim_point]
  -- the claims: the typed phases' (S2GT's halves, no table claims), the three claims (7c), then the front's
  have hz2 : (⟨kc q2.k, kc q2.k⟩ : C2).val (memT TiL20 x qm qr) = 0 := by
    show (⟨((kc q2.k).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 0; rw [hzkv]; rfl
  have ho2 : (⟨kc (q2.k + 1), kc q2.k⟩ : C2).val (memT TiL20 x qm qr) = 1 := by
    show (⟨((kc (q2.k + 1)).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 1; rw [hokv, hzkv]; rfl
  have hrelT := typed_relT (c := ctxOf TiL20.Q) (M := memT TiL20 x qm qr) (zc := ec q2.e)
    (b := TypedV.smallT P20L (Lvm.E2T.pubG vk (hdrOf x).cL sig)) (N := NTL20) (p := P20L)
    (m := Lvm.E2T.m3G NTL20 P20L) (pub := Lvm.E2T.pubG vk (hdrOf x).cL sig) (T := tdataL20)
    (sOff := (layout0 cfgL20.p).s) (t := t.1) (z := ec q2.e) hzv hz2 ⟨rfl, rfl⟩ ho2 ⟨rfl, rfl⟩ htd hTR rfl rfl rfl
    hry hryK hrr hrrK hvR hrvK (by rw [htab]; simp)
    (st := Lvm.M3.sumcheckTabs NTL20.mbT) (by rw [show NTL20.mbT = NTL20.toN.mbT from rfl, hsc]; exact hSs)
    (m3G_tableClaimsT _ _ _ _)
  have hlinR := lin_rel (M := memT TiL20 x qm qr) (zc := ec q2.e)
    (b := TypedV.smallT P20L (Lvm.E2T.pubG vk (hdrOf x).cL sig)) (tabs := Lvm.M3.sumcheckTabs NTL20.mbT)
    (by rw [show NTL20.mbT = NTL20.toN.mbT from rfl, hsc]; exact hcs) (fun cc hc => (hcok cc hc).1)
  have hTC' := hTC.1
  unfold typedClaimsGL at hTC' htc
  obtain ⟨l, -, hl, -, hl1, -⟩ := ok_bindV hTC
  have htcE : tc = l ++ t.2.map Lvm.Q2.FClaim.e3 := by rw [← htc, bind_apply, hl]; rfl
  have hrl := hrelT q3 hl1.1
  rw [hl, htab] at hrl
  simp only [List.map_nil, m3G_tableClaimsT, Lvm.M3.tableClaimsR, List.zip_nil_right, Shape.zeroTails,
    List.map_nil, List.flatMap_nil, List.append_nil] at hrl
  have htrel := List.rel_append hrl hlinR
  beta_reduce at htrel
  rw [← htcE] at htrel
  have hrel := List.rel_append htrel hfrel
  -- the opening's static inputs
  have hopenU : posOf P20L (phaseItem0 P20L .openMain) =
      8 * (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).U := by
    rw [cfgMainF_U]; exact hOU
  have hlayO : Lvm.Har.LayOk (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)) (streamLanes P20L) =
      true := by
    rw [layOkF_pb P20L _ _ (fun _ => 0) (fun _ => 0)]; exact hLY
  have hposO : Lvm.Har.PosOk (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)) (memT TiL20 x qm qr)
      sig 0 (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).levels
      ((cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).U + 15) := by
    have hPL' : Lvm.Fin.PosLanes P20L (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).g
        (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).ood
        (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).levels
        ((cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).U + 15) 0 := by
      rw [cfgMainF_g, cfgMainF_ood, cfgMainF_levels, cfgMainF_U]; exact hPL
    rw [← hsig]
    exact posOk_ofG P20L cfgL20 rfl _ 0 (fun i => by rw [Nat.zero_add, cfgMainF_pb]) hPL' streamOk_P20L hLL hQL20
      (posCellsL S H hok hb hG)
  have hpwO : Lvm.Har.PwOk (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)) (memT TiL20 x qm qr) 0
      (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).levels := by
    intro i hi _
    rw [cfgMainF_levels] at hi
    rw [cfgMainF_pw, cfgMainF_g, Nat.zero_add]
    exact pw_onC hon hGR i (lt_of_lt_of_le hi hML)
  have hendO : 8 * Lvm.Har.stackEndL (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).g
      (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).ood
      (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).levels
      ((cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)).U + 15) = sig.size := by
    rw [← hsig, sigL_size hLL, stackEnd_cfgMainF]; exact hSE
  have hq7 : 1 ≤ q7.e := by
    have h3 : 1 ≤ q3.e := le_trans (by simp) hq3e
    omega
  rw [show cfgL20.p = P20L from rfl] at hOpen
  -- `core_of_phasesL`, the opening by `open_phase`
  refine Lvm.Har.decideFLG_of P20L P20 3843 NTL20 vk (hdrOf x).cL sig ?_ (phiL20_acc S hlin H hG.1 hin.pub)
  refine Lvm.Har.core_of_phasesL P20L P20 3843 NTL20 vk (hdrOf x).cL sig hbL hpin htyped htape ?_
  intro s hs hsok
  rw [Lvm.E2T.typedItemsND_flat]
  dsimp only
  rw [show (Lvm.E2T.m3G NTL20 P20L).busFinal = Lvm.M3.busFinalR (Lvm.M3.sumcheckTabs NTL20.mbT) from rfl,
    show P20L.nuMain = CMain.nu20 from rfl]
  have key := Lvm.Q2.open_phase P20L (cfgMainF P20L (Lvm.Har.posBase cfgL20) (Lvm.Har.pwBase cfgL20)) rfl rfl rfl
    rfl rfl hF pin hpt _ _ hpinR _ _ _ hrel o.mb hσ sK (kc (pbB cfgL20)) hsK hS hlayO
    (by rw [Cell.val_K, hg, ofK_one]) rfl hposO hpwO hendO hq7 hOpen s (hs.trans hopenU) hsok
  beta_reduce at key
  rw [hnu] at key
  dsimp only at key
  exact key

/-- **MBL-STMT 7f** (owner C): **`NodeSound` at S2GL** (`nodeU20`'s twin at `THypL`). -/
theorem nodeL20 (S : SFL20) (H : THypL (NTL20.inst QL20 layL20)) (vk : RecursionFast.Digest) :
    NodeSound (VSLX NTL20) vk (fun x qm qr ↦ GoodTL (NTL20.inst QL20 layL20) H x qm qr ∧ SBlkU qm qr)
      (Lvm.NS.childSP P20L) := by
  have hone : (NTL20.toN.instL Pub.hdrLanesT QL20 layL20).src? layL20.one = some .one := H.ok.2
  have hW : ∀ {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}, GoodTL (NTL20.inst QL20 layL20) H x qm qr →
      WiringRelX QL20 layL20 (zTX (NTL20.toN.instL Pub.hdrLanesT QL20 layL20) Lvm.VEq.pubXT x qm qr) :=
    fun hG ↦ (wiringRelT_iff QL20 layL20 S.1.st.hlay _).mp hG.1.1.1.1
  have hB : spongeBlocks P20L ≤ 2 ^ 13 := by rw [sizes_P20L.1.2.2.2.2.1]; norm_num
  have hn : 615 ≤ pubLanesT := by decide
  exact nodeSoundCB cfgL20 Lvm.E2L.bL (VSLX NTL20) (decideFLX NTL20) (fun _ _ _ ↦ rfl) nodeStL20 Lvm.E2L.bL_eq
    pubLanesT Lvm.VEq.pubXT vk (NTL20.inst QL20 layL20) qaL20 _ QL20_eq S.1.st.inj
    (fun _ _ _ _ _ hG ↦ ⟨hG.1.2, hG.1.1.1.2, hG.2⟩)
    (fun _ _ _ _ _ _ hG ↦ hholdsCB S.1 Pub.hdrLanesT Lvm.VEq.pubXT cfgU_L20 hone (hW hG.1) H.hτ H.layOk
      hG.1.1.1.1.2 hG.2)
    (fun _ _ _ _ hok hb hG ↦ hmapCB S.1 Pub.hdrLanesT Lvm.VEq.pubXT cfgU_L20 nodeStL20 hB hn
      (fun x _ hj ↦ pubXT_lane x hj) hok hb hG.2)
    (fun _ _ _ _ _ _ _ ↦ hqltCB S.1 Lvm.VEq.pubXT _ rfl)
    (fun _ _ _ _ hok hb hG ↦ hposCB S.1 Pub.hdrLanesT Lvm.VEq.pubXT cfgU_L20 nodeStL20 hB hn
      (fun x _ hj ↦ pubXT_lane x hj) hone (hW hG.1) hok hb hG.2)
    (fun _ _ _ _ _ _ hG ↦ hbitsCB S.1 Pub.hdrLanesT Lvm.VEq.pubXT nodeStL20 hone (hW hG.1))
    (harithL20 S.1 S.2.1 S.2.2.2.1 H vk)

end Lvm.E2Q
