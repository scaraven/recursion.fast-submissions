-- New for lvm2 S2GT (GT-L, 2026-11-15): DAY-0 STATEMENTS of the circuit side at S2GT: the instance of blob GT, the
-- guard `staticOkBG20` and its facts, `nodeG20` (`NodeSound` at S2GT) and `harithG20` (Q_arith is `V_S`'s decision).
-- Every `sorry` is a day-0 statement tagged `-- S2GT-STMT <n>`; `opaque`s are PLACEHOLDERS tagged
-- `-- S2GT-PH <name> (owner)` (their values are S2GF's only so that they elaborate), to be replaced by the owner's
-- definition of the same name and type when blob GT lands.
import LvmS2GTStmtV
import LvmE2QNodeF
import LvmE2QInstT
import LvmS2GTFront
import LvmS2GTPlan
import LvmE2QTypedPhaseT
import LvmE2VHarG
import LvmE2VDecRef

/-!
# The S2GT circuit (day-0 statements)

* Instance of blob GT (GT-C's `LvmE2QInstT`): `cfgG20`, `frzG20`, `qaG20`, `QG20`, `layG20`, `cacheG20`,
  `staticOkTG20` (`staticOkTXc` at S2GT: segments, layout, cache, twins, regions, mini-bus); here `harChkBG20` (the
  HAR's static checks at S2GT) and `NodeGG` (the guard's facts: `NodeGC`, `NodeGF` generalised over the
  configuration, the `PUB` lanes and the sponge blocks, at `cfgG20`, `pubLanesT`, `spongeBlocks P20T`).
* Definitions: `pubLanesT` (707: `acc_in` 46 × 2 lanes), `NTG20` (`TNatT`, `phiT := PhiQGC cacheG20`), `TiG20`,
  **`staticOkBG20`** (the S2GT guard, S2GF's conjuncts at the S2GT instance), `SFG20`.
* Statements (owner C): `sfG20`, **`nodeG20`**, **`harithG20`**, and its typed phase (the table's 13a–13e).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol
open Lvm.E2T (TNatT VSGX decideFGX PhiQGC GoodTT THypT)

/-! ## The instance of blob GT -/

-- `pubLanesT` moved to `LvmE2QNodeG` (lvm2 U-TAPE: S2GU reads it too).

/-- **V_S's typed record at S2GT** (`phiT`: the fast `Φ_Q` at `E2`, 45 variables). -/
def NTG20 : TNatT := ⟨Lvm.QTyped.nregsOf layG20 frzG20, PhiQGC cacheG20, Lvm.QTyped.mbTOf cfgG20 frzG20⟩

/-- **The typed instance at S2GT.** -/
noncomputable def TiG20 : TInst := NTG20.inst QG20 layG20

/-- **The HAR's static checks at S2GT** (`harChkBF20` at the S2GT instance): the circuit's typed regions are V_S's
(`tdMatchB`); the typed phases (lanes from the schedule) end where the tape phase starts, inside the stream; the
opening starts inside the stream; every proof-of-work answer (the front's and the typed phases') is streamed with
`g ≤ 64`; `C_main`'s opening's layout facts; the regions and table columns are regular (`typedRegB`). -/
def harChkBG20 : Bool :=
  Lvm.QTyped.tdMatchB tdataG20 NTG20.toN &&
    typedEndT tdataG20 P20T == posOf P20T (phaseItem0 P20T .tape) &&
    decide (typedEndT tdataG20 P20T + 40 ≤ 8 * streamLanes P20T) &&
    decide (posOf P20T (phaseItem0 P20T .openMain) + 48 ≤ 8 * streamLanes P20T) &&
    powG20.all (fun a => decide (a.1 + 2 < streamLanes P20T) && decide (a.2 ≤ 64)) &&
    posOf P20T (phaseItem0 P20T .openMain) == 8 * (phaseLane P20T .openMain 0 - 5) &&
    Lvm.Har.LayOk (cfgMainF P20T (fun _ => 0) (fun _ => 0)) (streamLanes P20T) &&
    8 * Lvm.Har.stackEndL P20T.grind P20T.mainOod P20T.mainLevels (phaseLane P20T .openMain 0 - 5 + 15) ==
      hashedLen P20T &&
    decide (P20T.mainLevels.length ≤ (Lvm.QLink.opens P20T).length) && decide (1 ≤ 64 - P20T.grind) &&
    decide (Lvm.Fin.PosLanes P20T P20T.grind P20T.mainOod P20T.mainLevels (phaseLane P20T .openMain 0 - 5 + 15) 0) &&
    typedRegB tdataG20 (layout0 P20T).s

/-- **S2GT-STMT 10h** (owner L): **the facts `harChkBG20` decides** (`harChkF20_sound` at S2GT). -/
theorem harChkG20_sound (h : harChkBG20 = true) :
    Lvm.Har.TdOk tdataG20 NTG20.toN ∧
      typedEndT tdataG20 P20T = posOf P20T (phaseItem0 P20T .tape) ∧
      typedEndT tdataG20 P20T + 40 ≤ 8 * streamLanes P20T ∧
      posOf P20T (phaseItem0 P20T .openMain) + 48 ≤ 8 * streamLanes P20T ∧
      (∀ a ∈ powG20, a.1 + 2 < streamLanes P20T ∧ a.2 ≤ 64) ∧
      posOf P20T (phaseItem0 P20T .openMain) = 8 * (phaseLane P20T .openMain 0 - 5) ∧
      Lvm.Har.LayOk (cfgMainF P20T (fun _ => 0) (fun _ => 0)) (streamLanes P20T) = true ∧
      8 * Lvm.Har.stackEndL P20T.grind P20T.mainOod P20T.mainLevels (phaseLane P20T .openMain 0 - 5 + 15) =
        hashedLen P20T ∧
      P20T.mainLevels.length ≤ (Lvm.QLink.opens P20T).length ∧ 1 ≤ 64 - P20T.grind ∧
      Lvm.Fin.PosLanes P20T P20T.grind P20T.mainOod P20T.mainLevels (phaseLane P20T .openMain 0 - 5 + 15) 0 ∧
      typedRegB tdataG20 (layout0 P20T).s = true := by
  simp only [harChkBG20, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨Lvm.Har.tdOk_of h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- **The S2GT guard's circuit facts** (`NodeGC` at `cfgG20`, `spongeBlocks P20T`, `pubLanesT`, on
`frzG20 QG20 layG20 NTG20.toN`). -/
abbrev NodeGG : Prop := NodeGC cfgG20 (spongeBlocks P20T) pubLanesT frzG20 QG20 layG20 NTG20.toN

/-- **The S2GT guard** (S2GF's five conjuncts at the S2GT instance, and the cache's linearity check `linOkX`,
amendment A1). -/
def staticOkBG20 : Bool :=
  staticOkTG20 && Lvm.QTyped.nodeChkBG (spongeBlocks P20T) pubLanesT cfgG20 frzG20 QG20 layG20 NTG20.toN &&
    Lvm.TypedV.sigInSB NTG20.toN && harChkBG20 && Lvm.T.oneOkB layG20 && Lvm.Typed.KT.linOkX cacheG20

/-- **The S2GT guard's facts** (with the cache's linearity check `linOkX`, amendment A1, which `trefG20` reads). -/
abbrev SFG20 : Prop :=
  NodeGG ∧ harChkBG20 = true ∧ Lvm.T.oneOkB layG20 = true ∧ Lvm.Typed.KT.linOkX cacheG20 = true

/-- **S2GT-STMT 9** (owner C): the guard's facts from `staticOkBG20 = true`. -/
theorem sfG20 (h : staticOkBG20 = true) : SFG20 := by
  simp only [staticOkBG20, Bool.and_eq_true] at h
  exact ⟨nodeGC_of QG20_eq rfl rfl rfl h.1.1.1.1.1 h.1.1.1.1.2 h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- S2GT's stage facts. -/
theorem stageG20 : StageC cfgG20 (spongeBlocks P20T) pubLanesT :=
  ⟨by decide +kernel, by decide +kernel, rfl, by show (layout0 P20T).s = _; decide +kernel, by decide +kernel,
    by decide, by rw [sizes_P20T.1.2.2.2.2.1]; norm_num, by decide, by decide, ⟨by decide, by decide⟩⟩

/-- The S2GT node program is a node program with Q_arith `qaG20`. -/
theorem QG20_qa : QG20 = toProgram (nK cfgG20) 0 (qprogP P20T (lay cfgG20) (sigIn cfgG20) qaG20) :=
  QG20_eq

/-- **The Keccak half of S2GT's good pair** (`GoodKP P20T`; `goodKF_of`'s twin on `GkFR contRowsT`). -/
theorem goodKT_of {Ti : TInst} {H : THypT Ti} {vk c : RecursionFast.Digest} {x : List UInt8}
    {qm : Column CMain.nu20} {qr : Column 19} (hok : okS vk c x = true) (hG : GoodTT Ti H x qm qr) :
    GoodKP P20T x (qm, qr) := by
  have e : Lvm.E2T.contRowsT = contRows P20T := by
    unfold Lvm.E2T.contRowsT contRows
    rw [sizes_P20T.1.2.2.2.2.1]
    rfl
  exact ⟨hG.2.1, by rw [← e]; exact hG.2.2, hG.1.1.2 (okS_n hok).2⟩

/-! ## Q_arith's inputs at S2GT (`harithF20`'s, at `cfgG20`) -/

section PairG

variable {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}

/-- The trace bytes of the child at S2GT have `hashedLen P20T` bytes. -/
theorem sigG_size (hL : LaneLink P20T (wsC qr)) : (traceBytesB (decode P20T (wsC qr))).size = hashedLen P20T := by
  rw [traceBytesB_decode streamOk_P20T hL, Lvm.Har.sigma_sizeT hL.size]

/-- **The node memory streams the child's trace at S2GT** (`streamed_child` at `cfgG20`). -/
theorem streamedG {M : Mem} (hst : ∀ j < 2 ^ (lay cfgG20).m, M.k ((lay cfgG20).sb + j) = laneK (wsC qr) j)
    (hL : LaneLink P20T (wsC qr)) : Lvm.Q1.Streamed M (traceBytesB (decode P20T (wsC qr))) (streamLanes P20T) := by
  have hh : hashedLen P20T = 583152 := sizes_P20T.1.2.2.1
  have hw : (wsC qr).length = 17 * 2 ^ 14 := by rw [wsC, wsOf, List.length_map, List.length_range]
  exact Lvm.Har.streamed_child cfgG20 streamOk_P20T hL hst (T := streamLanes P20T)
    (by rw [streamLanes, hh]; decide) (by rw [show cfgG20.p = P20T from rfl, streamLanes]; omega)
    (by rw [streamLanes, hh, hw]; norm_num)

theorem hWG (S : NodeGG) (H : THypT TiG20) (hG : GoodTT TiG20 H x qm qr) :
    WiringRelX QG20 layG20 (zTX (NTG20.toN.instL Pub.hdrLanesT QG20 layG20) Lvm.VEq.pubXT x qm qr) :=
  (wiringRelT_iff QG20 layG20 S.st.hlay _).mp hG.1.1.1.1

/-- **The two row switches' words at S2GT** (`rowWordsF` at `cfgG20`). -/
theorem rowWordsG (S : NodeGG) (H : THypT TiG20) (hG : GoodTT TiG20 H x qm qr) :
    (∀ j < 128, (memT TiG20 x qm qr).k (tBw cfgG20 + j) =
      rowWordD (Lvm.Q2.slicesOf (memT TiG20 x qm qr) (wireSlices P20T)) j) ∧
    (∀ j < 128, (memT TiG20 x qm qr).k (tBk cfgG20 + j) =
      rowWordD (Lvm.Q2.slicesOf (memT TiG20 x qm qr) (ksSlices P20T)) j) := by
  obtain ⟨f, hf⟩ := Lvm.QTyped.aux_mkLayD QG20 (specQF cfgG20 QG20 powG20) dintsG20
  have hmem : ∀ B, B ∈ Lvm.Q2.rowAuxL (f (specQ cfgG20 QG20).auxWords.length) (tBw cfgG20) (wireSlices P20T) ++
      Lvm.Q2.rowAuxL (f ((specQ cfgG20 QG20).auxWords.length + 1)) (tBk cfgG20) (ksSlices P20T) →
      B ∈ layG20.aux := fun B hB => by
    show B ∈ (mkLayD QG20 (specQF cfgG20 QG20 powG20) dintsG20).1.aux
    rw [hf]
    show B ∈ (specQ cfgG20 QG20).auxOf f ++ _ ++ _
    exact List.mem_append_left _ (List.mem_append_right _ hB)
  have hone := zOf_one (NTG20.toN.instL Pub.hdrLanesT QG20 layG20) H.ok.2 Lvm.M3.lay26 (Lvm.VEq.pubXT x) qm qr
  exact ⟨fun j hj => rowWords_of_aux S.st.hlay hone (hWG S H hG) (fun B hB => hmem B (List.mem_append_left _ hB)) hj,
    fun j hj => rowWords_of_aux S.st.hlay hone (hWG S H hG) (fun B hB => hmem B (List.mem_append_right _ hB)) hj⟩

/-- **V's proof-of-work checks at S2GT** (`powOk_of_blks` at `cfgG20`). -/
theorem powOkG (S : NodeGG) (H : THypT TiG20) (hG : GoodTT TiG20 H x qm qr) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memT TiG20 x qm qr) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ powG20)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L :=
  powOk_of_blks cfgG20 (Q := QG20) (tl := layG20) (d := dintsG20) rfl S.st.hlay
    (zOf_one (NTG20.toN.instL Pub.hdrLanesT QG20 layG20) H.ok.2 Lvm.M3.lay26 (Lvm.VEq.pubXT x) qm qr) (hWG S H hG) hS hL hpw

/-- **Q_sig's `ChildOk` at S2GT** (`childOkF` at `cfgG20`). -/
theorem childOkG (S : NodeGG) (H : THypT TiG20) {vk c : RecursionFast.Digest} (hok : okS vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTT TiG20 H x qm qr ∧ SBlk qm qr) : ChildOk (sigIn cfgG20) (memT TiG20 x qm qr).k := by
  obtain ⟨hH, hA⟩ := hholdsC S Pub.hdrLanesT Lvm.VEq.pubXT stageG20 H.ok.2 (hWG S H hG.1) H.hτ H.layOk
    hG.1.1.1.1.2 hG.2
  have hH' : QG20.Holds (memT TiG20 x qm qr) := hH
  have hA' : QG20.Asserts (memT TiG20 x qm qr) := hA
  rw [QG20_eq] at hH' hA'
  have P := parts_of_holdsP hH' hA'
  have mp := hmapC S Pub.hdrLanesT Lvm.VEq.pubXT stageG20 (fun x _ hj ↦ pubXT_lane x hj) hok hb hG.2
  have hks := sigKSin_of_goodKP P20T ksSplit_P20T (by rw [sizes_P20T.1.2.2.2.2.1]; norm_num) (goodKT_of hok hG.1)
    mp.xs mp.ys mp.yc mp.yls mp.yns
  exact (qsig_sound_in (by rw [show (sigIn cfgG20).ln = 20 from rfl]; omega) P.2.1 mp.flag hks
    (hbitsC S Pub.hdrLanesT Lvm.VEq.pubXT stageG20 H.ok.2 (hWG S H hG.1))
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h).2

/-- **Q_link's position cells at S2GT** (`posCellsF` at `cfgG20`). -/
theorem posCellsG (S : NodeGG) (H : THypT TiG20) {vk c : RecursionFast.Digest} (hok : okS vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTT TiG20 H x qm qr ∧ SBlk qm qr) :
    ∀ k < (opens P20T).length, ((opens P20T).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20T).getD k default).L.t,
      (memT TiG20 x qm qr).k (nK cfgG20 + posIdx P20T k j) =
        kOf (posL P20T (wsC qr) (((opens P20T).getD k default).pe + j / 8)
          (j % 8 * ((opens P20T).getD k default).L.height) ((opens P20T).getD k default).L.height) := by
  intro k hk hH j hj
  obtain ⟨hH', hA⟩ := hholdsC S Pub.hdrLanesT Lvm.VEq.pubXT stageG20 H.ok.2 (hWG S H hG.1) H.hτ H.layOk
    hG.1.1.1.1.2 hG.2
  have hH'' : QG20.Holds (memT TiG20 x qm qr) := hH'
  have hA' : QG20.Asserts (memT TiG20 x qm qr) := hA
  rw [QG20_eq] at hH'' hA'
  have P := parts_of_holdsP hH'' hA'
  have mp := hmapC S Pub.hdrLanesT Lvm.VEq.pubXT stageG20 (fun x _ hj ↦ pubXT_lane x hj) hok hb hG.2
  have hp : cfgG20.p = P20T := rfl
  have hk' : k < (opens cfgG20.p).length := by rw [hp]; exact hk
  have hH2 : ((opens cfgG20.p).getD k default).L.height ≤ 64 := by rw [hp]; exact hH
  have hj' : j < ((opens cfgG20.p).getD k default).L.t := by rw [hp]; exact hj
  have hv := posVal_onC (C := cfgG20) (outsOnC S Pub.hdrLanesT Lvm.VEq.pubXT H.ok.2 (hWG S H hG.1))
    (by rw [hp]; exact streamOk_P20T) (by rw [hp]; exact hQT20) mp.stream hk' hH2 hj'
  rw [hp] at hv
  have hq := qlink_pos (pt := p0 (nK cfgG20) 0) hQT20 P.1.1 hk hj
  exact hq.trans hv

/-- The current proof's `vk` cells at S2GT (`vk_cellsT` on `PUB`'s 707 lanes). -/
theorem vk_cellsG {M : Mem} {vk : RecursionFast.Digest}
    (hpub : ∀ j < pubLanesT, M.k ((sigIn cfgG20).flag + j) = hdrLane x j) (hvk : (hdrOf x).vk = vk) :
    ∀ i < 4, M.k (pbB cfgG20 + 1 + i) = (digestLanes vk).getD i 0 := by
  intro i hi
  have hj : 1 + i < pubLanes := by rw [pubLanes_eq]; omega
  have e1 : M.k (pbB cfgG20 + 1 + i) = (Lvm.NS.hdrLanes x).getD (1 + i) 0 := by
    rw [Nat.add_assoc, show pbB cfgG20 = (sigIn cfgG20).flag from rfl, hpub _ (by unfold pubLanesT; omega),
      Lvm.NS.hdrLanes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some]
  have hv : (Lvm.VEq.pubX x).vk = digestLanes vk := by rw [← hvk]; rfl
  have hl : i < (digestLanes vk).length := by simp only [digestLanes, List.length_map, List.length_range]; omega
  rw [e1, Lvm.NS.hdrLanes_eq_pubX, Pub.hdrLanes, hv]
  simp only [List.append_assoc, List.singleton_append]
  rw [Nat.add_comm, List.getD_append _ _ _ _ (by rw [List.length_cons]; omega), List.getD_cons_succ]

/-- **`Φ_Q` at `E2` holds at the folded accumulator** (the good pair's `AccOkTT`, STMT 6 with `linOkX`). -/
theorem phiG20_acc (S : NodeGG) (hlin : Lvm.Typed.KT.linOkX cacheG20 = true) (H : THypT TiG20)
    (hG : GoodTT TiG20 H x qm qr) {M : Mem} (hpub : ∀ j < pubLanesT, M.k ((sigIn cfgG20).flag + j) = hdrLane x j) :
    NTG20.phiT ((accCT M (pbB cfgG20)).pt.map Lvm.e2OfFE) = Lvm.e2OfFE (accCT M (pbB cfgG20)).y := by
  have hacc : Lvm.E2T.AccOkTT TiG20 (Lvm.VEq.pubXT x) := hG.1.2
  -- the folded accumulator's lanes are the statement's `acc_in`
  have hl : ∀ j < 46, (Lvm.Q2.ld2 (pbB cfgG20 + 615 + 2 * j)).val M =
      Lvm.e2OfFE (fe16At (Lvm.VEq.sigOfX x) (headerAt (offAcc + 16 * j))) := by
    intro j hj
    have hpb : (sigIn cfgG20).flag = pbB cfgG20 := rfl
    have e1 := hpub (615 + 2 * j) (by show 615 + 2 * j < 615 + 2 * (45 + 1); omega)
    have e2 := hpub (615 + 2 * j + 1) (by show 615 + 2 * j + 1 < 615 + 2 * (45 + 1); omega)
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (615 + 2 * j) = headerAt (offAcc + 16 * j) by
      simp only [headerAt, offAcc, sigBytes]; omega] at e1
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (615 + 2 * j + 1) = headerAt (offAcc + 16 * j) + 8 by
      simp only [headerAt, offAcc, sigBytes]; omega] at e2
    show (⟨(FE.ofK (M.k (pbB cfgG20 + 615 + 2 * j))).c₀, (FE.ofK (M.k (pbB cfgG20 + 615 + 2 * j + 1))).c₀⟩ : FE2) = _
    rw [Nat.add_assoc (pbB cfgG20), e1, Nat.add_assoc (pbB cfgG20) (615 + 2 * j), e2]
    rfl
  have hpt : (accCT M (pbB cfgG20)).pt.map Lvm.e2OfFE = (Lvm.VEq.pubXT x).accIn.pt.map Lvm.e2OfFE := by
    simp only [accCT, Lvm.VEq.pubXT, pubOfW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 45 := List.mem_range.mp hj
    exact hl j (by omega)
  have hy : Lvm.e2OfFE (accCT M (pbB cfgG20)).y = Lvm.e2OfFE (Lvm.VEq.pubXT x).accIn.y := by
    simp only [accCT, Lvm.VEq.pubXT, pubOfW]
    exact hl Lvm.VEq.accVT (by decide)
  rw [hpt, hy]
  -- `Φ_Q` at `E2` (STMT 6) and the good pair's `AccOkTT`
  have hc : cacheG20 = Lvm.Typed.cacheWX QG20 layG20 := cacheWXF_eq QG20 layG20 S.st.hlay
  show Lvm.E2T.PhiQGC cacheG20 _ = _
  rw [hc, Lvm.E2T.PhiQGC_eq QG20 layG20 S.st.hlay S.st.cache (hc ▸ hlin) _
    (by rw [List.length_map]; exact H.acc x)]
  have hpt' : Lvm.E2T.accPtT (Lvm.VEq.pubXT x) = ((Lvm.VEq.pubXT x).accIn.pt.map Lvm.e2OfFE).map FE2.toE2 := by
    rw [Lvm.E2T.accPtT, List.map_map]; rfl
  have hy' : Lvm.E2T.accYT (Lvm.VEq.pubXT x) = FE2.toE2 (Lvm.e2OfFE (Lvm.VEq.pubXT x).accIn.y) := rfl
  have hof : ∀ z : FE2, Lvm.Typed.ofE2 (FE2.toE2 z) = z := fun _ => rfl
  rw [Lvm.E2T.AccOkTT, Lvm.Typed.PhiQT, hpt', hy', List.map_map] at hacc
  simp only [Function.comp_def, hof, List.map_id'] at hacc
  exact FE2.toE2_injective hacc

end PairG

set_option maxRecDepth 100000 in
/-- **S2GT 10e (`miniG20`)**: the mini-bus record at S2GT (`miniC` at `cfgG20`). -/
theorem miniG20 (S : NodeGG) : Lvm.M3.sumcheckTabs NTG20.toN.mbT = NTG20.toN.mbT ∧
    (Lvm.QTyped.tdataOf cfgG20 frzG20).mbS = NTG20.toN.mbT.map Lvm.M3.Tab.shape ∧
    (Lvm.QTyped.tdataOf cfgG20 frzG20).mbR = cfgG20.p.tableRounds ∧ (Lvm.QTyped.tdataOf cfgG20 frzG20).mbD = cfgG20.p.busDepth ∧
    Lvm.Har.FixListed NTG20.toN.mbT (Lvm.QTyped.tdataOf cfgG20 frzG20).mbFix :=
  miniC S

/-- **S2GT-STMT 10** (owner C): **Q_arith at S2GT is V_S's decision** (`harithF20`'s twin): from Q_arith's segments
on a good S2GT pair's memory, `decideFGX NTG20` accepts the child's stream (read with the S2GT schedule). -/
theorem harithG20 (S : NodeGG) (hhar : harChkBG20 = true) (hlin : Lvm.Typed.KT.linOkX cacheG20 = true)
    (H : THypT TiG20) (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 →
      GoodTT TiG20 H x qm qr ∧ SBlk qm qr →
      InMapMB (spongeBlocks P20T) pubLanesT (lay cfgG20) (sigIn cfgG20) (memT TiG20 x qm qr) vk x qm qr →
      LaneLink P20T (wsC qr) → LinkOk P20T (decode P20T (wsC qr)) →
      Ok (ctxOf TiG20.Q) (memT TiG20 x qm qr) qaG20 (p2P (lay cfgG20) (sigIn cfgG20) (nK cfgG20) 0 P20T) →
      decideFGX NTG20 vk (hdrOf x).cL (traceBytesB (decode P20T (wsC qr))) = true := by
  intro c x qm qr hok hb hG hin hLL hlink hrun
  obtain ⟨sig, hsig⟩ : ∃ s, traceBytesB (decode P20T (wsC qr)) = s := ⟨_, rfl⟩
  rw [hsig]
  -- the program's three parts after Q_sig: the pin, the front, `qarithG`
  have hrun' : Lvm.QSig.Ok (ctxOf TiG20.Q) (memT TiG20 x qm qr)
      (pinF cfgG20.p >>= fun pin ↦ frontF cfgG20 >>= fun o ↦ qarithG cfgG20 tdataG20 pin o)
      (p2P (lay cfgG20) (sigIn cfgG20) (nK cfgG20) 0 P20T) := hrun
  obtain ⟨hPin, hR⟩ := Lvm.Har.okb hrun'
  obtain ⟨q1, hq1⟩ : ∃ q1, (p2P (lay cfgG20) (sigIn cfgG20) (nK cfgG20) 0 P20T).adv
      (pinF cfgG20.p (p2P (lay cfgG20) (sigIn cfgG20) (nK cfgG20) 0 P20T)).2 = q1 := ⟨_, rfl⟩
  obtain ⟨pin, hpinE⟩ : ∃ pin, (pinF cfgG20.p (p2P (lay cfgG20) (sigIn cfgG20) (nK cfgG20) 0 P20T)).1 = pin :=
    ⟨_, rfl⟩
  rw [hq1, hpinE] at hR
  obtain ⟨hFr, hQa⟩ := Lvm.Har.okb hR
  obtain ⟨o, hfr⟩ : ∃ o, (frontF cfgG20 q1).1 = o := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2, q1.adv (frontF cfgG20 q1).2 = q2 := ⟨_, rfl⟩
  rw [hfr, hq2] at hQa
  -- the static facts, the stream, the gate, `vk`
  obtain ⟨htd, hTE, hTT, hTO, hPW, hOU, hLY, hSE, hML, hGR, hPL, hTR⟩ := harChkG20_sound hhar
  have hS : Lvm.Q1.Streamed (memT TiG20 x qm qr) sig (streamLanes P20T) := hsig ▸ streamedG hin.stream hLL
  have hTl : streamLanes P20T = 72894 := by rw [streamLanes, sizes_P20T.1.2.2.1]
  have hg : (memT TiG20 x qm qr).k (pbB cfgG20) = 1 := hin.flag
  have hvk := vk_cellsG hin.pub (okS_vk hok)
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
  have hzkv : (kc q2.k).val (memT TiG20 x qm qr) = 0 := by
    have e := const_val hZK.1
    rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, ofK_zero] at e
    exact e
  have hokv : (kc (q2.k + 1)).val (memT TiG20 x qm qr) = 1 := by
    have e := const_val hOK.1
    rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, ofK_one] at e
    exact e
  -- the typed phases (`typed_phaseT`), their claims, the shape cell (outputs and pointers opaque)
  obtain ⟨t, q3, ht, hq3e, hTy, hR⟩ := ok_bindV hR
  obtain ⟨tc, q4, htc, hq4e, hTC, hR⟩ := ok_bindV hR
  obtain ⟨ka, q5, hka, hq5e, hKA, hR⟩ := ok_bindV hR
  obtain ⟨kb, q6, hkb, hq6e, hKB, hR⟩ := ok_bindV hR
  obtain ⟨sK, q7, hsKe, hq7e, hSK, hOpen⟩ := ok_bindV hR
  obtain ⟨hsc, hSs, hRr, hDd, hfix⟩ := miniG20 S
  have hpowA := powOkG S H hG.1 hS (L := powG20) (fun a ha => ha) hPW
  have hpowT : Lvm.Q1.PowOkV (feAt sig) (typedChalsT P20T) := fun a ha =>
    hpowA a (List.mem_append_right _ ha)
  have hpowF : Lvm.Q1.PowOkV (feAt sig) (powFront P20T) := fun a ha => hpowA a (List.mem_append_left _ ha)
  have hP0 := pinEndT
  have htyped := typed_phaseT (c := ctxOf TiG20.Q) vk (hdrOf x).cL hS hg hvk (z := ec q2.e) (o := ec (q2.e + 1))
    (zk := kc q2.k) (ok := kc (q2.k + 1)) rfl rfl hzv hov rfl rfl hzkv hokv htd P20 rfl hsc hSs hRr hDd hfix
    (busLanes_of busLanesB_P20T) hpowT (by rw [hTl] at hTT ⊢; exact hTT) (by rw [hTl]; decide) _ (by simp) hTy
  have hle : typedPosF P20T ≤ typedEndT tdataG20 P20T := by
    have h1 := mbPT_le tdataG20 P20T
    have h2 := (busLanes_of busLanesB_P20T).mb
    have h3 : mbPT P20T = 8 * busL P20T iMB - 40 := rfl
    omega
  rw [show cfgG20.p = P20T from rfl] at ht
  -- the typed claims' inputs (the gadget's shape), before `ht` renames the output
  obtain ⟨⟨hry, hryK⟩, ⟨hrr, hrrK⟩, hvR, hrvK, htabl⟩ := typedGT_shape (c := ctxOf TiG20.Q)
    (M := memT TiG20 x qm qr) tdataG20 P20T (pbB cfgG20) (pubLanesTC P20T) (ec q2.e) (ec (q2.e + 1)) (kc q2.k)
    (kc (q2.k + 1)) _ hTy.1
  rw [ht] at hry hryK hrr hrrK hvR hrvK htabl
  rw [hTE, ht] at htyped
  -- the pin (`pin_phase`)
  have hnu : P20T.nuMain = 23 := rfl
  have hpb := pinHPT
  have hpe := pinEndT
  have hqa := pinQaT
  rw [hnu] at hpe hqa
  have epin : pinF cfgG20.p = Lvm.Q2.pinG 23 (phaseLane P20T .commit 1) (phaseLane P20T .commit (23 + 1)) := rfl
  rw [epin] at hPin hpinE
  obtain ⟨hpin, hpinV⟩ := Lvm.Q2.pin_phase hS (nu := 23) (by norm_num) hpb.symm hqa
    (by rw [hTl] at hTT ⊢; omega) (by rw [hqa]; rw [hTl] at hTT ⊢; omega) hPin.1
  rw [hpe] at hpin
  rw [hpinE] at hpinV
  obtain ⟨zP, aP, hzP, hzL⟩ := pinG_fst 23 (phaseLane P20T .commit 1) (phaseLane P20T .commit (23 + 1))
    (p2P (lay cfgG20) (sigIn cfgG20) (nK cfgG20) 0 P20T)
  rw [hpinE] at hzP
  have hpinB : (Lvm.pinD 23 sig ⟨posOf P20T 1, 0, true⟩).1 =
      BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memT TiG20 x qm qr) zP) (aP.val (memT TiG20 x qm qr)) := by
    rw [hzP, cclaim_point] at hpinV
    exact (Prod.mk.inj hpinV).2.symm
  rw [hpinB] at hpin
  -- the front's inputs and its phases
  have hT29 : 29 ≤ streamLanes P20T := by rw [hTl]; norm_num
  obtain ⟨hrw, hrk⟩ := rowWordsG S H hG.1
  have hch := childOkG S H hok hb hG
  have hon := outsOnC S Pub.hdrLanesT Lvm.VEq.pubXT H.ok.2 (hWG S H hG.1)
  have hsb := sBits_onC hon
  obtain ⟨hnb, hn, hsbv⟩ := frontIns hS hT29 (hbitsC S Pub.hdrLanesT Lvm.VEq.pubXT stageG20 H.ok.2 (hWG S H hG.1))
    hch hsb Lvm.VEq.accVT vk (hdrOf x).cL rfl rfl
  have hh : (Lvm.E2T.pubG vk (hdrOf x).cL sig).h =
      (List.range 4).map fun l => (memT TiG20 x qm qr).k (Lvm.Har.hLane l) := Lvm.Har.pub_h hS hT29 vk (hdrOf x).cL
  have hsmE : TypedV.smallT P20T (Lvm.E2T.pubG vk (hdrOf x).cL sig) =
      decide ((Lvm.E2T.pubG vk (hdrOf x).cL sig).n ≤ 2 ^ 18) := rfl
  obtain ⟨tp, co, lo, htape, hcall, hlink, hfrel, hmbv⟩ := front_phasesT hS hTO hg hpowF hrw hrk
    (Lvm.E2T.pubG vk (hdrOf x).cL sig) hnb hn hsbv hh (ec q2.e)
    (TypedV.smallT P20T (Lvm.E2T.pubG vk (hdrOf x).cL sig))
    (fun h => by rw [hsmE] at h; exact of_decide_eq_true h) hFr
  rw [hfr] at hfrel hmbv
  have ecr : Lvm.E2T.contRowsT = contRows P20T := by
    unfold Lvm.E2T.contRowsT contRows
    rw [sizes_P20T.1.2.2.2.2.1]
    rfl
  rw [← ecr] at hlink
  -- the shape: `σ` from `n' − 1`'s bits 18, 19, the `K` cell `sK`
  have hσ := Lvm.Har.sigma_val o.mb _ hmbv hn.1 hn.2
  rw [← hsmE] at hσ
  have hsK : sK.val (memT TiG20 x qm qr) =
      if TypedV.smallT P20T (Lvm.E2T.pubG vk (hdrOf x).cL sig) then 1 else 0 := by
    rw [← hsKe, mulAdd_spec hSK.1, ← hka, ← hkb, Lvm.Har.addK_val hKA.1, Lvm.Har.addK_val hKB.1, hzkv, ofK_one,
      add_zero, ← hσ]
    ring
  -- the opening's context, the pin as `FRel`
  have hF : Lvm.Q2.FCtxOk (memT TiG20 x qm qr)
      ⟨ec q2.e, ec (q2.e + 1), kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc (q2.k + 1), kc q2.k⟩, true⟩ := by
    refine ⟨hzv, hov, hzkv, rfl, rfl, ?_, ⟨rfl, rfl⟩, ?_⟩
    · show (⟨((kc (q2.k + 1)).val (memT TiG20 x qm qr)).c₀, ((kc q2.k).val (memT TiG20 x qm qr)).c₀⟩ : FE2) = 1
      rw [hokv, hzkv]; rfl
    · show (⟨((kc q2.k).val (memT TiG20 x qm qr)).c₀, ((kc q2.k).val (memT TiG20 x qm qr)).c₀⟩ : FE2) = 0
      rw [hzkv]; rfl
  have hzl : zP.length = 23 := by
    rw [hzL]; simp
  have hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (Lvm.Q2.pinPt pin) := by rw [hzP]; rfl
  have hpinR : Lvm.Q2.FRel (memT TiG20 x qm qr) CMain.nu20 (.e3 pin)
      (BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memT TiG20 x qm qr) zP) (aP.val (memT TiG20 x qm qr))) := by
    refine ⟨?_, ?_⟩
    · rw [hzP]; simp [Lvm.Har.WF1, hzl]
    · rw [hzP, cclaim_point]
  -- the claims: the typed phases' (10d), then the front's
  have hz2 : (⟨kc q2.k, kc q2.k⟩ : C2).val (memT TiG20 x qm qr) = 0 := by
    show (⟨((kc q2.k).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 0; rw [hzkv]; rfl
  have ho2 : (⟨kc (q2.k + 1), kc q2.k⟩ : C2).val (memT TiG20 x qm qr) = 1 := by
    show (⟨((kc (q2.k + 1)).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 1; rw [hokv, hzkv]; rfl
  have htrel := typed_relT (c := ctxOf TiG20.Q) (M := memT TiG20 x qm qr) (zc := ec q2.e)
    (b := TypedV.smallT P20T (Lvm.E2T.pubG vk (hdrOf x).cL sig)) (N := NTG20) (p := P20)
    (m := Lvm.E2T.m3G NTG20 P20T) (pub := Lvm.E2T.pubG vk (hdrOf x).cL sig) (T := tdataG20) (sOff := (layout0 cfgG20.p).s)
    (t := t) (z := ec q2.e) hzv hz2 ⟨rfl, rfl⟩ ho2 ⟨rfl, rfl⟩ htd hTR rfl rfl rfl hry hryK hrr hrrK hvR hrvK htabl
    (st := Lvm.M3.sumcheckTabs NTG20.mbT) (by rw [show NTG20.mbT = NTG20.toN.mbT from rfl, hsc]; exact hSs)
    (m3G_tableClaimsT _ _ _ _) _ hTC.1
  beta_reduce at htrel
  rw [htc] at htrel
  have hrel := List.rel_append htrel hfrel
  beta_reduce at hrel
  -- the opening's static inputs
  have hopenU : posOf P20T (phaseItem0 P20T .openMain) =
      8 * (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).U := by
    rw [cfgMainF_U]; exact hOU
  have hlayO : Lvm.Har.LayOk (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)) (streamLanes P20T) =
      true := by
    rw [layOkF_pb P20T _ _ (fun _ => 0) (fun _ => 0)]; exact hLY
  have hposO : Lvm.Har.PosOk (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)) (memT TiG20 x qm qr)
      sig 0 (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).levels
      ((cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).U + 15) := by
    have hPL' : Lvm.Fin.PosLanes P20T (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).g
        (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).ood
        (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).levels
        ((cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).U + 15) 0 := by
      rw [cfgMainF_g, cfgMainF_ood, cfgMainF_levels, cfgMainF_U]; exact hPL
    rw [← hsig]
    exact posOk_ofG P20T cfgG20 rfl _ 0 (fun i => by rw [Nat.zero_add, cfgMainF_pb]) hPL' streamOk_P20T hLL hQT20
      (posCellsG S H hok hb hG)
  have hpwO : Lvm.Har.PwOk (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)) (memT TiG20 x qm qr) 0
      (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).levels := by
    intro i hi _
    rw [cfgMainF_levels] at hi
    rw [cfgMainF_pw, cfgMainF_g, Nat.zero_add]
    exact pw_onC hon hGR i (lt_of_lt_of_le hi hML)
  have hendO : 8 * Lvm.Har.stackEndL (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).g
      (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).ood
      (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).levels
      ((cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)).U + 15) = sig.size := by
    rw [← hsig, sigG_size hLL, stackEnd_cfgMainF]; exact hSE
  have hq7 : 1 ≤ q7.e := by
    have h3 : 1 ≤ q3.e := le_trans (by simp) hq3e
    omega
  rw [show cfgG20.p = P20T from rfl] at hOpen
  -- `core_of_phasesG` (10g), the opening by `open_phase` (10f)
  have em : Lvm.E2T.dTypedT P20 NTG20 (Lvm.E2T.m3G NTG20 P20T) (Lvm.E2T.pubG vk (hdrOf x).cL sig) =
      Lvm.E2T.dTypedT P20 NTG20 (NTG20.toN.m3 P20) (Lvm.E2T.pubG vk (hdrOf x).cL sig) := by
    unfold Lvm.E2T.dTypedT Lvm.E2T.dTypedTG
    rw [Lvm.VEq.dMiniT_congr P20 P20 (Lvm.E2T.m3G NTG20 P20T) (NTG20.toN.m3 P20) NTG20.mbT _ rfl rfl rfl rfl rfl]
  rw [← em] at htyped
  refine Lvm.Har.decideFGX_of (acc := accCT (memT TiG20 x qm qr) (pbB cfgG20)) NTG20 vk (hdrOf x).cL sig ?_
    (phiG20_acc S hlin H hG.1 hin.pub)
  refine Lvm.Har.core_of_phasesG NTG20 vk (hdrOf x).cL sig hbT hpin htyped htape hcall hlink ?_
  intro s hs hsok
  have key := Lvm.Q2.open_phase P20T (cfgMainF P20T (Lvm.Har.posBase cfgG20) (Lvm.Har.pwBase cfgG20)) rfl rfl rfl
    rfl rfl hF pin hpt _ _ hpinR _ _ _ hrel o.mb hσ sK (kc (pbB cfgG20)) hsK hS hlayO
    (by rw [Cell.val_K, hg, ofK_one]) rfl hposO hpwO hendO hq7 hOpen s (hs.trans hopenU) hsok
  rw [hnu] at key
  exact key


set_option maxRecDepth 100000 in
/-- **S2GT-STMT 11** (owner L since 18:17): **`nodeG20`**: `NodeSound` of the S2GT circuit for `VSGX NTG20`, on
stream-block pairs of the S2GT good relation `GoodTT TiG20 H` (E2F-T), the left child read with the S2GT schedule
(`childSP P20T`) (`nodeSoundC` at `cfgG20`, `pubXT`, `PUB` as `Pub.hdrLanesT`; Q_arith by `harithG20`). -/
theorem nodeG20 (S : SFG20) (H : THypT TiG20) (vk : RecursionFast.Digest) :
    NodeSound (VSGX NTG20) vk (fun x qm qr ↦ GoodTT TiG20 H x qm qr ∧ SBlk qm qr) (childSP P20T) := by
  have hone : (NTG20.toN.instL Pub.hdrLanesT QG20 layG20).src? layG20.one = some .one := H.ok.2
  have hW : ∀ {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}, GoodTT TiG20 H x qm qr →
      WiringRelX QG20 layG20 (zTX (NTG20.toN.instL Pub.hdrLanesT QG20 layG20) Lvm.VEq.pubXT x qm qr) :=
    fun hG ↦ (wiringRelT_iff QG20 layG20 S.1.st.hlay _).mp hG.1.1.1.1
  exact nodeSoundC cfgG20 (VSGX NTG20) (decideFGX NTG20) (fun _ _ _ ↦ rfl) nodeStG20 pubLanesT Lvm.VEq.pubXT vk
    TiG20 qaG20 _ QG20_qa S.1.st.inj (fun _ _ _ _ hok hG ↦ goodKT_of hok hG.1)
    (fun _ _ _ _ _ _ hG ↦ hholdsC S.1 Pub.hdrLanesT Lvm.VEq.pubXT stageG20 hone (hW hG.1) H.hτ H.layOk
      hG.1.1.1.1.2 hG.2)
    (fun _ _ _ _ hok hb hG ↦ hmapC S.1 Pub.hdrLanesT Lvm.VEq.pubXT stageG20 (fun x _ hj ↦ pubXT_lane x hj) hok hb
      hG.2)
    (fun _ _ _ _ _ _ _ ↦ hqltC S.1 Lvm.VEq.pubXT _ rfl)
    (fun _ _ _ _ hok hb hG ↦ hposC S.1 Pub.hdrLanesT Lvm.VEq.pubXT stageG20 streamOk_P20T hQT20
      (fun x _ hj ↦ pubXT_lane x hj) hone (hW hG.1) hok hb hG.2)
    (fun _ _ _ _ _ _ hG ↦ hbitsC S.1 Pub.hdrLanesT Lvm.VEq.pubXT stageG20 hone (hW hG.1))
    (harithG20 S.1 S.2.1 S.2.2.2 H vk)

end Lvm.E2Q
