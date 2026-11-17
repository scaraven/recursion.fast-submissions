-- New for lvm2 MP-B cap pruning (CAP-C2, 2026-11-17): DAY-0 STATEMENTS of the S2GB guard and input map. Every
-- `sorry` is tagged `-- CAP-FRZ C2`; a proof never changes its statement (changes go to the lead, old → new).
import LvmS2GBInstC
import LvmS2GSGuardC
import LvmS2GBV

/-!
# The S2GB guard and input map (day-0 statements)

* Instance of blob B (`LvmS2GBInstC`): `cfgB20`, `frzB20`, `tdataB20`, `qaB20`, `QB20`, `powB20`, `layB20`,
  `cacheB20`, `staticOkTB20`; here **`NTB20`**, `TiB20`, `harChkBB20` (the HAR's static checks on the S2GB stream:
  `LayOkB`, `stackEndL … (some P20B)`, `PosLanes … (some P20B)`).
* **`nodeChkBGB`**: S2GS's input-map and mini-bus checks (`nodeChkBGS`, generic in the configuration: the mini-bus
  seeds the heap-bottom regions at `capPrune`) at the S2GB instance; `NodeGB`, **`staticOkBB20`**, `SFB20`, **`sfB20`**.
* `GoodTSB`: the good pair at S2GB (`GoodTS` over the S2GB tape intervals `contIvSB aSP`).
* `harChkB20_sound`, `miniB20`, `inMapB20`: `harChkS20_sound`'s, `miniS20`'s, `inMapS20`'s twins.
-/

set_option autoImplicit false

namespace Lvm.E2S

open Lvm Lvm.E2U Lvm.Typed

/-- **The good pair at S2GB** (RE-FREEZE R1: over `THypSB`, the mini-bus at depth 13): `GbTS` and the merged tape over S2GB's intervals `contIvSB aSP` (the trace's rows
`1 … bB`). -/
def GoodTSB (Ti : TInst) (H : THypSB Ti) : Lvm.ASM.GoodRel :=
  fun x qm qr ↦ GbTS Ti H.hτ x (qm, qr) ∧ GkL (contIvSB aSP) x (qm, qr)

end Lvm.E2S

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped Lvm.TypedV Lvm.BitsTab LeanVM.Protocol
open Lvm.E2T (TNatT PhiQGC)
open Lvm.E2U (SBlkU YqU MqU)
open Lvm.E2S (THypSB GoodTSB)
open Lvm.CT (slM20)
open Lvm.ASM (okSL NodeSoundS)

/-! ## The instance of blob B -/

/-- **V_S's typed record at S2GB** (`phiT`: the fast `Φ_Q` at `E2`). -/
def NTB20 : TNatT := ⟨Lvm.QTyped.nregsOf layB20 frzB20, PhiQGC cacheB20, Lvm.QTyped.mbTOf cfgB20 frzB20⟩

/-- **The typed instance at S2GB.** -/
noncomputable def TiB20 : TInst := NTB20.inst QB20 layB20

/-- **The HAR's static checks at S2GB** (`harChkBS20` at the S2GB instance; the opening's lanes on the S2GB stream:
`LayOkB`, `stackEndL`, `PosLanes` with `cp = some P20B`). -/
def harChkBB20 : Bool :=
  Lvm.QTyped.tdMatchB tdataB20 NTB20.toN &&
    typedEndL tdataB20 P20B == posOf P20B (phaseItem0 P20B .tape) &&
    decide (typedEndL tdataB20 P20B + 40 ≤ 8 * streamLanes P20B) &&
    decide (posOf P20B (phaseItem0 P20B .openMain) + 48 ≤ 8 * streamLanes P20B) &&
    powB20.all (fun a => decide (a.1 + 2 < streamLanes P20B) && decide (a.2 ≤ 64)) &&
    posOf P20B (phaseItem0 P20B .openMain) == 8 * (phaseLane P20B .openMain 0 - 5) &&
    Lvm.Har.LayOkB (cfgMainF P20B (fun _ => 0) (fun _ => 0)) (some P20B) (streamLanes P20B) &&
    8 * Lvm.Har.stackEndL P20B.grind P20B.mainOod P20B.mainLevels (phaseLane P20B .openMain 0 - 5 + 15) (some P20B) ==
      hashedLen P20B &&
    decide (P20B.mainLevels.length ≤ (Lvm.QLink.opens P20B).length) && decide (1 ≤ 64 - P20B.grind) &&
    decide (Lvm.Fin.PosLanes P20B P20B.grind P20B.mainOod P20B.mainLevels (phaseLane P20B .openMain 0 - 5 + 15) 0
      (some P20B)) &&
    typedRegB tdataB20 (layout0 P20B).s

/-! ## The guard at S2GB -/

/-- **The checks `NodeSound` reads at S2GB** (`nodeChkBGS` at the S2GB instance: the input map with `spongeBlocks
P20B` trace blocks, the mini-bus reads and seeds). -/
def nodeChkBGB : Bool :=
  nodeChkBGS (spongeBlocks P20B) (pubLanesS P20B) cfgB20 frzB20 QB20 layB20 NTB20.toN

/-- **The S2GB guard's circuit facts** (`NodeGCS` at `cfgB20`). -/
abbrev NodeGB : Prop := NodeGCS cfgB20 (spongeBlocks P20B) (pubLanesS P20B) frzB20 QB20 layB20 NTB20.toN

/-- **The S2GB guard** (S2GS's conjuncts at the S2GB instance, the HAR's on the S2GB stream). -/
def staticOkBB20 : Bool :=
  staticOkTB20 && nodeChkBGB && Lvm.TypedV.sigInSBL (layout0 P20B).s NTB20.toN && harChkBB20 &&
    Lvm.T.oneOkB layB20 && Lvm.Typed.KT.linOkX cacheB20 && Lvm.M3.mbLinB NTB20.mbT

/-- **The S2GB guard's facts.** -/
abbrev SFB20 : Prop :=
  NodeGB ∧ harChkBB20 = true ∧ Lvm.T.oneOkB layB20 = true ∧ Lvm.Typed.KT.linOkX cacheB20 = true ∧
    Lvm.M3.mbLinB NTB20.mbT = true

/-- **CAP-FRZ C2**: the guard's facts from `staticOkBB20 = true` (`sfS20`'s twin). -/
theorem sfB20 (h : staticOkBB20 = true) : SFB20 := by
  simp only [staticOkBB20, Bool.and_eq_true] at h
  exact ⟨nodeGCS_of QB20_eq rfl rfl rfl h.1.1.1.1.1.1 h.1.1.1.1.1.2 h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **The facts `harChkBB20` decides** (`harChkS20_sound`'s twin, on the S2GB stream). -/
theorem harChkB20_sound (h : harChkBB20 = true) :
    Lvm.Har.TdOk tdataB20 NTB20.toN ∧
      typedEndL tdataB20 P20B = posOf P20B (phaseItem0 P20B .tape) ∧
      typedEndL tdataB20 P20B + 40 ≤ 8 * streamLanes P20B ∧
      posOf P20B (phaseItem0 P20B .openMain) + 48 ≤ 8 * streamLanes P20B ∧
      (∀ a ∈ powB20, a.1 + 2 < streamLanes P20B ∧ a.2 ≤ 64) ∧
      posOf P20B (phaseItem0 P20B .openMain) = 8 * (phaseLane P20B .openMain 0 - 5) ∧
      Lvm.Har.LayOkB (cfgMainF P20B (fun _ => 0) (fun _ => 0)) (some P20B) (streamLanes P20B) = true ∧
      8 * Lvm.Har.stackEndL P20B.grind P20B.mainOod P20B.mainLevels (phaseLane P20B .openMain 0 - 5 + 15)
        (some P20B) = hashedLen P20B ∧
      P20B.mainLevels.length ≤ (Lvm.QLink.opens P20B).length ∧ 1 ≤ 64 - P20B.grind ∧
      Lvm.Fin.PosLanes P20B P20B.grind P20B.mainOod P20B.mainLevels (phaseLane P20B .openMain 0 - 5 + 15) 0
        (some P20B) ∧
      typedRegB tdataB20 (layout0 P20B).s = true := by
  simp only [harChkBB20, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨Lvm.Har.tdOk_of h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

set_option maxRecDepth 100000 in
/-- The mini-bus record at S2GB (`miniS20`'s twin). -/
theorem miniB20 (S : NodeGB) : Lvm.M3.sumcheckTabs NTB20.toN.mbT = NTB20.toN.mbT ∧
    (Lvm.QTyped.tdataOf cfgB20 frzB20).mbS = NTB20.toN.mbT.map Lvm.M3.Tab.shape ∧
    (Lvm.QTyped.tdataOf cfgB20 frzB20).mbD = cfgB20.p.busDepth ∧
    Lvm.Har.FixListed NTB20.toN.mbT (Lvm.QTyped.tdataOf cfgB20 frzB20).mbFix := by
  have hsc : Lvm.M3.sumcheckTabs (mbTOf cfgB20 frzB20) = mbTOf cfgB20 frzB20 := Lvm.Har.mbT_sumcheck cfgB20 _ _ _
  have hm := S.st.mini
  rw [S.mb] at hm ⊢
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hD⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hm
  obtain ⟨t1, -, t3, t4⟩ := Lvm.Har.tdataOf_mb cfgB20 frzB20
  rw [t1, t3, t4, hD]
  exact ⟨hsc, rfl, rfl, Lvm.Har.mbT_fix cfgB20 _ _ _⟩

/-- Q_sig's pointer at S2GB (after `qlinkB`). -/
def p1PB (lay : Layout) (nK nE : ℕ) (p : Params) : Ptr := (p0 nK nE).adv (qlinkB p lay (p0 nK nE)).2

/-- At `capPrune`, `p1C` (the pointer of the `BITS` classes' Q_sig cells, `sigOut`) is `p1PB`. -/
theorem p1C_of_pr (C : QCfg) (h : C.p.capPrune = true) : p1C C = p1PB (lay C) (nK C) 0 C.p := by
  unfold p1C; rw [h]; rfl

/-- **The S2GB program's three parts hold** (`parts_of_holdsS` for `qlinkB; qsigSC; qa`). -/
theorem parts_of_holdsB {α : Type} {p : Params} {lay : Layout} {I I2 : SigIn} {qa : BM α} {nK nE : ℕ} {M : Mem}
    (hH : (toProgram nK nE (do qlinkB p lay; let _ ← qsigSC I I2; qa)).Holds M)
    (hA : (toProgram nK nE (do qlinkB p lay; let _ ← qsigSC I I2; qa)).Asserts M) :
    Ok (ctxOf (toProgram nK nE (do qlinkB p lay; let _ ← qsigSC I I2; qa))) M (qlinkB p lay) (p0 nK nE) ∧
      Ok (ctxOf (toProgram nK nE (do qlinkB p lay; let _ ← qsigSC I I2; qa))) M (qsigSC I I2) (p1PB lay nK nE p) ∧
      Ok (ctxOf (toProgram nK nE (do qlinkB p lay; let _ ← qsigSC I I2; qa))) M qa
        ((p1PB lay nK nE p).adv (qsigSC I I2 (p1PB lay nK nE p)).2) := by
  rw [toProgram_holds] at hH
  rw [toProgram_asserts] at hA
  have hh : SegsHold (ctxOf (toProgram nK nE (do qlinkB p lay; let _ ← qsigSC I I2; qa))) M (p0 nK nE)
      ((do qlinkB p lay; let _ ← qsigSC I I2; qa : BM α) (p0 nK nE)).2 := hH
  have ha : SegsAssert M (p0 nK nE) ((do qlinkB p lay; let _ ← qsigSC I I2; qa : BM α) (p0 nK nE)).2 := hA
  rw [hold_bind, hold_bind] at hh
  rw [assert_bind, assert_bind] at ha
  exact ⟨⟨hh.1, ha.1⟩, ⟨hh.2.1, ha.2.1⟩, ⟨hh.2.2, ha.2.2⟩⟩

/-- `cfgB20` is on S2GU's `C_main` layout. -/
theorem cfgU_B20 : CfgU cfgB20 := ⟨rfl, rfl, rfl, by decide, rfl, rfl, rfl⟩

/-- **CAP-FRZ C2**: **the node's cells on a good S2GB pair** (`inMapS20`'s twin, from the guard's input map, `qr` the
stream block of `qm`). -/
theorem inMapB20 (S : NodeGB) (H : THypSB TiB20) (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okSL vk c x = true → (hdrOf x).b = 1 → GoodTSB TiB20 H x qm qr ∧ SBlkU qm qr →
      InMapMBS (spongeBlocks P20B) (pubLanesS P20B) cfgB20 (memTX TiB20 Lvm.pubXTS x qm qr) vk x qm qr := by
  intro c x qm qr hok hb hG
  have hC := cfgU_B20
  have hreg : NTB20.toN.okB 23 19 = true := by have h := S.st.regs; rwa [hC.nm, hC.nr] at h
  have hσ : SigInSL CMain.sOffU20 NTB20.toN := by have h := S.sig; rwa [hC.s_eq] at h
  have hchk := S.chk
  simp only [nodeChkBGS, Bool.and_eq_true] at hchk
  have hB : spongeBlocks P20B ≤ 2 ^ 13 := by rw [sizes_P20B.1.2.2.2.2.1]; norm_num
  exact inMapTGLS cfgB20 hC _ _ NTB20.toN Pub.hdrLanesT QB20 layB20 Lvm.pubXTS S.st.hlay hreg S.st.hlayOk hσ
    hchk.1.1 hB (by decide) (by decide) rfl (by decide)
    (by rw [w2RowC, layC.2.2.2.2.2.2.2.2.2.1]; decide) (by rw [w2RowC, layC.2.2.2.2.2.2.2.2.2.1]; decide)
    (fun x _ hj ↦ pubXTS_lane x (lt_of_lt_of_le hj (by decide))) qm qr hG.2 hok hb

end Lvm.E2Q
