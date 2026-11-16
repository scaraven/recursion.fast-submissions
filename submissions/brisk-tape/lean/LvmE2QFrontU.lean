-- New for lvm2 U-TAPE (UT-C2, STMT 25a/25b): blob U's front for `harithU20`: the stream positions of `P20U` (one kernel
-- evaluation), the proof-of-work blocks on `specQU`'s layout, and the front's phases (`front_phasesU`: `frontU`
-- replays V_S's `tapeUDG rowSwitchDR P20U`, its claims stand for `frontItemsU`'s).
import LvmE2QHarGen
import LvmE2QTypedPhaseT
import LvmE2QAsmU
import LvmE2QInstU
import LvmE2UDec
import LvmS2GUPlan
import LvmE2QWUSem
import LvmQAsmHarTop

/-!
# Blob U's front (`harithU20`'s 25a, 25b)

* **Positions at `P20U`** (`posU20`, one kernel evaluation of the schedule's lanes): the root pin's (`hbU`, `pinHPU`,
  `pinQaU`, `pinEndU`) and the typed phases' (`busLanesB_P20U`).
* **`powOk_of_blksU`**: V's proof-of-work checks from `specQU`'s PoW blocks (`powOk_of_blks` with three row switches).
* **`front_phasesU`** (25b): from the front's rows and assertions (gate on), its PoW answers, the three row
  switches' words, `n'`'s bits and range and the bits of `s'`, V_S's merged tape `tapeUDG rowSwitchDR P20U` runs from
  the tape's first item to the opening's, and the front's claims stand for `frontItemsU`'s.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped

/-! ## Positions at `P20U` -/

set_option maxRecDepth 200000 in
/-- **`P20U`'s positions** (one kernel evaluation of the schedule's lanes): the pin's start after the cap, its first
answer, its value, its end at the typed phases, and the lanes of the phase `bus`. -/
theorem posU20 : startByte P20U + nodeBytes * 2 ^ (P20U.level ⟨.main, 0⟩).cap = posOf P20U 1 ∧
    posOf P20U 1 + 40 = 8 * phaseLane P20U .commit 1 ∧
    phaseLane P20U .commit (P20U.nuMain + 1) = phaseLane P20U .commit 1 + 9 * P20U.nuMain ∧
    posOf P20U 1 + 72 * P20U.nuMain + 24 = typedPosF P20U ∧ busLanesB P20U = true ∧
    ((∀ i < 20, 8 * phaseLane P20U .tape (2 + 2 * i) = posOf P20U (phaseItem0 P20U .tape) + 120 + 80 * i) ∧
      8 * phaseLane P20U .tape 41 = posOf P20U (phaseItem0 P20U .tape) + 1712 ∧
      8 * phaseLane P20U .tape 43 = posOf P20U (phaseItem0 P20U .tape) + 2520 ∧
      8 * phaseLane P20U .tape 45 = posOf P20U (phaseItem0 P20U .tape) + 2600 ∧
      posOf P20U (phaseItem0 P20U .wire) = 8 * Lvm.Q1.tapeEnd2 16 (phaseLane P20U .tape 45) - 40 ∧
      8 * phaseLane P20U .wire 0 = posOf P20U (phaseItem0 P20U .wire) + 40 ∧
      posOf P20U (phaseItem0 P20U .openMain) = posOf P20U (phaseItem0 P20U .wire) + 8216 ∧
      posOf P20U (phaseItem0 P20U .tape) % 8 = 0) := by
  unfold P20U P20T; rw [Lvm.Replay.P20_eq]; decide +kernel

theorem hbU : Lvm.Har.pos (RS.startH (headerBytesP P20U)) + nodeBytes * 2 ^ (P20U.level ⟨.main, 0⟩).cap =
    posOf P20U 1 := by
  rw [pos_startH]; exact posU20.1

theorem pinHPU : posOf P20U 1 + 40 = 8 * phaseLane P20U .commit 1 := posU20.2.1

theorem pinQaU : phaseLane P20U .commit (P20U.nuMain + 1) = phaseLane P20U .commit 1 + 9 * P20U.nuMain :=
  posU20.2.2.1

theorem pinEndU : posOf P20U 1 + 72 * P20U.nuMain + 24 = typedPosF P20U := posU20.2.2.2.1

theorem busLanesB_P20U : busLanesB P20U = true := posU20.2.2.2.2.1


/-! ## The proof-of-work blocks on `specQU`'s layout -/

/-- **V's proof-of-work checks from `specQU`'s PoW blocks** (`powOk_of_blks` with the three row switches' blocks
before the PoW words). -/
theorem powOk_of_blksU (C : QCfg) {Q : Program} {tl : Typed.Lay} {z : ℕ → FK} {pw : List (ℕ × ℕ)}
    {d : Array (Ty × ℕ × ℕ)} (hl : tl = (mkLayD Q (specQU C Q pw) d).1) (hlay : tl.Ok Q)
    (hone : z tl.one = 1) (h : WiringRelX Q tl z) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memOf tl z) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ pw)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L := by
  intro a ha
  obtain ⟨q, g⟩ := a
  have hapw := hL _ ha
  obtain ⟨hq, hg⟩ := hpw _ ha
  obtain ⟨f, hf⟩ := aux_mkLayD Q (specQU C Q pw) d
  set n := (specQ C Q).auxWords.length with hn
  have haux : tl.aux = (specQ C Q).auxOf f ++
      (Lvm.Q2.rowAuxL (f n) (tBu C 0) (Lvm.Q2.wireLanesU C.p.logN (phaseLane C.p .wire 0)).slicesD ++
        Lvm.Q2.rowAuxL (f (n + 1)) (tBu C 1) (Lvm.Q2.wireLanesU C.p.logN (phaseLane C.p .wire 0)).slicesY ++
        Lvm.Q2.rowAuxL (f (n + 2)) (tBu C 2) (Lvm.Q2.wireLanesU C.p.logN (phaseLane C.p .wire 0)).slicesM) ++
      powBlksL (f (n + 3)) pw := by rw [hl, hf]; rfl
  set bw := f (n + 3) with hbw
  have hP : ∀ B ∈ powBlksL bw pw, B ∈ tl.aux := fun B hB => by rw [haux]; exact List.mem_append_right _ hB
  obtain ⟨bw', h1, h2, hb⟩ := powRecRows_mem bw pw hapw
  have hrows : ∀ r ∈ (Lvm.Q2.powBlk g bw' q).rows, ARowHolds tl z 0 r := by
    intro r hr
    rw [Lvm.Q2.powBlk, powRangeRows] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      rw [List.mem_range] at hi
      obtain ⟨a, b, hB, hb1, hb2⟩ := boolRuns_cover bw (Lvm.Q2.powWords pw) ((Lvm.Q2.powWords pw).log2 + 1)
        (bw' + i - bw) (by rw [Nat.mod_eq_of_lt Nat.lt_log2_self]; omega) (by omega)
      have hBm : (⟨a, [Lvm.Q2.rowBoolL b]⟩ : ABlk) ∈ tl.aux := hP _ (List.mem_append_left _ hB)
      have hj : bw' + i - b < 2 ^ a := by omega
      refine (Lvm.Q2.aRowHolds_congr ?_).mpr (auxRow_mem hlay hone h hBm List.mem_cons_self hj)
      simp only [Lvm.Q2.aRowVals, Lvm.Q2.rowBoolL, List.map_cons, List.map_nil, aopVal, Nat.mul_zero, Nat.add_zero,
        Nat.one_mul, show b + (bw' + i - b) = bw' + i by omega]
    · rw [List.mem_singleton] at hr
      subst hr
      exact auxRow_mem hlay hone h (hP _ (List.mem_append_right _ List.mem_cons_self)) hb (by simp)
  have hc : (memOf tl z).k (q + 2) = (feAt sig (8 * q)).c₂ := by
    rw [hS _ hq]
    show kAt sig (8 * (q + 2)) = kAt sig (8 * q + 16)
    rw [show 8 * (q + 2) = 8 * q + 16 by ring]
  exact Lvm.Q2.powBlk_ok tl z hg hc hrows


/-! ## V's S2GU wire by phases -/

section WirePh

open Lvm.Q2 DM

/-- **A plain sumcheck of `R` rounds at `E2`** from `P` (first message at lane `q`, `8 q = P + 40`), its challenges'
proof of work passing: the points are the stream's answers, the final claim the stream's fold. -/
theorem sumcheckD_phase {sig : ByteArray} {R q P : ℕ} {claim : FE2} (hq : 8 * q = P + 40)
    (hpow : ∀ k < R, powOKR E2V.gC2 (feAt sig (P + 80 + 112 * k)) = true) :
    PhaseAt (sumcheckD E2V.gC2 claim 3 (List.replicate R none)) sig P (P + 112 * R)
      ((List.range R).map (fun k => fe2At sig (P + 80 + 112 * k)), scFold2 (fun k => fe2At sig (8 * k)) R q claim) := by
  intro s hs hok
  have hs' : rpos s = P := hs
  obtain ⟨u1, u2, u3⟩ := sumcheckD_run E2V.gC2 sig R claim s q (by rw [hs']; exact hq)
  exact ⟨by rw [u1, hs'], by rw [u3, okS_true _ _ (by rw [hs']; exact hpow), hok]; rfl,
    by show rpos _ = _; rw [u2, hs']⟩

theorem rowSwitchDR_run (zz sv : List FE2) (sig : ByteArray) (s : RS) :
    (rowSwitchDR zz sv sig s).1 = (rowSwitchDR zz sv sig ⟨rpos s, 0, true⟩).1 ∧
      (rowSwitchDR zz sv sig s).2 = ⟨rpos s + 504, 0, s.ok⟩ := by
  unfold rowSwitchDR
  rw [dbind_run, dbind_run, Lvm.Q1.samples_run sig 7 s (by norm_num), Lvm.Q1.samples_run sig 7 _ (by norm_num)]
  exact ⟨rfl, rfl⟩

/-- **A row switch's phase** (data form): from `P`, `P + 504`, its value the run from the bare cursor at `P`. -/
theorem rowSwitchDR_phase {sig : ByteArray} {P : ℕ} (zz sv : List FE2) :
    PhaseAt (rowSwitchDR zz sv) sig P (P + 504) (rowSwitchDR zz sv sig ⟨P, 0, true⟩).1 := by
  intro s hs hok
  have hs' : rpos s = P := hs
  obtain ⟨h1, h2⟩ := rowSwitchDR_run zz sv sig s
  rw [hs'] at h1 h2
  exact ⟨h1, by rw [h2]; exact hok, by rw [h2]; rfl⟩

/-- **A slot reduction's phase** (`slotDFG rowSwitchDR`): `b` rounds from `P` (first message lane `q`), the 64
slices, the slot check (`hchk`, on the stream's values), the row switch. -/
theorem slotDFG_phase {sig : ByteArray} {b sb blk q P : ℕ} {W : ℕ → ℕ → FE2} {pt : List FE2} {v : FE2}
    (hq : 8 * q = P + 40) (hpow : ∀ k < b, powOKR E2V.gC2 (feAt sig (P + 80 + 112 * k)) = true)
    (hchk : scFold2 (fun k => fe2At sig (8 * k)) b q v = E2V.sumF ((List.range 64).map fun z =>
      E2V.slotWF b W ((List.range b).map (fun k => fe2At sig (P + 80 + 112 * k))) z *
        (readsE2 sig (P + 112 * b) 64).getD z 0)) :
    PhaseAt (slotDFG rowSwitchDR b sb blk W pt v) sig P (P + 112 * b + 1024 + 504)
      ((((List.range b).map (fun k => fe2At sig (P + 80 + 112 * k)), scFold2 (fun k => fe2At sig (8 * k)) b q v),
        readsE2 sig (P + 112 * b) 64,
        (rowSwitchDR (pt ++ (List.range b).map (fun k => fe2At sig (P + 80 + 112 * k)) ++ Lvm.E2V.selPtF blk sb)
          (readsE2 sig (P + 112 * b) 64) sig ⟨P + 112 * b + 1024, 0, true⟩).1)) := by
  unfold slotDFG
  refine phaseAt_bind (sumcheckD_phase hq hpow) (phaseAt_bind readE2s_phase (phaseAt_bind
    (phaseAt_require (by rw [beq_iff_eq]; exact hchk)) ?_))
  rw [show P + 112 * b + 16 * 64 = P + 112 * b + 1024 by ring]
  exact phaseAt_bind (rowSwitchDR_phase _ _) phaseAt_pure

/-- The `E2` points of `R` sumcheck rounds from `P`. -/
def scPts (sig : ByteArray) (P R : ℕ) : List FE2 := (List.range R).map fun k => fe2At sig (P + 80 + 112 * k)

set_option maxHeartbeats 1000000 in
/-- **V's S2GU wire by phases** (`wireUDG rowSwitchDR`, `w = 20`, from `P`, first message lane `q`): the wire
sumcheck, `g_D, g_Y, g_M`, the final check (`hfin`), the slot reductions of `D` (2 rounds, from `P + 2288`), `Y`
(5, from `+ 1752`) and `M` (5, from `+ 2088`) with their checks. -/
theorem wireUDG_phase {sig : ByteArray} {q P : ℕ} (p : Params) (hw : p.logN = 20) (hk : p.ksLog = 13) (s : List FK)
    (n : ℕ) (claim : E2V.KClaim FE2) (hq : 8 * q = P + 40)
    (hpw : ∀ k < 20, powOKR E2V.gC2 (feAt sig (P + 80 + 112 * k)) = true)
    (hpD : ∀ k < 2, powOKR E2V.gC2 (feAt sig (P + 2288 + 80 + 112 * k)) = true)
    (hpY : ∀ k < 5, powOKR E2V.gC2 (feAt sig (P + 4040 + 80 + 112 * k)) = true)
    (hpM : ∀ k < 5, powOKR E2V.gC2 (feAt sig (P + 6128 + 80 + 112 * k)) = true)
    (hfin : scFold2 (fun k => fe2At sig (8 * k)) 20 q (wireTargetDF (sBitsD s) n claim) =
      E2V.msEvalF claim.point claim.mu (scPts sig P 20) 0 (n - 1) * fe2At sig (P + 2280) +
        Lvm.E2U.eTailF 13 20 (scPts sig P 20) *
          (Lvm.E2U.kksF Lvm.E2U.contIvU claim.point claim.mu ((scPts sig P 20).take 13) (2 ^ 20) *
              fe2At sig (P + 2296) +
            E2V.ikEvalP claim.point claim.mu ((scPts sig P 20).take 13) (2 ^ 20) * fe2At sig (P + 2312)))
    (hD : scFold2 (fun k => fe2At sig (8 * k)) 2 ((P + 2288 + 40) / 8) (fe2At sig (P + 2280)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 2 (dWA claim.weights.toArray) (scPts sig (P + 2288) 2) z *
        (readsE2 sig (P + 2288 + 112 * 2) 64).getD z 0))
    (hY : scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 4040 + 40) / 8) (fe2At sig (P + 2296)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.yWG claim.weights) (scPts sig (P + 4040) 5) z *
        (readsE2 sig (P + 4040 + 112 * 5) 64).getD z 0))
    (hM : scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 6128 + 40) / 8) (fe2At sig (P + 2312)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.mWG claim.weights) (scPts sig (P + 6128) 5) z *
        (readsE2 sig (P + 6128 + 112 * 5) 64).getD z 0)) :
    PhaseAt (Lvm.E2U.wireUDG rowSwitchDR p s n claim) sig P (P + 8216)
      ⟨(scPts sig P 20, scFold2 (fun k => fe2At sig (8 * k)) 20 q (wireTargetDF (sBitsD s) n claim)),
        readsE2 sig (P + 2240) 3,
        ((scPts sig (P + 2288) 2, scFold2 (fun k => fe2At sig (8 * k)) 2 ((P + 2288 + 40) / 8) (fe2At sig (P + 2280))),
          readsE2 sig (P + 2288 + 112 * 2) 64,
          (rowSwitchDR (scPts sig P 20 ++ scPts sig (P + 2288) 2 ++ Lvm.E2V.selPtF (dSel p) (dSelBits p))
            (readsE2 sig (P + 2288 + 112 * 2) 64) sig ⟨P + 2288 + 112 * 2 + 1024, 0, true⟩).1),
        ((scPts sig (P + 4040) 5, scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 4040 + 40) / 8) (fe2At sig (P + 2296))),
          readsE2 sig (P + 4040 + 112 * 5) 64,
          (rowSwitchDR ((scPts sig P 20).take 13 ++ scPts sig (P + 4040) 5 ++
              Lvm.E2V.selPtF ((layout0 p).ks / 2 ^ (p.ksLog + 5)) (p.nuMain - (p.ksLog + 5)))
            (readsE2 sig (P + 4040 + 112 * 5) 64) sig ⟨P + 4040 + 112 * 5 + 1024, 0, true⟩).1),
        ((scPts sig (P + 6128) 5, scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 6128 + 40) / 8) (fe2At sig (P + 2312))),
          readsE2 sig (P + 6128 + 112 * 5) 64,
          (rowSwitchDR ((scPts sig P 20).take 13 ++ [0] ++ scPts sig (P + 6128) 5 ++
              Lvm.E2V.selPtF ((layout0 p).s / 2 ^ p.nuRec) (p.nuMain - p.nuRec))
            (readsE2 sig (P + 6128 + 112 * 5) 64) sig ⟨P + 6128 + 112 * 5 + 1024, 0, true⟩).1)⟩ := by
  unfold Lvm.E2U.wireUDG
  rw [hw, hk]
  simp only [Lvm.E2U.slotBitsU]
  refine phaseAt_bind (sumcheckD_phase hq hpw) (phaseAt_bind readE2s_phase (phaseAt_bind
    (phaseAt_require ?_) ?_))
  · have g0 : (readsE2 sig (P + 112 * 20) 3).getD 0 0 = fe2At sig (P + 2280) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g1 : (readsE2 sig (P + 112 * 20) 3).getD 1 0 = fe2At sig (P + 2296) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g2 : (readsE2 sig (P + 112 * 20) 3).getD 2 0 = fe2At sig (P + 2312) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    dsimp only
    rw [beq_iff_eq, g0, g1, g2]
    exact hfin
  · have hP8 : P % 8 = 0 := by omega
    have e1 : P + 112 * 20 + 16 * 3 = P + 2288 := by ring
    have hr : readsE2 sig (P + 112 * 20) 3 = readsE2 sig (P + 2240) 3 := by rw [show 112 * 20 = 2240 by rfl]
    dsimp only
    rw [e1, hr]
    have g0 : (readsE2 sig (P + 2240) 3).getD 0 0 = fe2At sig (P + 2280) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g1 : (readsE2 sig (P + 2240) 3).getD 1 0 = fe2At sig (P + 2296) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g2 : (readsE2 sig (P + 2240) 3).getD 2 0 = fe2At sig (P + 2312) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    rw [g0, g1, g2]
    refine phaseAt_bind (slotDFG_phase (q := (P + 2288 + 40) / 8) (by omega) hpD hD) ?_
    rw [show P + 2288 + 112 * 2 + 1024 + 504 = P + 4040 by ring, Lvm.E2U.slotDFW_yWG]
    refine phaseAt_bind (slotDFG_phase (q := (P + 4040 + 40) / 8) (by omega) hpY hY) ?_
    rw [show P + 4040 + 112 * 5 + 1024 + 504 = P + 6128 by ring, Lvm.E2U.slotDFW_mWG,
      show Lvm.E2U.slotBitsU = 5 from rfl]
    refine phaseAt_bind (slotDFG_phase (q := (P + 6128 + 40) / 8) (by omega) hpM hM) ?_
    rw [show P + 6128 + 112 * 5 + 1024 + 504 = P + 8216 by ring]
    exact phaseAt_pure

/-- **One ground challenge's phase** (`sampleG g` from `P`: its nonce, its answer at `P + 48`). -/
theorem sampleG_phase {sig : ByteArray} {g P : ℕ} (hpow : powOKR g (feAt sig (P + 48)) = true) :
    PhaseAt (sampleG g) sig P (P + 80) (fe2At sig (P + 48)) := by
  intro s hs hok
  have hs' : s.ent + s.msg = P := hs
  rw [sampleG_run]
  refine ⟨?_, ?_, ?_⟩
  · show e2OfFE (feAt sig (s.ent + 40 + (s.msg + 8))) = _
    rw [show s.ent + 40 + (s.msg + 8) = P + 48 by omega]; rfl
  · show (powOKR g (feAt sig (s.ent + 40 + (s.msg + 8))) && s.ok) = true
    rw [show s.ent + 40 + (s.msg + 8) = P + 48 by omega, hpow, hok]; rfl
  · show s.ent + 72 + (s.msg + 8) + 0 = P + 80
    omega

set_option maxHeartbeats 1000000 in
/-- **V's merged tape by phases** (`tapeUDG rowSwitchDR`, `w = 20`, from `P`): the separator, `r_{<20}` (answers
`8 q₀ = P + 120`), the 50 scalars, `r₂₀` (answer at `P + 2520`), the GKR on T1's values (`htg`, from `P + 2552`),
`n`'s range, the wire (`hwire`). -/
theorem tapeUDG_phase {sig : ByteArray} {q0 P P5 P6 : ℕ} (p : Params) (hw : p.logN = 20) (hk : p.ksLog = 13)
    (s : List FK) (n : ℕ) {claim : E2V.KClaim FE2} {wo : Lvm.E2U.WireU RowZ} (hq0 : 8 * q0 = P + 120)
    (hpowR : Lvm.Q1.PowOkV (feAt sig) (chalsG q0 E2V.gC1 20))
    (hpow20 : powOKR E2V.gC1 (feAt sig (P + 2520)) = true)
    (htg : PhaseAt (tapeGkrDF 21 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)])
      (Lvm.E2U.t1ValsF 20 13 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50)))
      sig (P + 2552) P5 claim)
    (hn : 1 ≤ n ∧ n ≤ 2 ^ 20) (hwire : PhaseAt (Lvm.E2U.wireUDG rowSwitchDR p s n claim) sig P5 P6 wo) :
    PhaseAt (Lvm.E2U.tapeUDG rowSwitchDR p s n) sig P P6
      ⟨sampsG sig (P + 72) 20, fe2At sig (P + 2520), readsE2 sig (P + 1672) 50, claim, wo⟩ := by
  unfold Lvm.E2U.tapeUDG
  rw [hw, hk]
  refine phaseAt_bind sepE2_phase (phaseAt_bind (samplesG_phase (by omega) hpowR) (phaseAt_bind readE2s_phase ?_))
  rw [show P + 72 + 80 * 20 + 16 * (2 * 25) = P + 2472 by ring,
    show P + 72 + 80 * 20 = P + 1672 by ring]
  refine phaseAt_bind (sampleG_phase (by rw [show P + 2472 + 48 = P + 2520 by ring]; exact hpow20)) ?_
  rw [show P + 2472 + 48 = P + 2520 by ring, show P + 2472 + 80 = P + 2552 by ring]
  exact phaseAt_bind htg (phaseAt_bind (phaseAt_require (decide_eq_true hn)) (phaseAt_bind hwire phaseAt_pure))

/-- The tape GKR's layer template at `P = 16` (`logN + 1 = 21` row bits). -/
theorem layOk2_16 : Lvm.Q1.layOk2 16 = true := by
  rw [Lvm.Q1.layOk2_eq_lit, Lvm.Q1.layerTB2T_eq_F, Lvm.Q1.layOk2T_eq_R]; decide +kernel

/-- **The merged tape's GKR phase** (E2F-QH4's `tape_phase2` at `P = 16`): V's `tapeGkrDF 21` on `r ‖ r₂₀` and T1's
values runs from `P + 2552` to the wire, and the gadget's carried cells represent its claim. -/
theorem tapeGkr_phaseU {c : Ctx} {M : Mem} {sig : ByteArray} {T : ℕ} (hS : Lvm.Q1.Streamed M sig T) {P qs : ℕ}
    {inst out : ℕ → C2} {b : Cell} {p : Ptr} (hqs : 8 * qs = P + 2600) (hT : Lvm.Q1.tapeEnd2 16 qs + 2 ≤ T)
    (hh : SegsHold c M p (Lvm.Q1.tapeGadgetE2 16 qs inst out b p).2)
    (ha : SegsAssert M p (Lvm.Q1.tapeGadgetE2 16 qs inst out b p).2) (hb : b.val M = 1)
    (hpow : Lvm.Q1.PowOkV (feAt sig) (Lvm.Q1.tapeChals2 16 qs))
    (hinst : (List.range (16 + 5)).map (fun i => (inst i).val M) = sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)])
    (hout : (List.range 25).map (fun l => (out l).val M) = Lvm.E2U.t1ValsF 20 13
      (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50)) :
    PhaseAt (tapeGkrDF 21 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (Lvm.E2U.t1ValsF 20 13
        (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50))) sig (P + 2552)
      (8 * Lvm.Q1.tapeEnd2 16 qs - 40)
      (tapeGkrD 21 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (Lvm.E2U.t1ValsF 20 13
        (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50)) sig ⟨P + 2552, 0, true⟩).1 ∧
    Lvm.Q1.Rep2 16 (fun j => ((Lvm.Q1.tapeGadgetE2 16 qs inst out b p).1.cv j).val M)
      (tapeGkrD 21 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (Lvm.E2U.t1ValsF 20 13
        (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50)) sig ⟨P + 2552, 0, true⟩).1
      false := by
  have h := Lvm.Q1.tape_phase2 layOk2_16 (by omega) hS hT hh ha hb hpow
  rw [hinst, hout, show 8 * qs - 48 = P + 2552 by omega] at h
  rw [tapeGkrDF_eq]
  exact h

end WirePh

/-! ## The front's phases at `P20U` (25b) -/

/-- The lanes of `CHwire` at `P20U` (the slices of the three slot reductions, the row switches' answers). -/
abbrev wlU : Lvm.Q2.WireLanesU := Lvm.Q2.wireLanesU P20U.logN (phaseLane P20U .wire 0)

section FrontU

open Lvm.Q2 Lvm.QShape

variable {M : Mem}

/-- **`frontU`'s claims** from its gadgets' outputs as variables (`frontU`'s list). -/
def frontCsU (p : Params) (F : FCtx) (r a b : List C2) (wo : WireOutU) (rD : RowOut) (nuD : RowNu) (rY : RowOut)
    (nuY : RowNu) (rM : RowOut) (nuM : RowNu) (mbE : List Cell) : List FClaim :=
  let L := layout0 p
  let blkD := dBlock p
  let sg' := wo.sigma.take p.ksLog
  let dw : List FClaim :=
    (List.range dLanes).flatMap fun l =>
      let zl := r ++ selC2 F l 2
      let vl := a.getD l default
      [.dhalf false zl vl.re, .dhalf true zl vl.im]
  let yw : List FClaim := (List.range 25).flatMap fun l =>
    halves [(F.o2, (⟨p.ksLog, L.ks + l * 2 ^ p.ksLog⟩ : Placement), r.take p.ksLog)] (b.getD l default)
  let rows : List FClaim :=
    [.drow (wo.sigma ++ wo.tauD ++ selC2 F (dSel p) (dSelBits p)) nuD rD.target,
     .row ⟨p.ksLog + 5, L.ks⟩ (sg' ++ wo.tauY) nuY rY.target,
     .row ⟨p.recRowsLog + 5, L.s⟩ (sg' ++ [F.z2] ++ wo.tauM) nuM rM.target]
  let hs : List FClaim :=
    (List.range 4).map fun l => .e3 ⟨.main, .point blkD (mbE ++ Lvm.Har.selC F.z.n F.o.n l 2), kc (hLane l)⟩
  dw ++ yw ++ rows ++ hs

theorem dSel_P20U' : dSel P20U = 0 := by unfold dSel; rw [layout0_P20U]; rfl

theorem dBlock_P20U' : dBlock P20U = ⟨22, 0⟩ := by unfold dBlock; rw [layout0_P20U]; rfl

theorem regY_P20U {l : ℕ} (hl : l < 25) : RegP ⟨13, CMain.yOffU20 + l * 2 ^ 13⟩ := by
  unfold RegP
  simp only [CMain.yOffU20, CMain.nu20]
  refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> (clear * - hl; omega)

/-- A row switch's data with its point `z ++ s`, on its first `|z|` coordinates, weighs V's `rowW`. -/
theorem takeC_w (z s : List FE2) (tgt : FE) (eqR : List FE) {k : ℕ} (hk : z.length = k) :
    (RowR.takeC k ⟨tgt, (z ++ s).map tColsW, eqR.toArray, eqR⟩).w = rowW eqR z := by
  funext x
  unfold RowR.takeC RowR.w
  rw [List.map_append, List.take_append_of_le_length (by rw [List.length_map]; omega),
    List.take_of_length_le (by rw [List.length_map]; omega), tensorDotT_eq]
  rfl

/-- **A row claim on a block** stands for V's block row (`RowK`'s item: the row's data on the block's coordinates). -/
theorem row_rel {zc : Cell} {b : Bool} {blk : Placement} {z : List C2} {nu : RowNu} {v : Cell} {eqR : List FE}
    {s : List FE2} (hnu : RowNuOk M nu eqR) (hzK : ∀ x ∈ z, KC2 x) (hzl : z.length = blk.variableCount)
    (hne : z ≠ []) (hk : blk.variableCount ≤ CMain.nu20) (hR : RegP blk) (R : RowZ)
    (hRv : R.1 = ⟨v.val M, (z.map (C2.val M) ++ s).map tColsW, eqR.toArray, eqR⟩) :
    FRelZ M zc b (.row blk z nu v)
      (.main, ⟨blk, (R.1.takeC blk.variableCount).w, (R.1.takeC blk.variableCount).tgt⟩, 0) := by
  refine ⟨⟨rfl, eqR, hnu, hne, hzK, hzl, hk, ?_⟩, hR, rfl⟩
  rw [hRv, takeC_w _ _ _ _ (by rw [List.length_map]; exact hzl)]
  rfl

/-- An `E2` split item's claims are `splitD`'s halves with its tails. -/
theorem split_flat (nu : ℕ) (parts : List (FE2 × Placement × List FE2)) (v : FE2) (t0 t1 : FE) :
    (FItem.split nu parts v t0 t1).flat = ((splitD nu parts v).zip [t0, t1]).map fun e => (Com.main, e.1, e.2) := by
  simp only [FItem.flat, splitRe, splitIm, splitD, sumW6DF_eq, List.zip_cons_cons, List.zip_nil_right,
    List.map_cons, List.map_nil]

theorem split_flat0 (nu : ℕ) (parts : List (FE2 × Placement × List FE2)) (v : FE2) :
    (FItem.split nu parts v 0 0).flat = splitZ nu parts v := by
  simp only [FItem.flat, splitRe, splitIm, splitZ, splitD, sumW6DF_eq, List.map_cons, List.map_nil]

theorem tailDE2_two (r : List FE2) (l : ℕ) : tailDE2 r l = [(tailDE2 r l).getD 0 0, (tailDE2 r l).getD 1 0] := rfl

theorem flatMap_map_eq {α β γ : Type} (f : α → β) (g : β → List γ) (l : List α) :
    (l.map f).flatMap g = l.flatMap fun a => g (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]

theorem nu_P20U : P20U.nuMain = CMain.nu20 := rfl
theorem ksLog_P20U : P20U.ksLog = 13 := rfl
theorem logN_P20U : P20U.logN = 20 := rfl

theorem rowR_w (z : List FE2) (tgt : FE) (eqR : List FE) :
    (⟨tgt, z.map tColsW, eqR.toArray, eqR⟩ : RowR).w = rowW eqR z :=
  funext fun x => tensorDotT_eq z eqR x

theorem rowItemK_flat (nu : ℕ) (blk : Placement) (R : RowZ) (t : FE) :
    (Lvm.E2U.RowK.rowItemK nu blk R t).flat =
      [(.main, ⟨blk, (R.1.takeC blk.variableCount).w, (R.1.takeC blk.variableCount).tgt⟩, t)] := rfl

theorem rowAccR_eqR (R : RowZ) : rowAccR.eqR R = R.1.eqR := rfl

theorem rowAccR_flat (blk : Placement) (R : RowZ) (t : FE) :
    (rowAccR.rowItem blk R t).flat = [(.main, ⟨blk, R.1.w, R.1.tgt⟩, t)] := rfl

theorem regRows_P20U : RegP ⟨P20U.ksLog + 5, (layout0 P20U).ks⟩ ∧ RegP ⟨P20U.recRowsLog + 5, (layout0 P20U).s⟩ := by
  rw [layout0_P20U, ksLog_P20U, show P20U.recRowsLog = 14 from rfl]
  unfold RegP
  simp only [CMain.yOffU20, CMain.sOffU20, CMain.nu20]
  decide

set_option maxHeartbeats 1000000 in
/-- **`frontU`'s claims stand for V's** (`frontItemsU rowAccR P20U pub tp`'s claims), from the front gadgets' outputs
as variables: `D`'s word halves, the `Y` block's word halves, the three row claims, the boundary claims. -/
theorem front_claimsU {zc : Cell} {b : Bool} {pub : Pub} {F : FCtx} {r a bb : List C2} {wo : WireOutU}
    {rD rY rM : RowOut} {nuD nuY nuM : RowNu} {mbE : List Cell} {tp : Lvm.E2U.TapeU RowZ} {eqD eqY eqM : List FE}
    (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (hz2K : KC2 F.z2) (ho2K : KC2 F.o2) (hzE : M.e F.z.n = 0)
    (hoE : M.e F.o.n = 1)
    (hr : ∀ x ∈ r, KC2 x) (hrl : r.length = 20) (ha : ∀ l < 4, KC2 (a.getD l default))
    (hb : ∀ l < 25, KC2 (bb.getD l default))
    (htr : tp.r = r.map (C2.val M)) (hta : ∀ l < 4, tp.ab.getD l 0 = (a.getD l default).val M)
    (htb : ∀ l < 25, tp.ab.getD (25 + l) 0 = (bb.getD l default).val M)
    (hsgK : ∀ x ∈ wo.sigma, KC2 x) (hsgl : wo.sigma.length = 20) (hdK : ∀ x ∈ wo.tauD, KC2 x)
    (hdl : wo.tauD.length = 2) (hyK : ∀ x ∈ wo.tauY, KC2 x) (hyl : wo.tauY.length = 5)
    (hmK : ∀ x ∈ wo.tauM, KC2 x) (hml : wo.tauM.length = 5)
    (hsc : tp.wo.sc.1 = wo.sigma.map (C2.val M)) (htd : tp.wo.d.1.1 = wo.tauD.map (C2.val M))
    (hRD : tp.wo.d.2.2.1 = ⟨rD.target.val M, (wo.sigma.map (C2.val M) ++ wo.tauD.map (C2.val M) ++
      E2V.selPtF (dSel P20U) (dSelBits P20U)).map tColsW, eqD.toArray, eqD⟩) (hnuD : RowNuOk M nuD eqD)
    {sY sM : List FE2}
    (hRY : tp.wo.y.2.2.1 = ⟨rY.target.val M, ((wo.sigma.map (C2.val M)).take 13 ++ wo.tauY.map (C2.val M) ++ sY).map
      tColsW, eqY.toArray, eqY⟩) (hnuY : RowNuOk M nuY eqY)
    (hRM : tp.wo.m.2.2.1 = ⟨rM.target.val M, ((wo.sigma.map (C2.val M)).take 13 ++ [0] ++ wo.tauM.map (C2.val M) ++
      sM).map tColsW, eqM.toArray, eqM⟩) (hnuM : RowNuOk M nuM eqM)
    (hmbE : vs M mbE = selectorPoint (pub.n - 1) 20) (hh : pub.h = (List.range 4).map fun l => M.k (hLane l))
    (hsm : b = true → pub.n ≤ 2 ^ 18) (hn : 1 ≤ pub.n) :
    List.Forall₂ (FRelZ M zc b) (frontCsU P20U F r a bb wo rD nuD rY nuY rM nuM mbE)
      ((Lvm.E2U.frontItemsU rowAccR P20U pub tp).flatMap FItem.flat) := by
  have hdS : dSel P20U = 0 := dSel_P20U'
  have hdB : dSelBits P20U = 1 := rfl
  have hdBl : dBlock P20U = ⟨22, 0⟩ := dBlock_P20U'
  have hdL : dLanes = 4 := rfl
  unfold frontCsU Lvm.E2U.frontItemsU
  simp only [List.flatMap_append]
  rw [nu_P20U]
  refine List.rel_append (List.rel_append (List.rel_append ?_ ?_) ?_) ?_
  · -- `D`'s word claims
    rw [flatMap_map_eq, hdBl, hdL]
    have e : ∀ l, (FItem.split CMain.nu20 [(1, (⟨22, 0⟩ : Placement), tp.r ++ E2V.selPtF l 2)] (tp.ab.getD l 0)
        ((tailDE2 tp.r l).getD 0 0) ((tailDE2 tp.r l).getD 1 0)).flat =
        ((splitD 23 [(1, ⟨22, 0⟩, tp.r ++ E2V.selPtF l 2)] (tp.ab.getD l 0)).zip (tailDE2 tp.r l)).map
          fun e => (Com.main, e.1, e.2) := fun l => by
      rw [split_flat, ← tailDE2_two]
    simp only [e]
    exact dhalves_rel hz2 ho2 hz2K ho2K hr hrl ha htr hta
  · -- the `Y` block's word claims
    rw [flatMap_map_eq]
    refine forall₂_flatMap _ fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [split_flat0]
    refine halves_rel ?_ ?_ (hb l hl') (htb l hl').symm
    · simp only [List.mem_singleton, forall_eq]
      refine ⟨ho2K, fun x hx => hr x (List.mem_of_mem_take hx), ?_, ?_, ?_⟩
      · simp [hrl, ksLog_P20U]
      · show P20U.ksLog ≤ CMain.nu20; rw [ksLog_P20U]; decide
      · rw [layout0_P20U, ksLog_P20U]; exact regY_P20U hl'
    · simp only [partsV, List.map_cons, List.map_nil, ho2, htr, List.map_take]
  · -- the row claims
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, rowAccR_flat,
      rowItemK_flat, rowItemK_flat]
    have hsg : (wo.sigma.take P20U.ksLog).map (C2.val M) = (wo.sigma.map (C2.val M)).take 13 := by
      rw [List.map_take, ksLog_P20U]
    have hsgK' : ∀ x ∈ wo.sigma.take P20U.ksLog, KC2 x := fun x hx => hsgK x (List.mem_of_mem_take hx)
    have hsgl' : (wo.sigma.take P20U.ksLog).length = 13 := by rw [List.length_take, hsgl, ksLog_P20U]; rfl
    refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
    · have hzz : (wo.sigma ++ wo.tauD ++ selC2 F (dSel P20U) (dSelBits P20U)).map (C2.val M) =
          wo.sigma.map (C2.val M) ++ wo.tauD.map (C2.val M) ++ E2V.selPtF (dSel P20U) (dSelBits P20U) := by
        simp only [List.map_append, selC2_vals hz2 ho2]
      have hzl : (wo.sigma ++ wo.tauD ++ selC2 F (dSel P20U) (dSelBits P20U)).length = CMain.nu20 := by
        simp only [List.length_append, hsgl, hdl, selC2_length, hdB]
      have hzK : ∀ x ∈ wo.sigma ++ wo.tauD ++ selC2 F (dSel P20U) (dSelBits P20U), KC2 x := fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · rcases List.mem_append.mp h with h | h
          · exact hsgK x h
          · exact hdK x h
        · exact selC2_K hz2K ho2K _ _ x h
      refine ⟨⟨rfl, eqD, hnuD, ?_, hzK, hzl, le_refl _, ?_⟩, ?_, eqD, hnuD, ?_⟩
      · intro e; rw [e] at hzl; simp at hzl
      · rw [hRD, rowR_w, hzz]
      · rw [hzz, List.getD_append_right _ _ _ _ (by simp [hsgl, hdl]), hdS, hdB]
        simp [hsgl, hdl, E2V.selPtF]
      · rw [rowAccR_eqR, hRD, hsc, htd, hzz]
    · refine row_rel (blk := ⟨P20U.ksLog + 5, (layout0 P20U).ks⟩) (s := sY) hnuY ?_ ?_ ?_ ?_
        regRows_P20U.1 _ ?_
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hsgK' x h
        · exact hyK x h
      · show (wo.sigma.take P20U.ksLog ++ wo.tauY).length = P20U.ksLog + 5
        rw [List.length_append, hsgl', hyl, ksLog_P20U]
      · intro e; have := congrArg List.length e; simp [hsgl', hyl] at this
      · show P20U.ksLog + 5 ≤ CMain.nu20; rw [ksLog_P20U]; decide
      · rw [hRY]; simp only [List.map_append, List.map_take, ksLog_P20U]
    · refine row_rel (blk := ⟨P20U.recRowsLog + 5, (layout0 P20U).s⟩) (s := sM) hnuM ?_ ?_ ?_ ?_
        regRows_P20U.2 _ ?_
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · rcases List.mem_append.mp h with h | h
          · exact hsgK' x h
          · rw [List.mem_singleton] at h; rw [h]; exact hz2K
        · exact hmK x h
      · show (wo.sigma.take P20U.ksLog ++ [F.z2] ++ wo.tauM).length = P20U.recRowsLog + 5
        rw [List.length_append, List.length_append, hsgl', hml]; rfl
      · intro e; have := congrArg List.length e; simp [hsgl', hml] at this
      · show P20U.recRowsLog + 5 ≤ CMain.nu20; decide
      · rw [hRM]; simp only [List.map_append, List.map_take, ksLog_P20U, List.map_cons, List.map_nil, hz2]
  · -- the boundary claims
    rw [hh, zipIdx_map_range, List.map_map, flatMap_map_eq]
    simp only [Function.comp_apply, FItem.flat]
    rw [flatMap_single, hdBl, logN_P20U]
    exact forall₂_map_of _ fun l _ => bound_rel hmbE hsm hn hzE hoE (hLane l)

/-! ## The assembly -/

/-- **`rowSwitchDR`'s data** from a bare cursor at `P`: the target of `rowValD`, the point's words, `eq(r'', ·)`. -/
theorem rowSwitchDR_val (zz sv : List FE2) (sig : ByteArray) (P : ℕ) :
    ((rowSwitchDR zz sv sig ⟨P, 0, true⟩).1).1 =
      ⟨(rowValD zz sv (eqKernel ((List.range 7).map fun k => feAt sig (P + 40 + 72 * k)))).1.1, zz.map tColsW,
        (eqKernel ((List.range 7).map fun k => feAt sig (P + 40 + 72 * k))).toArray,
        eqKernel ((List.range 7).map fun k => feAt sig (P + 40 + 72 * k))⟩ := by
  unfold rowSwitchDR
  rw [dbind_run, Lvm.Q1.samples_run sig 7 _ (by norm_num)]
  simp only [Nat.add_zero]
  rw [dpure_run]
  show RowR.mk _ _ _ _ = RowR.mk _ _ _ _
  refine congrArg (fun t => RowR.mk t (zz.map tColsW) _ _) ?_
  unfold rowValD
  refine congrArg sumE (List.map_congr_left fun j hj => ?_)
  rw [list_toArray_getD, rowWordDF_eq _ (List.mem_range.mp hj)]

theorem slicesOf_reads {sig : ByteArray} {T : ℕ} (hS : Lvm.Q1.Streamed M sig T) {a P : ℕ} (ha : 8 * a = P + 40)
    (hT : a + 128 < T) : slicesOf M a = readsE2 sig P 64 := by
  unfold slicesOf readsE2
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rw [← laneC2_mk, Lvm.Q1.laneC2_val hS (by omega)]
  exact congrArg _ (by omega)

theorem map_range_getD {α β : Type} [Inhabited α] (l : List α) (g : α → β) :
    (List.range l.length).map (fun i => g (l.getD i default)) = l.map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ h1]

theorem readsE2_add (sig : ByteArray) (P m n : ℕ) :
    readsE2 sig P (m + n) = readsE2 sig P m ++ readsE2 sig (P + 16 * m) n := by
  unfold readsE2
  rw [List.range_add, List.map_append, List.map_map]
  refine congrArg (_ ++ ·) (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  exact congrArg _ (by ring)

theorem hsA_out {c : Ctx} {α : Type} {m : BM α} {P : α → Prop} {p : Ptr} (hP : HsA c M m P)
    (h : Lvm.QSig.Ok c M m p) : ∃ o, (m p).1 = o ∧ P o := ⟨_, rfl, hP p h.1 h.2⟩

/-- **A row switch's data** (`rowSwitchDR` from a bare cursor at `P`) is the gadget's: its target, the point's words,
its `eq(r'', ·)` cells' values. -/
theorem row_data {c : Ctx} {sig : ByteArray} {T : ℕ} (hS : Lvm.Q1.Streamed M sig T) {qr tB z o : ℕ}
    (hz : M.e z = 0) (ho : M.e o = 1) (hT : qr + 9 * 6 + 2 < T) {p : Ptr}
    (hh : SegsHold c M p (rowG qr tB z o p).2) {P : ℕ} (hP : 8 * qr = P + 40) (zz sv : List FE2)
    (ht : ∀ j < 128, M.k (tB + j) = rowWordD sv j) :
    ((rowSwitchDR zz sv sig ⟨P, 0, true⟩).1).1 = ⟨(rowG qr tB z o p).1.target.val M, zz.map tColsW,
      ((rowG qr tB z o p).1.eqR.map (Cell.val M)).toArray, (rowG qr tB z o p).1.eqR.map (Cell.val M)⟩ := by
  have hE := (rowG_spec (c := c) hS hz ho hT p hh).1
  have e : eqKernel ((List.range 7).map fun k => feAt sig (P + 40 + 72 * k)) =
      (rowG qr tB z o p).1.eqR.map (Cell.val M) := by
    rw [hE]
    exact congrArg _ (List.map_congr_left fun k _ => congrArg _ (by omega))
  rw [rowSwitchDR_val, e, (rowSwitch_phase hS hz ho hT hh hP zz sv ht).2]

theorem ksSplit_P20U' : ksSplit P20U = 7680 := by decide

theorem readsE2_getD (sig : ByteArray) (P n : ℕ) {i : ℕ} (hi : i < n) :
    (readsE2 sig P n).getD i 0 = fe2At sig (P + 40 + 16 * i) := by
  simp [readsE2, List.getD_eq_getElem?_getD, hi]

/-- `V`'s slot weights of `nl` lanes in slots `0 … nl − 1` from a represented claim's weights. -/
theorem slotWF_omega {M : Mem} {cv : ℕ → C2} {ω : List FE2} (hω : ∀ j < 1600, ω.getD j 0 = omegaF M 16 cv j)
    {nl : ℕ} (hnl : nl ≤ 25) (τ : List FE2) {zz : ℕ} (hzz : zz < 64) :
    E2V.slotWF 5 (fun o z => if o < nl then ω.getD (64 * o + z) 0 else 0) τ zz =
      slotWv (cvB M 16 cv) (E2V.eqKernelF (cvA M 16 cv)) τ nl zz := by
  rw [slotWF_blk (fun j => ω.getD j 0) nl (by omega) τ zz]
  unfold slotWv
  refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
  have ho' := List.mem_range.mp ho
  rw [hω _ (by omega), omegaF, show (64 * o + zz) % 64 = zz by omega, show (64 * o + zz) / 64 = o by omega]

theorem slotWF_yWG {M : Mem} {cv : ℕ → C2} {ω : List FE2} (hω : ∀ j < 1600, ω.getD j 0 = omegaF M 16 cv j)
    (τ : List FE2) {zz : ℕ} (hzz : zz < 64) :
    E2V.slotWF 5 (E2V.yWG ω) τ zz = slotWv (cvB M 16 cv) (E2V.eqKernelF (cvA M 16 cv)) τ 25 zz :=
  slotWF_omega hω le_rfl τ hzz

theorem slotWF_mWG {M : Mem} {cv : ℕ → C2} {ω : List FE2} (hω : ∀ j < 1600, ω.getD j 0 = omegaF M 16 cv j)
    (τ : List FE2) {zz : ℕ} (hzz : zz < 64) :
    E2V.slotWF 5 (E2V.mWG ω) τ zz = slotWv (cvB M 16 cv) (E2V.eqKernelF (cvA M 16 cv)) τ 17 zz :=
  slotWF_omega hω (by norm_num) τ hzz

/-- The lanes of `CHwire` at `w = 20`. -/
theorem wireLanesU_20 (qw : ℕ) : wireLanesU 20 qw =
    ⟨qw + 280, qw + 286, qw + 314, qw + 442, qw + 505, qw + 575, qw + 703, qw + 766, qw + 836, qw + 964,
      qw + 1027⟩ := by
  simp only [wireLanesU, slotLanesU, roundLanes2]

/-- The wire's proof of work by round family (`wireChalsU` at `w = 20`, first message lane `8 qw = P + 40`). -/
theorem powW_of {sig : ByteArray} {qw P : ℕ} (hq : 8 * qw = P + 40)
    (h : Lvm.Q1.PowOkV (feAt sig) (wireChalsU 20 qw)) :
    (∀ k < 20, DM.powOKR E2V.gC2 (feAt sig (P + 80 + 112 * k)) = true) ∧
    (∀ k < 2, DM.powOKR E2V.gC2 (feAt sig (P + 2288 + 80 + 112 * k)) = true) ∧
    (∀ k < 5, DM.powOKR E2V.gC2 (feAt sig (P + 4040 + 80 + 112 * k)) = true) ∧
    (∀ k < 5, DM.powOKR E2V.gC2 (feAt sig (P + 6128 + 80 + 112 * k)) = true) := by
  unfold wireChalsU at h
  rw [wireLanesU_20] at h
  dsimp only at h
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have := h (qw + roundLanes2 * k + 5, E2V.gC2) (List.mem_map.mpr ⟨_, List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))), rfl⟩)
    rwa [show 8 * (qw + roundLanes2 * k + 5) = P + 80 + 112 * k by simp only [roundLanes2]; omega] at this
  · have := h (qw + 286 + roundLanes2 * k + 5, E2V.gC2) (List.mem_map.mpr ⟨_, List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))), rfl⟩)
    rwa [show 8 * (qw + 286 + roundLanes2 * k + 5) = P + 2288 + 80 + 112 * k by simp only [roundLanes2]; omega]
      at this
  · have := h (qw + 505 + roundLanes2 * k + 5, E2V.gC2) (List.mem_map.mpr ⟨_, List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)), rfl⟩)
    rwa [show 8 * (qw + 505 + roundLanes2 * k + 5) = P + 4040 + 80 + 112 * k by simp only [roundLanes2]; omega]
      at this
  · have := h (qw + 766 + roundLanes2 * k + 5, E2V.gC2) (List.mem_map.mpr ⟨_,
      List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), rfl⟩)
    rwa [show 8 * (qw + 766 + roundLanes2 * k + 5) = P + 6128 + 80 + 112 * k by simp only [roundLanes2]; omega]
      at this

/-- `R` rounds' answers from lane `q` (`8 q = P + 40`) are `scPts`. -/
theorem sc2_vals {sig : ByteArray} {T : ℕ} (hS : Lvm.Q1.Streamed M sig T) {R q P : ℕ} (hq : 8 * q = P + 40)
    (hT : q + 14 * R + 1 < T) : ((sc2Ans R q).map ld2).map (C2.val M) = scPts sig P R := by
  unfold sc2Ans scPts
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.mp hk
  simp only [Function.comp_apply, roundLanes2]
  rw [ld2_val hS (by omega)]
  exact congrArg _ (by omega)

theorem scFold2_ld2 {sig : ByteArray} {T : ℕ} (hS : Lvm.Q1.Streamed M sig T) {R q : ℕ} (hT : q + 14 * R + 1 < T)
    (x : FE2) : scFold2 (fun k => (ld2 k).val M) R q x = scFold2 (fun k => fe2At sig (8 * k)) R q x :=
  scFold2_congr _ _ R q x fun j hj => ⟨ld2_val hS (by omega), ld2_val hS (by omega), ld2_val hS (by omega)⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **UTAPE-STMT 25b (`front_phasesU`)**: the front's phases at `P20U` (`front_phasesT`'s twin for `frontU`): from the
front's rows and assertions (gate on), the proof-of-work answers (`powFrontU`), the three row switches' words (the
`rowAux` blocks on `tBu`), `n'`'s bits and range and the bits of `s'`, V_S's merged tape with the wire runs from the
tape's first item to the opening's, the front's claims stand for `frontItemsU`'s, and `mb` is `n' − 1`'s selector. -/
theorem front_phasesU {c : Ctx} {M : Mem} {sig : ByteArray} {q : Ptr}
    (hS : Lvm.Q1.Streamed M sig (streamLanes P20U))
    (hTo : posOf P20U (phaseItem0 P20U .openMain) + 48 ≤ 8 * streamLanes P20U)
    (hg : M.k (pbB cfgU20) = 1) (hpow : Lvm.Q1.PowOkV (feAt sig) (powFrontU P20U))
    (hrD : ∀ j < 128, M.k (tBu cfgU20 0 + j) = rowWordD (Lvm.Q2.slicesOf M wlU.slicesD) j)
    (hrY : ∀ j < 128, M.k (tBu cfgU20 1 + j) = rowWordD (Lvm.Q2.slicesOf M wlU.slicesY) j)
    (hrM : ∀ j < 128, M.k (tBu cfgU20 2 + j) = rowWordD (Lvm.Q2.slicesOf M wlU.slicesM) j)
    (pub : Pub) (hnb : ∀ j < 20, (kc ((sigIn cfgU20).bn + 2 + j)).val M = bitE pub.n j)
    (hn : 1 ≤ pub.n ∧ pub.n ≤ 2 ^ 20) (hsb : ∀ i < 256, M.k (bsB cfgU20 + i) = if sBitsD pub.s i then 1 else 0)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) (zc : Cell) (b : Bool)
    (hsm : b = true → pub.n ≤ 2 ^ 18) (h : Lvm.QSig.Ok c M (frontU cfgU20) q) :
    ∃ tp : Lvm.E2U.TapeU Lvm.RowZ,
      Lvm.Har.PhaseAt (Lvm.E2U.tapeUDG Lvm.rowSwitchDR P20U pub.s pub.n) sig
        (posOf P20U (phaseItem0 P20U .tape)) (posOf P20U (phaseItem0 P20U .openMain)) tp ∧
      List.Forall₂ (Lvm.Q2.FRelZ M zc b) (frontU cfgU20 q).1.cs
        ((Lvm.E2U.frontItemsU Lvm.rowAccR P20U pub tp).flatMap Lvm.FItem.flat) ∧
      vs M (frontU cfgU20 q).1.mb = selectorPoint (pub.n - 1) 20 := by
  obtain ⟨hn1, hn2⟩ := hn
  obtain ⟨T, hTl⟩ : ∃ T, streamLanes P20U = T := ⟨_, rfl⟩
  rw [hTl] at hS hTo
  have hgv : (kc (pbB cfgU20)).val M = 1 := by rw [Cell.val_K, hg, ofK_one]
  have hp : cfgU20.p = P20U := rfl
  -- the positions
  obtain ⟨pR, pOut, p20, pQs, pW, pQw, pOp, -⟩ := posU20.2.2.2.2.2
  simp only [phaseLane] at pR pOut p20 pQs pW pQw
  simp only [wlU, phaseLane, logN_P20U] at hrD hrY hrM
  -- the proof of work, by phase
  simp only [powFrontU, getD_toArray, logN_P20U, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hpow
  obtain ⟨hp3, hpW⟩ := powOkV_append hpow
  obtain ⟨hp2, hpT⟩ := powOkV_append hp3
  obtain ⟨hpR, hp20⟩ := powOkV_append hp2
  clear hpow hp3 hp2
  -- the front's gadgets
  obtain ⟨fo, hfo⟩ : ∃ fo, (frontU cfgU20 q).1 = fo := ⟨_, rfl⟩
  rw [hfo]
  simp only [frontU, hp, getD_toArray, Lvm.Q1.tapeGadgetE2F_eq, logN_P20U, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub] at h hfo
  obtain ⟨q1, hZ, h1, E⟩ := ok_bindE h
  clear h
  rw [E] at hfo
  rw [show (const .E 0 (kc 0) q).1 = ec q.e from rfl] at h1 hfo
  obtain ⟨q2, hO, h2, E⟩ := ok_bindE h1
  clear h1
  rw [E] at hfo
  rw [show (const .E 1 (kc 0) q1).1 = ec q1.e from rfl] at h2 hfo
  obtain ⟨q3, hZK, h3, E⟩ := ok_bindE h2
  clear h2
  rw [E] at hfo
  rw [show (const .K 0 (kc 0) q2).1 = kc q2.k from rfl] at h3 hfo
  obtain ⟨q4, hOK, h4, E⟩ := ok_bindE h3
  clear h3
  rw [E] at hfo
  rw [show (const .K 1 (kc 0) q3).1 = kc q3.k from rfl] at h4 hfo
  have hz : M.e q.e = 0 := (const_val hZ.1).trans ofK_zero
  have ho : M.e q1.e = 1 := (const_val hO.1).trans ofK_one
  have hzk : (kc q2.k).val M = 0 := (const_val hZK.1).trans ofK_zero
  have hok : M.k q3.k = 1 := congrArg FE.c₀ ((const_val hOK.1).trans ofK_one.symm)
  clear hZ hO hZK hOK
  obtain ⟨q5, hV, h5, E⟩ := ok_bindE h4
  clear h4
  rw [E] at hfo
  obtain ⟨q6, hT, h6, E⟩ := ok_bindE h5
  clear h5
  rw [E] at hfo
  obtain ⟨q7, hB, h7, E⟩ := ok_bindE h6
  clear h6
  rw [E] at hfo
  obtain ⟨q8, hW, h8, E⟩ := ok_bindE h7
  clear h7
  rw [E] at hfo
  obtain ⟨q9, hRD, h9, E⟩ := ok_bindE h8
  clear h8
  rw [E] at hfo
  obtain ⟨q10, hND, h10, E⟩ := ok_bindE h9
  clear h9
  rw [E] at hfo
  obtain ⟨q11, hRY, h11, E⟩ := ok_bindE h10
  clear h10
  rw [E] at hfo
  obtain ⟨q12, hNY, h12, E⟩ := ok_bindE h11
  clear h11
  rw [E] at hfo
  obtain ⟨q13, hRM, h13, E⟩ := ok_bindE h12
  clear h12
  rw [E] at hfo
  obtain ⟨q14, hNM, h14, E⟩ := ok_bindE h13
  clear h13
  rw [E] at hfo
  obtain ⟨q15, hME, -, E⟩ := ok_bindE h14
  clear h14
  rw [E] at hfo
  clear E
  -- names
  set Pt := posOf P20U (phaseItem0 P20U .tape) with hPt
  set Pw := posOf P20U (phaseItem0 P20U .wire) with hPw
  set qs := laneOf P20U (phaseItem0 P20U .tape + 45) with hqs
  set qw := laneOf P20U (phaseItem0 P20U .wire + 0) with hqw
  set tOut := laneOf P20U (phaseItem0 P20U .tape + 41) with htOut
  set q0 := laneOf P20U (phaseItem0 P20U .tape + 2) with hq0
  have hq0' : 8 * q0 = Pt + 120 := by have := pR 0 (by norm_num); simpa using this
  have hri : ∀ i < 20, laneOf P20U (phaseItem0 P20U .tape + (2 + 2 * i)) = q0 + 10 * i := fun i hi => by
    have := pR i hi; omega
  have htE : qs + 49 ≤ Lvm.Q1.tapeEnd2 16 qs := by unfold Lvm.Q1.tapeEnd2 Lvm.Q1.tapeQ2; omega
  have hqwE : qw = Lvm.Q1.tapeEnd2 16 qs := by omega
  have hTw : qw + 1027 < T := by omega
  -- T1's values and the tape GKR
  set F : FCtx := ⟨ec q.e, ec q1.e, kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc q3.k, kc q2.k⟩, false⟩ with hF
  set r : List C2 := (List.range 20).map fun i => Lvm.Q1.laneC2 (laneOf P20U (phaseItem0 P20U .tape + (2 + 2 * i)))
    with hr
  set r20 := Lvm.Q1.laneC2 (laneOf P20U (phaseItem0 P20U .tape + 43)) with hr20
  set a : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 2 * l) with ha
  set bb : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 50 + 2 * l) with hbb
  have hz2v : F.z2.val M = 0 := by
    show (⟨((kc q2.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 0
    rw [hzk]; rfl
  have ho2v : F.o2.val M = 1 := by
    show (⟨((kc q3.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 1
    rw [Cell.val_K, hok, ofK_one, hzk]; rfl
  have hrl : r.length = 20 := by simp [hr]
  have hrv : r.map (C2.val M) = sampsG sig (Pt + 72) 20 := by
    rw [hr, List.map_map]
    unfold sampsG
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [hri i hi', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have hr20v : r20.val M = fe2At sig (Pt + 2520) := by rw [hr20, Lvm.Q1.laneC2_val hS (by omega), p20]
  have hav : (List.range 25).map (fun l => (a.getD l default).val M) = readsE2 sig (Pt + 1672) 25 := by
    unfold readsE2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [ha, getD_map_range _ hl', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have hbv : (List.range 25).map (fun l => (bb.getD l default).val M) = readsE2 sig (Pt + 1672 + 16 * 25) 25 := by
    unfold readsE2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [hbb, getD_map_range _ hl', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have habv : ((List.range 25).map fun l => (a.getD l default).val M) ++
      (List.range 25).map (fun l => (bb.getD l default).val M) = readsE2 sig (Pt + 1672) 50 := by
    rw [hav, hbv, show 50 = 25 + 25 from rfl, readsE2_add]
  have hV1 := hs_tOneU F hz2v ho2v r hrl r20 a bb q4 hV.1
  have hinst : (List.range (16 + 5)).map (fun i => ((r ++ [r20]).getD i default).val M) =
      sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)] := by
    rw [show 16 + 5 = (r ++ [r20]).length by simp [hrl], map_range_getD, List.map_append, hrv, List.map_singleton,
      hr20v]
  have hout : (List.range 25).map (fun l => ((tOneU F r r20 a bb q4).1.getD l default).val M) =
      Lvm.E2U.t1ValsF 20 13 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50) := by
    rw [List.map_congr_left fun l hl => hV1 l (List.mem_range.mp hl), hrv, hr20v, habv]
    conv_rhs => unfold Lvm.E2U.t1ValsF
    exact List.map_congr_left fun l hl => by
      unfold Lvm.E2U.t1ValsF; exact getD_map_range0 _ (List.mem_range.mp hl)
  have TG := tapeGkr_phaseU hS (P := Pt) (qs := qs) pQs (by omega) hT.1 hT.2 hgv hpT hinst hout
  obtain ⟨TG1, hR⟩ := TG
  set claimV := (tapeGkrD 21 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (Lvm.E2U.t1ValsF 20 13
    (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50)) sig ⟨Pt + 2552, 0, true⟩).1
    with hclaimV
  set cv := (Lvm.Q1.tapeGadgetE2 16 qs (fun i => (r ++ [r20]).getD i default)
    (fun l => ((tOneU F r r20 a bb q4).1).getD l default) (kc (pbB cfgU20)) q5).1.cv with hcv
  -- `n' − 1`'s bits
  have hmbv := borrowK_vs (N := pub.n) (show M.k (kc q3.k).n = 1 from hok) (fun j hj => hnb j hj) hn1 hB.1
  have hmb := kC2_bits (m := 20) hzk hmbv
  -- the wire gadget
  have hsbl : (sbCells cfgU20).length = 256 := by simp [sbCells]
  have hBs : spongeBlocks P20U - 1 < 2 ^ 13 := by rw [sizes_P20U.1.2.2.2.2.1]; norm_num
  have hKs : ksSplit P20U + 399 + 31 < 2 ^ 13 := by rw [ksSplit_P20U']; norm_num
  obtain ⟨wo, hwo, WS⟩ := hsA_out (wireGU_sound qw cv _ (sbCells cfgU20) (spongeBlocks P20U) (ksSplit P20U + 399)
    (kc q2.k) (kc (pbB cfgU20)) (pub.n - 1) hzk hgv hsbl hmb (by omega) hBs hKs) hW
  rw [wireLanesU_20] at WS
  dsimp only at WS
  obtain ⟨hs1, hd1, hy1, hm1, hfinW, hDW, hYW, hMW⟩ := WS
  have hpt : cvRho M 16 cv = claimV.point := hR.point
  have hmu : cvMu M cv = claimV.mu := hR.mu
  have hω : ∀ j < 1600, claimV.weights.getD j 0 = omegaF M 16 cv j := fun j hj => Lvm.Q1.rep2_lt_posF hR hj
  have htgt : targetF M 16 cv (((sbCells cfgU20).map fun b => kC2 b (kc q2.k)).map (C2.val M)) (pub.n - 1) =
      wireTargetDF (sBitsD pub.s) pub.n claimV := by
    rw [wireTargetDF_eq]
    exact targetF_eq 16 cv claimV pub.s pub.n _ hR.value.symm hmu.symm hpt.symm hω (sb_vals hzk pub.s hsb)
  have hσ : wo.sigma.map (C2.val M) = scPts sig Pw 20 := by rw [hs1]; exact sc2_vals hS pQw (by omega)
  have hτD : wo.tauD.map (C2.val M) = scPts sig (Pw + 2288) 2 := by rw [hd1]; exact sc2_vals hS (by omega) (by omega)
  have hτY : wo.tauY.map (C2.val M) = scPts sig (Pw + 4040) 5 := by rw [hy1]; exact sc2_vals hS (by omega) (by omega)
  have hτM : wo.tauM.map (C2.val M) = scPts sig (Pw + 6128) 5 := by rw [hm1]; exact sc2_vals hS (by omega) (by omega)
  have hg0 : (ld2 (qw + 280)).val M = fe2At sig (Pw + 2280) := by rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hg1 : (ld2 (qw + 280 + 2)).val M = fe2At sig (Pw + 2296) := by
    rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hg2 : (ld2 (qw + 280 + 4)).val M = fe2At sig (Pw + 2312) := by
    rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hcont : [(1, spongeBlocks P20U - 1), (ksSplit P20U + 399 + 1, ksSplit P20U + 399 + 31)] = Lvm.E2U.contIvU := by
    rw [sizes_P20U.1.2.2.2.2.1, ksSplit_P20U']; rfl
  have hfin : scFold2 (fun k => fe2At sig (8 * k)) 20 qw (wireTargetDF (sBitsD pub.s) pub.n claimV) =
      E2V.msEvalF claimV.point claimV.mu (scPts sig Pw 20) 0 (pub.n - 1) * fe2At sig (Pw + 2280) +
        Lvm.E2U.eTailF 13 20 (scPts sig Pw 20) *
          (Lvm.E2U.kksF Lvm.E2U.contIvU claimV.point claimV.mu ((scPts sig Pw 20).take 13) (2 ^ 20) *
              fe2At sig (Pw + 2296) +
            E2V.ikEvalP claimV.point claimV.mu ((scPts sig Pw 20).take 13) (2 ^ 20) * fe2At sig (Pw + 2312)) := by
    rw [← htgt, ← scFold2_ld2 hS (by omega), hfinW, hpt, hmu, hσ, hg0, hg1, hg2, hcont]
  have hD : scFold2 (fun k => fe2At sig (8 * k)) 2 ((Pw + 2288 + 40) / 8) (fe2At sig (Pw + 2280)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 2 (dWA claimV.weights.toArray) (scPts sig (Pw + 2288) 2) z *
        (readsE2 sig (Pw + 2288 + 112 * 2) 64).getD z 0) := by
    rw [show (Pw + 2288 + 40) / 8 = qw + 286 by omega, ← hg0, ← scFold2_ld2 hS (by omega), hDW, E2V.sumF_eq_sum,
      dWA_eq]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτD, slotW_eq _ _ (by simp [scPts]) _ hω zz hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  have hY : scFold2 (fun k => fe2At sig (8 * k)) 5 ((Pw + 4040 + 40) / 8) (fe2At sig (Pw + 2296)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.yWG claimV.weights) (scPts sig (Pw + 4040) 5) z *
        (readsE2 sig (Pw + 4040 + 112 * 5) 64).getD z 0) := by
    rw [show (Pw + 4040 + 40) / 8 = qw + 505 by omega, ← hg1, ← scFold2_ld2 hS (by omega), hYW, E2V.sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτY, slotWF_yWG hω _ hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  have hM : scFold2 (fun k => fe2At sig (8 * k)) 5 ((Pw + 6128 + 40) / 8) (fe2At sig (Pw + 2312)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.mWG claimV.weights) (scPts sig (Pw + 6128) 5) z *
        (readsE2 sig (Pw + 6128 + 112 * 5) 64).getD z 0) := by
    rw [show (Pw + 6128 + 40) / 8 = qw + 766 by omega, ← hg2, ← scFold2_ld2 hS (by omega), hMW, E2V.sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτM, slotWF_mWG hω _ hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  obtain ⟨hpw, hpD, hpY, hpM⟩ := powW_of pQw hpW
  have WP := wireUDG_phase (P := Pw) (q := qw) P20U rfl rfl pub.s pub.n claimV pQw hpw hpD hpY hpM hfin hD hY hM
  have TG1' : Lvm.Har.PhaseAt (tapeGkrDF 21 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)])
      (Lvm.E2U.t1ValsF 20 13 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50)))
      sig (Pt + 2552) Pw claimV := by rw [pW]; exact TG1
  have hp20' : DM.powOKR E2V.gC1 (feAt sig (Pt + 2520)) = true := by
    have := hp20 _ List.mem_cons_self; rwa [p20] at this
  have TP := tapeUDG_phase (P := Pt) (q0 := q0) P20U rfl rfl pub.s pub.n hq0' hpR hp20' TG1' ⟨hn1, hn2⟩ WP
  rw [pOp]
  refine ⟨_, TP, ?_, ?_⟩
  · rw [← hfo]
    subst hwo
    simp only [wireLanesU_20] at hrD hrY hrM
    have hsD := slicesOf_reads hS (a := qw + 314) (P := Pw + 2288 + 112 * 2) (by omega) (by omega)
    have hsY := slicesOf_reads hS (a := qw + 575) (P := Pw + 4040 + 112 * 5) (by omega) (by omega)
    have hsM := slicesOf_reads hS (a := qw + 836) (P := Pw + 6128 + 112 * 5) (by omega) (by omega)
    rw [hsD] at hrD
    rw [hsY] at hrY
    rw [hsM] at hrM
    have hTD : (wireLanesU 20 qw).ringD + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    have hTY : (wireLanesU 20 qw).ringY + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    have hTM : (wireLanesU 20 qw).ringM + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    refine front_claimsU (zc := zc) (b := b) (pub := pub) (F := F) (r := r) (a := a) (bb := bb)
      (sY := E2V.selPtF ((layout0 P20U).ks / 2 ^ (P20U.ksLog + 5)) (P20U.nuMain - (P20U.ksLog + 5)))
      (sM := E2V.selPtF ((layout0 P20U).s / 2 ^ P20U.nuRec) (P20U.nuMain - P20U.nuRec))
      (eqD := (rowG (wireLanesU 20 qw).ringD (tBu cfgU20 0) (ec q.e).n (ec q1.e).n q8).1.eqR.map (Cell.val M))
      (eqY := (rowG (wireLanesU 20 qw).ringY (tBu cfgU20 1) (ec q.e).n (ec q1.e).n q10).1.eqR.map (Cell.val M))
      (eqM := (rowG (wireLanesU 20 qw).ringM (tBu cfgU20 2) (ec q.e).n (ec q1.e).n q12).1.eqR.map (Cell.val M))
      hz2v ho2v ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hz ho ?_ hrl ?_ ?_ hrv.symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hσ.symm hτD.symm ?_
      ?_ ?_ ?_ ?_ ?_ ?_ hh hsm hn1
    · intro x hx
      rw [hr] at hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨rfl, rfl⟩
    · intro l hl; rw [ha, getD_map_range _ (by omega)]; exact ⟨rfl, rfl⟩
    · intro l hl; rw [hbb, getD_map_range _ hl]; exact ⟨rfl, rfl⟩
    · intro l hl
      show (readsE2 sig (Pt + 1672) 50).getD l 0 = _
      rw [← habv, List.getD_append _ _ _ _ (by simp; omega), getD_map_range0 _ (by omega)]
    · intro l hl
      show (readsE2 sig (Pt + 1672) 50).getD (25 + l) 0 = _
      rw [← habv, List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
        Nat.add_sub_cancel_left, getD_map_range0 _ hl]
    · rw [hs1]; exact ld2_K _
    · rw [hs1]; simp [sc2Ans]
    · rw [hd1]; exact ld2_K _
    · rw [hd1]; simp [sc2Ans]
    · rw [hy1]; exact ld2_K _
    · rw [hy1]; simp [sc2Ans]
    · rw [hm1]; exact ld2_K _
    · rw [hm1]; simp [sc2Ans]
    · show ((rowSwitchDR _ _ sig ⟨Pw + 2288 + 112 * 2 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTD hRD.1 (by simp only [wireLanesU_20]; omega) _ _ hrD, hσ, hτD]
    · exact rowNuOk_of hS hz ho hTD hRD.1 hND.1
    · show ((rowSwitchDR _ _ sig ⟨Pw + 4040 + 112 * 5 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTY hRY.1 (by simp only [wireLanesU_20]; omega) _ _ hrY, hσ, hτY]
    · exact rowNuOk_of hS hz ho hTY hRY.1 hNY.1
    · show ((rowSwitchDR _ _ sig ⟨Pw + 6128 + 112 * 5 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTM hRM.1 (by simp only [wireLanesU_20]; omega) _ _ hrM, hσ, hτM]
    · exact rowNuOk_of hS hz ho hTM hRM.1 hNM.1
    · exact (mapB_add_vs (by rw [Cell.val_E, hz]) _ _ hME.1).trans (by rw [hmbv, selectorPoint_bits])
  · rw [← hfo]
    exact hmbv.trans (selectorPoint_bits _ _).symm

end FrontU

end Lvm.E2Q

-- ===== merged from `LvmE2UHar` (lvm2 U-TAPE closure: `LvmE2UHar.lean` is now a stub importing `LvmE2QFrontU`) =====
-- New for lvm2 U-TAPE (UT-C2, STMT 25g): V_S's decision at S2GU cut into its phases (`core_of_phasesU`, the twin of
-- `core_of_phasesFG` for `decideProgUG`: the cap's skip, the root pin, the typed phases at `E2`, the merged tape with
-- the wire, the opening on items) and `decideFUG_of`.

/-!
# `decideProgUG` by phases

**`core_of_phasesU`**: from the cursor after S2GU's header, if the root pin, the typed phases (`dTypedTG pT` with the
items `typedItemsND N p`), the merged tape (`tapeUDG rowSwitchDR p`) keep `ok` and meet the next phase, and the
opening (`dOpenF` on the flattened items) reads `Σ` to its end, then `decideProgUG p pT` returns the typed phases'
accumulator in an accepting state. **`decideFUG_of`**: `decideFUG p pT N` accepts once also `Φ_Q` at `E2` holds.
-/


namespace Lvm.Har

open Lvm DM Lvm.E2T Lvm.E2U

theorem core_of_phasesU (p pT : Params) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb P1 P2 P3 : Nat} {pin : BlockClaim} {acc : Acc} {ti : List FItem}
    {evals : List (List FE × List FE)} {tp : TapeU RowZ}
    (hb : pos (RS.startH (headerBytesP p)) + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap = Pb)
    (hpin : PhaseAt (pinD p.nuMain) sig Pb P1 pin)
    (htyped : PhaseAt (dTypedTG pT N (m3G N p) (pubG vk c sig) (typedItemsND N p)) sig P1 P2 (acc, ti, evals))
    (htape : PhaseAt (tapeUDG rowSwitchDR p (pubG vk c sig).s (pubG vk c sig).n) sig P2 P3 tp)
    (hopen : ∀ s : RS, pos s = P3 → s.ok = true →
      let o := dOpenF p (TypedV.smallT p (pubG vk c sig)) pin
        ((ti ++ tabItemsR (M3.sumcheckTabs N.mbT) evals ++ frontItemsU rowAccR p (pubG vk c sig) tp).flatMap
          FItem.flat) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    ∃ s₉ : RS, decideProgUG p pT N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧ s₉.ok = true ∧
      s₉.ent = sig.size ∧ s₉.msg = 0 := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : RS, RS.startH (headerBytesP p) = s₀ := ⟨_, rfl⟩
  have h₀ : s₀.ok = true := by rw [← hs₀]; rfl
  rw [hs₀] at hb ⊢
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = { s₀ with msg := s₀.msg + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap } :=
    ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← hb, hs1]; simp only [pos]; omega
  obtain ⟨a1, a2, a3⟩ := hpin s1 e1 (by rw [hs1]; exact h₀)
  generalize hA : pinD p.nuMain sig s1 = AA at a1 a2 a3
  obtain ⟨av, s2⟩ := AA
  simp only at a1 a2 a3
  rw [a1] at hA
  obtain ⟨b1, b2, b3⟩ := htyped s2 a3 a2
  generalize hB : dTypedTG pT N (m3G N p) (pubG vk c sig) (typedItemsND N p) sig s2 = BB at b1 b2 b3
  obtain ⟨bv, s3⟩ := BB
  simp only at b1 b2 b3
  rw [b1] at hB
  obtain ⟨c1, c2, c3⟩ := htape s3 b3 b2
  generalize hC : tapeUDG rowSwitchDR p (pubG vk c sig).s (pubG vk c sig).n sig s3 = CC at c1 c2 c3
  obtain ⟨cv, s4⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨o1, o2, o3⟩ := hopen s4 c3 c2
  rw [← dOpenFFI_eq] at o1 o2 o3
  generalize hO : dOpenFFI p (TypedV.smallT p (pubG vk c sig)) pin (ti ++ tabItemsR (M3.sumcheckTabs N.mbT) evals)
    (frontItemsU rowAccR p (pubG vk c sig) tp) sig s4 = OO at o1 o2 o3
  obtain ⟨ov, s5⟩ := OO
  simp only at o1 o2 o3
  refine ⟨s5, ?_, o1, o2, o3⟩
  unfold decideProgUG
  simp only [bind_run', read_run', skip_run', pure_run']
  rw [← hs1, hA]
  simp only
  rw [hB]
  simp only
  rw [hC]
  simp only
  rw [hO]

/-- **`decideFUG` accepts** when its run (from the cursor after S2GU's header) ends accepting with the accumulator
`acc` and `Φ_Q` at `E2` holds at it. -/
theorem decideFUG_of (p pT : Params) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) {acc : Acc}
    (hrun : ∃ s₉ : RS, decideProgUG p pT N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧
      s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0)
    (hphi : N.phiT (acc.pt.map Lvm.e2OfFE) = Lvm.e2OfFE acc.y) :
    decideFUG p pT N vk c sig = true := by
  obtain ⟨s₉, h1, h2, h3, h4⟩ := hrun
  unfold decideFUG DM.runOnH
  simp only [StateT.run, h1, h2, h3, h4, hphi, Bool.true_and, beq_self_eq_true, Bool.and_self]

/-- `dMiniT` reads only the bus depth, the leaf reads, the table rounds and the record's `busFinal` and tables
(`Lvm.VEq.dMiniT_congr`'s copy). -/
theorem dMiniT_congrU (p p' : Params) (m m' : M3) (tabs : List M3.Tab) (pub : Pub) (h1 : p.busDepth = p'.busDepth)
    (h2 : p.leafdecReads = p'.leafdecReads) (h3 : p.tableRounds = p'.tableRounds) (hb : m.busFinal = m'.busFinal)
    (ht : m.tables = m'.tables) : TypedV.dMiniT p m tabs pub = TypedV.dMiniT p' m' tabs pub := by
  unfold TypedV.dMiniT
  rw [h1, h2, h3, hb, ht]

end Lvm.Har
