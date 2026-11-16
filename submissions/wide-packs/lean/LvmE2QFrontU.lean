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

-- (SLF-K: 21 declarations that `certified` does not use moved verbatim to `LvmS2GUOff`, outside its import closure.)

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

/-! Proof help (GOLF3-U, generic in the parameter set): the lanes the position facts read, as lookups into one
suffix of `itemLanes p` per phase (`laneOf_drop` …), and `List.drop`/`List.getD` in `List.rec` form (`dropLN`,
`getDLN`, `itemLanesR`): the kernel computes each phase's suffix once (a closed term, cached) and walks only within the
phase (the bus's runs from their first lane, `getDLN_add`), where `List.getD` from the list's head cost ≈ 0.5 M heartbeats
per lane past item 2,600. -/

/-- `List.drop` on lane lists by `List.rec` (proof help: `dropLN_eq`). -/
noncomputable def dropLN (l : List Nat) : Nat → List Nat :=
  l.rec (fun _ => []) (fun a t ih n => Nat.casesOn (motive := fun _ => List Nat) n (a :: t) (fun m => ih m))

/-- `List.getD _ _ 0` on lane lists by `List.rec` (proof help: `getDLN_eq`). -/
noncomputable def getDLN (l : List Nat) : Nat → Nat :=
  l.rec (fun _ => 0) (fun a _ ih i => Nat.casesOn (motive := fun _ => Nat) i a (fun j => ih j))

theorem dropLN_eq : ∀ (l : List Nat) (n : Nat), dropLN l n = l.drop n
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => (dropLN_eq l n : _)

theorem getDLN_eq : ∀ (l : List Nat) (n : Nat), getDLN l n = l.getD n 0
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => (getDLN_eq l n : _)

theorem getDLN_add (l : List Nat) (a j : Nat) : getDLN l (a + j) = getDLN (dropLN l a) j := by
  rw [getDLN_eq, getDLN_eq, dropLN_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- `itemLanesAux` by `List.rec` (proof help: `itemLanesAux_eq_R`). -/
noncomputable def itemLanesR (p : Params) (l : List Item) : Nat → Nat → List Nat :=
  l.rec (fun _ _ => []) fun it _ ih b pend =>
    match it with
    | .read m => (b + 40 + pend) / 8 :: ih b (pend + eBytes * m)
    | .readW m w => (b + 40 + pend) / 8 :: ih b (pend + w * m)
    | .cap c _ => (b + 40 + pend) / 8 :: ih b (pend + nodeBytes * 2 ^ c)
    | .sample => (b + 40 + pend) / 8 :: ih (b + 72 + pend) 0
    | .positions ref => (b + 40 + pend) / 8 :: ih (b + 72 + pend + ((p.level ref).nPosQ - 1) * 72) 0
    | .opening ref =>
      b / 8 :: ih (b + (p.level ref).t * (40 + (p.level ref).row) + (p.level ref).t * (p.level ref).path * 104) pend

theorem itemLanesAux_eq_R (p : Params) :
    ∀ (l : List Item) (b pend : Nat), itemLanesAux p b pend l = itemLanesR p l b pend
  | [], _, _ => by rw [itemLanesAux]; rfl
  | it :: l, b, pend => by cases it <;> (rw [itemLanesAux]; simp only [itemLanesAux_eq_R p l]; rfl)

theorem laneOf_drop (p : Params) (a j : Nat) : laneOf p (a + j) = ((itemLanes p).drop a).getD j 0 := by
  simp only [laneOf, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem phaseLane_drop (p : Params) (ph : Phase) (j : Nat) :
    phaseLane p ph j = ((itemLanes p).drop (phaseItem0 p ph)).getD j 0 := laneOf_drop p _ j

theorem posOf_drop (p : Params) (k : Nat) : posOf p k = 8 * ((itemLanes p).drop k).getD 0 0 - 40 := by
  rw [posOf, ← laneOf_drop, Nat.add_zero]

theorem busL_drop (p : Params) (j : Nat) : busL p j = ((itemLanes p).drop (phaseItem0 p .bus)).getD j 0 := by
  rw [← laneOf_drop]
  simp only [busL, laneOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

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

/-- The tape GKR's layer template at `P = 15` (`logN + 1 = 21` row bits, K = 32). -/
theorem layOk2_15 : Lvm.Q1.layOk2 15 = true := by
  rw [Lvm.Q1.layOk2_eq_lit, Lvm.Q1.layerTB2T_eq_F, Lvm.Q1.layerTB2F_eq_R, Lvm.Q1.layOk2T_eq_R, Lvm.Q1.layOk2TR_eq_S]
  decide +kernel

/-- **The merged tape's GKR phase** (E2F-QH4's `tape_phase2` at `P = 15`): V's `tapeGkrDF 21` on `r ‖ r₂₀` and T1's
values runs from `P + 2552` to the wire, and the gadget's carried cells represent its claim. -/
theorem tapeGkr_phaseU {c : Ctx} {M : Mem} {sig : ByteArray} {T : ℕ} (hS : Lvm.Q1.Streamed M sig T) {P qs : ℕ}
    {inst out : ℕ → C2} {b : Cell} {p : Ptr} (hqs : 8 * qs = P + 2600) (hT : Lvm.Q1.tapeEnd2 15 qs + 2 ≤ T)
    (hh : SegsHold c M p (Lvm.Q1.tapeGadgetE2 15 qs inst out b p).2)
    (ha : SegsAssert M p (Lvm.Q1.tapeGadgetE2 15 qs inst out b p).2) (hb : b.val M = 1)
    (hpow : Lvm.Q1.PowOkV (feAt sig) (Lvm.Q1.tapeChals2 15 qs))
    (hinst : (List.range (15 + 6)).map (fun i => (inst i).val M) = sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)])
    (hout : (List.range 25).map (fun l => (out l).val M) = Lvm.E2U.t1ValsF 20 13
      (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50)) :
    PhaseAt (tapeGkrDF 21 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (Lvm.E2U.t1ValsF 20 13
        (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50))) sig (P + 2552)
      (8 * Lvm.Q1.tapeEnd2 15 qs - 40)
      (tapeGkrD 21 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (Lvm.E2U.t1ValsF 20 13
        (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50)) sig ⟨P + 2552, 0, true⟩).1 ∧
    Lvm.Q1.Rep2 15 (fun j => ((Lvm.Q1.tapeGadgetE2 15 qs inst out b p).1.cv j).val M)
      (tapeGkrD 21 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (Lvm.E2U.t1ValsF 20 13
        (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50)) sig ⟨P + 2552, 0, true⟩).1
      false := by
  have h := Lvm.Q1.tape_phase2 layOk2_15 (by omega) hS hT hh ha hb hpow
  rw [hinst, hout, show 8 * qs - 48 = P + 2552 by omega] at h
  rw [tapeGkrDF_eq]
  exact h

end WirePh

/-! ## The front's phases at `P20U` (25b) -/

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
  rw [show tColsWF = tColsW from funext tColsWF_eq]
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

theorem readsE2_getD (sig : ByteArray) (P n : ℕ) {i : ℕ} (hi : i < n) :
    (readsE2 sig P n).getD i 0 = fe2At sig (P + 40 + 16 * i) := by
  simp [readsE2, List.getD_eq_getElem?_getD, hi]

/-- `V`'s slot weights of `nl` lanes in slots `0 … nl − 1` from a represented claim's weights. -/
theorem slotWF_omega {M : Mem} {cv : ℕ → C2} {ω : List FE2} (hω : ∀ j < 1600, ω.getD j 0 = omegaF M 15 cv j)
    {nl : ℕ} (hnl : nl ≤ 25) (τ : List FE2) {zz : ℕ} (hzz : zz < 64) :
    E2V.slotWF 5 (fun o z => if o < nl then ω.getD (64 * o + z) 0 else 0) τ zz =
      slotWv (cvB M 15 cv) (E2V.eqKernelF (cvA M 15 cv)) τ nl zz := by
  rw [slotWF_blk (fun j => ω.getD j 0) nl (by omega) τ zz]
  unfold slotWv
  refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
  have ho' := List.mem_range.mp ho
  rw [hω _ (by omega), omegaF, show (64 * o + zz) % 64 = zz by omega, show (64 * o + zz) / 64 = o by omega]

theorem slotWF_yWG {M : Mem} {cv : ℕ → C2} {ω : List FE2} (hω : ∀ j < 1600, ω.getD j 0 = omegaF M 15 cv j)
    (τ : List FE2) {zz : ℕ} (hzz : zz < 64) :
    E2V.slotWF 5 (E2V.yWG ω) τ zz = slotWv (cvB M 15 cv) (E2V.eqKernelF (cvA M 15 cv)) τ 25 zz :=
  slotWF_omega hω le_rfl τ hzz

theorem slotWF_mWG {M : Mem} {cv : ℕ → C2} {ω : List FE2} (hω : ∀ j < 1600, ω.getD j 0 = omegaF M 15 cv j)
    (τ : List FE2) {zz : ℕ} (hzz : zz < 64) :
    E2V.slotWF 5 (E2V.mWG ω) τ zz = slotWv (cvB M 15 cv) (E2V.eqKernelF (cvA M 15 cv)) τ 17 zz :=
  slotWF_omega hω (by norm_num) τ hzz

/-- The lanes of `CHwire` at `w = 20`. -/
theorem wireLanesU_20 (qw : ℕ) : wireLanesU 20 qw =
    ⟨qw + 280, qw + 286, qw + 314, qw + 442, qw + 505, qw + 575, qw + 703, qw + 766, qw + 836, qw + 964,
      qw + 1027⟩ := by
  -- GOLF3-U: the numerals summed by `simp` (the closing `rfl` compared `qw + 14 * 20 + 6 + …` with `qw + 286` by
  -- unary `Nat.succ` unfolding: 0.98 M → 0.01 M heartbeats)
  simp only [wireLanesU, slotLanesU, roundLanes2, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]

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

/-! Proof help (GOLF3-U): the `DM` run lemmas with a non-`rfl` proof (`LvmE2QHarTop`'s private `bind_runH` …): as `rfl`
lemmas in `simp` the kernel re-checked the rewritten run against the program through `DM`'s `bind`. -/

end Lvm.Har
