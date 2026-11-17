-- New for lvm2 (roll 8 = B1, wave L, L-C): O5b for the typed backend. `VST P20 N` (parse, drive the typed
-- schedule, `decideFT`) accepting implies the compiled verifier of an IOP verifier `PS` accepting, on every log,
-- given the value refinement and the schedule's shape (roll 7's simulation, `sim`). lvm2 roll 11 (M′, R11-IR): the
-- grouping and the opening at `S2GM` (one cap, `C_main`'s opening only); the M′ instance is `LvmMPVEq`.
import LvmCertTInst
import LvmVEqFolMid
import LvmShape
import LvmCertS
import LvmReplay
import LvmWhirParamsJp
import LvmTypedSpec
import LvmTypedVEqForms
import LvmAccNodeFold
import LvmVEqTop
import LvmVEqStream
import LvmSchedLit
import LvmVEqSim
import LvmVEqParse

-- (GOLF2: 38 declarations that `certified` does not use moved verbatim to `LvmE2VWidthsFOff`, outside its import closure.)

-- ===== merged from `LvmVEqFolPS` (GOLF module merge: `LvmVEqFolPS.lean` is now a stub importing `LvmTypedVEqTop`) =====
section
-- New for lvm (WP-14a, H0): the IOP verifier `P_S` (LvmCertS `PSWith`) with the middle phases `midS`
-- follows the whole schedule at P20 (`Fol`, LvmVEqShape): the root, the middle phases (LvmVEqFolMid),
-- and the WHIR opening against `openMainI` (lvm2 JB-VQP J1: with OOD samples, `fol_verifyStackedJ`; lvm2 roll 11,
-- M′: `PSWithM`, one commitment).

/-!
# `P_S` follows the schedule

* `lvMatch_main`: `cfgMain23Jq 1`'s levels are P20's (`LvMatchJ` with the OOD samples' `κ`, at `capS`, `shpS`,
  `idxS`), by evaluation on `P20L` (LvmReplay's `P20_eq`: the levels written out);
* `fol_openMain`: the opening against `openMainI P20`; `folP_commit`: the root against `commitI P20`;
* **`fol_PSOfM`**: `PSWithM mid x`'s body against `atomsOf P20 (schedule P20)` from no pending positions, for any middle
  phases that follow `midItems` (lvm2 roll 11, M′: one root, one opening; B1's two-root `fol_PSOf` and `C_rec`'s
  `lvMatch_rec`, `fol_openRec`, `cap_rec0` are gone with the refreeze `S2GM`).

A `Fol` at concrete atoms is applied with `@` (the default application elaborator would unfold it).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.Replay (P20_eq)

theorem lvMatch_main : LvMatchJ P20 capS shpS idxS .main (cfgMain23Jq 1).μ (cfgMain23Jq 1).c₀
    (cfgMain23Jq 1).n₀ P20.mainFinalLog 0 0 (cfgMain23Jq 1).levels P20.mainLevels := by
  rw [P20_eq]
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩⟩

theorem openMainI_P20 : openMainI P20 = smp 1 ++ whirIJ .main P20.mainLevels P20.mainFinalLog P20.grind := by
  rw [openMainI, if_pos (by rw [P20_eq]; rfl)]

/-- **`C_main`'s opening** (J1: with OOD samples; M′: `n₀ = 1` commitment before it) against `openMainI P20`. -/
theorem fol_openMain (claims : List Verifier.StackClaim) (pp : List ℕ) :
    Fol capS shpS idxS (Verifier.verifyStackedJ (cfgMain23Jq 1) claims) (atomsOf P20 (openMainI P20)) pp
      fun _ _ ↦ True := by
  rw [openMainI_P20]
  exact @fol_verifyStackedJ P20 capS shpS idxS (cfgMain23Jq 1) rfl rfl .main P20.mainLevels P20.mainFinalLog
    lvMatch_main claims pp

theorem cap_main0 : capS (cfgMain24G.μ - 6 + 1) (2 ^ 6) = (P20.level ⟨.main, 0⟩).cap := by
  rw [P20_eq]; rfl

theorem atomsOf_commitI : atomsOf P20 (commitI P20) = [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] := rfl

end Lvm.VEq
end
-- ===== end of `LvmVEqFolPS` =====

-- ===== merged from `LvmTypedVEqFol` (GOLF module merge: `LvmTypedVEqFol.lean` is now a stub importing `LvmTypedVEqTop`) =====
section
-- New for lvm2 (roll 8 = B1, wave L, L-C): the typed backend's middle phases (`midT₂ Ti`) follow the typed schedule
-- (`LvmSchedule.phases` at the refreeze `S2GB1`: `phasesT`'s items under the old phase names; lvm2 roll 11, M′: the
-- whole `P_S` is `PSWithM`, `LvmMPVEqFol.fol_PSTM`).

/-!
# The typed `P_S` follows the schedule

* The typed items (`zeroI` … `miniTabI`, `typedI`) and the schedule by phase (`phases_eq`, `schedule_eq`,
  `midItems_eq`) are `LvmVEqFolMid`'s; `atomsOf_schedule` is `LvmVEqFolPS`'s.
* **`folP_typedProg`**: `typedProg Ti pub` against `typedI p` (the record's mini-bus numbers are `Ti.mbT`'s);
  **`folP_midT₂`**: `midT₂ Ti x` against `midItems`; **`midFollows_midT₂`**: WP-14d's `MidFollows (midT₂ Ti)`
  (lvm2 roll 11, M′: the whole `P_S` is `LvmMPVEqFol.fol_PSTM`, B1's two-root `fol_PST` is gone).

A `Fol` at concrete atoms is applied with `@` (the default application elaborator would unfold it).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgRec20G)

/-! ## The typed phases -/

section Typed

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- The mini-bus against `miniBusI ++ miniTabI`. -/
theorem folP_miniBusProg (Ti : Typed.TInst) (hl : p.leafdecReads = 1) (hd : p.busDepth = Typed.miniDepth)
    (hr : p.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : p.tableEvals = (Ti.mbT.map (·.w)).sum) :
    FolP cap shp idx (Typed.miniBusProg Ti) (atomsOf p (miniBusI p ++ miniTabI p)) fun _ ↦ True := by
  have hb : FolP cap shp idx (M3.lvmBusProg Typed.miniDepth) (atomsOf p (miniBusI p)) fun _ ↦ True := by
    have h := folP_lvmBusProg (cap := cap) (shp := shp) (idx := idx) p hl
    rw [hd] at h
    exact h
  have e : atomsOf p (miniBusI p ++ miniTabI p) = atomsOf p (miniBusI p) ++
      (.sm :: (atomsOf p (sumcheckI (((M3.vLayout Ti.mbT).tableLogHeights).foldl max 0) 3) ++
        List.replicate ((M3.vTables Ti.mbT).map (·.width)).sum .rd)) := by
    simp only [miniTabI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
      atomsOf_rd, width_vTables, M3.vLayout, ← hr, ← he]
    rfl
  rw [e, ← List.append_nil (_ ++ _)]
  unfold Typed.miniBusProg M3.lbusTableCheckProg M3.lvmBusTableProg
  exact (hb.bind fun b _ ↦
    folP_tablePhaseClaims p (M3.vTables _) (M3.vLayout _) _ (by simp [M3.vLayout])
      (by simp [M3.busResV, M3.busFinalV])).bind fun _ _ ↦
    (folP_require _).bind_ret fun _ _ ↦ trivial

end Typed

end Lvm.VEq
end
-- ===== end of `LvmTypedVEqFol` =====

-- ===== merged from `LvmTypedVEqPhases` (GOLF module merge: `LvmTypedVEqPhases.lean` is now a stub importing `LvmTypedVEqTop`) =====
section
-- New for lvm2 (roll 8 = B1, wave L, L-C): V_S's typed phases (`LvmTypedV`: `dZeroT`, `dWiringT`, `dRelayT`,
-- `dAccT`, `dMiniT`, `dTypedT`) refine the specification's (`LvmTypedSpec`: `zeroProg`, `wireProg`, `relayProg`,
-- `accProgQ`, `miniBusProg`, `typedProg`) on the stream, read for read.

/-!
# The typed phases: V_S refines the specification

On the native instance `N` with `TRefHyp N Q lay` (the shape check, the regions the layout's, the record the
mini-bus's, every mini-bus table a sumcheck table, `N.phi` the specification's `Φ_Q` on `43` coordinates) and
`Ti = N.inst Q lay`:

* `ref_dZeroT`, `ref_dWiringT` (`virtEF_rel`), `ref_dRelayT` (`relayKernF_rel`): the zerocheck, the wiring and the
  relayout, values mapped by `FE.toExt3`;
* `ref_dAccT`: A23 at `Φ_Q` under the promise that the folded claim holds natively (`N.phi a.pt = a.y`, which
  `decideFT` checks after the run), as roll 7's `ref_accFold`;
* `ref_dMiniT`: the mini-bus (WP-9b's bus and table phase, then the fixed columns: `tableCheckVB_of_R`);
* **`ref_dTypedT`**: the typed phases against `typedProg Ti pub` (`TRelT`: the native claims are `typedClaimsN`
  of the values whose images the specification's `typedClaims` takes, the mini-bus's claims those of its
  evaluations).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs AllSc lbusTableCheckProg)

/-- **What the typed refinement needs of the native instance** (INT's `StaticFactsT` gives `ok`, `hlay`, `mini`;
`THyp.sc` gives `sc`; `PhiQC_eq` with `cacheT20_eq` gives `phi`). -/
structure TRefHyp (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) : Prop where
  /-- The shape check the closed forms rely on. -/
  ok : N.okB P20.nuMain P20.nuRec = true
  /-- The native regions are the layout's. -/
  hlay : N.layOk lay = true
  /-- The record is the mini-bus's. -/
  mini : fitsMiniB P20 N.mbT = true
  /-- Every mini-bus table takes part in the table sumcheck. -/
  sc : AllSc N.mbT
  /-- V_S's `Φ_Q` is the specification's at `43` coordinates. -/
  phi : ∀ pt : List FE, pt.length = phiVars → N.phi pt = PhiQF Q lay pt

namespace TRefHyp

variable {N : TNat} {Q : Lvm.Loop.Program} {lay : Lay}

/-- Every mini-bus table is a sumcheck table. -/
theorem sc_eq (H : TRefHyp N Q lay) : sumcheckTabs N.mbT = N.mbT := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  rcases H.sc t ht with h | h <;> simp [h]

/-- The record's mini-bus numbers (`fitsMiniB`). -/
theorem fits (H : TRefHyp N Q lay) : P20.leafdecReads = 1 ∧
    P20.tableRounds = (N.mbT.map (·.τ)).foldl max 0 ∧ P20.tableEvals = (N.mbT.map (·.w)).sum ∧
    M3.colsFitB P20 N.mbT = true ∧ M3.colsHiB N.mbT = true := by
  have h := H.mini
  unfold fitsMiniB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hl, -⟩, -⟩, -⟩, hr⟩, he⟩, hc⟩, hh⟩, -⟩ := h
  rw [H.sc_eq] at hr he
  exact ⟨hl, hr, he, hc, hh⟩

end TRefHyp

/-- The mini-bus's depth at `P20`. -/
theorem busDepth_P20 : P20.busDepth = miniDepth := by decide +kernel

section Phases

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **The zerocheck.** -/
theorem ref_dZeroT :
    RefAt cap occ shp sig dZeroT zeroProg fun z z' ↦
      z' = (z.1.map FE.toExt3, FE.toExt3 z.2.1, FE.toExt3 z.2.2.1, FE.toExt3 z.2.2.2) ∧ z.1.length = xVars := by
  unfold dZeroT zeroProg
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) ((ref_samples _).retD (retD_samples _)) ?_
  rintro tau _ ⟨rfl, htau⟩
  have hs := (ref_sumcheck (cap := cap) (occ := occ) (shp := shp) (sig := sig) 3 (tau.map some) 0).retD
    (retD_sumcheck 3 (tau.map some) 0)
  rw [FE.toExt3_zero, List.map_map,
    show (Option.map FE.toExt3 ∘ some) = (some ∘ FE.toExt3) from rfl, ← List.map_map] at hs
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf _ ⟨rfl, hrf⟩
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro abc _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · simp only [getD_map_toExt3]
    rw [← FE.toExt3_mul, ← FE.toExt3_add]
    exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq hc)
  · intro _ _ _
    refine RefAt.pure ⟨?_, ?_⟩
    · simp only [getD_map_toExt3]
    · rw [hrf, List.length_map, htau]

/-- **The wiring** (`virtEF_rel`). -/
theorem ref_dWiringT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (pub : Pub)
    (abc : FE × FE × FE) :
    RefAt cap occ shp sig (dWiringT N pub abc)
      (wireProg (N.inst Q lay) pub (FE.toExt3 abc.1, FE.toExt3 abc.2.1, FE.toExt3 abc.2.2)) fun w w' ↦
        w' = (w.1.map FE.toExt3, w.2.1.map FE.toExt3, w.2.2.map FE.toExt3) ∧ w.1.length = yVars ∧
          w.2.1.length = 4 ∧ w.2.2.length = 4 := by
  unfold dWiringT wireProg
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) ref_sampleE ?_
  rintro g _ rfl
  have hs := (ref_sumcheck (cap := cap) (occ := occ) (shp := shp) (sig := sig) 3
    (List.replicate yVars none) (abc.1 + g * abc.2.1 + g * g * abc.2.2)).retD
    (retD_sumcheck 3 (List.replicate yVars none) _)
  rw [map_replicate_none] at hs
  simp only [FE.toExt3_add, FE.toExt3_mul] at hs
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf _ ⟨rfl, hrf⟩
  rw [List.length_replicate] at hrf
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (ref_readEsL _) ?_
  rintro vs _ ⟨rfl, hvs⟩
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_readEsL _) ?_
  rintro rv _ ⟨rfl, hrv⟩
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · simp only [getD_map_toExt3]
    rw [sumE_map, ← virtEF_rel N Q lay P20.nuMain P20.nuRec H.ok H.hlay pub rf.1 hrf]
    simp only [← FE.toExt3_mul, ← FE.toExt3_add]
    exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq hc)
  · intro _ _ _
    exact RefAt.pure ⟨rfl, hrf, hvs, hrv⟩

/-- **The relayout** (`relayKernF_rel`). -/
theorem ref_dRelayT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (ry : List FE)
    (hry : ry.length = yVars) (vS : FE) :
    RefAt cap occ shp sig (dRelayT N ry vS) (relayProg (N.inst Q lay) (ry.map FE.toExt3) (FE.toExt3 vS))
      fun r r' ↦ r' = (r.1.map FE.toExt3, FE.toExt3 r.2) ∧ r.1.length = relayRoundsN := by
  unfold dRelayT relayProg
  have hs := (ref_sumcheck (cap := cap) (occ := occ) (shp := shp) (sig := sig) 3
    (List.replicate relayRoundsN none) vS).retD (retD_sumcheck 3 (List.replicate relayRoundsN none) _)
  rw [map_replicate_none] at hs
  refine RefAt.bind (fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf _ ⟨rfl, hrf⟩
  rw [List.length_replicate] at hrf
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) ref_readE ?_
  rintro vR _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · rw [← relayKernF_rel N Q lay P20.nuMain P20.nuRec H.ok H.hlay ry rf.1 hry hrf, ← FE.toExt3_mul]
    exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq hc)
  · intro _ _ _
    exact RefAt.pure ⟨rfl, hrf⟩

/-- **A23 at `Φ_Q`** under the promise that the folded claim holds natively. -/
theorem ref_dAccT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = phiVars) (rxy vs : List FE) (hrxy : rxy.length = xVars + yVars) :
    RefAtP cap occ shp sig (dAccT pub rxy vs)
      (accProgQ Q lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (rxy.map FE.toExt3)
        (vs.map FE.toExt3))
      (fun _ _ ↦ True) (fun a ↦ N.phi a.pt = a.y) := by
  unfold dAccT accProgQ Lvm.Acc.accProg
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_readEs _).bind fun _ ↦
    monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (((ref_samples _).retD (retD_samples _)).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro κ _ ⟨rfl, hκ⟩ -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    ((ref_readEsL _).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro h _ ⟨rfl, -⟩ -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ monoD_readE.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    (ref_sampleE.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro t _ rfl -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (ref_readE.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro z _ rfl -
  refine RefAtP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    MonoD.pure _) fun h0 ↦ ?_
  refine RefAtP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) fun h1 ↦ ?_
  refine RefAtP.require_left (fun _ ↦ MonoD.pure _) fun hz ↦ ?_
  refine RefAtP.pure_require fun hA ↦ ?_
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [Lvm.Acc.hEval_zero, ← toExt3_headD, Lvm.M3.FE_eq_of_beq h0]
  · rw [Lvm.Acc.hEval_one, sumE_map, Lvm.M3.FE_eq_of_beq h1, yOwnQ, ← map_eqKernel, toExt3_dot]
  · rw [Lvm.M3.FE_eq_of_beq hz, FE.toExt3_zero]
  · have hlen : (accLine pub.accIn.pt (κ ++ rxy) t).length = phiVars := by
      rw [length_accLine, hacc, List.length_append, hκ, hrxy]; rfl
    rw [bOfQ, ← List.map_append, line_map, PhiQ, List.map_map,
      show (FE.ofExt3 ∘ FE.toExt3) = id from funext FE.ofExt3_toExt3, List.map_id, hEval_map,
      ← H.phi _ hlen]
    exact congrArg FE.toExt3 hA

/-- **The mini-bus**: the bus at the record's depth, the table sumcheck, the fixed columns natively. -/
theorem ref_dMiniT (p : Params) (tabs : List Tab) (pub : Pub) (hl : p.leafdecReads = 1)
    (hd : p.busDepth = miniDepth) (hr : p.tableRounds = (tabs.map (·.τ)).foldl max 0)
    (hsc : sumcheckTabs tabs = tabs) :
    RefAt cap occ shp sig (dMiniT p (M3.real p fun _ ↦ tabs) tabs pub) (lbusTableCheckProg tabs miniDepth)
      fun evs cl ↦ cl = claimsOfEvs tabs evs ∧ EvLen tabs evs ∧
        List.Forall₂ CRel (tableClaimsR tabs evs) (tableClaimsE tabs cl) := by
  have e : dMiniT p (M3.real p fun _ ↦ tabs) tabs pub =
      ((dBus p (M3.real p fun _ ↦ tabs) pub >>= fun pb ↦
        dTab p (M3.real p fun _ ↦ tabs) pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev)) >>= fun r ↦
          DM.require (M3.tableCheckR (sumcheckTabs tabs) r.2) >>= fun _ ↦ pure r.2) := by
    simp only [dMiniT, dBus, dTab, bind_assoc, pure_bind]
  rw [e]
  have h := ref_busTabP (cap := cap) (occ := occ) (shp := shp) (sig := sig) p (fun _ ↦ tabs) pub hl
    (by rw [hsc]; exact hr)
  simp only [hsc, hd] at h
  unfold lbusTableCheckProg
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) h ?_
  rintro r cl ⟨-, hcl, rfl, hlen⟩
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · rw [hsc] at hc
    exact Lvm.M3.tableCheckVB_of_R _ _ hc fun j h1 h2 ↦ (hlen j h1 h2).le
  · intro _ _ _
    exact RefAt.pure ⟨rfl, hlen, hcl⟩

end Phases

theorem runD_bind_pure_fst {β γ δ : Type} (d : DM β) (a : γ) (f : β → δ) (sig : ByteArray) (s : RS) :
    (runD (d >>= fun k ↦ Pure.pure (a, f k)) sig s).1.1 = a := rfl

theorem monoD_dWiringT (N : TNat) (pub : Pub) (abc : FE × FE × FE) : MonoD (dWiringT N pub abc) :=
  monoD_sampleE.bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dRelayT (N : TNat) (ry : List FE) (vS : FE) : MonoD (dRelayT N ry vS) :=
  (monoD_sumcheck _ _ _).bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dAccT (pub : Pub) (rxy vs : List FE) : MonoD (dAccT pub rxy vs) :=
  (monoD_samples _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dMiniT (p : Params) (m : M3) (tabs : List Tab) (pub : Pub) : MonoD (dMiniT p m tabs pub) :=
  (monoD_samples _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_verifyGkrGrandProducts _).bind fun ⟨_, _, _⟩ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        (monoD_tableSumcheck _ _ _ _ _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dZeroT : MonoD dZeroT :=
  (monoD_samples _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dTypedT (p : Params) (N : TNat) (m : M3) (pub : Pub) : MonoD (dTypedT p N m pub) :=
  monoD_dZeroT.bind fun _ ↦ (monoD_dWiringT _ _ _).bind fun _ ↦ (monoD_dRelayT _ _ _).bind fun _ ↦
    (monoD_dAccT _ _ _).bind fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _

/-- **The typed phases' native results against the specification's claims**: the native claims are
`typedClaimsN` of values (`r_y` of 21 coordinates, `r` of 19) whose images `typedClaims` takes, with the
mini-bus's claims those of its evaluations (`claimsOfEvs`), as many as its tables' columns. -/
def TRelT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay)
    (r : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) (a : Lvm.ASM.OpenClaims) : Prop :=
  ∃ ry rv rr : List FE, ∃ vR : FE, r.2.1 = typedClaimsN N P20 ry rv rr vR ∧ ry.length = yVars ∧
    rr.length = relayRoundsN ∧
    a = typedClaims (N.inst Q lay) (ry.map FE.toExt3) (rv.map FE.toExt3) (rr.map FE.toExt3) (FE.toExt3 vR)
      (claimsOfEvs N.mbT r.2.2) ∧
    EvLen N.mbT r.2.2 ∧ List.Forall₂ CRel (tableClaimsR N.mbT r.2.2) (tableClaimsE N.mbT (claimsOfEvs N.mbT r.2.2))

/-- **The typed phases refine `typedProg`** under the promise that the folded claim holds natively. -/
theorem ref_dTypedT {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} (N : TNat)
    (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (pub : Pub) (hacc : pub.accIn.pt.length = phiVars) :
    RefAtP cap occ shp sig (dTypedT P20 N (N.m3 P20) pub) (typedProg (N.inst Q lay) pub) (TRelT N Q lay)
      (fun r ↦ N.phi r.1.pt = r.1.y) := by
  obtain ⟨hl, hr, -, -, -⟩ := H.fits
  unfold dTypedT typedProg
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_dWiringT _ _ _).bind fun _ ↦
    (monoD_dRelayT _ _ _).bind fun _ ↦ (monoD_dAccT _ _ _).bind fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦
      MonoD.pure _) (ref_dZeroT.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro z _ ⟨rfl, hz⟩ -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_dRelayT _ _ _).bind fun _ ↦
    (monoD_dAccT _ _ _).bind fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((ref_dWiringT N Q lay H pub z.2).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro w _ ⟨rfl, hry, hvs, hrv⟩ -
  have hR := ref_dRelayT (cap := cap) (occ := occ) (shp := shp) (sig := sig) N Q lay H w.1 hry (w.2.2.getD 1 0)
  rw [← getD_map_toExt3] at hR
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_dAccT _ _ _).bind fun _ ↦
    (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _) (hR.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro r _ ⟨rfl, hrr⟩ -
  have hA : RefAtP cap occ shp sig (dAccT pub (z.1 ++ w.1) w.2.1)
      (accProgQ (N.inst Q lay).Q (N.inst Q lay).lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3)
        (z.1.map FE.toExt3 ++ w.1.map FE.toExt3) (w.2.1.map FE.toExt3)) (fun _ _ ↦ True)
      (fun a ↦ N.phi a.pt = a.y) := by
    rw [← List.map_append]
    exact ref_dAccT N Q lay H pub hacc (z.1 ++ w.1) w.2.1 (by rw [List.length_append, hz, hry])
  dsimp only
  refine RefAtP.bind (Q := fun a ↦ N.phi a.pt = a.y) (fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _)
    hA (fun _ _ h ↦ by rw [runD_bind_pure_fst] at h; exact h) ?_
  intro acc _ _ _
  have hM := ref_dMiniT (cap := cap) (occ := occ) (shp := shp) (sig := sig) P20 N.mbT pub hl busDepth_P20 hr
    H.sc_eq
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) (hM.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro evs cl ⟨rfl, hlen, hcl⟩ -
  exact (RefAt.pure ⟨w.1, w.2.2, r.1, r.2, rfl, hry, hrr, rfl, hlen, hcl⟩).toP _

end Lvm.VEq
end
-- ===== end of `LvmTypedVEqPhases` =====

-- ===== merged from `LvmVEqStatic` (GOLF module merge: `LvmVEqStatic.lean` is now a stub importing `LvmTypedVEqTop`) =====
section
-- New for lvm (WP-14a): the static facts of P20's schedule the simulation needs, decided once.

/-!
# P20's schedule meets the static check

`stA_P20`: every Fiat–Shamir query of `schedule P20` is within `queryCap`, nothing is pending at an
opening or at the end, the caps come in `idxS` order (each oracle once), and every opening's level
geometry is P20's commitment table, its positions of the commitment's height. One kernel
evaluation over the items (`LvmReplay.P20_eq` gives the levels as literals): `stI` is `stA` on
the items' atoms (`stA_atomsOf`), a read of `m` scalars one step instead of `m` atoms (WP-16b).
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm

/-- `stA` over the `ps` atoms of a positions item, then `k`. -/
def stPos (h : ℕ) : ℕ → ℕ → List ℕ → (ℕ → List ℕ → Bool) → Bool
  | 0, pend, hs, k => k pend hs
  | n + 1, pend, hs, k => decide (32 + pend ≤ queryCap) && stPos h n 0 (h :: hs) k

/-- **`stA` on the items** (`stA_atomsOf`). -/
def stI (p : Params) : List Item → ℕ → List Ref → List ℕ → optParam (ℕ → ℕ → ℕ) occS → Bool
  | [], pend, _, _, _ => pend == 0
  | .read m :: its, pend, cr, hs, occ => stI p its (pend + eBytes * m) cr hs occ
  | .readW m w :: its, pend, cr, hs, occ => stI p its (pend + w * m) cr hs occ
  | .cap c r :: its, pend, cr, hs, occ =>
    (idxS r == cr.length) && !(cr.contains r) && stI p its (pend + nodeBytes * 2 ^ c) (cr ++ [r]) hs occ
  | .sample :: its, pend, cr, hs, occ => decide (32 + pend ≤ queryCap) && stI p its 0 cr hs occ
  | .positions r :: its, pend, cr, _, occ =>
    stPos (p.level r).height (p.level r).nPosQ pend [] fun pend hs => stI p its pend cr hs occ
  | .opening r :: its, pend, cr, hs, occ =>
    (pend == 0) && cr.contains r && geomOk p r occ && hs.all (· == (shpS (idxS r)).1) && stI p its 0 cr hs occ

theorem stA_reads (p : Params) (as : List Atom) (cr : List Ref) (hs : List ℕ) (occ : ℕ → ℕ → ℕ) :
    ∀ (m pend : ℕ), stA p (List.replicate m .rd ++ as) pend cr hs occ = stA p as (pend + eBytes * m) cr hs occ
  | 0, pend => rfl
  | m + 1, pend => by
    rw [List.replicate_succ, List.cons_append, stA, stA_reads p as cr hs occ m, Nat.mul_succ]
    congr 1
    omega

theorem stA_readsW (p : Params) (w : ℕ) (as : List Atom) (cr : List Ref) (hs : List ℕ) (occ : ℕ → ℕ → ℕ) :
    ∀ (m pend : ℕ), stA p (List.replicate m (.rdw w) ++ as) pend cr hs occ = stA p as (pend + w * m) cr hs occ
  | 0, pend => rfl
  | m + 1, pend => by
    rw [List.replicate_succ, List.cons_append, stA, stA_readsW p w as cr hs occ m, Nat.mul_succ]
    congr 1
    omega

theorem stA_pos (p : Params) (as : List Atom) (cr : List Ref) (h : ℕ) (occ : ℕ → ℕ → ℕ) :
    ∀ (n rem pend : ℕ) (hs : List ℕ), stA p (posAtoms h n rem ++ as) pend cr hs occ =
      stPos h n pend hs fun pend hs => stA p as pend cr hs occ
  | 0, _, _, _ => rfl
  | n + 1, rem, pend, hs => by
    rw [posAtoms, List.cons_append, stA, stA_pos p as cr h occ n, stPos]

/-- `stA` over a schedule's atoms is `stI` over its items, at any occupied words `occ`. -/
theorem stA_atomsOf (p : Params) {occ : ℕ → ℕ → ℕ} : ∀ (its : List Item) (pend : ℕ) (cr : List Ref) (hs : List ℕ),
    stA p (atomsOf p its) pend cr hs occ = stI p its pend cr hs occ
  | [], _, _, _ => rfl
  | it :: its, pend, cr, hs => by
    rw [atomsOf_cons]
    cases it with
    | read m => rw [itemAtoms, stA_reads, stI, stA_atomsOf p its]
    | readW m w => rw [itemAtoms, stA_readsW, stI, stA_atomsOf p its]
    | cap c r => rw [itemAtoms, List.singleton_append, stA, stI, stA_atomsOf p its]
    | sample => rw [itemAtoms, List.singleton_append, stA, stI, stA_atomsOf p its]
    | positions r =>
      rw [itemAtoms, List.cons_append, stA, stA_pos, stI]
      congr 1
      funext pend hs
      exact stA_atomsOf p its pend cr hs
    | opening r => rw [itemAtoms, List.singleton_append, stA, stI, stA_atomsOf p its]

private theorem nw_append {a b : List Item} (ha : noWB a = true) (hb : noWB b = true) : noWB (a ++ b) = true := by
  rw [noWB, List.all_append, Bool.and_eq_true]; exact ⟨ha, hb⟩

private theorem nw_flatten {L : List (List Item)} (h : ∀ l ∈ L, noWB l = true) : noWB L.flatten = true := by
  rw [noWB, List.all_eq_true]
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 hx
  exact List.all_eq_true.1 (h l hl) x hx

private theorem nw_rep {n : ℕ} {l : List Item} (h : noWB l = true) : noWB (List.replicate n l).flatten = true :=
  nw_flatten fun _ hl' => (List.eq_of_mem_replicate hl') ▸ h

private theorem nw_rd (m : ℕ) : noWB (rd m) = true := by unfold rd; split <;> rfl

private theorem nw_smp (n : ℕ) : noWB (smp n) = true := by
  rw [noWB, List.all_eq_true]; intro x hx; unfold smp at hx; rw [List.eq_of_mem_replicate hx]; rfl

private theorem nw_sumcheckI (r d : ℕ) : noWB (sumcheckI r d) = true := nw_rep (nw_append (nw_rd d) rfl)

private theorem nw_keccakLayerI (pt : ℕ) : noWB (keccakLayerI pt) = true := by
  refine nw_flatten ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro l (rfl | rfl | rfl | rfl | rfl | rfl) <;> first | exact nw_rd _ | exact nw_smp _ | exact nw_sumcheckI _ _

private theorem nw_keccakI (ls : ℕ) : noWB (keccakI ls) = true := by
  refine nw_flatten ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro l (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    first | exact nw_rd _ | exact nw_smp _ | exact nw_sumcheckI _ _ | exact nw_rep (nw_keccakLayerI _)

private theorem nw_tapeLayersI (ls : ℕ) : noWB (tapeLayersI ls) = true :=
  nw_append (nw_smp _) (nw_rep (nw_keccakLayerI _))

private theorem nw_gpLayersI : ∀ (fuel layer point : ℕ), noWB (gpLayersI fuel layer point) = true
  | 0, _, _ => rfl
  | fuel + 1, layer, point => by
    rw [gpLayersI]
    split
    · rfl
    · refine nw_append (nw_flatten ?_) (nw_gpLayersI fuel _ _)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro l (rfl | rfl | rfl | rfl) <;>
        first | exact nw_rd _ | exact nw_smp _ | exact nw_rep (nw_append (nw_rd _) (nw_smp _))

private theorem nw_tailI : ∀ n : ℕ, noWB (tailI n) = true
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [tailI, noWB, List.all_cons, List.all_cons]
    exact nw_tailI (n + 1)

private theorem nw_grindI (g : ℕ) : noWB (grindI g) = true := by unfold grindI; split <;> rfl

private theorem nw_levelI (com : Com) (fl g : ℕ) (L : Level) (next : Option Level) :
    noWB (levelI com fl g L next) = true := by
  cases next <;>
  · refine nw_flatten ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      first
        | rfl
        | exact nw_rd _
        | exact nw_smp _
        | exact nw_grindI _
        | exact nw_tailI _
        | exact nw_rep (nw_append (nw_smp _) (nw_rd _))

private theorem nw_levelIJ (com : Com) (fl g : ℕ) (L : Level) (next : Option Level) :
    noWB (levelIJ com fl g L next) = true := by
  cases next <;>
  · refine nw_flatten ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      first
        | rfl
        | exact nw_rd _
        | exact nw_smp _
        | exact nw_grindI _
        | exact nw_tailI _
        | exact nw_rep (nw_append (nw_smp _) (nw_rd _))
        | exact nw_append (nw_append (nw_append rfl (nw_smp _)) (nw_rd _)) (nw_rd _)

private theorem nw_whirLevelsI (com : Com) (fl g : ℕ) : ∀ Ls : List Level, noWB (whirLevelsI com fl g Ls) = true
  | [] => rfl
  | [L] => nw_levelI com fl g L none
  | L :: N :: rest => nw_append (nw_levelI com fl g L (some N)) (nw_whirLevelsI com fl g (N :: rest))

private theorem nw_whirLevelsIJ (com : Com) (fl g : ℕ) : ∀ Ls : List Level, noWB (whirLevelsIJ com fl g Ls) = true
  | [] => rfl
  | [L] => nw_levelIJ com fl g L none
  | L :: N :: rest => nw_append (nw_levelIJ com fl g L (some N)) (nw_whirLevelsIJ com fl g (N :: rest))

/-- Stage `0`'s schedule has no `readW`, by the builders (GOLF3: deciding it on `P20`'s 2,489 items cost the
kernel 2.6 M heartbeats). -/
private theorem noWB_stage0 (p : Params) (h1 : p.stage ≠ 1) (h2 : p.stage ≠ 2) (h3 : p.stage ≠ 3) :
    noWB (schedule p) = true := by
  rw [schedule, phases, if_neg h1, if_neg h2, if_neg h3, noWB, List.all_eq_true]
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatMap.1 hx
  suffices hl2 : noWB l.2 = true from List.all_eq_true.1 hl2 x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals first
    | exact nw_append (nw_smp _) (by
        split
        · exact nw_append (nw_rd _) (nw_whirLevelsIJ _ _ _ _)
        · exact nw_append (nw_rd _) (nw_whirLevelsI _ _ _ _))
    | (refine nw_flatten ?_
       simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
       and_intros <;>
         first
           | exact nw_rd _
           | exact nw_smp _
           | exact nw_sumcheckI _ _
           | exact nw_append (nw_rd _) (nw_gpLayersI _ _ _)
           | exact nw_tapeLayersI _
           | exact nw_keccakI _)

/-- `P20`'s schedule has no `readW` (stage `0`). -/
theorem noWB_P20 : noWB (schedule P20) = true :=
  noWB_stage0 P20 (by decide) (by decide) (by decide)

/-! ## Read widths of a stage-0 schedule -/

theorem widthsA_append (a b : List Atom) : widthsA (a ++ b) = widthsA a ++ widthsA b := by
  induction a with
  | nil => rfl
  | cons x a ih => cases x <;> simp [widthsA, ih]

theorem widthsA_replicate_rd (m : ℕ) : widthsA (List.replicate m .rd) = List.replicate m 24 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.replicate_succ, ← ih]; rfl

theorem widthsA_posAtoms (h : ℕ) : ∀ (n rem : ℕ), widthsA (posAtoms h n rem) = []
  | 0, _ => rfl
  | n + 1, rem => widthsA_posAtoms h n _

/-- **Without `readW`, every read of the atoms takes 24 bytes.** -/
theorem mem_widthsA_atomsOf (p : Params) : ∀ (its : List Item), noWB its = true →
    ∀ x ∈ widthsA (atomsOf p its), x = 24
  | [], _, x, hx => by simp [widthsA] at hx
  | it :: its, h, x, hx => by
    simp only [noWB, List.all_cons, Bool.and_eq_true] at h
    rw [atomsOf_cons, widthsA_append, List.mem_append] at hx
    rcases hx with hx | hx
    · cases it with
      | read m =>
        rw [itemAtoms, widthsA_replicate_rd] at hx
        exact List.eq_of_mem_replicate hx
      | readW m w => simp [Item.isW] at h
      | positions r =>
        simp [itemAtoms, widthsA, widthsA_posAtoms] at hx
      | _ => simp [itemAtoms, widthsA] at hx
    · exact mem_widthsA_atomsOf p its h.2 x hx

end Lvm.VEq
end
-- ===== end of `LvmVEqStatic` =====

-- ===== merged from `LvmVEqMain` (GOLF module merge: `LvmVEqMain.lean` is now a stub importing `LvmTypedVEqTop`) =====
section
-- New for lvm (WP-14a): V_S's acceptance implies the compiled S.V's (obligation O5b, WP-14's
-- `OpenS.refines`), from the value refinement (`ref_decide`), the query correspondence (`sim`), the
-- schedule's shape (`Fol`) and its static facts (`stA_P20`).

/-!
# V_S ⇒ S.V

**`refines_seqOf`**: for every key, statement, proof and trace, if `V_S = VSL P20 tabs` accepts the
proof on the trace, so does WP-5's compiled verifier of WP-14's `P_S = PSWith mid`, for any middle phases
`mid` that V_S's decision refines (`RefD`; roll 7: `ref_decide` gives it for `midS₂ tabs`).
**`refines_logOf`/`refines_logF`** are the same on every log (the form of `OpenS.refines`): the trace
`V_S` asks on the log is answered by the log, and the compiled verifier asks the same queries.
The headline without the shape hypothesis is `LvmVEqRefines.refines_VSL`.

The proof: `V_S`'s header check gives the compiled verifier's header (`hdrS`, `okS`), its driver's
acceptance gives the stream `Σ = traceBytesB tr` on which `F` holds; `RefD` turns `F` into the
program `P_S x` read off `Σ` returning `true`; `sim` (with `Fol` of `P_S x` against the schedule's
atoms and `stA_P20`) runs the compiled verifier on the same trace to the same verdict.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

theorem capOfS_eq : Lvm.ASM.capOfS = capS := rfl

theorem occOfS_eq : Lvm.ASM.occOfS = occS := rfl

theorem size_q0Query : q0Query.size = 7 := rfl

/-! ## From traces to logs -/

/-- The trace a program asks on a log (answers by the log's first matching entry). -/
def traceOf {α : Type} (L : Log) : OProg α → Trace
  | .ret _ => []
  | .query q k => match L.find? (fun e ↦ e.1 = q) with
    | some e => (q, e.2) :: traceOf L (k e.2)
    | none => []

theorem runSeq_traceOf {α : Type} (L : Log) : ∀ (p : OProg α) {b : α}, p.runLog L = some b →
    p.runSeq (traceOf L p) = some b
  | .ret a, b, h => by simpa [OProg.runLog, traceOf, OProg.runSeq] using h
  | .query q k, b, h => by
    simp only [OProg.runLog] at h
    simp only [traceOf]
    cases he : L.find? (fun e ↦ decide (e.1 = q)) with
    | none => rw [he] at h; simp at h
    | some e =>
      rw [he] at h
      simp only [Option.bind_some] at h
      simp only [OProg.runSeq, ↓reduceIte]
      exact runSeq_traceOf L (k e.2) h

/-- Every entry of the trace a program asks on a log is the log's answer. -/
def LogCons (L : Log) (tr : Trace) : Prop :=
  ∀ e ∈ tr, ∃ e', L.find? (fun x ↦ decide (x.1 = e.1)) = some e' ∧ e'.2 = e.2

theorem logCons_traceOf {α : Type} (L : Log) : ∀ p : OProg α, LogCons L (traceOf L p)
  | .ret _ => fun e he ↦ by simp [traceOf] at he
  | .query q k => by
    intro e he
    simp only [traceOf] at he
    cases hf : L.find? (fun x ↦ decide (x.1 = q)) with
    | none => rw [hf] at he; simp at he
    | some e' =>
      rw [hf] at he
      rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨e', hf, rfl⟩
      · exact logCons_traceOf L (k e'.2) e he'

theorem runLog_of_runSeq {α : Type} (L : Log) : ∀ (p : OProg α) (tr : Trace) {b : α}, LogCons L tr →
    p.runSeq tr = some b → p.runLog L = some b
  | .ret a, tr, b, _, h => by
    rcases tr with _ | ⟨e, tr⟩
    · simpa [OProg.runSeq, OProg.runLog] using h
    · simp [OProg.runSeq] at h
  | .query q k, tr, b, hc, h => by
    rcases tr with _ | ⟨⟨q', a⟩, tr⟩
    · simp [OProg.runSeq] at h
    · simp only [OProg.runSeq] at h
      split at h
      · rename_i hq
        subst hq
        obtain ⟨e', he', he2⟩ := hc (q', a) List.mem_cons_self
        simp only [OProg.runLog, he', Option.bind_some]
        rw [he2]
        exact runLog_of_runSeq L (k a) tr (fun e he ↦ hc e (List.mem_cons_of_mem _ he)) h
      · simp at h

/-- **Acceptance on every trace transfers to every log.** -/
theorem runLog_of_seq {p q : OProg Bool} (h : ∀ tr, p.runSeq tr = some true → q.runSeq tr = some true)
    (L : Log) (hp : p.runLog L = some true) : q.runLog L = some true :=
  runLog_of_runSeq L q _ (logCons_traceOf L p) (h _ (runSeq_traceOf L p hp))

section Main

variable (tabs : Pub → List M3.Tab) (mid : List UInt8 → LeanVM.Protocol.Compile.VerifierProgram
  (List VStackClaim × List VStackClaim))

end Main

end Lvm.VEq
end
-- ===== end of `LvmVEqMain` =====

/-!
# V_S ⇒ S.V, typed

* `dMidT`, `dTopT`, **`decideProgT_dTopT`**: `decideProgT` grouped as `P_S` (the cap, the typed phases and
  phases 4–7 as `midT₂`, the opening).
* `okB_dst`, `regsOf_dst`: `okB`'s facts on the region targets (M′: `σ′`'s on `C_main`).
* **`ref_dOpenT`**: the M′ opening (`C_main`'s claims, both shapes) refines `verifyStackedJ (cfgMain23Jq 1)`.
* `refines_seqOfT`: O5b on every trace, for any `PS` V_S's decision refines (`RefDT`) and that follows the
  schedule (roll 7's `refines_seqOf`, read for `VST`/`decideFT`).
* `trefHyp20`; **`midFollowsT20L`**: `LvmCertT20.midFollowsT20` (statement verbatim).
* (lvm2 roll 11, M′ `S2GM`: B1's `typedClaims_rel`, `ref_dMidT`, `ref_decideT`, `refines_VST`, `refinesT20L`
  targeted the two-root `PSWith` and are gone; their M′ forms are `LvmMPVEq`'s.)
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)

/-! ## `decideProgT` grouped as `P_S` -/

theorem nuMain_P20 : P20.nuMain = 23 := by decide +kernel

theorem nuRec_P20 : P20.nuRec = 19 := by decide +kernel

/-! ## The claims -/

/-- `okB`'s facts on a region's target (M′ `S2GM`: `σ′`'s regions are in `C_main`, as the committed block's and
`KS`'s; B1 had them in `C_rec`). -/
theorem okB_dst {N : TNat} {nuMain nuRec : ℕ} (h : N.okB nuMain nuRec = true) {g : NReg} (hg : g ∈ N.regs) :
    (g.src = .com ∨ g.src = .ks ∨ g.src = .sigma) → g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ nuMain := by
  unfold TNat.okB at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hs := (h.1.1.1.1.1 g hg).2
  rintro (he | he | he) <;> rw [he] at hs <;> simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs <;>
    exact ⟨hs.1.1, le_trans hs.2 (min_le_left _ _)⟩

theorem regsOf_dst {N : TNat} {nuMain nuRec : ℕ} (h : N.okB nuMain nuRec = true) (s : YSrc)
    (hs : s = .com ∨ s = .ks ∨ s = .sigma) :
    ∀ g ∈ N.regsOf s, g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ nuMain := by
  intro g hg
  simp only [TNat.regsOf, List.mem_filter, beq_iff_eq] at hg
  obtain ⟨hg, hgs⟩ := hg
  exact okB_dst h hg (hgs ▸ hs)

/-! ## The opening -/

section Ref

variable {sig : ByteArray}

theorem commitRootUd_mainT : Verifier.commitRootUd cfgMain24G = VerifierProgram.readCommitment 19 64 := rfl

end Ref

/-! ## V_S ⇒ S.V -/

section Main

variable (N : TNat) (PS : List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool)

end Main

/-! ## At `P20`: `LvmCertT20`'s stubs -/

end Lvm.VEq
