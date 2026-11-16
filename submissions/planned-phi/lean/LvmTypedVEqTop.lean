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

/-- **The root** against `commitI P20`. -/
theorem folP_commit : FolP capS shpS idxS (Verifier.commitRootUd cfgMain24G)
    (atomsOf P20 (commitI P20)) fun _ ↦ True := by
  rw [atomsOf_commitI]
  exact folP_commitRootUd cfgMain24G rfl cap_main0 rfl

theorem atomsOf_schedule : atomsOf P20 (schedule P20) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf P20 Lvm.ASM.midItems ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [schedule_eq P20 (by decide), midItems_eq]
  simp only [atomsOf_append, List.append_assoc, List.append_nil, atomsOf_commitI]

/-- **`P_S` at M′ follows the schedule** at P20 (`LvmMPCert.PSWithM mid x`'s body: one root, the middle phases,
`C_main`'s opening), for any middle phases that follow `midItems`. -/
theorem fol_PSOfM (mid : List UInt8 → VerifierProgram (List VStackClaim))
    (hmid : ∀ x, FolP capS shpS idxS (mid x) (atomsOf P20 Lvm.ASM.midItems) fun _ ↦ True) (x : List UInt8) :
    Fol capS shpS idxS (do
        Verifier.commitRootUd cfgMain24G
        let cl ← mid x
        Verifier.verifyStackedJ (cfgMain23Jq 1) cl
        return true) (atomsOf P20 (schedule P20)) [] fun _ _ ↦ True := by
  rw [atomsOf_schedule]
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine Fol.bindP (hmid x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

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

/-- The zerocheck against `zeroI`. -/
theorem folP_zeroProg : FolP cap shp idx Typed.zeroProg (atomsOf p zeroI) fun _ ↦ True := by
  simp only [zeroI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Typed.zeroProg
  exact (folP_sampleChallenges Typed.xVars).bind fun τ hτ ↦
    (folP_sumcheck p rfl (by norm_num) (τ.map some) Typed.xVars 0 (by simp [hτ])).bind fun _ _ ↦
    (folP_readScalars 3).bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

/-- The wiring against `wiringI`. -/
theorem folP_wireProg (Ti : Typed.TInst) (pub : Pub) (abc : E × E × E) :
    FolP cap shp idx (Typed.wireProg Ti pub abc) (atomsOf p wiringI) fun _ ↦ True := by
  simp only [wiringI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Typed.wireProg
  exact folP_sampleChallenge.bind fun _ _ ↦
    (folP_sumcheck p rfl (by norm_num) _ Typed.yVars _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 4).bind fun _ _ ↦ (folP_readScalars 4).bind_nil fun _ _ ↦
    (folP_require _).bind_ret fun _ _ ↦ trivial

/-- The relayout against `relayI`. -/
theorem folP_relayProg (Ti : Typed.TInst) (ry : List E) (vS : E) :
    FolP cap shp idx (Typed.relayProg Ti ry vS) (atomsOf p relayI) fun _ ↦ True := by
  simp only [relayI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rd]
  unfold Typed.relayProg
  exact (folP_sumcheck p rfl (by norm_num) _ TypedV.relayRoundsN _ (List.length_replicate ..)).bind fun _ _ ↦
    folP_readScalar.bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

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

/-- **The typed phases** against `typedI p`, the record's mini-bus numbers those of `Ti.mbT` (one
leaf-decomposition scalar, depth `miniDepth`, the tallest table's rounds, the widths' sum). -/
theorem folP_typedProg (Ti : Typed.TInst) (pub : Pub) (hl : p.leafdecReads = 1)
    (hd : p.busDepth = Typed.miniDepth) (hr : p.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0)
    (he : p.tableEvals = (Ti.mbT.map (·.w)).sum) :
    FolP cap shp idx (Typed.typedProg Ti pub) (atomsOf p (typedI p)) fun _ ↦ True := by
  simp only [typedI, atomsOf_append]
  rw [← atomsOf_append p (miniBusI p)]
  unfold Typed.typedProg
  exact (folP_zeroProg p).bind fun _ _ ↦ (folP_wireProg p Ti pub _).bind fun _ _ ↦
    (folP_relayProg p Ti _ _).bind fun _ _ ↦
    (folP_accProg p 2 TypedV.phiVarsN _ _ _ _ _ _).bind fun _ _ ↦
    (folP_miniBusProg p Ti hl hd hr he).bind_ret fun _ _ ↦ trivial

/-- **The typed middle phases follow `midItems`** (`P20`'s mini-bus numbers those of `Ti.mbT`). -/
theorem folP_midT₂ (Ti : Typed.TInst) (hl : P20.leafdecReads = 1) (hd : P20.busDepth = Typed.miniDepth)
    (hr : P20.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    FolP cap shp idx (Typed.midT₂ Ti x) (atomsOf P20 Lvm.ASM.midItems) fun _ ↦ True := by
  have e : atomsOf P20 Lvm.ASM.midItems = atomsOf P20 (typedI P20) ++
      atomsOf P20 (tapeI P20 ++ (wireI P20 ++ (ksI P20 ++ ksLinkI P20))) := by
    rw [midItems_eq]
    simp only [atomsOf_append, List.append_nil]
  rw [e]
  unfold Typed.midT₂
  exact (folP_typedProg P20 Ti (pubX x) hl hd hr he).bind fun _ _ ↦
    (folP_kgProgS _ _).bind_ret fun _ _ ↦ trivial

end Typed

/-- **WP-14d's shape obligation, typed**: every accepted run of `midT₂ Ti x` has the kinds of `midItems`. -/
theorem midFollows_midT₂ (Ti : Typed.TInst) (hl : P20.leafdecReads = 1) (hd : P20.busDepth = Typed.miniDepth)
    (hr : P20.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20.tableEvals = (Ti.mbT.map (·.w)).sum) :
    Lvm.ASM.MidFollows (Typed.midT₂ Ti) := by
  intro x l a hl'
  rw [(@fol_after capS shpS idxS _ (atomsOf P20 Lvm.ASM.midItems) (Typed.midT₂ Ti x) []
    (fun _ pp' ↦ pp' = []) (@FolP.fol capS shpS idxS _ (Typed.midT₂ Ti x) (atomsOf P20 Lvm.ASM.midItems)
      (fun _ ↦ True) (folP_midT₂ Ti hl hd hr he x) []) l a hl').1, atomKinds_atomsOf P20 _ midItems_noPos]

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

set_option maxRecDepth 200000 in
/-- `P20`'s schedule has no `readW` (stage `0`). -/
theorem noWB_P20 : noWB (schedule P20) = true := by
  rw [Lvm.Replay.P20_eq]; decide +kernel

set_option maxRecDepth 200000 in
/-- **The static check at P20.** -/
theorem stA_P20 : stA P20 (atomsOf P20 (schedule P20)) 0 [] [] = true := by
  rw [stA_atomsOf, schedule, phases_P20_lit, Lvm.Replay.P20_eq]; decide +kernel

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

/-- Widths that are all 24 at the constant width 24. -/
theorem wAt_24 {l : List ℕ} (h : ∀ x ∈ l, x = 24) (i : ℕ) : WAt (fun _ ↦ 24) i l := fun k hk ↦ by
  rw [List.getD_eq_getElem _ _ hk, h _ (List.getElem_mem hk)]

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

theorem entOff_one (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) :
    entOff ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) 1 = 48 := by
  simp [entOff, traceBytes_cons, traceBytes_nil, length_enc64, length_blb, size_q0Query]

theorem size_seedQuery (π : ByteArray) (a₀ : Digest) (hH : headerBytes ≤ π.size) :
    (seedQuery π a₀).size = 32 + (headerBytes - 8) := by
  rw [seedQuery, ByteArray.size_append, size_digestBytes, ← length_blb, blb_extract]
  simp [length_blb]; omega

theorem entOff_two (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) (hH : headerBytes ≤ π.size) :
    entOff ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) 2 = RS.start.ent := by
  have hd1 : ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest).drop 1 = (seedQuery π a₀, st₀) :: rest := rfl
  rw [(stream_entry hd1).2.2, entOff_one, size_seedQuery π a₀ hH]
  rfl

/-- The header bytes in the stream: the seed entry holds `π`'s bytes 8…4927. -/
theorem seed_bytes (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) (hH : headerBytes ≤ π.size) :
    ∀ t < headerBytes - 8, (traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest)).get!
      (headerAt 8 + t) = π.get! (8 + t) := by
  intro t ht
  have hd1 : ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest).drop 1 = (seedQuery π a₀, st₀) :: rest := rfl
  have he := (stream_entry hd1).1 (32 + t) 1 (by rw [size_seedQuery π a₀ hH]; omega)
  rw [entOff_one, show 48 + 8 + (32 + t) = headerAt 8 + t by simp [headerAt]; omega] at he
  have hg := getD_sb (traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest)) (headerAt 8 + t) 1 0
    (by omega)
  rw [Nat.add_zero] at hg
  rw [← hg, show sb = sbs from rfl, he, get!_blb]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_zero,
    seedQuery, blb_append, blb_digestBytes, List.getElem?_append_right (by simp),
    show 32 + t - (Vector.toList a₀).length = t by simp, blb_extract, List.getElem?_take_of_lt (by omega),
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem decideF_ok {p : Params} {m : M3} {vk c : Digest} {sig : ByteArray}
    (h : decideF p m vk c sig = true) : (runD (decideProg p m vk c) sig RS.start).2.ok = true := by
  rw [decideF_eq, Bool.and_eq_true] at h
  have h1 := h.1
  unfold decideCore DM.runOn at h1
  have e : (decideProg p m vk c sig).run RS.start = runD (decideProg p m vk c) sig RS.start := rfl
  rw [e] at h1
  rcases hr : runD (decideProg p m vk c) sig RS.start with ⟨u, s⟩
  rw [hr] at h1
  simp only [Bool.and_eq_true] at h1
  exact h1.1.1

/-- A23: `decideF` also checks the folded claim of the run (`AccOk`). -/
theorem decideF_acc {p : Params} {m : M3} {vk c : Digest} {sig : ByteArray}
    (h : decideF p m vk c sig = true) :
    AccOk p m (pubOf vk c sig) (runD (decideProg p m vk c) sig RS.start).1 = true := by
  rw [decideF_eq, Bool.and_eq_true] at h
  have h2 := h.2
  unfold accOutOf DM.runOn at h2
  have e : (decideProg p m vk c sig).run RS.start = runD (decideProg p m vk c) sig RS.start := rfl
  rw [e] at h2
  exact h2

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

/-- **V_S's decision refines `PSWith mid`** on every stream whose header is the statement's (roll 7:
the chain below is generic in the middle phases `mid`; `ref_decide` gives it for `midS₂ tabs`). -/
def RefD : Prop :=
  ∀ (sig : ByteArray) (vk c : Digest) (x : List UInt8), pubOf vk c sig = pubX x →
    RefAtP capS occS shpS sig (decideProg P20 (M3.real P20 tabs) vk c) (Lvm.ASM.PSWith mid x)
      (fun _ b ↦ b = true) (fun a ↦ AccOk P20 (M3.real P20 tabs) (pubX x) a = true)

/-- **V_S ⇒ S.V on a trace**, given the program's shape and the parse facts. -/
theorem refines_seqOf (href : RefD tabs mid)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith mid x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (hhdr : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.hdrS π = some (xOf π, (π.data.toList).drop headerBytes))
    (hok : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.okS vk c (xOf π) = true)
    (hpubeq : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true → ∀ {sig : ByteArray},
      (∀ t < headerBytes - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      pubOf vk c sig = pubX (xOf π))
    (vk c : Digest) (π : ByteArray) (tr : Trace)
    (h : (VSL P20 tabs vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)).V c π).runSeq tr = some true := by
  -- the header check
  unfold VSL VS at h
  by_cases hp : parseOk P20 vk c π = true
  swap
  · rw [if_neg hp] at h; exact absurd (runSeq_ret_true h).2 (by simp)
  rw [if_pos hp] at h
  have hp' := hp
  simp only [parseOk, Bool.and_eq_true, beq_iff_eq] at hp'
  have hsize : π.size = piSize P20 := hp'.1.1.1
  have hHle : headerBytes ≤ π.size := by rw [hsize, sizes_P20.1]; decide
  -- the driver: q₀, the seed, the schedule
  rw [drive_of (p := P20) rfl (by decide)] at h
  obtain ⟨a₀, tr1, rfl, h1⟩ := runSeq_query_cons h
  obtain ⟨st₀, rest, rfl, h2⟩ := runSeq_query_cons h1
  rw [driveItems_eq] at h2
  -- the driver's final state: the whole trace logged, the body used up, `F` on the stream
  obtain ⟨sf, n, hf1, hf2, -, -⟩ := drive_run P20 π _ _ _ rest h2
  obtain ⟨hnil, hb⟩ := runSeq_ret_true hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨-, hF⟩ := hb
  have hn : rest.take n = rest := List.take_of_length_le (List.drop_eq_nil_iff.mp hnil)
  have hlog : streamOf sf.log =
      traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) := by
    rw [streamOf, hf2, hn]; simp
  rw [hlog] at hF
  set tr := (q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest with htr
  set x := xOf π with hx
  -- the value refinement: the program read off the stream returns `true`
  have hpub := hpubeq hp (sig := traceBytesB tr) (seed_bytes π a₀ st₀ rest hHle)
  have hok0 : (runD (decideProg P20 (M3.real P20 tabs) vk c) (traceBytesB tr) RS.start).2.ok = true :=
    decideF_ok hF
  have hacc : AccOk P20 (M3.real P20 tabs) (pubX x)
      (runD (decideProg P20 (M3.real P20 tabs) vk c) (traceBytesB tr) RS.start).1 = true := by
    rw [← hpub]; exact decideF_acc hF
  obtain ⟨b, hb1, -, -, rfl⟩ :=
    href (traceBytesB tr) vk c x hpub RS.start hok0 hacc
  obtain ⟨⟨b0, rs'⟩, hivp⟩ : ∃ r, ivp capS occS shpS (Lvm.ASM.PSWith mid x) (traceBytesB tr) RS.start = r :=
    ⟨_, rfl⟩
  rw [hivp] at hb1
  simp only at hb1
  subst hb1
  obtain ⟨⟨o, rsW, nW⟩, hW⟩ : ∃ r, ivpW capS occS shpS (fun _ ↦ 24) (Lvm.ASM.PSWith mid x) (traceBytesB tr) RS.start 0 = r :=
    ⟨_, rfl⟩
  have hWI := ivpW_ivp (cap := capS) (occ := occS) (shp := shpS) (Lvm.ASM.PSWith mid x) (traceBytesB tr) RS.start 0
  rw [hW, hivp] at hWI
  simp only at hWI
  obtain ⟨rfl, rfl⟩ := hWI
  -- the simulation
  have hJ0 : J (Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)) π tr
      ⟨headerBytes, headerBytes, st₀, [(seedQuery π a₀, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((π.data.toList).drop headerBytes) RS.start 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_two π a₀ st₀ rest hHle).symm,
      by show 0 = headerBytes - headerBytes; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  obtain ⟨s', st', buf', caps', body', i', cr', hJ', hk', -, hrun⟩ :=
    simW (S := Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)) (π := π) (tr := tr) (p := P20)
      rfl rfl rfl capOfS_eq occOfS_eq (atomsOf P20 (schedule P20)) (Lvm.ASM.PSWith mid x) [] _ _ st₀ [] []
      _ RS.start 2 [] [] _ true _ 0 nW (hfol x) (by simpa using stA_P20) hJ0 rfl
      (fun _ h ↦ by simp at h)
      (fun s'' m hm ↦ by
        obtain ⟨-, hb⟩ := runSeq_ret_true hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        rw [hb.1])
      h2 (wAt_24 (mem_widthsA_atomsOf P20 _ noWB_P20) 0) hW
  obtain ⟨hnil', hb'⟩ := runSeq_ret_true hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hb'
  have hbody' : body' = [] := by
    rw [hJ'.body, hb'.1, List.drop_eq_nil_iff, length_blb]
  -- the compiled verifier
  have hx5976 : x.length = Lvm.ASM.hdrLen := by
    rw [hx, xOf, List.length_take, List.length_drop, length_blb]
    simp only [Lvm.ASM.hdrLen]; omega
  have hseed : toQ (a₀.toList ++ x) = seedQuery π a₀ := by
    apply toQ_eq
    rw [seedQuery, blb_append, blb_digestBytes, blb_extract, hx, xOf]
    rfl
  have hqc : 32 + x.length ≤ queryCap := by rw [hx5976]; decide
  set S := Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid) with hSdef
  have hS_hdr : S.hdr π = some (x, (π.data.toList).drop headerBytes) := hhdr hp
  have hS_pre : S.preOk c x = true := by
    show (Lvm.ASM.okS vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [hok hp]; simp [hqc]
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, htr, runSeq_query_eq,
    show S.seedQ a₀ x = seedQuery π a₀ from hseed, runSeq_query_eq,
    show S.P x = Lvm.ASM.PSWith mid x from rfl, runW_eq_runKW,
    show rest = tr.drop 2 from rfl, hrun, hnil', hbody']
  rfl

/-- **V_S ⇒ S.V on every log** (WP-14's `OpenS.refines` form), given the program's shape and the
parse facts. -/
theorem refines_logOf (href : RefD tabs mid)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith mid x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (hhdr : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.hdrS π = some (xOf π, (π.data.toList).drop headerBytes))
    (hok : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.okS vk c (xOf π) = true)
    (hpubeq : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true → ∀ {sig : ByteArray},
      (∀ t < headerBytes - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      pubOf vk c sig = pubX (xOf π)) :
    ∀ (vk : Digest) (L : Log) (c : Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VSL P20 tabs vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)).V c π).runLog L = some true :=
  fun vk L c π _ h ↦ runLog_of_seq
    (fun tr ht ↦ refines_seqOf tabs mid href hfol hhdr hok hpubeq vk c π tr ht) L h

/-- **V_S ⇒ S.V on every log** (O5b, WP-14's `OpenS.refines`), given the program's shape against
the schedule. -/
theorem refines_logF (href : RefD tabs mid)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith mid x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True) :
    ∀ (vk : Digest) (L : Log) (c : Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VSL P20 tabs vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)).V c π).runLog L = some true :=
  refines_logOf tabs mid href hfol (fun h ↦ hdrS_of_parseOk h) (fun h ↦ okS_of_parseOk h)
    (fun h _ hs ↦ pubOf_eq_pubX h hs)

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

/-- A bus result with no claim (the typed path has no bus; the mini-bus's claims are its table phase's). -/
def busNil : BusOut := ⟨true, [], [], []⟩

/-- **Phases 2–7 of the typed decision** (the typed phases, then roll 7's `dKg`), grouped as `midT₂`: the claims
and the folded accumulator. -/
def dMidT (p : Params) (N : TNat) (pub : Pub) : DM (List (Com × BlockClaim × FE) × Acc) :=
  dTypedT p N (N.m3 p) pub >>= fun t ↦ dKg p (N.m3 p) pub >>= fun kg ↦
    pure (t.2.1 ++ dClaimsT (N.m3 p) p pub busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2, t.1)

/-- **`decideProgT` grouped as `P_S`** (its value: the folded accumulator; M′ `S2GM`: one cap). -/
def dTopT (p : Params) (N : TNat) (vk c : Vector UInt8 32) : DM Acc :=
  MonadReader.read >>= fun sig ↦
    DM.skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap) >>= fun _ ↦
    dMidT p N (pubOf vk c sig) >>= fun r ↦ dOpenT p (smallT p (pubOf vk c sig)) r.1 >>= fun _ ↦ pure r.2

theorem decideProgT_dTopT (p : Params) (N : TNat) (vk c : Vector UInt8 32) :
    decideProgT p N vk c = dTopT p N vk c := by
  simp only [decideProgT, dTopT, dMidT, dKg, dKec, dKsLink, dClaimsT, busNil, bind_assoc, pure_bind]

theorem monoD_dMidT (p : Params) (N : TNat) (pub : Pub) : MonoD (dMidT p N pub) :=
  (monoD_dTypedT _ _ _ _).bind fun _ ↦ (monoD_dKg _ _ _).bind fun _ ↦ MonoD.pure _

theorem nuMain_P20 : P20.nuMain = 23 := by decide +kernel

theorem nuRec_P20 : P20.nuRec = 19 := by decide +kernel

/-- The typed shape bit is roll 7's (`nuT = CMain.nu20 = 23`, `2^18`). -/
theorem smallT_eq (p : Params) (pub : Pub) : smallT p pub = Shape.smallP p pub := rfl

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

theorem onStackZsF_append (s : Bool) (a b : List (BlockClaim × FE)) :
    Shape.onStackZsF s (a ++ b) = Shape.onStackZsF s a ++ Shape.onStackZsF s b := by
  unfold Shape.onStackZsF; split <;> simp

theorem onStackZs_append (x : List UInt8) (a b : List VStackClaim) :
    Shape.onStackZs x (a ++ b) = Shape.onStackZs x a ++ Shape.onStackZs x b := by
  unfold Shape.onStackZs; split <;> simp

theorem m3_eq (N : TNat) (p : Params) : N.m3 p = M3.real p fun _ ↦ N.mbT := rfl

/-! ## The opening -/

section Ref

variable {sig : ByteArray}

theorem commitRootUd_mainT : Verifier.commitRootUd cfgMain24G = VerifierProgram.readCommitment 19 64 := rfl

theorem monoD_dOpenT (p : Params) (s : Bool) (claims : List (Com × BlockClaim × FE)) : MonoD (dOpenT p s claims) :=
  (MonoD.require _).bind fun _ ↦ monoD_verifyStacked _ _ _ _ _ _

/-- **The M′ opening at `P20`** (`S2GM`: `C_main`'s claims only, on the statement's shape's stack): V_S's
`dOpenT` refines `verifyStackedJ (cfgMain23Jq 1)` on a list `SCRel`-related to `onStackZsF`'s, where its
`require` (every claim on `C_main`) held. -/
theorem ref_dOpenT (s : Bool) (claims : List (Com × BlockClaim × FE)) (cl : List VStackClaim)
    (h : claims.all (·.1 == .main) = true →
      List.Forall₂ SCRel (Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2))) cl) :
    RefAtP capS occS shpS sig (dOpenT P20 s claims) (Verifier.verifyStackedJ (cfgMain23Jq 1) cl)
      (fun _ _ ↦ True) (fun _ ↦ True) := by
  unfold dOpenT
  refine RefAtP.require_left (fun _ ↦ monoD_verifyStacked _ _ _ _ _ _) fun hall ↦ ?_
  have h' := h hall
  have e : (if s then ((claims.filter (·.1 == .main)).map (·.2)).map fun e ↦ onStackZBN P20.nuMain e.1 e.2
      else ((claims.filter (·.1 == .main)).map (·.2)).map (·.1.onStack)) =
      Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2)) := by
    unfold Shape.onStackZsF; rw [nuMain_P20]; rfl
  dsimp only
  rw [e, nuMain_P20]
  exact (ref_verifyStackedJ _ (cfgMain23Jq 1) _ _ _ _ _ h' mainOod_P20 rfl rfl rfl rfl rfl corrMain24).toP _

end Ref

/-! ## V_S ⇒ S.V -/

/-- `decideFT` holds: the run's checks held and its folded claim passes `Φ_Q`. -/
theorem decideFT_ok {p : Params} {N : TNat} {vk c : RecursionFast.Digest} {sig : ByteArray}
    (h : decideFT p N vk c sig = true) :
    (runD (decideProgT p N vk c) sig RS.start).2.ok = true ∧
      N.phi (runD (decideProgT p N vk c) sig RS.start).1.pt = (runD (decideProgT p N vk c) sig RS.start).1.y := by
  -- `decideFT`'s body by `delta` on the bare constant (GOLF-HAR's pattern): `unfold … at h` left a cast the kernel
  -- checked by reducing the run (GOLF-DEC3)
  have eF : @decideFT = @decideFT := rfl
  conv at eF => rhs; delta decideFT
  rw [eF] at h
  beta_reduce at h
  rw [decideProgTS_eq, DM.runOn.eq_1] at h
  -- `StateT.run`'s equation, not `rfl`: the kernel's lazy unfolding took `decideProgT` (the higher definition) first
  -- and reduced the program (GOLF-DEC2, 2 s)
  have e : (decideProgT p N vk c sig).run RS.start = runD (decideProgT p N vk c) sig RS.start :=
    StateT.run.eq_1 _ _
  rw [e] at h
  rcases hr : runD (decideProgT p N vk c) sig RS.start with ⟨a, s⟩
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, Lvm.M3.FE_eq_of_beq h.2⟩

section Main

variable (N : TNat) (PS : List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool)

/-- **V_S's typed decision refines the IOP verifier `PS`** on every stream whose header is the statement's (lvm2
roll 11: generic in `PS`; M′'s is `PSWithM`, B1's was `PSWith mid`). -/
def RefDT : Prop :=
  ∀ (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8), pubOf vk c sig = pubX x →
    RefAtP capS occS shpS sig (decideProgT P20 N vk c) (PS x)
      (fun _ b ↦ b = true) (fun a ↦ N.phi a.pt = a.y)

/-- **V_S ⇒ S.V on a trace, typed** (roll 7's `refines_seqOf` for `VST`/`decideFT`). -/
theorem refines_seqOfT (href : RefDT N PS)
    (hfol : ∀ x, Fol capS shpS idxS (PS x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (vk c : RecursionFast.Digest) (π : ByteArray) (tr : Trace)
    (h : (VST P20 N vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeS vk PS).V c π).runSeq tr = some true := by
  -- the header check
  unfold VST at h
  by_cases hp : parseOk P20 vk c π = true
  swap
  · rw [if_neg hp] at h; exact absurd (runSeq_ret_true h).2 (by simp)
  rw [if_pos hp] at h
  have hp' := hp
  simp only [parseOk, Bool.and_eq_true, beq_iff_eq] at hp'
  have hsize : π.size = piSize P20 := hp'.1.1.1
  have hHle : headerBytes ≤ π.size := by rw [hsize, sizes_P20.1]; decide
  -- the driver: q₀, the seed, the schedule
  rw [drive_of (p := P20) rfl (by decide)] at h
  obtain ⟨a₀, tr1, rfl, h1⟩ := runSeq_query_cons h
  obtain ⟨st₀, rest, rfl, h2⟩ := runSeq_query_cons h1
  rw [driveItems_eq] at h2
  obtain ⟨sf, n, hf1, hf2, -, -⟩ := drive_run P20 π _ _ _ rest h2
  obtain ⟨hnil, hb⟩ := runSeq_ret_true hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨-, hF⟩ := hb
  have hn : rest.take n = rest := List.take_of_length_le (List.drop_eq_nil_iff.mp hnil)
  have hlog : streamOf sf.log =
      traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) := by
    rw [streamOf, hf2, hn]; simp
  rw [hlog] at hF
  set tr := (q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest with htr
  set x := xOf π with hx
  -- the value refinement: the program read off the stream returns `true`
  have hpub := pubOf_eq_pubX hp (sig := traceBytesB tr) (seed_bytes π a₀ st₀ rest hHle)
  obtain ⟨hok0, hacc⟩ := decideFT_ok hF
  obtain ⟨b, hb1, -, -, rfl⟩ := href (traceBytesB tr) vk c x hpub RS.start hok0 hacc
  obtain ⟨⟨b0, rs'⟩, hivp⟩ : ∃ r, ivp capS occS shpS (PS x) (traceBytesB tr) RS.start = r :=
    ⟨_, rfl⟩
  rw [hivp] at hb1
  simp only at hb1
  subst hb1
  obtain ⟨⟨o, rsW, nW⟩, hW⟩ : ∃ r, ivpW capS occS shpS (fun _ ↦ 24) (PS x) (traceBytesB tr) RS.start 0 = r :=
    ⟨_, rfl⟩
  have hWI := ivpW_ivp (cap := capS) (occ := occS) (shp := shpS) (PS x) (traceBytesB tr) RS.start 0
  rw [hW, hivp] at hWI
  simp only at hWI
  obtain ⟨rfl, rfl⟩ := hWI
  -- the simulation
  have hJ0 : J (Lvm.ASM.schemeS vk PS) π tr
      ⟨headerBytes, headerBytes, st₀, [(seedQuery π a₀, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((π.data.toList).drop headerBytes) RS.start 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_two π a₀ st₀ rest hHle).symm,
      by show 0 = headerBytes - headerBytes; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  obtain ⟨s', st', buf', caps', body', i', cr', hJ', hk', -, hrun⟩ :=
    simW (S := Lvm.ASM.schemeS vk PS) (π := π) (tr := tr) (p := P20)
      rfl rfl rfl capOfS_eq occOfS_eq (atomsOf P20 (schedule P20)) (PS x) [] _ _ st₀ [] []
      _ RS.start 2 [] [] _ true _ 0 nW (hfol x) (by simpa using stA_P20) hJ0 rfl
      (fun _ h ↦ by simp at h)
      (fun s'' m hm ↦ by
        obtain ⟨-, hb⟩ := runSeq_ret_true hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        rw [hb.1])
      h2 (wAt_24 (mem_widthsA_atomsOf P20 _ noWB_P20) 0) hW
  obtain ⟨hnil', hb'⟩ := runSeq_ret_true hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hb'
  have hbody' : body' = [] := by
    rw [hJ'.body, hb'.1, List.drop_eq_nil_iff, length_blb]
  -- the compiled verifier
  have hx5976 : x.length = Lvm.ASM.hdrLen := by
    rw [hx, xOf, List.length_take, List.length_drop, length_blb]
    simp only [Lvm.ASM.hdrLen]; omega
  have hseed : toQ (a₀.toList ++ x) = seedQuery π a₀ := by
    apply toQ_eq
    rw [seedQuery, blb_append, blb_digestBytes, blb_extract, hx, xOf]
    rfl
  have hqc : 32 + x.length ≤ queryCap := by rw [hx5976]; decide
  set S := Lvm.ASM.schemeS vk PS with hSdef
  have hS_hdr : S.hdr π = some (x, (π.data.toList).drop headerBytes) := hdrS_of_parseOk hp
  have hS_pre : S.preOk c x = true := by
    show (Lvm.ASM.okS vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [okS_of_parseOk hp]; simp [hqc]
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, htr, runSeq_query_eq,
    show S.seedQ a₀ x = seedQuery π a₀ from hseed, runSeq_query_eq,
    show S.P x = PS x from rfl, runW_eq_runKW,
    show rest = tr.drop 2 from rfl, hrun, hnil', hbody']
  rfl

end Main

/-- **The typed middle phases follow the schedule** (`MidFollows`), the mini-bus's numbers from `TRefHyp`. -/
theorem midFollows_T (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) :
    Lvm.ASM.MidFollows (midT₂ (N.inst Q lay)) := by
  obtain ⟨hl, hr, he, -, -⟩ := H.fits
  exact midFollows_midT₂ (N.inst Q lay) hl busDepth_P20 hr he

/-! ## At `P20`: `LvmCertT20`'s stubs -/

open Lvm.CT Lvm.QTyped in
/-- **`TRefHyp` at `P20`** from the guard's facts and `THyp`: `PhiQC cacheT20` is `PhiQF` (`cacheT20_eq`, then
`PhiQC_eq`, rewriting only). -/
theorem trefHyp20 (S : SF20) (H : THyp Ti20) : TRefHyp NT20 QB20 layT20 where
  ok := S.regs
  hlay := S.hlayOk
  mini := S.mini
  sc := H.sc
  phi pt hpt := by
    have e : NT20.phi = PhiQC cacheT20 := rfl
    have hc : (cacheW QB20 layT20).okB QB20 layT20 = true := by rw [← cacheT20_eq]; exact S.cache
    rw [e, cacheT20_eq]
    exact PhiQC_eq QB20 layT20 S.hlay hc pt hpt

open Lvm.CT Lvm.QTyped Lvm.ASM in
/-- **`LvmCertT20.midFollowsT20`** (statement verbatim). -/
theorem midFollowsT20L (S : SF20) (H : THyp Ti20) : MidFollows (midT₂ Ti20) :=
  midFollows_T NT20 QB20 layT20 (trefHyp20 S H)

end Lvm.VEq
