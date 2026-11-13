-- New for lvm2 (roll 8 = B1, wave L, L-C): the typed backend's `P_S` (`PSWith (midT₂ Ti)`) follows the typed
-- schedule (`LvmSchedule.phases` at the refreeze `S2GB1`: `phasesT`'s items under the old phase names).
import LvmVEqFolPS
import LvmTypedSpec
import LvmTypedVSched

/-!
# The typed `P_S` follows the schedule

* The typed items (`zeroI` … `miniTabI`, `typedI`) and the schedule by phase (`phases_eq`, `schedule_eq`,
  `midItems_eq`) are `LvmVEqFolMid`'s; `atomsOf_schedule` is `LvmVEqFolPS`'s.
* **`folP_typedProg`**: `typedProg Ti pub` against `typedI p` (the record's mini-bus numbers are `Ti.mbT`'s);
  **`folP_midT₂`**: `midT₂ Ti x` against `midItems`; **`fol_PST`**: `PSWith (midT₂ Ti) x` against the whole
  schedule; **`midFollows_midT₂`**: WP-14d's `MidFollows (midT₂ Ti)`.

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

/-- **The typed `P_S` follows the schedule** at P20. -/
theorem fol_PST (Ti : Typed.TInst) (hl : P20.leafdecReads = 1) (hd : P20.busDepth = Typed.miniDepth)
    (hr : P20.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWith (Typed.midT₂ Ti) x) (atomsOf P20 (schedule P20)) [] fun _ _ ↦ True := by
  rw [atomsOf_schedule]
  unfold Lvm.ASM.PSWith
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine Fol.bindP (folP_commitRootUd cfgRec20G rfl cap_rec0 rfl) fun _ _ ↦ ?_
  refine Fol.bindP (folP_midT₂ Ti hl hd hr he x) fun cl _ ↦ ?_
  refine @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openRecI P20)) _ [] _ _ (@fol_openRec cl.1 [])
    fun _ pp' _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] pp' _ _ (@fol_openMain cl.2 pp')
    fun _ _ _ ↦ trivial

/-- **WP-14d's shape obligation, typed**: every accepted run of `midT₂ Ti x` has the kinds of `midItems`. -/
theorem midFollows_midT₂ (Ti : Typed.TInst) (hl : P20.leafdecReads = 1) (hd : P20.busDepth = Typed.miniDepth)
    (hr : P20.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20.tableEvals = (Ti.mbT.map (·.w)).sum) :
    Lvm.ASM.MidFollows (Typed.midT₂ Ti) := by
  intro x l a hl'
  rw [(@fol_after capS shpS idxS _ (atomsOf P20 Lvm.ASM.midItems) (Typed.midT₂ Ti x) []
    (fun _ pp' ↦ pp' = []) (@FolP.fol capS shpS idxS _ (Typed.midT₂ Ti x) (atomsOf P20 Lvm.ASM.midItems)
      (fun _ ↦ True) (folP_midT₂ Ti hl hd hr he x) []) l a hl').1, atomKinds_atomsOf P20 _ midItems_noPos]

end Lvm.VEq
