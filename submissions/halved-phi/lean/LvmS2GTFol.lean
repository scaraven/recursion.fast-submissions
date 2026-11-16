-- New for lvm2 S2GT (GT-L2, 2026-11-15): S2GT's pinned middle phases (`midP (midM reloc (midGT Ti))`) follow the S2GT
-- schedule's middle items (`FolP`): the typed phases at `E2` (`typedProgT`, E2F-T) against the phase `bus` of
-- `phasesS2GT` (`busT`) and the tables, the `E2` front against S2GF's front items (S2GT-STMT 17's core).
import LvmE2VFol
import LvmE2VWidthsF
import LvmE2TVEq
import LvmE2TSpec
import LvmS2GTSched

/-!
# S2GT's middle phases follow the schedule

* The items: `zeroIT`, `wiringIT`, `relayIT`, `accIT` (`busT p` is `zeroIT ++ wiringIT ++ relayIT ++ accIT p ++
  miniBusI p`), `typedIT`, `midItemsT`; **`phasesT_eq`**, **`scheduleT_eq`** at a stage-2 record.
* `folP_zeroProgT`, `folP_wireProgT`, `folP_relayProgT`, `folP_accProgT`, **`folP_typedProgT`** (E2F-T's typed
  phases at `E2`, the mini-bus as roll 11's), `folP_midGT`, **`folP_midPT`**.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.E2V
open LeanVM.Protocol.Whir.Sound (cfgMain24G)

/-! ## The S2GT items -/

section Items

variable (p : Params)

/-- The zerocheck at `E2`: the separator, `τ` (20 ground challenges), `ω`, 20 rounds of 2, the nine values. -/
def zeroIT : List Item := List.flatten [sepI, gsmpN 20, gsmp, sumcheckE2I 20 2, rdE2 9]

/-- The wiring at `E2`: `γ`, 21 rounds of 2, the twelve matrix and four region values. -/
def wiringIT : List Item := List.flatten [gsmp, sumcheckE2I 21 2, rdE2 12, rdE2 4]

/-- The relayout at `E2`: 19 rounds of 2, `v_R`. -/
def relayIT : List Item := List.flatten [sumcheckE2I 19 2, rdE2 1]

/-- A23 at `E2`: `κ` (4), `h` (`accV + 1`), `t`, the zero scalar. -/
def accIT : List Item := List.flatten [gsmpN 4, rdE2 (p.accV + 1), gsmp, rdE2 1]

/-- **The typed phases' items at S2GT** (the phase `bus` of `phasesS2GT` and the tables). -/
def typedIT : List Item := zeroIT ++ (wiringIT ++ (relayIT ++ (accIT p ++ (miniBusI p ++ miniTabI p))))

/-- **S2GT's pinned middle phases' items**: the pin, the typed phases, the tape, the wire, `KS`, the `KS` link. -/
def midItemsT : List Item := pinI p ++ (typedIT p ++ (tapeIF p ++ (wireIF p ++ (ksIF p ++ ksLinkIF p))))

/-- The phase `bus` at S2GT by its parts. -/
theorem busT_eq : busT p = zeroIT ++ (wiringIT ++ (relayIT ++ (accIT p ++ miniBusI p))) := by
  simp only [busT, zeroIT, wiringIT, relayIT, accIT, miniBusI, List.flatten_cons, List.flatten_nil,
    List.append_assoc, List.append_nil]

set_option maxRecDepth 10000 in
/-- **S2GT's schedule by phase.** -/
theorem phasesT_eq (h : p.stage = 2) : phases p = [(.commit, commitI p ++ pinI p),
    (.bus, zeroIT ++ (wiringIT ++ (relayIT ++ (accIT p ++ miniBusI p)))), (.tables, miniTabI p), (.tape, tapeIF p),
    (.wire, wireIF p), (.ks, ksIF p), (.ksLink, ksLinkIF p), (.openMain, openMainI p)] := by
  rw [phases, if_neg (by omega), if_pos h, phasesS2GT, ← busT_eq]
  rfl

/-- S2GT's schedule: the root, the pinned middle phases, `C_main`'s opening. -/
theorem scheduleT_eq (h : p.stage = 2) : schedule p = commitI p ++ (midItemsT p ++ (openMainI p ++ [])) := by
  rw [schedule, phasesT_eq p h]
  simp only [midItemsT, typedIT, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil]

end Items

/-! ## The typed phases at `E2` -/

section Typed

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- The zerocheck at `E2` against `zeroIT`. -/
theorem folP_zeroProgT : FolP cap shp idx Lvm.E2T.zeroProgT (atomsOf p zeroIT) fun _ ↦ True := by
  simp only [zeroIT, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_sepI,
    atomsOf_gsmpN, atomsOf_gsmp, atomsOf_rdE2]
  unfold Lvm.E2T.zeroProgT
  exact folP_e2Sep.bind fun _ _ ↦ (folP_e2Samples _ 20).bind fun τ hτ ↦ (folP_e2Sample _).bind fun _ _ ↦
    (folP_sumcheckE2 p _ rfl (by norm_num) (τ.map some) 20 0 (by rw [List.length_map, hτ])).bind fun _ _ ↦
    (folP_e2Reads 9).bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

/-- The wiring at `E2` against `wiringIT`. -/
theorem folP_wireProgT (Ti : Typed.TInst) (pub : Pub) (v : List E2) :
    FolP cap shp idx (Lvm.E2T.wireProgT Ti pub v) (atomsOf p wiringIT) fun _ ↦ True := by
  simp only [wiringIT, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_gsmp,
    atomsOf_rdE2]
  unfold Lvm.E2T.wireProgT
  exact (folP_e2Sample _).bind fun _ _ ↦
    (folP_sumcheckE2 p _ rfl (by norm_num) _ 21 _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_e2Reads 12).bind fun _ _ ↦ (folP_e2Reads 4).bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

/-- The relayout at `E2` against `relayIT`. -/
theorem folP_relayProgT (Ti : Typed.TInst) (ry : List E2) (vS : E2) :
    FolP cap shp idx (Lvm.E2T.relayProgT Ti ry vS) (atomsOf p relayIT) fun _ ↦ True := by
  simp only [relayIT, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2]
  unfold Lvm.E2T.relayProgT
  exact (folP_sumcheckE2 p _ rfl (by norm_num) _ 19 _ (List.length_replicate ..)).bind fun _ _ ↦
    folP_e2Read.bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

/-- A23 at `E2` against `accIT` (`accV = 45`). -/
theorem folP_accProgT (hacc : p.accV = Typed.phiVarsT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (ok : Bool)
    (yIn : E2) (a rxy vs : List E2) :
    FolP cap shp idx (Lvm.E2T.accProgT Q lay ok yIn a rxy vs) (atomsOf p (accIT p)) fun _ ↦ True := by
  simp only [accIT, hacc, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_gsmpN,
    atomsOf_gsmp, atomsOf_rdE2]
  unfold Lvm.E2T.accProgT
  exact (folP_e2Samples _ 4).bind fun _ _ ↦ (folP_e2Reads _).bind fun _ _ ↦ (folP_e2Sample _).bind fun _ _ ↦
    folP_e2Read.bind_nil fun _ _ ↦ (folP_require _).mono fun _ _ ↦ trivial

/-- **The typed phases at `E2`** against `typedIT p` (`accV = 45`; the record's mini-bus numbers those of
`Ti.mbT`). -/
theorem folP_typedProgT (Ti : Typed.TInst) (pub : Pub) (hacc : p.accV = Typed.phiVarsT)
    (hl : p.leafdecReads = 1) (hd : p.busDepth = Typed.miniDepth)
    (hr : p.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : p.tableEvals = (Ti.mbT.map (·.w)).sum) :
    FolP cap shp idx (Lvm.E2T.typedProgT Ti pub) (atomsOf p (typedIT p)) fun _ ↦ True := by
  simp only [typedIT, atomsOf_append]
  rw [← atomsOf_append p (miniBusI p)]
  unfold Lvm.E2T.typedProgT
  exact (folP_zeroProgT p).bind fun _ _ ↦ (folP_wireProgT p Ti pub _).bind fun _ _ ↦
    (folP_relayProgT p Ti _ _).bind fun _ _ ↦ (folP_accProgT p hacc _ _ _ _ _ _ _).bind fun _ _ ↦
    (folP_miniBusProg p Ti hl hd hr he).bind_ret fun _ _ ↦ trivial

end Typed

/-! ## The pinned middle phases -/

section Mid

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **S2GT's middle phases** (`midGT Ti`) against the typed and the front items at `P20T`. -/
theorem folP_midGT (Ti : Typed.TInst) (hl : P20T.leafdecReads = 1) (hd : P20T.busDepth = Typed.miniDepth)
    (hr : P20T.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20T.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    FolP cap shp idx (Lvm.E2T.midGT Ti x) (atomsOf P20T (typedIT P20T ++
      (tapeIF P20T ++ (wireIF P20T ++ (ksIF P20T ++ ksLinkIF P20T))))) fun _ ↦ True := by
  rw [atomsOf_append]
  unfold Lvm.E2T.midGT midFWithR
  exact (folP_typedProgT _ Ti _ rfl hl hd hr he).bind fun _ _ ↦
    (folP_kgProgFR _ rfl rfl _ _ _).bind_ret fun _ _ ↦ trivial

theorem atomsOf_pinIT : atomsOf P20T (pinI P20T) = List.replicate CMain.nu20 .sm ++ [.rd] := by
  rw [pinI, atomsOf_append, atomsOf_smp, atomsOf_rd]
  rfl

/-- **S2GT's pinned middle phases follow `midItemsT`** at `P20T`, for every relocation. -/
theorem folP_midPT (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : P20T.leafdecReads = 1) (hd : P20T.busDepth = Typed.miniDepth)
    (hr : P20T.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20T.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    FolP cap shp idx (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2T.midGT Ti)) x) (atomsOf P20T (midItemsT P20T))
      fun _ ↦ True := by
  rw [midItemsT, atomsOf_append, atomsOf_pinIT]
  exact folP_midP _ x _ (folP_midMk 4 reloc _ x _ (folP_midGT Ti hl hd hr he x))

end Mid

/-! ## The whole `P_S` at S2GT -/

theorem level_T : P20T.level = P20.level := rfl

theorem atomsOf_T (its : List Item) : atomsOf P20T its = atomsOf P20 its := by
  unfold atomsOf
  congr 1

theorem openMainI_T : openMainI P20T = openMainI P20 := rfl

theorem commitI_T : commitI P20T = commitI P20 := by
  unfold commitI
  rw [level_T]

theorem atomsOf_scheduleT : atomsOf P20T (schedule P20T) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf P20T (midItemsT P20T) ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [scheduleT_eq _ rfl, atomsOf_append, atomsOf_append, atomsOf_append, openMainI_T, atomsOf_T (openMainI P20),
    commitI_T, atomsOf_T (commitI P20), atomsOf_commitI, atomsOf_nil]

/-- **S2GT's `P_S` follows the schedule** at `P20T`: the root, the pin, the typed phases at `E2`, the `E2` front,
`C_main`'s opening (`P20`'s levels), from no pending positions (`fol_PSOfF`'s proof). -/
theorem fol_PSOfT (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : P20T.leafdecReads = 1) (hd : P20T.busDepth = Typed.miniDepth)
    (hr : P20T.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20T.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2T.midGT Ti))) x)
      (atomsOf P20T (schedule P20T)) [] fun _ _ ↦ True := by
  rw [atomsOf_scheduleT]
  unfold Lvm.ASM.PSWithM
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine @Fol.bindP capS shpS idxS _ _ (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2T.midGT Ti)) x) _
    (atomsOf P20T (midItemsT P20T)) (atomsOf P20 (openMainI P20) ++ []) _ [] _
    (folP_midPT reloc Ti hl hd hr he x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

/-! ## The static check and the read widths at S2GT -/

/-- S2GT's record with `P20`'s levels as literals (`LvmReplay.P20_eq`). -/
theorem PT_eq : P20T = { Lvm.Replay.P20L with name := "P20T", stage := 2, accV := accVT } := by
  unfold P20T
  rw [Lvm.Replay.P20_eq]

set_option maxRecDepth 200000 in
/-- **The static check at S2GT** (one kernel evaluation over the items, `stA_atomsOf`). -/
theorem stA_P20T : stA P20T (atomsOf P20T (schedule P20T)) 0 [] [] = true := by
  rw [stA_atomsOf, PT_eq]
  decide +kernel

theorem readWidthsP_eqA : readWidthsP P20T = widthsA (atomsOf P20T (schedule P20T)) := by
  rw [widthsA_atomsOf]
  unfold readWidthsP
  exact List.flatMap_congr fun it _ => by cases it <;> rfl

/-- **`rwG20` is the S2GT schedule's read widths** from read `0`. -/
theorem wAt_rwG20 : WAt rwG20 0 (widthsA (atomsOf P20T (schedule P20T))) := by
  rw [← readWidthsP_eqA]
  exact wAt_getD _ _

/-! ## The read widths at S2GT, phase by phase -/

/-- A list of atoms reading 24-byte scalars only reads `atomReads` of them. -/
theorem widthsA_eq_replicate : ∀ as : List Atom, (∀ w ∈ widthsA as, w = 24) →
    widthsA as = List.replicate (Lvm.E2T.atomReads as) 24
  | [], _ => rfl
  | .rd :: as, h => by
    rw [show widthsA (.rd :: as) = 24 :: widthsA as from rfl,
      widthsA_eq_replicate as fun w hw ↦ h w (List.mem_cons_of_mem _ hw)]
    simp [Lvm.E2T.atomReads, List.countP_cons, List.replicate_succ]
  | .rdw w :: as, h => by
    have hw : w = 24 := h w List.mem_cons_self
    subst hw
    rw [show widthsA (.rdw 24 :: as) = 24 :: widthsA as from rfl,
      widthsA_eq_replicate as fun w hw ↦ h w (List.mem_cons_of_mem _ hw)]
    simp [Lvm.E2T.atomReads, List.countP_cons, List.replicate_succ]
  | .sm :: as, h => by
    rw [show widthsA (.sm :: as) = widthsA as from rfl, widthsA_eq_replicate as h]
    simp [Lvm.E2T.atomReads, List.countP_cons]
  | .cap _ _ :: as, h => by
    rw [show widthsA (.cap _ _ :: as) = widthsA as from rfl, widthsA_eq_replicate as h]
    simp [Lvm.E2T.atomReads, List.countP_cons]
  | .pclr :: as, h => by
    rw [show widthsA (.pclr :: as) = widthsA as from rfl, widthsA_eq_replicate as h]
    simp [Lvm.E2T.atomReads, List.countP_cons]
  | .ps _ _ :: as, h => by
    rw [show widthsA (.ps _ _ :: as) = widthsA as from rfl, widthsA_eq_replicate as h]
    simp [Lvm.E2T.atomReads, List.countP_cons]
  | .op _ :: as, h => by
    rw [show widthsA (.op _ :: as) = widthsA as from rfl, widthsA_eq_replicate as h]
    simp [Lvm.E2T.atomReads, List.countP_cons]

/-- **The typed phases' read widths at S2GT are E2F-T's `wTypedT`.** -/
theorem widthsA_typedIT : widthsA (atomsOf P20T (typedIT P20T)) = Lvm.E2T.wTypedT := by
  have e : typedIT P20T = (zeroIT ++ (wiringIT ++ (relayIT ++ accIT P20T))) ++
      (miniBusI P20T ++ miniTabI P20T) := by
    simp only [typedIT, List.append_assoc]
  have hm : widthsA (atomsOf P20T (miniBusI P20T ++ miniTabI P20T)) = List.replicate Lvm.E2T.nMiniRd 24 := by
    rw [widthsA_eq_replicate _ (mem_widthsA_atomsOf _ _ (by
      rw [noWB_append]; simp only [miniBusI, miniTabI, gpI, List.flatten_cons, List.flatten_nil, List.append_nil,
        noWB_append, noWB_smp, noWB_rd, noWB_sumcheckI, noWB_gpLayersI, Bool.and_self]))]
    rw [atomsOf_T]
    rfl
  rw [e, atomsOf_append, widthsA_append, hm, widthsA_atomsOf]
  simp only [zeroIT, wiringIT, relayIT, accIT, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.flatMap_append, wI_rdE2, wI_gsmpN, wI_gsmp, wI_sumcheckE2I, show sepI.flatMap itemW = [] from rfl,
    Lvm.E2T.wTypedT, Lvm.E2T.wZeroT, Lvm.E2T.wWireT, Lvm.E2T.wRelayT, Lvm.E2T.wAccT, List.append_assoc,
    List.nil_append]
  rfl

/-- **The S2GT schedule's read widths** in V_S's decision order: the pin's read, the typed phases', the front's,
the opening's. -/
theorem widthsA_scheduleT :
    widthsA (atomsOf P20T (schedule P20T)) =
      [24] ++ widthsA (atomsOf P20T (typedIT P20T)) ++ (wTape 20 ++ wCaller 13 ++ wKsLink 13) ++
        widthsA (atomsOf P20 (openMainI P20)) := by
  have hp : widthsA (List.replicate CMain.nu20 Atom.sm) = [] := by
    generalize CMain.nu20 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ]; exact ih
  rw [atomsOf_scheduleT, midItemsT, atomsOf_append P20T (pinI _), atomsOf_append P20T (typedIT _), atomsOf_pinIT]
  simp only [widthsA_append, widthsA_frontG P20T rfl rfl, hp, List.append_nil, List.nil_append, List.append_assoc]
  rfl

end Lvm.VEq
