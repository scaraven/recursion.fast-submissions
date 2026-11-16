-- New for lvm2 U-TAPE (UT-L, 2026-11-16): S2GU's pinned middle phases (`midP (midMk 4 reloc (midGU Ti))`) follow the
-- S2GU schedule's middle items (`FolP`): S2GT's typed phases (`LvmS2GTFol`), the merged tape (`tapeProgU`) against
-- `tapeU`, the wire (`wireProgU`) against `wireU` (UTAPE-STMT 31's core).
import LvmS2GTFol
import LvmS2GUMid

/-!
# S2GU's middle phases follow the schedule

* `midItemsU p` (the pin, S2GT's typed items, `tapeU p`, `wireU p`); **`phasesU_eq`**, **`scheduleU_eq`** at a
  stage-3 record.
* `folP_slotRedU` (a slot reduction of any `b` rounds), `folP_wireProgU`, `folP_tapeProgU`, `folP_midGU`,
  **`folP_midPU`**.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.E2V

section Items

variable (p : Params)

/-- **The pinned middle phases' items at S2GU**: the pin, S2GT's typed phases, the merged tape, the wire. -/
def midItemsU : List Item := pinI p ++ (typedIT p ++ (tapeU p ++ wireU p))

set_option maxRecDepth 10000 in
/-- **S2GU's schedule by phase.** -/
theorem phasesU_eq (h : p.stage = 3) : phases p = [(.commit, commitI p ++ pinI p),
    (.bus, zeroIT ++ (wiringIT ++ (relayIT ++ (accIT p ++ miniBusI p)))), (.tables, miniTabI p), (.tape, tapeU p),
    (.wire, wireU p), (.openMain, openMainI p)] := by
  rw [phases, if_neg (by omega), if_neg (by omega), if_pos h, phasesS2GU, phasesS2GT, ← busT_eq]
  rfl

/-- S2GU's schedule: the root, the pinned middle phases, `C_main`'s opening. -/
theorem scheduleU_eq (h : p.stage = 3) : schedule p = commitI p ++ (midItemsU p ++ (openMainI p ++ [])) := by
  rw [schedule, phasesU_eq p h]
  simp only [midItemsU, typedIT, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil]

end Items

section Front

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- **A slot reduction at `E2`** (`b` slot rounds) against `slotRedI b`. -/
theorem folP_slotRedU (b sb blk : ℕ) (W : ℕ → ℕ → E2) (pt : List E2) (v : E2) :
    FolP cap shp idx (slotProgE2 b sb blk W pt v) (atomsOf p (slotRedI b)) fun _ ↦ True := by
  simp only [slotRedI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rdE2]
  unfold slotProgE2
  exact (folP_sumcheckE2 p _ rfl (by norm_num) _ b _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_e2Reads 64).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_rowSwitch _ _).bind_ret fun _ _ ↦ trivial

/-- **The S2GU wire** against `wireU` at a record with `logN = 20`. -/
theorem folP_wireProgU (hN : p.logN = 20) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) :
    FolP cap shp idx (Lvm.E2U.wireProgU s n claim) (atomsOf p (wireU p)) fun _ ↦ True := by
  have e : atomsOf p (wireU p) = atomsOf p (sumcheckE2I 20 2) ++ (List.replicate 3 (.rdw e2Bytes) ++
      (atomsOf p (slotRedI 2) ++ (atomsOf p (slotRedI laneBits) ++ atomsOf p (slotRedI laneBits)))) := by
    simp only [wireU, hN, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2]
  rw [e]
  unfold Lvm.E2U.wireProgU
  exact (folP_sumcheckE2 p _ rfl (by norm_num) _ 20 _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_e2Reads 3).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_slotRedU p 2 _ _ _ _ _).bind fun _ _ ↦ (folP_slotRedU p 5 _ _ _ _ _).bind fun _ _ ↦
    (folP_slotRedU p 5 _ _ _ _ _).bind_ret fun _ _ ↦ trivial

/-- **The S2GU tape** (`CHtape`, `CHwire`) against `tapeU ++ wireU` at a record with `logN = 20`. -/
theorem folP_tapeProgU (hN : p.logN = 20) (s : RecursionFast.Digest) (n : ℕ) :
    FolP cap shp idx (Lvm.E2U.tapeProgU s n) (atomsOf p (tapeU p) ++ atomsOf p (wireU p)) fun _ ↦ True := by
  have e : atomsOf p (tapeU p) ++ atomsOf p (wireU p) =
      [.sm] ++ ((List.replicate 20 [Atom.rdw nonceBytes, .sm]).flatten ++ (List.replicate 50 (.rdw e2Bytes) ++
        ((List.replicate 1 [Atom.rdw nonceBytes, .sm]).flatten ++
          (atomsOf p (tapeLayersE2I 21) ++ atomsOf p (wireU p))))) := by
    simp only [tapeU, hN, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rdE2,
      atomsOf_sepI, atomsOf_gsmpN, atomsOf_gsmp, List.append_assoc]
    rfl
  rw [e]
  unfold Lvm.E2U.tapeProgU
  exact folP_e2Sep.bind fun _ _ ↦ (folP_e2Samples _ 20).bind fun r hr ↦ (folP_e2Reads 50).bind fun _ _ ↦
    (folP_e2Samples _ 1).bind fun r1 hr1 ↦
    (folP_tapeGkrE2 p 21 (r ++ r1) _ (by rw [List.length_append, hr, hr1])).bind fun _ _ ↦
    (folP_require _).bind fun _ _ ↦ (folP_wireProgU p hN _ _ _).bind_ret fun _ _ ↦ trivial

end Front

section Mid

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **S2GU's middle phases** (`midGU Ti`) against the typed and the front items at `P20U`. -/
theorem folP_midGU (Ti : Typed.TInst) (hl : P20U.leafdecReads = 1) (hd : P20U.busDepth = Typed.miniDepth)
    (hr : P20U.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20U.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    FolP cap shp idx (Lvm.E2U.midGU Ti x) (atomsOf P20U (typedIT P20U ++ (tapeU P20U ++ wireU P20U)))
      fun _ ↦ True := by
  rw [atomsOf_append, atomsOf_append]
  unfold Lvm.E2U.midGU
  exact (folP_typedProgT _ Ti _ rfl hl hd hr he).bind fun _ _ ↦
    (folP_tapeProgU _ rfl _ _).bind_ret fun _ _ ↦ trivial

theorem atomsOf_pinIU : atomsOf P20U (pinI P20U) = List.replicate CMain.nu20 .sm ++ [.rd] := by
  rw [pinI, atomsOf_append, atomsOf_smp, atomsOf_rd]
  rfl

/-- **S2GU's pinned middle phases follow `midItemsU`** at `P20U`, for every relocation. -/
theorem folP_midPU (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : P20U.leafdecReads = 1) (hd : P20U.busDepth = Typed.miniDepth)
    (hr : P20U.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20U.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    FolP cap shp idx (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2U.midGU Ti)) x) (atomsOf P20U (midItemsU P20U))
      fun _ ↦ True := by
  rw [midItemsU, atomsOf_append, atomsOf_pinIU]
  exact folP_midP _ x _ (folP_midMk 4 reloc _ x _ (folP_midGU Ti hl hd hr he x))

end Mid

end Lvm.VEq
