-- New for lvm (WP-14a, H0): the IOP verifier `P_S` (LvmCertS `PSWith`) with the middle phases `midS`
-- follows the whole schedule at P20 (`Fol`, LvmVEqShape): the root, the middle phases (LvmVEqFolMid),
-- and the WHIR opening against `openMainI` (lvm2 JB-VQP J1: with OOD samples, `fol_verifyStackedJ`; lvm2 roll 11,
-- M′: `PSWithM`, one commitment).
import LvmVEqFolMid
import LvmShape
import LvmCertS
import LvmReplay
import LvmWhirParamsJp

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
  rw [schedule_eq, midItems_eq]
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
