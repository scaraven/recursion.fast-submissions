/- `LvmQAsmArith2WhirPOff` (GOLF2 off-path move, group 47 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmQAsmArith2WhirP,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmQAsmArith2WhirP

-- ===== from `LvmQAsmArith2WhirP` =====

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm

theorem phB20 : phByte P20 .openMain = 230888 := by
  rw [phByte, phaseFirst, phases_P20_lit]; decide +kernel
theorem phB8 : phByte P8 .openMain = 183800 := by decide +kernel

theorem lay20₀ : LayOk ⟨P20.mainLevels, P20.nuMain, 28873, fun _ => 0, fun i => pchOf (P20.mainLevels.getD i default).t,
      fun i => bitsDesc (P20.mainLevels.getD i default).kappa, P20.grind, P20.mainOod, fun _ => 0⟩ 75593 = true ∧
    8 * stackEndL P20.grind P20.mainOod P20.mainLevels (28873 + 15) = 604744 := by
  decide +kernel

theorem lay8₀ : LayOk ⟨P8.mainLevels, P8.nuMain, 22987, fun _ => 0, fun i => pchOf (P8.mainLevels.getD i default).t,
      fun i => bitsDesc (P8.mainLevels.getD i default).kappa, P8.grind, P8.mainOod, fun _ => 0⟩ 38437 = true ∧
    8 * stackEndL P8.grind P8.mainOod P8.mainLevels (22987 + 15) = 307496 := by
  decide +kernel

/-- **`P20`'s layout** (M′): `C_main`'s opening passes the static checks below the stream's lanes, starts after
phase 7's four pending scalars and ends at `hashedLen`. -/
theorem lay20 (pb pw : Nat → Nat) :
    LayOk (cfgMain P20 pb pw) (streamLanes P20) = true ∧
    8 * stackEndL P20.grind P20.mainOod P20.mainLevels (openU P20 + 15) = hashedLen P20 ∧
    8 * openU P20 = phByte P20 .openMain + 96 := by
  have hT : streamLanes P20 = 75593 := sizes_P20.2.2.2.2.2.2.1
  have hL : hashedLen P20 = 604744 := sizes_P20.2.2.2.2.2.1
  have hU : openU P20 = 28873 := by rw [openU, phB20]
  obtain ⟨l2, l4⟩ := lay20₀
  refine ⟨?_, ?_, ?_⟩
  · rw [hT, cfgMain, hU, layOk_pb _ _ _ pb (fun _ => 0) _ _ _ _ pw (fun _ => 0)]; exact l2
  · rw [hU, l4, hL]
  · rw [hU, phB20]

/-- **`P8`'s layout.** -/
theorem lay8 (pb pw : Nat → Nat) :
    LayOk (cfgMain P8 pb pw) (streamLanes P8) = true ∧
    8 * stackEndL P8.grind P8.mainOod P8.mainLevels (openU P8 + 15) = hashedLen P8 ∧
    8 * openU P8 = phByte P8 .openMain + 96 := by
  have hT : streamLanes P8 = 38437 := sizes_P8.2.2.2.2.2.2.2.2.1
  have hL : hashedLen P8 = 307496 := sizes_P8.2.2.2.2.2.2.2.1
  have hU : openU P8 = 22987 := by rw [openU, phB8]
  obtain ⟨l2, l4⟩ := lay8₀
  refine ⟨?_, ?_, ?_⟩
  · rw [hT, cfgMain, hU, layOk_pb _ _ _ pb (fun _ => 0) _ _ _ _ pw (fun _ => 0)]; exact l2
  · rw [hU, l4, hL]
  · rw [hU, phB8]

end Lvm.Har
end
