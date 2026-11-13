-- New for lvm (HAR-WH): the configurations of phases 8–9 at P20 and P8 (start lane, position
-- chunks, coordinate chunks) and their static checks.
import LvmQAsmArith2WhirPD
import LvmQAsmArith2Whir

/-!
# Phases 8–9 at `P20` and `P8`

`cfgRec p pb`, `cfgMain p pb`: `C_rec`'s opening starts at position `8 · openU p` (the `openRec`
phase's first entry plus phase 7's four pending scalars), `C_main`'s where `C_rec`'s ends. Opening
`k`'s positions are the `K` cells `pb k + j` (`k = 0`: `C_rec`; `k = 1 + i`: `C_main`'s level `i`;
Q_link's `pt.k + posIdx p k j`). Position chunks: `2^⌊log t⌋` then the rest rounded up
(`311 = 256 + 64`, `191 = 128 + 64`, `156 = 128 + 32`, `142 = 128 + 16`); coordinate chunks: the
binary digits of `κ`. `lay20`, `lay8`: the layout checks against the stream's lanes, and the ends
(`C_rec` at the `openMain` entry, `C_main` at `hashedLen`, `msg = 0`: `decideF`'s `ent = |Σ|`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm

theorem lvOk_congr {C C' : SCfg} (h1 : C.nu = C'.nu) (h2 : C.pch = C'.pch) (h3 : C.cch = C'.cch)
    (h4 : C.g = C'.g) (h5 : C.ood = C'.ood)
    (T : Nat) : ∀ (Ls : List Level) (i f V : Nat), lvOk C T Ls i f V = lvOk C' T Ls i f V
  | [], _, _, _ => rfl
  | [L], i, f, V => by rw [lvOk, lvOk, h1, h2, h3, h4, h5]
  | L :: N :: rest, i, f, V => by rw [lvOk, lvOk, h1, h2, h3, h4, h5, lvOk_congr h1 h2 h3 h4 h5 T (N :: rest)]

/-- The layout checks do not read the position or PoW cells. -/
theorem layOk_pb (lv : List Level) (nu U : Nat) (pb pb' : Nat → Nat) (pch cch : Nat → List Nat) (g : Nat)
    (ood : Bool) (pw pw' : Nat → Nat) (T : Nat) :
    LayOk ⟨lv, nu, U, pb, pch, cch, g, ood, pw⟩ T = LayOk ⟨lv, nu, U, pb', pch, cch, g, ood, pw'⟩ T := by
  unfold LayOk
  rw [lvOk_congr (C := ⟨lv, nu, U, pb, pch, cch, g, ood, pw⟩) (C' := ⟨lv, nu, U, pb', pch, cch, g, ood, pw'⟩)
    rfl rfl rfl rfl rfl]
  rfl

theorem phB20 : phByte P20 .openRec = 243552 ∧ phByte P20 .openMain = 470936 := by decide +kernel
theorem phB8 : phByte P8 .openRec = 190192 ∧ phByte P8 .openMain = 246088 := by decide +kernel

theorem lay20₀ : LayOk ⟨P20.recLevels, P20.nuRec, 30456, fun _ => 0, fun i => pchOf (P20.recLevels.getD i default).t,
      fun i => bitsDesc (P20.recLevels.getD i default).kappa, P20.grind, P20.recOod, fun _ => 0⟩ 105472 = true ∧
    LayOk ⟨P20.mainLevels, P20.nuMain, 58867, fun _ => 0, fun i => pchOf (P20.mainLevels.getD i default).t,
      fun i => bitsDesc (P20.mainLevels.getD i default).kappa, P20.grind, P20.mainOod, fun _ => 0⟩ 105472 = true ∧
    stackEndL P20.grind P20.recOod P20.recLevels (30456 + 15) = 58867 ∧
    8 * stackEndL P20.grind P20.mainOod P20.mainLevels (58867 + 15) = 843776 := by
  decide +kernel

theorem lay8₀ : LayOk ⟨P8.recLevels, P8.nuRec, 23786, fun _ => 0, fun i => pchOf (P8.recLevels.getD i default).t,
      fun i => bitsDesc (P8.recLevels.getD i default).kappa, P8.grind, P8.recOod, fun _ => 0⟩ 46178 = true ∧
    LayOk ⟨P8.mainLevels, P8.nuMain, 30761, fun _ => 0, fun i => pchOf (P8.mainLevels.getD i default).t,
      fun i => bitsDesc (P8.mainLevels.getD i default).kappa, P8.grind, P8.mainOod, fun _ => 0⟩ 46178 = true ∧
    stackEndL P8.grind P8.recOod P8.recLevels (23786 + 15) = 30761 ∧
    8 * stackEndL P8.grind P8.mainOod P8.mainLevels (30761 + 15) = 369424 := by
  decide +kernel

/-- **`P20`'s layout**: both openings pass the static checks below the stream's lanes; `C_rec` ends
at the `openMain` entry, `C_main` at `hashedLen`. -/
theorem lay20 (pb pw : Nat → Nat) :
    LayOk (cfgRec P20 pb pw) (streamLanes P20) = true ∧ LayOk (cfgMain P20 pb pw) (streamLanes P20) = true ∧
    8 * stackEndL P20.grind P20.recOod P20.recLevels (openU P20 + 15) = phByte P20 .openMain ∧
    8 * stackEndL P20.grind P20.mainOod P20.mainLevels (stackEndL P20.grind P20.recOod P20.recLevels (openU P20 + 15) + 15) =
      hashedLen P20 ∧
    8 * openU P20 = phByte P20 .openRec + 96 := by
  have hT : streamLanes P20 = 105472 := sizes_P20.2.2.2.2.2.2.1
  have hL : hashedLen P20 = 843776 := sizes_P20.2.2.2.2.2.1
  have hU : openU P20 = 30456 := by rw [openU, phB20.1]
  obtain ⟨l1, l2, l3, l4⟩ := lay20₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, cfgRec, hU, layOk_pb _ _ _ pb (fun _ => 0) _ _ _ _ pw (fun _ => 0)]; exact l1
  · rw [hT, cfgMain, hU, l3, layOk_pb _ _ _ (fun i => pb (P20.recLevels.length + i)) (fun _ => 0) _ _ _ _
      (fun i => pw (P20.recLevels.length + i)) (fun _ => 0)]; exact l2
  · rw [hU, l3, phB20.2]
  · rw [hU, l3, l4, hL]
  · rw [hU, phB20.1]

/-- **`P8`'s layout.** -/
theorem lay8 (pb pw : Nat → Nat) :
    LayOk (cfgRec P8 pb pw) (streamLanes P8) = true ∧ LayOk (cfgMain P8 pb pw) (streamLanes P8) = true ∧
    8 * stackEndL P8.grind P8.recOod P8.recLevels (openU P8 + 15) = phByte P8 .openMain ∧
    8 * stackEndL P8.grind P8.mainOod P8.mainLevels (stackEndL P8.grind P8.recOod P8.recLevels (openU P8 + 15) + 15) =
      hashedLen P8 ∧
    8 * openU P8 = phByte P8 .openRec + 96 := by
  have hT : streamLanes P8 = 46178 := sizes_P8.2.2.2.2.2.2.2.2.1
  have hL : hashedLen P8 = 369424 := sizes_P8.2.2.2.2.2.2.2.1
  have hU : openU P8 = 23786 := by rw [openU, phB8.1]
  obtain ⟨l1, l2, l3, l4⟩ := lay8₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, cfgRec, hU, layOk_pb _ _ _ pb (fun _ => 0) _ _ _ _ pw (fun _ => 0)]; exact l1
  · rw [hT, cfgMain, hU, l3, layOk_pb _ _ _ (fun i => pb (P8.recLevels.length + i)) (fun _ => 0) _ _ _ _
      (fun i => pw (P8.recLevels.length + i)) (fun _ => 0)]; exact l2
  · rw [hU, l3, phB8.2]
  · rw [hU, l3, l4, hL]
  · rw [hU, phB8.1]

end Lvm.Har
