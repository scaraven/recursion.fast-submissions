-- New for lvm (HAR-WH): the configurations of phases 8–9 at P20 and P8 (start lane, position
-- chunks, coordinate chunks) and their static checks.
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

/-- The byte offset of phase `ph`'s first trace entry. -/
def phByte (p : Params) (ph : Phase) : Nat := ((phaseFirst p).find? (·.1 == ph)).elim 0 (·.2.2)

/-- The start lane of phases 8–9: phase 7 leaves four scalars pending. -/
def openU (p : Params) : Nat := (phByte p .openRec + 96) / 8

/-- Position chunks: `2^⌊log t⌋`, then the rest rounded up to a power of two. -/
def pchOf (t : Nat) : List Nat :=
  if 2 ^ Nat.log2 t = t then [Nat.log2 t] else [Nat.log2 t, Nat.clog 2 (t - 2 ^ Nat.log2 t)]

/-- The binary digits of `n < 64`, high first. -/
def bitsDesc (n : Nat) : List Nat := (List.range 6).reverse.filter fun b => n.testBit b

/-- `C_rec`'s opening. -/
def cfgRec (p : Params) (pb pw : Nat → Nat) : SCfg :=
  ⟨p.recLevels, p.nuRec, openU p, pb, fun i => pchOf (p.recLevels.getD i default).t,
    fun i => bitsDesc (p.recLevels.getD i default).kappa, p.grind, false, pw⟩

/-- `C_main`'s opening (after `C_rec`'s). -/
def cfgMain (p : Params) (pb pw : Nat → Nat) : SCfg :=
  ⟨p.mainLevels, p.nuMain, stackEndL p.grind false p.recLevels (openU p + 15), fun i => pb (1 + i),
    fun i => pchOf (p.mainLevels.getD i default).t, fun i => bitsDesc (p.mainLevels.getD i default).kappa,
    p.grind, p.mainOod, fun i => pw (1 + i)⟩

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

theorem phB20 : phByte P20 .openRec = 326112 ∧ phByte P20 .openMain = 762320 := by decide +kernel
theorem phB8 : phByte P8 .openRec = 267712 ∧ phByte P8 .openMain = 407056 := by decide +kernel

theorem lay20₀ : LayOk ⟨P20.recLevels, P20.nuRec, 40776, fun _ => 0, fun i => pchOf (P20.recLevels.getD i default).t,
      fun i => bitsDesc (P20.recLevels.getD i default).kappa, P20.grind, false, fun _ => 0⟩ 179052 = true ∧
    LayOk ⟨P20.mainLevels, P20.nuMain, 95290, fun _ => 0, fun i => pchOf (P20.mainLevels.getD i default).t,
      fun i => bitsDesc (P20.mainLevels.getD i default).kappa, P20.grind, P20.mainOod, fun _ => 0⟩ 179052 = true ∧
    stackEndL P20.grind false P20.recLevels (40776 + 15) = 95290 ∧
    8 * stackEndL P20.grind P20.mainOod P20.mainLevels (95290 + 15) = 1432416 := by
  decide +kernel

theorem lay8₀ : LayOk ⟨P8.recLevels, P8.nuRec, 33476, fun _ => 0, fun i => pchOf (P8.recLevels.getD i default).t,
      fun i => bitsDesc (P8.recLevels.getD i default).kappa, P8.grind, false, fun _ => 0⟩ 66728 = true ∧
    LayOk ⟨P8.mainLevels, P8.nuMain, 50882, fun _ => 0, fun i => pchOf (P8.mainLevels.getD i default).t,
      fun i => bitsDesc (P8.mainLevels.getD i default).kappa, P8.grind, P8.mainOod, fun _ => 0⟩ 66728 = true ∧
    stackEndL P8.grind false P8.recLevels (33476 + 15) = 50882 ∧
    8 * stackEndL P8.grind P8.mainOod P8.mainLevels (50882 + 15) = 533824 := by
  decide +kernel

/-- **`P20`'s layout**: both openings pass the static checks below the stream's lanes; `C_rec` ends
at the `openMain` entry, `C_main` at `hashedLen`. -/
theorem lay20 (pb pw : Nat → Nat) :
    LayOk (cfgRec P20 pb pw) (streamLanes P20) = true ∧ LayOk (cfgMain P20 pb pw) (streamLanes P20) = true ∧
    8 * stackEndL P20.grind false P20.recLevels (openU P20 + 15) = phByte P20 .openMain ∧
    8 * stackEndL P20.grind P20.mainOod P20.mainLevels (stackEndL P20.grind false P20.recLevels (openU P20 + 15) + 15) =
      hashedLen P20 ∧
    8 * openU P20 = phByte P20 .openRec + 96 := by
  have hT : streamLanes P20 = 179052 := sizes_P20.2.2.2.2.2.2.1
  have hL : hashedLen P20 = 1432416 := sizes_P20.2.2.2.2.2.1
  have hU : openU P20 = 40776 := by rw [openU, phB20.1]
  obtain ⟨l1, l2, l3, l4⟩ := lay20₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, cfgRec, hU, layOk_pb _ _ _ pb (fun _ => 0) _ _ _ _ pw (fun _ => 0)]; exact l1
  · rw [hT, cfgMain, hU, l3, layOk_pb _ _ _ (fun i => pb (1 + i)) (fun _ => 0) _ _ _ _ (fun i => pw (1 + i))
      (fun _ => 0)]; exact l2
  · rw [hU, l3, phB20.2]
  · rw [hU, l3, l4, hL]
  · rw [hU, phB20.1]

/-- **`P8`'s layout.** -/
theorem lay8 (pb pw : Nat → Nat) :
    LayOk (cfgRec P8 pb pw) (streamLanes P8) = true ∧ LayOk (cfgMain P8 pb pw) (streamLanes P8) = true ∧
    8 * stackEndL P8.grind false P8.recLevels (openU P8 + 15) = phByte P8 .openMain ∧
    8 * stackEndL P8.grind P8.mainOod P8.mainLevels (stackEndL P8.grind false P8.recLevels (openU P8 + 15) + 15) =
      hashedLen P8 ∧
    8 * openU P8 = phByte P8 .openRec + 96 := by
  have hT : streamLanes P8 = 66728 := sizes_P8.2.2.2.2.2.2.2.2.1
  have hL : hashedLen P8 = 533824 := sizes_P8.2.2.2.2.2.2.2.1
  have hU : openU P8 = 33476 := by rw [openU, phB8.1]
  obtain ⟨l1, l2, l3, l4⟩ := lay8₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, cfgRec, hU, layOk_pb _ _ _ pb (fun _ => 0) _ _ _ _ pw (fun _ => 0)]; exact l1
  · rw [hT, cfgMain, hU, l3, layOk_pb _ _ _ (fun i => pb (1 + i)) (fun _ => 0) _ _ _ _ (fun i => pw (1 + i))
      (fun _ => 0)]; exact l2
  · rw [hU, l3, phB8.2]
  · rw [hU, l3, l4, hL]
  · rw [hU, phB8.1]

end Lvm.Har
