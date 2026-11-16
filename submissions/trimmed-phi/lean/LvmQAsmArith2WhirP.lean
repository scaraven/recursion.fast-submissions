-- New for lvm (HAR-WH): the configurations of phases 8–9 at P20 and P8 (start lane, position
-- chunks, coordinate chunks) and their static checks.
import LvmQAsmArith2WhirPD
import LvmQAsmArith2Whir
import LvmSchedLit

-- (GOLF2: 6 declarations that `certified` does not use moved verbatim to `LvmQAsmArith2WhirPOff`, outside its import closure.)

/-!
# Phases 8–9 at `P20` and `P8`

`cfgMain p pb` (M′, lvm2 roll 11 `S2GM`: one commitment): `C_main`'s opening starts at position `8 · openU p` (the
`openMain` phase's first entry plus phase 7's four pending scalars). Opening
`k`'s positions are the `K` cells `pb k + j` (`k = i`: `C_main`'s level `i`; Q_link's `pt.k + posIdx p k j`). Position chunks: `2^⌊log t⌋` then the rest rounded up
(`311 = 256 + 64`, `191 = 128 + 64`, `156 = 128 + 32`, `142 = 128 + 16`); coordinate chunks: the
binary digits of `κ`. `lay20`, `lay8`: the layout checks against the stream's lanes, and the ends
(`C_main` at `hashedLen`, `msg = 0`: `decideF`'s `ent = |Σ|`).
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

end Lvm.Har
