-- Moved out of `LvmQAsmArith2WhirP` (lvm2 roll 8, wave L, L-W; a pure move): the configurations of phases 8–9
-- (`phByte`, `openU`, `pchOf`, `bitsDesc`, `cfgRec`, `cfgMain`), so that `LvmQAsmArith2` (the B program's Q_arith)
-- does not import the openings' proofs. Their static checks stay in `LvmQAsmArith2WhirP`.
import LvmQAsmArith2WhirD

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
    fun i => bitsDesc (p.recLevels.getD i default).kappa, p.grind, p.recOod, pw⟩

/-- `C_main`'s opening (after `C_rec`'s). -/
def cfgMain (p : Params) (pb pw : Nat → Nat) : SCfg :=
  ⟨p.mainLevels, p.nuMain, stackEndL p.grind p.recOod p.recLevels (openU p + 15), fun i => pb (p.recLevels.length + i),
    fun i => pchOf (p.mainLevels.getD i default).t, fun i => bitsDesc (p.mainLevels.getD i default).kappa,
    p.grind, p.mainOod, fun i => pw (p.recLevels.length + i)⟩

end Lvm.Har
