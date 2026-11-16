-- New for lvm2 (T-Q): the wire gadget's closed forms (`LvmQEqWire`) against V_S's `FE` evaluators
-- (T-V's `msEvalF`, `thrEvalF`, through `FE.toExt3` and T-K's `msEvalA_bitsE`, `thrEvalA_bitsE`).
import LvmVEqWire
import LvmQSigDefs
import LvmQWire
import LvmQEqKeccakTape

-- (GOLF2: 76 declarations that `certified` does not use moved verbatim to `LvmQTypedHarCOff`, outside its import closure.)

-- ===== merged from `LvmQEqWire` (GOLF module merge: `LvmQEqWire.lean` is now a stub importing `LvmQWireSound`) =====
section
-- New for lvm2 (T-Q): Q_arith_eq of the S2 wiring gadget's blocks (`LvmQWire`), part 1: the
-- closed forms the rows compute. The proofs follow v1's template gadget specs (`LvmQKeccakTB`,
-- `LvmQKeccakParts*`); the `F`-side bridges (T-V's `dWire`, T-K's `msEvalA_bitsE`) are part 2.

/-!
# The wiring gadget's closed forms (`LvmQEqWire`)

Every gadget of `preW`, `postW`, `slotW` has a spec stating the value its result source takes in any
row assignment that satisfies the template (`THold`), as an `FE` closed form:

* `thrStepC`, `thrTailC`, `ltC`, `thrC`: `gThrStep`, `gThrTail`, `gLtTab`, `gThr` (`thrEvalA`'s rows);
* `msStepC`, `msTailC`, `msC`: `gMsStepA`, `gMsTail`, `gMs` (`msEvalA`'s rows);
* `gOmega_spec`: `ω_j = laneForm B (eq(a, (j mod 64 + ·) mod 64)) (j / 64)`, and `lt_pos`: that is
  entry `j` of `keccakLinearTranspose (prodW (eq a) B)` (the claim's weights, `Rep.weights`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build DM

variable {xv : Src → FE} {V : Nat → FE}

/-! ## Peeling -/

/-! ## `thrEvalA`'s rows -/

/-! ## `eq(ρ, 0)` -/

/-! ## The weights `ω` -/

/-! ## `msEvalA`'s rows -/

/-! ## The blocks' assertions -/

/-! ## The target block -/

end Lvm.Q1
end
-- ===== end of `LvmQEqWire` =====

/-!
# The wire gadget against V_S (`LvmQWireSound`)

The rows compute T-K's circuit twins: `q4E (msStepC …) = msStepA …`, `p2E (thrTailC …) = thrTailA …`,
`toExt3 (msC …) = msEvalA … 1`, `toExt3 (thrC …) = thrEvalA …`. With the bits of `m` in the cells
(`toExt3` of them is `bitsE m w`), T-K's `*_bitsE` and T-V's `toExt3_*F` give
**`msC_eq_msEvalF`** and **`thrC_eq_thrEvalF`**: the circuit's values are V_S's.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm DM Lvm.VEq Lvm.VEq.Wr

local notation "tE" => FE.toExt3

/-! ## `msEvalA` -/

/-! ## `thrEvalA` -/

/-! ## The bits of `m` and V_S's evaluators -/

/-- Bit `j` of `t` as an `FE` (`0` or `1`; the borrow chain's cells, HAR's `bitE`). -/
def bitF (t j : Nat) : FE := if t.testBit j then 1 else 0

/-! ## The wiring target -/

/-! ## The bits of the child's `s` (S2's `sSpec` class) -/

/-- **The `BITS` outputs of `s`'s lanes** (`sSpec`): bit `z` of the stream lane `hd + 9 + l` at
`sb + 64 l + z`. -/
def SBitsS (v : Nat → FK) (hd sb : Nat) : Prop :=
  ∀ l < 4, ∀ z < 64, Lvm.QSig.Out1 v (hd + 9 + l) (.bit z) (sb + 64 * l + z)

theorem bitWord (w : UInt64) {z : Nat} (hz : z < 64) :
    (Lvm.Bits.BOut.bit z).word w = if w.toNat.testBit z then 1 else 0 := by
  simp only [Lvm.Bits.BOut.word]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have hz' : z.toUInt64.toNat % 64 = z := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [hz', show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
  split_ifs with h <;> simp [Nat.testBit, Nat.shiftRight_eq_div_pow] at h ⊢ <;> omega

/-! ## The gadget -/

section gadget

open Lvm.Loop Lvm.Loop.Build Lvm.Har

end gadget

end Lvm.Q1
