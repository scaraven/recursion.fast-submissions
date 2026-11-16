-- lvm2 GOLF (a pure move out of `LvmSigBits`): the non-vacuity checks of `Q_sig`'s `BITS` tables on honest rows.
-- Nothing uses them, so they sit outside `Solution`'s import closure (`LvmFinDec` imports this module).
import LvmSigBits

set_option autoImplicit false

namespace Lvm.SigBits

open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.Loop Lvm.QSig

/-! ## Non-vacuity: honest tables -/

/-- The honest rows of a small word list satisfy every `Q_sig` `BITS` table's constraints, and its
output reads carry the word functions (`honest_tab`, for every word). -/
theorem honest_sig (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) :
    ∀ S ∈ sigSpecs I o bpl, ∀ w ∈ [(⟨0x0123456789abcdef⟩ : FK), ⟨0xffffffffffffffff⟩, 0, 1],
      (∀ C ∈ S.tab.cons, CPoly.evalB (fun i => FK.toBF64 (honest w i)) C = 0) ∧
        ∀ j < S.outs.length, (S.out j).Valid →
          CPoly.evalB (fun i => FK.toBF64 (honest w i)) (outPoly (S.out j)) =
            FK.toBF64 ⟨(S.out j).word w.val⟩ :=
  fun S _ w _ => honest_tab S w

/-- A computed check of the coefficients (independent of the proofs): the `shl 24`, `shr 40`
and `bit 5` polynomials on the honest row of `0x0123456789abcdef`. -/
theorem honest_check :
    evalK (honest ⟨0x0123456789abcdef⟩) (outPoly (.shl 24)) = ⟨0x6789abcdef000000⟩ ∧
      evalK (honest ⟨0x0123456789abcdef⟩) (outPoly (.shr 40)) = ⟨0x0000000000012345⟩ ∧
      evalK (honest ⟨0x0123456789abcdef⟩) (outPoly (.bit 5)) = ⟨1⟩ ∧
      ∀ C ∈ cons, evalK (honest ⟨0x0123456789abcdef⟩) C = 0 := by
  decide +kernel

end Lvm.SigBits
