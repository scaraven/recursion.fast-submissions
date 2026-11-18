-- New for lvm (HAR): `F`'s phases 4–7 (`chPh`, `chLinkPh`, `ksPh`, `ksLinkPh`) as functions of the
-- reader position, and the loads of `phases47` as stream values (composition of WP-16a's wiring with
-- QA1's `chLink_sound`, `ksLink_sound`).
import LvmQAsmArith2P47
import LvmQAsmHarBase
import LvmQEqKeccakGkr
import LvmQBusBase

-- (GOLF2: 4 declarations that `certified` does not use moved verbatim to `LvmQAsmHar47Off`, outside its import closure.)

/-!
# Phases 4–7: the reading

* `ringSwitch_run`: a ring switch reads 6 challenges and moves the position by `72·6`.
* `ksLinkPh_run`: QA1's `ksLinkPhase_run` without the `require` (which `decideProgH` does after the phase).
* `loadEs_val`: a `loadEs` cell is the stream's scalar (`phases47`'s points and lanes).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-! ## The reading -/

/-- The value of a ring switch at the challenges read at `P` (`ringSwitch`'s result). -/
def ringAt (v : Nat → FE) (P : Nat) (point s : List FE) : FE × (List FE → FE) :=
  let chs := samplesAt v P ringStages
  (polyEval (s.map (phiMap · chs)) gen, fun rPrime => ringWeight point rPrime (ringCoefficients chs))

theorem ringSwitch_run (sig : ByteArray) (point s : List FE) (st : RS) :
    ringSwitch point s sig st = (ringAt (feAt sig) (pos st) point s, ⟨pos st + 72 * ringStages, 0, st.ok⟩) := by
  rw [show ringSwitch point s = (samples ringStages >>= fun challenges =>
    pure (polyEval (s.map (phiMap · challenges)) gen,
      fun rPrime => ringWeight point rPrime (ringCoefficients challenges))) from rfl,
    bind_run, samples_run sig ringStages st (by decide), pure_run]
  rfl

/-! ## The loads of `phases47` -/

/-! ## A Keccak block of `phases47`: the loads and the GKR -/

end Lvm.Har
