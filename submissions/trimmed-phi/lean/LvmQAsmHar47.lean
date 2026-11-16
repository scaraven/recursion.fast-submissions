-- New for lvm (HAR): `F`'s phases 4–7 (`chPh`, `chLinkPh`, `ksPh`, `ksLinkPh`) as functions of the
-- reader position, and the loads of `phases47` as stream values (composition of WP-16a's wiring with
-- QA1's `gkr_spec`, `chLink_sound`, `ksLink_sound`).
import LvmQAsmArith2P47
import LvmQAsmHarBase
import LvmQEqKeccakGkr
import LvmQBusBase

-- (GOLF2: 4 declarations that `certified` does not use moved verbatim to `LvmQAsmHar47Off`, outside its import closure.)

/-!
# Phases 4–7: the reading

* `ringSwitch_run`: a ring switch reads 6 challenges and moves the position by `72·6`.
* `ksPh_run`: `KS`'s instance point, lanes, Keccak GKR (`verifyKeccak_run`), ring switch, from any
  position (lvm2 S2: v1's `CH` phases are gone; the tape and wire are `LvmQAsmHarP47`'s).
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

/-- The positions of phase 4 (or 6) from its start `P` with `ls` instance coordinates: the lanes, the GKR. -/
def kV (ls P : Nat) : Nat := P + 72 * ls
def kG (ls P : Nat) : Nat := kV ls P + 24 * lanes

/-- **Phase 4 (and 6) from position `P`**: the point and lanes read at `P`, the GKR's `vkSpec`, the ring
switch at the GKR's end. -/
theorem kPh_run (sig : ByteArray) (ls : Nat) (hls : 1 ≤ ls) (s : RS) :
    (do let r ← samples ls; let v ← readEs lanes; let ko ← verifyKeccak ls r v
        let ring ← ringSwitch ko.slicePoint ko.slices; pure (r, v, ko, ring) : DM _) sig s =
      let r := samplesAt (feAt sig) (pos s) ls
      let v := scalarsAt (feAt sig) (kV ls (pos s) + 40) lanes
      let K := vkSpec (feAt sig) ls r v (kG ls (pos s)) s.ok
      ((r, v, K.1, ringAt (feAt sig) (K.2.2 + 24 * kBits) K.1.slicePoint K.1.slices),
        ⟨K.2.2 + 24 * kBits + 72 * ringStages, 0, K.2.1⟩) := by
  rw [bind_run, samples_run sig ls s hls]
  dsimp only
  rw [bind_run, readEs_run]
  dsimp only
  rw [bind_run, verifyKeccak_run sig ls _ _ _ (kG ls (pos s)) (by simp [kG, kV, pos])]
  dsimp only
  rw [bind_run, ringSwitch_run, pure_run]
  simp only [pos, samplesAt, kV, Nat.add_zero]

/-! ## The loads of `phases47` -/

/-! ## A Keccak block of `phases47`: the loads and the GKR -/

end Lvm.Har
