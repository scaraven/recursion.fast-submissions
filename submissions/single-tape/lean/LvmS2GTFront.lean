-- New for lvm2 S2GT (GT-L2, 2026-11-15): the S2GT instances of the generic position and front lemmas (S2GT-STMT
-- 10a, 10b): `P20T`'s schedule on lane boundaries, the root pin's positions, the front's static facts and its phases
-- (`front_phasesG` at `cfgG20`).
import LvmS2GTSched
import LvmE2QHarFront
import LvmE2QInstT

/-!
# The S2GT pin and front positions

* **`alignT`**: `P20T`'s schedule keeps the cursor on lane boundaries (one kernel evaluation of `schedule P20T`).
* **10a** (the root pin at `P20T`): **`hbT`** (`Pb = posOf P20T 1`), **`pinHPT`**, **`pinQaT`** (QH5's `pin_phase`
  hypotheses), **`pinEndT`** (`Pb + 72ν + 24 = typedPosF P20T`).
* **10b** (the front at `P20T`): `regs_P20T`, `dsel_P20T`, the link's bounds, and **`front_phasesT`**
  (`front_phasesG` at `cfgG20`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm

theorem stE2_P20T : StE2 P20T := Or.inr rfl

set_option maxRecDepth 200000 in
/-- **The S2GT schedule keeps the cursor on lane boundaries** (the one evaluation of `schedule P20T` here). -/
theorem alignT : alignB P20T = true := by
  unfold P20T; rw [Lvm.Replay.P20_eq]; decide +kernel

/-! ## 10a: the root pin at `P20T` -/

/-- **`core_of_phases`'s `hb` at S2GT**: the pin's start `Pb` is `posOf P20T 1`. -/
theorem hbT : Lvm.Har.pos (RS.startH (headerBytesP P20T)) + nodeBytes * 2 ^ (P20T.level ⟨.main, 0⟩).cap =
    posOf P20T 1 := by
  rw [pos_startH, posOf_one stE2_P20T alignT]

/-- **QH5's `pin_phase` `hP` at S2GT.** -/
theorem pinHPT : posOf P20T 1 + 40 = 8 * phaseLane P20T .commit 1 := pin_hP stE2_P20T alignT

/-- **QH5's `pin_phase` `hqa` at S2GT.** -/
theorem pinQaT : phaseLane P20T .commit (P20T.nuMain + 1) = phaseLane P20T .commit 1 + 9 * P20T.nuMain :=
  pin_hqa stE2_P20T alignT

/-- **The pin's end is the typed phases' start at S2GT.** -/
theorem pinEndT : posOf P20T 1 + 72 * P20T.nuMain + 24 = typedPosF P20T := pin_end stE2_P20T alignT

/-! ## 10b: the front at `P20T` -/

/-- The front's blocks at `P20T` are `P20F`'s (the layout reads neither the stage nor `accV`). -/
theorem regs_P20T : RegsP P20T := regs_P20F

theorem dsel_P20T : DselP P20T := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `KS`'s split row at S2GT (as `P20`'s). -/
theorem ksSplit_P20T : ksSplit P20T = 7680 := ksSplit_P20F

/-- The `KS` link's bounds at S2GT (stated at `cfgG20.p`, as `front_phasesG` reads them). -/
theorem blk_cfgG20 : spongeBlocks cfgG20.p - 1 < 2 ^ cfgG20.p.ksLog := by
  rw [show cfgG20.p = P20T from rfl, sizes_P20T.1.2.2.2.2.1]; decide

theorem ksp_cfgG20 : ksSplit cfgG20.p + 399 + 31 < 2 ^ cfgG20.p.ksLog := by
  rw [show cfgG20.p = P20T from rfl, ksSplit_P20T]; decide

set_option maxRecDepth 100000 in
/-- **The front's phases at `P20T`** (`front_phasesG` at `cfgG20`): V's tape (with the wiring), `KS` and `KS` link
phases run from their starts to the next phase's start, and the front's claims stand for V's. -/
theorem front_phasesT {c : Ctx} {M : Mem} {sig : ByteArray} {q : Ptr}
    (hS : Lvm.Q1.Streamed M sig (streamLanes P20T))
    (hTo : posOf P20T (phaseItem0 P20T .openMain) + 48 ≤ 8 * streamLanes P20T)
    (hg : M.k (pbB cfgG20) = 1) (hpow : Lvm.Q1.PowOkV (feAt sig) (powFront P20T))
    (hrw : ∀ j < 128, M.k (tBw cfgG20 + j) = rowWordD (Lvm.Q2.slicesOf M (wireSlices P20T)) j)
    (hrk : ∀ j < 128, M.k (tBk cfgG20 + j) = rowWordD (Lvm.Q2.slicesOf M (ksSlices P20T)) j)
    (pub : Pub) (hnb : ∀ j < 20, (kc ((sigIn cfgG20).bn + 2 + j)).val M = bitE pub.n j)
    (hn : 1 ≤ pub.n ∧ pub.n ≤ 2 ^ 20) (hsb : ∀ i < 256, M.k (bsB cfgG20 + i) = if sBitsD pub.s i then 1 else 0)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) (zc : Cell) (b : Bool)
    (hsm : b = true → pub.n ≤ 2 ^ 18) (h : Lvm.QSig.Ok c M (frontF cfgG20) q) :
    ∃ tp co lo,
      Lvm.Har.PhaseAt (tapeD P20T.logN (dSelBits P20T) (dSel P20T) pub.s pub.n) sig
        (posOf P20T (phaseItem0 P20T .tape)) (posOf P20T (phaseItem0 P20T .ks)) tp ∧
      Lvm.Har.PhaseAt (callerD P20T.ksLog) sig (posOf P20T (phaseItem0 P20T .ks))
        (posOf P20T (phaseItem0 P20T .ksLink)) co ∧
      Lvm.Har.PhaseAt (ksLinkD P20T.ksLog (ksXLog P20T) (contRows P20T)) sig (posOf P20T (phaseItem0 P20T .ksLink))
        (posOf P20T (phaseItem0 P20T .openMain)) lo ∧
      List.Forall₂ (Lvm.Q2.FRelZ M zc b) (frontF cfgG20 q).1.cs (frontClaimsD P20T pub tp co lo) ∧
      vs M (frontF cfgG20 q).1.mb = selectorPoint (pub.n - 1) 20 :=
  front_phasesG (C := cfgG20) stE2_P20T alignT regs_P20T dsel_P20T
    blk_cfgG20 ksp_cfgG20 hS hTo hg hpow hrw hrk pub hnb hn hsb hh zc b
    hsm h

end Lvm.E2Q
