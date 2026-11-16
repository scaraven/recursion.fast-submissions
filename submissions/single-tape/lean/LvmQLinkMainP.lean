-- lvm2 GOLF (a pure move out of `LvmQLinkMain`): Q_link's decided static facts at `P20` and `P8` and the replays at
-- both parameter sets. Nothing in `Solution`'s import closure uses them, so they leave the certificate's build
-- (≈ 49 s of kernel decisions there). `LvmFinDec` imports this module.
import LvmQLinkMain

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

set_option maxRecDepth 200000 in
theorem streamOk_P8 : StreamOk P8 := by rw [P8_eq]; exact ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 200000 in
theorem qOk_P20 : QOk P20 lay20 :=
  qOk_of streamOk_P20 (by show qOkB P20 (layOf P20 11 8 18 10) = true; rw [P20_eq]; decide +kernel)

set_option maxRecDepth 200000 in
theorem qOk_P8 : QOk P8 lay8 :=
  qOk_of streamOk_P8 (by show qOkB P8 (layOf P8 11 5 17 8) = true; rw [P8_eq]; decide +kernel)

set_option maxRecDepth 200000 in
/-- Q_link's program check at `P20` (so `(toProgram …).wf`, by `toProgram_wf`). -/
theorem segsOk_P20 : segsOk ⟨nInKOf lay20, 0⟩ (qlink P20 lay20 ⟨nInKOf lay20, 0⟩).2 = true := by
  show segsOk ⟨nInKOf (layOf P20 11 8 18 10), 0⟩
    (qlink P20 (layOf P20 11 8 18 10) ⟨nInKOf (layOf P20 11 8 18 10), 0⟩).2 = true
  rw [P20_eq]; decide +kernel

set_option maxRecDepth 200000 in
theorem segsOk_P8 : segsOk ⟨nInKOf lay8, 0⟩ (qlink P8 lay8 ⟨nInKOf lay8, 0⟩).2 = true := by
  show segsOk ⟨nInKOf (layOf P8 11 5 17 8), 0⟩
    (qlink P8 (layOf P8 11 5 17 8) ⟨nInKOf (layOf P8 11 5 17 8), 0⟩).2 = true
  rw [P8_eq]; decide +kernel

section
variable {ws : List Word} {c : Ctx} {M : Mem}

/-- **Replay at `P20`** from Q_link's rows (`V_S` = `VSL P20 tabs`, any tables). -/
theorem qlink20_replay (tabs : Pub → List M3.Tab) (vk cd : Digest) (hin : QIn P20 lay20 ws M) (hws : 2 ^ 18 ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : 2 ^ 18 ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink P20 lay20 pt).2) (hA : SegsAssert M pt (qlink P20 lay20 pt).2)
    (hparse : parseOk P20 vk cd (reassemble P20 (decode P20 ws)) = true) :
    (VSL P20 tabs vk cd (reassemble P20 (decode P20 ws))).runSeq (decode P20 ws) =
        some (decideF P20 (M3.real P20 tabs) vk cd (sigma P20 ws)) ∧
      LinkOk P20 (decode P20 ws) ∧ PadOkB (wordsBytes ws) (hashedLen P20) :=
  qlink_replay rfl (M3.real P20 tabs) vk cd planOk_P20 streamOk_P20 qOk_P20 hin hws hinj hN
    (by simp only [lay20, layOf]; omega) h hA hparse

/-- **Replay at `P8`** from Q_link's rows. -/
theorem qlink8_replay (tabs : Pub → List M3.Tab) (vk cd : Digest) (hin : QIn P8 lay8 ws M) (hws : 2 ^ 17 ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : 2 ^ 17 ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink P8 lay8 pt).2) (hA : SegsAssert M pt (qlink P8 lay8 pt).2)
    (hparse : parseOk P8 vk cd (reassemble P8 (decode P8 ws)) = true) :
    (VSL P8 tabs vk cd (reassemble P8 (decode P8 ws))).runSeq (decode P8 ws) =
        some (decideF P8 (M3.real P8 tabs) vk cd (sigma P8 ws)) ∧
      LinkOk P8 (decode P8 ws) ∧ PadOkB (wordsBytes ws) (hashedLen P8) :=
  qlink_replay rfl (M3.real P8 tabs) vk cd planOk_P8 streamOk_P8 qOk_P8 hin hws hinj hN
    (by simp only [lay8, layOf]; omega) h hA hparse

end

end Lvm.QLink
