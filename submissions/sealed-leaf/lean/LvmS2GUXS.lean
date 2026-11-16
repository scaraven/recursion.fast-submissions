-- New for lvm2 U-TAPE (UT-L, 2026-11-16): S2GU's extractor stage `stU20` and its decided facts (UTAPE-STMT 27–30;
-- `LvmS2GTXS`'s twins at `P20U`).
import LvmS2GUSched
import LvmXSStage
import LvmXSExtEq
import LvmS2GUSchedLit
import LvmXSWinU
import LvmS2GUOff

/-!
# S2GU's extractor stage

* **`stU20`**: `P20U`'s schedule, header `headerBytesP P20U` (5,664), `|π| = piSize P20U` (283,960), `openMain` after
  the fifth phase, the root's 46 occupied words (`leafLensU = [368, 384]`).
* Decided (one kernel evaluation each): **`outOK_stU20`**, **`progOK_stU20`**, **`replayOK_stU20`**; `fmtOK_stU20`.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

-- `leafLensU` is in `LvmXSWinU`.

/-- S2GU's leaf lengths are `P20U`'s level rows. -/
theorem leafLensU_eq : leafLensU = [(P20U.level ⟨.main, 0⟩).row, (P20U.level ⟨.main, 1⟩).row] := by
  decide +kernel

/-- **S2GU's stage**: `P20U`'s schedule, the 16-B header (5,664), `|π| = piSize P20U` (283,960), `openMain` after
the fifth phase, the root's 46 occupied words (`leafLensU`). (D-WIN: the stage also names the window `(32, 16)`.) -/
def stU20 : XStage :=
  ⟨P20U, headerBytesP P20U, piSize P20U, leafLensU, (((phases P20U).take 5).flatMap (·.2)).length, 46⟩

/-- S2GU's `|π|`. -/
theorem stU20_pz : stU20.pz = 283960 := sizes_P20U.1.1

set_option maxRecDepth 200000 in
/-- S2GU's output facts, in one kernel evaluation (`outOK_allG`'s at `stU20`). -/
theorem outOK_allU :
    (Replay.planItems stU20.p Replay.w0 stU20.items).2.ok = true ∧
    (blocksS stU20).all (fun b => blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b)) = true ∧
    8 + 8 * ((blocksS stU20).map blkPOutsL).sum = stU20.pz ∧ 4928 ≤ stU20.pz ∧ stU20.pz < 2 ^ 64 ∧
    6 + ((blocksS stU20).map Blk.lanes).sum ≤ nCp ∧ qSS stU20 < 2 ^ 64 ∧
    ((blocksS stU20).map blkPCostL).sum + ((blocksS stU20).map blkTCostL).sum ≤ 7128485 ∧
    ((blocksS stU20).map blkPOutsL).sum + ((blocksS stU20).map blkTOutsL).sum ≤ 163533 ∧
    ((blocksS stU20).map blkPSizeL).sum + ((blocksS stU20).map blkTSizeL).sum ≤ 250000 := by
  -- the schedule read off the literal `schedU20` (GOLF3-U, `schedule_P20U_lit`)
  rw [stU20_pz, qSS, XStage.items, blocksS, blocks, show stU20.p = P20U from rfl, schedule_P20U_lit]
  decide +kernel

/-- **UTAPE-STMT 27** (owner L): the node output's static facts at S2GU (one kernel evaluation, `outOK_stG20`'s). -/
theorem outOK_stU20 : OutOK stU20 :=
  let h := outOK_allU
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- S2GU's static facts (`progFacts_stG20`'s at `stU20`, one `decide +kernel`, `|π|` as its value). -/
theorem progFacts_stU20 : stU20.occ0 ≤ 64 ∧ 283960 < 2 ^ 32 ∧ nChainS stU20 < 2 ^ 11 ∧
    nChainS stU20 ≤ (fsMsgsS stU20).length ∧
    ((fsMsgsS stU20).take (nChainS stU20)).all (msgOkP 283960) = true ∧
    (fsMsgsS stU20).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    (∀ k < 14, foldPosKS stU20 k < nChainS stU20) ∧
    capOffS stU20 0 / 8 + 4 * 2 ^ 8 ≤ 283960 / 8 ∧ capOffS stU20 1 / 8 + 4 * 2 ^ 7 ≤ 283960 / 8 ∧
    capOffS stU20 2 / 8 + 4 * 2 ^ 7 ≤ 283960 / 8 ∧ resOffS stU20 / 8 + 3 * 2 ^ 9 ≤ 283960 / 8 ∧
    capWS stU20 0 + 4 * 2 ^ 8 < 2 ^ 62 ∧ capWS stU20 1 + 4 * 2 ^ 7 < 2 ^ 62 ∧ capWS stU20 2 + 4 * 2 ^ 7 < 2 ^ 62 ∧
    resWS stU20 + 3 * 2 ^ 9 < 2 ^ 63 ∧ posL 283960 ≤ 2 ^ 60 ∧ 15 ≤ 283960 / 8 := by
  decide +kernel

/-- **UTAPE-STMT 28** (owner L): the extractor program's static facts at S2GU (`progOK_stG20`'s). -/
theorem progOK_stU20 : ProgOK stU20 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := progFacts_stU20
  have e : msgOkS stU20 = msgOkP 283960 := by funext m; rw [msgOkS, stU20_pz]
  exact ⟨outOK_stU20, h1, stU20_pz ▸ h2, h3, h4, e ▸ h5, h6, h7, stU20_pz ▸ h8, stU20_pz ▸ h9, stU20_pz ▸ h10,
    stU20_pz ▸ h11, h12, h13, h14, h15, by show posL stU20.pz ≤ 2 ^ 60; rw [stU20_pz]; exact h16, stU20_pz ▸ h17⟩

set_option maxRecDepth 200000 in
/-- **UTAPE-STMT 29** (owner L): the replay's facts at S2GU (`replayOK_stG20`'s split after the fifth phase). -/
theorem replayOK_stU20 : Lvm.ASM.ReplayOK stU20 :=
  Lvm.ASM.replayOK_ofR (pre := ((phases P20U).take 5).flatMap (·.2)) (rest := ((phases P20U).drop 5).flatMap (·.2))
    (by show schedule P20U = _; rw [schedule, ← List.flatMap_append, List.take_append_drop]) rfl
    (by
      -- `|π|` as its value and the items read off the literal `phasesU20` (GOLF3-U, `LvmS2GTXS`'s pattern)
      rw [show stU20 = ⟨P20U, headerBytesP P20U, 283960, leafLensU, (((phases P20U).take 5).flatMap (·.2)).length, 46⟩
        by rw [stU20, sizes_P20U.1.1], phases_P20U_lit]
      decide +kernel)

/-- `stU20`'s read widths are `readWidthsP P20U`. -/
theorem readWidthsS_stU20 : readWidthsS stU20 = readWidthsP P20U := by
  unfold readWidthsS readWidthsP
  exact List.flatMap_congr fun it _ => by cases it <;> rfl

/-- **UTAPE-STMT 30** (owner L): S2GU's format agrees with its stage (`fmtOK_stG20`'s; `occOfU`'s 46 is `occ0`). -/
theorem fmtOK_stU20 : Lvm.ASM.FmtOK stU20 Lvm.CT.fmtU20 :=
  ⟨fun n => by show rwU20 n = _; rw [rwU20, readWidthsS_stU20], rfl, rfl, rfl, rfl, rfl⟩

end Lvm.XS
