-- New for `flock-recursive` (stage P4a pass 5 (P4e)): positive and negative controls for the
-- definitions of `FRSoundness4P4aRS`, `FRSoundness4P4aNZ`, `FRSoundness4P4aNS`,
-- `FRSoundness4P4aSplit`.
import FRSoundness4P4aSplit
import FRSoundness4P4aCtrl4

/-!
# Controls (P4a pass 5)

| Definition | Positive | Negative |
|---|---|---|
| `oLc4` | `oLc4_vBeta` | `not_oLc4_succ` |
| `SegInd` | `segInd_zlm4` | `not_segInd_zero` |
| `KfInd` | `kfInd4` | `not_kfInd_zero` (a zero kind factor) |
| `ShHoldsN4`/`truthSN4` | `shHoldsN4_zero`, `truthSN4_seg` | `not_shHoldsN4_link` (a broken chain link) |
| `resNode4` | `resNode4_zero_tbl` (the zero table) | `res_ne_node4` (a failed truth) |
| `Stmt4` | `stmt4_seg_iff`, `stmt4_node_iff` | `not_stmt4_seg` |
| `front4` | `front4_ok` | — |
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

/-- (+) Claim 2's binding accepts `v_β`. -/
theorem oLc4_vBeta (κ : CKind) (es : Log) : oLc4 κ es (vBetaL es) := rfl

/-- (−) … and nothing else. -/
theorem not_oLc4_succ (κ : CKind) (es : Log) : ¬ oLc4 κ es (vBetaL es + 1) := fun h => by
  have : (1 : F) = 0 := by
    have h' : vBetaL es + 1 = vBetaL es + 0 := by rw [add_zero]; exact h
    exact add_left_cancel h'
  exact one_ne_zero this

/-- (−) Matrices whose segment indicators are all `0` are not `SegInd`. -/
theorem not_segInd_zero (M : ZLM4) :
    ¬ SegInd ⟨M.Ak, M.Bk, fun _ _ _ => 0, M.Et⟩ := fun h =>
  zero_ne_one (h .L32 0)

/-- (−) A zero kind factor is not the node's batched indicators (block 0 of `N2` is a
`streamStart` block, so `B_1(0) = 1`). -/
theorem not_kfInd_zero : ¬ KfInd (zlm4 N4c.indN4 N4c.etN4) (fun _ _ _ => 0) := fun h => by
  have e := (h .N2 1 0).trans (kfInd4 .N2 1 0).symm
  rw [N4c.kf4_eq, one_pow] at e
  exact zero_ne_one e

/-- (+) The zero table meets the node's S truth. -/
theorem shHoldsN4_zero (ν : Rev4.NodeKind) : ShHoldsN4 ν (fun _ _ => (0 : F)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩

/-- (+) A segment's `truthSN4` is vacuous (`truthS` reads the segment's own `ShHoldsSeg`). -/
theorem truthSN4_seg (zw : Wit) (σ : Rev4.SegKind) (L es : Log) : truthSN4 zw (.seg σ) L es :=
  trivial

theorem chainLk4_N2_zero : N4c.chainLk4 .N2 0 = true := by
  simp [N4c.chainLk4, N4c.chLen, N4c.isAgg, N4c.cLen, Rev4.NodeKind.hasPrev]

/-- (−) A table whose block 1 does not take block 0's `h_out` as its `h_in` fails the truth. -/
theorem not_shHoldsN4_link :
    ¬ ShHoldsN4 .N2 (fun y p => if y = 1 ∧ p = 0 then (1 : F) else 0) := fun h => by
  have e := h.1 0 chainLk4_N2_zero 0 (by norm_num)
  simp at e

/-- (+) The zero table has zero residuals. -/
theorem resNode4_zero_tbl (ν : Rev4.NodeKind) (j u q : ℕ) :
    resNode4 ν (fun _ _ => (0 : F)) j u q = 0 := by
  unfold resNode4; split_ifs <;> simp

end FR.Snd.P4a
