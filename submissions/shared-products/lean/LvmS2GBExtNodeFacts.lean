-- New for lvm2 MP-B cap pruning (CAP-X4, 2026-11-17): S2GB's extractor stage's static facts (`ProgOK stB20`), for
-- the node branch's semantics (proof-help of `EXB_node`).
import LvmS2GBExtProg
import LvmS2GBExtRep

/-!
# `ProgOK stB20`

`progFacts_stS20`'s facts at `stB20` (from the replay record `replayOKB_stB20`, `|π|` as its value `269,336`) and `ProgOK stB20`.
The facts that read `st.pz` hold at every size of the range `SzB` (the offsets do not read `st.pz`).
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS

/-- S2GB's static facts (`progFacts_stS20`'s at `stB20`, `|π|` as its value). -/
theorem progFacts_stB20 : stB20.occ0 ≤ 64 ∧ 269336 < 2 ^ 32 ∧ nChainS stB20 < 2 ^ 11 ∧
    nChainS stB20 ≤ (fsMsgsS stB20).length ∧
    ((fsMsgsS stB20).take (nChainS stB20)).all (msgOkP 269336) = true ∧
    (fsMsgsS stB20).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    (∀ k < 14, foldPosKS stB20 k < nChainS stB20) ∧
    capOffS stB20 0 / 8 + 4 * 2 ^ 8 ≤ 269336 / 8 ∧ capOffS stB20 1 / 8 + 4 * 2 ^ 7 ≤ 269336 / 8 ∧
    capOffS stB20 2 / 8 + 4 * 2 ^ 7 ≤ 269336 / 8 ∧ resOffS stB20 / 8 + 3 * 2 ^ 9 ≤ 269336 / 8 ∧
    capWS stB20 0 + 4 * 2 ^ 8 < 2 ^ 62 ∧ capWS stB20 1 + 4 * 2 ^ 7 < 2 ^ 62 ∧ capWS stB20 2 + 4 * 2 ^ 7 < 2 ^ 62 ∧
    resWS stB20 + 3 * 2 ^ 9 < 2 ^ 63 ∧ posL 269336 ≤ 2 ^ 60 ∧ 15 ≤ 269336 / 8 :=
  Lvm.ASM.progFactsG stB20 Lvm.ASM.replayOKB_stB20

/-- **S2GB's extractor program facts** (`progOK_stS20`'s). -/
theorem progOK_stB20 : ProgOK stB20 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := progFacts_stB20
  have e : msgOkS stB20 = msgOkP 269336 := by funext m; rw [msgOkS, stB20_pz]
  exact ⟨outOK_stB20, h1, stB20_pz ▸ h2, h3, h4, e ▸ h5, h6, h7, stB20_pz ▸ h8, stB20_pz ▸ h9, stB20_pz ▸ h10,
    stB20_pz ▸ h11, h12, h13, h14, h15, by show posL stB20.pz ≤ 2 ^ 60; rw [stB20_pz]; exact h16, stB20_pz ▸ h17⟩

end Lvm.XB
