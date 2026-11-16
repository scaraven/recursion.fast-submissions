-- New for lvm2 S2GT (GT-L, 2026-11-15): S2GT's extractor stage `stG20` and its decided facts (frozen statements
-- S2GT-STMT 13–15), and the stage-generic lemmas the S2GT certificate shares with S2GF's (the child's trace bridge,
-- the guarded certificate's extractor, `NodeSoundM` from the pair form).
import LvmS2GTSched
import LvmXSComputes
import LvmXSExtRun
import LvmXSChild
import LvmNodeSoundTr
import LvmCertM20

/-!
# S2GT's extractor stage

* **`stG20`**: `P20T`'s schedule, header `headerBytesP P20T` (5,664), `|π| = piSize P20T` (305,992), M′'s rows,
  `openMain` after the seventh phase, the root's 47 occupied words (lead decision D1).
* Decided (one kernel evaluation each, `|π|` entering as its value): **`outOK_stG20`**, **`progOK_stG20`**,
  **`replayOK_stG20`**.
* Stage-generic: `lens_S`, `trBridgeS` (the extractor's trace reader is `Q_link`'s `decode` at any stage whose plan
  walk is ok), `EXS_Wn`, `extS`.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-- **S2GT's stage.** -/
def stG20 : XStage :=
  ⟨P20T, headerBytesP P20T, piSize P20T, leafLens, (((phases P20T).take 7).flatMap (·.2)).length, 47⟩

/-- S2GT's `|π|`. -/
theorem stG20_pz : stG20.pz = 305992 := sizes_P20T.1.1

set_option maxRecDepth 200000 in
/-- S2GT's output facts, in one kernel evaluation (`outOK_all`'s at `stG20`). -/
theorem outOK_allG :
    (Replay.planItems stG20.p Replay.w0 stG20.items).2.ok = true ∧
    (blocksS stG20).all (fun b => blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b)) = true ∧
    8 + 8 * ((blocksS stG20).map blkPOutsL).sum = stG20.pz ∧ 4928 ≤ stG20.pz ∧ stG20.pz < 2 ^ 64 ∧
    6 + ((blocksS stG20).map Blk.lanes).sum ≤ nCp ∧ qSS stG20 < 2 ^ 64 ∧
    ((blocksS stG20).map blkPCostL).sum + ((blocksS stG20).map blkTCostL).sum ≤ 7128485 ∧
    ((blocksS stG20).map blkPOutsL).sum + ((blocksS stG20).map blkTOutsL).sum ≤ 163533 ∧
    ((blocksS stG20).map blkPSizeL).sum + ((blocksS stG20).map blkTSizeL).sum ≤ 250000 := by
  rw [stG20_pz]
  decide +kernel

/-- **S2GT-STMT 13** (owner L): the node output's static facts at S2GT. -/
theorem outOK_stG20 : OutOK stG20 :=
  let h := outOK_allG
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- S2GT's static facts (`progFacts_stF20`'s at `stG20`, one `decide +kernel`, `|π|` as its value). -/
theorem progFacts_stG20 : stG20.occ0 ≤ 64 ∧ 305992 < 2 ^ 32 ∧ nChainS stG20 < 2 ^ 11 ∧
    nChainS stG20 ≤ (fsMsgsS stG20).length ∧
    ((fsMsgsS stG20).take (nChainS stG20)).all (msgOkP 305992) = true ∧
    (fsMsgsS stG20).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    (∀ k < 14, foldPosKS stG20 k < nChainS stG20) ∧
    capOffS stG20 0 / 8 + 4 * 2 ^ 8 ≤ 305992 / 8 ∧ capOffS stG20 1 / 8 + 4 * 2 ^ 7 ≤ 305992 / 8 ∧
    capOffS stG20 2 / 8 + 4 * 2 ^ 7 ≤ 305992 / 8 ∧ resOffS stG20 / 8 + 3 * 2 ^ 9 ≤ 305992 / 8 ∧
    capWS stG20 0 + 4 * 2 ^ 8 < 2 ^ 62 ∧ capWS stG20 1 + 4 * 2 ^ 7 < 2 ^ 62 ∧ capWS stG20 2 + 4 * 2 ^ 7 < 2 ^ 62 ∧
    resWS stG20 + 3 * 2 ^ 9 < 2 ^ 63 ∧ posL 305992 ≤ 2 ^ 60 ∧ 15 ≤ 305992 / 8 := by
  decide +kernel

/-- **S2GT-STMT 14** (owner L): the extractor program's static facts at S2GT. -/
theorem progOK_stG20 : ProgOK stG20 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := progFacts_stG20
  have e : msgOkS stG20 = msgOkP 305992 := by funext m; rw [msgOkS, stG20_pz]
  exact ⟨outOK_stG20, h1, stG20_pz ▸ h2, h3, h4, e ▸ h5, h6, h7, stG20_pz ▸ h8, stG20_pz ▸ h9, stG20_pz ▸ h10,
    stG20_pz ▸ h11, h12, h13, h14, h15, by show posL stG20.pz ≤ 2 ^ 60; rw [stG20_pz]; exact h16, stG20_pz ▸ h17⟩

set_option maxRecDepth 200000 in
/-- **S2GT-STMT 15** (owner L): the replay's facts at S2GT (`replayOK_stF20`'s split after the seventh phase). -/
theorem replayOK_stG20 : Lvm.ASM.ReplayOK stG20 :=
  Lvm.ASM.replayOK_ofR (pre := ((phases P20T).take 7).flatMap (·.2)) (rest := ((phases P20T).drop 7).flatMap (·.2))
    (by show schedule P20T = _; rw [schedule, ← List.flatMap_append, List.take_append_drop]) rfl
    (by decide +kernel)

/-- `stG20`'s read widths are `readWidthsP P20T`. -/
theorem readWidthsS_stG20 : readWidthsS stG20 = readWidthsP P20T := by
  unfold readWidthsS readWidthsP
  exact List.flatMap_congr fun it _ => by cases it <;> rfl

/-! ## Stage-generic lemmas -/

set_option maxRecDepth 100000 in
/-- **The plan's lengths at a stage**: `q₀`'s `7`, then the stage's (`lens_P20F` for every stage whose plan walk is
ok). -/
theorem lens_S (st : XStage) (ho : OutOK st) : Lvm.QLink.lens st.p = 7 :: lensLS st := by
  rw [Lvm.QLink.lens, show Replay.plan st.p = ⟨.q0, 7⟩ :: ⟨.fs 0, seedLenP st.p⟩ ::
      (Replay.planItems st.p Replay.w0 (schedule st.p)).1 from rfl, List.map_cons, List.map_cons,
    plan_lens st.p (schedule st.p) Replay.w0 ho.planOk, show Replay.w0.pend = 0 from rfl, lensLS,
    show blocksS st = .one .seed (seedLenP st.p) :: Lvm.X.itemBlks st.p (schedule st.p) 0 from rfl,
    List.flatMap_cons]
  simp only [Lvm.X.Blk.queries, List.map_cons, List.map_nil, List.cons_append, List.nil_append]

/-- The trace's lanes at a stage, as `lanesOf`. -/
theorem lanesOf_lensLS' (st : XStage) :
    Lvm.X.lanesOf ((blocksS st).flatMap Lvm.X.lensB) = ((lensLS st).map fun len => 5 + len / 8).sum := rfl

/-- **The trace bridge at a stage** (`trBridgeF20` for every stage with `OutOK`): the extractor's reader of the stream
lanes is `Q_link`'s `decode` at the stage's parameters. -/
theorem trBridgeS (st : XStage) (ho : OutOK st) (W : ℕ → Word) :
    readTraceLS st W = Lvm.QLink.decode st.p (Lvm.NS.wsOf W) := by
  have h8 : ∀ len ∈ lensLS st, len % 8 = 0 := fun len h ↦ by
    rw [lensLS_eq] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    exact (qryOk_qsLS st ho.blkOk q hq).1
  have hend : 6 + ((lensLS st).map fun len => 5 + len / 8).sum ≤ Lvm.NS.nLanes := by
    have h2 := ho.lanes
    rw [← lanesOf_flatMapB, lanesOf_lensLS', Lvm.X.nCp_eq] at h2
    exact h2
  rw [readTraceLS, entLS, Lvm.QLink.decode, lens_S st ho, Lvm.QLink.readEntries, Lvm.NS.entryAt_q0,
    show 1 + 40 + 7 = 8 * 6 from rfl, Lvm.NS.readEntries_walk W _ 6 h8 hend]

/-- Witness-sending proofs decode (`EXF20_W` at a stage). -/
theorem EXS_Wn (st : XStage) (hp : ProgOK st) (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof)
    (L : Log) (h : Lvm.T.isS π = false) : EXS st A c π L = RecursionFast.WitnessSending.decode π := by
  refine EXS_W st hp A c π L fun h0 ↦ ?_
  have : π.data.getD 0 0 = 0x53 := by
    rw [Array.getD_eq_getD_getElem?, h0]; rfl
  simp [Lvm.T.isS, this, Lvm.T.sByte] at h

end Lvm.XS
