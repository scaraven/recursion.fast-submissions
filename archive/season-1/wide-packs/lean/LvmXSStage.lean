-- Moved out of `LvmS2GTXS` (lvm2 U-TAPE, UT-L, 2026-11-16; text unchanged): the extractor's stage-generic lemmas,
-- so that a stage's certificate need not import another stage's decisions.
import LvmXSComputes
import LvmXSExtRun
import LvmXSChild
import LvmNodeSoundTr
import LvmCertM20

/-!
# The extractor at any stage

* **`lens_S`**: the plan's lengths at a stage whose plan walk is ok; **`trBridgeS`**: the extractor's trace reader is
  `Q_link`'s `decode` at any stage with `OutOK`; **`EXS_Wn`**: witness-sending proofs decode.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

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
