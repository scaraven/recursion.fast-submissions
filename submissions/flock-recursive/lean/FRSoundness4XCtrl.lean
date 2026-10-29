-- New for `flock-recursive` (stage X4): positive and negative controls for the composed front, the
-- run facts and the per-kind laws.
import FRSoundness4XFinal

/-!
# Controls for X4

| Definition | Positive | Negative |
|---|---|---|
| `BgA4` | `bgA4_cover` (a node's failed rest), `bgA4_of_far` | `bgA4_seg` (on a segment only level 0's distance is left) |
| `RejFX` | `rejFX_of_rejS2` | `rejF4b_seg` (on a segment only RS0's slice check is left), `not_rejFX_short` |
| `DFX` | `DFX_lo`, `DFX_hi` | `not_DFX_out` (phases 0, 1 are never doomed) |
| `GoodX` | `goodX_nil` | — (`muT` below 1 is T4's) |
| `SegLog`/`NodeLog` | `segSound_X`, `nodeRun_X` | `not_segLog_node`, `not_nodeLog_seg` |
| `RunFacts4` | `runFacts4_false` (programs that never accept) | — (`AcceptTail.len` needs 482 entries) |
-/

namespace FR.Snd.X4
open RecursionFast FR.Rev4

/-- (+) Level 0 far is in the background. -/
theorem bgA4_of_far {L es : Log} (h : T4.farL (kindOfC es) L es 0) : BgA4 L es := .inl h

/-- (−) On a segment the background is only level 0's distance: no public cell, L row or M row. -/
theorem bgA4_seg {L es : Log} {σ : SegKind} (hk : kindOfC es = .seg σ) :
    BgA4 L es ↔ T4.farL (kindOfC es) L es 0 := by
  refine ⟨fun h => ?_, .inl⟩
  rcases h with h | h | h | h
  · exact h
  · exact absurd (fun ν hν => by rw [hk] at hν; cases hν) h
  · exact absurd h (P4b.not_onNode_seg hk)
  · exact absurd h (P4b.not_onNode_seg hk)

/-- (+) S2's failed round is a front check. -/
theorem rejFX_of_rejS2 {L es : Log} (h : P4a.RejS2 L es) : RejFX L es :=
  .inl (P4a.rejF4a_of_rejS2 h)

/-- (−) On a segment, P4b's checks reduce to RS0's slice check (the Lr/E checks are the node's). -/
theorem rejF4b_seg {L es : Log} {σ : SegKind} (hk : kindOfC es = .seg σ) :
    RejF4b L es ↔ P4b.RejRS4 okX L es := by
  refine ⟨fun h => ?_, fun h => .inr (.inr (.inr (.inr h)))⟩
  rcases h with h | h | h | h | h
  · exact absurd h (P4b.not_onNode_seg hk)
  · exact absurd h (P4b.not_onNode_seg hk)
  · exact absurd h (P4b.not_onNode_seg hk)
  · exact absurd h (P4b.not_onNode_seg hk)
  · exact h

/-- (−) No front check fails before 68 entries on a segment. -/
theorem not_rejFX_short {L es : Log} {σ : SegKind} (hk : kindOfC es = .seg σ) (hl : es.length < 68) :
    ¬ RejFX L es := by
  rintro (h | h)
  · exact P4a.not_rejF4a_short hl h
  · exact absurd ((rejF4b_seg hk).mp h).1 (by omega)

/-- (−) Phases 0 and 1 are never doomed. -/
theorem not_DFX_out {DFhi : ℕ → Log → Log → Prop} {L es : Log} {k : ℕ} (hk : k < 2) :
    ¬ DFX DFhi k L es := by
  rw [DFX_lo (by omega)]; exact P4a.not_DF4a_out (.inl hk)

/-- (+) The empty log is good. -/
theorem goodX_nil {DFhi : ℕ → Log → Log → Prop} (hH : FrontHi DFhi) : GoodX DFhi [] :=
  ⟨by simp, by rw [(T4.muT_laws_of_front (frontObl_X hH)).1]; norm_num⟩

/-- (−) A node's chain is no segment's statement. -/
theorem not_segLog_node {v : SegView} {es : Log} {κ : NodeKind} (hk : kindOfC es = .node κ) :
    ¬ SegLog v es := fun h => by have := h.1; rw [hk] at this; cases this

/-- (−) A segment's chain is no node's statement. -/
theorem not_nodeLog_seg {κ : NodeKind} {vk c : Digest} {π : Proof} {es : Log} {σ : SegKind}
    (hk : kindOfC es = .seg σ) : ¬ NodeLog κ vk c π es := fun h => by
  have := h.1; rw [hk] at this; cases this

/-- (+) Programs that never accept meet the run facts. -/
theorem runFacts4_false (vk : Digest) :
    RunFacts4 (fun _ _ _ _ => .ret false) (fun _ _ _ _ => .ret false) vk :=
  ⟨fun _ _ _ _ _ h => by simp [OProg.runLog] at h, fun _ _ _ _ _ _ h => by simp [OProg.runLog] at h⟩

end FR.Snd.X4
