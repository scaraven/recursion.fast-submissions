-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10; stage P4f): controls for the front's
-- phases 13 … 25 (`FRSoundness4P4fDF`, `FRSoundness4P4fObl`).
import FRSoundness4P4fObl
import FRSoundness4RsvCtrl

/-!
# Controls for P4f

| Definition | Positive | Negative |
|---|---|---|
| `DFhi` | `DFhi_of_far` (a far word dooms phases 14 … 25 but the `msD` ones), `DFhi13_of_far` (Lr1's last answer) | `DFhi_out` (no doom outside 13 … 25), `not_DFhi25_true` (a close word with the true claim clears B′) |
| `bg12X`, `bg16X` | `bg12X_of_nE`, `bg16X_of_bat` (a node's M rows, Lr's batch) | `bg12X_seg`, `bg16X_seg` (on a segment only `bg20X` is left) |
| `frontClsHi` | `frontClsHi_pos` (Lr2's first squeeze, Lr2's first absorb, RS1) | `frontClsHi_neg` (Lrend is no squeeze, Lr3 no absorb) |
| F1 (`final_segU`) | `eqAtR_pad_past` (past the blocks the end term is `0`) | `eqAtR_pad_in` (inside, it is the short point's) |
| `FrontHi` | `frontHi_X`, `frontObl_P4f`, `ks_rev4F` | — (X4's `FrontHi` is a `Prop` structure; its content is `T4.FrontObl`'s) |
-/

namespace FR.Snd.P4f
open RecursionFast FR.Merkle FR.Rev4 Finset FR.Impl

/-- (+) A far level-0 word dooms every phase from 14 to 25 but E1's and RS1's (`msD`). -/
theorem DFhi_of_far {L es : Log} (h : far0X L es) :
    ∀ k, 14 ≤ k → k ≤ 25 → k ≠ 17 → k ≠ 24 → DFhi k L es := by
  intro k h1 h2 h17 h24
  have b : bg20X L es := .inl h
  interval_cases k <;> first
    | exact .inl (.inl b) | exact .inl b | exact .inl (.inl (.inl b)) | exact .inl h | omega

/-- (+) After Lr1's last answer a far word dooms Lr1. -/
theorem DFhi13_of_far {L es : Log} (h : far0X L es) (hl : 169 + 9 < es.length) : DFhi 13 L es := by
  simp only [DFhi, msD, if_neg (show ¬ es.length ≤ 169 + 9 by omega)]
  exact .inl (.inl (.inl h))

/-- (−) No phase outside 13 … 25 is doomed by `DFhi` (phases 0 … 12 are P4a's in `DFX`). -/
theorem DFhi_out : DFhi 12 = (fun _ _ => False) ∧ DFhi 26 = fun _ _ => False := ⟨rfl, rfl⟩

/-- (−) B′'s doom is cleared on a close word whose claim is `⟨W₀, f⁽⁰⁾⟩`. -/
theorem not_DFhi25_true {L es : Log} (hnf : ¬ far0X L es)
    (hc : P4b.vStarL4 (kindOfC es) es = P4b.ipW (P4b.wrsL4 N4c.kf4 (kindOfC es) es)
      (P4b.cellsC X4.cellsX (kindOfC es)) (P4b.kpL4 es) ((kindOfC es).m - 7) (X4.src4.fz L es)) :
    ¬ DFhi 25 L es :=
  P4b.dB4_ctrl.2 hnf hc

/-- (+) A node's failed M rows are in `bg12X`. -/
theorem bg12X_of_nE {L es : Log} (h : P4b.nE4 X4.src4 NI4F.srcE4 L es) : bg12X L es := .inr h

/-- (+) A node's false Lr batch is in `bg16X`. -/
theorem bg16X_of_bat {L es : Log} (h : P4b.BatBadLr4 X4.src4 NI4F.srcL4 L es) : bg16X L es := .inr h

/-- (−) On a segment the node parts of the backgrounds are false. -/
theorem bg12X_seg {L es : Log} {σ : SegKind} (h : kindOfC es = .seg σ) : bg12X L es ↔ bg20X L es :=
  ⟨fun h' => h'.resolve_right (P4b.not_onNode_seg h), .inl⟩

theorem bg16X_seg {L es : Log} {σ : SegKind} (h : kindOfC es = .seg σ) : bg16X L es ↔ bg20X L es :=
  ⟨fun h' => h'.resolve_right (P4b.not_onNode_seg h), .inl⟩

/-- (+) Lr2's first squeeze (180), first round absorb (181) and RS1's squeezes are classified. -/
theorem frontClsHi_pos : frontClsHi 180 .squeeze = true ∧ frontClsHi 181 (.absorb 48) = true ∧
    frontClsHi 328 .squeeze = true := by
  unfold frontClsHi rndClsHi absPtsHi sqPtsHi rndPhHi fsRnd4
  rw [fsRanges4_eq]; decide

/-- (−) Lrend's absorb (213) is no squeeze class, Lr3's squeeze (214) no absorb class. -/
theorem frontClsHi_neg : frontClsHi 213 .squeeze = false ∧ frontClsHi 214 (.absorb 48) = false := by
  unfold frontClsHi rndClsHi absPtsHi sqPtsHi rndPhHi fsRnd4
  rw [fsRanges4_eq]; decide

/-- (+) F1: past a segment's blocks (`2^nb ≤ L`), the end term's `eq(τ ‖ 0, L)` is `0`. -/
theorem eqAtR_pad_past {nb : ℕ} (hnb : nb ≤ 18) (τs : List F) (hτ : τs.length = nb) {Lb : ℕ}
    (h1 : 2 ^ nb ≤ Lb) (h2 : Lb < 2 ^ 18) :
    eqAtR (ptOf 18 (τs ++ List.replicate (18 - nb) 0)) Lb = 0 := by
  rw [P4a.eqAtR_padN hnb τs hτ h2, if_neg (by omega)]

/-- (−) Inside the blocks it is the short point's `eq(τ, L)`, which the bound in P4a's `final_seg`
selects. -/
theorem eqAtR_pad_in {nb : ℕ} (hnb : nb ≤ 18) (τs : List F) (hτ : τs.length = nb) {Lb : ℕ}
    (h1 : Lb < 2 ^ nb) :
    eqAtR (ptOf 18 (τs ++ List.replicate (18 - nb) 0)) Lb = eqAtR (ptOf nb τs) Lb := by
  rw [P4a.eqAtR_padN hnb τs hτ (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hnb)),
    if_pos h1]

end FR.Snd.P4f
