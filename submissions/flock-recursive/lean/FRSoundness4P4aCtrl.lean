-- New for `flock-recursive` (stage P4a): the controls of the P4a definitions.
import FRSoundness4P4aSeg
import FRSoundness4P4aLast

/-!
# Controls of P4a's definitions (positive and negative)

* **`ShHoldsSeg`**: the zero table meets it (`shHoldsSeg_zero`, +); a table whose only nonzero bits
  are block `L + 1`'s inputs meets it (`shHoldsSeg_cut`, +: the link `L → L + 1` is masked), while
  3.x's unmasked `ShHoldsL` refuses the same table (`not_shHoldsL_cut`, −); a wrong start is refused
  (`not_shHoldsSeg_start`, −).
* **`EtSeg`**: the chain target on the blocks `t ≤ L` (`etSeg_le`, +), `0` past (`etSeg_past`, −).
* **`zlm4`**: its indicators are bits and match the L3 mask (`zlm4_indKinds`, +, for any node
  parameters that have no `chain` block); a segment's indicator refuses every kind but `chain`
  (`zlm4_seg_ind`, −).
* **`lastL`**: `n − 1` on `1 ≤ n ≤ 2^18` (`lastL_eq`, +); `n = 0` wraps to `2^18 − 1`
  (`lastL_zero`, −: `V_A`'s `1 ≤ n` check is what excludes it). `lb`/`borrow`: `lastSum` at `n = 1`
  and `n = 2^18` (`lastSum_one`, `lastSum_top`).
* **The `Rej*`**: none holds before its first position (`not_rejZ_short`, `not_rejLc2_short`,
  `not_rejLcN_short`, `not_rejS2_short`, −); `RejLc2` and `RejLcN` exclude each other by kind
  (`not_rejLc2_node`, −). Their positive instances are R4's (an accepting run's checks).
-/

namespace FR.Snd.P4a
open RecursionFast Finset FR.Impl

/-! ## `ShHoldsSeg` -/

theorem shHoldsSeg_zero (nb Lb : ℕ) :
    ShHoldsSeg nb Lb (fun _ _ => 0) (fun _ => 0) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

/-- The table whose only nonzero bits are block `Lb + 1`'s inputs (slot `520 + σ`). -/
def cutTbl (Lb : ℕ) : ℕ → ℕ → F := fun y q => if y = Lb + 1 ∧ 520 ≤ q then 1 else 0

/-- (+) **The mask**: block `L + 1`'s input need not be block `L`'s output. -/
theorem shHoldsSeg_cut (nb Lb : ℕ) :
    ShHoldsSeg nb Lb (cutTbl Lb) (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun y hy hyL σ hσ => ?_, fun σ hσ => ?_, fun σ hσ => ?_, fun _ σ hσ => ?_⟩
  · simp only [cutTbl]
    rw [if_neg (by omega), if_neg (by omega)]
  · simp only [cutTbl]; rw [if_neg (by omega)]
  · simp only [cutTbl]; rw [if_neg (by omega)]
  · simp only [cutTbl]; rw [if_neg (by omega)]

/-- (−) **3.x's unmasked truth refuses it**: the link `L → L + 1` fails. -/
theorem not_shHoldsL_cut {nb Lb : ℕ} (h : Lb + 2 < 2 ^ nb) :
    ¬ ShHoldsL nb (cutTbl Lb) (fun _ => 0) (fun _ => 0) := fun hS => by
  have := hS.1 Lb (by omega) 0 (by norm_num)
  simp [cutTbl] at this

/-- (−) A wrong start is refused. -/
theorem not_shHoldsSeg_start (nb Lb : ℕ) :
    ¬ ShHoldsSeg nb Lb (fun _ _ => 0) (fun _ => 1) (fun _ => 0) := fun hS =>
  zero_ne_one (hS.2.1 0 (by norm_num))

/-! ## `EtSeg` -/

theorem etSeg_le {Lb t : ℕ} (h : t ≤ Lb) (p : Fin (2 ^ 14)) : EtSeg Lb t p = chainE p.val := by
  simp [EtSeg, h]

theorem etSeg_past {Lb t : ℕ} (h : Lb < t) (p : Fin (2 ^ 14)) : EtSeg Lb t p = 0 := by
  simp [EtSeg, show ¬ t ≤ Lb by omega]

/-! ## `zlm4` -/

theorem zlm4_indKinds {indN : Rev4.NodeKind → Fin 9 → ℕ → F}
    {etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F} (h0 : ∀ ν t, indN ν 0 t = 0) :
    (zlm4 indN etN).IndKinds := fun κ t => by
  cases κ with
  | seg κ => exact ⟨fun h => (by cases h), fun _ j hj => (by simp [zlm4, hj])⟩
  | node ν => exact ⟨fun _ => h0 ν t, fun h => (by cases h)⟩

theorem zlm4_seg_ind {indN : Rev4.NodeKind → Fin 9 → ℕ → F}
    {etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F} (κ : Rev4.SegKind) (t : ℕ) :
    (zlm4 indN etN).Ind (.seg κ) 0 t = 1 ∧ ∀ j : Fin 9, j ≠ 0 → (zlm4 indN etN).Ind (.seg κ) j t = 0 :=
  ⟨by simp [zlm4], fun j hj => by simp [zlm4, hj]⟩

/-! ## `lastL` and the borrow chain -/

theorem lastL_zero {es : Log} (h : nStmt es = 0) : lastL es = 2 ^ 18 - 1 := by
  unfold lastL; rw [h]; norm_num

theorem lastSum_one : (∑ k ∈ range 18, if lb 1 k then 2 ^ k else 0) = 0 := by
  rw [lastSum_eq le_rfl (by norm_num)]

theorem lastSum_top : (∑ k ∈ range 18, if lb (2 ^ 18) k then 2 ^ k else 0) = 2 ^ 18 - 1 := by
  rw [lastSum_eq (by norm_num) le_rfl]

/-! ## The asserted checks before their positions -/

variable {M : ZLM4} {L es : Log}

theorem not_rejZ_short (h : es.length < 68) : ¬ RejZ M L es := fun hr => by
  have := hr.1; omega

theorem not_rejLc2_short (h : es.length < 98) : ¬ RejLc2 M L es := fun hr => by
  have := hr.1; omega

theorem not_rejLcN_short (h : es.length < 98) : ¬ RejLcN M L es := fun hr => by
  have := hr.1; omega

theorem not_rejS2_short (h : es.length ≤ 114) : ¬ RejS2 L es := fun ⟨l, _, hl, _⟩ => by omega

theorem not_rejLc2_node (h : (kindOfC es).isNode = true) : ¬ RejLc2 M L es := fun hr => by
  have := hr.2.1; rw [h] at this; cases this

end FR.Snd.P4a
