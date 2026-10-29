-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): T4's control
-- `tail_shift`, moved verbatim out of `FRSoundness4TailLig` (QUEUE 2026-10-28: approved) so that the
-- revision 4.1 certificate's closure does not import the 3.x tail (`FRSoundnessTail`) for it. It compares
-- T4's positions with 3.x's, so it lives outside the certificate's closure, with the 3.x modules.
import FRSoundness4TailLig
import FRSoundnessTail

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-- **Control (the position map)**: T4's tail positions are 3.x's plus 14 (`phStart4_shift`) at
every level: P1.i, C.i, P3.i's entry, the caps of levels 1–4 and Pf; level 0's cap (`cap₀`, in
the front) is unchanged. In particular T4's positions are not 3.x's. -/
theorem tail_shift : (∀ i < 5, p1Start i = _root_.FR.Snd.p1Start i + 14 ∧
      cStart i = _root_.FR.Snd.cStart i + 14 ∧ p3S0 i = _root_.FR.Snd.p3S0 i + 14 ∧
      capPos (i + 1) = _root_.FR.Snd.capPos (i + 1) + 14) ∧
    pfStart = _root_.FR.Snd.pfStart + 14 ∧ capPos 0 = _root_.FR.Snd.capPos 0 := by
  have h := phStart4_shift.2.2.2.2.2
  have h3 : ∀ i < 5, 1 ≤ phStart (30 + 5 * i) := fun i hi => by
    rw [show phStart (30 + 5 * i) = fsStarts.getD (30 + 5 * i) 0 from rfl, fsStarts_eq]
    interval_cases i <;> decide
  refine ⟨fun i hi => ⟨h _ (by omega) (by omega), h _ (by omega) (by omega), ?_, ?_⟩,
    h 51 (by norm_num) (by norm_num), ?_⟩
  rotate_left 2
  · show (if (0 : ℕ) = 0 then phStart4 2 else phStart4 (22 + 5 * 0)) =
      if (0 : ℕ) = 0 then phStart 2 else phStart (22 + 5 * 0)
    rw [if_pos rfl, if_pos rfl]
    exact phStart4_shift.1 2 (by norm_num)
  · show phStart4 (30 + 5 * i) - 1 = phStart (30 + 5 * i) - 1 + 14
    have := h (30 + 5 * i) (by omega) (by omega)
    have := h3 i hi
    omega
  · show (if i + 1 = 0 then phStart4 2 else phStart4 (22 + 5 * (i + 1))) =
      (if i + 1 = 0 then phStart 2 else phStart (22 + 5 * (i + 1))) + 14
    rw [if_neg (by omega), if_neg (by omega)]
    exact h _ (by omega) (by omega)

end FR.Snd.T4
