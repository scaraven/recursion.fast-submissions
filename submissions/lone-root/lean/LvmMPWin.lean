-- New for lvm2 roll 11 (M′, R11-E `S2GM`): the stream window's layout check. The stream and `σ'` (every word the
-- extractor's `child` reads, `NodeSoundM`) lie in `C_main`'s level-0 lanes `winLo … winLo + winC − 1` in both of
-- `P20`'s shapes (strides 1 and 2), decided by the kernel on the shared layout (`LvmLayout`).
import LvmMPDec
import LvmDecideV0

/-!
# The stream window at `S2GM`

The child's words are the stream block's columns `0 … 16` (the `KS` message lanes) and `σ'` (column 17's first
`2^10` words): the logical words `[S, S + streamLen)` of `C_main`, `streamLen = 17·2^14 + 2^10`. A step at stride
`s` (`1`: the big shape, `n > 2^18`; `2`: the small shape, logical word `w` at physical word `2w`) puts logical word
`w` at physical word `s·w`, in level-0 lane `s·w / 2^17` (64 lanes of `2^17` words).

* `winOkB S s`: the first and the last word's lanes lie in the window (the lanes are monotone in `w`).
* **`winOk_lanes`**: then every word of the region lies in the window.
* **`win_P20`**: `P20`'s two shapes pass (`decide +kernel`): big `S = 5,767,168` (lanes 44–46), small
  `S = 2,621,440` (physical lanes 40–44); and `layout0 P20`'s stream block is `CMain.sOff20`.
-/

set_option autoImplicit false

namespace Lvm.X

/-- The words of the stream block the extractor's child reads: the 17 stream columns of `2^14` and `σ'`'s
`2^10`-word region. -/
abbrev streamLen : Nat := recStreamCols * 2 ^ 14 + 2 ^ 10

/-- The level-0 lane of physical word `w` (`C_main` at ν = 23: 64 lanes of `2^17` words). -/
abbrev laneOf (w : Nat) : Nat := w / 2 ^ 17

/-- **The window check**: at stride `s`, the stream region from logical word `S` starts in lane `≥ winLo` and ends in
lane `< winLo + winC`. -/
def winOkB (S s : Nat) : Bool :=
  decide (winLo ≤ laneOf (s * S)) && decide (laneOf (s * (S + streamLen - 1)) < winLo + winC)

/-- **Every word of the region lies in the window** when the check passes. -/
theorem winOk_lanes {S s : Nat} (h : winOkB S s = true) {i : Nat} (hi : i < streamLen) :
    winLo ≤ laneOf (s * (S + i)) ∧ laneOf (s * (S + i)) < winLo + winC := by
  simp only [winOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · exact le_trans h1 (Nat.div_le_div_right (Nat.mul_le_mul_left s (Nat.le_add_right S i)))
  · exact lt_of_le_of_lt (Nat.div_le_div_right (Nat.mul_le_mul_left s (by omega))) h2

/-- **`P20`'s shapes keep the stream in the window**: the big shape at stride 1 from `CMain.sOff20`, the small shape at
stride 2 from `CMain.sOff20s`; the layout rule's stream block is the shared one. -/
theorem win_P20 : winOkB CMain.sOff20 1 = true ∧ winOkB CMain.sOff20s 2 = true ∧
    (layout0 P20).s = CMain.sOff20 ∧ CMain.sOff20s + 3 * 2 ^ 20 = CMain.sOff20 := by
  decide +kernel

/-- The physical lanes the stream occupies at `P20`: 44–46 (big), 40–44 (small). -/
theorem win_P20_lanes : laneOf CMain.sOff20 = 44 ∧ laneOf (CMain.sOff20 + streamLen - 1) = 46 ∧
    laneOf (2 * CMain.sOff20s) = 40 ∧ laneOf (2 * (CMain.sOff20s + streamLen - 1)) = 44 := by
  decide +kernel

end Lvm.X
