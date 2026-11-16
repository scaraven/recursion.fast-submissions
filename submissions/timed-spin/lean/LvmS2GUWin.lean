-- New for lvm2 U-TAPE (UT-L, 2026-11-16; lead decision D-WIN (B), re-freeze of UTAPE-STMT 15a): S2GU's extractor
-- window. At S2GU the stream block `S` sits at `5·2^20` (big shape: physical lanes 40–42) and at `2·2^20` logical
-- (small shape, stride 2: physical lanes 32–36), so the level-0 decoder reads lanes `32 … 39` for a small statement
-- and `40 … 47` (M′'s window) for a big one: 8 lanes in both shapes, the same memory map and cost.
import LvmS2GUSched

/-!
# The S2GU extractor window (D-WIN (B))

* **`winOkBW lo C S s`**: `LvmMPWin.winOkB` with the window as parameters.
* **`win_U20`** (UTAPE-STMT 15a): the big shape's stream (stride 1 from `CMain.sOffU20`) is in lanes `[40, 48)`, the
  small shape's (stride 2 from `CMain.sOffU20s`) in lanes `[32, 40)`, and in both the stream starts the window (window
  word `0` is `S`'s word `0`); the layout rule's stream block at `P20U` is `CMain.sOffU20`.
-/

set_option autoImplicit false

namespace Lvm.X

open RecursionFast

/-- The words of the stream block the extractor's child reads (`LvmMPWin.streamLen`: `LvmMPWin` cannot be imported
next to `LvmXTop`, both declare `Lvm.X.laneOf`). -/
abbrev streamLenU : ℕ := recStreamCols * 2 ^ 14 + 2 ^ 10

/-- The level-0 lane of physical word `w` (`LvmMPWin.laneOf`). -/
abbrev laneOfU (w : ℕ) : ℕ := w / 2 ^ 17

/-- **The window check with the window as parameters**: at stride `s`, the stream region from logical word `S` starts
in lane `≥ lo` and ends in lane `< lo + C`. -/
def winOkBW (lo C S s : ℕ) : Bool :=
  decide (lo ≤ laneOfU (s * S)) && decide (laneOfU (s * (S + streamLenU - 1)) < lo + C)

/-- **UTAPE-STMT 15a** (owner L; D-WIN (B)): **S2GU's shapes keep the stream in their windows**: big at stride 1 from
`CMain.sOffU20` in lanes `[40, 48)`, small at stride 2 from `CMain.sOffU20s` in lanes `[32, 40)`; in both the stream's
first physical word is the window's first word; the layout rule's stream block at `P20U` is `CMain.sOffU20`. -/
theorem win_U20 : winOkBW 40 8 CMain.sOffU20 1 = true ∧ winOkBW 32 8 CMain.sOffU20s 2 = true ∧
    CMain.sOffU20 = 40 * 2 ^ 17 ∧ 2 * CMain.sOffU20s = 32 * 2 ^ 17 ∧
    (layout0 P20U).s = CMain.sOffU20 ∧ CMain.sOffU20s + 3 * 2 ^ 20 = CMain.sOffU20 := by
  decide +kernel

/-- The physical lanes the stream occupies at `P20U`: 40–42 (big), 32–36 (small). -/
theorem win_U20_lanes : laneOfU CMain.sOffU20 = 40 ∧ laneOfU (CMain.sOffU20 + streamLenU - 1) = 42 ∧
    laneOfU (2 * CMain.sOffU20s) = 32 ∧ laneOfU (2 * (CMain.sOffU20s + streamLenU - 1)) = 36 := by
  decide +kernel

end Lvm.X
