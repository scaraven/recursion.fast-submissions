-- G6: `FRXAgree`'s controls (`AgreeControls`), moved here verbatim from `FRXAgree` to keep them off `Solution`'s
-- import closure (stage G6); `FR` imports this module.
import FRXAgree

namespace FR.X

open RecursionFast

/-! ## Controls (kernel runs on a toy memory) -/

namespace AgreeControls

/-- Store the flags `fs` at `256 …` (scratch registers `200`, `201`). -/
def putFlags : List Word → ℕ → XIR
  | [], _ => .blk []
  | f :: fs, j => .seq (.blk [.const 200 (toWord (256 + j)), .const 201 f])
      (.seq (.store 200 201) (putFlags fs (j + 1)))

/-- Output the count, then `m` list cells from `270`. -/
def outList : ℕ → XIR
  | 0 => .out rCn
  | m + 1 => .seq (outList m) (.seq (.blk [.const 200 (toWord (270 + m))])
      (.seq (.load 201 200) (.out 201)))

/-- The flags `0, 5, 0, 7, 7, 0, 1, 0` (`A = {1, 3, 4, 6}`), the scan for `k`, the output. -/
def toyScan (k m : ℕ) : XIR :=
  .seq (putFlags [0, 5, 0, 7, 7, 0, 1, 0] 0) (.seq (scanIR 8 k 256 270) (outList m))

/-- **Positive**: the first two flagged positions are `1, 3` (`firstK 8 A 2`). -/
theorem toyScan_two : (toProg 280 0 (toyScan 2 2)).run [] 1500 = some [2, 1, 3] := by
  decide +kernel

/-- **Limit**: asking for six lists all four (`min(|A|, k)`); the cells past the count stay `0`. -/
theorem toyScan_six : (toProg 280 0 (toyScan 6 6)).run [] 1500 = some [4, 1, 3, 4, 6, 0, 0] := by
  decide +kernel

end AgreeControls

end FR.X
