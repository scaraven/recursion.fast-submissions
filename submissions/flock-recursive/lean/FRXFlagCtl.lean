-- G6: `FRXFlag`'s controls (`FlagControls`), moved here verbatim from `FRXFlag` to keep them off `Solution`'s
-- import closure (stage G6); `FR` imports this module.
import FRXMsg

namespace FR.X

open RecursionFast FR Finset

/-! ## Controls (a kernel run on a toy memory) -/

namespace FlagControls

/-- Store the words `ws` at `256 …` (scratch registers `200`, `201`). -/
def putWords : List Word → ℕ → XIR
  | [], _ => .blk []
  | w :: ws, j => .seq (.blk [.const 200 (toWord (256 + j)), .const 201 w])
      (.seq (.store 200 201) (putWords ws (j + 1)))

/-- One row, two positions: `W[0][0] = W[0][1] = 1` at `256`, `E[0] = 1` at `260`, `X = (1, 0)`
at `264`, `Y = (0, 0)` at `268`; the flags at `272`, then output. -/
def toyFlag : XIR :=
  .seq (putWords [1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] 0)
    (.seq (flagIR 2 1 2 256 260 264 268 272)
      (.seq (.blk [.const 200 272]) (.seq (.load 201 200) (.seq (.out 201)
        (.seq (.blk [.const 200 273]) (.seq (.load 201 200) (.out 201)))))))

/-- **Positive and negative**: position `0` agrees (`1·1 = X[0]`, `1·0 = Y[0]`), position `1`
does not (`1·1 ≠ X[1] = 0`). -/
theorem toyFlag_run : (toProg 300 0 toyFlag).run [] 1400 = some [1, 0] := by
  decide +kernel

end FlagControls

end FR.X
