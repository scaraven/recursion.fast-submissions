-- New for lvm2 (T-Q): v1's ring-switch gadget (`ringG`, HAR-RC's, from `LvmQAsmArith2Ring`) and
-- its cell spec, moved below the assembly modules so that the S2 wire gadget (`LvmQWire`) can use
-- it without the v1 phase cut. Unchanged text; `vs` moved here from `LvmQAsmHarBase`.
import LvmQSumcheckCore
import LvmQRing
import LvmQWhirBase

-- (GOLF2: 24 declarations that `certified` does not use moved verbatim to `LvmQAsmArith2Off`, outside its import closure.)

-- ===== merged from `LvmQRingTarget` (GOLF module merge: `LvmQRingTarget.lean` is now a stub importing `LvmQRingG`) =====
section
-- New for lvm (WP-11b-QA2, helper H1); `polyEval_sum` adapted from our `LvmPolyLE.polyEval_eq_sum`
-- (leanVM formal `EndToEnd/Complete/Sumcheck.lean` rev 40f877dc), restated on `Lvm.FE`.

/-!
# QA2 ring switching, part 2: the target `Σ_i g^i Φ(s_i)`

`F`'s target (`LvmDecideKeccak.ringSwitch`): `polyEval (s.map (phiMap · ch)) gen` over the 64
slices `s_i` (stream scalars) and the six challenges. Gadget `ringTargetG lb ch z`:

* `loadL [6]`: the slices from the `K` lanes `lb + 3i + (0, 1, 2)` (64 `loadE` rows);
* `phiStages`: `Φ` stage by stage over all 64 slices at once (`phiStage b f`, shift `2^b`, challenge
  cell `f`): squarings dims `[6, b]` (slice fastest; the step-`j` row reads step `j − 1`, 64 cells
  back, and step 0 the 64 stage inputs just before the block), then `v' = v + f·v^(2^(2^b))`
  (dims `[6]`); `64·2^b + 64` rows per stage, 4416 in all;
* Horner in natural order: `acc_x = Φ_x + g⁻¹·acc_{x−1}` (`lin`, `acc_{−1}` a copy of the zero
  cell), and `target = g^63·acc_63` (one `lin`). 66 rows.

`ringTarget_eq`: **the target cell is `F`'s `polyEval (s.map (phiMap · ch)) gen`**.
-/

set_option autoImplicit false

namespace Lvm.Loop.QRing

open Lvm Lvm.Loop Lvm.Loop.Build

variable {c : Ctx} {M : Mem}

/-! ## `F`'s side -/

-- adapted from LvmPolyLE.polyEval_eq_sum (leanVM formal Complete/Sumcheck.lean), on Lvm.FE
/-! ## One stage of `Φ` -/

/-- Stage with shift `2^b` and challenge cell `f`: the stage inputs `V_x` are the 64 cells before
the pointer; squarings `(x, j) ↦ V_x^(2^(j+1))` (dims `[6, b]`), then `V_x + f·V_x^(2^(2^b))`. -/
def phiStage (b f z : Nat) : BM Unit := do
  let p ← getPtr
  let _ ← madL [6, b] (eA (p.e - 64) [1, 64]) (eA (p.e - 64) [1, 64]) (eA z [])
  let _ ← madL [6] (eA f []) (eA (p.e + 64 * (2 ^ b - 1)) [1]) (eA (p.e - 64) [1])
  pure ()

/-! ## All stages -/

/-- The stages `(b, f)` in order. -/
def phiStages (z : Nat) : List (Nat × Nat) → BM Unit
  | [] => pure ()
  | (b, f) :: rest => do
    phiStage b f z
    phiStages z rest

/-- The stages of `F`'s `Φ`: shift `32` with challenge cell `ch`, …, shift `1` with `ch + 5`. -/
def phiList (ch : Nat) : List (Nat × Nat) :=
  [(5, ch), (4, ch + 1), (3, ch + 2), (2, ch + 3), (1, ch + 4), (0, ch + 5)]

/-! ## The target -/

/-- **The ring-switching target** from the slices in the `K` lanes `lb + 3i + (0, 1, 2)`
(`i < 64`), the challenges in the `E` cells `ch + i` and a zero `E` cell `z`; its cell is returned. -/
def ringTargetG (lb ch z : Nat) : BM Nat := do
  let _ ← loadL [6] ⟨.K, lb, [3]⟩ ⟨.K, lb + 1, [3]⟩ ⟨.K, lb + 2, [3]⟩
  phiStages z (phiList ch)
  let p ← getPtr
  let q ← copy (ec z)
  let _ ← linL [6] (FK.x)⁻¹ 0 (eA (p.e - 64) [1]) (eA q.n [1])
  let t ← lin .E (Build.gpow 63) 0 (ec z) (ec (q.n + 64))
  pure t.n

end Lvm.Loop.QRing
end
-- ===== end of `LvmQRingTarget` =====

/-!
# The ring-switch gadget (`ringG`)

* `loadAt qs`: one `loadE` row per stream lane `q`; `loadAt_e`, `loadAt_vs`: the cells are
  `feAt Σ (8 q)`.
* **`ringG q lb z`**: the six challenges from lanes `q + 9 i`, QA2's `coeffs` and `ringTargetG`
  over the slices at lanes `lb + 3 k`; outputs `RingOut` = the 64 coefficient cells and the target.
* **`ringG_spec`**: the coefficients are `ringCoefficients (chsAt Σ q)`, the target is
  `polyEval ((slAt Σ lb).map (phiMap · chs)) gen`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 DM

/-- The values of a list of cells. -/
def vs (M : Mem) (l : List Cell) : List FE := l.map (Cell.val M)

/-! ## Loading stream scalars -/

/-- One `loadE` row per lane `q`: the stream's `E` scalar at lanes `q, q + 1, q + 2`. -/
def loadAt : List Nat → BM (List Cell)
  | [] => pure []
  | q :: qs => do
    let c ← loadE (kc q) (kc (q + 1)) (kc (q + 2))
    let cs ← loadAt qs
    pure (c :: cs)

variable {c : Ctx} {M : Mem}

/-! ## The ring-switch gadget -/

/-- The lanes of a ring switch's six challenges (`sampleE` answers from the reader at `8 q − 40`). -/
def ringLanes (q : Nat) : List Nat := (List.range ringStages).map fun i => q + 9 * i

/-- A ring switch's output cells. -/
structure RingOut where
  /-- The 64 Frobenius coefficients `c_k` (`ringCoefficients`). -/
  cs : List Cell
  /-- The target `Σ_i g^i Φ(s_i)`. -/
  target : Cell

/-- **A ring switch**: the challenges from lanes `q + 9 i`, the slices from lanes `lb + 3 k`, `z` an
`E` zero cell. -/
def ringG (q lb z : Nat) : BM RingOut := do
  let p ← getPtr
  let _ ← loadAt (ringLanes q)
  let cb ← coeffs p.e z
  let t ← ringTargetG lb p.e z
  pure ⟨(List.range kBits).map fun k => ec (cb + k), ec t⟩

end Lvm.Har
