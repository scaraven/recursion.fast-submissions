-- New for `flock-recursive` (BLUEPRINT §4.3, §4.5, A.6, A.7, stage S-E2; B-2's kill test).
import FRTranscriptDefs

/-!
# The node's block layout: `nodeLayout`, the kind intervals, the size checks

BLUEPRINT §4.3's region table and A.6/A.7 (revision 3.5). Blocks of `2^14` positions; the node has
`2^16` (`m = 30`).

* **H** (from block 0): digest chain 1 `[0, 22,472)` and chain 2 `[22,472, 44,944)` (`streamStart`
  first, `stream` after), `hashStmt` (`hashA`, `hashB1`, `hashB2` per slot), WOTS per slot laid
  out consecutively (§4.2: the 399 `w43` chain steps, the key leaf `hashB1` + 65 `stream` +
  `streamEnd41`, the 16 path steps `hashB1`, `hashB2`), the mirror sub-region `WM` (10 blocks per
  slot, no kind), 8 spare;
* **L** at block 46,336, 124 used; **M** at `3 · 2^14 = 49,152`, `N_M = 2^21` elements (16,384
  blocks) to the end, slot `σ`'s rows at `Mbase + (σ − 1) · 2^20`.

`nodeLayout` lists the kind intervals in address order; `Ind κ` (A.6's `Ind_kind`) and `Sel` are
read off it. **The checks (B-2's kill test) are closed-form**: `nodeLayout_chained` (the intervals
are nonempty and in order, a check of 82 interval endpoints), `nodeLayout_end` (they end at `WM`),
`regions_fit` (H, L, M disjoint and inside `2^16`), `usedBlocks_le`, and `mRows_le` over the row
model of §4.3 (deviation D-2 of the RESULT: the blueprint's `decide` over the compiled program is
replaced by the closed-form row model; the link `rows (compileMux (gen fin)) = mRowModel` waits
for `gen fin`).
-/

namespace FR
namespace Layout

/-! ## Constants (§4.3, A.7) -/

/-- Compressions of one digest chain (§4.2, revision 3.7: the Lr-end and E-end absorbs). -/
def chainN : ℕ := 22472
/-- `hashStmt`'s blocks: 3 per slot. -/
def stmtBase : ℕ := 2 * chainN
/-- WOTS: 133 chains × 3 steps, the key leaf's 67 blocks, the path's 16 × 2 per slot. -/
def wotsBase : ℕ := stmtBase + 6
def wotsSlot : ℕ := 133 * 3 + 67 + 2 * 16
/-- The mirror sub-region `WM` (10 blocks per slot). -/
def wmBase : ℕ := wotsBase + 2 * wotsSlot
def wmSlot : ℕ := 10
/-- The end of region H (after 8 spare blocks). -/
def hEnd : ℕ := wmBase + 2 * wmSlot + 8
/-- Region L: base and used blocks. -/
def lBase : ℕ := 46336
def lUsed : ℕ := 124
/-- Region M: base, elements, blocks, per-slot elements. -/
def mBase : ℕ := 3 * 2 ^ 14
def nM : ℕ := 2 ^ 21
def mBlocks : ℕ := nM / 128
def slotM : ℕ := 2 ^ 20
/-- **M's `one` cell** (revision 3.6, S-E2 F-4): element `Mbase · 128` of `f`, pinned to `1` by a
point claim (`PubCells`); the compiler's `Params.one` is this cell. -/
def oneCell : ℕ := mBase * 128
/-- The node's blocks (`2^(30 − 14)`). -/
def nodeBlocks : ℕ := 2 ^ 16

/-! ## The kind intervals -/

/-- Blocks `[lo, hi)` of one kind. -/
structure Iv where
  kind : BlockKind
  lo : ℕ
  hi : ℕ

/-- Slot `σ`'s digest chain. -/
def chainIvs (σ : ℕ) : List Iv :=
  [⟨.streamStart, σ * chainN, σ * chainN + 1⟩, ⟨.stream, σ * chainN + 1, (σ + 1) * chainN⟩]

/-- `hashStmt`'s blocks A, B1, B2 of both slots. -/
def stmtIvs : List Iv :=
  (List.range 2).flatMap fun σ =>
    let b := stmtBase + 3 * σ
    [⟨.hashA, b, b + 1⟩, ⟨.hashB1, b + 1, b + 2⟩, ⟨.hashB2, b + 2, b + 3⟩]

/-- Slot `σ`'s WOTS blocks, consecutive (§4.2): chain steps, key leaf, path steps. -/
def wotsIvs (σ : ℕ) : List Iv :=
  let b := wotsBase + wotsSlot * σ
  [⟨.w43, b, b + 399⟩, ⟨.hashB1, b + 399, b + 400⟩, ⟨.stream, b + 400, b + 465⟩,
    ⟨.streamEnd41, b + 465, b + 466⟩] ++
  (List.range 16).flatMap fun t =>
    [⟨.hashB1, b + 466 + 2 * t, b + 467 + 2 * t⟩, ⟨.hashB2, b + 467 + 2 * t, b + 468 + 2 * t⟩]

/-- **`nodeLayout`**: the node's kind intervals in address order. -/
def nodeLayout : List Iv := chainIvs 0 ++ chainIvs 1 ++ stmtIvs ++ wotsIvs 0 ++ wotsIvs 1

/-- **`Ind_kind`** (A.6): block `blk` is of kind `κ`. -/
def Ind (κ : BlockKind) (blk : ℕ) : Bool :=
  nodeLayout.any fun iv => iv.kind == κ && iv.lo ≤ blk && blk < iv.hi

/-- **`Sel`** (§4): block `blk` is in some kind's interval. -/
def Sel (blk : ℕ) : Bool := nodeLayout.any fun iv => iv.lo ≤ blk && blk < iv.hi

/-- The intervals of a kind (`kindInd`'s prefix sums run over them). -/
def kindIvs (κ : BlockKind) : List (ℕ × ℕ) :=
  (nodeLayout.filter fun iv => iv.kind == κ).map fun iv => (iv.lo, iv.hi)

/-- Nonempty and in increasing order, without overlap. -/
def chained : List Iv → Bool
  | a :: b :: t => decide (a.lo < a.hi) && decide (a.hi ≤ b.lo) && chained (b :: t)
  | [a] => decide (a.lo < a.hi)
  | [] => true

/-! ## The checks (B-2's kill test, closed form) -/

theorem nodeLayout_length : nodeLayout.length = 82 := by decide

/-- **The intervals are disjoint and in order** (so `Ind` partitions `Sel`). -/
theorem nodeLayout_chained : chained nodeLayout = true := by decide

/-- They start at block 0 and end where `WM` starts. -/
theorem nodeLayout_end : (nodeLayout.head?.map Iv.lo, nodeLayout.getLast?.map Iv.hi) =
    (some 0, some wmBase) := by decide

/-- **The regions fit**: H ends before L, L's used blocks before M, M ends at `2^16`. -/
theorem regions_fit : hEnd ≤ lBase ∧ lBase + lUsed ≤ mBase ∧ mBase + mBlocks = nodeBlocks ∧
    hEnd = 45974 := by
  simp only [hEnd, wmBase, wmSlot, wotsBase, wotsSlot, stmtBase, chainN, lBase, lUsed, mBase,
    mBlocks, nM, nodeBlocks]; norm_num

/-! ## The M rows (§4.3's row model, per slot) -/

/-- §4.3's row count per slot, by category (revision 3.5's table). -/
def mRowModel : List ℕ :=
  [74461,             -- imports (revision 3.7)
   54841,             -- folds
   2 * 2 ^ 7 * 126,   -- final Enc₄
   4 * 7552,          -- Merkle steps
   400,               -- Z2 Lagrange
   15000,             -- eq/tensor
   5 * 25 * 128,      -- MBP (J_z = 5)
   2000,              -- sumchecks
   65536 + 16384,     -- lincheck replay, per-kind adjustment
   2 * 74461 + 2 * chainN + 2 ^ 14, -- evalM replay
   8192,              -- evalL replay
   2 * 431 + 2 * 871 + 600, -- gated asserts
   2600,              -- mirror-cell mux
   266,               -- selector–digit rows
   8,                 -- gated stmt equalities
   4]                 -- selector and kind rows

theorem mRowModel_sum : mRowModel.sum = 531610 := by decide

/-- **The M rows fit**: a slot's rows in its `2^20` half of M, the node's in `N_M` (margin
`2^20 / 531,610 ≈ 1.97`; §4.3 revision 3.7 states 531,618, its listed numbers sum to 531,610: F-3″). -/
theorem mRows_le : mRowModel.sum ≤ slotM ∧ 2 * mRowModel.sum ≤ nM := by
  rw [mRowModel_sum]; simp only [slotM, nM]; norm_num

/-- **The used blocks fit** in `2^16` (H, L and the M rows of both slots, 128 per block). -/
theorem usedBlocks_le : hEnd + lUsed + (2 * mRowModel.sum + 127) / 128 ≤ nodeBlocks := by
  rw [mRowModel_sum, regions_fit.2.2.2]; simp only [lUsed, nodeBlocks]; norm_num

/-! ## Controls -/

/-- Positive: block 0 is `streamStart`, block 1 `stream`, the first `w43` block is `w43`. -/
theorem ind_controls : Ind .streamStart 0 = true ∧ Ind .stream 1 = true ∧
    Ind .w43 wotsBase = true ∧ Sel (wmBase - 1) = true := by decide

/-- Negative: block 0 is not `stream`, `WM`'s first block has no kind, nor has region L. -/
theorem ind_controls_neg : Ind .stream 0 = false ∧ Sel wmBase = false ∧ Sel lBase = false := by
  decide

/-- Negative: a layout with an overlap fails the order check. -/
theorem chained_neg : chained [⟨.w43, 0, 2⟩, ⟨.hashA, 1, 3⟩] = false := by decide

end Layout
end FR
