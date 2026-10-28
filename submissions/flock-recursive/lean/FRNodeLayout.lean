-- New for `flock-recursive` (BLUEPRINT §4.3, §4.5, A.6, A.7, stage S-E2; B-2's kill test).
import FRVIRMux
import FRVIRFinals

/-!
# The node's block layout: `nodeLayout`, the kind intervals, the size checks

BLUEPRINT §4.3's region table and A.6/A.7 (revision 3.5). Blocks of `2^14` positions; the node has
`2^16` (`m = 30`).

* **H** (from block 0): digest chain 1 `[0, 23,146)` and chain 2 `[23,146, 46,292)` (`streamStart`
  first, `stream` after), `hashStmt` (`hashA`, `hashB1`, `hashB2` per slot), WOTS per slot laid
  out consecutively (§4.2: the 399 `w43` chain steps, the key leaf `hashB1` + 65 `stream` +
  `streamEnd41`, the 16 path steps `hashB1`, `hashB2`), the mirror sub-region `WM` (146 blocks per
  slot after both WOTS runs, kind `free`; revision 3.14, A.6's pinned map: `mirBlock`, `mirPos`), 8
  spare;
* **L** at block 47,616 (revision 3.12: H grew by `2 × 760` blocks; the first multiple of 256
  after H, as 46,336 was), 124 used; **M** at `3 · 2^14 = 49,152`, `N_M = 2^21` elements (16,384
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

/-- Compressions of one digest chain (§4.2, revision 3.13: `chainLen_eq`; 23,225 under 3.12). -/
def chainN : ℕ := 23146
/-- `hashStmt`'s blocks: 3 per slot. -/
def stmtBase : ℕ := 2 * chainN
/-- WOTS: 133 chains × 3 steps, the key leaf's 67 blocks, the path's 16 × 2 per slot. -/
def wotsBase : ℕ := stmtBase + 6
def wotsSlot : ℕ := 133 * 3 + 67 + 2 * 16
/-- The mirror sub-region `WM` (revision 3.14, A.6: 146 blocks per slot, after both WOTS runs). -/
def wmBase : ℕ := wotsBase + 2 * wotsSlot
def wmSlot : ℕ := 146
/-- The end of region H (after 8 spare blocks). -/
def hEnd : ℕ := wmBase + 2 * wmSlot + 8
/-- Region L: base and used blocks (revision 3.12: moved from 46,336 past H's end, 47,480 then;
47,322 under revision 3.13, the base kept: stage-review changes 19). -/
def lBase : ℕ := 47616
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

/-- **`nodeLayout`**: the node's kind intervals in address order; `WM`, the spares, L and M have
the kind `free` (`A₀ = B₀ = I`, revision 3.8.1), so `Sel ≡ 1`. -/
def nodeLayout : List Iv :=
  chainIvs 0 ++ chainIvs 1 ++ stmtIvs ++ wotsIvs 0 ++ wotsIvs 1 ++ [⟨.free, wmBase, nodeBlocks⟩]

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

/-! ## The WOTS block order (exported for S-G's `nodeKind`, S-G1h) -/

/-- **The kind of WOTS block `off` of a slot** (`off < wotsSlot = 498`), as `wotsIvs` lays them out:
chain `i`'s step `s` at `3 i + s` (`off < 399`, kind `w43`); the key leaf at `399 … 465`
(`hashB1` at 399, 65 `stream` blocks at 400–464, `streamEnd41` at 465); path step `t` at
`466 + 2 t` (`hashB1`) and `467 + 2 t` (`hashB2`). -/
def wotsKindAt (off : ℕ) : BlockKind :=
  if off < 399 then .w43
  else if off = 399 then .hashB1
  else if off < 465 then .stream
  else if off = 465 then .streamEnd41
  else if (off - 466) % 2 = 0 then .hashB1 else .hashB2

/-- The block of chain `i`'s step `s` (`i < 133`, `s < 3`) of slot `σ`. -/
def wotsStepBlock (σ i s : ℕ) : ℕ := wotsBase + wotsSlot * σ + 3 * i + s
/-- Block `j` (`j < 67`) of slot `σ`'s key leaf. -/
def wotsLeafBlock (σ j : ℕ) : ℕ := wotsBase + wotsSlot * σ + 399 + j
/-- Path step `t`'s block `h` (`t < 16`, `h < 2`: `hashB1`, `hashB2`) of slot `σ`. -/
def wotsPathBlock (σ t h : ℕ) : ℕ := wotsBase + wotsSlot * σ + 466 + 2 * t + h

theorem ind_of_mem {iv : Iv} (h : iv ∈ nodeLayout) {blk : ℕ} (h1 : iv.lo ≤ blk) (h2 : blk < iv.hi) :
    Ind iv.kind blk = true := by
  unfold Ind
  exact List.any_eq_true.2 ⟨iv, h, by simp [h1, h2]⟩

theorem wotsIvs_mem {σ : ℕ} (hσ : σ < 2) {iv : Iv} (h : iv ∈ wotsIvs σ) : iv ∈ nodeLayout := by
  unfold nodeLayout
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> simp [h]

/-- **The order is `nodeLayout`'s**: WOTS block `off` of slot `σ` has kind `wotsKindAt off`. -/
theorem ind_wots {σ off : ℕ} (hσ : σ < 2) (ho : off < wotsSlot) :
    Ind (wotsKindAt off) (wotsBase + wotsSlot * σ + off) = true := by
  have hw : wotsSlot = 498 := rfl
  set b := wotsBase + wotsSlot * σ
  unfold wotsKindAt
  by_cases h1 : off < 399
  · simp only [h1, if_true]
    exact ind_of_mem (iv := ⟨.w43, b, b + 399⟩) (wotsIvs_mem hσ (by simp [wotsIvs, b])) (by simp)
      (by simp; omega)
  by_cases h2 : off = 399
  · subst h2
    exact ind_of_mem (iv := ⟨.hashB1, b + 399, b + 400⟩) (wotsIvs_mem hσ (by simp [wotsIvs, b]))
      (by simp) (by simp)
  by_cases h3 : off < 465
  · simp only [h1, h2, h3, if_true, if_false]
    exact ind_of_mem (iv := ⟨.stream, b + 400, b + 465⟩) (wotsIvs_mem hσ (by simp [wotsIvs, b]))
      (by simp; omega) (by simp; omega)
  by_cases h4 : off = 465
  · subst h4
    exact ind_of_mem (iv := ⟨.streamEnd41, b + 465, b + 466⟩)
      (wotsIvs_mem hσ (by simp [wotsIvs, b])) (by simp) (by simp)
  obtain ⟨t, ht, hh⟩ : ∃ t, t < 16 ∧ (off = 466 + 2 * t ∨ off = 467 + 2 * t) := by
    refine ⟨(off - 466) / 2, by omega, by omega⟩
  have hmem : ∀ iv ∈ [(⟨.hashB1, b + 466 + 2 * t, b + 467 + 2 * t⟩ : Iv),
      ⟨.hashB2, b + 467 + 2 * t, b + 468 + 2 * t⟩], iv ∈ nodeLayout := fun iv hiv =>
    wotsIvs_mem hσ (by
      simp only [wotsIvs, List.mem_append, List.mem_flatMap, List.mem_range]
      exact .inr ⟨t, ht, hiv⟩)
  rcases hh with rfl | rfl
  · simp only [h1, h2, h3, h4, if_false, show (466 + 2 * t - 466) % 2 = 0 by omega, if_true]
    exact ind_of_mem (iv := ⟨.hashB1, b + 466 + 2 * t, b + 467 + 2 * t⟩) (hmem _ (by simp))
      (by simp only; omega) (by simp only; omega)
  · simp only [h1, h2, h3, h4, if_false, show ¬ (467 + 2 * t - 466) % 2 = 0 by omega]
    exact ind_of_mem (iv := ⟨.hashB2, b + 467 + 2 * t, b + 468 + 2 * t⟩) (hmem _ (by simp))
      (by simp only; omega) (by simp only; omega)

/-! ## The mirror map (A.6, revision 3.14: S-CN D-2/D-3, the `WM` ruling) -/

/-- **Slot `σ`'s first `WM` block** (`wmB σ = wmBase + 146 σ`). -/
def wmB (σ : ℕ) : ℕ := wmBase + wmSlot * σ

/-- **The first mirror source of family `f`** (A.6's `off_f`; families in A.8's order `x`, `j`,
`end9`, `end41lo`, `end41hi`, `l`, `r0`, `r31`; `end41lo` and `end41hi` share their sources, `j`
has one source). -/
def mirOff : ℕ → ℕ
  | 0 => 0 | 1 => 399 | 2 => 400 | 3 => 467 | 4 => 467 | 5 => 533 | 6 => 549 | 7 => 565 | _ => 0

/-- The number of mirror sources of family `f` (`j`'s 400 links share one source). -/
def mirN : ℕ → ℕ
  | 0 => 399 | 1 => 1 | 2 => 67 | 3 => 66 | 4 => 66 | 5 => 16 | 6 => 16 | 7 => 16 | _ => 0

/-- Mirror sources per slot: `0 … 580` (581 of the 584 positions of 146 blocks). -/
def mirSources : ℕ := 581

/-- **Mirror source `g`'s block** in slot `σ`: four sources per block. -/
def mirBlock (σ g : ℕ) : ℕ := wmB σ + g / 4

/-- **The position of bit `s` (`s < 256`) of mirror source `g`** in its block: elements
`2 (g mod 4)`, `+1` (positions `< 1024`, the only ones the Sh collapse reaches). -/
def mirPos (g s : ℕ) : ℕ := 256 * (g % 4) + s

/-- The bit of `z` holding bit `s` of slot `σ`'s mirror source `g` (A.6: block-major, `2^14` bits
per block). -/
def mirBit (σ g s : ℕ) : ℕ := mirBlock σ g * 2 ^ 14 + mirPos g s

/-- The `F` element of `f` (A.7's pack) holding half `k` (`k < 2`) of mirror source `g`. -/
def mirElem (σ g k : ℕ) : ℕ := mirBlock σ g * 128 + 2 * (g % 4) + k

theorem mirElem_bit (σ g s : ℕ) (hs : s < 256) :
    mirBit σ g s / 128 = mirElem σ g (s / 128) := by
  unfold mirBit mirElem mirPos
  have h4 := Nat.mod_lt g (show 0 < 4 by norm_num)
  omega

/-- **Every family's mirror sources are below `mirSources`**, and the sources of distinct
families are disjoint except `end41lo`/`end41hi`, which share theirs. -/
theorem mir_sources (f : ℕ) (hf : f < 8) : mirOff f + mirN f ≤ mirSources := by
  interval_cases f <;> decide

theorem mir_disjoint : ∀ f < 7, mirOff f + mirN f ≤ mirOff (f + 1) ∨ (f = 3 ∧
    mirOff 3 = mirOff 4 ∧ mirN 3 = mirN 4) := by decide

/-- **The `WM` blocks fit**: slot `σ`'s mirrors lie in its 146 blocks, which end before `hEnd`,
past both WOTS runs and before L. -/
theorem mir_fits {σ g : ℕ} (hσ : σ < 2) (hg : g < mirSources) :
    wotsBase + 2 * wotsSlot ≤ mirBlock σ g ∧ mirBlock σ g < wmB σ + wmSlot ∧
      mirBlock σ g < hEnd ∧ hEnd ≤ lBase := by
  simp only [mirBlock, wmB, hEnd, wmBase, wmSlot, mirSources, lBase, wotsBase, wotsSlot, stmtBase,
    chainN] at hg ⊢
  omega

theorem mirPos_lt {g s : ℕ} (hs : s < 256) : mirPos g s < 1024 := by
  unfold mirPos; have := Nat.mod_lt g (show 0 < 4 by norm_num); omega

/-- Positive: the first and last sources' blocks (`47,294` and `47,585` for slot 2). -/
theorem mir_controls : mirBlock 0 0 = 47294 ∧ mirBlock 1 580 = 47585 ∧ mirPos 7 3 = 771 ∧
    mirElem 0 5 1 = 47295 * 128 + 3 := by decide

/-- Negative: the 3.13 map's element `2 (off_f + t) + p` put source 400 (`end9`'s first) at
element 800, past the slot coordinates; the pinned map puts it at element `0` of block `+100`. -/
theorem mir_control_neg : mirElem 0 400 0 ≠ wmB 0 * 128 + 2 * 400 ∧ mirElem 0 400 0 = (wmB 0 + 100) * 128 := by
  decide

/-! ## The checks (B-2's kill test, closed form) -/

theorem nodeLayout_length : nodeLayout.length = 83 := by decide

/-- **The intervals are disjoint and in order** (so `Ind` partitions `Sel`). -/
theorem nodeLayout_chained : chained nodeLayout = true := by decide

/-- They start at block 0 and end at `2^16`. -/
theorem nodeLayout_end : (nodeLayout.head?.map Iv.lo, nodeLayout.getLast?.map Iv.hi) =
    (some 0, some nodeBlocks) := by decide

/-- **The regions fit**: H ends before L, L's used blocks before M, M ends at `2^16`. -/
theorem regions_fit : hEnd ≤ lBase ∧ lBase + lUsed ≤ mBase ∧ mBase + mBlocks = nodeBlocks ∧
    hEnd = 47594 := by
  simp only [hEnd, wmBase, wmSlot, wotsBase, wotsSlot, stmtBase, chainN, lBase, lUsed, mBase,
    mBlocks, nM, nodeBlocks]; norm_num

/-! ## The M rows (A.11's row model on the measured counts, per slot) -/

/-- **Per slot, the row model of revision 3.16** (BLUEPRINT §10 changes 22–23; S-E11). Built and
measured (`logs/S-E11/evbrk-3.log`: slot 0's last indexed row is `464,764`): the skeleton and every
emitted template in their aligned layout, with the walk as the XOR DAG in `G` blocks (85,506 rows,
S-E10) and the `phiRS` split layout (S-E11: −61,440). Not emitted yet (S-E12), at changes 22–23's
figures (`sizes.py`): `rsWeight` with 4 claims 45,604 and its claim-2 kind factor 68,473 (R-V-M1),
`shiftTarget` 1,300, `finPf`'s 745 `tensorW` (aligned) 47,680, `tplTargetSNode` 16,000,
`tplLinkWAll` 15,000, the `free` term 80 (R-V-M2), and the replay `R` with the sparse-skeleton and
instance-AP levers (changes 23: in the plan) 163,795 plus its closed-form share 3,000. -/
def mRowModel : List ℕ :=
  [464765,            -- skeleton + emitted templates + walk DAG + phiRS split, aligned (measured)
   45604,             -- rsWeight, 4 claims (A.11)
   68473,             -- rsWeight's claim-2 kind factor (changes 23, R-V-M1)
   1300,              -- shiftTarget (changes 22)
   47680,             -- finPf's 745 tensorW still imported, aligned
   16000,             -- tplTargetSNode (changes 21)
   15000,             -- tplLinkWAll (changes 21)
   80,                -- the free term (changes 23, R-V-M2)
   166795]            -- the replay R with the levers (163,795) and its closed-form share (3,000)

theorem mRowModel_sum : mRowModel.sum = 825697 := by norm_num [mRowModel]

/-- **The M rows fit**: a slot's rows in its `2^20` half of M (margin `1.27` on this model), the node's in
`N_M = 2^21`. -/
theorem mRows_le : mRowModel.sum ≤ slotM ∧ 2 * mRowModel.sum ≤ nM := by
  rw [mRowModel_sum]; simp only [slotM, nM]; norm_num

/-- (−) The bound is not vacuous: S-E9's sized shape (1,065,133 rows per slot, the DAG walk replayed
in `R`; changes 22 (1)) does not fit a slot. -/
theorem mRows_neg : ¬ (1065133 ≤ slotM) := by simp only [slotM]; norm_num

/-- **The used blocks fit** in `2^16` (H, L and the M rows of both slots, 128 per block). -/
theorem usedBlocks_le : hEnd + lUsed + (2 * mRowModel.sum + 127) / 128 ≤ nodeBlocks := by
  rw [mRowModel_sum, regions_fit.2.2.2]; simp only [lUsed, nodeBlocks]; norm_num

/-! ## The slots' compiled programs (the node's M rows) -/

/-- Slot `σ`'s selector cells in L (A.7, revision 3.11 F-5: after `sig` 299, the digits' 266
bit-elements, selectors 399, position bits 7,552). -/
def selCells (σ : ℕ) : FR.Kind → ℕ
  | .L32 => lBase * 128 + σ * 2 ^ 14 + 8516
  | .P30 => lBase * 128 + σ * 2 ^ 14 + 8517
  | .N30 => lBase * 128 + σ * 2 ^ 14 + 8518

/-- Slot `σ`'s first fresh M cell (after the `one` cell). -/
def slotBase (σ : ℕ) : ℕ := oneCell + 1 + σ * slotM

/-- Slot `σ`'s compiled program (`compileMux (gen fin .mux)`). -/
def slotCS (fin : Finals) (σ : ℕ) : Circ.CS :=
  Circ.compileMux oneCell (selCells σ) (slotBase σ) (gen fin .mux).ops

/-- **The node's M rows**: both slots'. -/
def nodeRows (fin : Finals) : List Circ.Row := (slotCS fin 0).rowList ++ (slotCS fin 1).rowList


/-! ## L's rows (Lr, A.7) -/

/-- Slot `σ`'s declared bit cells in L (A.7, revision 3.11 F-5: after `sig`'s 299 elements, the
digits' 266 bit-elements (two per base-4 digit, the checksum's included), the step selectors 399,
the position bits 7,552 and the kind selector 3, each a bit-element). -/
def lBitCells (σ : ℕ) : List ℕ :=
  (List.range (266 + 399 + 7552 + 3)).map fun j => lBase * 128 + σ * 2 ^ 14 + 299 + j

/-- **L's rows** (`N_L = 2^15`): `b · (1 − b) = 0` for every declared bit of both slots, with M's
`one` cell. -/
def lRows : List Circ.Row :=
  ((List.range 2).flatMap lBitCells).map fun b =>
    ⟨Circ.Lin.cell b, (Circ.Lin.cell oneCell).sub (Circ.Lin.cell b), []⟩

theorem lRows_length : lRows.length = 16440 := by simp [lRows, lBitCells]

/-- **Lr's rows make the declared cells bits.** -/
theorem lRows_sound {w : Circ.Asg} (hone : w oneCell = 1) (h : ∀ r ∈ lRows, r.Holds w)
    {b : ℕ} (hb : b ∈ (List.range 2).flatMap lBitCells) : Circ.IsBitCell w b := by
  have := h _ (List.mem_map.2 ⟨b, hb, rfl⟩)
  simp only [Circ.Row.Holds, Circ.Lin.ev_cell, Circ.Lin.ev_sub, Circ.Lin.ev_nil, hone] at this
  rcases mul_eq_zero.1 this with h0 | h1
  · exact .inl h0
  · exact .inr (sub_eq_zero.1 h1).symm

/-- The selector cells are among L's declared bits. -/
theorem selCells_mem (σ : ℕ) (hσ : σ < 2) (κ : FR.Kind) :
    selCells σ κ ∈ (List.range 2).flatMap lBitCells := by
  have h : ∀ j, j < 266 + 399 + 7552 + 3 → lBase * 128 + σ * 2 ^ 14 + 299 + j ∈ lBitCells σ :=
    fun j hj => List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  refine List.mem_flatMap.2 ⟨σ, List.mem_range.2 hσ, ?_⟩
  cases κ
  · exact (show lBase * 128 + σ * 2 ^ 14 + 299 + 8217 = selCells σ .L32 by
      show _ = lBase * 128 + σ * 2 ^ 14 + 8516; omega) ▸ h 8217 (by norm_num)
  · exact (show lBase * 128 + σ * 2 ^ 14 + 299 + 8218 = selCells σ .P30 by
      show _ = lBase * 128 + σ * 2 ^ 14 + 8517; omega) ▸ h 8218 (by norm_num)
  · exact (show lBase * 128 + σ * 2 ^ 14 + 299 + 8219 = selCells σ .N30 by
      show _ = lBase * 128 + σ * 2 ^ 14 + 8518; omega) ▸ h 8219 (by norm_num)

/-! ## Controls -/

/-- Positive: block 0 is `streamStart`, block 1 `stream`, the first `w43` block is `w43`. -/
theorem ind_controls : Ind .streamStart 0 = true ∧ Ind .stream 1 = true ∧
    Ind .w43 wotsBase = true ∧ Sel (wmBase - 1) = true := by decide

/-- `WM` and region L are `free`; negative: block 0 is not `stream`, no block past `2^16`. -/
theorem ind_controls_free : Ind .free wmBase = true ∧ Ind .free lBase = true ∧
    Ind .stream 0 = false ∧ Sel nodeBlocks = false := by
  decide

/-- Negative: a layout with an overlap fails the order check. -/
theorem chained_neg : chained [⟨.w43, 0, 2⟩, ⟨.hashA, 1, 3⟩] = false := by decide

end Layout
end FR
