-- New for lvm2 (roll 8 = B1, B1-S0 skeleton; B-DES §1.1 with B1-G0a's corrections 1–2): the typed layout of a
-- LoopIR program: where each cell's words live in the word vector `z`, where each constraint row's slot lives,
-- and the memory read off `z`. B1-K owns the layout data and its solver (B1-P1P2 §4); L-B proves against it.
import LvmLoopInterp

/-!
# The typed layout `Lay`

B-DES §1.1: the witness is a vector `z` of `K` words over a word space of `2^21` (`y`), and every constraint row
of the program has a slot in a constraint space of `2^20` (`x`). B1-G0a's corrections: the result regions are
**binary-chunked** (B1-P1P2 §5.1), with **iteration bits low** (word `= chunk base + (slot − s₀)·2^ℓ + jf`;
slot `= chunk base + (rank − r₀)·2^ℓ + jf`), plus **dense regions** in cell order (§2's choice 1).

* **Word space** (`yregs`): aligned regions with their source: committed (`com`, the typed table block of
  `C_main`) or virtual: `S_flat` (the child's trace, one claim on `C_rec` through the relayout), `PUB`, `σ′`,
  the `KS` aliases, `QLT`, the constant `1`. The `BITS` outputs are committed inputs (B1-P1P2 §5.3).
* **Cells.** Per block (a copy of the program's block structure, checked by `okB`): for each rank among the
  block's `τ`-writers its source `CSrc`: a committed slot, a **virtual `loadE`** (limb `m` is the `K` word of
  operand `m` at the iteration: "via limbs"), or a **static `readd` alias** (QLT: the `K` input cell
  `tgt[jf]`). Glue blocks (`dims = []`) are blocks with `ℓ = 0`. Input cells live in input regions, dense
  result runs in dense regions.
* **Slots** (`xs`): the constraint chunks, sorted by base; the constraint rows of a block (`muladd`, `lin`,
  `assert0`, `fixmul`) have consecutive ranks; auxiliary blocks (`BITS` rows, B1-Q) own chunks too.
* `Lay.word τ n m`, `Lay.slot b t jf`, **`memOf lay z`** (an `E` cell is `Σ_m y^m · z(word E n m)`);
  **`Lay.okB Q`** / `Lay.Ok Q`: the decidable check that the layout is one of `Q` and fits `2^20 × 2^21`.

What `Ok` gives (and all that `LvmTyped.holds_of_wiring` needs): the block copies are `Q`'s; every `loadE`
writer is virtual with `Q`'s operands; constraint slots are injective and below `2^20`; every word is below
`2^21`. Words need not be injective (aliasing words is sound, not complete).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-! ## Sizes -/

/-- Variables of the constraint space `x` (B-DES §1.1: `2^20` slots). -/
abbrev xVars : ℕ := 20

/-- Variables of the word space `y` (`2^21` words). -/
abbrev yVars : ℕ := 21

/-! ## The word space -/

/-- What a region of the word space holds. -/
inductive YSrc where
  /-- Committed words: the typed table block of `C_main`. -/
  | com
  /-- `S_flat`: position `p` of the child's trace (virtual; `C_rec` through the relayout). -/
  | sflat
  /-- `PUB` (virtual; V computes it). -/
  | pub
  /-- `σ′` (virtual; `C_rec`'s column 17). -/
  | sigma
  /-- The `KS` aliases `xs`, `ys`, `md` (virtual; `C_main`'s `KS` block). -/
  | ks
  /-- `QLT`'s public table (virtual). -/
  | qlt
  /-- The constant `1` (virtual). -/
  | one
  deriving DecidableEq, Repr, Inhabited

/-- A region of the word space: `2^log` words from `base` (aligned) and their source. -/
structure YReg where
  /-- The first word. -/
  base : ℕ
  /-- `log₂` of the size. -/
  log : ℕ
  /-- The source. -/
  src : YSrc
  deriving DecidableEq, Repr, Inhabited

/-! ## Cells -/

/-- Where the cells of one rank among a block's `τ`-writers live. -/
inductive CSrc where
  /-- Committed: slot `s` of the block's result chunks of its type. -/
  | slot (s : ℕ)
  /-- A virtual `loadE` result: limb `m` is the `K` cell `args[m].at j` (a copy of the row's operands). -/
  | load (args : List Addr)
  /-- A static `readd` (QLT): the `K` input cell `tgt[jf]`. -/
  | alias (tgt : List ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- A result chunk: committed slots `[s0, s0 + n)` of one type of a block; limb `m` of slot `s` at iteration
`jf` is word `bases[m] + (s − s0)·2^ℓ + jf`. -/
structure RChunk where
  /-- The first slot. -/
  s0 : ℕ
  /-- The slots. -/
  n : ℕ
  /-- One base per limb. -/
  bases : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- A region of cells in cell order: cells `[lo, lo + n)` of memory `ty`, limb `m` of cell `c` at word
`bases[m] + (c − lo)`. The input regions and the dense result regions. -/
structure DReg where
  /-- The memory. -/
  ty : Ty
  /-- The first cell. -/
  lo : ℕ
  /-- The cells. -/
  n : ℕ
  /-- One base per limb. -/
  bases : List ℕ
  /-- B1-IX: `lanes > 1` for an input region whose cells are `lanes` row-major lanes (cell `lo + lanes·x + l`, as the
  program's arrays read `KS`'s `xs`, `ys`): lane `l`'s rows are their own aligned word region, row `x` at word
  `laneBases[l] + x` (so each lane maps affinely onto its `C_main` column). `1`: the cells in order from `bases`. -/
  lanes : ℕ := 1
  /-- The lanes' word regions (`lanes > 1`). -/
  laneBases : List ℕ := []
  deriving DecidableEq, Repr, Inhabited

/-- **The word of limb `m` of cell `n`** in its region `d`: `bases[m] + (n − lo)`, or (`lanes > 1`) its lane's base
plus its row. -/
def DReg.word (d : DReg) (n m : ℕ) : ℕ :=
  if d.lanes ≤ 1 then d.bases.getD m 0 + (n - d.lo)
  else d.laneBases.getD ((n - d.lo) % d.lanes) 0 + (n - d.lo) / d.lanes

/-- **A block's layout**: a copy of its structure (checked against the program) and where its cells live. -/
structure BLay where
  /-- The loop dimensions (copy). -/
  dims : List ℕ
  /-- The first `K` result cell (copy of `Q.start .K b`). -/
  stK : ℕ
  /-- The first `E` result cell. -/
  stE : ℕ
  /-- `K` writers per iteration (copy of `tw .K`). -/
  twK : ℕ
  /-- `E` writers per iteration. -/
  twE : ℕ
  /-- Per rank among the `K` writers: where its cells live. -/
  srcK : List CSrc
  /-- Per rank among the `E` writers. -/
  srcE : List CSrc
  /-- The `K` result chunks. -/
  chK : List RChunk
  /-- The `E` result chunks (three bases each). -/
  chE : List RChunk
  /-- Per template row: its constraint rank, if it is a constraint row (copy, checked). -/
  cr : List (Option ℕ)
  deriving DecidableEq, Repr, Inhabited

namespace BLay

variable (B : BLay)

/-- `log₂` of the iterations. -/
def l : ℕ := B.dims.sum

/-- The first result cell of memory `τ`. -/
def st : Ty → ℕ
  | .K => B.stK
  | .E => B.stE

/-- Writers of memory `τ` per iteration. -/
def tw : Ty → ℕ
  | .K => B.twK
  | .E => B.twE

/-- The sources of memory `τ`'s writers. -/
def src : Ty → List CSrc
  | .K => B.srcK
  | .E => B.srcE

/-- The result chunks of memory `τ`. -/
def ch : Ty → List RChunk
  | .K => B.chK
  | .E => B.chE

/-- Limb `m` of committed slot `s` of memory `τ` at iteration `jf` (`0` if no chunk holds the slot). -/
def slotWord (τ : Ty) (s jf m : ℕ) : ℕ :=
  match (B.ch τ).find? fun c ↦ decide (c.s0 ≤ s ∧ s < c.s0 + c.n) with
  | some c => c.bases.getD m 0 + (s - c.s0) * 2 ^ B.l + jf
  | none => 0

end BLay

/-! ## Auxiliary rows (`BITS`, B1-Q) -/

/-- An operand of an auxiliary row. -/
inductive AOp where
  /-- The word `base + stride·j` at iteration `j` (a free committed word: `BITS`' bit columns). -/
  | word (base stride : ℕ)
  /-- The cell `a.at [j]` (through the layout). -/
  | cell (a : Addr)
  /-- The constant `1`. -/
  | one
  deriving DecidableEq, Repr, Inhabited

/-- An auxiliary constraint row: its entries `(matrix o, operand, weight)` (`o`: 0 `A`, 1 `B`, 2 `D`, 3 `W`). -/
structure ARow where
  /-- The entries. -/
  ops : List (ℕ × AOp × FE)
  deriving Inhabited

/-- An auxiliary block: `2^l` iterations of its rows (constraint ranks = row indices). -/
structure ABlk where
  /-- `log₂` of the iterations. -/
  l : ℕ
  /-- The rows. -/
  rows : List ARow
  deriving Inhabited

/-! ## Constraint chunks -/

/-- A constraint chunk: ranks `[r0, r0 + n)` of block `blk` (`blk` at or past the block count `nB`: auxiliary
block `blk − nB`) with `2^l` iterations; rank `r` at iteration `jf` is slot `base + (r − r0)·2^l + jf`. -/
structure XChunk where
  /-- The block. -/
  blk : ℕ
  /-- `log₂` of its iterations (copy). -/
  l : ℕ
  /-- The first rank. -/
  r0 : ℕ
  /-- The ranks. -/
  n : ℕ
  /-- The first slot. -/
  base : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The slots after a chunk. -/
def XChunk.top (c : XChunk) : ℕ := c.base + c.n * 2 ^ c.l

/-! ## The layout -/

/-- **The typed layout of a program.** -/
structure Lay where
  /-- Input `K` cells (copy of `Q.nInK`). -/
  nInK : ℕ
  /-- Input `E` cells. -/
  nInE : ℕ
  /-- The input regions (cells below `nIn`). -/
  inp : List DReg
  /-- The dense result regions (committed cells in cell order). -/
  dense : List DReg
  /-- The blocks. -/
  blocks : List BLay
  /-- The auxiliary blocks (`BITS` rows). -/
  aux : List ABlk
  /-- The constraint chunks, sorted by `base`. -/
  xs : List XChunk
  /-- The word of the constant `1`. -/
  one : ℕ
  /-- The word space's regions, sorted by `base`. -/
  yregs : List YReg
  /-- **Constant input cells** (B1-Q/B-DES §1.3: QLT's public table in `Φ_Q`): `K` cells `[lo, lo + |vs|)` with
  the values `vs`. They have no word: an operand naming one is the word `1` with the value as weight. -/
  cst : List (ℕ × List FK) := []
  deriving Inhabited

namespace Lay

variable (lay : Lay)

/-! ### Words -/

/-- The value of `K` cell `n` if it is a constant input cell. -/
def cst? (n : ℕ) : Option FK :=
  (lay.cst.find? fun r ↦ decide (r.1 ≤ n ∧ n < r.1 + r.2.length)).map fun r ↦ r.2.getD (n - r.1) 0

/-- The input or dense region holding cell `n` of memory `τ`. -/
def dreg? (τ : Ty) (n : ℕ) : Option DReg :=
  (lay.dense ++ lay.inp).find? fun d ↦ d.ty == τ && decide (d.lo ≤ n ∧ n < d.lo + d.n)

/-- Limb `m` of cell `n` of memory `τ` in its input or dense region (`0` if none). -/
def wordD (τ : Ty) (n m : ℕ) : ℕ :=
  match lay.dreg? τ n with
  | some d => d.word n m
  | none => 0

/-- The block whose results hold cell `n` of memory `τ`. -/
def owner? (τ : Ty) (n : ℕ) : Option ℕ :=
  (List.range lay.blocks.length).find? fun b ↦
    let B := lay.blocks.getD b default
    decide (B.st τ ≤ n ∧ n < B.st τ + B.tw τ * 2 ^ B.l)

/-- A committed result cell: its dense region, else its slot's chunk. -/
def wordC (B : BLay) (τ : Ty) (n s jf m : ℕ) : ℕ :=
  match lay.dreg? τ n with
  | some d => d.word n m
  | none => B.slotWord τ s jf m

/-- **The word of a `K` cell**: an input cell's region word; a committed result's dense or chunk word; a static
`readd`'s target input cell's word. -/
def wordK (n : ℕ) : ℕ :=
  match lay.owner? .K n with
  | some b =>
    let B := lay.blocks.getD b default
    let off := n - B.stK
    match B.srcK.getD (off % B.twK) default with
    | .slot s => lay.wordC B .K n s (off / B.twK) 0
    | .alias tgt => lay.wordD .K (tgt.getD (off / B.twK) 0) 0
    | .load _ => 0
  | none => lay.wordD .K n 0

/-- **The word of limb `m` of an `E` cell**: an input cell's region word; a committed result's dense or chunk
word; a `loadE` result's operand `m` (a `K` cell at the iteration). -/
def wordE (n m : ℕ) : ℕ :=
  match lay.owner? .E n with
  | some b =>
    let B := lay.blocks.getD b default
    let off := n - B.stE
    match B.srcE.getD (off % B.twE) default with
    | .slot s => lay.wordC B .E n s (off / B.twE) m
    | .load args => lay.wordK ((args.getD m default).at (unflat B.dims (off / B.twE)))
    | .alias _ => 0
  | none => lay.wordD .E n m

/-- **`lay.word τ n m`**: the word of limb `m` of cell `n` of memory `τ` (`K` cells have one limb). -/
def word : Ty → ℕ → ℕ → ℕ
  | .K, n, _ => lay.wordK n
  | .E, n, m => lay.wordE n m

/-! ### Slots -/

/-- The chunk of rank `r` of block `b` (constraint or auxiliary). -/
def xchunk? (b r : ℕ) : Option XChunk :=
  lay.xs.find? fun c ↦ c.blk == b && decide (c.r0 ≤ r ∧ r < c.r0 + c.n)

/-- The slot of rank `r` of block `b` at iteration `jf` (`0` if no chunk holds it). -/
def slotR (b r jf : ℕ) : ℕ :=
  match lay.xchunk? b r with
  | some c => c.base + (r - c.r0) * 2 ^ c.l + jf
  | none => 0

/-- **`lay.slot b t jf`**: the constraint slot of template row `t` of block `b` at iteration `jf`. -/
def slot (b t jf : ℕ) : ℕ :=
  match (lay.blocks.getD b default).cr.getD t none with
  | some r => lay.slotR b r jf
  | none => 0

/-- The slot of row `r` of auxiliary block `k` at iteration `j`. -/
def auxSlot (k r j : ℕ) : ℕ := lay.slotR (lay.blocks.length + k) r j

end Lay

/-! ## The memory read off the words -/

/-- **The memory read off `z`** through the layout: `K` cell `n` is its constant (`lay.cst`) or `z(word K n)`;
`E` cell `n` is `Σ_m y^m · z(word E n m)` (a `loadE` cell through its operands' words, which are never constant:
`cstOk`). -/
def memOf (lay : Lay) (z : ℕ → FK) : Mem :=
  ⟨fun n ↦ (lay.cst? n).getD (z (lay.wordK n)), fun n ↦
    FE.ofK (z (lay.wordE n 0)) + FE.y * FE.ofK (z (lay.wordE n 1)) +
      FE.y * FE.y * FE.ofK (z (lay.wordE n 2))⟩

/-! ## The check -/

/-- A constraint row: `muladd`, `lin`, `assert0`, `fixmul` (`loadE` is virtual; `readd` is the mini-bus's or
static). -/
def Row.isCon (r : Row) : Bool :=
  match r.op with
  | .muladd => true
  | .lin .. => true
  | .assert0 => true
  | .fixmul => true
  | _ => false

/-- The source of a writer fits its operation: `loadE` is virtual with the row's operands (an `E` result of `K`
operands); a `readd` is committed (mini-bus) or a static alias of `size` input cells; every other writer is
committed. -/
def srcOk (r : Row) (size nInK : ℕ) : CSrc → Bool
  | .slot _ => r.op.kind != .loadE
  | .load args => r.op.kind == .loadE && r.ty == .E && args == r.args && args.all (·.ty == .K)
  | .alias tgt => r.op.kind == .readd && r.ty == .K && tgt.length == size && tgt.all (· < nInK)

/-- The template walk: every writer's source fits, the sources are consumed in rank order, and the constraint
ranks are consecutive (`rC` the next one). -/
def tplOk (size nInK : ℕ) : List Row → List (Option ℕ) → List CSrc → List CSrc → ℕ → Bool
  | [], cr, sK, sE, _ => cr.isEmpty && sK.isEmpty && sE.isEmpty
  | _ :: _, [], _, _, _ => false
  | r :: rs, c :: cr, sK, sE, rC =>
    let okC := c == (if Row.isCon r then some rC else none)
    let rC' := if Row.isCon r then rC + 1 else rC
    match r.writes, sK, sE with
    | some .K, s :: sK', _ => okC && srcOk r size nInK s && tplOk size nInK rs cr sK' sE rC'
    | some .E, _, s :: sE' => okC && srcOk r size nInK s && tplOk size nInK rs cr sK sE' rC'
    | none, _, _ => okC && tplOk size nInK rs cr sK sE rC'
    | _, _, _ => false

/-- The constraint rows of a template. -/
def nCon (B : Block) : ℕ := (B.tpl.filter Row.isCon).length

/-- The chunks of block `b` cover its ranks `[r, n)` consecutively, in list order. -/
def chunksCover (l : ℕ) : List XChunk → ℕ → ℕ → Bool
  | [], r, n => r == n
  | c :: cs, r, n => c.l == l && c.r0 == r && 0 < c.n && chunksCover l cs (r + c.n) n

/-- The chunks sorted by base, disjoint, below `2^xVars`. -/
def xsSorted : List XChunk → Bool
  | [] => true
  | [c] => decide (c.top ≤ 2 ^ xVars)
  | c :: c' :: cs => decide (c.top ≤ c'.base) && xsSorted (c' :: cs)

/-- The word regions sorted by base, disjoint, aligned, below `2^yVars`. -/
def yregsSorted : List YReg → Bool
  | [] => true
  | [r] => decide (r.base % 2 ^ r.log = 0 ∧ r.base + 2 ^ r.log ≤ 2 ^ yVars)
  | r :: r' :: rs => decide (r.base % 2 ^ r.log = 0 ∧ r.base + 2 ^ r.log ≤ r'.base) && yregsSorted (r' :: rs)

/-- A region's words are below `2^yVars`. -/
def dregFits (d : DReg) : Bool :=
  if d.lanes ≤ 1 then d.bases.length == d.ty.limbs && d.bases.all fun b ↦ decide (b + d.n ≤ 2 ^ yVars)
  else d.ty == .K && d.n % d.lanes == 0 && d.laneBases.length == d.lanes &&
    d.laneBases.all fun b ↦ decide (b + d.n / d.lanes ≤ 2 ^ yVars)

/-- A block's chunks' words are below `2^yVars`. -/
def chFits (l : ℕ) (τ : Ty) (c : RChunk) : Bool :=
  c.bases.length == τ.limbs && c.bases.all fun b ↦ decide (b + c.n * 2 ^ l ≤ 2 ^ yVars)

/-- The blocks are copies of the program's, with consecutive cell ranges from the inputs. -/
def blocksOk (nInK : ℕ) (xs : List XChunk) : ℕ → ℕ → ℕ → List BLay → List Block → Bool
  | _, _, _, [], [] => true
  | b, sK, sE, B :: Bs, Bq :: Bqs =>
    B.dims == Bq.dims && B.stK == sK && B.stE == sE && B.twK == Bq.tw .K && B.twE == Bq.tw .E &&
      tplOk Bq.size nInK Bq.tpl B.cr B.srcK B.srcE 0 &&
      B.chK.all (chFits B.l .K) && B.chE.all (chFits B.l .E) &&
      chunksCover B.l (xs.filter (·.blk == b)) 0 (nCon Bq) &&
      blocksOk nInK xs (b + 1) (sK + B.twK * Bq.size) (sE + B.twE * Bq.size) Bs Bqs
  | _, _, _, _, _ => false

/-- An auxiliary operand's words are below `2^yVars` (cells: through the layout, always). -/
def aopFits (l : ℕ) : AOp → Bool
  | .word base stride => decide (base + stride * (2 ^ l - 1) < 2 ^ yVars)
  | _ => true

/-- The auxiliary blocks: matrices `o < 4`, words below `2^yVars`, their chunks cover their rows. -/
def auxOk (xs : List XChunk) : ℕ → List ABlk → Bool
  | _, [] => true
  | k, A :: As =>
    A.rows.all (fun r ↦ r.ops.all fun e ↦ decide (e.1 < 4) && aopFits A.l e.2.1) &&
      chunksCover A.l (xs.filter (·.blk == k)) 0 A.rows.length && auxOk xs (k + 1) As

/-- The cells `[lo, hi]` miss every constant region. -/
def cstMiss (cst : List (ℕ × List FK)) (lo hi : ℕ) : Bool := cst.all fun r ↦ hi < r.1 || r.1 + r.2.length ≤ lo

/-- **The constant cells are inputs, never a `loadE` operand nor a static `readd`'s target** (so `memOf`'s `E`
cells and the aliases read words only). -/
def cstOk (cst : List (ℕ × List FK)) (nInK : ℕ) (blocks : List BLay) (Qb : List Block) : Bool :=
  cst.all (fun r ↦ decide (r.1 + r.2.length ≤ nInK)) &&
    (Qb.all fun B ↦ B.tpl.all fun r ↦ r.op.kind != .loadE || r.args.all fun a ↦
      cstMiss cst a.base (a.base + dot a.strides (B.dims.map fun d ↦ 2 ^ d - 1))) &&
    blocks.all fun B ↦ B.srcK.all fun s ↦ match s with
      | .alias tgt => tgt.all fun n ↦ cstMiss cst n n
      | _ => true

namespace Lay

variable (lay : Lay)

/-- **The layout check** (decidable, per block and per template row, no enumeration of instances): `lay` is a
layout of `Q` and fits `2^xVars × 2^yVars`. -/
def okB (Q : Program) : Bool :=
  lay.nInK == Q.nInK && lay.nInE == Q.nInE && lay.blocks.length == Q.blocks.length &&
    blocksOk lay.nInK lay.xs 0 Q.nInK Q.nInE lay.blocks Q.blocks &&
    auxOk lay.xs lay.blocks.length lay.aux &&
    xsSorted lay.xs && yregsSorted lay.yregs &&
    lay.inp.all dregFits && lay.dense.all dregFits && decide (lay.one < 2 ^ yVars) &&
    cstOk lay.cst lay.nInK lay.blocks Q.blocks

/-- **`lay` is a layout of `Q`.** -/
def Ok (Q : Program) : Prop := lay.okB Q = true

instance (Q : Program) : Decidable (lay.Ok Q) := inferInstanceAs (Decidable (lay.okB Q = true))

end Lay

end Lvm.Typed
