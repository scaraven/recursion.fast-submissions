-- New for lvm6 (PORT17, package L2). The node circuit's stack placement as one record (`Place`) with one decided
-- interface (`Place.Ok`), its two instances `place18` (deployed until PORT17;(in `Lvm6P18Park` since INT11)) and `place17` (P17-freeze §3.3, with the
-- coordinator's fallback: `X` at slot 42); the shapes are `P18` and L1's `P17` (`Lvm6FormatP17`).
import Lvm6FormatP17

/-!
# The stack placement of the node circuit (`Place`, PORT17 L2)

The committed stack has `2^M` words in `lanes` slots of `2^slotLog` words. The node circuit `Q` places its claims
on these blocks (P17-freeze §3.3; FORMAT6 §T, §6.5):

| Block | Words | `place18` | `place17` |
|---|---|---|---|
| tree inputs, middle state | `33·2^slotLog` | slots 0–32 | slots 0–32 |
| `STREAM` = `C_rec` | `2^relay` | slot 33 | slot 33 |
| `SP` | `2^19` | slot 35 (`spSel` 35 on 6 bits) | slots 34–35 (`spSel` 17 on 5 bits) |
| `com` | `2^comLog` | slots 38–39 | slots 36–39 |
| `Y` | `25·2^yLog` | slot 36, low half | slot 40 |
| mini-bus counts | `2^12 + 64·reads` | slot 36 from `2^18` | slot 41 |
| `X` | `17·2^xLog` | slot 37 | slot 42 (fallback, coordinator) |

* **`Place`**: the record (stack geometry, `STREAM`'s window and `σ` words, the block bases, the sponge rows
  `B K₁ K₂ split`, the mini-bus counts `seeds reads readLeaves`).
* **`Place.Ok`**: the six groups of decidable conditions of P17-freeze §3.3 (alignment, disjointness and bounds,
  stream, sponge, mini-bus, selectors), in an order-free form (pairwise disjoint blocks) so that both instances
  meet the same interface. `Place.okB` is the same as one Boolean; `Place.ok_of_okB` turns `okB = true` into `Ok`.
* Derived quantities: `recOff`, `sLB`, `spSel`, `yIdx`, `xIdx` (the block bases in the units the claims use).
* **`place18_ok`, `place17_ok`**: one `decide` each.
* **`Place.Fits`**: a placement against a shape (`place18` against `P18`, `place17` against L1's `P17`).
-/

set_option autoImplicit false

namespace Lvm6

/-- **The stack placement of the node circuit** (P17-freeze §3.3). -/
structure Place where
  /-- The stack has `2^M` words. -/
  M : ℕ
  /-- A slot has `2^slotLog` words. -/
  slotLog : ℕ
  /-- The slots the stack hashes (a level-0 leaf's lanes). -/
  lanes : ℕ
  /-- The slots the circuit uses (`[0, used)`; the rest are zero). -/
  used : ℕ
  /-- `STREAM`'s slot. -/
  recSlot : ℕ
  /-- `C_rec`'s window: `2^relay` words (the relayout rounds). -/
  relay : ℕ
  /-- The stream word of `σ′` (`σ_leaf` follows at `sB + 597`). -/
  sB : ℕ
  /-- `log₂` of the `σ` region. -/
  sigLog : ℕ
  /-- `SP`'s first stack word (`2^19` words: `2^13` rows of 64 lanes). -/
  spOff : ℕ
  /-- `SP`'s selector bits (`spSel = spOff / 2^19` on `spSelBits` bits). -/
  spSelBits : ℕ
  /-- `com`'s first stack word and its `log₂` size. -/
  comOff : ℕ
  comLog : ℕ
  /-- `Y`'s first stack word; a lane has `2^yLog` words (the sponge batch). -/
  yBase : ℕ
  yLog : ℕ
  /-- The first mini-bus count word (finalize words `cnt0 + 16i`, counts from `cnt0 + 2^12`). -/
  cnt0 : ℕ
  /-- `X`'s first stack word; a lane has `2^xLog` words; the lane group is `2^xGrp` lanes. -/
  xBase : ℕ
  xLog : ℕ
  xGrp : ℕ
  /-- The sponge trace rows `B`, the signature rows `K₁`, `K₂`, the row split. -/
  B : ℕ
  K₁ : ℕ
  K₂ : ℕ
  split : ℕ
  /-- The mini-bus: seed tables, read tables, read leaves `Σ 2^τ`. -/
  seeds : ℕ
  reads : ℕ
  readLeaves : ℕ
  deriving DecidableEq, Repr

namespace Place

variable (pl : Place)

/-- `C_rec`'s offset on the stack. -/
def recOff : ℕ := pl.recSlot * 2 ^ pl.slotLog

/-- The stream word of `σ_leaf`. -/
def sLB : ℕ := pl.sB + 597

/-- `SP`'s selector value (`SP` is a block of `2^19` words). -/
def spSel : ℕ := pl.spOff / 2 ^ 19

/-- `Y`'s first lane index (in lanes of `2^yLog` words). -/
def yIdx : ℕ := pl.yBase / 2 ^ pl.yLog

/-- `SP`'s first lane index (in lanes of `2^yLog` words). -/
def spIdx : ℕ := pl.spOff / 2 ^ pl.yLog

/-- `X`'s first lane index (in lanes of `2^xLog` words). -/
def xIdx : ℕ := pl.xBase / 2 ^ pl.xLog

/-- The mini-bus count region: `2^12` finalize words, then `64` words per read. -/
def cntLen : ℕ := 2 ^ 12 + 64 * pl.reads

/-- **The blocks `(base, words)`** in address order of `place18`'s map: tree, `STREAM`, `SP`, `com`, `Y`, counts,
`X`. -/
def blocks : List (ℕ × ℕ) :=
  [(0, 33 * 2 ^ pl.slotLog), (pl.recOff, 2 ^ pl.relay), (pl.spOff, 2 ^ 19), (pl.comOff, 2 ^ pl.comLog),
    (pl.yBase, 25 * 2 ^ pl.yLog), (pl.cnt0, pl.cntLen), (pl.xBase, 17 * 2 ^ pl.xLog)]

/-- Two blocks do not meet. -/
def Apart (a b : ℕ × ℕ) : Prop := a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

instance (a b : ℕ × ℕ) : Decidable (Apart a b) := by unfold Apart; infer_instance

/-- **The placement's interface** (P17-freeze §3.3, six groups). -/
structure Ok : Prop where
  -- 1. alignment
  recAl : 2 ^ pl.relay ∣ pl.recOff
  spAl : 2 ^ 19 ∣ pl.spOff
  comAl : 2 ^ pl.comLog ∣ pl.comOff
  yAl : 2 ^ (pl.yLog + 6) ∣ pl.yBase
  spLaneAl : 2 ^ (pl.yLog + 6) ∣ pl.spOff
  xAl : 2 ^ (pl.xLog + pl.xGrp) ∣ pl.xBase
  finAl : 2 ^ 4 ∣ pl.cnt0
  cntAl : 2 ^ 6 ∣ pl.cnt0 + 2 ^ 12
  -- 2. order, disjointness, bounds
  apart : pl.blocks.Pairwise Apart
  inUsed : ∀ b ∈ pl.blocks, b.1 + b.2 ≤ pl.used * 2 ^ pl.slotLog
  usedLe : pl.used ≤ pl.lanes
  lanesLe : pl.lanes * 2 ^ pl.slotLog ≤ 2 ^ pl.M
  yBelowCnt : pl.yBase + 25 * 2 ^ pl.yLog ≤ pl.cnt0
  recSlotW : pl.relay = pl.slotLog
  relayLe : pl.relay ≤ pl.M
  -- 3. stream
  mFit : 17 * pl.split ≤ pl.sB
  sigFit : pl.sB + 2 ^ pl.sigLog ≤ 2 ^ pl.relay
  sigLen : 2 * 597 ≤ 2 ^ pl.sigLog
  sigAl : 2 ^ pl.sigLog ∣ pl.sB
  -- 4. sponge
  bLe : pl.B ≤ pl.split
  k1 : pl.K₁ = pl.split + 399
  k2 : pl.K₂ = pl.split + 864
  -- 5. mini-bus
  seedFit : 2 ^ 4 * 2 ^ 14 + pl.recOff ≤ 2 ^ pl.M
  finLen : 2 ^ 4 * pl.seeds ≤ 2 ^ 12
  finFit : pl.cnt0 + 2 ^ 4 * pl.seeds ≤ 2 ^ pl.M
  cntFit : pl.cnt0 + 2 ^ 12 + 2 ^ 6 * pl.reads ≤ 2 ^ pl.M
  leavesLo : 2 ^ 11 < 2 ^ 4 * pl.seeds + pl.readLeaves
  leavesHi : 2 ^ 4 * pl.seeds + pl.readLeaves ≤ 2 ^ 12
  -- 6. selectors
  spSelLt : pl.spSel < 2 ^ pl.spSelBits
  spBits : pl.spSelBits + 19 = pl.M
  spLanes : pl.yLog + 6 = 19
  recSel : pl.recSlot < 2 ^ (pl.M - pl.relay)
  yLt : pl.yLog < pl.M
  yIdxFit : pl.yIdx + 25 ≤ 2 ^ (pl.M - pl.yLog)
  spIdxFit : pl.spIdx + 25 ≤ 2 ^ (pl.M - pl.yLog)
  xLe : pl.xLog + pl.xGrp ≤ pl.M
  xGrpFit : 17 ≤ 2 ^ pl.xGrp
  xSel : pl.xIdx / 2 ^ pl.xGrp < 2 ^ (pl.M - pl.xLog - pl.xGrp)

/-- **`Ok` as one Boolean** (one kernel evaluation decides an instance). -/
def okB : Bool :=
  decide (2 ^ pl.relay ∣ pl.recOff) && decide (2 ^ 19 ∣ pl.spOff) && decide (2 ^ pl.comLog ∣ pl.comOff) &&
  decide (2 ^ (pl.yLog + 6) ∣ pl.yBase) && decide (2 ^ (pl.yLog + 6) ∣ pl.spOff) &&
  decide (2 ^ (pl.xLog + pl.xGrp) ∣ pl.xBase) && decide (2 ^ 4 ∣ pl.cnt0) && decide (2 ^ 6 ∣ pl.cnt0 + 2 ^ 12) &&
  decide (pl.blocks.Pairwise Apart) && decide (∀ b ∈ pl.blocks, b.1 + b.2 ≤ pl.used * 2 ^ pl.slotLog) &&
  decide (pl.used ≤ pl.lanes) && decide (pl.lanes * 2 ^ pl.slotLog ≤ 2 ^ pl.M) &&
  decide (pl.yBase + 25 * 2 ^ pl.yLog ≤ pl.cnt0) && decide (pl.relay = pl.slotLog) && decide (pl.relay ≤ pl.M) &&
  decide (17 * pl.split ≤ pl.sB) && decide (pl.sB + 2 ^ pl.sigLog ≤ 2 ^ pl.relay) &&
  decide (2 * 597 ≤ 2 ^ pl.sigLog) && decide (2 ^ pl.sigLog ∣ pl.sB) &&
  decide (pl.B ≤ pl.split) && decide (pl.K₁ = pl.split + 399) && decide (pl.K₂ = pl.split + 864) &&
  decide (2 ^ 4 * 2 ^ 14 + pl.recOff ≤ 2 ^ pl.M) && decide (2 ^ 4 * pl.seeds ≤ 2 ^ 12) &&
  decide (pl.cnt0 + 2 ^ 4 * pl.seeds ≤ 2 ^ pl.M) && decide (pl.cnt0 + 2 ^ 12 + 2 ^ 6 * pl.reads ≤ 2 ^ pl.M) &&
  decide (2 ^ 11 < 2 ^ 4 * pl.seeds + pl.readLeaves) && decide (2 ^ 4 * pl.seeds + pl.readLeaves ≤ 2 ^ 12) &&
  decide (pl.spSel < 2 ^ pl.spSelBits) && decide (pl.spSelBits + 19 = pl.M) && decide (pl.yLog + 6 = 19) &&
  decide (pl.recSlot < 2 ^ (pl.M - pl.relay)) && decide (pl.yLog < pl.M) &&
  decide (pl.yIdx + 25 ≤ 2 ^ (pl.M - pl.yLog)) && decide (pl.spIdx + 25 ≤ 2 ^ (pl.M - pl.yLog)) &&
  decide (pl.xLog + pl.xGrp ≤ pl.M) && decide (17 ≤ 2 ^ pl.xGrp) &&
  decide (pl.xIdx / 2 ^ pl.xGrp < 2 ^ (pl.M - pl.xLog - pl.xGrp))

theorem ok_of_okB (h : pl.okB = true) : pl.Ok := by
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h14a⟩, h15⟩, h16⟩, h17⟩, h17a⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩, h28⟩, h28a⟩,
    h29⟩, h30⟩, h31⟩, h32⟩, h33⟩, h34⟩, h35⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h14a, h15, h16, h17, h17a, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28, h28a, h29, h30, h31, h32, h33, h34, h35⟩

end Place

/-! ## The two instances -/

/-- **The `P17` placement** (P17-freeze §3.3 with the coordinator's fallback for `X`): slots of `2^18` words,
`SP` at slots 34–35 (`17·2^19`), `com` at slots 36–39 (`9·2^20`), `Y` at slot 40, the counts at slot 41, `X` at
slot 42 (lane group `2^9`, as at `P18`); 43 slots used, 46 hashed. -/
def place17 : Place where
  M := 24
  slotLog := 18
  lanes := 46
  used := 43
  recSlot := 33
  relay := 18
  sB := 2 ^ 17
  sigLog := 11
  spOff := 17 * 2 ^ 19
  spSelBits := 5
  comOff := 9 * 2 ^ 20
  comLog := 20
  yBase := 40 * 2 ^ 18
  yLog := 13
  cnt0 := 41 * 2 ^ 18
  xBase := 42 * 2 ^ 18
  xLog := 10
  xGrp := 9
  B := 3816
  K₁ := 7567
  K₂ := 8032
  split := 7168
  seeds := 77
  reads := 40
  readLeaves := 1000

theorem place17_okB : place17.okB = true := by decide +kernel

/-- **The `P17` placement meets the interface.** -/
theorem place17_ok : place17.Ok := place17.ok_of_okB place17_okB

/-- The stack offsets of P17-freeze §3.3 (and the fallback's `X`), as numbers. -/
theorem place17_offsets :
    place17.recOff = 8650752 ∧ place17.spOff = 8912896 ∧ place17.comOff = 9437184 ∧
      place17.yBase = 10485760 ∧ place17.cnt0 = 10747904 ∧ place17.xBase = 11010048 ∧
      place17.spSel = 17 ∧ place17.yIdx = 40 * 32 ∧ place17.spIdx = 17 * 64 ∧ place17.xIdx = 42 * 2 ^ 8 ∧
      place17.sLB = 2 ^ 17 + 597 := by
  decide

/-- **A placement fits a shape**: the same stack, slots of `2^κ` words (`stackOK`'s 64-slot rows), the leaf's lanes. -/
def Place.Fits (pl : Place) (sh : Shape) : Prop :=
  pl.M = sh.M ∧ pl.slotLog = sh.κ ∧ pl.lanes = sh.lanes ∧ pl.yLog = sh.κs

instance (pl : Place) (sh : Shape) : Decidable (pl.Fits sh) := by unfold Place.Fits; infer_instance

theorem place17_fits : place17.Fits P17 := by decide

end Lvm6
