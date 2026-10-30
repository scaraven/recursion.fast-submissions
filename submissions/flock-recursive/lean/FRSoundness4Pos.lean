-- G6: this module also holds the former modules `FRShape4`, `FRSoundnessCoreChain` (one section each, in import order).
import FRFormat
import FRSoundnessCoreDefs
import FRSoundnessCoreTruths

section G6_FRShape4

-- New for `flock-recursive` (BLUEPRINT revision 4.0, B-11 … B-13, B-17; stage S-0′).

/-!
# Revision 4.1's shapes: kinds, ladders, the item sequence, sizes

BLUEPRINT B-11 … B-13, B-17 and §10 changes 25 (b). Everything here is **parametric** in the
kind's dimensions (`Dims`: `m`, node or not, `log₂` of the L and M rows); the 3.x constants are
instances, proved below (`ladderOf_32`, `ladderOf_30`, `phasesOf_seq3`, `itemsOf_seq3`,
`piSizeOf_seq3`). The 3.x definitions (`Kind`, `phases`, `items`, `piSize`) stay untouched: they
are used, with their exact values, by modules this stage may not edit (S-0′ JOURNAL, C1).

* **Kinds** (revision 4.1, B-12, B-13). Segments `L30`/`L31`/`L32` (`m = 30/31/32`,
  `n ≤ 2^(m − 14)`; `L30` is 3.x's `P30` with a variable `n`, byte `'P'`), nodes `N2` (`m = 31`: the
  previous node and `≤ 2` segments), `N4` (`m = 32`: the previous node and `≤ 4` segments), `N8`
  (`m = 32`, step 1: `≤ 8` segments), sized by total bits (tight packing), the aggregate leaf `A`
  (no SNARK of its own) and `W`.
* **The ladder** of a kind is `ladderOf m = ladderOfR 6 m` (§2.2's rule; level 0 has `2^6` rows).
  `ell0 = 6` is the ruling: S-D3 declined lever 5 (`ell0 = 5`). The parameter `ell0` reaches only
  `ladderOfR`/`Seq.lvK`; `colBytes` (`lvlStar`'s rows), the final tails (`2^(m − 25)`, revision 4.3:
  `FRVIRFinals4.gTailOps`) and `Dims.seq`/`seqOf` (`seqR 6`) hard-code 6, so another value would
  mis-size the format (R-4-m3).
* **One item sequence** `seq4` (B-13: every kind at `m ≤ 32`): 3.x's sequence (`seq3`, `m* = 32`)
  with the node phases sized for `N_L = 2^17`, `N_M = 2^23` and `f`'s `2^25` cells (Lr 17, E2 23,
  E4 25 rounds: 14 more items than 3.x, all dummies for the segments) and, revision 4.4.1 (PACK-4.4
  §11, (β′)), the cap check (`CapD`: absorb the 871 path digests `D`; `CapZeta`: squeeze `ζ`;
  `CapChk`: absorb `A`, 1,536 K elements; `CapChkZ`: squeeze `z`) and level 4's cap at depth 8
  (`Seq.cap4`, lever L2; 3.x's `seq3` keeps 7); revision 4.4.2 (the reserve, D1p §3; RSV2: one stacked claim): `Lrend`
  1,008 and `Eend` 112 bytes (`Seq.lrEnd`, `Seq.eEnd`, the previous node's `evalM` claim; no item
  added): 8,783 items, `piSize` 876,304, a stream of `64 · 24,236` bytes; `4 × 8,783 + 3 ≤ qV = 36,000`.
-/

namespace FR
namespace Rev4
open RecursionFast

/-! ## Kinds -/

/-- The segment kinds (B-12). -/
inductive SegKind where
  | L30 | L31 | L32
  deriving DecidableEq, Repr

/-- The node kinds (B-13). -/
inductive NodeKind where
  | N2 | N4 | N8
  deriving DecidableEq, Repr

namespace SegKind
/-- The kind byte (`L32` keeps 3.x's `'L'`, `L30` 3.x's `P30` byte `'P'`). -/
def byte : SegKind → UInt8 | L30 => 0x50 | L31 => 0x4B | L32 => 0x4C
/-- `log₂` of the witness bits. -/
def m : SegKind → ℕ | L30 => 30 | L31 => 31 | L32 => 32
/-- **The capacity**: a segment of kind `κ` proves `1 ≤ n ≤ 2^(m − 14)` chain steps. -/
def cap (κ : SegKind) : ℕ := 2 ^ (κ.m - 14)
/-- The kind of a kind byte. -/
def ofByte? (b : UInt8) : Option SegKind :=
  if b = 0x50 then some L30 else if b = 0x4B then some L31 else if b = 0x4C then some L32 else none
theorem ofByte?_byte (κ : SegKind) : ofByte? κ.byte = some κ := by cases κ <;> decide
theorem cap_eq : cap L30 = 2 ^ 16 ∧ cap L31 = 2 ^ 17 ∧ cap L32 = 2 ^ 18 := ⟨rfl, rfl, rfl⟩
end SegKind

namespace NodeKind
/-- The kind byte. -/
def byte : NodeKind → UInt8 | N2 => 0x4D | N4 => 0x4E | N8 => 0x4F
/-- `log₂` of the witness bits (B-13, revision 4.1: tight packing, `m ≤ 32`). -/
def m : NodeKind → ℕ | N2 => 31 | N4 => 32 | N8 => 32
/-- The segment sub-slots. -/
def segSlots : NodeKind → ℕ | N2 => 2 | N4 => 4 | N8 => 8
/-- Whether slot 1 is the previous step's node. -/
def hasPrev : NodeKind → Bool | N2 => true | N4 => true | N8 => false
/-- The kind's index in the reserve's stacked matrix (RSV2 §2.1: `N2`, `N4`, `N8` ↦ 0, 1, 2). -/
def ix : NodeKind → ℕ | N2 => 0 | N4 => 1 | N8 => 2
/-- The kinds in index order. -/
def all : List NodeKind := [N2, N4, N8]
theorem all_ix (κ : NodeKind) : all.getD κ.ix N2 = κ := by cases κ <;> rfl
/-- The kind of a kind byte. -/
def ofByte? (b : UInt8) : Option NodeKind :=
  if b = 0x4D then some N2 else if b = 0x4E then some N4 else if b = 0x4F then some N8 else none
theorem ofByte?_byte (κ : NodeKind) : ofByte? κ.byte = some κ := by cases κ <;> decide
end NodeKind

/-- The aggregate leaf's kind byte `'A'`. -/
def aggByte : UInt8 := 0x41

/-- The kind bytes are distinct from each other and from a witness-sending proof's first byte
(`0`/`1`). -/
theorem bytes_distinct :
    [aggByte, SegKind.L30.byte, SegKind.L31.byte, SegKind.L32.byte, NodeKind.N2.byte, NodeKind.N4.byte,
      NodeKind.N8.byte, 0, 1].Nodup := by
  decide

/-! ## Dimensions -/

/-- A kind's dimensions: `m`, node or not, `log₂` of the L rows and of the M rows. -/
structure Dims where
  m : ℕ
  node : Bool
  logL : ℕ
  logM : ℕ
  deriving DecidableEq, Repr

def SegKind.dims (κ : SegKind) : Dims := ⟨κ.m, false, 0, 0⟩
/-- `N_L`: a `2^14` stride per verifier slot (S-0′ issue I-4); `N_M`: `2^20` cells per verifier slot,
rounded up to a power of two (B-13). -/
def NodeKind.dims : NodeKind → Dims
  | .N2 => ⟨31, true, 16, 22⟩ | .N4 => ⟨32, true, 17, 23⟩ | .N8 => ⟨32, true, 17, 23⟩
/-- The 3.x kinds' dimensions. -/
def Kind.dims : Kind → Dims
  | .L32 => ⟨32, false, 15, 21⟩ | .P30 => ⟨30, false, 15, 21⟩ | .N30 => ⟨30, true, 15, 21⟩

/-- A sequence's counts: `m*` (its ladder), Z1's coordinates, Z3's and S2's rounds, Lr's and E2's
coordinates = rounds, E4's rounds, `log₂` of the final message's K elements (= Pf's rounds). -/
structure Seq where
  mStar : ℕ
  z1 : ℕ
  z3 : ℕ
  s2 : ℕ
  lr : ℕ
  e2 : ℕ
  e4 : ℕ
  pf : ℕ
  /-- E4 end's absorb: `f̂(r′)` (16 B) zero-padded so that the hashed stream is a multiple of 64
  bytes (3.x: 32, INT-2; the node sequence: 64). -/
  e4end : ℕ := 32
  /-- `log₂` of level 0's rows: 6 (lever 5's `5` is declined, S-D3). Not threaded through the
  format: `colBytes`, the final tails (`FRVIRFinals4.gTailOps`, `2^(m − 25)`) and `seqOf` assume 6
  (R-4-m3). -/
  ell0 : ℕ := 6
  /-- Revision 4.4.1 (PACK-4.4 §11, B2 (β′)): the batched cap check after `Pf` (absorb `D`, squeeze
  `ζ`, absorb `A`, squeeze `z`), which replaces the per-position dynamic cap reads. `seq4` only. -/
  capChk : Bool := false
  /-- Revision 4.4.1 (PACK-4.4 §11.2, lever L2): level 4's cap depth (3.x: 7; `seq4`: 8, `sib` one
  less at level 4). Threaded into `ladderOfR`, so `seq3`'s ladder (and 3.x's `lvlStar`) is untouched. -/
  cap4 : ℕ := 7
  /-- Revision 4.4.2 (the reserve, D1p §3): `Lrend`'s absorb (`fLrEnd`; 3.x: 48 = `â_L ‖ b̂_L ‖ ĉ_L`;
  `seq4`: 1,008, the previous node's stacked `evalM` claim `p_x (23) ‖ p_y (25) ‖ s (9) ‖ X₃ (3)` after
  the three values, RSV2 §2.1) and `Eend`'s (`fEEnd`; 3.x: 48; `seq4`: 112, `â_M ‖ b̂_M ‖ ĉ_M ‖ m̂* ‖ 0^48`).
  No item or phase is added, so no Fiat–Shamir position moves. -/
  lrEnd : ℕ := 48
  eEnd : ℕ := 48
  deriving DecidableEq, Repr

/-- **The counts one kind needs** (§2.3): Z1 `m − 13`, Z3 `m − 6`, S2 `(m − 14) + 10`; node only:
Lr `log N_L`, E2 `log N_M`, E4 `m − 7` (`f`'s cells); the final message `2^(m − 25)`. -/
def Dims.seqR (ell0 : ℕ) (d : Dims) : Seq :=
  ⟨d.m, d.m - 13, d.m - 6, d.m - 4, if d.node then d.logL else 0, if d.node then d.logM else 0,
   if d.node then d.m - 7 else 0, d.m - 19 - ell0, 32, ell0, false, 7, 48, 48⟩

/-- The counts at level-0 rows `2^6`. -/
def Dims.seq (d : Dims) : Seq := d.seqR 6

/-- The componentwise maximum. -/
def Seq.max (a b : Seq) : Seq :=
  ⟨Nat.max a.mStar b.mStar, Nat.max a.z1 b.z1, Nat.max a.z3 b.z3, Nat.max a.s2 b.s2,
   Nat.max a.lr b.lr, Nat.max a.e2 b.e2, Nat.max a.e4 b.e4, Nat.max a.pf b.pf, a.e4end, a.ell0,
   a.capChk, a.cap4, a.lrEnd, a.eEnd⟩

/-- **The sequence of a kind group**: the componentwise maximum of its kinds' counts. -/
def seqOf : List Dims → Seq
  | [] => ⟨0, 0, 0, 0, 0, 0, 0, 0, 32, 6, false, 7, 48, 48⟩
  | d :: ds => d.seq.max (seqOf ds)

/-- `a` fits in `b`: every count of `a` is at most `b`'s (a kind's unused items are dummies). -/
def Seq.Le (a b : Seq) : Prop :=
  a.mStar ≤ b.mStar ∧ a.z1 ≤ b.z1 ∧ a.z3 ≤ b.z3 ∧ a.s2 ≤ b.s2 ∧ a.lr ≤ b.lr ∧ a.e2 ≤ b.e2 ∧
    a.e4 ≤ b.e4 ∧ a.pf ≤ b.pf

instance (a b : Seq) : Decidable (a.Le b) := by unfold Seq.Le; infer_instance

/-- 3.x's sequence: `{L32, P30, N30}`. -/
def seq3 : Seq := seqOf [Kind.dims .L32, Kind.dims .P30, Kind.dims .N30]
/-- **The item sequence of revision 4.1** (B-13: every kind at `m ≤ 32`, one sequence): the six
kinds' maximum; its hashed stream is a multiple of 64 bytes with 3.x's 32-byte E4 end
(`chainLenOf_seq4`). It is 3.x's sequence with the node phases sized for `N_L = 2^17`,
`N_M = 2^23` and `f`'s `2^25` cells (`seq4_eq`, `seq3_eq`); revision 4.4.1: with the cap check
`CapD`/`CapZeta`/`CapChk`/`CapChkZ` after `Pf` (`capChk := true`) and level 4's cap at depth 8
(`cap4 := 8`, PACK-4.4 §11.2 L2). -/
def seq4 : Seq := { seqOf (SegKind.dims .L30 :: SegKind.dims .L31 :: SegKind.dims .L32 ::
    [NodeKind.dims .N2, NodeKind.dims .N4, NodeKind.dims .N8]) with
    e4end := 32, capChk := true, cap4 := 8, lrEnd := 1008, eEnd := 112 }

theorem seq3_eq : seq3 = ⟨32, 19, 26, 28, 15, 21, 23, 7, 32, 6, false, 7, 48, 48⟩ := by decide
theorem seq4_eq : seq4 = ⟨32, 19, 26, 28, 17, 23, 25, 7, 32, 6, true, 8, 1008, 112⟩ := by decide

/-- Every kind fits the sequence (its unused items are dummies). -/
theorem seg_fits (κ : SegKind) : κ.dims.seq.Le seq4 := by cases κ <;> decide
theorem node_fits (κ : NodeKind) : κ.dims.seq.Le seq4 := by cases κ <;> decide

/-! ## The ladder (§2.2) -/

/-- **The ladder of `m` with `2^ell0` rows at level 0 and level 4's cap at depth `cap4`** (§2.2's
rule `kᵢ₊₁ = kᵢ/8`, `nᵢ = 2^(i+1) kᵢ`, `log₂ k₀ = m − 7 − ell0`): level `i` has
`log₂ n = m − 6 − ell0 − 2i`; rows `2^ell0, 16, …`; queries and caps as revision 3.1 (they depend
on the rate only), except level 4's cap (3.x: 7; revision 4.4.1's `seq4`: 8, PACK-4.4 §11.2 L2). -/
def ladderOfR (ell0 cap4 m : ℕ) : List Level :=
  [⟨ell0, m - 6 - ell0, 290, 9⟩, ⟨4, m - 8 - ell0, 178, 8⟩, ⟨4, m - 10 - ell0, 145, 8⟩,
   ⟨4, m - 12 - ell0, 132, 8⟩, ⟨4, m - 14 - ell0, 126, cap4⟩]

/-- The ladder at revision 3.1's rows and caps (`2^6` rows at level 0, level 4's cap at 7). -/
def ladderOf (m : ℕ) : List Level := ladderOfR 6 7 m

/-- Level `i` of a kind of `log₂` size `m` in the sequence `S` (its level-0 rows, its level-4 cap). -/
def Seq.lvK (S : Seq) (m i : ℕ) : Level := (ladderOfR S.ell0 S.cap4 m).getD i ⟨0, 1, 0, 0⟩

/-- Level `i` of the sequence `S` itself. -/
def Seq.lv (S : Seq) (i : ℕ) : Level := S.lvK S.mStar i

/-- **Level `i` of a kind of `log₂` size `m` in revision 4.4.1** (`seq4`'s ladder: level 4's cap at
depth 8; `CKind.lv`). -/
def lvOf (m i : ℕ) : Level := seq4.lvK m i

theorem ladderOf_32 : ladderOf 32 = ladder32 := rfl
theorem ladderOf_30 : ladderOf 30 = ladder30 := rfl
/-- (+) Levels 0–3 of revision 4.4.1's `m = 32` ladder are 3.x's; (−) level 4's cap is 8, not 7. -/
theorem lvOf_32 : (∀ i < 4, lvOf 32 i = lvlStar i) ∧ (lvOf 32 4).cap = 8 ∧ (lvlStar 4).cap = 7 := by
  refine ⟨fun i hi => ?_, by rw [lvOf, seq4_eq]; rfl, rfl⟩
  rw [lvOf, seq4_eq]; interval_cases i <;> rfl

/-- The squeezes and siblings of revision 4.4.1's ladders, `m = 32`, `31` (`L31`, `N2`) and `30`
(`L30`): level 4's siblings are one less than 3.x's (`ladder_sib`: 5 and 3). -/
theorem ladder_sq_sib :
    ((List.range 5).map fun i => ((lvOf 32 i).sq, (lvOf 32 i).sib)) =
      [(25, 11), (13, 10), (10, 8), (8, 6), (6, 4)] ∧
    ((List.range 5).map fun i => ((lvOf 31 i).sq, (lvOf 31 i).sib)) =
      [(23, 10), (12, 9), (9, 7), (7, 5), (6, 3)] ∧
    ((List.range 5).map fun i => ((lvOf 30 i).sq, (lvOf 30 i).sib)) =
      [(21, 9), (12, 8), (9, 6), (7, 4), (6, 2)] := by
  simp only [lvOf, seq4_eq]; decide

/-- A kind's ladder fits its sequence's position by position (squeezes and siblings). -/
def LadderFits (m mStar : ℕ) : Prop :=
  ∀ i < nLevels, (lvOf m i).sq ≤ (lvOf mStar i).sq ∧ (lvOf m i).sib ≤ (lvOf mStar i).sib ∧
    (lvOf m i).ell = (lvOf mStar i).ell ∧ (lvOf m i).t = (lvOf mStar i).t

theorem seg_ladder_fits (κ : SegKind) : LadderFits κ.m seq4.mStar := by
  intro i hi; simp only [nLevels] at hi; cases κ <;> interval_cases i <;> decide
theorem node_ladder_fits (κ : NodeKind) : LadderFits κ.m seq4.mStar := by
  intro i hi; simp only [nLevels] at hi; cases κ <;> interval_cases i <;> decide

/-! ## The phase table, parametric -/

/-- What a phase's squeezes yield (3.x's `Chal` without its kind tables). -/
inductive ChalK where
  | coords | one
  | pos (i : ℕ)
  deriving DecidableEq, Repr

/-- A phase's shape without kind tables (the item sequence and the field sizes need only counts). -/
inductive Sh where
  | seed
  | absorb (fld len : ℕ)
  | squeezes (n : ℕ) (ch : ChalK)
  | uni (fld : ℕ)
  | rounds (fld n deg : ℕ) (inK : Bool)
  | queries (i : ℕ)
  deriving DecidableEq, Repr

/-- The 3.x shape without its kind tables. -/
def _root_.FR.Shape.toSh : Shape → Sh
  | .seed => .seed
  | .absorb f len => .absorb f len
  | .squeezes n (.coords _) => .squeezes n .coords
  | .squeezes n (.one _) => .squeezes n .one
  | .squeezes n (.pos i) => .squeezes n (.pos i)
  | .uni f => .uni f
  | .rounds f n d inK _ => .rounds f n d inK
  | .queries i => .queries i

/-- Ceiling of `x / 2` (coordinates per squeeze: two). -/
def half (x : ℕ) : ℕ := (x + 1) / 2

/-- The bytes level `i` absorbs after its fold rounds: `cap_{i+1}`, or the final message. -/
def capBytesOf (S : Seq) (i : ℕ) : ℕ :=
  if i + 1 < nLevels then 2 ^ (S.lv (i + 1)).cap * 32 else 2 ^ S.pf * 32

/-- **The cap check's entries** (PACK-4.4 §11.1): the five caps' digests, `Σᵢ 2^capᵢ` (`seq4`: `512 +
256 + 256 + 256 + 256 = 1,536`). Entry `offᵢ + k` is `capᵢ[k]`, `offᵢ = capEntriesBelow S i`. -/
def capEntriesBelow (S : Seq) (i : ℕ) : ℕ := ((List.range i).map fun i' => 2 ^ (S.lv i').cap).sum

/-- All five caps' entries. -/
def capEntries (S : Seq) : ℕ := capEntriesBelow S nLevels

/-- **The cap check's reads** (PACK-4.4 §11.1): every position of every level, in item order
(`seq4`: `290 + 178 + 145 + 132 + 126 = 871`). Read `r`'s path digest is `D_r`. -/
def capReadsBelow (S : Seq) (i : ℕ) : ℕ := ((List.range i).map fun i' => (S.lv i').t).sum

/-- All levels' reads. -/
def capReadsN (S : Seq) : ℕ := capReadsBelow S nLevels

/-- **`D`'s bytes** (A.3 row 18): one digest (32 bytes) per read. -/
def dBytes (S : Seq) : ℕ := capReadsN S * 32

/-- **`A`'s bytes** (A.3 row 19): one K element (32 bytes) per cap entry, no pad (PACK-4.4 §11.4
item 1: with L2, the stream is whole blocks without it, `chainLenOf_seq4`). -/
def aBytes (S : Seq) : ℕ := capEntries S * 32

/-- **The cap check's four phases** (revision 4.4.1, PACK-4.4 §11.1 (β′)): absorb the path digests
`D` (field `fD`), squeeze `ζ`, absorb `A` (field `fA`), squeeze `z`. `D` is in the chain before `ζ`,
`A` before `z`. -/
def capChkPh (S : Seq) : List (String × Sh) :=
  if S.capChk then
    [("CapD", .absorb fD (dBytes S)), ("CapZeta", .squeezes 1 .one), ("CapChk", .absorb fA (aBytes S)),
      ("CapChkZ", .squeezes 1 .one)]
  else []

/-- **The phase table of a sequence** (§2.3, A.4; 3.x's order, counts from `S`; revision 4.4.1: then
the cap check, `capChkPh`). -/
def phasesOf (S : Seq) : List (String × Sh) :=
  -- the ascription: without it the `++` chain's elaboration takes ≈ 19 s (A2′'s profile)
  ([("seed", .seed), ("stmt", .absorb fStmt 128), ("cap0", .absorb fCaps (2 ^ (S.lv 0).cap * 32)),
   ("Z1", .squeezes (half S.z1) .coords), ("Z2", .uni fZ2), ("Z3", .rounds fZ3 S.z3 3 false),
   ("Zend", .absorb fZend 32), ("L1", .squeezes 1 .one), ("L2", .rounds fL2 14 2 false),
   ("L3", .absorb fL2 (8 * 16)), ("L3β", .squeezes 1 .one),
   ("S1", .squeezes (half (S.mStar - 14 + 11)) .coords), ("S2", .rounds fS2 S.s2 2 false),
   ("Lr1", .squeezes (half S.lr) .coords), ("Lr2", .rounds fLr S.lr 3 false), ("Lrend", .absorb fLrEnd S.lrEnd),
   ("Lr3", .squeezes 1 .one), ("E1", .squeezes (half S.e2) .coords), ("E2", .rounds fE S.e2 3 false),
   ("Eend", .absorb fEEnd S.eEnd), ("E3", .squeezes 1 .one), ("E4", .rounds fE S.e4 2 false),
   ("E4end", .absorb fE S.e4end), ("RS0", .absorb fRS0 (4 * 128 * 16)), ("RS1", .squeezes 4 .coords),
   ("B'", .squeezes 1 .one)] : List (String × Sh)) ++
  (List.range nLevels).flatMap (fun i =>
    [("P1", .rounds fP1 (S.lv i).ell 2 true), ("C", .absorb (capField i) (capBytesOf S i)),
     ("P2", .squeezes (S.lv i).sq (.pos i)), ("Q", .queries i), ("P3", .squeezes 5 .coords)]) ++
  [("Pf", .rounds fPf S.pf 2 true)] ++ capChkPh S

/-- **The 3.x table is `phasesOf seq3`** (names, shapes and counts). -/
theorem phasesOf_seq3 : phases.map (fun p => (p.name, p.shape.toSh)) = phasesOf seq3 := by
  decide

/-! ## Items and sizes, parametric -/

/-- The queries of one position of level `i` under the level map `lv`. -/
def posItemsL (lv : ℕ → Level) (i : ℕ) : List Item := .col i :: (List.range (lv i).sib).map (.node i)

/-- A phase's items under the level map `lv`. -/
def Sh.itemsL (lv : ℕ → Level) : Sh → List Item
  | .seed => [.seed]
  | .absorb _ len => [.absorb len]
  | .squeezes n _ => List.replicate n .squeeze
  | .uni _ => [.absorb uniBytes, .squeeze]
  | .rounds _ n _ inK => (List.replicate n [.absorb (roundBytes inK), .squeeze]).flatten
  | .queries i => (List.replicate (lv i).t (posItemsL lv i)).flatten

theorem _root_.FR.Shape.itemsL_toSh (s : Shape) : s.toSh.itemsL lvlStar = s.items := by
  cases s with
  | squeezes n ch => cases ch <;> rfl
  | _ => rfl

/-- **The item sequence of `S`.** -/
def itemsOf (S : Seq) : List Item := (phasesOf S).flatMap fun p => p.2.itemsL (S.lv)

/-- **`seq3`'s items are 3.x's `items`**: the generator's fidelity check (4.1's segments use
`seq4`, `itemsOf_seq4_length`). -/
theorem itemsOf_seq3 : itemsOf seq3 = items := by
  have h : seq3.lv = lvlStar := by rw [seq3_eq]; rfl
  rw [itemsOf, ← phasesOf_seq3, List.flatMap_map, h, items]
  exact List.flatMap_congr fun p _ => p.shape.itemsL_toSh

/-- The bytes of field `f` a phase contributes under `lv`. -/
def Sh.bytesToL (lv : ℕ → Level) (f : ℕ) : Sh → ℕ
  | .seed => if f = fHdr then 48 else 0
  | .absorb g len => if f = g then len else 0
  | .squeezes _ _ => 0
  | .uni g => if f = g then uniBytes else 0
  | .rounds g n _ inK => if f = g then n * roundBytes inK else 0
  | .queries i =>
    if f = fCols then (lv i).t * colBytes i
    else if f = fSibs then (lv i).t * (lv i).sib * 32 else 0

theorem _root_.FR.Shape.bytesToL_toSh (f : ℕ) (s : Shape) : s.toSh.bytesToL lvlStar f = s.bytesTo f := by
  cases s with
  | squeezes n ch => cases ch <;> rfl
  | _ => rfl

/-- The size of field `f` in `S`'s format. -/
def fieldSizeOf (S : Seq) (f : ℕ) : ℕ := ((phasesOf S).map fun p => p.2.bytesToL (S.lv) f).sum

/-- The fields of revision 4.4's format: 3.x's 18, `fD` (A.3 row 18) and `fA` (row 19). -/
def nFields4 : ℕ := 20

/-- **`piSize` of `S`'s format** (`hdr ‖ stmt ‖ body`, A.3's fields; `fD`, `fA` empty without the
cap check). -/
def piSizeOf (S : Seq) : ℕ := ((List.range nFields4).map (fieldSizeOf S)).sum

theorem fieldSizeOf_seq3 (f : ℕ) : fieldSizeOf seq3 f = fieldSize f := by
  have h : seq3.lv = lvlStar := by rw [seq3_eq]; rfl
  rw [fieldSizeOf, ← phasesOf_seq3, List.map_map, h, fieldSize]
  exact congrArg List.sum (List.map_congr_left fun p _ => p.shape.bytesToL_toSh f)

/-- **`seq3`'s format has 3.x's `piSize`** (797,904; a 4.1 segment proof has
`piSizeOf seq4 = 798,192`). -/
theorem piSizeOf_seq3 : piSizeOf seq3 = piSize := by
  rw [piSizeOf, nFields4, List.range_succ, List.map_append, List.sum_append, List.range_succ,
    List.map_append, List.sum_append, piSize, fieldSizes]
  have h18 : fieldSizeOf seq3 18 = 0 := by rw [fieldSizeOf_seq3]; decide +kernel
  have h19 : fieldSizeOf seq3 19 = 0 := by rw [fieldSizeOf_seq3]; decide +kernel
  rw [List.map_singleton, List.map_singleton, h18, h19]
  simp only [List.sum_singleton, Nat.add_zero]
  exact congrArg List.sum (List.map_congr_left fun f _ => fieldSizeOf_seq3 f)

/-- The hashed stream's bytes of `S`'s trace (`0x54 ‖ traceBytes`). -/
def streamBytesOf (S : Seq) : ℕ := 1 + ((itemsOf S).map fun it => 8 + it.qlen + 32).sum

/-- Compressions of `S`'s trace digest chain. -/
def chainLenOf (S : Seq) : ℕ := (streamBytesOf S + 63) / 64

theorem streamBytesOf_seq3 : streamBytesOf seq3 = streamBytes := by
  rw [streamBytesOf, itemsOf_seq3]; rfl

/-! ## The sequence's numbers -/

theorem itemsOf_seq4_length : (itemsOf seq4).length = 8783 := by
  rw [seq4_eq]; decide +kernel

/-- The cap check's sizes at `seq4`: 871 reads (`D` 27,872 bytes), 1,536 cap entries (`A` 49,152
bytes; level 4's cap has 256 entries under L2). -/
theorem capEntries_seq4 : capReadsN seq4 = 871 ∧ dBytes seq4 = 27872 ∧ capEntries seq4 = 1536 ∧
    aBytes seq4 = 49152 := by
  rw [seq4_eq]; decide

/-- (+) `seq4` has the cap check: `D` (27,872 bytes), `ζ`, `A` (49,152 bytes), `z`; (−) `seq3`
(3.x's) has none. -/
theorem capChkPh_ctl : capChkPh seq4 = [("CapD", .absorb fD 27872), ("CapZeta", .squeezes 1 .one),
    ("CapChk", .absorb fA 49152), ("CapChkZ", .squeezes 1 .one)] ∧ capChkPh seq3 = [] := by
  rw [seq4_eq, seq3_eq]; decide

/-- **`CapD ‖ CapZeta` is block-aligned**: `(80 + |D|) + 80 = 64 · 438` stream bytes. `CapChk ‖
CapChkZ` (`80 + 49,152 + 80`) is half a block over; level 4's 126 fewer node items (L2) give the
half block back, so the stream stays whole blocks (`chainLenOf_seq4`). -/
theorem capChk_aligned : ((Item.absorb (dBytes seq4)).slen + Item.squeeze.slen) % 64 = 0 ∧
    ((Item.absorb (aBytes seq4)).slen + Item.squeeze.slen) % 64 = 32 := by
  rw [capEntries_seq4.2.1, capEntries_seq4.2.2.2]; decide

theorem fieldSizesOf_seq4 : (List.range nFields4).map (fieldSizeOf seq4) = [48, 128, 2048, 1248, 32,
    800, 1344, 816, 1008, 2336, 112, 8192, 2112, 672, 49152, 4096, 487504, 237632, 27872, 49152] := by
  rw [seq4_eq]; decide +kernel

theorem piSizeOf_seq4 : piSizeOf seq4 = 876304 := by rw [piSizeOf, fieldSizesOf_seq4]; rfl

theorem streamBytesOf_seq4 : streamBytesOf seq4 = 1551104 := by rw [seq4_eq]; decide +kernel

/-- The stream is `64 · chainLen` bytes: no padding cell (as INT-2's 3.x stream). -/
theorem chainLenOf_seq4 : chainLenOf seq4 = 24236 ∧ streamBytesOf seq4 = 64 * 24236 := by
  rw [chainLenOf, streamBytesOf_seq4]; decide

/-! ## `qV` (B-17) -/

/-- **`qV = 36,000`** (B-17). -/
def qV4 : ℕ := 36000

/-- The aggregate leaf's trace (`≤ 4` segments) and a node's trace fit `qV`. -/
theorem traces_le_qV : 4 * (itemsOf seq4).length ≤ qV4 := by
  rw [itemsOf_seq4_length]; decide

/-- Revision 4.4.1: with R-A′'s three spacers between four segments, `4 · 8,783 + 3 = 35,135 ≤ qV`. -/
theorem traces_spacers_le_qV : 4 * (itemsOf seq4).length + 3 ≤ qV4 := by
  rw [itemsOf_seq4_length]; decide

/-! ## `hdr` and `stmt` -/

/-- A segment's `hdr`: `kindByte ‖ m ‖ 0^14 ‖ s` (3.x's leaf header; `s` the segment's start). -/
def segHdr (κ : SegKind) (s : Digest) : List UInt8 := [κ.byte, κ.m.toUInt8] ++ List.replicate 14 0 ++ s.toList

/-- A node's `hdr`: `kindByte ‖ m ‖ 0^14 ‖ vk`. -/
def nodeHdr (κ : NodeKind) (vk : Digest) : List UInt8 := [κ.byte, κ.m.toUInt8] ++ List.replicate 14 0 ++ vk.toList

/-- **`L32`'s segment header is 3.x's `L32` header.** -/
theorem segHdr_L32 (s : Digest) : segHdr .L32 s = hdrBytes .L32 s := rfl

theorem segHdr_length (κ : SegKind) (s : Digest) : (segHdr κ s).length = 48 := by simp [segHdr]
theorem nodeHdr_length (κ : NodeKind) (vk : Digest) : (nodeHdr κ vk).length = 48 := by simp [nodeHdr]

end Rev4
end FR

end G6_FRShape4

section G6_FRSoundnessCoreChain

-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessDefs` (14), `FRSoundnessFrChain` (25). Content:
-- the potential's item-list part (`Defs`: `fsStarts`, `fsRanges`, `pRound`, …) and the generic
-- chain `G.*` (`FsSeq`, `Matches`, `IsChain`, `EscG`, `muG`, `chains`). The 3.x modules import this
-- one.

/-! ## From `FRSoundnessDefs` (14 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle

open scoped NNReal

section Potential

variable (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0)

open Classical in
/-- The charge of chain `j` in `L`: its `φ` if its last entry is on the frontier, else `0`. -/
noncomputable def termG (L : Log) (j : ℕ) : ℝ≥0 :=
  if OnFrontier L L[j]! then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0

/-- A function supported on one index sums, over a duplicate-free list, to its value there. -/
theorem sum_map_single {l : List ℕ} (hl : l.Nodup) (f : ℕ → ℝ≥0) (i : ℕ)
    (hf : ∀ j ∈ l, j ≠ i → f j = 0) : (l.map f).sum = if i ∈ l then f i else 0 := by
  classical
  rw [← List.sum_toFinset f hl]
  split_ifs with hi
  · exact Finset.sum_eq_single i (fun j hj hji => hf j (List.mem_toFinset.mp hj) hji)
      (fun h => absurd (List.mem_toFinset.mpr hi) h)
  · exact Finset.sum_eq_zero fun j hj => hf j (List.mem_toFinset.mp hj)
      (fun h => hi (h ▸ List.mem_toFinset.mp hj))

theorem sum_map_zero {l : List ℕ} (f : ℕ → ℝ≥0) (hf : ∀ j ∈ l, f j = 0) : (l.map f).sum = 0 := by
  rw [List.map_congr_left hf]; simp

variable {D φ}

section Step

variable {L : Log} {q : ByteArray} {a : Digest}

theorem L₀_append {x : ByteArray × Digest} {j : ℕ} (hj : j < L.length) :
    L₀ (L ++ [x]) j = L₀ L j := by
  unfold L₀; rw [List.take_append_of_le_length hj.le]

theorem L₀_new : L₀ (L ++ [(q, a)]) L.length = L := by simp [L₀]

/-- An old chain's charge after appending a fresh non-bad entry, plus the charge it loses when the
query is its squeeze, is its charge before. -/
theorem termG_append (hq : q ∉ L.map Prod.fst) (hb : ¬ Bad (L ++ [(q, a)])) {j : ℕ}
    (hj : j < L.length) :
    termG φ (L ++ [(q, a)]) j +
        (if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0) =
      termG φ L j := by
  classical
  have hget : (L ++ [(q, a)])[j]! = L[j]! := by
    rw [getElem!_pos (L ++ [(q, a)]) j (by simp; omega), getElem!_pos L j hj,
      List.getElem_append_left hj]
  have hmem : L[j]! ∈ L := by rw [getElem!_pos L j hj]; exact List.getElem_mem hj
  unfold termG
  rw [hget, L₀_append hj, entriesOf_pathOf_append hb hj]
  have hfr := frontier_append (q := q) (a := a) hmem
  generalize L[j]! = e at hmem hfr ⊢
  by_cases hs : q = squeezeQ e.2
  · have hf : OnFrontier L e := ⟨hmem, hs ▸ hq⟩
    rw [ite_eq_right (fun h => (hfr.mp h).2 hs), ite_eq_left hs, ite_eq_left hf, zero_add]
  · rw [ite_eq_right hs, add_zero]
    by_cases hf : OnFrontier L e
    · rw [ite_eq_left (hfr.mpr ⟨hf, hs⟩), ite_eq_left hf]
    · rw [ite_eq_right (fun h => hf (hfr.mp h).1), ite_eq_right hf]

end Step

open Classical in
/-- `Bad` of a log with an entry appended, as a sum of indicators, is at most the H row's count. -/
theorem card_bad_le {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst)
    (hl : L.length < logCap) :
    (∑ a : Digest, (if Bad (L ++ [(q, a)]) then 1 else 0 : ℝ≥0)) ≤ (badCount : ℝ≥0) := by
  rw [Finset.sum_boole]
  exact_mod_cast bad_step_frac hb hq hl

end Potential

section Ext

variable (D : Log → Log → Prop)

theorem condCount_split (L₀ es₀ : Log) {r : ℕ} {pre : List Digest} (h : pre.length < r) :
    ∑ a : Digest, condCount D L₀ es₀ r (pre ++ [a]) = 2 ^ 256 * condCount D L₀ es₀ r pre := by
  classical
  unfold condCount
  obtain ⟨k, hk⟩ : ∃ k, r - pre.length = k + 1 := ⟨r - pre.length - 1, by omega⟩
  have hk' : ∀ a : Digest, r - (pre ++ [a]).length = k := fun a => by simp; omega
  simp only [hk', hk]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← Nat.cast_sum, extCount_split, show 256 * (k + 1) = 256 * k + 256 by ring, pow_add, mul_inv]
  have h2 : (2 : ℝ≥0) ^ 256 ≠ 0 := by positivity
  have h3 : (2 : ℝ≥0) ^ (256 * k) ≠ 0 := by positivity
  field_simp

open Classical in
theorem condCount_last (L₀ es₀ : Log) {r : ℕ} {pre : List Digest} (h : pre.length = r) :
    condCount D L₀ es₀ r pre = if EscAtG D L₀ (ext es₀ pre) then 1 else 0 := by
  classical
  unfold condCount
  rw [h, Nat.sub_self, mul_zero, pow_zero, div_one, extCount, Finset.card_filter,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [List.ofFn_zero, List.append_nil]
  split_ifs <;> simp

end Ext

section Local

theorem lastAns_of_getLast? {es : Log} {e : ByteArray × Digest} (h : es.getLast? = some e) :
    lastAns es = e.2 := by
  simp [lastAns, h]

/-- A 40-byte query is its first 8 bytes and its 32-byte state. -/
theorem split40 (q : ByteArray) (hs : q.size = 40) :
    q.data.toList = q.data.toList.take 8 ++ (bytesAt q 8 32).toList := by
  have hl : q.data.toList.length = 40 := by rw [Array.length_toList]; exact hs
  have ht : (q.data.toList.take 8).length = 8 := by rw [List.length_take, hl]; rfl
  refine List.ext_getElem (by rw [List.length_append, ht, hl]; simp) fun k h₁ h₂ => ?_
  by_cases k8 : k < 8
  · rw [List.getElem_append_left (by rw [ht]; omega), List.getElem_take]
  · rw [List.getElem_append_right (by rw [ht]; omega), Vector.getElem_toList, getElem_bytesAt,
      List.getD_eq_getElem _ _ (by omega)]
    congr 1; rw [ht]; omega

/-- A query of the squeeze item with state `st` is `squeezeQ st`. -/
theorem eq_squeezeQ {q : ByteArray} {st : Digest} (hm : fsCheck .squeeze q = true)
    (hs : stateIn q = some st) : q = squeezeQ st := by
  simp only [fsCheck, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨ht, hsz⟩ := hm
  simp only [stateIn, ht, hsz, and_true, or_true, ↓reduceIte, Option.some.injEq] at hs
  apply Merkle.byteArray_ext_toList
  rw [squeezeQ_data, split40 q hsz, ht, hs]

theorem fsCheck_absorb_or {it : Item} {q : ByteArray} (h : fsCheck it q = true) :
    it = .seed ∨ it = .squeeze ∨ ∃ len, it = .absorb len := by
  cases it <;> simp_all [fsCheck]

variable (D : Log → Log → Prop) (rnd : ℕ → Option (ℕ × ℕ))

theorem pRoundG_seed (L : Log) (e : ByteArray × Digest) (h0 : rnd 0 = none) :
    pRoundG D rnd L [e] = 0 := by
  simp [pRoundG, h0]

variable {D rnd}

end Local

end FR.Snd

end

/-! ## From `FRSoundnessFrChain` (25 declarations) -/

section

namespace FR.Snd.G

open RecursionFast FR.Merkle

open scoped NNReal

/-- **A Fiat–Shamir item list** for the chains (3.x: `fsItems`; revision 4.1: `seq4`'s). -/
class FsSeq where
  fs : List Item
  one_le : 1 ≤ fs.length

variable [FsSeq]

/-- **The entries follow the Fiat–Shamir items**: a seed first, at most `|FsSeq.fs|` entries, each
later entry with the previous answer as its state and the tag and length of its item. -/
def Matches (es : Log) : Prop :=
  (es.head?.map fun e => fsCheck .seed e.1) = some true ∧ ∃ hl : es.length ≤ FsSeq.fs.length,
    ∀ i (hi : i + 1 < es.length), stateIn es[i + 1].1 = some es[i].2 ∧
      fsCheck (FsSeq.fs[i + 1]'(by omega)) es[i + 1].1 = true

/-- **A chain of `L`**: an entry index whose forest path, read as entries, `Matches`. -/
def IsChain (L : Log) (j : ℕ) : Prop := j < L.length ∧ Matches (entriesOf L (pathOf L j))

noncomputable instance (L : Log) : DecidablePred (IsChain L) := Classical.decPred _

/-- The indices of `L` that are chains. -/
noncomputable def chains (L : Log) : List ℕ :=
  (List.range L.length).filter fun j => decide (IsChain L j)

theorem matches_ne_nil {es : Log} (h : Matches es) : es ≠ [] := by
  rintro rfl; simp [Matches] at h

/-- `Matches` of a longer list gives `Matches` of its nonempty prefix. -/
theorem matches_of_append {es : Log} {x : ByteArray × Digest} (hne : es ≠ [])
    (h : Matches (es ++ [x])) : Matches es := by
  obtain ⟨h0, hl, hm⟩ := h
  refine ⟨?_, by simp at hl; omega, fun i hi => ?_⟩
  · rwa [List.head?_append_of_ne_nil _ hne] at h0
  · have := hm i (by simp; omega)
    simp only [List.getElem_append_left hi, List.getElem_append_left (show i < es.length by omega)]
      at this
    exact this

/-- **`chains_append`**: appending a non-bad entry keeps every old chain (with its path) and adds
at most the new entry. -/
theorem chains_append {L : Log} {e : ByteArray × Digest} (hb : ¬ Bad (L ++ [e])) :
    chains (L ++ [e]) = chains L ++ (if IsChain (L ++ [e]) L.length then [L.length] else []) := by
  classical
  unfold chains
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro j hj
    rw [List.mem_range] at hj
    apply decide_eq_decide.mpr
    unfold IsChain
    rw [List.length_append, List.length_singleton, pathOf_append_old hb hj,
      entriesOf_append fun i hi => (mem_pathOf_le hi).trans_lt hj]
    constructor
    · rintro ⟨-, h⟩; exact ⟨hj, h⟩
    · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
  · by_cases h : IsChain (L ++ [e]) L.length <;> simp [h]

theorem chains_nodup (L : Log) : (chains L).Nodup := (List.nodup_range).filter _

theorem mem_chains {L : Log} {j : ℕ} : j ∈ chains L ↔ IsChain L j := by
  unfold chains
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- `Matches` extends by an entry linked to the last answer and matching the next item. -/
theorem matches_append {es : Log} {x : ByteArray × Digest} (h : Matches es)
    (hl' : es.length < FsSeq.fs.length) (hy : ∃ y, es.getLast? = some y ∧ stateIn x.1 = some y.2)
    (hmatch : fsCheck (FsSeq.fs[es.length]'hl') x.1 = true) : Matches (es ++ [x]) := by
  obtain ⟨h0, hl, hm⟩ := h
  obtain ⟨y, hy, hst⟩ := hy
  have hne : es ≠ [] := by rintro rfl; simp at h0
  refine ⟨?_, by simp; omega, fun i hi => ?_⟩
  · rwa [List.head?_append_of_ne_nil _ hne]
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i + 1 < es.length
    · have := hm i hlt
      rwa [List.getElem_append_left hlt, List.getElem_append_left (show i < es.length by omega)]
    · have hie : i + 1 = es.length := by omega
      have hy' : es[i]'(by omega) = y := by
        rw [List.getLast?_eq_getElem?] at hy
        have : es.length - 1 = i := by omega
        rw [this, List.getElem?_eq_getElem (by omega)] at hy
        exact Option.some.inj hy
      rw [List.getElem_append_left (show i < es.length by omega), hy',
        List.getElem_concat_length hie]
      refine ⟨hst, ?_⟩
      have : FsSeq.fs[i + 1]'(by omega) = FsSeq.fs[es.length]'hl' := by congr 1
      rw [this]; exact hmatch

section Potential

variable (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0)

/-- **`Esc`**: some chain of `L` escapes at its last entry. -/
def EscG (L : Log) : Prop := ∃ j ∈ chains L, EscAtG D (L₀ L j) (entriesOf L (pathOf L j))

/-- The sum of the frontier charges over the chains of `L`. -/
noncomputable def sumG (L : Log) : ℝ≥0 := ((chains L).map (termG φ L)).sum

open Classical in
/-- **The potential** (§5.1): `1` on a bad or escaped log, else the frontier charges. -/
noncomputable def muG (L : Log) : ℝ≥0 := if Bad L ∨ EscG D L then 1 else sumG φ L

theorem muG_empty : muG D φ [] = 0 := by
  have hc : chains ([] : Log) = [] := rfl
  have he : ¬ EscG D [] := by rintro ⟨j, hj, -⟩; simp [hc] at hj
  have hb := not_bad_nil
  rw [muG, ite_eq_right (by tauto), sumG, hc]
  rfl

theorem muG_lt_one {L : Log} (h : muG D φ L < 1) : ¬ Bad L ∧ ¬ EscG D L := by
  by_contra hc
  rw [muG, ite_eq_left (by tauto)] at h
  exact lt_irrefl _ h

variable {D φ}

section Step

variable {L : Log} {q : ByteArray} {a : Digest}

/-- The sum over the chains of an extended (non-bad) log: the old chains, then the new entry. -/
theorem sumG_append (hb : ¬ Bad (L ++ [(q, a)])) :
    sumG φ (L ++ [(q, a)]) = ((chains L).map (termG φ (L ++ [(q, a)]))).sum +
      (if IsChain (L ++ [(q, a)]) L.length then termG φ (L ++ [(q, a)]) L.length else 0) := by
  rw [sumG, chains_append hb, List.map_append, List.sum_append]
  split_ifs <;> simp

/-- An escape after appending a non-bad entry is at the new entry. -/
theorem escG_append (hb : ¬ Bad (L ++ [(q, a)])) (he : ¬ EscG D L)
    (h : EscG D (L ++ [(q, a)])) :
    IsChain (L ++ [(q, a)]) L.length ∧
      EscAtG D L (entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length)) := by
  obtain ⟨j, hj, hesc⟩ := h
  rw [chains_append hb, List.mem_append] at hj
  rcases hj with hj | hj
  · have hjL : j < L.length := (mem_chains.mp hj).1
    rw [L₀_append hjL, entriesOf_pathOf_append hb hjL] at hesc
    exact absurd ⟨j, hj, hesc⟩ he
  · split_ifs at hj with hc
    · simp only [List.mem_singleton] at hj
      subst hj
      rw [L₀_new] at hesc
      exact ⟨hc, hesc⟩
    · simp at hj

/-- The new entry of a seed chain is charged nothing and cannot escape. -/
theorem new_seed (hseed : ∀ L₀ e, Matches [e] → φ L₀ [e] = 0) (hb : ¬ Bad (L ++ [(q, a)]))
    (hn : (stateIn q).bind (ansIdx L) = none) (hc : IsChain (L ++ [(q, a)]) L.length) :
    termG φ (L ++ [(q, a)]) L.length = 0 ∧
      ¬ EscAtG D L (entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length)) := by
  classical
  have hpath := back_new hb
  rw [hn] at hpath
  have hes : entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length) = [(q, a)] := by
    rw [hpath]; simp [entriesOf]
  have hm := hc.2
  rw [hes] at hm
  refine ⟨?_, ?_⟩
  · unfold termG; rw [hes, hseed _ _ hm]; simp
  · rw [hes]; rintro ⟨h2, -⟩; simp at h2

end Step

open Classical in
/-- **`muG_step`**: the contract's `step` law for the potential `muG D φ`, with error the H row's
`badCount / 2^256` plus `δ`, from the local inequality `hloc` on one chain `i` of a non-bad log and
one fresh query whose state is `i`'s answer, and `hseed`. -/
theorem muG_step (δ : ℝ≥0)
    (hseed : ∀ L₀ e, Matches [e] → φ L₀ [e] = 0)
    (hloc : ∀ (L : Log) (i : ℕ) (q : ByteArray), ¬ Bad L → IsChain L i →
      q ∉ L.map Prod.fst → stateIn q = some L[i]!.2 →
      ∑ a : Digest, (if Matches (entriesOf L (pathOf L i) ++ [(q, a)]) then
          (if EscAtG D L (entriesOf L (pathOf L i) ++ [(q, a)]) then 1 else 0) +
            φ L (entriesOf L (pathOf L i) ++ [(q, a)]) else 0) ≤
        2 ^ 256 * ((if q = squeezeQ L[i]!.2 then φ (L₀ L i) (entriesOf L (pathOf L i)) else 0) +
          δ))
    {L : Log} {q : ByteArray} (hl : L.length < logCap) (hμ : muG D φ L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG D φ (L ++ [(q, a)]) ≤
      (muG D φ L + ((badCount : ℝ≥0) / 2 ^ 256 + δ)) * 2 ^ 256 := by
  obtain ⟨hbL, heL⟩ := muG_lt_one D φ hμ
  have hX : muG D φ L = sumG φ L := by rw [muG, ite_eq_right (by tauto)]
  set X := sumG φ L with hXdef
  set B : ℝ≥0 := (badCount : ℝ≥0)
  obtain ⟨c, nt, hcX, hpt, hnt⟩ : ∃ (c : ℝ≥0) (nt : Digest → ℝ≥0), c ≤ X ∧
      (∀ a, ¬ Bad (L ++ [(q, a)]) → muG D φ (L ++ [(q, a)]) + c ≤ X + nt a) ∧
      ∑ a, nt a ≤ 2 ^ 256 * (c + δ) := by
    have hold : ∀ (c : ℝ≥0), (((chains L).map fun j =>
        if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0).sum = c) →
        ∀ a, ¬ Bad (L ++ [(q, a)]) →
          ((chains L).map (termG φ (L ++ [(q, a)]))).sum + c = X := by
      intro c hc a hb
      rw [← hc, ← List.sum_map_add, hXdef, sumG]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact termG_append hq hb (mem_chains.mp hj).1
    cases hi : (stateIn q).bind (ansIdx L) with
    | none =>
      refine ⟨0, fun _ => 0, zero_le, fun a hb => ?_, by simp⟩
      have hc0 := sum_map_zero (l := chains L) (fun j =>
          if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0)
        (fun j hj => by
          have hjL := (mem_chains.mp hj).1
          rw [ite_eq_right]
          intro hs
          rw [istar_of_squeeze hbL hjL hs] at hi
          cases hi)
      have hsum := hold 0 hc0 a hb
      have hesc : ¬ EscG D (L ++ [(q, a)]) := fun h => by
        obtain ⟨hc, hesc⟩ := escG_append hb heL h
        exact (new_seed hseed hb hi hc).2 hesc
      rw [muG, ite_eq_right (by tauto), sumG_append hb, add_zero, add_zero]
      split_ifs with hc
      · rw [(new_seed (D := D) hseed hb hi hc).1, add_zero, ← hsum, add_zero]
      · rw [add_zero, ← hsum, add_zero]
    | some i =>
      obtain ⟨hiL, hst⟩ := lt_of_ansIdx hi
      set es := entriesOf L (pathOf L i) with hes
      let c : ℝ≥0 := if IsChain L i ∧ q = squeezeQ L[i]!.2 then φ (L₀ L i) es else 0
      let nt : Digest → ℝ≥0 := fun a => if Matches (es ++ [(q, a)]) then
          (if EscAtG D L (es ++ [(q, a)]) then 1 else 0) + φ L (es ++ [(q, a)]) else 0
      have hc : ((chains L).map fun j =>
          if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0).sum = c := by
        rw [sum_map_single (chains_nodup L) _ i]
        · by_cases h1 : IsChain L i
          · rw [ite_eq_left (mem_chains.mpr h1)]; simp only [c, h1, true_and]; rfl
          · rw [ite_eq_right (fun h => h1 (mem_chains.mp h))]; simp only [c, h1, false_and]; rfl
        · intro j hj hji
          have hjL := (mem_chains.mp hj).1
          rw [ite_eq_right]
          intro hs
          rw [istar_of_squeeze hbL hjL hs] at hi
          exact hji (Option.some.inj hi)
      refine ⟨c, nt, ?_, fun a hb => ?_, ?_⟩
      · simp only [c]
        split_ifs with hh
        · obtain ⟨hci, hs⟩ := hh
          have hmem : L[i]! ∈ L := by rw [getElem!_pos L i hiL]; exact List.getElem_mem hiL
          have hterm : termG φ L i = φ (L₀ L i) es := by
            unfold termG; rw [ite_eq_left ⟨hmem, hs ▸ hq⟩]
          rw [← hterm, hXdef, sumG]
          exact List.single_le_sum (fun _ _ => zero_le) _
            (List.mem_map_of_mem (mem_chains.mpr hci))
        · exact zero_le
      · have hsum := hold c hc a hb
        have hesn := entriesOf_new hb hi
        have hnew : (if EscG D (L ++ [(q, a)]) then 1 else 0) +
            (if IsChain (L ++ [(q, a)]) L.length then termG φ (L ++ [(q, a)]) L.length else 0) ≤
            nt a := by
          by_cases hc' : IsChain (L ++ [(q, a)]) L.length
          · have hm : Matches (es ++ [(q, a)]) := by have := hc'.2; rwa [hesn] at this
            simp only [nt, ite_eq_left hm, ite_eq_left hc']
            gcongr
            · split_ifs with h1 h2 h2
              · exact le_rfl
              · obtain ⟨-, h3⟩ := escG_append hb heL h1
                rw [hesn] at h3
                exact absurd h3 h2
              · exact zero_le
              · exact le_rfl
            · unfold termG
              rw [L₀_new, hesn]
              split_ifs
              · exact le_rfl
              · exact zero_le
          · have : ¬ EscG D (L ++ [(q, a)]) := fun h => hc' (escG_append hb heL h).1
            simp [this, hc']
        calc muG D φ (L ++ [(q, a)]) + c
            ≤ ((if EscG D (L ++ [(q, a)]) then 1 else 0) + sumG φ (L ++ [(q, a)])) + c := by
              gcongr
              rw [muG]
              split_ifs with h1 h2
              · exact le_add_right le_rfl
              · tauto
              · tauto
              · exact le_add_self
          _ = ((chains L).map (termG φ (L ++ [(q, a)]))).sum + c +
                ((if EscG D (L ++ [(q, a)]) then 1 else 0) +
                  (if IsChain (L ++ [(q, a)]) L.length then termG φ (L ++ [(q, a)]) L.length
                    else 0)) := by rw [sumG_append hb]; ring
          _ ≤ X + nt a := by rw [hsum]; gcongr
      · by_cases hci : IsChain L i
        · have hloc' := hloc L i q hbL hci hq hst
          have hcc : c = if q = squeezeQ L[i]!.2 then φ (L₀ L i) es else 0 := by
            simp only [c, hci, true_and]
          rw [hcc]
          exact hloc'
        · have : ∀ a, nt a = 0 := fun a => by
            simp only [nt]
            rw [ite_eq_right]
            intro hm
            exact hci ⟨hiL, matches_of_append (by
              rw [← List.length_pos_iff, length_entriesOf, List.length_pos_iff]
              exact pathOf_ne_nil L i) hm⟩
          simp [this]
  have hpt' : ∀ a, muG D φ (L ++ [(q, a)]) ≤
      (if Bad (L ++ [(q, a)]) then 1 else 0) + ((X - c) + nt a) := by
    intro a
    by_cases hb : Bad (L ++ [(q, a)])
    · rw [muG, ite_eq_left (Or.inl hb), ite_eq_left hb]; exact le_self_add
    · rw [ite_eq_right hb, zero_add]
      have h := hpt a hb
      have : (X - c) + c = X := tsub_add_cancel_of_le hcX
      rw [← this, add_assoc, add_comm c, ← add_assoc] at h
      exact le_of_add_le_add_right h
  calc ∑ a : Digest, muG D φ (L ++ [(q, a)])
      ≤ ∑ a : Digest, ((if Bad (L ++ [(q, a)]) then 1 else 0) + ((X - c) + nt a)) :=
        Finset.sum_le_sum fun a _ => hpt' a
    _ = (∑ a : Digest, (if Bad (L ++ [(q, a)]) then 1 else 0 : ℝ≥0)) + 2 ^ 256 * (X - c) +
          ∑ a, nt a := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          fintype_card_digest, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ B + 2 ^ 256 * (X - c) + 2 ^ 256 * (c + δ) := by
        gcongr
        exact card_bad_le hbL hq hl
    _ = (muG D φ L + (B / 2 ^ 256 + δ)) * 2 ^ 256 := by
        rw [hX, add_mul, add_mul, div_mul_cancel₀ _ (by positivity)]
        have : (X - c) + c = X := tsub_add_cancel_of_le hcX
        calc B + 2 ^ 256 * (X - c) + 2 ^ 256 * (c + δ)
            = B + 2 ^ 256 * ((X - c) + c) + 2 ^ 256 * δ := by ring
          _ = X * 2 ^ 256 + (B + δ * 2 ^ 256) := by rw [this]; ring

end Potential

section Local

/-- **`Matches` extends exactly by the next item, linked to the last answer.** -/
theorem matches_append_iff {es : Log} (hm : Matches es) (x : ByteArray × Digest) :
    Matches (es ++ [x]) ↔ ∃ hl : es.length < FsSeq.fs.length,
      stateIn x.1 = some (lastAns es) ∧ fsCheck (FsSeq.fs[es.length]'hl) x.1 = true := by
  have hne := matches_ne_nil hm
  have hpos : 0 < es.length := List.length_pos_iff.mpr hne
  have hla : lastAns es = es[es.length - 1].2 := by
    simp [lastAns, List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show es.length - 1 < es.length by omega)]
  constructor
  · rintro ⟨-, hl, H⟩
    have hl' : es.length < FsSeq.fs.length := by simp at hl; omega
    obtain ⟨h1, h2⟩ := H (es.length - 1) (by simp; omega)
    have hx : (es ++ [x])[es.length - 1 + 1]'(by simp; omega) = x := by
      simp [show es.length - 1 + 1 = es.length by omega]
    have hy : (es ++ [x])[es.length - 1]'(by
        simp only [List.length_append, List.length_singleton]; omega) =
        es[es.length - 1] :=
      List.getElem_append_left _
    have hf : FsSeq.fs[es.length - 1 + 1]'(by omega) = FsSeq.fs[es.length]'hl' := by
      congr 1; omega
    rw [hx, hy] at h1; rw [hx, hf] at h2
    exact ⟨hl', by rw [hla]; exact h1, h2⟩
  · rintro ⟨hl, hs, hc⟩
    refine matches_append hm hl ⟨es[es.length - 1], ?_, by rw [hs, hla]⟩ hc
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem]

/-- On the squeeze positions after `s0`, a matching chain is the formal extension of its first
`s0 + 1` entries by its later answers. -/
theorem ext_take {es : Log} (hm : Matches es) {s0 : ℕ} (hs : s0 < es.length)
    (hsq : ∀ p, s0 < p → p < es.length → FsSeq.fs[p]? = some .squeeze) :
    es = ext (es.take (s0 + 1)) ((es.drop (s0 + 1)).map Prod.snd) := by
  obtain ⟨-, hl, H⟩ := hm
  suffices Hk : ∀ k, s0 + 1 + k ≤ es.length →
      es.take (s0 + 1 + k) = ext (es.take (s0 + 1)) (((es.take (s0 + 1 + k)).drop (s0 + 1)).map
        Prod.snd) by
    have := Hk (es.length - (s0 + 1)) (by omega)
    rwa [show s0 + 1 + (es.length - (s0 + 1)) = es.length by omega, List.take_length] at this
  intro k
  induction k with
  | zero => intro _; simp [ext]
  | succ k ih =>
    intro hk
    have hn : s0 + 1 + k < es.length := by omega
    rw [show s0 + 1 + (k + 1) = s0 + 1 + k + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem hn, Option.toList_some, List.drop_append_of_le_length
        (by simp; omega), List.map_append, List.map_cons, List.map_nil, ext_append, ← ih (by omega)]
    simp only [ext1]
    congr 1
    obtain ⟨hst, hck⟩ := H (s0 + k) (by omega)
    have hsqk := hsq (s0 + k + 1) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hsqk
    rw [hsqk] at hck
    have hla : lastAns (es.take (s0 + 1 + k)) = es[s0 + k].2 := by
      rw [lastAns, List.getLast?_eq_getElem?, List.length_take,
        show min (s0 + 1 + k) es.length - 1 = s0 + k by omega, List.getElem?_take_of_lt
          (by omega), List.getElem?_eq_getElem (by omega)]
      rfl
    rw [hla, ← eq_squeezeQ hck hst]
    have heq : es[s0 + k + 1]'(by omega) = es[s0 + 1 + k] := by congr 1; omega
    rw [heq]

/-- **The multi-squeeze phases**: `rnd p = some (s0, r)` places position `p` among the `r` squeezes
after the entry `s0`, and every position of the phase is a squeeze of the same phase. -/
def RndOK (rnd : ℕ → Option (ℕ × ℕ)) : Prop :=
  ∀ p s0 r, rnd p = some (s0, r) → s0 < p ∧ p ≤ s0 + r ∧
    ∀ p', s0 < p' → p' ≤ s0 + r → FsSeq.fs[p']? = some .squeeze ∧ rnd p' = some (s0, r)

variable (D : Log → Log → Prop) (rnd : ℕ → Option (ℕ × ℕ))

variable {D rnd}

open Classical in
/-- **`hloc_of`**: `muG_step`'s local inequality for the charge `pRoundG D rnd`, from
* `habs`: an absorb never undooms;
* `hmid`: a middle answer of a multi-squeeze phase neither dooms nor undooms;
* `hsingle`: a single squeeze escapes on at most `N ≤ 2^256 δ` answers;
* `hround`: a multi-squeeze phase's escape count from its entry is at most `δ`;
* `hstab`: on a non-bad log, `D` reads the same off the log before a chain's last entry and off the
  whole log, on the formal extensions inside a multi-squeeze phase (`StabExt`). -/
theorem hloc_of (hrnd : RndOK rnd) (δ : ℝ≥0) (N : ℕ) (hN : (N : ℝ≥0) ≤ 2 ^ 256 * δ)
    (habs : ∀ L es x len, Matches (es ++ [x]) → FsSeq.fs[es.length]? = some (.absorb len) →
      D L es → D L (es ++ [x]))
    (hmid : ∀ L es x s0 r, Matches (es ++ [x]) → rnd es.length = some (s0, r) →
      es.length < s0 + r → (D L (es ++ [x]) ↔ D L es))
    (hsingle : ∀ L es, Matches es → FsSeq.fs[es.length]? = some .squeeze → rnd es.length = none →
      (Finset.univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card ≤ N)
    (hround : ∀ L es₀ s0 r, Matches es₀ → es₀.length = s0 + 1 →
      rnd (s0 + 1) = some (s0, r) → condCount D L es₀ r [] ≤ δ)
    (hstab : ∀ L i, ¬ Bad L → IsChain L i → ∀ X, StabExt rnd (entriesOf L (pathOf L i)) X →
      (D (L.take i) X ↔ D L X))
    (L : Log) (i : ℕ) (q : ByteArray) (hb : ¬ Bad L) (hci : IsChain L i)
    (hst : stateIn q = some L[i]!.2) :
    ∑ a : Digest, (if Matches (entriesOf L (pathOf L i) ++ [(q, a)]) then
        (if EscAtG D L (entriesOf L (pathOf L i) ++ [(q, a)]) then 1 else 0) +
          pRoundG D rnd L (entriesOf L (pathOf L i) ++ [(q, a)]) else 0) ≤
      2 ^ 256 * ((if q = squeezeQ L[i]!.2 then
        pRoundG D rnd (L₀ L i) (entriesOf L (pathOf L i)) else 0) + δ) := by
  have hstab' := hstab L i hb hci
  generalize hes : entriesOf L (pathOf L i) = es at hstab' ⊢
  have hm : Matches es := hes ▸ hci.2
  have hla : lastAns es = L[i]!.2 := lastAns_of_getLast? (hes ▸ entriesOf_getLast? L i)
  have hne := matches_ne_nil hm
  have hp1 : 1 ≤ es.length := List.length_pos_iff.mpr hne
  have hlen : ∀ x : ByteArray × Digest, (es ++ [x]).length - 1 = es.length := fun x => by simp
  by_cases hex : ∃ hl : es.length < FsSeq.fs.length, fsCheck (FsSeq.fs[es.length]'hl) q = true
  swap
  · have : ∀ a, ¬ Matches (es ++ [(q, a)]) := fun a h => by
      obtain ⟨hl, -, hc⟩ := (matches_append_iff hm _).mp h; exact hex ⟨hl, hc⟩
    simp only [this, ite_false, Finset.sum_const_zero]; exact zero_le
  obtain ⟨hl, hc⟩ := hex
  have hM : ∀ a, Matches (es ++ [(q, a)]) := fun a =>
    (matches_append_iff hm _).mpr ⟨hl, by rw [hla]; exact hst, hc⟩
  simp only [hM, ite_true]
  have hit : FsSeq.fs[es.length]? = some (FsSeq.fs[es.length]'hl) := List.getElem?_eq_getElem hl
  have hpr0 : ∀ L₁ x, rnd es.length = none → pRoundG D rnd L₁ (es ++ [x]) = 0 := by
    intro L₁ x hr; unfold pRoundG; rw [hlen, hr]
  rcases fsCheck_absorb_or hc with h | h | ⟨len, h⟩
  · rw [h] at hc; rw [stateIn_of_seed hc] at hst; cases hst
  · -- a squeeze
    rw [h] at hc hit
    have hq : q = squeezeQ L[i]!.2 := eq_squeezeQ hc hst
    subst hq
    rw [ite_eq_left rfl]
    have hext1 : ∀ a, es ++ [(squeezeQ L[i]!.2, a)] = ext1 es a := fun a => by rw [ext1, hla]
    cases hr : rnd es.length with
    | none =>
      calc ∑ a, ((if EscAtG D L (es ++ [(squeezeQ L[i]!.2, a)]) then 1 else 0) +
              pRoundG D rnd L (es ++ [(squeezeQ L[i]!.2, a)]))
          ≤ ∑ a, (if D L es ∧ ¬ D L (ext1 es a) then 1 else 0 : ℝ≥0) := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [hpr0 _ _ hr, add_zero]
            split_ifs with h1 h2 h2
            · exact le_rfl
            · exfalso; obtain ⟨-, hd, hnd⟩ := h1
              rw [List.dropLast_concat, hext1] at *
              exact h2 ⟨hd, hnd⟩
            · exact zero_le
            · exact le_rfl
        _ = ((Finset.univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card : ℝ≥0) := by
            rw [Finset.sum_boole]
        _ ≤ N := by exact_mod_cast hsingle L es hm hit hr
        _ ≤ 2 ^ 256 * δ := hN
        _ ≤ 2 ^ 256 * (pRoundG D rnd (L₀ L i) es + δ) := by gcongr; exact le_add_self
    | some sr =>
      obtain ⟨s0, r⟩ := sr
      obtain ⟨hs0, hpr, hspec⟩ := hrnd _ _ _ hr
      have hes' : es = ext (es.take (s0 + 1)) ((es.drop (s0 + 1)).map Prod.snd) :=
        ext_take hm (by omega) (fun p h1 h2 => (hspec p h1 (by omega)).1)
      have hes0len : (es.take (s0 + 1)).length = s0 + 1 := by simp; omega
      have hnew : ∀ a, es ++ [(squeezeQ L[i]!.2, a)] =
          ext (es.take (s0 + 1)) ((es.drop (s0 + 1)).map Prod.snd ++ [a]) := by
        intro a; rw [ext_append, ← hes', hext1]
      have hterm : ∀ a, (if EscAtG D L (es ++ [(squeezeQ L[i]!.2, a)]) then 1 else 0) +
          pRoundG D rnd L (es ++ [(squeezeQ L[i]!.2, a)]) =
          condCount D L (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd ++ [a]) := by
        intro a
        have hpRnew : pRoundG D rnd L (es ++ [(squeezeQ L[i]!.2, a)]) =
            if es.length - s0 < r then
              condCount D L (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd ++ [a])
            else 0 := by
          unfold pRoundG
          rw [hlen, hr]
          simp only
          rw [List.take_append_of_le_length (by omega),
            List.drop_append_of_le_length (by omega), List.map_append]
          rfl
        by_cases hmidp : es.length < s0 + r
        · rw [ite_eq_right, zero_add, hpRnew, ite_eq_left (by omega)]
          rintro ⟨-, hd, hnd⟩
          rw [List.dropLast_concat] at hd
          exact hnd ((hmid L es _ s0 r (hM _) hr hmidp).mpr hd)
        · rw [hpRnew, ite_eq_right (show ¬ (es.length - s0 < r) by omega), add_zero,
            condCount_last D _ _ (by simp; omega), hnew]
      rw [Finset.sum_congr rfl (fun a _ => hterm a), condCount_split D _ _ (by simp; omega)]
      gcongr
      by_cases hfirst : es.length = s0 + 1
      · have htk : es.take (s0 + 1) = es := List.take_of_length_le (by omega)
        have hpre : (es.drop (s0 + 1)).map Prod.snd = [] := by
          rw [List.drop_of_length_le (by omega)]; rfl
        rw [hpre]
        refine le_trans ?_ le_add_self
        refine hround L _ s0 r (by rw [htk]; exact hm) hes0len ?_
        exact (hspec (s0 + 1) (by omega) (by omega)).2
      · -- the charge before the new answer, read off the charging log (`hstab`)
        have hcc : condCount D L (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd) =
            condCount D (L₀ L i) (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd) := by
          have hX : ∀ as', as'.length ≤ r →
              (D L (ext (es.take (s0 + 1)) as') ↔ D (L₀ L i) (ext (es.take (s0 + 1)) as')) :=
            fun as' h => (hstab' _ ⟨s0, r, as', (hspec (s0 + 1) (by omega) (by omega)).2,
              by omega, h, rfl⟩).symm
          have hpl : ((es.drop (s0 + 1)).map Prod.snd).length = es.length - (s0 + 1) := by simp
          unfold condCount extCount
          congr 3
          refine Finset.filter_congr fun v _ => ?_
          set as := (es.drop (s0 + 1)).map Prod.snd ++ List.ofFn v with has
          have hal : as.length = r := by
            rw [has, List.length_append, List.length_ofFn, hpl]; omega
          have hne : as ≠ [] := by
            intro h; rw [h] at hal; simp at hal; omega
          simp only [EscAtG]
          rw [ext_dropLast _ hne, hX _ hal.le, hX _ (by simp; omega)]
        have hp : pRoundG D rnd (L₀ L i) es =
            condCount D (L₀ L i) (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd) := by
          unfold pRoundG
          rw [(hspec (es.length - 1) (by omega) (by omega)).2]
          simp only
          rw [ite_eq_left (by omega)]
        rw [hcc, hp]; exact le_self_add
  · -- an absorb: no escape, no charge
    rw [h] at hit
    have hr : rnd es.length = none := by
      cases hr : rnd es.length with
      | none => rfl
      | some sr =>
        obtain ⟨h1, h2, hs⟩ := hrnd _ _ _ hr
        rw [(hs _ h1 h2).1] at hit; cases hit
    have hz : ∀ a, (if EscAtG D L (es ++ [(q, a)]) then 1 else 0) +
        pRoundG D rnd L (es ++ [(q, a)]) = (0 : ℝ≥0) := by
      intro a
      rw [hpr0 _ _ hr, add_zero, ite_eq_right]
      rintro ⟨-, hd, hnd⟩
      rw [List.dropLast_concat] at hd
      exact hnd (habs L es _ len (hM a) hit hd)
    simp only [hz, Finset.sum_const_zero]; exact zero_le

open Classical in
/-- **`muG_step_of`**: the contract's `step` law for `muG D (pRoundG D rnd)` from the per-position
facts of `hloc_of` (`rnd 0 = none`: the seed is in no phase). -/
theorem muG_step_of (hrnd : RndOK rnd) (h0 : rnd 0 = none) (δ : ℝ≥0) (N : ℕ)
    (hN : (N : ℝ≥0) ≤ 2 ^ 256 * δ)
    (habs : ∀ L es x len, Matches (es ++ [x]) → FsSeq.fs[es.length]? = some (.absorb len) →
      D L es → D L (es ++ [x]))
    (hmid : ∀ L es x s0 r, Matches (es ++ [x]) → rnd es.length = some (s0, r) →
      es.length < s0 + r → (D L (es ++ [x]) ↔ D L es))
    (hsingle : ∀ L es, Matches es → FsSeq.fs[es.length]? = some .squeeze → rnd es.length = none →
      (Finset.univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card ≤ N)
    (hround : ∀ L es₀ s0 r, Matches es₀ → es₀.length = s0 + 1 →
      rnd (s0 + 1) = some (s0, r) → condCount D L es₀ r [] ≤ δ)
    (hstab : ∀ L i, ¬ Bad L → IsChain L i → ∀ X, StabExt rnd (entriesOf L (pathOf L i)) X →
      (D (L.take i) X ↔ D L X))
    {L : Log} {q : ByteArray} (hl : L.length < logCap) (hμ : muG D (pRoundG D rnd) L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG D (pRoundG D rnd) (L ++ [(q, a)]) ≤
      (muG D (pRoundG D rnd) L + ((badCount : ℝ≥0) / 2 ^ 256 + δ)) * 2 ^ 256 :=
  muG_step δ (fun L₀ e _ => pRoundG_seed D rnd L₀ e h0)
    (fun L i q hb hci _ hst => hloc_of hrnd δ N hN habs hmid hsingle hround hstab L i q hb hci hst)
    hl hμ hq

end Local

end FR.Snd.G

end

end G6_FRSoundnessCoreChain

section G6_FRSoundness4Pos

-- New for `flock-recursive` (BLUEPRINT A.4, B-12, B-13, §5.1; stage S-G13, route C2): the
-- revision 4.1 chain's positions and kinds. `FRSoundnessStepA`/`FRSoundnessDefs` Part D are the
-- 3.x templates (`fsStarts`, `phStart`, `fsRanges`, `fsRnd`, `kindOf`).
-- RET-2: import re-pointed at Core: `FRSoundnessFrChain` → `FRSoundnessCoreChain`, `FRSoundnessStepA` → `FRSoundnessCoreTruths`.

/-!
# Revision 4.1's chains: the item list `fsItems4`, the phase starts, the multi-squeeze phases, the kind

All six SNARK programs of revision 4.1 ask one item sequence, `itemsOf seq4` (S-0′). Its
Fiat–Shamir items (486 since revision 4.4.1's cap check, (β′)) are **`fsItems4`**, and **`fsSeq4`** makes
them the chains' list for the generic potential (`FRSoundnessFrChain`).

* **Phase starts** (`fsStarts4`, `phStart4 k`): the Fiat–Shamir position of phase `k`'s first item,
  `fsStarts4_eq` pins them. They are 3.x's (`fsStarts_eq`) up to `Lr1` (phases 0–13, positions
  0 … 170) and then shift by `+1` (`Lr2`), `+5` (`Lrend`, `Lr3`, `E1`), `+6` (`E2`), `+10`
  (`Eend`, `E3`, `E4`) and `+14` (`E4end` … `Pf`): `Lr1` has 9 squeezes, `Lr2` 17 rounds, `E1` 12
  squeezes, `E2` 23 rounds, `E4` 25 rounds (`phStart4_shift`).
* **Multi-squeeze phases** (`fsRanges4`, `fsRnd4`), with **`fsRnd4_ok : RndOK fsRnd4`** (checked).
* **The chain's kind** (`CKind`, `kindOfC es`): byte 71 of the seed query (`hdr`'s first byte),
  one of the six SNARK kinds; `L32` if it is not one. Its `m`, `isNode`, and ladder `lvC κ i =
  lvOf κ.m i = seq4.lvK κ.m i` (revision 4.4.1: level 4's cap at depth 8).
-/

namespace FR.Snd
open RecursionFast FR.Rev4

/-! ## The item list -/

/-- **`seq4`'s Fiat–Shamir items**: the item sequence without the column and node queries. -/
def fsItems4 : List Item := (itemsOf seq4).filter Item.isFS

theorem fsItems4_length : fsItems4.length = 486 := by
  rw [fsItems4, seq4_eq]; decide +kernel

/-- **The chains of revision 4.1** follow `fsItems4`. -/
instance fsSeq4 : G.FsSeq := ⟨fsItems4, by rw [fsItems4_length]; decide⟩

theorem fs_eq4 : G.FsSeq.fs = fsItems4 := rfl

/-! ## Phase starts -/

/-- The Fiat–Shamir position of each phase's first item, in the order of `phasesOf seq4`. -/
def fsStarts4 : List ℕ :=
  ((phasesOf seq4).foldl (fun (acc : ℕ × List ℕ) p =>
    (acc.1 + ((p.2.itemsL seq4.lv).filter Item.isFS).length, acc.2 ++ [acc.1])) (0, [])).2

/-- The first Fiat–Shamir position of phase `k` of `phasesOf seq4`. -/
def phStart4 (k : ℕ) : ℕ := fsStarts4.getD k 0

/-- **The phase starts** (phases `0 … 25` the PIOP, level `i`'s `P1, C, P2, Q, P3` are
`26 + 5i … 30 + 5i`, `Pf` is `51`; revision 4.4.1 (β′): `CapD` `52` at 482, `CapZeta` `53` at 483,
`CapChk` `54` at 484, `CapChkZ` `55` at 485). -/
theorem fsStarts4_eq : fsStarts4 = [0, 1, 2, 3, 13, 15, 67, 68, 69, 97, 98, 99, 114, 170, 179, 213,
    214, 215, 227, 273, 274, 275, 325, 326, 327, 331, 332, 344, 345, 370, 370, 375, 383, 384, 397,
    397, 402, 410, 411, 421, 421, 426, 434, 435, 443, 443, 448, 456, 457, 463, 463, 468, 482,
    483, 484, 485] := by
  rw [fsStarts4, seq4_eq]; decide +kernel

/-- **Against 3.x**: the same starts through `Lr1` (phase 13), then the shifts `+1`, `+5`, `+6`,
`+10`, `+14`. -/
theorem phStart4_shift :
    (∀ k < 14, phStart4 k = phStart k) ∧ phStart4 14 = phStart 14 + 1 ∧
    (∀ k, 15 ≤ k → k < 18 → phStart4 k = phStart k + 5) ∧ phStart4 18 = phStart 18 + 6 ∧
    (∀ k, 19 ≤ k → k < 22 → phStart4 k = phStart k + 10) ∧
    (∀ k, 22 ≤ k → k < 52 → phStart4 k = phStart k + 14) := by
  have h4 : ∀ k, phStart4 k = fsStarts4.getD k 0 := fun _ => rfl
  have h3 : ∀ k, phStart k = fsStarts.getD k 0 := fun _ => rfl
  simp only [h4, h3, fsStarts4_eq, fsStarts_eq]
  refine ⟨by decide, rfl, by decide, rfl, by decide, by decide⟩

/-- The phase of a position: the last phase starting at or before it. -/
def phOf4 (q : ℕ) : ℕ := (fsStarts4.filter (· ≤ q)).length - 1

/-! ## Multi-squeeze phases -/

/-- The multi-squeeze phases as `(s0, r)`: `r ≥ 2` squeezes after the Fiat–Shamir entry `s0`. -/
def fsRanges4 : List (ℕ × ℕ) :=
  ((phasesOf seq4).foldl (fun (acc : ℕ × List (ℕ × ℕ)) p =>
    let n := ((p.2.itemsL seq4.lv).filter Item.isFS).length
    match p.2 with
    | .squeezes k _ => if 2 ≤ k then (acc.1 + n, acc.2 ++ [(acc.1 - 1, k)]) else (acc.1 + n, acc.2)
    | _ => (acc.1 + n, acc.2)) (0, [])).2

/-- The multi-squeeze phase of a Fiat–Shamir position. -/
def fsRnd4 (p : ℕ) : Option (ℕ × ℕ) := fsRanges4.find? fun x => decide (x.1 < p ∧ p ≤ x.1 + x.2)

/-- The phases' positions are squeezes, each in its own phase (checked). -/
def rangesOK4 : Bool :=
  fsRanges4.all fun x => (List.range x.2).all fun j =>
    fsItems4[x.1 + 1 + j]? == some .squeeze && fsRnd4 (x.1 + 1 + j) == some x

theorem rangesOK4_eq : rangesOK4 = true := by
  decide +kernel

/-- The 15 multi-squeeze phases (Z1 after `cap0`, S1, Lr1, E1, RS1, then P2 and P3 of each
level). Against 3.x (`fsRanges_eq`): `Lr1` 9 squeezes, `E1` 12, everything after `Lr1` moved. -/
theorem fsRanges4_eq : fsRanges4 = [(2, 10), (98, 15), (169, 9), (214, 12), (326, 4), (344, 25),
    (369, 5), (383, 13), (396, 5), (410, 10), (420, 5), (434, 8), (442, 5), (456, 6),
    (462, 5)] := by
  rw [fsRanges4, seq4_eq]; decide +kernel

theorem fsRnd4_zero : fsRnd4 0 = none := by
  unfold fsRnd4; rw [List.find?_eq_none]; intro x _; simp

/-- **`fsRnd4_ok`**: `fsRnd4` satisfies `RndOK` over `fsItems4`. -/
theorem fsRnd4_ok : G.RndOK fsRnd4 := by
  intro p s0 r h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  refine ⟨hp.1, hp.2, fun p' h1 h2 => ?_⟩
  have hall := rangesOK4_eq
  simp only [rangesOK4, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hall
  have := hall _ hmem (p' - (s0 + 1)) (by omega)
  rwa [show s0 + 1 + (p' - (s0 + 1)) = p' by omega] at this

/-! ## The chain's kind -/

/-- **The six SNARK kinds of revision 4.1** (a chain's kind; the aggregate `A` has no chain of its
own: its segments' chains are segment chains). -/
inductive CKind where
  | seg (κ : SegKind)
  | node (κ : NodeKind)
  deriving DecidableEq, Repr

namespace CKind

def byte : CKind → UInt8
  | seg κ => κ.byte | node κ => κ.byte

def m : CKind → ℕ
  | seg κ => κ.m | node κ => κ.m

def isNode : CKind → Bool
  | seg _ => false | node _ => true

/-- The kind of a kind byte (segment bytes first). -/
def ofByte? (b : UInt8) : Option CKind :=
  match SegKind.ofByte? b with
  | some κ => some (seg κ)
  | none => (NodeKind.ofByte? b).map node

theorem ofByte?_byte (κ : CKind) : ofByte? κ.byte = some κ := by
  cases κ with
  | seg κ => cases κ <;> decide
  | node κ => cases κ <;> decide

/-- Level `i` of the kind's ladder in `seq4` (revision 4.4.1: level 4's cap at depth 8, PACK-4.4
§11.2 L2; `= lvOf κ.m i` by definition). -/
def lv (κ : CKind) (i : ℕ) : Level := seq4.lvK κ.m i

theorem m_mem (κ : CKind) : κ.m = 30 ∨ κ.m = 31 ∨ κ.m = 32 := by
  rcases κ with κ | κ <;> cases κ <;> decide

end CKind

/-- **The kind of a chain**: byte 71 of its seed query (`"FRSEED0" ‖ vk ‖ c ‖ hdr`, `hdr`'s first
byte); `L32` if it is not a kind byte. -/
def kindOfC (es : Log) : CKind := (((entAt es 0).1.data[71]?).bind CKind.ofByte?).getD (.seg .L32)

theorem kindOfC_congr {es es' : Log} (h : Agree es es' 1) : kindOfC es = kindOfC es' := by
  simp only [kindOfC, h 0 one_pos]

/-! ## Controls -/

/-- (+) A seed query matches `fsItems4` (the first item is the seed). -/
theorem matches4_seed (vk c : Digest) (hdr : ByteArray) (hh : hdr.size = 48) (a : Digest) :
    G.Matches [(seedQ vk c hdr, a)] := by
  have h := matches_seed vk c hdr hh a
  exact ⟨h.1, by simp [fs_eq4, fsItems4_length], fun i hi => by simp at hi⟩

/-- (−) A chain of one squeeze does not match (it does not start at a seed). -/
theorem not_matches4_squeeze (st a : Digest) : ¬ G.Matches [(squeezeQ st, a)] := fun h =>
  not_matches_squeeze st a ⟨h.1, by simpa using one_le_fsItems, fun i hi => by simp at hi⟩

/-- (−) `fsItems4` is not 3.x's list: the instance changes what a chain is. -/
theorem fsItems4_ne : fsItems4 ≠ fsItems := fun h => by
  have := congrArg List.length h
  rw [fsItems4_length] at this
  exact absurd this (by rw [show fsItems.length = 468 from FR.fsItems_length]; decide)

/-- (+/−) The kind byte decides the chain's kind; a non-kind byte gives the default `L32`. -/
theorem kindOfC_ctrl : CKind.ofByte? 0x4D = some (.node .N2) ∧ CKind.ofByte? 0x4B = some (.seg .L31) ∧
    CKind.ofByte? 0x41 = none ∧ kindOfC [] = .seg .L32 := by
  refine ⟨by decide, by decide, by decide, rfl⟩

end FR.Snd

end G6_FRSoundness4Pos
