-- New for `flock-recursive` (BLUEPRINT revision 4.0, B-11 … B-13, B-17; stage S-0′).
import FRFormat

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
  (`Seq.cap4`, lever L2; 3.x's `seq3` keeps 7); revision 4.4.2 (the reserve, D1p §3): `Lrend` 880 and
  `Eend` 112 bytes (`Seq.lrEnd`, `Seq.eEnd`, the previous node's `evalM` claim; no item added): 8,783
  items, `piSize` 876,176, a stream of `64 · 24,234` bytes; `4 × 8,783 + 3 ≤ qV = 36,000`.
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
  `seq4`: 880, the previous node's `evalM` claim `r̄*_x (23) ‖ r̄*_y (25) ‖ a* ‖ b* ‖ c* ‖ kindElem*`
  after the three values) and `Eend`'s (`fEEnd`; 3.x: 48; `seq4`: 112, `â_M ‖ b̂_M ‖ ĉ_M ‖ m̂* ‖ 0^48`).
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
    e4end := 32, capChk := true, cap4 := 8, lrEnd := 880, eEnd := 112 }

theorem seq3_eq : seq3 = ⟨32, 19, 26, 28, 15, 21, 23, 7, 32, 6, false, 7, 48, 48⟩ := by decide
theorem seq4_eq : seq4 = ⟨32, 19, 26, 28, 17, 23, 25, 7, 32, 6, true, 8, 880, 112⟩ := by decide

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
    800, 1344, 816, 880, 2336, 112, 8192, 2112, 672, 49152, 4096, 487504, 237632, 27872, 49152] := by
  rw [seq4_eq]; decide +kernel

theorem piSizeOf_seq4 : piSizeOf seq4 = 876176 := by rw [piSizeOf, fieldSizesOf_seq4]; rfl

theorem streamBytesOf_seq4 : streamBytesOf seq4 = 1550976 := by rw [seq4_eq]; decide +kernel

/-- The stream is `64 · chainLen` bytes: no padding cell (as INT-2's 3.x stream). -/
theorem chainLenOf_seq4 : chainLenOf seq4 = 24234 ∧ streamBytesOf seq4 = 64 * 24234 := by
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
