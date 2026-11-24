/-
# The lvm6 wire format: shapes, header, codec and schedule (WP S; `FORMAT6.md` v2.2 §1–§7, §S)

The data every implementation of the lvm6 verifier must agree on byte for byte (`FORMAT6.md`,
normative; **Category B**: transcribed, the Lean is wrong if it deviates from that file):

* the codec (§1): little-endian lanes, `E` scalars `c₀ ‖ c₁` (16 bytes), digests as 32 bytes;
* a parsed **view** of the header, `Hdr` (with `vk`), its bytes `hdrBytes`, the parser `parseHdr`,
  `HdrWF`, the statement `stmtOf` and the statement check `stmtOk` (§2): what `node6` reads. The
  scheme's statement is the header's **bytes** (V1's `Lvm6.V.scheme6V`: `hdr6`, `hdrOkWith`, `enc6`,
  `q06`, `magic6` are V1's and are not restated here);
* the challenge `chal6`, the proof-of-work lane `powLane` and the grind test `powOK6` (§4), tied to
  the scheme's `chalOf` (`e2OfE_chalOf`, `powOK6_iff`); the query positions `posOf` (§5);
* the schedule (§6) as a list of V1's `Item`s (`Lvm6.V.Item`, with `B` and `pos`), generated from a
  `Shape` record by `sched6`; the levels as V1's `Lev`s (`Shape.levs`); `toV sh`, the `VShape` the
  scheme walks. The counts are V1's: `qSOf` (queries, with `q₀` and the seed), `bodyLen`,
  `piLenOf`, the length rule `fsLenOK`. **`sched6_P18`** (in `Lvm6P18Park` since INT11, with `P18`'s other
  counts) proves `sched6 P18` equal to V1's `sched18` (its fixed parts `s61 … s66`), so there is one schedule.

`P18` is the season's shape, `T15` refv's three-level test shape (not normative; its Keccak
constants are `P18`'s, so only `shapeOK` holds for it, not `stackOK`). The sub-schedules of
`FORMAT6.md` §T and §6.4 (sponge caller and link, typed phases, mini-bus) are the four lists of a
`SubT` record carried by the `Shape`; `subT18` has them all frozen (sponge: CB's §T freeze; typed
phases and mini-bus: FORMAT6 v2.3 §6.4), and `P18.phiVars = 43` (v2.3: `κ ∈ E^2`, `r_x ∈ E^20`,
`r_y ∈ E^21`).

Deviations from the sketch in §S: the view's `Hdr.b`, `Hdr.n` are `UInt64` (the 8-byte fields);
`fsLenOK` takes the shape; `hdrOk`, `enc6`, `q06` are V1's, on header bytes.
-/
import Lvm6LeafBlock
import Lvm6VSpec
import Lvm6Params
import LvmFieldE2
import LvmE2Grind
import LvmCompileCodec
import RecursionFast.Library.Fast

set_option autoImplicit false

namespace Lvm6

open RecursionFast LeanVM.Parameters

/-! ## Codec (§1) -/

/-- Byte strings. -/
abbrev Bytes : Type := List UInt8

/-- A lane as 8 bytes, little-endian. -/
def le64 (w : UInt64) : Bytes := (List.range 8).map (byteOf w)

/-- An `E` scalar `c₀ + c₁·y` as 16 bytes: `c₀` then `c₁`. -/
def eBytes (y : E2) : Bytes := le64 (K.lane y.re) ++ le64 (K.lane y.im)

/-- The lane at byte offset `o` (bytes past the end read as zero). -/
def rdU64 (p : Bytes) (o : ℕ) : UInt64 := K.lane (Lvm.FS.kOfBytes (p.drop o))

/-- The `E` scalar at byte offset `o`. -/
def rdE (p : Bytes) (o : ℕ) : E2 := ⟨Lvm.FS.kOfBytes (p.drop o), Lvm.FS.kOfBytes (p.drop (o + 8))⟩

/-- The digest at byte offset `o`. -/
def rdD (p : Bytes) (o : ℕ) : Digest := Lvm.FS.dg (p.drop o)

/-! ## The header (§2) -/

/-- The zero digest (`c'` in leaf mode). -/
def zeroD : Digest := Vector.replicate 32 0

/-- **The header** of an `S` proof: the mode `b` (0 leaf, 1 node), the leaf size `n`, the data
root `h`, the left child's statement `c'` and the accumulator input `accIn = (pt, y)`. -/
structure Hdr where
  /-- `0`: leaf mode (step 1); `1`: node mode. -/
  b : UInt64
  /-- The number of blocks of the leaf's data. -/
  n : UInt64
  /-- The claimed data root. -/
  h : Digest
  /-- The left child's statement (zero in leaf mode). -/
  c' : Digest
  /-- The signer's public key (checked against `V_S`'s argument). -/
  vk : Digest
  /-- The accumulator input: a point of `E^v` and a value. -/
  accIn : List E2 × E2

/-- The header's bytes: magic, `b`, `n`, `h`, `c'`, `vk`, `pt`, `y` (`|HDR| = 136 + 16v`). -/
def hdrBytes (x : Hdr) : Bytes :=
  V.magic6 ++ le64 x.b ++ le64 x.n ++ x.h.toList ++ x.c'.toList ++ x.vk.toList ++
    x.accIn.1.flatMap eBytes ++
    eBytes x.accIn.2

/-- The statement a header proves: `L = leafStmt h n`, and `nodeStmt c' L` in node mode. -/
def stmtOf (x : Hdr) : Digest :=
  if x.b = 0 then leafStmtF x.h x.n.toNat else nodeStmtF x.c' (leafStmtF x.h x.n.toNat)

/-- **The statement check** of §2: `c` is the header's statement. -/
def stmtOk (c : Digest) (x : Hdr) : Bool := decide (c = stmtOf x)

/-! ## Challenges (§4, §5) -/

/-- **The challenge** of an answer: lanes 0 and 1 as `c₀ + c₁·y`. -/
def chal6 (a : Digest) : E2 := ⟨Lvm.FS.kOfBytes a.toList, Lvm.FS.kOfBytes (a.toList.drop 8)⟩

/-- The proof-of-work lane of an answer: lane 2 (bytes 16–23). -/
def powLane (a : Digest) : UInt64 := rdU64 a.toList 16

/-- **A ground group of grind `g` passes** on the answer `a`: its PoW lane is below `2^(64−g)`. -/
def powOK6 (g : ℕ) (a : Digest) : Bool := decide ((powLane a).toNat < 2 ^ (64 - g))

/-- The positions a draw gives at a level of `2^ht` positions: `N = c₀ + 2^64·c₁`, then
`(N >> (j·ht)) mod 2^ht` for `j < ⌊128/ht⌋`. -/
def posOf (ht : ℕ) (a : Digest) : List ℕ :=
  let N := (rdU64 a.toList 0).toNat + 2 ^ 64 * (rdU64 a.toList 8).toNat
  (List.range (128 / ht)).map fun j => N / 2 ^ (j * ht) % 2 ^ ht

/-! ## Shapes and the schedule (§5, §6) -/

/-- One WHIR level (§5 table, §6.6). -/
structure Level where
  /-- `2^ht` positions. -/
  ht : ℕ
  /-- The cap is `2^lv` nodes. -/
  lv : ℕ
  /-- The bytes of a leaf. -/
  leafB : ℕ
  /-- The number of openings. -/
  nOpen : ℕ
  /-- The fold rounds `ℓ` of the level. -/
  fold : ℕ
  /-- The grind of a fold round. -/
  gFold : ℕ
  /-- The grind of the OOD sample after this level's commitment. -/
  gOod : ℕ
  /-- The grind of the level's position draws. -/
  gQuery : ℕ
deriving Inhabited, DecidableEq, Repr

/-- The grinds of the round groups outside WHIR (`P.groups`); one record serves both Keccak
batches. -/
structure Grinds where
  /-- Tree wiring point `ρ`. -/
  rho : ℕ
  /-- Tree fold challenge `u`. -/
  u : ℕ
  /-- Segment and lane point. -/
  seg : ℕ
  /-- Layer point `s` (pack product). -/
  layer : ℕ
  /-- Eq-mode pack and segment rounds. -/
  eqR : ℕ
  /-- Plain position rounds. -/
  posR : ℕ
  /-- Layer challenge `β`. -/
  beta : ℕ
  /-- Middle-state opening rounds. -/
  outR : ℕ
  /-- Input opening rounds. -/
  inR : ℕ
  /-- WHIR tail rounds. -/
  tail : ℕ
deriving Inhabited, DecidableEq, Repr

/-- **A schedule item** (§6): V1's `Lvm6.V.Item` (`E k`, `K k`, `cap i`, `G g`, `D k`, the bind `B`,
the position group `pos i g` = `G(g)`, `D(draws − 1)` of level `i`, `open i`). -/
abbrev Item : Type := V.Item

/-- **The sub-schedules not frozen yet** (`FORMAT6.md` §T): sponge caller and link, typed phases,
mini-bus. A parameter of the shape, so that `qSOf` and `bodyLen` stay kernel-checked. -/
structure SubT where
  /-- The sponge caller (instance point, output lanes against `Y`). -/
  spCaller : List Item
  /-- The sponge link. -/
  spLink : List Item
  /-- The typed phases. -/
  typed : List Item
  /-- The mini-bus. -/
  bus : List Item

/-- **A shape**: every constant of `FORMAT6.md`. -/
structure Shape where
  /-- `N★ = 2^logN` blocks. -/
  logN : ℕ
  /-- Tree batch: `2^κ` rows. -/
  κ : ℕ
  /-- Sponge batch: `2^κs` rows. -/
  κs : ℕ
  /-- The stack has `2^M` words. -/
  M : ℕ
  /-- Occupied lanes of a level-0 leaf. -/
  lanes : ℕ
  /-- `accIn.pt ∈ E^phiVars`. -/
  phiVars : ℕ
  /-- Keccak layers of the GKR (12). -/
  layers : ℕ
  /-- Scalars of a layer's pack product (47). -/
  prodLen : ℕ
  /-- Plain position rounds of a layer (11). -/
  posRounds : ℕ
  /-- The WHIR levels. -/
  levels : List Level
  /-- Scalars of the final polynomial. -/
  finalLen : ℕ
  /-- Tail sumcheck rounds. -/
  tail : ℕ
  /-- The grind of the ring-switching group. -/
  gRing : ℕ
  /-- The most stack claims `V_S` accepts. -/
  J₀ : ℕ
  /-- The level-0 list bound `L₀` (the batch group is priced at it). -/
  L₀ : ℕ
  /-- The grinds outside WHIR. -/
  gr : Grinds
  /-- The sub-schedules of §T. -/
  subT : SubT
  /-- The number of oracle queries of every accepted proof. -/
  qS : ℕ
  /-- The proof's length in bytes. -/
  piLen : ℕ

/-- `n` copies of a list of items. -/
def rep (n : ℕ) (l : List Item) : List Item := (List.replicate n l).flatten

/-- A sumcheck round `R(n, g)`: `n` scalars, then a ground group. -/
def rnd (n g : ℕ) : List Item := [.E n, .G g]

namespace Shape

variable (sh : Shape)

/-- Level `i`. -/
def lvl (i : ℕ) : Level := sh.levels.getD i default

/-- The variables left before level `i` folds. -/
def nu (i : ℕ) : ℕ := sh.M - ((sh.levels.take i).map (·.fold)).sum

/-- The words of a level's committed row: level 0's `2^ℓ` lanes (64), later levels `2^ℓ` scalars
as `2·2^ℓ` words. -/
def rowW (i : ℕ) : ℕ := if i = 0 then 2 ^ (sh.lvl 0).fold else 2 * 2 ^ (sh.lvl i).fold

/-- Level `i` as V1's `Lev`: height, cap, row width, occupied words (the lanes at level 0),
openings. -/
def lev (i : ℕ) : V.Lev :=
  ⟨(sh.lvl i).ht, (sh.lvl i).lv, sh.rowW i, if i = 0 then sh.lanes else sh.rowW i, (sh.lvl i).nOpen⟩

/-- The levels as V1's `Lev`s. -/
def levs : List V.Lev := (List.range sh.levels.length).map sh.lev

/-- One Keccak layer (`verify_layer`): product, `s`, eq-mode rounds over the pack coordinates and
the segment, plain position rounds, `t₀ t₁ t₂`, `β`. -/
def layer (κ : ℕ) : List Item :=
  [.E sh.prodLen, .G sh.gr.layer] ++ rep (κ - 3) (rnd 2 sh.gr.eqR) ++
    rep sh.posRounds (rnd 3 sh.gr.posR) ++ [.E 3, .G sh.gr.beta]

/-- The Keccak reduction of a batch of `2^κ` rows (§6.2 rows 6–10): segment and lane point,
`c_st`, the layers, the middle-state opening (6 slot rounds, `c_out`), the input opening
(4 low bits, the top row bit if `top`, 6 slot bits; then 64 slices). -/
def keccakCore (κ : ℕ) (top : Bool) : List Item :=
  [.G sh.gr.seg, .D 5, .E 1] ++ rep sh.layers (sh.layer κ) ++ rep 6 (rnd 2 sh.gr.outR) ++
    [.E 1] ++ rep (if top then 11 else 10) (rnd 2 sh.gr.inR) ++ [.E 64]

/-- §6.1: the stack's cap, a bind, its OOD point `z₀ ∈ E^M`, the value `y₀`. -/
def commitPart : List Item := [.cap 0, .B, .G (sh.lvl 0).gOod, .D (sh.M - 1), .E 1]

/-- §6.2 rows 1–5, then the reduction: `δ`, `ρ ∈ E^logN`, `D⁰ D¹`, `u`, `o₄ … o₂₄`. -/
def treePart : List Item :=
  [.K 4, .G sh.gr.rho, .D (sh.logN - 1), .E 8, .G sh.gr.u, .E 21] ++ sh.keccakCore sh.κ true

/-- §6.3: caller (§T), the reduction core, link (§T). -/
def spongePart : List Item := sh.subT.spCaller ++ sh.keccakCore sh.κs false ++ sh.subT.spLink

/-- §6.5: a bind, then one group: the two ring maps and `λ₀`. -/
def ringPart : List Item := [.B, .G sh.gRing, .D 32]

/-- §6.6, level `i`: fold rounds; then the high part, the next commitment, a bind, its OOD point
and value,
positions, `λ`, the openings; at the last level the final polynomial, positions, openings and
the tail rounds. -/
def levelPart (i : ℕ) : List Item :=
  rep (sh.lvl i).fold [.E 4, .G (sh.lvl i).gFold, .D 1] ++
    if i + 1 < sh.levels.length then
      [.E (sh.lvl i).fold, .cap (i + 1), .B, .G (sh.lvl (i + 1)).gOod, .D (sh.nu (i + 1) - 1), .E 1,
        .pos i (sh.lvl i).gQuery, .D 1, .open i]
    else
      [.E sh.finalLen, .pos i (sh.lvl i).gQuery, .open i] ++
        rep sh.tail (rnd 2 sh.gr.tail)

/-- §6.6, all levels. -/
def openPart : List Item := (List.range sh.levels.length).flatMap sh.levelPart

end Shape

/-- **The schedule** of a shape (§6, in `V_S`'s order: §6.1, §6.2, §6.3, §6.4, §6.5, §6.6). -/
def sched6 (sh : Shape) : List Item :=
  sh.commitPart ++ sh.treePart ++ sh.spongePart ++ sh.subT.typed ++ sh.subT.bus ++ sh.ringPart ++
    sh.openPart

/-- **The number of queries** of an accepted proof: `q₀`, the seed, and every query of the
schedule (V1's count). -/
def qSOf (sh : Shape) : ℕ := 2 + V.queriesOf sh.levs (sched6 sh)

/-- The length of `BODY` (V1's count). -/
def bodyLen (sh : Shape) : ℕ := V.bytesOf sh.levs (sched6 sh)

/-- The header's length: `136 + 16v`. -/
def hdrLen (sh : Shape) : ℕ := 136 + 16 * sh.phiVars

/-- **The seed query's length** (FORMAT6 v2.5: `a₀ ‖ HDR`, `168 + 16v`). -/
def seedLen (sh : Shape) : ℕ := 32 + hdrLen sh

/-- **The proof's length**. -/
def piLenOf (sh : Shape) : ℕ := hdrLen sh + bodyLen sh

/-- **The length rule** (§3) and the query cap (V1's `fsLenOK`). -/
def fsLenOK (sh : Shape) : Bool := V.fsLenOK sh.levs (sched6 sh)

/-- **The shape V1's scheme walks**: the leaf size, `v`, the levels and the schedule. -/
def toV (sh : Shape) : V.VShape := ⟨2 ^ sh.logN, sh.phiVars, sh.levs, sched6 sh⟩

/-- **Static consistency of the WHIR ladder** (refv's `Shape::check`): level 0 folds the 64 lanes
of a stack row and its leaf is the occupied lanes (at most 64), later leaves are `2^ℓ` scalars,
caps within the tree, positions fit one draw's 128 bits, the folds and tail use up the `M`
variables, the final polynomial is `2^tail + ℓ_last` scalars, and the levels' commitment shapes
`(ht, row width)` find their level (V1's `levsOK`: the scheme's caps and occupied words are keyed by
them; `T15` repeats a height). -/
def shapeOK (sh : Shape) : Bool :=
  decide (sh.lanes ≤ 64) && !sh.levels.isEmpty && decide ((sh.lvl 0).fold = 6) &&
    decide ((sh.lvl 0).leafB = 8 * sh.lanes) &&
    (sh.levels.drop 1).all (fun lv => decide (lv.leafB = 16 * 2 ^ lv.fold)) &&
    sh.levels.all (fun lv => decide (lv.lv ≤ lv.ht) && decide (lv.ht ≤ 128) && decide (0 < lv.ht)) &&
    decide ((sh.levels.map (·.fold)).sum + sh.tail = sh.M) &&
    decide (sh.finalLen = 2 ^ sh.tail + (sh.lvl (sh.levels.length - 1)).fold) &&
    V.levsOK sh.levs

/-- **The Keccak batches fit the stack**: `κ = logN + 1`, `M = κ + 6`, `4 ≤ κs ≤ κ`. -/
def stackOK (sh : Shape) : Bool :=
  decide (sh.κ = sh.logN + 1) && decide (sh.M = sh.κ + 6) && decide (4 ≤ sh.κs) &&
    decide (sh.κs ≤ sh.κ)

/-! ## The shapes -/

/-- The sub-schedules of `P18`, all frozen: the sponge caller and link of CB's §T freeze
(`Lvm6QKStmt.spCallerItems 13`, `linkItems 13`, copied here since that module imports this one:
13 draws and 25 scalars; 31 draws and 30 scalars), the typed phases and the mini-bus of FORMAT6
v2.3 §6.4a, §6.4b (84 draws and 176 scalars; 53 draws, 43 nonces, 194 scalars). -/
def subT18 : SubT where
  spCaller := rep 13 [.G 1] ++ [.E 25]
  spLink := rep 18 [.G 1] ++ rep 13 (rnd 2 2) ++ [.E 4]
  typed := rep 20 [.G 1] ++ rep 20 (rnd 2 2) ++ rnd 3 2 ++ rep 21 (rnd 2 2) ++ [.E 4, .E 4] ++
    rep 19 (rnd 2 2) ++ [.E 1] ++ rep 2 [.G 1] ++ rnd 44 6
  bus := [.G 16, .D 4, .E 2] ++ (List.range 6).flatMap fun k =>
    [.G 2] ++ rep (2 * k) (rnd 4 3) ++ [.E 4, .E 4, .E 4, .G (if k = 5 then 3 else 2), .D 1]

/-- The season's grinds outside WHIR (`P.groups`). -/
def grinds18 : Grinds := ⟨5, 1, 3, 6, 2, 2, 2, 2, 2, 2⟩

/-- **The season's shape** `P18` (`FORMAT6.md`): `N★ = 2^18`, `κ = 19`, `κs = 13`, `M = 25`,
46 lanes, the five WHIR levels of §5, `phiVars = 43`, the frozen sub-schedules `subT18`;
`qS = 4,349`, `|π| = 238,152`. -/
def P18 : Shape where
  logN := 18
  κ := 19
  κs := 13
  M := 25
  lanes := 46
  phiVars := 43
  layers := 12
  prodLen := 47
  posRounds := 11
  levels := [⟨21, 7, 368, 110, 6, 10, 18, 19⟩, ⟨20, 6, 256, 45, 4, 10, 18, 17⟩,
    ⟨19, 5, 256, 28, 4, 10, 18, 18⟩, ⟨18, 5, 256, 21, 4, 10, 18, 17⟩,
    ⟨17, 5, 256, 18, 4, 10, 18, 13⟩]
  finalLen := 12
  tail := 3
  gRing := 17
  J₀ := 1024
  L₀ := 111
  gr := grinds18
  subT := subT18
  qS := 4349
  piLen := 238152

/-- **refv's test shape** `T15` (`tools/refv/src/shape.rs`; not normative): `M = 15`, three levels
(folds 6, 3, 3; leaves of 368 and 128 bytes), grinds of 8–10 bits, no §T sub-schedules. Its
Keccak constants are `P18`'s (refv runs it for the opening), so `stackOK` does not hold. -/
def T15 : Shape where
  logN := 18
  κ := 19
  κs := 13
  M := 15
  lanes := 46
  phiVars := 44
  layers := 12
  prodLen := 47
  posRounds := 11
  levels := [⟨11, 3, 368, 13, 6, 8, 9, 10⟩, ⟨11, 2, 128, 7, 3, 8, 9, 10⟩, ⟨10, 2, 128, 14, 3, 8, 9, 10⟩]
  finalLen := 11
  tail := 3
  gRing := 9
  J₀ := 1024
  L₀ := 111
  gr := { grinds18 with tail := 8 }
  subT := ⟨[], [], [], []⟩
  qS := 1104
  piLen := 69968

/-! ## The header parser -/

/-- **The parsed view** of header bytes (§2 offsets: `b` 8, `n` 16, `h` 24, `c'` 56, `vk` 88,
`accIn` 120). -/
def hdrView (sh : Shape) (p : Bytes) : Hdr :=
  ⟨rdU64 p 8, rdU64 p 16, rdD p 24, rdD p 56, rdD p 88,
    ((List.range sh.phiVars).map fun i => rdE p (120 + 16 * i), rdE p (120 + 16 * sh.phiVars))⟩

/-- **The header parser** (§2): `HDR` is the first `hdrLen` bytes; it checks the magic,
`b ∈ {0, 1}`, `n = 2^logN` and `c' = 0` in leaf mode, and returns the header and `BODY`. -/
def parseHdr (sh : Shape) (π : Proof) : Option (Hdr × Bytes) :=
  let p := π.data.toList
  let x := hdrView sh p
  if hdrLen sh ≤ p.length ∧ p.take 8 = V.magic6 ∧ (x.b = 0 ∨ x.b = 1) ∧
      x.n.toNat = 2 ^ sh.logN ∧ (x.b = 0 → x.c' = zeroD) then
    some (x, p.drop (hdrLen sh))
  else none

/-- **What `parseHdr` guarantees** of a header (the hypotheses `node6` may use). -/
structure HdrWF (sh : Shape) (x : Hdr) : Prop where
  /-- Leaf or node mode. -/
  b_le : x.b = 0 ∨ x.b = 1
  /-- The season's leaf size. -/
  n_eq : x.n.toNat = 2 ^ sh.logN
  /-- No left child in leaf mode. -/
  c'_zero : x.b = 0 → x.c' = zeroD
  /-- `accIn.pt ∈ E^phiVars`. -/
  pt_len : x.accIn.1.length = sh.phiVars

theorem parseHdr_wf {sh : Shape} {π : Proof} {x : Hdr} {body : Bytes}
    (h : parseHdr sh π = some (x, body)) : HdrWF sh x := by
  simp only [parseHdr] at h
  split_ifs at h with hc
  obtain ⟨_, _, hb, hn, hc'⟩ := hc
  cases h
  exact ⟨hb, hn, hc', by simp [hdrView]⟩

theorem qS_T15 : qSOf T15 = T15.qS := by decide +kernel
theorem piLen_T15 : piLenOf T15 = T15.piLen := by decide +kernel
theorem fsLenOK_T15 : fsLenOK T15 = true := by decide +kernel
theorem shapeOK_T15 : shapeOK T15 = true := by decide +kernel

/-! ## The examples of `FORMAT6.md` §4, §5 (non-vacuity of the codec) -/

/-- The answer `00 01 … 1f`. -/
def ans0 : Digest := Vector.ofFn fun i => (i.val : ℕ).toUInt8

/-- §4: `χ = (0x0706050403020100, 0x0f0e0d0c0b0a0908)`, PoW lane `0x1716151413121110`: the group
passes at `g = 3` and fails at `g = 4`. -/
theorem ans0_chal :
    K.lane (chal6 ans0).re = 0x0706050403020100 ∧ K.lane (chal6 ans0).im = 0x0f0e0d0c0b0a0908 ∧
    powLane ans0 = 0x1716151413121110 ∧ powOK6 3 ans0 = true ∧ powOK6 4 ans0 = false := by
  decide +kernel

/-- §5: the positions of `00 01 … 1f` at level 0 (`ht = 21`). -/
theorem ans0_pos : posOf 21 ans0 = [131328, 532504, 115073, 1315344, 1097904, 493318] := by
  decide +kernel

/-! ## `chal6` and the PoW lane are lanes of season 1's challenge `chalOf` (the scheme's) -/

theorem chalOf_limb (a : Digest) (j : Fin 3) :
    (Lvm.FS.chalOf a).limb j = Lvm.FS.kOfBytes (a.toList.drop (8 * j)) := by
  simp only [Lvm.FS.chalOf, Lvm.FS.eOfBytes, E.limb]
  exact congrFun ((CompPoly.Extension.Ext.equivFn BF64.ext3Params).apply_symm_apply _) j

/-- **The scheme's challenge gives `chal6`**: `e2OfE` (lanes 0–1) of `chalOf a`. -/
theorem e2OfE_chalOf (a : Digest) : e2OfE (Lvm.FS.chalOf a) = chal6 a := by
  ext
  · simp [e2OfE, chal6, chalOf_limb]
  · simp [e2OfE, chal6, chalOf_limb]

/-- The PoW lane is lane 2 of `chalOf a`. -/
theorem lane2_chalOf (a : Digest) : K.lane ((Lvm.FS.chalOf a).limb 2) = powLane a := by
  simp [powLane, rdU64, chalOf_limb]

/-- **The grind test is season 1's `powOK`** on `chalOf a` (for `g ≤ 64`). -/
theorem powOK6_iff {g : ℕ} (hg : g ≤ 64) (a : Digest) :
    powOK6 g a = true ↔ LeanVM.Protocol.Verifier.powOK g (Lvm.FS.chalOf a) := by
  rw [powOK_iff_lane2 hg, powOK6, decide_eq_true_iff, ← lane2_chalOf]
  rfl

/-- A leaf-mode header of `T15`. -/
def hdrEx : Hdr := ⟨0, 262144, zeroD, zeroD, zeroD, (List.replicate 44 0, 0)⟩

/-- The parser accepts the bytes of a well-formed header (non-vacuity of `parseHdr`). -/
theorem parseHdr_ex : (parseHdr T15 ⟨(hdrBytes hdrEx).toArray⟩).isSome = true := by decide +kernel

end Lvm6
