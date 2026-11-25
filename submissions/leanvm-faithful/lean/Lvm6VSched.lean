-- New for lvm6 (WP-V1, part 1): FORMAT6 v2.2 §5–§7 as data: the Merkle geometry of each opened level, the
-- schedule items, the fixed sub-schedules §6.1, §6.2, §6.3 (core), §6.5, §6.6, and their counts.
import RecursionFast.Contract.Relation

/-!
# The lvm6 schedule (FORMAT6 §5, §6) as data

* `Lev`: one opened level (FORMAT6 §5): `2^ht` positions, a cap of `2^lv` nodes, rows of `wd` words of
  which the leaf carries the last `oc` (level 0: 64 and 46, season 1's `padRow`; levels 1–4: 32 and 32,
  sixteen `E` values), `t` openings. Derived: positions per draw `⌊128/ht⌋` (`per`), draws
  `⌈t/per⌉` (`draws`, at least one), path length `ht − lv` (`path`), leaf bytes `8·min oc wd` (`lb`),
  and the positions each draw contributes (`cnts`).
* `Item`: FORMAT6 §6's items. `E k` reads `k` scalars (16 B each), `K k` reads `k` words (8 B each),
  `cap i` reads level `i`'s cap (absorbed), `G g` is a ground group (an 8-B nonce, one draw, `g` bits of
  proof of work), `D k` is `k` further draws, `B` is a bind (a draw whose value is ignored, v2.2), `pos i g` is the ground group whose draws give level `i`'s
  positions (`G(g)`, `D(draws − 1)`), `open i` opens level `i` at the positions last drawn.
* The fixed parts: `s61`, `s62` (frozen subject to TOY2), `s63core`, `s65`, `s66`; `sched18 mid` puts the
  sub-schedules FORMAT6 §T still owes (`mid`: the sponge caller, §6.3's core, the link, the typed phases,
  the mini-bus) between §6.2 and §6.5.
* Counts (`bytesOf`, `queriesOf`, `noncesOf`) and the chain-query lengths (`fsLens`), with FORMAT6's
  table checked by `decide` (`counts_*`) and the length rule (`fsLenOK`).
-/

namespace Lvm6.V

/-- One opened level of the commitment (FORMAT6 §5). -/
structure Lev where
  /-- `2^ht` positions. -/
  ht : Nat
  /-- The cap is `2^lv` nodes. -/
  lv : Nat
  /-- Words of a row as the verifier holds it. -/
  wd : Nat
  /-- Words the leaf carries (the row's last `oc`; the others read as zero). -/
  oc : Nat
  /-- Openings. -/
  t : Nat
deriving Inhabited, DecidableEq, Repr

namespace Lev

/-- Positions per draw: `⌊128/ht⌋`. -/
def per (l : Lev) : Nat := 128 / l.ht

/-- Draws for the positions: `⌈t/per⌉`, at least one (the ground draw). -/
def draws (l : Lev) : Nat := max 1 ((l.t + l.per - 1) / l.per)

/-- Siblings per opening. -/
def path (l : Lev) : Nat := l.ht - l.lv

/-- Bytes of a leaf. -/
def lb (l : Lev) : Nat := 8 * min l.oc l.wd

/-- The positions draw `j` contributes (the surplus of the last draw is dropped). -/
def cnts (l : Lev) : List Nat := (List.range l.draws).map fun j => min l.per (l.t - j * l.per)

end Lev

/-- One item of the schedule (FORMAT6 §6). -/
inductive Item
  /-- `k` `E` scalars, read and absorbed. -/
  | E (k : Nat)
  /-- `k` `K` words, read and absorbed. -/
  | K (k : Nat)
  /-- Level `i`'s cap, read and absorbed. -/
  | cap (i : Nat)
  /-- A ground group: the nonce, one draw, `g` bits of proof of work. -/
  | G (g : Nat)
  /-- `k` further draws (empty buffer). -/
  | D (k : Nat)
  /-- A bind (FORMAT6 v2.2 §4): one draw whose value and proof-of-work lane are ignored. -/
  | B
  /-- Level `i`'s positions: the ground group `G(g)`, then `D(draws − 1)`. -/
  | pos (i g : Nat)
  /-- Level `i`'s openings at the positions last drawn (not absorbed). -/
  | «open» (i : Nat)
deriving Inhabited, DecidableEq, Repr

/-! ## The fixed sub-schedules -/

/-- `m` copies of `xs`. -/
def rep (m : Nat) (xs : List Item) : List Item := (List.replicate m xs).flatten

/-- A sumcheck round `R(n, g)`: `n` scalars, then a ground group. -/
def R (n g : Nat) : List Item := [.E n, .G g]

/-- §6.1: the cap of level 0, a bind, the OOD point `z₀ ∈ E^25`, its value `y₀`. -/
def s61 : List Item := [.cap 0, .B, .G 18, .D 24, .E 1]

/-- One layer of a Keccak reduction (§6.2 row 8): the product, `s`, `eq` eq-mode rounds, eleven plain
rounds, `t₀ t₁ t₂`, `β`. -/
def layer (eq : Nat) : List Item := [.E 47, .G 6] ++ rep eq (R 2 2) ++ rep 11 (R 3 2) ++ [.E 3, .G 2]

/-- §6.2: the tree batch (BLUEPRINT §2.3 v3; frozen subject to TOY2). -/
def s62 : List Item :=
  [.K 4, .G 5, .D 17, .E 8, .G 1, .E 21, .G 3, .D 5, .E 1] ++ rep 12 (layer 16) ++
    rep 6 (R 2 2) ++ [.E 1] ++ rep 11 (R 2 2) ++ [.E 64]

/-- §6.3: the core of the sponge batch's reduction (rows 6–10 at `κ_s = 13`). -/
def s63core : List Item :=
  [.G 3, .D 5, .E 1] ++ rep 12 (layer 10) ++ rep 6 (R 2 2) ++ [.E 1] ++ rep 10 (R 2 2) ++ [.E 64]

/-- §6.5: a bind, then the ring-switching group (`G(17)`, `D(32)`). -/
def s65 : List Item := [.B, .G 17, .D 32]

/-- A fold round of the opening: `v_G, v_F, t₀, t₁`, `α` (ground, 10 bits), `β`. -/
def foldR : List Item := [.E 4, .G 10, .D 1]

/-- §6.6, level `i < 4` (v2.2): `fold` rounds, the high part, the next cap, a bind, `z_{i+1} ∈ E^ν` (`g_ood`
of level `i+1`), `y_{i+1}`, the positions (`g_q` of level `i`), `λ_{i+1}`, the openings of level `i`. -/
def lvlG (i fold nu gOod gq : Nat) : List Item :=
  rep fold foldR ++ [.E fold, .cap (i + 1), .B, .G gOod, .D (nu - 1), .E 1, .pos i gq, .D 1, .open i]

/-- `lvlG` with `P18`'s OOD grind (18 at every level). -/
def lvl (i fold nu gq : Nat) : List Item := lvlG i fold nu 18 gq

/-- §6.6: levels 0–3, then level 4 (four fold rounds, the final polynomial, positions, openings, three
tail rounds). -/
def s66 : List Item :=
  lvl 0 6 19 19 ++ lvl 1 4 15 17 ++ lvl 2 4 11 18 ++ lvl 3 4 7 17 ++
    rep 4 foldR ++ [.E 12, .pos 4 13, .open 4] ++ rep 3 (R 2 2)

/-- The levels of `P18` (FORMAT6 §5). -/
def levs18 : List Lev :=
  [⟨21, 7, 64, 46, 110⟩, ⟨20, 6, 32, 32, 45⟩, ⟨19, 5, 32, 32, 28⟩, ⟨18, 5, 32, 32, 21⟩, ⟨17, 5, 32, 32, 18⟩]

/-- **The `P18` schedule**, with the sub-schedules of FORMAT6 §T (`mid`) between §6.2 and §6.5. -/
def sched18 (mid : List Item) : List Item := s61 ++ s62 ++ mid ++ s65 ++ s66

/-! ## Commitment shapes: the cap level and the occupied words of a `(height, width)` -/

/-- The level with this height and width. -/
def levOf (L : List Lev) (ht w : Nat) : Option Lev := L.find? fun l => l.ht == ht && l.wd == w

/-- The cap level of a commitment of `2^ht` rows of `w` words. -/
def capOfL (L : List Lev) (ht w : Nat) : Nat := ((levOf L ht w).map Lev.lv).getD 0

/-- The occupied words of a commitment of `2^ht` rows of `w` words. -/
def occL (L : List Lev) (ht w : Nat) : Nat := ((levOf L ht w).map Lev.oc).getD w

/-! ## Read widths (FORMAT6 §1: 16 bytes an `E` scalar, 8 bytes a `K` word or a nonce) -/

/-- The widths of the reads an item makes, in order. -/
def widthsI : Item → List Nat
  | .E k => (List.replicate k [16]).flatten
  | .K k => (List.replicate k [8]).flatten
  | .G _ => [8]
  | .pos _ _ => [8]
  | _ => []

/-- The widths of the reads of a schedule, in order. -/
def widths : List Item → List Nat
  | [] => []
  | it :: r => widthsI it ++ widths r

/-- **The width of the `n`-th read** of a schedule (8 past its end). -/
def rwOf (s : List Item) (n : Nat) : Nat := (widths s).getD n 8

theorem mem_widths {s : List Item} {x : Nat} (h : x ∈ widths s) : x = 8 ∨ x = 16 := by
  induction s with
  | nil => simp [widths] at h
  | cons it r ih =>
    simp only [widths, List.mem_append] at h
    rcases h with h | h
    · cases it <;> simp [widthsI] at h <;> omega
    · exact ih h

theorem rwOf_pos (s : List Item) (n : Nat) : 0 < rwOf s n := by
  unfold rwOf
  rw [List.getD_eq_getElem?_getD]
  cases h : (widths s)[n]? with
  | none => simp
  | some x =>
    have := mem_widths (List.mem_of_getElem? h)
    simp only [Option.getD_some]
    omega

/-- Every level is found by its height and width. -/
def levsOK (L : List Lev) : Bool := L.all fun l => levOf L l.ht l.wd == some l

theorem levsOK_18 : levsOK levs18 = true := by decide +kernel

/-! ## Counts -/

section Counts
variable (L : List Lev)

/-- Bytes of `BODY` an item takes. -/
def bytesI : Item → Nat
  | .E k => 16 * k
  | .K k => 8 * k
  | .cap i => 32 * 2 ^ (L.getD i default).lv
  | .G _ => 8
  | .D _ => 0
  | .B => 0
  | .pos _ _ => 8
  | .open i => (L.getD i default).t * ((L.getD i default).lb + 32 * (L.getD i default).path)

/-- Oracle queries an item asks. -/
def queriesI : Item → Nat
  | .E _ => 0
  | .K _ => 0
  | .cap _ => 0
  | .G _ => 1
  | .D k => k
  | .B => 1
  | .pos i _ => (L.getD i default).draws
  | .open i => (L.getD i default).t * (1 + (L.getD i default).path)

/-- Nonces an item reads. -/
def noncesI : Item → Nat
  | .G _ => 1
  | .pos _ _ => 1
  | _ => 0

/-- Bytes of a schedule. -/
def bytesOf (s : List Item) : Nat := (s.map (bytesI L)).sum
/-- Queries of a schedule. -/
def queriesOf (s : List Item) : Nat := (s.map (queriesI L)).sum
/-- Nonces of a schedule. -/
def noncesOf (s : List Item) : Nat := (s.map noncesI).sum

/-- The lengths of the chain queries of a schedule, the buffer holding `b` bytes at the start. -/
def fsLensAux : List Item → Nat → List Nat
  | [], _ => []
  | .E k :: r, b => fsLensAux r (b + 16 * k)
  | .K k :: r, b => fsLensAux r (b + 8 * k)
  | .cap i :: r, b => fsLensAux r (b + 32 * 2 ^ (L.getD i default).lv)
  | .G _ :: r, b => (32 + b + 8) :: fsLensAux r 0
  | .D 0 :: r, b => fsLensAux r b
  | .D (k + 1) :: r, b => (32 + b) :: List.replicate k 32 ++ fsLensAux r 0
  | .B :: r, b => (32 + b) :: fsLensAux r 0
  | .pos i _ :: r, b => (32 + b + 8) :: List.replicate ((L.getD i default).draws - 1) 32 ++ fsLensAux r 0
  | .open _ :: r, b => fsLensAux r b

/-- The chain-query lengths of a schedule. -/
def fsLens (s : List Item) : List Nat := fsLensAux L s 0

/-- **The length rule** (FORMAT6 §3): no chain query has a node's (64) or a leaf's length, no leaf has a
node's length, and every chain query fits `queryCap`. -/
def fsLenOK (s : List Item) : Bool :=
  (fsLens L s).all (fun n => n != 64 && L.all (fun l => n != l.lb) && decide (n ≤ RecursionFast.queryCap)) &&
    L.all fun l => l.lb != 64

end Counts

/-! ## FORMAT6's table (§6, §7), checked -/

theorem counts_61 : bytesOf levs18 s61 = 4120 ∧ queriesOf levs18 s61 = 26 ∧ noncesOf s61 = 1 := by decide +kernel
theorem counts_62 : bytesOf levs18 s62 = 27120 ∧ queriesOf levs18 s62 = 390 ∧ noncesOf s62 = 368 := by decide +kernel
theorem counts_63core :
    bytesOf levs18 s63core = 23688 ∧ queriesOf levs18 s63core = 298 ∧ noncesOf s63core = 293 := by decide +kernel
theorem counts_65 : bytesOf levs18 s65 = 8 ∧ queriesOf levs18 s65 = 34 ∧ noncesOf s65 = 1 := by decide +kernel
theorem counts_66_level0 : bytesOf levs18 (lvl 0 6 19 19) = 92368 ∧ queriesOf levs18 (lvl 0 6 19 19) = 1702 := by
  decide +kernel
theorem counts_66 : bytesOf levs18 s66 = 174224 ∧ queriesOf levs18 s66 = 3418 ∧ noncesOf s66 = 34 := by decide +kernel

/-- **The fixed part** (FORMAT6 v2.2 §6's last table): 205,472 bytes, 3,868 queries, 404 nonces. -/
theorem counts_fixed : bytesOf levs18 (sched18 []) = 205472 ∧ queriesOf levs18 (sched18 []) = 3868 ∧
    noncesOf (sched18 []) = 404 := by decide +kernel

/-- The draws of the five levels' positions (FORMAT6 §5): 19, 8, 5, 3, 3. -/
theorem draws_18 : levs18.map Lev.draws = [19, 8, 5, 3, 3] := by decide +kernel

/-- The length rule holds for the fixed part with §6.3's core in place of `mid`. -/
theorem fsLenOK_18 : fsLenOK levs18 (sched18 s63core) = true := by decide +kernel

end Lvm6.V
