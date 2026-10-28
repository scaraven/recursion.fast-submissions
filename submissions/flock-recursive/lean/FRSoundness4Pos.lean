-- New for `flock-recursive` (BLUEPRINT A.4, B-12, B-13, §5.1; stage S-G13, route C2): the
-- revision 4.1 chain's positions and kinds. `FRSoundnessStepA`/`FRSoundnessDefs` Part D are the
-- 3.x templates (`fsStarts`, `phStart`, `fsRanges`, `fsRnd`, `kindOf`).
import FRSoundnessFrChain
import FRShape4
import FRSoundnessStepA

/-!
# Revision 4.1's chains: the item list `fsItems4`, the phase starts, the multi-squeeze phases, the kind

All six SNARK programs of revision 4.1 ask one item sequence, `itemsOf seq4` (S-0′). Its
Fiat–Shamir items (482) are **`fsItems4`**, and **`fsSeq4`** makes them the chains' list for the
generic potential (`FRSoundnessFrChain`).

* **Phase starts** (`fsStarts4`, `phStart4 k`): the Fiat–Shamir position of phase `k`'s first item,
  `fsStarts4_eq` pins them. They are 3.x's (`fsStarts_eq`) up to `Lr1` (phases 0–13, positions
  0 … 170) and then shift by `+1` (`Lr2`), `+5` (`Lrend`, `Lr3`, `E1`), `+6` (`E2`), `+10`
  (`Eend`, `E3`, `E4`) and `+14` (`E4end` … `Pf`): `Lr1` has 9 squeezes, `Lr2` 17 rounds, `E1` 12
  squeezes, `E2` 23 rounds, `E4` 25 rounds (`phStart4_shift`).
* **Multi-squeeze phases** (`fsRanges4`, `fsRnd4`), with **`fsRnd4_ok : RndOK fsRnd4`** (checked).
* **The chain's kind** (`CKind`, `kindOfC es`): byte 71 of the seed query (`hdr`'s first byte),
  one of the six SNARK kinds; `L32` if it is not one. Its `m`, `isNode`, and ladder `lvC κ i =
  lvOf κ.m i` (`ladderOf 30/31/32`).
-/

namespace FR.Snd
open RecursionFast FR.Rev4

/-! ## The item list -/

/-- **`seq4`'s Fiat–Shamir items**: the item sequence without the column and node queries. -/
def fsItems4 : List Item := (itemsOf seq4).filter Item.isFS

theorem fsItems4_length : fsItems4.length = 482 := by
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
`26 + 5i … 30 + 5i`, `Pf` is `51`). -/
theorem fsStarts4_eq : fsStarts4 = [0, 1, 2, 3, 13, 15, 67, 68, 69, 97, 98, 99, 114, 170, 179, 213,
    214, 215, 227, 273, 274, 275, 325, 326, 327, 331, 332, 344, 345, 370, 370, 375, 383, 384, 397,
    397, 402, 410, 411, 421, 421, 426, 434, 435, 443, 443, 448, 456, 457, 463, 463, 468] := by
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

/-- Level `i` of the kind's ladder (`ladderOf m`). -/
def lv (κ : CKind) (i : ℕ) : Level := lvOf κ.m i

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
