-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-13, §4.3, §4.4, A.7; stage S-E12b, track
-- L-circ).
import FRVIR4Mux
import FRVIRTplFast
import FRVIRTplSet
import FRNodeKinds4
import FRNodeRows4Hint

/-!
# The N2/N4/N8 nodes' M rows: slots, prototypes, copies, link rows

A node of kind `κ` has `κ.vslots` verifier slots (`FRNodeLayout4`): slot 0 replays the previous
step's node when `κ.hasPrev` (`N2`, `N4`), every other slot a segment (`N8`: all eight).

**Slot regions.** M's cells are numbered from M's first cell `κ.oneCell = 3·2^logM` (`oneCell_eq`):
slot `σ` owns the M-relative cells and the rows `[σ·2^20, (σ+1)·2^20)`. Its cell `σ·2^20` is its
own `one` (slot 0's is M's `one`), `σ·2^20 + 1 … + 3` its selector copies, and its program is
compiled from `σ·2^20 + 4` with these as the selector forms (`protoP`). Rows that leave the region
are the slot's **link rows** (`linkRows4`, at the region's last 8 rows): `one′ = one` (σ ≥ 1),
`s′_ι = s_ι` (the selector bits in L, A.7's offset 8,516 of the slot's `2^14` L stride), and the
one-hot products `s′_ι s′_ι′ = 0`.

**Prototypes and copies.** There are two programs (`FRVIR4Mux`): the previous-node mux
`progNodeG` and the segment mux `progSegG`. Each is compiled **once**, as prototype `π` (`0`: the
node program at slot 0; `1`: the segment program at slot 1), and every slot of every kind is a
prototype's rows moved to its region (`mvRows π σ`: rows and cells `+ (σ − π)·2^20`). This is
sound slot by slot: rows over moved cells hold at `w` iff the prototype's hold at `w ∘ move`
(`ev_mapC`), so the prototype's `compileT_sound` applies to slot `σ`'s child. It makes the plan
one pair of prototypes for all three kinds, and `evalM` one evaluation per prototype
(`FRNodeRows4Plan`).

`nodeIRows4 κ` (absolute cells) is the node's M rows: what `evalM` evaluates, what S-G's `truthE`
is stated over, and what P2's node prover fills.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval

/-! ## Moving forms and rows -/

/-- A form with its cells mapped. -/
def mapC (f : ℕ → ℕ) (l : Lin) : Lin := l.map fun t => (f t.1, t.2)

/-- A row with its cells mapped. -/
def rowMapC (f : ℕ → ℕ) (r : Row) : Row := ⟨mapC f r.a, mapC f r.b, mapC f r.c⟩

theorem ev_mapC (w : Asg) (f : ℕ → ℕ) (l : Lin) : (mapC f l).ev w = l.ev (w ∘ f) := by
  simp [mapC, Lin.ev, Function.comp_def]

/-- **Moved rows hold iff the original rows hold at the moved assignment.** -/
theorem holds_rowMapC (w : Asg) (f : ℕ → ℕ) (r : Row) : (rowMapC f r).Holds w ↔ r.Holds (w ∘ f) := by
  simp only [Row.Holds, rowMapC, ev_mapC]

/-! ## The slot regions -/

/-- The selector index's offset in a slot's selector cells. -/
def selIx : Kind → ℕ | .L32 => 0 | .P30 => 1 | .N30 => 2

/-- **Slot `σ`'s selector bits in L** (A.7: after the signature 299, the digits' 266
bit-elements, the step selectors 399, the position bits 7,552 of the slot's `2^14` stride). -/
def selCells4 (κ : NodeKind) (σ : ℕ) (ι : Kind) : ℕ := κ.lBase * 128 + σ * 2 ^ 14 + 8516 + selIx ι

/-- Slot `σ`'s `one` copy (M-relative). -/
def oneR (σ : ℕ) : ℕ := σ * slotM4
/-- Slot `σ`'s selector copies (M-relative). -/
def selR (σ : ℕ) (ι : Kind) : ℕ := σ * slotM4 + 1 + selIx ι
/-- Slot `σ`'s first compiled cell (M-relative). -/
def baseR (σ : ℕ) : ℕ := σ * slotM4 + 4

/-- **Slot `σ`'s selector forms** (M-relative). -/
def protoP (σ : ℕ) : Params := ⟨Lin.cell (oneR σ), fun ι => Lin.cell (selR σ ι)⟩

/-- Whether slot `σ` replays the previous node. -/
def isPrevSlot (κ : NodeKind) (σ : ℕ) : Bool := κ.hasPrev && σ == 0

/-- **Slot `σ`'s prototype**: `0` (the previous-node program) or `1` (the segment program). -/
def protoOf (κ : NodeKind) (σ : ℕ) : ℕ := if isPrevSlot κ σ then 0 else 1

/-- **Prototype `π`'s program** (the previous node's public cells: S-E12a's `cells4` of the
representative `N4`, deviation 1 of the RESULT; the coordinator's ruling: `c_A` from `hashA`). -/
def protoProg (π : ℕ) : VProg := if π = 0 then progNodeG (N4c.cells4 .N4) else progSegG

/-- **Prototype `π`'s layout**: `layOf`'s two-pass layout at S-E12b's programs, as constants
(`FRNodeRows4Hint`; S-E12c: the process start then compiles each prototype once). Any layout is
sound (`compileT_sound`); that the rows fit is `ProtoFit`, checked. -/
def protoLay (π : ℕ) : TLay := if π = 0 then hintLay0 else hintLay1

/-- **Prototype `π`'s template set** (S-E12d, revision 4.3 (a)): revision 4.1's (`keys41`: 3.x's
`shiftMask` template left out, the op an import) for both prototypes. -/
def protoF (_π : ℕ) : TFilt := keys41

/-- **Prototype `π`'s templated compile** (at its template set). -/
def protoCS (π : ℕ) : CS := compileTF (protoF π) (protoLay π) (protoP π) (baseR π) (protoProg π).ops

/-- **Prototype `π`'s indexed rows** (rows from `π·2^20`, M-relative cells). -/
def protoRows (π : ℕ) : List (ℕ × Row) := slotIRows (protoLay π) (Lin.cell (oneR π)) (π * slotM4) (protoCS π)

/-- A cell or row moved from region `π` to region `σ`. -/
def mvC (π σ c : ℕ) : ℕ := c - π * slotM4 + σ * slotM4

/-- **Rows moved from region `π` to region `σ`.** -/
def mvRows (π σ : ℕ) (rows : List (ℕ × Row)) : List (ℕ × Row) :=
  rows.map fun p => (mvC π σ p.1, rowMapC (mvC π σ) p.2)

/-- **M-relative rows to absolute** (cells `+ κ.oneCell`; rows are M's own). -/
def absRows4 (κ : NodeKind) (rows : List (ℕ × Row)) : List (ℕ × Row) :=
  rows.map fun p => (p.1, rowMapC (· + κ.oneCell) p.2)

/-- **Slot `σ`'s rows** (absolute): its prototype's, moved. -/
def slotRows4 (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  absRows4 κ (mvRows (protoOf κ σ) σ (protoRows (protoOf κ σ)))

/-- **Slot `σ`'s activity** `S_σ = Σ_ι s′_ι` (its selector copies' sum; a bit, as the copies are
L bits with at most one set). -/
def selSum (κ : NodeKind) (σ : ℕ) : Lin := Circ.kinds.flatMap fun ι => Lin.cell (κ.oneCell + selR σ ι)

/-- Slot `σ`'s index among its aggregate's sub-slots (`N2`/`N4`: slots `1 …`; `N8`: `4a + i`). -/
def subIx (κ : NodeKind) (σ : ℕ) : ℕ := if κ.hasPrev then σ - 1 else σ % 4

/-- **The activity rows** (S-E12c): the previous node's slot and every aggregate's first sub-slot
are active (`S_σ = 1`: exactly one selector); a later sub-slot is active only if the one before it
is (`S_σ · (1 − S_{σ−1}) = 0`). With the selector bits, the copies and the one-hot products, an
active slot selects exactly one kind and an inactive one none (`FRNodeRows4Fit`); which sub-slots are
active is pinned by the aggregate's `k` (`ActK`, the pack map's). -/
def actRows4 (κ : NodeKind) (σ : ℕ) : List Row :=
  let one := Lin.cell κ.oneCell
  if isPrevSlot κ σ || subIx κ σ == 0 then [⟨one, (selSum κ σ).sub one, []⟩]
  else [⟨selSum κ σ, one.sub (selSum κ (σ - 1)), []⟩]

/-- **Slot `σ`'s link rows** (absolute cells): `one′ = one` (σ ≥ 1), `s′_ι = s_ι`, the one-hot
products, the activity row. -/
def linkRows4 (κ : NodeKind) (σ : ℕ) : List Row :=
  let one := Lin.cell κ.oneCell
  let s := fun ι => Lin.cell (κ.oneCell + selR σ ι)
  (if σ = 0 then [] else [⟨one, (Lin.cell (κ.oneCell + oneR σ)).sub one, []⟩]) ++
  Circ.kinds.map (fun ι => ⟨one, (s ι).sub (Lin.cell (selCells4 κ σ ι)), []⟩) ++
  [⟨s .L32, s .P30, []⟩, ⟨s .L32, s .N30, []⟩, ⟨s .P30, s .N30, []⟩] ++ actRows4 κ σ

/-- Slot `σ`'s link rows at its region's last 8 rows. -/
def linkIRows4 (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  (linkRows4 κ σ).zipIdx.map fun p => (σ * slotM4 + slotM4 - 8 + p.2, p.1)

/-! ## The rows' fit -/

/-- A cell of region `π`. -/
def inSB (π c : ℕ) : Bool := decide (π * slotM4 ≤ c) && decide (c < π * slotM4 + slotM4)
/-- A form over region `π`'s cells. -/
def linInB (π : ℕ) (l : Lin) : Bool := l.all fun t => inSB π t.1
/-- A row index of region `π`, below its link rows. -/
def idxInB (π r : ℕ) : Bool := decide (π * slotM4 ≤ r) && decide (r + 8 < π * slotM4 + slotM4)

/-- **Rows of region `π`**: indices below its link rows, every cell of every matrix in it. -/
def InSlot (π : ℕ) (rows : List (ℕ × Row)) : Prop :=
  ∀ p ∈ rows, (π * slotM4 ≤ p.1 ∧ p.1 + 8 < π * slotM4 + slotM4) ∧
    ∀ s : Mat, ∀ t ∈ s.r p.2, π * slotM4 ≤ t.1 ∧ t.1 < π * slotM4 + slotM4

/-- **The prototypes fit**: each prototype's rows lie in its region, below its link rows, with
distinct indices. -/
def ProtoFit : Prop := ∀ π ≤ 1, InSlot π (protoRows π) ∧ ((protoRows π).map Prod.fst).Nodup

/-- **The rejecting rows** (`one · one = 0`): the node's M rows when `ProtoFit` fails. -/
def rejectRows (κ : NodeKind) : List (ℕ × Row) := [(0, ⟨Lin.cell κ.oneCell, Lin.cell κ.oneCell, []⟩)]

/-- **The node's M rows** (absolute): per slot, its rows and then its link rows (indices increase
along a slot); the rejecting row if the prototypes do not fit (never in practice: the plan checks
`ProtoFit` on its pieces). Not compiled (a closed term of it would be evaluated at process start):
`evalM` evaluates it from the plan (`FRNodeRows4Plan.evalMT4_eq`). -/
noncomputable def nodeIRows4 (κ : NodeKind) : List (ℕ × Row) :=
  open Classical in
  if ProtoFit then (List.range κ.vslots).flatMap (fun σ => slotRows4 κ σ ++ linkIRows4 κ σ)
  else rejectRows κ

/-! ## L's rows -/

/-- Slot `σ`'s declared bit cells in L (A.7, as 3.x's `lBitCells`, in the slot's `2^14` stride). -/
def lBitCells4 (κ : NodeKind) (σ : ℕ) : List ℕ :=
  (List.range (266 + 399 + 7552 + 3)).map fun j => κ.lBase * 128 + σ * 2 ^ 14 + 299 + j

/-- **L's rows**: `b · (1 − b) = 0` for every declared bit of every slot, with M's `one` cell. -/
def lRows4 (κ : NodeKind) : List Row :=
  ((List.range κ.vslots).flatMap (lBitCells4 κ)).map fun b =>
    ⟨Lin.cell b, (Lin.cell κ.oneCell).sub (Lin.cell b), []⟩

/-! ## Facts and controls -/

/-- M's first cell is `3·2^logM` for every kind. -/
theorem oneCell_eq (κ : NodeKind) : κ.oneCell = 3 * 2 ^ κ.dims.logM := by cases κ <;> decide

/-- (+) `N4`'s slot 0 is the previous node, slots 1–4 copies of the segment prototype; `N8`'s eight
slots are all segment copies (its slot 0 is prototype 1 moved down). -/
theorem protoOf_ctl : protoOf .N4 0 = 0 ∧ protoOf .N4 1 = 1 ∧ protoOf .N4 4 = 1 ∧ protoOf .N8 0 = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- (+) Moving region 1 to region 3 adds `2·2^20`; (−) a cell is not left in place. -/
theorem mvC_ctl : mvC 1 3 (2 ^ 20 + 5) = 3 * 2 ^ 20 + 5 ∧ mvC 1 0 (2 ^ 20 + 5) = 5 ∧
    mvC 1 3 (2 ^ 20 + 5) ≠ 2 ^ 20 + 5 := by
  simp only [mvC, slotM4]; omega

/-- (+) The selector bits lie in the slot's own L stride, inside L; (−) two slots' differ. -/
theorem selCells4_fit (κ : NodeKind) (ι : Kind) :
    selCells4 κ (κ.vslots - 1) ι < κ.lBase * 128 + κ.nL ∧ selCells4 κ 0 ι ≠ selCells4 κ 1 ι := by
  have h2 := lSlots_fit κ
  have h1 : 1 ≤ κ.vslots := by cases κ <;> decide
  have : (κ.vslots - 1) * 2 ^ 14 + 2 ^ 14 = κ.vslots * 2 ^ 14 := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel h1]
  simp only [selCells4]
  cases ι <;> simp only [selIx] <;> omega

/-- (+) The slots' regions fill at most M: `N8`'s eight end at `N_M`. -/
theorem regions4_fit (κ : NodeKind) : κ.vslots * slotM4 ≤ κ.nM := mSlots_fit κ

theorem actRows4_length (κ : NodeKind) (σ : ℕ) : (actRows4 κ σ).length = 1 := by
  unfold actRows4; split <;> rfl

/-- (+) A slot's link rows: 8, and 7 for slot 0 (no `one′` row); they fit the region's last 8. -/
theorem linkRows4_length (κ : NodeKind) (σ : ℕ) :
    (linkRows4 κ σ).length = if σ = 0 then 7 else 8 := by
  unfold linkRows4; split_ifs <;> simp [Circ.kinds, actRows4_length]

end Rev4
end FR
