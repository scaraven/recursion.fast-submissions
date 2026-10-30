-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-13, §4.3, §4.4, A.7; stage S-E12b, track
-- L-circ).
import FRVIR4Mux
import FRVIRTplFast
import FRVIRTplSet
import FRNodeKinds4
import FRNodeRows4Hint
import FRNodeRows4Pack
import FRNodeRows4Ext
import FRNodeRows4AskPosT
import FRNodeRows4AskT
import FRNodeRows4AskI
import FRNodeRows4AskB
import FRNodeRows4Defs

/-!
# The N2/N4/N8 nodes' M rows: slots, prototypes, copies, link rows

A node of kind `κ` has `κ.vslots` verifier slots (`FRNodeLayout4`): slot 0 replays the previous
step's node when `κ.hasPrev` (`N2`, `N4`), every other slot a segment (`N8`: all eight).

**Slot regions.** M's cells are numbered from M's first cell `κ.oneCell = 3·2^logM` (`oneCell_eq`):
slot `σ` owns the M-relative cells and the rows `[σ·2^20, (σ+1)·2^20)`. Its cell `σ·2^20` is its
own `one` (slot 0's is M's `one`), `σ·2^20 + 1 … + 3` its selector copies, and its program is
compiled from `σ·2^20 + 4` with these as the selector forms (`protoP`). Rows that leave the region
are the slot's **link rows** (`linkRows4`, in the region's **link region**, its last `linkN = 2^15`
rows; S-E13a: was the last 8): `one′ = one` (σ ≥ 1), `s′_ι = s_ι` (the selector bits in L, A.7's
offset 8,516 of the slot's `2^14` L stride), the one-hot products `s′_ι s′_ι′ = 0`, the activity
row (`linkRowsB4`), then the slot's **pack rows** (`packRows4`, S-E13a: the kind tie and the
stream's pinned elements, `FRNodeRows4Pack`), then at slot 1 S-E13b's node rows (`extRowsC`: WOTS
and `aggPad`, `FRNodeRows4Ext`).

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

theorem ev_mapC (w : Asg) (f : ℕ → ℕ) (l : Lin) : (mapC f l).ev w = l.ev (w ∘ f) := by
  simp [mapC, Lin.ev, Function.comp_def]

/-- **Moved rows hold iff the original rows hold at the moved assignment.** -/
theorem holds_rowMapC (w : Asg) (f : ℕ → ℕ) (r : Row) : (rowMapC f r).Holds w ↔ r.Holds (w ∘ f) := by
  simp only [Row.Holds, rowMapC, ev_mapC]

/-! ## The slot regions -/

/-- **Slot `σ`'s selector bits in L** (A.7: after the signature 299, the digits' 266
bit-elements, the step selectors 399, the position bits 7,552 of the slot's `2^14` stride). -/
def selCells4 (κ : NodeKind) (σ : ℕ) (ι : Kind) : ℕ := κ.lBase * 128 + σ * 2 ^ 14 + 8516 + selIx ι

theorem nodeGrp_nodeOf (ι : Kind) : nodeGrp ι = .ofNode (nodeOf ι) := by cases ι <;> rfl

/-- **Prototype `π`'s templated compile** (at its template set and route). -/
def protoCS (π : ℕ) : CS :=
  compileTF4 (protoF π) (protoR π) (protoLay π) (protoP π) (baseR π) (protoProg π).ops

/-- **Prototype `π`'s indexed rows** (rows from `π·2^20`, M-relative cells). -/
def protoRows (π : ℕ) : List (ℕ × Row) := slotIRows (protoLay π) (Lin.cell (oneR π)) (π * slotM4) (protoCS π)

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

/-- **Slot `σ`'s link rows of S-E12c** (absolute cells): `one′ = one` (σ ≥ 1), `s′_ι = s_ι`, the
one-hot products, the activity row. -/
def linkRowsB4 (κ : NodeKind) (σ : ℕ) : List Row :=
  let one := Lin.cell κ.oneCell
  let s := fun ι => Lin.cell (κ.oneCell + selR σ ι)
  (if σ = 0 then [] else [⟨one, (Lin.cell (κ.oneCell + oneR σ)).sub one, []⟩]) ++
  Circ.kinds.map (fun ι => ⟨one, (s ι).sub (Lin.cell (selCells4 κ σ ι)), []⟩) ++
  [⟨s .L32, s .P30, []⟩, ⟨s .L32, s .N30, []⟩, ⟨s .P30, s .N30, []⟩] ++ actRows4 κ σ

/-- The aggregate a segment slot belongs to (`N2`/`N4`: 0; `N8`: `σ / 4`). -/
def aggSlot (κ : NodeKind) (σ : ℕ) : ℕ := if κ.hasPrev then 0 else σ / 4

/-- **Slot `σ`'s packed stream** (S-E13a; R-A′): the first block of the stream segment it reads and
its kind group: the previous node's (signed child 0, the node group) and every aggregate sub-slot
`i` (segment `i` of the aggregate's stream, the segment group). With R-A′'s spacers segment `i`
starts at `1 + i·strideB`, `strideB = 64·sBlk`, so its block is the aggregate's first plus
`i·sBlk` and its elements are segment 0's shifted (S-E13a's B1 closed). -/
def packB (κ : NodeKind) (σ : ℕ) : Option (ℕ × Grp) :=
  if isPrevSlot κ σ then some (N4c.chBase κ 0, nodeGrp)
  else some (N4c.chBase κ (N4c.aggChild κ (aggSlot κ σ)) + subIx κ σ * N4c.sBlk, segGrp)

/-- Slot `σ`'s segment index in its stream (`0` for the previous node). -/
def segIx (κ : NodeKind) (σ : ℕ) : ℕ := if isPrevSlot κ σ then 0 else subIx κ σ

/-- **Slot `σ`'s head rows**: the kind tie (stream element 5 `= Σ_ι K_ι s′_ι`,
`FRNodeRows4Pack.kindRow`), then its segment's element 0 and, for a later sub-slot, the spacer
before it (`headRows`, with the spacer's bit cells `spC` of its aggregate). -/
def packHead4 (κ : NodeKind) (σ : ℕ) : List Row :=
  match packB κ σ with
  | some (b0, G) => kindRow κ.oneCell (sCell b0 5) (fun ι => κ.oneCell + selR σ ι) G ::
      headRows κ.oneCell b0 (segIx κ σ) (spC κ (N4c.aggChild κ (aggSlot κ σ)) (segIx κ σ))
  | none => []

/-- The pinned elements of slot `σ`'s stream segment (`FRNodeRows4Pack.wfRows`). -/
def packWf4 (κ : NodeKind) (σ : ℕ) : List Row :=
  match packB κ σ with
  | some (b0, _) => wfRows κ.oneCell b0
  | none => []

/-- **Slot `σ`'s pack rows** (S-E13a; `FRNodeRows4Pack`): the kind tie and the head rows, then the
stream's pinned elements (each later item's length word and query tag). -/
def packRows4 (κ : NodeKind) (σ : ℕ) : List Row := packHead4 κ σ ++ packWf4 κ σ

/-! ### S-E13b's node rows (WOTS, `aggPad`) and B4's aggregate checks, folded in at slot 1 -/

/-- S-E13b's node rows and B4's check rows per kind (`W4.xRowsA`), closed constants (built once per process). -/
def xRowsN2 : List Row := W4.xRowsA .N2
def xRowsN4 : List Row := W4.xRowsA .N4
def xRowsN8 : List Row := W4.xRowsA .N8

/-- The node rows of kind `κ`, read off the closed constants. -/
def xRowsK : NodeKind → List Row
  | .N2 => xRowsN2
  | .N4 => xRowsN4
  | .N8 => xRowsN8

theorem xRowsK_eq (κ : NodeKind) : xRowsK κ = W4.xRowsA κ := by cases κ <;> rfl

/-- A row's cells are below `b`. -/
def rowCellsLt (b : ℕ) (r : Row) : Bool := (r.a ++ r.b ++ r.c).all fun t => decide (t.1 < b)

/-- **The node rows' cell check** (run once per process on the closed constants, like
`ProtoFit`): every cell below the end of the slots' M cells. -/
def xOkOf (κ : NodeKind) (rs : List Row) : Bool := rs.all (rowCellsLt (κ.oneCell + κ.vslots * slotM4))

def xOkN2 : Bool := xOkOf .N2 xRowsN2
def xOkN4 : Bool := xOkOf .N4 xRowsN4
def xOkN8 : Bool := xOkOf .N8 xRowsN8

/-- The check's result per kind. -/
def xOkK : NodeKind → Bool
  | .N2 => xOkN2
  | .N4 => xOkN4
  | .N8 => xOkN8

theorem xOkK_eq (κ : NodeKind) : xOkK κ = xOkOf κ (xRowsK κ) := by cases κ <;> rfl

/-- The rejecting row `one · one = 0`. -/
def rejR (κ : NodeKind) : Row := ⟨Lin.cell κ.oneCell, Lin.cell κ.oneCell, []⟩

/-- **S-E13b's node rows at slot 1** (`W4.extRows4`), if their cells check; the rejecting row
otherwise (never in practice). -/
def extRowsC (κ : NodeKind) (σ : ℕ) : List Row :=
  if σ = 1 then (if xOkK κ then xRowsK κ else [rejR κ]) else []

/-- **Slot `σ`'s link rows**: S-E12c's, the pack rows, then S-E13b's node rows (slot 1). -/
def linkRows4 (κ : NodeKind) (σ : ℕ) : List Row := linkRowsB4 κ σ ++ packRows4 κ σ ++ extRowsC κ σ

/-- **The link region**: a slot region's last `2^15` rows. -/
def linkN : ℕ := 2 ^ 15

/-- Slot `σ`'s link rows, from the start of its link region. -/
def linkIRows4 (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  (linkRows4 κ σ).zipIdx.map fun p => (σ * slotM4 + slotM4 - linkN + p.2, p.1)

/-! ## The rows' fit -/

/-- A cell of region `π`. -/
def inSB (π c : ℕ) : Bool := decide (π * slotM4 ≤ c) && decide (c < π * slotM4 + slotM4)
/-- A form over region `π`'s cells. -/
def linInB (π : ℕ) (l : Lin) : Bool := l.all fun t => inSB π t.1
/-- A row index of region `π`, below its link region. -/
def idxInB (π r : ℕ) : Bool := decide (π * slotM4 ≤ r) && decide (r + linkN < π * slotM4 + slotM4)

/-- **Rows of region `π`**: indices below its link region, every cell of every matrix in it. -/
def InSlot (π : ℕ) (rows : List (ℕ × Row)) : Prop :=
  ∀ p ∈ rows, (π * slotM4 ≤ p.1 ∧ p.1 + linkN < π * slotM4 + slotM4) ∧
    ∀ s : Mat, ∀ t ∈ s.r p.2, π * slotM4 ≤ t.1 ∧ t.1 < π * slotM4 + slotM4

/-- **The prototypes fit**: each prototype's rows lie in its region, below its link region, with
distinct indices. -/
def ProtoFit : Prop := ∀ π ≤ 1, InSlot π (protoRows π) ∧ ((protoRows π).map Prod.fst).Nodup

/-! ## The arena rows (track ASK-P): arena₁, the node's template rows, the bits

Every slot region holds, above its prototype's rows and below its link region (B2″'s placement,
`FRNodeRows4ArenaPlace`): **arena₁** (`a1Rows4`: the slot's stream segment copied into M, rows
`[arR1, arR1 + arN)`), the **node's template rows** in the binding's range `[arR2, arR2 + arR2N)` (the
ask templates' rows of the slot's prototype, `askRowsT`: B3's `askIRows4` at `b = arR2`, moved like
the prototype), and the **bits** (`bitRows4`, rows `[arRb, arRb + arNb)`). They are folded if they fit
(`ArFit`, checked by the plan at process start like `ProtoFit`); otherwise the slot gets one
rejecting row instead (so `ArFit` follows from the statement's rows, `FRNodeRows4AskPosF`). -/

/-- **Prototype `π`'s template extension** (`FRNodeRows4Rep.Xof`, by definition). -/
def XofT (π : ℕ) : Ext := tplExt4 (protoF π) (protoR π) (protoLay π).ctx

/-- **The node's row generator of prototype `π`**: the ask templates' rows (B3's `AT` with these
fields is SRA's `FRNodeRsvLink.withRsv`'s): IMP's `input` template
(`inpTG`), SRA's reserve template (`rsvTG`), and ASK-T's ask generator (`askTGT`: every ask's query
and answer, `FRNodeRows4AskT`), IMPC's import classes (`impcTG`, `FRNodeRows4AskI`; `colTG` not yet
folded). -/
def askTG (π : ℕ) : TG :=
  (((askTGT (XofT π) π).add (inpTG (XofT π) π)).add (rsvTG (XofT π) π)).add
    (impcTG (XofT π) π (provLT 0 (protoProg π).ops)) |>.addD
    (bitTGB (tplExt4 (protoF π) (protoR π) ⟨fun _ => ⟨[], []⟩, (protoLay π).cb⟩) π
      (bitTab (protoProg π).ops (if π = 0 then nodeGrp else segGrp))) |>.addD
    (bitTGS (tplExt4 (protoF π) (protoR π) ⟨fun _ => ⟨[], []⟩, (protoLay π).cb⟩) π
      (bitTab (protoProg π).ops (if π = 0 then nodeGrp else segGrp)))

/-- **Prototype `π`'s template rows** (its frame), along its compile's trail (`askRowsP`'s fold). -/
def askRowsT (π : ℕ) : List Row :=
  trailRows (XofT π) (protoP π) (askTG π) (CS.init (baseR π)) none 0 (protoProg π).ops

/-- **Prototype `π`'s template rows, indexed**: rows `π·2^20 + arR2 + k` (the binding's range). -/
def askPI (π : ℕ) : List (ℕ × Row) := (askRowsT π).zipIdx.map fun p => (π * slotM4 + arR2 + p.2, p.1)

/-- **The arena rows fit** (both prototypes): the prototype's rows below the binding's range, the
template rows inside it (at most `arR2N`) with their cells in the region. -/
def ArFit : Prop :=
  ∀ π ≤ 1, (∀ p ∈ protoRows π, p.1 < π * slotM4 + arR2) ∧ (askRowsT π).length ≤ arR2N ∧ InSlot π (askPI π)

/-- **Slot `σ`'s stream block** (`packB`'s: its segment's first H block). -/
def slotB0 (κ : NodeKind) (σ : ℕ) : ℕ :=
  if isPrevSlot κ σ then N4c.chBase κ 0 else N4c.chBase κ (N4c.aggChild κ (aggSlot κ σ)) + subIx κ σ * N4c.sBlk

theorem packB_b0 (κ : NodeKind) (σ : ℕ) : (packB κ σ).map Prod.fst = some (slotB0 κ σ) := by
  unfold packB slotB0; split_ifs <;> rfl

/-- The row index of slot `σ`'s rejecting arena row (its region's last row: the link rows end before it). -/
def arRej (σ : ℕ) : ℕ := σ * slotM4 + slotM4 - 1

/-- **Slot `σ`'s arena rows** (absolute cells): arena₁ of its stream, its prototype's template rows
moved (`askPI`), its bits; one rejecting row if they do not fit. -/
noncomputable def arIRows4 (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  open Classical in
  if ArFit then a1Rows4 κ σ (slotB0 κ σ) ++ absRows4 κ (mvRows (protoOf κ σ) σ (askPI (protoOf κ σ))) ++
    bitRows4 κ σ
  else [(arRej σ, rejR κ)]

/-! ## The replay rows (track REPF)

The previous node's ops `shiftTarget`, `linkWAll`, `rsWeight`, `targetS`, `evalL` (prototype 0) and the
segment's `linkWAll` (prototype 1) are replayed by C1/R3/C1b's templates `rtC1c`
(`FRNodeRows4Defs`): slot `v`'s rows `repIRowsW rtC1c κ v`, slot 0's (`N2`, `N4`) in the spare region
`κ.vslots` (rows and locals), a segment slot's at `v·2^20 + repSegB` over its frame cells. They are
folded if they fit (**`RepFit`**, checked by the plan at process start); otherwise one rejecting row at
the spare region's first row. -/

/-- A replay row's cell fits its prototype: prototype 0's frame (region 0) or its locals' block
(`[repB, repB + 2^20)`, moved to the spare region); prototype 1's frame (region 1). -/
def repCellOk (π c : ℕ) : Bool :=
  if π = 0 then decide (c < slotM4) || (decide (N4s.repB ≤ c) && decide (c < N4s.repB + slotM4)) else inSB 1 c

/-- Prototype `π`'s replay rows fit: at most `2^20` (prototype 0) or `2^10` (prototype 1) rows, every
cell fits. -/
def repFitB (π : ℕ) (rows : List Row) : Bool :=
  decide (rows.length ≤ if π = 0 then slotM4 else 2 ^ 10) &&
    rows.all fun r => (r.a ++ r.b ++ r.c).all fun t => repCellOk π t.1

/-- **The replay rows fit** (both prototypes). -/
def RepFit : Prop := ∀ π ≤ 1, repFitB π (N4s.repRowsP (N4s.rtC1c π) π) = true

/-- **The node's replay rows** (with the arenas, `ArFit`): every slot's (`repIRowsW rtC1c`) if they
fit; else one rejecting row at slot 0's `repSegB` (free when the arenas fit). Without `ArFit` the
arena's rejecting row stands for both. -/
noncomputable def repAllRows (κ : NodeKind) : List (ℕ × Row) :=
  open Classical in
  if ArFit then
    (if RepFit then (List.range κ.vslots).flatMap (N4s.repIRowsW N4s.rtC1c κ) else [(N4s.repSegB, rejR κ)])
  else []

/-- **The rejecting rows** (`one · one = 0`): the node's M rows when `ProtoFit` fails. -/
def rejectRows (κ : NodeKind) : List (ℕ × Row) := [(0, ⟨Lin.cell κ.oneCell, Lin.cell κ.oneCell, []⟩)]

/-- **The node's M rows** (absolute): per slot, its rows, its arena rows (ASK-P) and then its link
rows (indices increase along a slot), then the replay rows (REPF, `repAllRows`); the rejecting row if the prototypes do not fit (never in practice: the plan checks
`ProtoFit` on its pieces). Not compiled (a closed term of it would be evaluated at process start):
`evalM` evaluates it from the plan (`FRNodeRows4Plan.evalMT4_eq`). -/
noncomputable def nodeIRows4 (κ : NodeKind) : List (ℕ × Row) :=
  open Classical in
  if ProtoFit then (List.range κ.vslots).flatMap (fun σ => slotRows4 κ σ ++ arIRows4 κ σ ++ linkIRows4 κ σ) ++
    repAllRows κ
  else rejectRows κ

/-- **A slot's prototype rows are the node's.** -/
theorem mem_node_slot {κ : NodeKind} {σ : ℕ} {p : ℕ × Row} (hF : ProtoFit) (hσ : σ < κ.vslots)
    (hp : p ∈ slotRows4 κ σ) : p ∈ nodeIRows4 κ := by
  rw [nodeIRows4, if_pos hF]
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨σ, List.mem_range.2 hσ, List.mem_append_left _ (List.mem_append_left _ hp)⟩)

/-- **A slot's arena rows are the node's.** -/
theorem mem_node_ar {κ : NodeKind} {σ : ℕ} {p : ℕ × Row} (hF : ProtoFit) (hσ : σ < κ.vslots)
    (hp : p ∈ arIRows4 κ σ) : p ∈ nodeIRows4 κ := by
  rw [nodeIRows4, if_pos hF]
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨σ, List.mem_range.2 hσ, List.mem_append_left _ (List.mem_append_right _ hp)⟩)

/-- **A slot's link rows are the node's.** -/
theorem mem_node_link {κ : NodeKind} {σ : ℕ} {p : ℕ × Row} (hF : ProtoFit) (hσ : σ < κ.vslots)
    (hp : p ∈ linkIRows4 κ σ) : p ∈ nodeIRows4 κ := by
  rw [nodeIRows4, if_pos hF]
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨σ, List.mem_range.2 hσ, List.mem_append_right _ hp⟩)

/-- **The replay rows are the node's** (REPF). -/
theorem mem_node_rep {κ : NodeKind} {p : ℕ × Row} (hF : ProtoFit) (hp : p ∈ repAllRows κ) : p ∈ nodeIRows4 κ := by
  rw [nodeIRows4, if_pos hF]
  exact List.mem_append_right _ hp

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

/-- (+) S-E12c's link rows: 8, and 7 for slot 0 (no `one′` row). -/
theorem linkRowsB4_length (κ : NodeKind) (σ : ℕ) :
    (linkRowsB4 κ σ).length = if σ = 0 then 7 else 8 := by
  unfold linkRowsB4; split_ifs <;> simp [Circ.kinds, actRows4_length]

/-- A slot's pack rows: `1 + 1 + 8,782` for a segment 0, `1 + 136 + 8,782` for a later sub-slot. -/
theorem packRows4_length_le (κ : NodeKind) (σ : ℕ) : (packRows4 κ σ).length ≤ 8919 := by
  unfold packRows4 packHead4 packWf4
  rcases packB κ σ with _ | ⟨b0, G⟩
  · simp
  · simp only [List.length_append, List.length_cons, headRows_length, wfRows, List.length_map, wfSeg_length]
    split_ifs <;> omega

/-- S-E13b's node rows at a slot: at most 7,904. -/
theorem extRowsC_length_le (κ : NodeKind) (σ : ℕ) : (extRowsC κ σ).length ≤ 12136 := by
  unfold extRowsC
  split_ifs with h1 h2
  · subst h1; rw [xRowsK_eq]
    have := W4.extRows4_length_le κ 1
    simpa [W4.extRows4] using this
  · simp
  · simp

/-- (+) A slot's link rows fit its link region (at most `8 + 8,919 + 12,056` of `2^15`). -/
theorem linkRows4_length_le (κ : NodeKind) (σ : ℕ) : (linkRows4 κ σ).length < linkN := by
  have h1 := linkRowsB4_length κ σ
  have h2 := packRows4_length_le κ σ
  have h3 := extRowsC_length_le κ σ
  rw [linkRows4, List.length_append, List.length_append]
  simp only [linkN]
  split_ifs at h1 <;> omega

end Rev4
end FR
