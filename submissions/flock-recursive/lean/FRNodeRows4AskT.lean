-- New for `flock-recursive` (PACK-4.4.1 §1.3, §4.2; IMP-RESULT §5 item 2; track ASK-T): the ask
-- templates' generator, below `FRNodeRows4` so that the node's M rows hold its rows.
import FRNodeRows4AskPosT
import FRNodeRows4Pack

/-!
# The ask generator: every ask's query and answer bound to arena₁

At ask `k` of a prototype's compile trail (`trailRows`), **`askRowsG`** emits rows in the prototype's
frame over arena₁ (the slot's stream elements, `FRNodeRows4AskPosF.a1_slot`):

* **the item check**: the op asks item `k` of `seq4` (`itemsT`), else one failing row;
* **the digest operands** (an absorb's or a squeeze's state, a Merkle node's halves: `dopRows`): the
  operand's two cells are the query's elements in arena₁ (element `qElT k`, from the item's stream
  offset, its length word and its tag). Where the operand's slot or the node's activity depends on
  the kind, one row per kind gated by its selector; at a kind whose depth is inactive the elements
  are zero (`nodeQF i 0 0`);
* **the seed's `vk` and `c`**: arena₁'s elements `qElT 0 … + 3` are IMP's `input` cells (`inCT`);
* **the byte operand** (the seed's `hdr`, an absorb's message, a column): no row. The previous op is
  `piField` at the item's **source** (`srcT`: the absolute offset and length of the proof bytes the
  reassembled proof takes from this item's query), and the operand is its result; else one failing
  row (`preOk`);
* **the answer**: the answer slot's two cells are arena₁'s elements `aElT k`, `aElT k + 1`.

The tags and length words need no row here: the pack rows pin every item's first element
(`FRNodeRows4Pack.wfRows`, `headRows`). The tables are closed constants built once per process.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## The byte sources -/

/-- **Phase `n`'s byte sources**, one per item (`Sh.itemsL`'s order): the absolute offset and length
of the proof bytes `reassemble4` takes from the item's query (`FRNodeRows4AskPosR`: the seed's `hdr`,
an absorb's message, a round's message, a column), `none` for an item that gives none. -/
def Sh.srcL (S : Seq) (n : ℕ) : Sh → List (Option (ℕ × ℕ))
  | .seed => [some (fieldOffOf S fHdr + phaseOffOf S n fHdr, 48)]
  | .absorb g len => [if g < nFields4 then some (fieldOffOf S g + phaseOffOf S n g, len) else none]
  | .squeezes k _ => List.replicate k none
  | .uni g => [if g < nFields4 then some (fieldOffOf S g + phaseOffOf S n g, uniBytes) else none, none]
  | .rounds g k _ inK =>
    let o := fieldOffOf S g + phaseOffOf S n g
    (List.range k).flatMap fun p =>
      [if g < nFields4 then some (o + p * roundBytes inK, roundBytes inK) else none, none]
  | .queries i =>
    let o := fieldOffOf S fCols + phaseOffOf S n fCols
    (List.range (S.lv i).t).flatMap fun p =>
      some (o + p * colBytes i, colBytes i) :: List.replicate (S.lv i).sib none

/-- **The byte sources of `S`'s items** (aligned with `itemsOf S`). -/
def srcOf (S : Seq) : List (Option (ℕ × ℕ)) := (phasesOf S).zipIdx.flatMap fun p => p.1.2.srcL S p.2

/-! ## The tables (closed constants)

They are irreducible to the elaborator: a defeq check that reaches them (through `askTG`) would
otherwise evaluate `itemsOf seq4`. Proofs read them through `FRNodeRows4AskTB.itemsT_get` etc. -/

/-- `seq4`'s items. -/
@[irreducible] def itemsT : Array Item := (itemsOf seq4).toArray

/-- Their byte sources. -/
@[irreducible] def srcT : Array (Option (ℕ × ℕ)) := (srcOf seq4).toArray

/-- Their stream offsets after the trace's first byte (`itOff`: prefix sums of the stream lengths). -/
@[irreducible] def offT : Array ℕ := ((itemsOf seq4).scanl (fun o it => o + it.slen) 0).toArray

/-- **Item `k`'s first query element** (segment-relative): past its stream offset, its length word
and its tag (the seed's `vk`, every other query's first digest). -/
def qElT (k : ℕ) (it : Item) : ℕ := (1 + offT.getD k 0 + 8 + (itemTag it).length) / 16

/-- **Item `k`'s answer's first element** (segment-relative). -/
def aElT (k : ℕ) (it : Item) : ℕ := (1 + offT.getD k 0 + 8 + it.qlen) / 16

/-! ## The rows -/

/-- Arena₁'s cell of stream element `e` in prototype `π`'s frame. -/
def arC (π e : ℕ) : ℕ := π * slotM4 + arA1 + e

/-- `one · (l − c) = 0`: the form `l` is the cell `c`. -/
def eqCR (P : Params) (l : Lin) (c : ℕ) : Row := ⟨P.one, l.sub (Lin.cell c), []⟩

/-- Nothing if `b`, else one failing row. -/
def chkR (P : Params) (b : Bool) : List Row := if b then [] else [failRT P]

/-- Active at every kind. -/
def actAll (act : KC Bool) : Bool := act .L32 && act .P30 && act .N30

/-- **A digest operand on arena₁'s elements `E`, `E + 1`** (`act`: the kinds whose query carries it;
elsewhere the elements are zero). One row per half if the operand's slot and the activity do not
depend on the kind; otherwise one row per kind and half, gated by the kind's selector (a wrong slot
shape at an active kind: the gated failing row `sel · one = 0`). -/
def dopRows (P : Params) (cs : CS) (r π E : ℕ) (act : KC Bool) : List Row :=
  if actAll act && decide (cs.slotK r .P30 = cs.slotK r .L32) && decide (cs.slotK r .N30 = cs.slotK r .L32) then
    match cs.slotK r .L32 with
    | some (.d, [l₀, l₁]) => [eqCR P l₀ (arC π E), eqCR P l₁ (arC π (E + 1))]
    | _ => [failRT P]
  else kinds.flatMap fun κ =>
    if act κ then
      match cs.slotK r κ with
      | some (.d, [l₀, l₁]) =>
        [⟨P.sel κ, l₀.sub (Lin.cell (arC π E)), []⟩, ⟨P.sel κ, l₁.sub (Lin.cell (arC π (E + 1))), []⟩]
      | _ => [⟨P.sel κ, P.one, []⟩]
    else [⟨P.sel κ, Lin.cell (arC π E), []⟩, ⟨P.sel κ, Lin.cell (arC π (E + 1)), []⟩]

/-- **The answer** on arena₁'s elements `E`, `E + 1` (the ask's digest slot). -/
def ansRowsT (X : Ext) (P : Params) (cs : CS) (op : Op) (π E : ℕ) : List Row :=
  match (stepOut X P cs op).slots with
  | [some (.d, [l₀, l₁])] => [eqCR P l₀ (arC π E), eqCR P l₁ (arC π (E + 1))]
  | _ => [failRT P]

/-- **The byte operand `m` is the previous `piField`'s result, read at item `k`'s source.** -/
def preOk (cs : CS) (pre : Option Op) (m k : ℕ) : Bool :=
  match pre with
  | some (.piField f o len) => decide (m + 1 = cs.slots.size) && decide (srcT[k]? = some (some (absOff f o, len)))
  | _ => false

/-- **The rows at ask `k`** (prototype `π`, extension `X`). -/
def askRowsG (X : Ext) (π : ℕ) (P : Params) (cs : CS) (pre : Option Op) (op : Op) (k : ℕ) : List Row :=
  match op.item? with
  | none => []
  | some it =>
    if itemsT[k]? = some it then
      let q := qElT k it
      (match op with
        | .askSeed h =>
          chkR P (preOk cs pre h k) ++
            (List.range 4).map fun j => eqCR P (Lin.cell (arC π (q + j))) (inCT π (j / 2) (j % 2))
        | .askAbsorb st m _ => chkR P (preOk cs pre m k) ++ dopRows P cs st π q fun _ => true
        | .askSqueeze st => dopRows P cs st π q fun _ => true
        | .askNode _ _ l r act => dopRows P cs l π q act ++ dopRows P cs r π (q + 2) act
        | .askCol _ c => chkR P (preOk cs pre c k)
        | _ => []) ++
        ansRowsT X P cs op π (aElT k it)
    else [failRT P]

/-- **The ask generator** of prototype `π` (extension `X`): rows at every ask, covering no other op. -/
def askTGT (X : Ext) (π : ℕ) : TG := ⟨fun _ => false, askRowsG X π⟩

end Rev4
end FR
