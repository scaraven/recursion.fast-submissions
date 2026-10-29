-- New for `flock-recursive` (PACK-4.4.1 §1.3, §5.2; IMP-RESULT §5.3; SRA-RESULT §6; track IMPC): the
-- import-class generators `impcTG` (proof fields, challenge conversions, zero pins) and `colTG`, below `FRNodeRows4`.
import FRNodeRows4AskPosT
import FRNodeKinds4

/-!
# The import classes' row generator (`impcTG`)

B3's `ATImp` binds a covered op's import cells to its value at the slot's input. This module gives
the rows, as a generator along the compile's trail (`FRNodeRows4AskPosT.TG`), so that `FRNodeRows4`
can fold them with the other ask templates' (`askTG π := … .add (impcTG (XofT π) π)`):

* **Proof fields at a static offset** (`piElem`, `piElemK`, `piDigest`; PACK §1.3 "proof fields
  except siblings", and (β′)'s cap-check reads of `A`, the caps and `D`): a 16-byte window of the
  proof that is one whole stream element of the slot's segment is arena₁'s cell of that element.
  **`pfLoc o`** finds which item's query byte proof byte `o` is (the field's phase part, `pSegs`, then
  the phase's shape, `phItem`), **`winE o`** the element of a window `[o, o + 16)` if its 16 bytes are
  16 consecutive query bytes of one item starting on an element boundary (outside the segment's last
  block). A covered read gets one row per `F` component, `1·(l − A₁(e)) = 0`.
* **Challenge conversions** (`chF a c`, `c < 2`, and `chK a`): the import cells are the answer
  register's own cells (`dlo`/`dhi`), read off its slot.

* **Zero pins** (SRA §6.3): at a foreign `assertZero a act` whose operand is a `piField`'s bytes
  (`provL`: the program's `piField` registers, passed in as `pv`) and whose windows are elements, each
  window's arena₁ cell is pinned, `gate act · A₁(e) = 0`.
* **`colTG`** (separate, ≈ 27.9 k rows per prototype): a `dotKF`'s `felems` auxiliary cells on the
  arena₁ cells of its column's windows.

Reads whose window is not an element (the statement's `h`/`n` at stmt bytes 1 and 33) and the
siblings (`fSibs`, the half of a node query chosen by a position bit) are not covered: they stay
residual imports.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## Tables (computed once at process start) -/

/-- **Item `k`'s stream offset** `Σ_{j<k} slen_j` (in a segment, after its first byte), as a table. -/
def itOffA : Array ℕ := (((itemsOf seq4).map Item.slen).scanl (· + ·) 0).toArray

/-- `seq4`'s items, as a table. -/
def itemsA : Array Item := (itemsOf seq4).toArray

/-- `seq4`'s phases, as a table. -/
def phasesA : Array (String × Sh) := (phasesOf seq4).toArray

/-- **Phase `n`'s first item**: `Σ_{q<n} |items of phase q|`, as a table. -/
def phIxA : Array ℕ := (((phasesOf seq4).map fun p => (p.2.itemsL seq4.lv).length).scanl (· + ·) 0).toArray

/-- A field's phase part: its absolute start, length, the field and the phase. -/
structure PSeg where
  st : ℕ
  len : ℕ
  f : ℕ
  n : ℕ

/-- **The proof's phase parts** (every field `f`, every phase `n` contributing bytes to it): field `f`'s
bytes of phase `n` start at `fieldOffOf seq4 f + phaseOffOf seq4 n f` (the generators' `o f`). -/
def pSegs : List PSeg :=
  (List.range nFields4).flatMap fun f => (List.range (phasesOf seq4).length).filterMap fun n =>
    let len := ((phasesOf seq4).getD n ("", .seed)).2.bytesToL seq4.lv f
    if len = 0 then none else some ⟨fieldOffOf seq4 f + phaseOffOf seq4 n f, len, f, n⟩

/-- **Which query byte of the phase's items byte `j` of its part of field `f` is**: the item (relative
to the phase's first) and the query byte (`ctb4`'s shapes; `none` for the siblings). -/
def phItem (sh : Sh) (f j : ℕ) : Option (ℕ × ℕ) :=
  match sh with
  | .seed => if f = fHdr then some (0, 71 + j) else none
  | .absorb g _ => if f = g then some (0, 40 + j) else none
  | .uni g => if f = g then some (0, 40 + j) else none
  | .rounds g _ _ inK => if f = g then some (2 * (j / roundBytes inK), 40 + j % roundBytes inK) else none
  | .queries i =>
    if f = fCols then some ((1 + (seq4.lv i).sib) * (j / colBytes i), 8 + j % colBytes i) else none
  | .squeezes _ _ => none

/-- **Proof byte `o`'s item and query byte** (`(k, q)`: byte `q` of item `k`'s query). -/
def pfLoc (o : ℕ) : Option (ℕ × ℕ) :=
  match pSegs.find? (fun s => decide (s.st ≤ o ∧ o < s.st + s.len)) with
  | some s =>
    (phItem (phasesA.getD s.n ("", .seed)).2 s.f (o - s.st)).map fun r => (phIxA.getD s.n 0 + r.1, r.2)
  | none => none

/-- **A 16-byte proof window that is one stream element** of the slot's segment: `[o, o + 16)` are
query bytes `[q, q + 16)` of one item `k`, the window starts on an element boundary, and item `k` is
not the last block's. The element. -/
def winE (o : ℕ) : Option ℕ :=
  match pfLoc o with
  | some (k, q) =>
    let x := 1 + itOffA.getD k 0 + 8 + q
    if x % 16 = 0 ∧ k < itemsA.size ∧ q + 16 ≤ (itemsA.getD k .seed).qlen ∧
        1 + itOffA.getD k 0 + (itemsA.getD k .seed).slen + 64 ≤ N4c.segB ∧
        (List.range 16).all (fun t => pfLoc (o + t) == some (k, q + t)) = true
    then some (x / 16) else none
  | none => none

/-! ## The generator -/

/-- **A component on arena₁'s element `e`** (prototype `π`'s frame): `1·(l − A₁(e)) = 0`. -/
def a1Row (P : Params) (π : ℕ) (l : Lin) (e : ℕ) : Row := ⟨P.one, l.sub (Lin.cell (π * slotM4 + arA1 + e)), []⟩

/-- `l` equals `m`: `1·(l − m) = 0`. -/
def eqLRow (P : Params) (l m : Lin) : Row := ⟨P.one, l.sub m, []⟩

/-- **A static proof read's rows**: its `F` components on the elements of its windows. -/
def pfRows (P : Params) (π : ℕ) (sl : List Slot) (t : Ty) (os : List ℕ) : List Row :=
  match sl with
  | [some (t', ls)] =>
    if t' = t ∧ ls.length = os.length then
      (ls.zip os).flatMap fun p => match winE p.2 with
        | some e => [a1Row P π p.1 e]
        | none => [failRT P]
    else [failRT P]
  | _ => [failRT P]

/-- **A challenge conversion's rows**: its components are the answer's (a digest slot `[a₀, a₁]`, the
same at every kind): `chF a c` is `a_c`, `chK a` is `[a₀, a₁]`. -/
def chRows (P : Params) (cs : CS) (a : ℕ) (sl : List Slot) (t : Ty) (cs' : List ℕ) : List Row :=
  match cs.kslots.lookup a, cs.slot a, sl with
  | none, some (.d, [a₀, a₁]), [some (t', ls)] =>
    if t' = t ∧ ls.length = cs'.length then
      (ls.zip cs').map fun p => eqLRow P p.1 (if p.2 = 0 then a₀ else a₁)
    else [failRT P]
  | _, _, _ => [failRT P]

/-! ## Register provenance, zero pins, column words -/

/-- **The `piField` registers of an op list** from register `n`: `(r, f, o, len)` for the register `r` a
`piField f o len` appends (each op appends `Op.outs` registers). -/
def provL : ℕ → List Op → List (ℕ × ℕ × ℕ × ℕ)
  | _, [] => []
  | n, op :: ops =>
    (match op with | .piField f o len => [(n, f, o, len)] | _ => []) ++ provL (n + op.outs) ops

/-- Register `r`'s `piField` (its field, offset, length), if a `piField` appended it. -/
def provOf (pv : List (ℕ × ℕ × ℕ × ℕ)) (r : ℕ) : Option (ℕ × ℕ × ℕ) :=
  (pv.find? (·.1 == r)).map (·.2)

/-- **A byte register's windows are elements**: its bytes `[o, o + len)` of the proof are `len / 16`
whole windows `winE` accepts (`len ≡ 0 mod 16`), inside the proof. -/
def winsOk (f o len : ℕ) : Bool :=
  decide (len % 16 = 0) && decide (absOff f o + len ≤ piSizeOf seq4) &&
    (List.range (len / 16)).all fun t => (winE (absOff f o + 16 * t)).isSome

/-- **The zero pins of a foreign `assertZero a act`** whose operand is a `piField`'s bytes: each of its
windows' arena₁ cell is `0` at the active kinds (`gate act · A₁(e) = 0`). -/
def zRows (P : Params) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) (cs : CS) (a : ℕ) (act : KC Bool) : List Row :=
  match provOf pv a with
  | some (f, o, len) =>
    if a < cs.slots.size ∧ winsOk f o len = true then
      (List.range (len / 16)).filterMap fun t =>
        (winE (absOff f o + 16 * t)).map fun e => ⟨P.gate act, Lin.cell (π * slotM4 + arA1 + e), []⟩
    else []
  | none => []

/-- **A column's word cells** (`dotKF`'s auxiliary import `felems n` on register `r`, a `piField`'s
bytes): cell `b` is arena₁'s cell of window `b` (`b < len / 16`), else `0`. -/
def colRows (P : Params) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) (sz : ℕ) (cells : List Lin) (r n : ℕ) : List Row :=
  match provOf pv r with
  | some (f, o, len) =>
    if cells.length = n ∧ r < sz ∧ winsOk f o len = true then
      (cells.zipIdx).filterMap fun p =>
        if p.2 < len / 16 then (winE (absOff f o + 16 * p.2)).map fun e => a1Row P π p.1 e
        else some ⟨P.one, p.1, []⟩
    else []
  | none => []

/-- The `felems` auxiliary imports' rows (`bits` ones are not bound here). -/
def auxRows (P : Params) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) (sz : ℕ) : List (List Lin × ℕ × AuxK) → List Row
  | [] => []
  | (cells, r, .felems n) :: as => colRows P π pv sz cells r n ++ auxRows P π pv sz as
  | (_, _, .bits _) :: as => auxRows P π pv sz as

/-- **The rows at an op** (prototype `π`, extension `X`, the program's `piField` registers `pv`). At an
`assertZero` or a `dotKF` (no import of their own as compiled) a failing row if the compile made them
imports. -/
def impcRows (X : Ext) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) (P : Params) (cs : CS) (op : Op) : List Row :=
  match op with
  | .piElem f o => pfRows P π (stepOut X P cs op).slots .f [absOff f o]
  | .piElemK f o => pfRows P π (stepOut X P cs op).slots .k [absOff f o, absOff f o + 16]
  | .piDigest f o => pfRows P π (stepOut X P cs op).slots .d [absOff f o, absOff f o + 16]
  | .chF a c => chRows P cs a (stepOut X P cs op).slots .f [c]
  | .chK a => chRows P cs a (stepOut X P cs op).slots .k [0, 1]
  | .assertZero a act => if (stepOut X P cs op).imp then [failRT P] else zRows P π pv cs a act
  | _ => []

/-- **The ops it covers**: static proof reads whose windows are elements, challenge conversions, and
(for their zero pins only) `assertZero`. -/
def impcCov : Op → Bool
  | .piElem f o => (winE (absOff f o)).isSome
  | .piElemK f o | .piDigest f o => (winE (absOff f o)).isSome && (winE (absOff f o + 16)).isSome
  | .chF _ c => decide (c < 2)
  | .chK _ => true
  | .assertZero .. => true
  | _ => false

/-- **The import-class generator** of prototype `π` (extension `X`; `pv` the program's `piField`
registers, `provL 0 (protoProg π).ops`). -/
def impcTG (X : Ext) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) : TG where
  cov := impcCov
  rows P cs _ op _ := impcRows X π pv P cs op

/-- Whether an op is a `dotKF`. -/
def isDotKF : Op → Bool
  | .dotKF .. => true
  | _ => false

/-- **The column-word generator** of prototype `π` (`dotKF`'s `felems` auxiliary imports on arena₁; a
failing row if the compile made the `dotKF` an import). Separate from `impcTG`: ≈ 27.9 k rows per
prototype. -/
def colTG (X : Ext) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) : TG where
  cov := isDotKF
  rows P cs _ op _ :=
    if isDotKF op then
      if (stepOut X P cs op).imp then [failRT P] else auxRows P π pv cs.slots.size (stepOut X P cs op).aux
    else []

end Rev4
end FR
