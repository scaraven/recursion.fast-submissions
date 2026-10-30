-- New for `flock-recursive` (IMPC2 §0–§4, PACK-4.4.1 §5.2; track IMPC2): the shared bit area's rows
-- (position bits, statement bits) and the generator `bitTG`, below `FRNodeRows4`.
import FRNodeRows4AskBL
import FRNodeRows4AskI
import FRNodeRows4AskT
import FRVIR4Mux

/-!
# The bit area and its generator (`bitTG`)

The import cells of a position bit, a sibling, a `tensorW`'s `bits 20` and an unaligned statement
read are free M cells, and a bit of an `F` element is not `F`-linear. This module gives them Boolean
cells: the slot's **bit area** (`FRNodeRows4ArenaPlace`'s `arBt`, Boolean by `bitRows4`), laid out
(relative to `arBt`) as

* **positions** `[0, nPos)`, position-major and kind-free: bit `h` of position `p` of level `i` is
  `posCell i p h = posB i + p·logN*ᵢ + h` (`logN*ᵢ` at `m* = 32`, the largest);
* **spares** `[nPos, nPos + spareN)`: the answer bits no position uses, numbered per kind (the kinds
  share the range: one is selected);
* **statement bits** `[stmtB, stmtB + 8·(z − 1))`: bits `8 … 8z − 1` of the statement message
  (bytes `1 … z − 1`; byte `0` is the tag and bytes `≥ z` the zero tail, both constants).

**Decomposition rows** (once, at the seed's ask): each P2 answer half (arena₁'s element
`aElT k + c`) is `Σ_{j<128} e_j·cell(j)` under each kind's map (`ansCell`), gated by the kinds that
map alike; each statement element is its constant part plus `Σ e_j·cell(j)`. `e_j` (`eBit`) is the
`F` element with bit `j` alone, so Boolean cells are exactly the element's bits.

**Per-op rows** (`bitRowsOp`):

* a **sibling** read (`piDigest` in a `fSibs` part, `sibLoc`): `b·(l − r) = sib − r` per half, `b`
  the position bit, `l`, `r` the node query's halves on arena₁ (`qElT`); `sib = 0` at the kinds whose
  depth is inactive;
* an **unaligned statement read** (`stmtWins`): each 16-byte window is `Σ e_i·s(·)`;
* after a **`bitOf r h`** (at the following `selectHalf`, whose bit operand it is): the import cell is
  the bit's source (`bitSrc`: through the `idx`/`shrN` provenance to an answer's or the statement's
  bit cell, or zero);
* a **`tensorW`**'s `bits n` auxiliary cells: bit `i` of its index register, the same way.

Kind-dependent sources become one copy row, one product row (two classes) or one gated row per kind
(`selRows`). Everything is computed from the prototype's op list and its kind group (tables built
once per prototype, `BTab`); a check that fails gives a failing row, never a decision over the program.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## Bits of `F` -/

/-- `eBit`'s table (`j < 128`). -/
@[irreducible] def eBitT : Array F := ((List.range 128).map eBit).toArray

/-- `Σ e_j · cell` over `(j, cell)` pairs (absolute cells). -/
def bitsLin (cs : List (ℕ × ℕ)) : Lin := cs.map fun p => (p.2, eBitT.getD p.1 0)

/-- `a − b` without a product per term (`Lin.sub`'s value: `F`'s negation is the identity). -/
def subN (a b : Lin) : Lin := a ++ b.map fun t => (t.1, -t.2)

/-- **The tag element**: byte `0` is `t`, the rest zero. -/
def tagF (t : UInt8) : F := ⟨⟨t.toUInt64⟩, ⟨0⟩⟩

/-! ## The position layout (kind-free) -/

/-- `seq4`'s levels (at `m*`). -/
@[irreducible] def lvT : Array Level := ((List.range nLevels).map seq4.lv).toArray

/-- **Level `i`'s first position cell** (relative): `Σ_{i'<i} tᵢ'·logN*ᵢ'`. -/
@[irreducible] def posBT : Array ℕ :=
  (((List.range nLevels).map fun i => (seq4.lv i).t * (seq4.lv i).logN).scanl (· + ·) 0).toArray

/-- **Bit `h` of position `p` of level `i`** (relative to the bit area). -/
def posCell (i p h : ℕ) : ℕ := posBT.getD i 0 + p * (lvT.getD i ⟨0, 1, 0, 0⟩).logN + h

/-- The position cells' count. -/
def nPos : ℕ := posBT.getD nLevels 0

/-! ## The tables of a prototype -/

/-- **What made a register** (the provenance the bit sources follow). -/
inductive RI where
  | none
  /-- The answer of ask `k`. -/
  | ans (k : ℕ)
  | idx (a b i : KC ℕ)
  | shr (n : ℕ) (s : KC ℕ)
  /-- A digest read at absolute offset `o`. -/
  | dig (o : ℕ)
  /-- A byte read `[o, o + len)`. -/
  | pf (o len : ℕ)
  /-- A byte constant. -/
  | cb (bs : ByteArray)
  deriving Inhabited

/-- The entries op `op` appends (the ask counter `k`, the register count `n`): an `idx`/`shrN` only on
earlier registers, a byte constant only if it is the same at every kind (the run proofs read them). -/
def riOf (k n : ℕ) (op : Op) : List RI :=
  if op.item?.isSome then [.ans k] else
  match op with
  | .idx a b i => if a .L32 < n ∧ a .P30 < n ∧ a .N30 < n then [.idx a b i] else [.none]
  | .shrN m s => if m < n then [.shr m s] else [.none]
  | .piDigest f o => [.dig (absOff f o)]
  | .piField f o len => [.pf (absOff f o) len]
  | .const c => match c .L32, c .P30, c .N30 with
    | .b x, .b y, .b z => if x = y ∧ x = z then [.cb x] else [.none]
    | _, _, _ => [.none]
  | op => List.replicate op.outs .none

/-- **The provenance array**: entry `r` says what made register `r` (tail-recursive). -/
def riAcc : ℕ → List Op → Array RI → Array RI
  | _, [], acc => acc
  | k, op :: ops, acc => riAcc (if op.item?.isSome then k + 1 else k) ops (acc ++ (riOf k acc.size op).toArray)

/-- The kind's index in `kinds`. -/
def kix : Kind → ℕ
  | .L32 => 0 | .P30 => 1 | .N30 => 2

/-- **The statement's layout** read off the program: its offset `so` and tag `t` (the `assertEq` of a
1-byte `piField` and a 1-byte constant), its zero tail from byte `z` to its end `L` (the `assertZero`
of a `piField` starting inside it). -/
structure StSpec where
  so : ℕ
  t : UInt8
  z : ℕ
  L : ℕ

/-- The tag's `(offset, byte)`. -/
def tagScan (rt : Array RI) : List Op → Option (ℕ × UInt8)
  | [] => none
  | .assertEq a b _ :: ops =>
    match rt.getD a .none, rt.getD b .none with
    | .pf o 1, .cb bs => if bs.size = 1 then some (o, bs.get! 0) else tagScan rt ops
    | _, _ => tagScan rt ops
  | _ :: ops => tagScan rt ops

/-- The zero tail `(start, length)` of a statement at `so`. -/
def tailScan (rt : Array RI) (so : ℕ) : List Op → Option (ℕ × ℕ)
  | [] => none
  | .assertZero a _ :: ops =>
    match rt.getD a .none with
    | .pf o len => if so < o ∧ o < so + 128 then some (o, len) else tailScan rt so ops
    | _ => tailScan rt so ops
  | _ :: ops => tailScan rt so ops

/-- **A prototype's bit tables** (built once per prototype). -/
structure BTab where
  /-- The provenance array. -/
  rt : Array RI
  /-- Each kind's ladder (`kix`, then the level). -/
  lv : Array (Array Level)
  /-- Item `k`'s answer place, if a P2 answer: level, index in its phase, global answer index. -/
  ans : Array (Option (ℕ × ℕ × ℕ))
  /-- Each kind's first spare (relative to the spare range) per global answer index. -/
  sp : Array (Array ℕ)
  /-- The spare range's size (the kinds' maximum). -/
  spN : ℕ
  /-- The statement's layout. -/
  st : Option StSpec

/-- Kind `ι`'s level `i`. -/
def BTab.lvl (T : BTab) (ι : Kind) (i : ℕ) : Level := (T.lv.getD (kix ι) #[]).getD i ⟨0, 1, 0, 0⟩

/-- **The answer bits positions use** (answer `q` of a level at ladder `K`): `min(per, t − q·per)`
positions of `logN` bits. -/
def usedBits (K : Level) (q : ℕ) : ℕ := Nat.min K.per (K.t - q * K.per) * K.logN

/-- The P2 answers' places: `(item, level, index)` in item order. -/
@[irreducible] def ansList : List (ℕ × ℕ × ℕ) :=
  (List.range (phasesOf seq4).length).flatMap fun n =>
    match ((phasesOf seq4).getD n ("", .seed)).2 with
    | .squeezes k (.pos i) => (List.range k).map fun q => (phIxA.getD n 0 + q, i, q)
    | _ => []

/-- The spares of one kind's answers, in order (`0` for an answer the kind does not use). -/
def spareL (lv : Array Level) : List ℕ :=
  ansList.map fun a =>
    let K := lv.getD a.2.1 ⟨0, 1, 0, 0⟩
    if a.2.2 < K.sq then 256 - usedBits K a.2.2 else 0

/-- **The tables** of a prototype (its op list `ops`, its kind group `G`). -/
def mkTab (ops : List Op) (G : Grp) : BTab :=
  let rt := riAcc 0 ops #[]
  let lv : Array (Array Level) :=
    (kinds.map fun ι => ((List.range nLevels).map fun i => seq4.lvK (G ι).d.m i).toArray).toArray
  let al := ansList
  let ans := (al.zipIdx.foldl (fun (a : Array (Option (ℕ × ℕ × ℕ))) p =>
      a.set! p.1.1 (some (p.1.2.1, p.1.2.2, p.2)))
    (Array.replicate (itemsOf seq4).length none))
  let sl := lv.toList.map spareL
  let sp := (sl.map fun l => (l.scanl (· + ·) 0).toArray).toArray
  let spN := (sl.map List.sum).foldl Nat.max 0
  let st := (tagScan rt ops).bind fun p =>
    (tailScan rt p.1 ops).map fun q => ⟨p.1, p.2, q.1 - p.1, q.1 + q.2 - p.1⟩
  ⟨rt, lv, ans, sp, spN, st⟩

/-! ## Cells -/

/-- The statement bits' first cell (relative): after the positions and the spares. -/
def BTab.stmtB (T : BTab) : ℕ := nPos + T.spN

/-- **Bit `j` of answer item `k` at kind `ι`** (relative cell): its position's bit, or a spare;
`none` if the kind does not use the answer or `j ≥ 256`. -/
def BTab.ansCell (T : BTab) (ι : Kind) (k j : ℕ) : Option ℕ :=
  match T.ans.getD k none with
  | some (i, q, g) =>
    let K := T.lvl ι i
    if q < K.sq ∧ j < 256 then
      let u := usedBits K q
      if j < u then some (posCell i (q * K.per + j / K.logN) (j % K.logN))
      else some (nPos + (T.sp.getD (kix ι) #[]).getD g 0 + (j - u))
    else none
  | none => none

/-- **Statement bit `b`** (bit `b % 8` of byte `b / 8` of the message): its cell (`some (some c)`),
the constant zero of the tail (`some none`), or `none` (the tag byte, or outside the message). -/
def BTab.stCell (T : BTab) (b : ℕ) : Option (Option ℕ) :=
  match T.st with
  | some s =>
    if 8 ≤ b ∧ b < 8 * s.z then some (some (T.stmtB + (b - 8)))
    else if 8 * s.z ≤ b ∧ b < 8 * s.L then some none else none
  | none => none

/-- **The source of bit `h` of the `N` value an `idx a b i` makes** (at kind `ι`): zero above its
`b` bits, else bit `i·b + h` of the digest it indexes (a P2 answer's cell or a statement cell). -/
def BTab.idxSrc (T : BTab) (a b i : KC ℕ) (h : ℕ) (ι : Kind) : Option (Option ℕ) :=
  if b ι ≤ 24 then
    if h < b ι then
      match T.rt.getD (a ι) .none with
      | .ans k => (T.ansCell ι k (i ι * b ι + h)).map some
      | .dig o =>
        match T.st with
        | some s => if s.so ≤ o ∧ i ι * b ι + h < 256 then T.stCell (8 * (o - s.so) + i ι * b ι + h) else none
        | none => none
      | _ => none
    else some none
  else none

/-- **The source of bit `h` of register `r`** at kind `ι`: an `idx`'s, or a `shrN` of an `idx` (bit
`h + s` of it). -/
def BTab.bitSrc (T : BTab) (r h : ℕ) (ι : Kind) : Option (Option ℕ) :=
  match T.rt.getD r .none with
  | .idx a b i => T.idxSrc a b i h ι
  | .shr n s =>
    match T.rt.getD n .none with
    | .idx a b i => T.idxSrc a b i (h + s ι) ι
    | _ => none
  | _ => none

/-! ## Rows -/

/-- The bit area's cell `c` (relative) in prototype `π`'s frame. -/
def bitC (π c : ℕ) : ℕ := π * slotM4 + arBt + c

/-- A source's form: the cell, or zero. -/
def srcLin (π : ℕ) : Option ℕ → Lin
  | some c => Lin.cell (bitC π c)
  | none => []

/-- `Σ_{κ : act κ} sel_κ` (no zero terms). -/
def gateS (P : Params) (act : KC Bool) : Lin := kinds.flatMap fun κ => if act κ then P.sel κ else []

/-- **`imp` is the selected kind's source**: one copy row if the kinds agree; one product row
`g_A·(a − b) = imp − b` for two classes (`A` the kinds with `L32`'s source); one gated row per kind
otherwise; a failing row if a kind has none. -/
def selRows (P : Params) (π : ℕ) (imp : Lin) (src : KC (Option (Option ℕ))) : List Row :=
  match src .L32, src .P30, src .N30 with
  | some a, some b, some c =>
    let v : KC (Option ℕ) := fun ι => match ι with | .L32 => a | .P30 => b | .N30 => c
    if b = a ∧ c = a then [⟨P.one, subN imp (srcLin π a), []⟩]
    else if b = a ∨ c = a ∨ b = c then
      let o := if b = a then c else b
      [⟨gateS P fun ι => decide (v ι = a), subN (srcLin π a) (srcLin π o), subN imp (srcLin π o)⟩]
    else kinds.map fun ι => ⟨P.sel ι, subN imp (srcLin π (v ι)), []⟩
  | _, _, _ => [failRT P]

/-- **An answer half's decomposition rows**: per class of kinds with the same map (the kinds using
the answer), `g·(A₁(e) − Σ_{j<128} e_j·cell(128c + j)) = 0`. -/
def ansRows (T : BTab) (P : Params) (π k : ℕ) (e c : ℕ) : List Row :=
  -- each kind's map once (`kt`: the three values computed before the closure)
  let m := kt fun ι => (List.range 128).map fun j => T.ansCell ι k (128 * c + j)
  let ok := kt fun ι => (m ι).all Option.isSome
  let lin := fun ι => subN (Lin.cell (arC π e))
    (bitsLin ((m ι).zipIdx.filterMap fun p => p.1.map fun x => (p.2, bitC π x)))
  let cls : List Kind := kinds.filter fun ι => ok ι && !(kinds.any fun κ => decide (kix κ < kix ι) && ok κ &&
    decide (m κ = m ι))
  (if kinds.all fun ι => (m ι).all fun x => x.all (· < arNb) then [] else [failRT P]) ++
  cls.map fun ι =>
    let g := kinds.filter fun κ => ok κ && decide (m κ = m ι)
    if g.length = 3 then ⟨P.one, lin ι, []⟩ else ⟨gateS P fun κ => g.contains κ, lin ι, []⟩

/-- Statement element `k`'s bit cells: `(j, cell)` for each bit `128k + j` a cell takes. -/
def stCells (T : BTab) (π k : ℕ) : List (ℕ × ℕ) :=
  (List.range 128).filterMap fun j =>
    match T.stCell (128 * k + j) with
    | some (some x) => some (j, bitC π x)
    | _ => none

/-- **Statement element `k`'s row**: `A₁(e) = c·one + Σ e_j·cell` (its constant part `c`: the tag at
byte `0`; the tail is zero). -/
def stElRow (T : BTab) (P : Params) (π : ℕ) (s : StSpec) (k : ℕ) : Row :=
  match winE (s.so + 16 * k) with
  | some e =>
    ⟨P.one, subN (Lin.cell (arC π e)) (bitsLin (stCells T π k)), if k = 0 then P.one.smul (tagF s.t) else []⟩
  | none => failRT P

/-- **The decomposition rows** (once per prototype): every P2 answer's halves, every statement
element (a failing row without a statement, or if the cells overflow the bit area). -/
def globRows (T : BTab) (P : Params) (π : ℕ) : List Row :=
  (ansList.flatMap fun a =>
    match itemsT[a.1]? with
    | some it => ansRows T P π a.1 (aElT a.1 it) 0 ++ ansRows T P π a.1 (aElT a.1 it + 1) 1
    | none => [failRT P]) ++
  match T.st with
  | some s =>
    (if 1 ≤ s.z ∧ s.z ≤ s.L ∧ s.L % 16 = 0 ∧ T.stmtB + 8 * s.z ≤ arNb + 8 then [] else [failRT P]) ++
      (List.range (s.L / 16)).map (stElRow T P π s)
  | none => [failRT P]

/-- **A sibling read's place**: `(level, position, depth, node item)` of the `fSibs` byte `o` (a
32-byte boundary of a queries phase's sibling part). -/
def sibLoc (o : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match pSegs.find? (fun s => decide (s.f = fSibs ∧ s.st ≤ o ∧ o < s.st + s.len)) with
  | some s =>
    match ((phasesA.getD s.n ("", .seed)).2) with
    | .queries i =>
      let sib := (lvT.getD i ⟨0, 1, 0, 0⟩).sib
      let d := o - s.st
      if d % 32 = 0 ∧ 0 < sib then
        let p := d / 32 / sib; let h := d / 32 % sib
        some (i, p, h, phIxA.getD s.n 0 + (1 + sib) * p + 1 + h)
      else none
    | _ => none
  | none => none

/-- **A sibling's rows**: per half `c`, `b·(A₁(l_c) − A₁(r_c)) = sib_c − A₁(r_c)` (`b` the position
bit), and `g·sib_c = 0` at the kinds whose depth `h` is inactive. -/
def sibRows (T : BTab) (P : Params) (π : ℕ) (sl : List Slot) (i p h k : ℕ) : List Row :=
  match itemsT[k]?, sl with
  | some (.node i' h'), [some (.d, [s₀, s₁])] =>
    if i' = i ∧ h' = h then
      let q := qElT k (.node i h)
      let b := Lin.cell (bitC π (posCell i p h))
      let ina : KC Bool := fun ι => decide ((T.lvl ι i).sib ≤ h)
      let pr := fun (s : Lin) (c : ℕ) =>
        (⟨b, subN (Lin.cell (arC π (q + c))) (Lin.cell (arC π (q + 2 + c))),
          subN s (Lin.cell (arC π (q + 2 + c)))⟩ : Row)
      [pr s₀ 0, pr s₁ 1] ++
        (if kinds.any ina then [⟨gateS P ina, s₀, []⟩, ⟨gateS P ina, s₁, []⟩] else [])
    else [failRT P]
  | _, _ => [failRT P]

/-- **An unaligned statement read's windows** (absolute offset `o`, `n` windows): inside the message
past its tag, not on an element boundary. -/
def BTab.stWin (T : BTab) (o n : ℕ) : Bool :=
  match T.st with
  | some s => decide (s.so < o ∧ o + 16 * n ≤ s.so + s.L ∧ (o - s.so) % 16 ≠ 0)
  | none => false

/-- **An unaligned statement read's rows**: window `c`'s form is `Σ_{i<128} e_i·s(8(o + 16c − so) + i)`. -/
def stRdRows (T : BTab) (P : Params) (π : ℕ) (sl : List Slot) (t : Ty) (o n : ℕ) : List Row :=
  match T.st, sl with
  | some s, [some (t', ls)] =>
    if t' = t ∧ ls.length = n then
      (ls.zipIdx).map fun p =>
        let b0 := 8 * (o + 16 * p.2 - s.so)
        let src := (List.range 128).map fun j => (j, T.stCell (b0 + j))
        if src.all (·.2.isSome) then
          ⟨P.one, subN p.1 (bitsLin (src.filterMap fun x => match x.2 with
            | some (some c) => some (x.1, bitC π c) | _ => none)), []⟩
        else failRT P
    else [failRT P]
  | _, _ => [failRT P]

/-- An unaligned statement window's bit cells, from statement bit `b0`. -/
def rdCells (T : BTab) (π b0 : ℕ) : List (ℕ × ℕ) :=
  (List.range 128).filterMap fun j =>
    match T.stCell (b0 + j) with
    | some (some c) => some (j, bitC π c)
    | _ => none

/-- Every bit of the window from statement bit `b0` has a source. -/
def rdOk (T : BTab) (b0 : ℕ) : Bool := (List.range 128).all fun j => (T.stCell (b0 + j)).isSome

/-- **An unaligned statement read's rows** (`stRdRows` with the cells named, `bitTGS`'s). -/
def stRdRowsS (T : BTab) (P : Params) (π : ℕ) (sl : List Slot) (t : Ty) (o n : ℕ) : List Row :=
  match T.st, sl with
  | some s, [some (t', ls)] =>
    if t' = t ∧ ls.length = n then
      (ls.zipIdx).map fun p =>
        if rdOk T (8 * (o + 16 * p.2 - s.so)) then
          ⟨P.one, subN p.1 (bitsLin (rdCells T π (8 * (o + 16 * p.2 - s.so)))), []⟩
        else failRT P
    else [failRT P]
  | _, _ => [failRT P]

/-- **The `bits n` auxiliary cells' rows**: cell `i` is bit `i` of the register (an earlier one: below
the register count `m`; `n` cells). -/
def auxBRows (T : BTab) (P : Params) (π m : ℕ) : List (List Lin × ℕ × AuxK) → List Row
  | [] => []
  | (cells, r, .bits n) :: as =>
    (if r < m ∧ cells.length = n then cells.zipIdx.flatMap fun p => selRows P π p.1 (T.bitSrc r p.2)
      else [failRT P]) ++ auxBRows T P π m as
  | (_, _, .felems _) :: as => auxBRows T P π m as

/-- Whether an op is a `tensorW`. -/
def isTensorW : Op → Bool
  | .tensorW .. => true
  | _ => false

/-- **The reads `bitTGR` covers** (`ATImp` classes): sibling reads, unaligned statement reads. -/
def bitCovR (T : BTab) : Op → Bool
  | .piDigest f o => (sibLoc (absOff f o)).isSome || T.stWin (absOff f o) 2
  | .piElem f o => T.stWin (absOff f o) 1
  | .piElemK f o => T.stWin (absOff f o) 2
  | _ => false

/-- **The ops `bitTGB` covers**: every `selectHalf` (its rows only after a `bitOf`) and every
`tensorW`; neither is an import as compiled, so `ATImp` holds there vacuously. -/
def bitCovB : Op → Bool
  | .selectHalf .. => true
  | .tensorW .. => true
  | _ => false

/-- **The reads' rows** (`bitTGR`). -/
def bitRowsR (T : BTab) (X : Ext) (π : ℕ) (P : Params) (cs : CS) (_ : Option Op) (op : Op) (_ : ℕ) :
    List Row :=
  match op with
  | .piDigest f o =>
    match sibLoc (absOff f o) with
    | some (i, p, h, kk) => sibRows T P π (stepOut X P cs op).slots i p h kk
    | none => if T.stWin (absOff f o) 2 then stRdRows T P π (stepOut X P cs op).slots .d (absOff f o) 2 else []
  | .piElem f o => if T.stWin (absOff f o) 1 then stRdRows T P π (stepOut X P cs op).slots .f (absOff f o) 1 else []
  | .piElemK f o => if T.stWin (absOff f o) 2 then stRdRows T P π (stepOut X P cs op).slots .k (absOff f o) 2 else []
  | _ => []

/-- **The bits' rows** (`bitTGB`): the decomposition rows at the seed's ask; after a `bitOf`, at the
following `selectHalf`, its import cell on the bit's source; a `tensorW`'s `bits` auxiliary cells. A
covered op the compile made an import gets a failing row. -/
def bitRowsB (T : BTab) (X : Ext) (π : ℕ) (P : Params) (cs : CS) (pre : Option Op) (op : Op) (k : ℕ) :
    List Row :=
  match op with
  | .askSeed _ => if k = 0 then globRows T P π else []
  | .selectHalf b _ _ =>
    -- the extension alone (`opOut`'s `selectHalf` is never an import): no mux built per op
    if ((X P cs op).map Out.imp).getD false then [failRT P] else
    match pre with
    | some (.bitOf r h) =>
      match cs.slot b with
      | some (.bit, [l]) =>
        if b + 1 = cs.slots.size ∧ r < b then selRows P π l (T.bitSrc r h) else [failRT P]
      | _ => [failRT P]
    | _ => []
  | .tensorW .. =>
    if (stepOut X P cs op).imp then [failRT P] else auxBRows T P π cs.slots.size (stepOut X P cs op).aux
  | _ => []

/-- **The statement reads `bitTGS` covers** (`ATImp` class): the unaligned statement reads. -/
def bitCovS (T : BTab) : Op → Bool
  | .piDigest f o => T.stWin (absOff f o) 2
  | .piElem f o => T.stWin (absOff f o) 1
  | .piElemK f o => T.stWin (absOff f o) 2
  | _ => false

/-- **The statement reads' rows** (`bitTGS`). -/
def bitRowsS (T : BTab) (X : Ext) (π : ℕ) (P : Params) (cs : CS) (_ : Option Op) (op : Op) (_ : ℕ) :
    List Row :=
  match op with
  | .piDigest f o => if T.stWin (absOff f o) 2 then stRdRowsS T P π (stepOut X P cs op).slots .d (absOff f o) 2 else []
  | .piElem f o => if T.stWin (absOff f o) 1 then stRdRowsS T P π (stepOut X P cs op).slots .f (absOff f o) 1 else []
  | .piElemK f o => if T.stWin (absOff f o) 2 then stRdRowsS T P π (stepOut X P cs op).slots .k (absOff f o) 2 else []
  | _ => []

/-- **The bit tables of a prototype** (its op list, its kind group): `mkTab`, built once. -/
def bitTab (ops : List Op) (G : Grp) : BTab := mkTab ops G

/-- **The bits' generator** (decomposition, `bitOf`, `bits n`) of prototype `π`. `X` is the compile's
extension **with a template-free context** (`trailMS`'s key context): the rows read `imp`, `aux` and
the slots of imports, none of which depends on a template's body; building a `tensorW` template per op
costs ≈ 0.8 s per prototype at process start (`logs/IMPC2/bitstat-cls.log`). -/
def bitTGB (X : Ext) (π : ℕ) (T : BTab) : TG := ⟨bitCovB, bitRowsB T X π⟩

/-- **The reads' generator** (siblings, unaligned statement reads) of prototype `π`. -/
def bitTGR (X : Ext) (π : ℕ) (T : BTab) : TG := ⟨bitCovR T, bitRowsR T X π⟩

/-- **The statement reads' generator** (the unaligned statement reads of `bitTGR`, without the
siblings: IMPC2b's phase 2a) of prototype `π`. -/
def bitTGS (X : Ext) (π : ℕ) (T : BTab) : TG := ⟨bitCovS T, bitRowsS T X π⟩

/-- **Two generators side by side, each consulted only at its own ops** (its covered ops and the
asks): `B`'s covered reads (a sibling, an unaligned statement read) are reads `A`'s rows refuse when
asked (`impcTG`'s `pfRows`), and `A` is not asked there. `B.cov` is evaluated once per op, `A.cov`
only at `B`'s ops (`trailRows` asks for rows only at a covered op or an ask). -/
def TG.addD (A B : TG) : TG :=
  ⟨fun op => A.cov op || B.cov op, fun P cs pre op k =>
    if B.cov op then
      B.rows P cs pre op k ++ (if A.cov op || op.item?.isSome then A.rows P cs pre op k else [])
    else A.rows P cs pre op k ++ (if op.item?.isSome then B.rows P cs pre op k else [])⟩

/-- **`trailRows` of `addD` at the ops either covers is `add`'s with each side asked only there**: in
particular, if `B` covers nothing `A` refuses, the fold is unchanged on `A`'s side (`addD_none`). -/
theorem addD_none (A : TG) : (A.addD TG.none).cov = A.cov := by
  funext op; simp [TG.addD, TG.none]

/-- **Both** (the RESULT's `askTG` diff folds them one after the other). -/
def bitTG (X : Ext) (π : ℕ) (ops : List Op) (G : Grp) : TG :=
  let T := bitTab ops G
  (bitTGB X π T).addD (bitTGR X π T)

end Rev4
end FR
