-- G6: this module also holds the former modules `FRVIRTplPlan`, `FRVIRTplGrp` (one section each, in import order).
import FRVIRTplEval

section G6_FRVIRTplPlan

-- New for `flock-recursive` (BLUEPRINT §10 changes 17, revision 3.12 item 3; stage S-E5, track
-- L-circ).

/-!
# The evaluation plan of a slot's M rows: keys, pieces, and the search for them

BLUEPRINT §10 changes 17 (a), revision 3.12 item 3. A slot's indexed M rows (`slotIRows`: the
skeleton's rows at `off + j`, then the template instances') are cut into **pieces**: runs of rows
evaluated sparsely, and **instances** of a **key** — a raw template (a list of `RowT`) with its row
bits `A` and cell bits `B` — at row base `2^A · xh` and cell base `2^B · ch`, with input forms
`sh ++ own`: the key's **shared** inputs (the same forms for every instance in the slot) and the
instance's **own**. `FRVIRTplFast` evaluates an instance in closed form (`tplR_mle`).

Correctness does not depend on how the pieces are found: `FRVIRTplFast.mkPlan` keeps them only if
the keys are well formed (`Key.ok`) and the pieces' rows **are** the slot's rows (`eqL`, checked
once per node); otherwise the slot is one sparse piece. This module holds the search (untrusted):

* **skeleton blocks**: the compiler aligns a Merkle position and a Horner block
  (`FRVIRCompile.alignOf`); a block runs from its aligned start to its closing `assertEq` or to the
  next aligned start, and is cut into aligned pieces (`cutSeg`, B0). The tensor `eqTable` gives one
  block per `hi` index. A block's rows are abstracted (`absRows`): cells
  in its window `[c0, c0 + 2^B)` become locals, every other cell an input;
* **template instances** (S-E3's `tins`): the template's rows and input forms as they are;
* **grouping** by `(rows, A, B)`; per key, an input whose form is one cell at a fixed offset in every
  instance's window becomes a local, one with the same form in every instance of the slot is shared,
  the rest are own.
-/

namespace FR
namespace TEval
open Circ Tpl

/-! ## Keys and pieces -/

/-- **A key**: raw template rows, row bits, cell window bits. -/
structure Key where
  rows : List RowT
  A : ℕ
  B : ℕ

/-- The empty key (the default of a lookup). -/
def dkey : Key := ⟨[], 0, 0⟩

/-- Every local of a form is below `2^B`. -/
def locOk (B : ℕ) (l : LinT) : Bool :=
  l.all fun t => match t.1 with
    | .loc k => decide (k < 2 ^ B)
    | _ => true

/-- **A well-formed key** for `2^n` rows: its rows fit `2^A` rows, its locals `2^B` cells, the bits
fit the matrix (`A ≤ n`, `B ≤ 23`). -/
def Key.ok (n : ℕ) (K : Key) : Bool :=
  decide (K.A ≤ n) && decide (K.B ≤ 23) && decide (K.rows.length ≤ 2 ^ K.A) &&
    K.rows.all fun r => locOk K.B r.a && locOk K.B r.b && locOk K.B r.c

/-- **A piece** of a slot's indexed rows: sparse rows, or an instance `(key, xh, ch, own inputs)`. -/
inductive Piece where
  | sp (rows : List (ℕ × Row))
  | ins (k xh ch : ℕ) (own : List Lin)

/-- The indexed rows of an instance of raw template rows `T` at row base `X`, cell base `cb`. -/
def instIR (T : List RowT) (one : Lin) (ins : List Lin) (X cb : ℕ) : List (ℕ × Row) :=
  T.zipIdx.map fun p => (X + p.2, instRow one ins cb p.1)

/-- **A piece's indexed rows** (`sh`: the slot's shared input forms per key). -/
def Piece.rows (keys : Array Key) (sh : Array (List Lin)) (one : Lin) : Piece → List (ℕ × Row)
  | .sp rs => rs
  | .ins k xh ch own =>
    instIR (keys.getD k dkey).rows one (sh.getD k [] ++ own) (2 ^ (keys.getD k dkey).A * xh)
      (2 ^ (keys.getD k dkey).B * ch)

/-- List equality by a tail-recursive loop (the check runs over a slot's 3·10^5 rows). -/
def eqL {α : Type*} [BEq α] : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => a == b && eqL as bs
  | _, _ => false

theorem eqL_eq {α : Type*} [BEq α] [LawfulBEq α] : ∀ {l₁ l₂ : List α}, eqL l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [eqL, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, eqL_eq h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

/-! ## The search (untrusted: `mkPlan` checks its result) -/

/-- A block of skeleton rows `[r0, r1)` with its cell window `[c0, c0 + 2^B)`. -/
structure Seg where
  r0 : ℕ
  r1 : ℕ
  c0 : ℕ
  B : ℕ

/-- The alignment bits of `p`, up to `k`: the largest `j ≤ k` with `2^j ∣ p`. -/
def alignBits (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if p % 2 ^ (k + 1) = 0 then k + 1 else alignBits p k

/-- **A skeleton block `[p, r1)` cut into aligned pieces** (B0, untrusted): from `p`, the piece of
`2^k` rows, `k` the smaller of `p`'s alignment and the bits of the rows left, cut at `r1`; every piece
over the block's cell window `(c0, b)`. A block of `3u` rows at a `u`-aligned start is two pieces
(`FRVIRCompile.strideBits`). Pushed last first, as `segsGo`'s blocks. -/
def cutSeg (c0 b r1 : ℕ) : ℕ → ℕ → List Seg → List Seg
  | 0, _, acc => acc
  | fuel + 1, p, acc =>
    if r1 ≤ p then acc else
    let q := min (p + 2 ^ alignBits p (Nat.size (r1 - p - 1))) r1
    cutSeg c0 b r1 fuel q (⟨p, q, c0, b⟩ :: acc)

/-- A block `[r0, r1)`'s pieces pushed on `acc`. -/
def cutBlock (r0 r1 c0 b : ℕ) (acc : List Seg) : List Seg := cutSeg c0 b r1 (r1 - r0) r0 acc

/-- (+) A Horner block of 383 rows at a start `≡ 128 (mod 256)` is 128 + 255 rows, at a start
`≡ 0 (mod 256)` 256 + 127; (−) at a start `≡ 0 (mod 512)` it is one piece. -/
theorem cutBlock_ctl : (cutBlock 128 511 0 9 []).map (fun s => (s.r0, s.r1)) = [(256, 511), (128, 256)] ∧
    (cutBlock 256 639 0 9 []).map (fun s => (s.r0, s.r1)) = [(512, 639), (256, 512)] ∧
    (cutBlock 512 895 0 9 []).map (fun s => (s.r0, s.r1)) = [(512, 895)] := by
  decide

/-- The product blocks of a tensor `eqTable` (as `FRVIRCompile.eqTensor` lays them out), the op's
state `cs` (after alignment). -/
def tensorSegs (P : Params) (cs : CS) (xs : List Lin) : List Seg :=
  let p := (xs.length + 1) / 2
  let l := eqRows cs (xs.take p) [P.one] 0
  let h := eqRows cs (xs.drop p) [P.one] l.2.2
  let r0 := cs.nrows + l.2.1.length + h.2.1.length
  let u0 := alignUp (cs.next + h.2.2) p - cs.next
  let s0 := alignUp r0 p
  (List.range h.1.length).map fun j =>
    ⟨s0 + 2 ^ p * j, s0 + 2 ^ p * (j + 1), cs.next + u0 + 2 ^ p * j, p⟩

/-- The skeleton's blocks, by replaying the compile (`compileFromX`'s recursion): a block opens at
an aligned op and closes after the next `assertEq` or at the next aligned op, cut into aligned
pieces (`cutBlock`); tensor `eqTable`s add their product blocks.
Returned last first. -/
def segsGo (X : Ext) (P : Params) : CS → List Op → Option (ℕ × ℕ × ℕ) → List Seg → List Seg
  | _, [], _, acc => acc
  | cs, op :: ops, cur, acc =>
    let a := alignOf op ops
    -- a block still open when the next one opens ends here (B0: a block need not end in `assertEq`)
    let acc := match a, cur with
      | some _, some (r0, c0, b) => cutBlock r0 cs.nrows c0 b acc
      | _, _ => acc
    let cs' := cs.align a
    let cur := match a with
      | some (_, b) => some (cs'.nrows, cs'.next, b)
      | none => cur
    -- (everything read off `cs'` before `add`, so that the slot array is updated in place)
    let acc := match op with
      | .eqTable r =>
        if (cs'.slot r).isSome && decide (8 ≤ (asAF (cs'.slot r)).length) then
          (tensorSegs P cs' (asAF (cs'.slot r))).reverse ++ acc
        else acc
      | _ => acc
    let cs2 := cs'.add op (stepOut X P cs' op)
    match op, cur with
    | .assertEq .., some (r0, c0, b) => segsGo X P cs2 ops none (cutBlock r0 cs2.nrows c0 b acc)
    | _, _ => segsGo X P cs2 ops cur acc

/-- The abstraction's state: the input cells, numbered by first appearance. -/
structure AbsSt where
  idx : Std.HashMap ℕ ℕ
  cells : Array ℕ

def absTerm (c0 W : ℕ) (st : AbsSt) (t : ℕ × F) : (Wire × F) × AbsSt :=
  if c0 ≤ t.1 ∧ t.1 < c0 + W then ((.loc (t.1 - c0), t.2), st)
  else match st.idx[t.1]? with
    | some i => ((.inp i, t.2), st)
    | none => ((.inp st.cells.size, t.2), ⟨st.idx.insert t.1 st.cells.size, st.cells.push t.1⟩)

def absLin (c0 W : ℕ) (st : AbsSt) (l : Lin) : LinT × AbsSt :=
  let r := l.foldl (fun (q : LinT × AbsSt) t => let u := absTerm c0 W q.2 t; (u.1 :: q.1, u.2)) ([], st)
  (r.1.reverse, r.2)

/-- **The abstraction of rows** over the window `[c0, c0 + W)`: template rows and input cells. -/
def absRows (c0 W : ℕ) (rows : List Row) : List RowT × Array ℕ :=
  let r := rows.foldl (fun (q : List RowT × AbsSt) row =>
    let a := absLin c0 W q.2 row.a
    let b := absLin c0 W a.2 row.b
    let c := absLin c0 W b.2 row.c
    (⟨a.1, b.1, c.1⟩ :: q.1, c.2)) ([], ⟨{}, #[]⟩)
  (r.1.reverse, r.2.cells)

/-- A raw instance: template rows, input forms, row base, cell base, row and cell bits. -/
structure RawI where
  T : List RowT
  ins : Array Lin
  X : ℕ
  cb : ℕ
  A : ℕ
  B : ℕ

def RawI.aligned (r : RawI) : Bool :=
  r.X % 2 ^ r.A == 0 && r.cb % 2 ^ r.B == 0 && decide (r.A ≤ 21) && decide (r.B ≤ 23)


/-- A proto-piece: sparse rows, or a raw instance (whose rows it stands for). -/
inductive PP where
  | sp (rows : List (ℕ × Row))
  | raw (r : RawI) (rows : List (ℕ × Row))

/-- A skeleton block's proto-piece (`rows` at index `X`). -/
def blockPP (rows : List Row) (X c0 B : ℕ) : PP :=
  let ab := absRows c0 (2 ^ B) rows
  let r : RawI := ⟨ab.1, ab.2.map Lin.cell, X, c0, Nat.size (rows.length - 1), B⟩
  let idx := rows.zipIdx.map fun p => (X + p.2, p.1)
  if r.aligned then .raw r idx else .sp idx

/-- The skeleton's proto-pieces: the blocks, and sparse runs between them. -/
def skelPPs (sk : Array Row) (off : ℕ) (segs : List Seg) : List PP :=
  let run := fun (a b : ℕ) => ((List.range (b - a)).map fun i => (off + a + i, sk.getD (a + i) ⟨[], [], []⟩))
  let r := segs.foldl (fun (q : List PP × ℕ) s =>
    if s.r0 < q.2 ∨ sk.size < s.r1 ∨ s.r1 ≤ s.r0 then q else
    let gap := if q.2 < s.r0 then [PP.sp (run q.2 s.r0)] else []
    let blk := blockPP ((List.range (s.r1 - s.r0)).map fun i => sk.getD (s.r0 + i) ⟨[], [], []⟩)
      (off + s.r0) s.c0 s.B
    (blk :: gap.reverse ++ q.1, s.r1)) ([], 0)
  (PP.sp (run r.2 sk.size) :: r.1).reverse

/-- A key's cell window bits in a layout (`cW` of its cell field; B2″). -/
def _root_.FR.Circ.TLay.bits (L : TLay) (k : TKey) : ℕ :=
  match L.find? (·.1 == k) with
  | some (_, _, _, f) => cW f
  | none => 0

/-- A key's cell field in a layout (B2″: `w + 64·g` if packed). -/
def _root_.FR.Circ.TLay.cf (L : TLay) (k : TKey) : ℕ :=
  match L.find? (·.1 == k) with
  | some (_, _, _, f) => f
  | none => 0

/-- A template instance's proto-pieces: the instance, or for a template of more than `2^12` rows
(`rowW`, `maskRows`: row `k` writes local `k`) its 64-row chunks, each abstracted over the 64 cells
it writes (S-E6). -/
def tinPP (L : TLay) (one : Lin) (off : ℕ) (t : TKey × ℕ × List Lin) : List PP :=
  let TR := tRows t.1; let rbk := tRbits t.1
  let X := off + L.rb t.1 + t.2.1 * 2 ^ rbk
  let cb := L.cb t.1 t.2.1
  let r : RawI := ⟨TR, t.2.2.toArray, X, cb, rbk, L.bits t.1⟩
  match splitOf t.1 with
  | some (a, b) =>
    -- a split template (S-E11): the head and the tail blocks, each over the instance's cells
    let rows := ((tinIRows L one off t).map (·.2)).toArray
    let seg := fun (u v : ℕ) => (List.range (v - u)).map fun i => rows.getD (u + i) ⟨[], [], []⟩
    let X0 := off + L.rb t.1
    let hd := X0 + splitRow a b t.2.1 0
    let tl := X0 + splitRow a b t.2.1 (2 ^ a)
    let bl := fun (u v X B : ℕ) =>
      let r : RawI := ⟨(TR.drop u).take (v - u), t.2.2.toArray, X, cb, B, L.bits t.1⟩
      let idx := (seg u v).zipIdx.map fun p => (X + p.2, p.1)
      if r.aligned then PP.raw r idx else PP.sp idx
    [bl 0 (2 ^ a) hd a, bl (2 ^ a) rows.size tl b]
  | none =>
  if isWalk t.1 then
    -- the walk's DAG (S-E10): its `2^gBits` blocks (the 80 `G` gadgets, the head, the tail), each
    -- abstracted over the block's cells, so that the `G` blocks are instances of one key
    let rows := ((tinIRows L one off t).map (·.2)).toArray
    let B := 2 ^ gBits
    let nb := rows.size / B
    let seg := fun (a b : ℕ) => (List.range (b - a)).map fun i => rows.getD (a + i) ⟨[], [], []⟩
    let idx := fun (a b : ℕ) => (seg a b).zipIdx.map fun p => (X + a + p.2, p.1)
    ((List.range nb).map fun c => blockPP (seg (B * c) (B * c + B)) (X + B * c) (cb + B * c) gBits) ++
      [PP.sp (idx (B * nb) rows.size)]
  else if 12 < rbk then
    let rows := ((tinIRows L one off t).map (·.2)).toArray
    let nb := rows.size / 64
    let seg := fun (a b : ℕ) => (List.range (b - a)).map fun i => rows.getD (a + i) ⟨[], [], []⟩
    let idx := fun (a b : ℕ) => (seg a b).zipIdx.map fun p => (X + a + p.2, p.1)
    ((List.range nb).map fun c => blockPP (seg (64 * c) (64 * c + 64)) (X + 64 * c) (cb + 64 * c) 6) ++
      [PP.sp (idx (64 * nb) rows.size)]
  else if r.aligned then [.raw r (tinIRows L one off t)] else [.sp (tinIRows L one off t)]

/-- A slot's proto-pieces. -/
def slotPPs (X : Ext) (P : Params) (base : ℕ) (ops : List Op) (L : TLay) (one : Lin) (off : ℕ)
    (cs : CS) : Array PP :=
  let segs := (segsGo X P (CS.init base) ops none []).reverse
  (skelPPs cs.rowList.toArray off segs ++ cs.tins.flatMap (tinPP L one off)).toArray

/-- The proto-pieces of an arbitrary row list (`evalL`'s L rows): aligned blocks of `2^a` rows, each
with the aligned cell window of bits `a + 2` holding its least cell (a block whose cells run past
the window reads the rest as own inputs). -/
def listPPs (a : ℕ) (rows : List Row) : Array PP :=
  let sk := rows.toArray
  let nb := sk.size / 2 ^ a
  let segs := (List.range nb).map fun b =>
    let r0 := b * 2 ^ a
    let c := ((List.range (2 ^ a)).map fun i =>
      ((sk.getD (r0 + i) ⟨[], [], []⟩).a.map (·.1)).foldl min (2 ^ 23)).foldl min (2 ^ 23)
    (⟨r0, r0 + 2 ^ a, c / 2 ^ (a + 2) * 2 ^ (a + 2), a + 2⟩ : Seg)
  (skelPPs sk 0 segs).toArray

/-! ## Grouping -/

/-- How a key's input is read: a local, the `i`-th shared input, the `i`-th own input. -/
inductive IK where
  | loc (c : ℕ)
  | sh (i : ℕ)
  | own (i : ℕ)

def rwWire (f : ℕ → Wire) : Wire → Wire
  | .inp i => f i
  | w => w

def rwLin (f : ℕ → Wire) (l : LinT) : LinT := l.map fun t => (rwWire f t.1, t.2)

def rwRow (f : ℕ → Wire) (r : RowT) : RowT := ⟨rwLin f r.a, rwLin f r.b, rwLin f r.c⟩

/-- The cell offset of a one-cell form `[(cb + c, 1)]` in the window, if it is one. -/
def offIn (cb W : ℕ) (l : Lin) : Option ℕ :=
  match l with
  | [(c, u)] => if u == 1 && cb ≤ c && c < cb + W then some (c - cb) else none
  | _ => none

/-- The distinct values of a list, in order of first appearance, if there are at most `cap`. -/
def distinctUpTo (cap : ℕ) (vs : List Lin) : Option (List Lin) :=
  vs.foldl (fun acc v => acc.bind fun d =>
    if d.contains v then some d else if d.length < cap then some (d ++ [v]) else none) (some [])

/-- **A template group's inputs**: an input is a local if it is one cell at a fixed offset in every
member's window; a **partition** input if it takes at most 16 values in each slot (the members are
split by these values, so that each part shares them); otherwise own. Returns the kinds (`sh j` for
the `j`-th partition input, own inputs numbered after them) and, per partition input, its index and
its distinct values in slots 0 and 1. -/
def inputKinds (mem : List (ℕ × RawI)) (part : Bool := true) :
    Array IK × List (ℕ × List Lin × List Lin) :=
  let n := mem.foldl (fun m p => max m p.2.ins.size) 0
  let r := (List.range n).foldl (fun (q : Array IK × List (ℕ × List Lin × List Lin) × ℕ) i =>
    let col := mem.map fun p => (p.1, p.2.cb, p.2.B, p.2.ins.getD i [])
    let offs := col.map fun c => offIn c.2.1 (2 ^ c.2.2.1) c.2.2.2
    let lc := match offs with
      | some c :: rest => if rest.all (· == some c) then some c else none
      | _ => none
    match lc with
    | some c => (q.1.push (IK.loc c), q.2.1, q.2.2)
    | none =>
      let d := fun (σ : ℕ) => distinctUpTo 16 ((col.filter (·.1 == σ)).map (·.2.2.2))
      -- a partition input splits the group only into parts of at least 4 members (per slot)
      let big := fun (σ : ℕ) (dv : List Lin) => 4 * dv.length ≤ (col.filter (·.1 == σ)).length
      match (if part then d 0 else none), d 1 with
      | some d0, some d1 =>
        if (d0.length ≤ 1 && d1.length ≤ 1) || (big 0 d0 && big 1 d1) then
          (q.1.push (IK.sh q.2.1.length), q.2.1 ++ [(i, d0, d1)], q.2.2)
        else (q.1.push (IK.own q.2.2), q.2.1, q.2.2 + 1)
      | _, _ => (q.1.push (IK.own q.2.2), q.2.1, q.2.2 + 1)) ((#[] : Array IK), [], 0)
  (r.1.map fun k => match k with
    | .own i => IK.own (r.2.1.length + i)
    | k => k, r.2.1)

/-- A member's part label: the indices of its partition inputs' values among the slot's. -/
def partLabel (parts : List (ℕ × List Lin × List Lin)) (σ : ℕ) (r : RawI) : List ℕ :=
  parts.map fun p => (if σ = 0 then p.2.1 else p.2.2).idxOf (r.ins.getD p.1 [])

/-- A part's shared forms in slot `σ`. -/
def partShared (parts : List (ℕ × List Lin × List Lin)) (σ : ℕ) (lab : List ℕ) : List Lin :=
  (parts.zip lab).map fun q => (if σ = 0 then q.1.2.1 else q.1.2.2).getD q.2 []

/-- The key's template rows after the rewrite. -/
def kindWire (ks : Array IK) (i : ℕ) : Wire :=
  match ks[i]? with
  | some (.loc c) => .loc c
  | some (.sh j) => .inp j
  | some (.own j) => .inp j
  | none => .inp i

/-- An instance's own forms, in the order of their numbers. -/
def ownOf (ks : Array IK) (r : RawI) : List Lin :=
  (((List.range ks.size).filterMap fun i => match ks[i]? with
    | some (IK.own j) => some (j, r.ins.getD i [])
    | _ => none).mergeSort (fun a b => a.1 ≤ b.1)).map (·.2)

/-- **The own inputs renumbered by the cells of a member's forms** (S-E11), so that inputs reading
consecutive cells get consecutive numbers: the evaluator's runs (`FRVIRTplRun`). One-cell forms
first, by cell; the others after, in order. -/
def sortOwn (r : RawI) (ks : Array IK) : Array IK :=
  let own := (List.range ks.size).filterMap fun i => match ks[i]? with
    | some (IK.own j) => some (i, j)
    | _ => none
  let base := own.foldl (fun m p => min m p.2) (2 ^ 62)
  let key := fun (i : ℕ) => match r.ins.getD i [] with
    | [(c, _)] => c
    | _ => 2 ^ 40 + i
  let srt := own.mergeSort (fun a b => key a.1 ≤ key b.1)
  let rk : Std.HashMap ℕ ℕ := srt.zipIdx.foldl (fun m q => m.insert q.1.1 q.2) {}
  (List.range ks.size).toArray.map fun i => match ks[i]? with
    | some (IK.own _) => IK.own (base + rk.getD i 0)
    | some k => k
    | none => IK.own 0

/-- **The plan's data** for two slots' proto-pieces: the keys, each slot's shared forms and pieces.
Members are grouped by template, then each group is split by its partition inputs' values. -/
def groupPPs (pp0 pp1 : Array PP) : Array Key × Array (List Lin) × Array (List Lin) × List Piece ×
    List Piece :=
  let addAll := fun (σ : ℕ) (pps : Array PP)
      (st : Std.HashMap (List RowT × ℕ × ℕ) ℕ × Array (List (ℕ × RawI))) =>
    pps.foldl (fun st p => match p with
      | .raw r _ =>
        match st.1[(r.T, r.A, r.B)]? with
        | some k => (st.1, st.2.modify k ((σ, r) :: ·))
        | none => (st.1.insert (r.T, r.A, r.B) st.2.size, st.2.push [(σ, r)])
      | .sp _ => st) st
  let st := addAll 1 pp1 (addAll 0 pp0 ({}, #[]))
  let mems := st.2.map List.reverse
  -- partition inputs whose joint labels cut the group into parts of fewer than 4 members are
  -- read as own inputs instead (the walk's message words: 16 values each, 80 joint labels; S-E10)
  let ana := mems.map fun m =>
    let a := inputKinds m
    let labs := m.foldl (fun (acc : List (ℕ × List ℕ)) p =>
      let l := (p.1, partLabel a.2 p.1 p.2); if acc.contains l then acc else l :: acc) []
    let a := if 4 * labs.length ≤ m.length then a else inputKinds m false
    match m with
    | (_, r) :: _ => (sortOwn r a.1, a.2)
    | [] => a
  -- the parts: key ids by (group, label)
  let st2 := (List.range mems.size).foldl (fun (q : Std.HashMap (ℕ × List ℕ) ℕ × Array (ℕ × List ℕ)) g =>
    (mems.getD g []).foldl (fun q m =>
      let lab := partLabel (ana.getD g (#[], [])).2 m.1 m.2
      match q.1[(g, lab)]? with
      | some _ => q
      | none => (q.1.insert (g, lab) q.2.size, q.2.push (g, lab))) q) ({}, #[])
  let keys := st2.2.map fun gl => match mems.getD gl.1 [] with
    | (_, r) :: _ => (⟨r.T.map (rwRow (kindWire (ana.getD gl.1 (#[], [])).1)), r.A, r.B⟩ : Key)
    | [] => dkey
  let sh := fun σ => st2.2.map fun gl => partShared (ana.getD gl.1 (#[], [])).2 σ gl.2
  let pieces := fun (σ : ℕ) (pps : Array PP) => pps.toList.map fun p => match p with
    | .sp rs => Piece.sp rs
    | .raw r rs =>
      match st.1[(r.T, r.A, r.B)]? with
      | some g =>
        let a := ana.getD g (#[], [])
        match st2.1[(g, partLabel a.2 σ r)]? with
        | some k => .ins k (r.X / 2 ^ r.A) (r.cb / 2 ^ r.B) (ownOf a.1 r)
        | none => .sp rs
      | none => .sp rs
  (keys, sh 0, sh 1, pieces 0 pp0, pieces 1 pp1)

end TEval
end FR

end G6_FRVIRTplPlan

section G6_FRVIRTplGrp

-- New for `flock-recursive` (BLUEPRINT §10 changes 17, revision 3.12 item 3; stages S-E4/S-E5, track
-- L-circ). Split out of `FRVIRTplFast` in S-E11 (unchanged): grouped forms, the raw template's closed
-- form, dense input coefficients, the high `eq` factors, a key's preparation.

/-!
# The flat evaluation of the node's M matrices (`evalM`): grouped forms, closed forms, key preparation

BLUEPRINT §10 changes 17 (e), revision 3.12 item 3. `FRVIRTplEval.slotVal` evaluates a slot's
rows through lists of boxed terms, one `eq(σ, cell)` product per entry and one lookup in the
layout per template instance (S-E3: 1.13 s per `evalM`). Here the same value is computed from data
prepared **once per node** (`Plan.fs`, at `planOf`):

* every linear form is **grouped by the high part of its cells** (`grp`: consecutive terms with the
  same `cell / 2^12`), so a term costs a table lookup (and a product only when its coefficient is
  not `1`), and a group one product with `eq(σ_hi, ·)`;
* the skeleton's rows are **grouped by the high part of their index** (`grows`), so a row costs
  one product with `eq(τ_lo, ·)` per non-empty form;
* each template instance's alignment test, bases and grouped input forms are precomputed
  (`GInst`); its two high `eq` factors are computed once per evaluation and shared by the three
  matrices; each key's input terms are **compacted per input** (`compactIT`: one coefficient per
  input instead of one per occurrence);
* the `eq` tables of `τ` and `σ` and the keys' local parts are shared by the two slots.

**`evalMT_eq`** (the statement of S-E3, unchanged): `evalMT pl τ σ = evalMS pl τ σ`, the MLEs of
the node's indexed M rows. The proof goes through `slotVal_eq`: `fslotVal_eq` shows that the flat
value of a slot is `slotVal`'s.
-/

namespace FR
namespace TEval
open Circ Tpl

/-! ## Products without a unit coefficient -/

/-- `c · x`, with no product when `c = 1`. -/
@[inline] def cmulF (c x : F) : F := if c == 1 then x else c * x

theorem cmulF_eq (c x : F) : cmulF c x = c * x := by
  unfold cmulF; split_ifs with h
  · rw [beq_iff_eq.1 h, one_mul]
  · rfl

/-! ## Forms grouped by high cell index -/

/-- A linear form in groups `(hi, [(lo, coefficient)])` of consecutive terms with the same high
index. -/
abbrev GForm := List (ℕ × List (ℕ × F))

/-- Put one term in front of a grouped form. -/
def grpStep (p : ℕ) (t : ℕ × F) : GForm → GForm
  | g :: gs => if g.1 = t.1 / p then (g.1, (t.1 % p, t.2) :: g.2) :: gs
    else (t.1 / p, [(t.1 % p, t.2)]) :: g :: gs
  | [] => [(t.1 / p, [(t.1 % p, t.2)])]

/-- **The grouped form** (`p` = the size of the low table). -/
def grp (p : ℕ) (l : Lin) : GForm := l.foldr (grpStep p) []

/-- A group's inner sum `Σ c · lo[j]`. -/
@[inline] def gInner (lo : Array F) (es : List (ℕ × F)) : F := sumL (fun e => cmulF e.2 (lo.getD e.1 0)) es

/-- **The value of a grouped form**: `Σ_groups hi[h] · Σ c · lo[j]`. -/
def glVal (lo hi : Array F) (g : GForm) : F := sumL (fun h => hi.getD h.1 0 * gInner lo h.2) g

theorem glVal_cons (lo hi : Array F) (h : ℕ × List (ℕ × F)) (g : GForm) :
    glVal lo hi (h :: g) = hi.getD h.1 0 * gInner lo h.2 + glVal lo hi g := by
  simp only [glVal, sumL_eq, List.map_cons, List.sum_cons]

theorem gInner_cons (lo : Array F) (e : ℕ × F) (es : List (ℕ × F)) :
    gInner lo (e :: es) = e.2 * lo.getD e.1 0 + gInner lo es := by
  simp only [gInner, sumL_eq, List.map_cons, List.sum_cons, cmulF_eq]

theorem glVal_grpStep (lo hi : Array F) (p : ℕ) (t : ℕ × F) (G : GForm) :
    glVal lo hi (grpStep p t G) =
      t.2 * (lo.getD (t.1 % p) 0 * hi.getD (t.1 / p) 0) + glVal lo hi G := by
  cases G with
  | nil =>
    simp only [grpStep, glVal_cons, gInner_cons]
    simp [glVal, gInner, sumL_eq]; ring
  | cons g gs =>
    simp only [grpStep]
    split_ifs with h
    · simp only [glVal_cons, gInner_cons, h]; ring
    · simp only [glVal_cons, gInner_cons]
      simp [gInner, sumL_eq]; ring

/-- **The grouped form has the form's value** (with `eq(σ, ·)` split at `p`). -/
theorem glVal_grp (lo hi : Array F) (p : ℕ) (l : Lin) :
    glVal lo hi (grp p l) = linEI (RingHom.id F) (splitAt lo hi p) l := by
  unfold grp
  induction l with
  | nil => simp [glVal, linEI, sumL_eq]
  | cons t l ih =>
    rw [List.foldr_cons, glVal_grpStep, ih]
    simp only [linEI, sumL_eq, List.map_cons, List.sum_cons, cmul_eq, splitAt, RingHom.id_apply]

theorem glVal_nil (lo hi : Array F) : glVal lo hi [] = 0 := rfl

/-! ## Rows grouped by high row index -/

/-- A grouped row: the low part of its index and its three grouped forms. -/
structure GRow where
  lo : ℕ
  a : GForm
  b : GForm
  c : GForm

/-- Matrix `s`'s form of a grouped row. -/
def GRow.m : Mat → GRow → GForm
  | .a, r => r.a | .b, r => r.b | .c, r => r.c

/-- Rows in groups `(hi, rows)` of consecutive rows with the same high index. -/
abbrev GRows := List (ℕ × List GRow)

/-- A row grouped at low row table size `pr` and low cell table size `pc`. -/
def growOf (pr pc : ℕ) (r : ℕ × Row) : GRow := ⟨r.1 % pr, grp pc r.2.a, grp pc r.2.b, grp pc r.2.c⟩

/-- Put one row in front of grouped rows. -/
def growsStep (pr pc : ℕ) (r : ℕ × Row) : GRows → GRows
  | g :: gs => if g.1 = r.1 / pr then (g.1, growOf pr pc r :: g.2) :: gs
    else (r.1 / pr, [growOf pr pc r]) :: g :: gs
  | [] => [(r.1 / pr, [growOf pr pc r])]

/-- **The grouped rows.** -/
def grows (pr pc : ℕ) (rows : List (ℕ × Row)) : GRows := rows.foldr (growsStep pr pc) []

/-- `w · v(g)`, no product for an empty form. -/
@[inline] def rowMul (lo hi : Array F) (w : F) (g : GForm) : F :=
  match g with
  | [] => 0
  | _ => w * glVal lo hi g

theorem rowMul_eq (lo hi : Array F) (w : F) (g : GForm) : rowMul lo hi w g = w * glVal lo hi g := by
  cases g with
  | nil => simp [rowMul, glVal_nil]
  | cons _ _ => rfl

/-- A row group's inner sum. -/
@[inline] def rInner (s : Mat) (tlo slo shi : Array F) (rs : List GRow) : F :=
  sumL (fun r => rowMul slo shi (tlo.getD r.lo 0) (r.m s)) rs

/-- **The value of grouped rows** for matrix `s`. -/
def growsVal (s : Mat) (tlo thi slo shi : Array F) (G : GRows) : F :=
  sumL (fun h => thi.getD h.1 0 * rInner s tlo slo shi h.2) G

theorem growsVal_cons (s : Mat) (tlo thi slo shi : Array F) (h : ℕ × List GRow) (G : GRows) :
    growsVal s tlo thi slo shi (h :: G) =
      thi.getD h.1 0 * rInner s tlo slo shi h.2 + growsVal s tlo thi slo shi G := by
  simp only [growsVal, sumL_eq, List.map_cons, List.sum_cons]

theorem rInner_cons (s : Mat) (tlo slo shi : Array F) (r : GRow) (rs : List GRow) :
    rInner s tlo slo shi (r :: rs) =
      tlo.getD r.lo 0 * glVal slo shi (r.m s) + rInner s tlo slo shi rs := by
  simp only [rInner, sumL_eq, List.map_cons, List.sum_cons, rowMul_eq]

theorem growOf_m (s : Mat) (pr pc : ℕ) (r : ℕ × Row) :
    (growOf pr pc r).m s = grp pc (s.r r.2) := by cases s <;> rfl

theorem growsVal_step (s : Mat) (tlo thi slo shi : Array F) (pr pc : ℕ) (r : ℕ × Row) (G : GRows) :
    growsVal s tlo thi slo shi (growsStep pr pc r G) =
      (tlo.getD (r.1 % pr) 0 * thi.getD (r.1 / pr) 0) *
        linEI (RingHom.id F) (splitAt slo shi pc) (s.r r.2) + growsVal s tlo thi slo shi G := by
  have hv : glVal slo shi ((growOf pr pc r).m s) = linEI (RingHom.id F) (splitAt slo shi pc) (s.r r.2) := by
    rw [growOf_m, glVal_grp]
  cases G with
  | nil =>
    simp only [growsStep, growsVal_cons, rInner_cons, hv]
    simp only [growOf, rInner, sumL_eq, List.map_nil, List.sum_nil, growsVal]; ring
  | cons g gs =>
    simp only [growsStep]
    split_ifs with h
    · simp only [growsVal_cons, rInner_cons, hv, h]
      simp only [growOf]; ring
    · simp only [growsVal_cons, rInner_cons, hv]
      simp only [growOf, rInner, sumL_eq, List.map_nil, List.sum_nil]; ring

/-- **The grouped rows have the rows' sparse value** (`eq(τ, ·)` split at `pr`, `eq(σ, ·)` at
`pc`). -/
theorem growsVal_grows (s : Mat) (tlo thi slo shi : Array F) (pr pc : ℕ) (rows : List (ℕ × Row)) :
    growsVal s tlo thi slo shi (grows pr pc rows) =
      rowsValI (RingHom.id F) s (splitAt tlo thi pr) (splitAt slo shi pc) rows := by
  unfold grows
  induction rows with
  | nil => simp [growsVal, rowsValI, sumL_eq]
  | cons r rows ih =>
    rw [List.foldr_cons, growsVal_step, ih]
    simp only [rowsValI, sumL_eq, List.map_cons, List.sum_cons, splitAt]

/-! ## Input terms compacted per input -/

/-- **One coefficient per input**: the terms `(i, u)` summed per `i` (zero sums dropped). -/
def compactIT (it : List (ℕ × F)) : List (ℕ × F) :=
  let N := it.foldl (fun m q => max m (q.1 + 1)) 0
  let U := it.foldl (fun U q => U.modify q.1 (· + q.2)) (Array.replicate N (0 : F))
  (List.range N).filterMap fun i => let u := U.getD i 0; if u == 0 then none else some (i, u)

theorem foldl_max_ge (it : List (ℕ × F)) (a : ℕ) : a ≤ it.foldl (fun m q => max m (q.1 + 1)) a := by
  induction it generalizing a with
  | nil => exact le_rfl
  | cons q it ih => exact le_trans (le_max_left _ _) (ih _)

theorem foldl_max_lt (it : List (ℕ × F)) (a : ℕ) : ∀ q ∈ it, q.1 < it.foldl (fun m q => max m (q.1 + 1)) a := by
  induction it generalizing a with
  | nil => simp
  | cons q it ih =>
    intro q' hq'
    rcases List.mem_cons.1 hq' with rfl | h
    · exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)) (foldl_max_ge _ _)
    · exact ih _ q' h

theorem modify_getD (U : Array F) (j : ℕ) (c : F) (i : ℕ) :
    (U.modify j (· + c)).getD i 0 = U.getD i 0 + (if i = j ∧ j < U.size then c else 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hij : j = i
  · subst hij
    by_cases hs : j < U.size
    · simp [Array.getElem?_eq_getElem hs, hs]
    · simp [Array.getElem?_eq_none (by omega : U.size ≤ j), hs]
  · simp [hij, Ne.symm hij]

theorem sum_range_ite (N j : ℕ) (a : F) :
    ((List.range N).map fun i => if i = j then a else 0).sum = if j < N then a else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases h : j < N
    · simp [h, show j < N + 1 by omega, show N ≠ j by omega]
    · by_cases h' : j = N
      · subst h'; simp
      · simp [h, h', show ¬ j < N + 1 by omega, Ne.symm h']

theorem sum_range_modify (N : ℕ) (U : Array F) (hU : U.size = N) (j : ℕ) (hj : j < N) (c : F)
    (f : ℕ → F) :
    ((List.range N).map fun i => (U.modify j (· + c)).getD i 0 * f i).sum =
      ((List.range N).map fun i => U.getD i 0 * f i).sum + c * f j := by
  have : ∀ i, (U.modify j (· + c)).getD i 0 * f i =
      U.getD i 0 * f i + (if i = j then c * f j else 0) := fun i => by
    rw [modify_getD]; by_cases h : i = j
    · subst h; simp [hU, hj]; ring
    · simp [h]
  simp only [this, List.sum_map_add, sum_range_ite, hj, if_true]

theorem foldl_modify (N : ℕ) (f : ℕ → F) :
    ∀ (it : List (ℕ × F)) (U : Array F), U.size = N → (∀ q ∈ it, q.1 < N) →
      ((List.range N).map fun i => (it.foldl (fun U q => U.modify q.1 (· + q.2)) U).getD i 0 * f i).sum =
        ((List.range N).map fun i => U.getD i 0 * f i).sum + (it.map fun q => q.2 * f q.1).sum
  | [], U, _, _ => by simp
  | q :: it, U, hU, hq => by
    rw [List.foldl_cons, foldl_modify N f it _ (by rw [Array.size_modify, hU])
      (fun q' h => hq q' (List.mem_cons_of_mem _ h)),
      sum_range_modify N U hU q.1 (hq q (List.mem_cons_self ..)) q.2 f, List.map_cons, List.sum_cons]
    ring

theorem sum_filterMap_nz (L : List ℕ) (u : ℕ → F) (f : ℕ → F) :
    ((L.filterMap fun i => if u i == 0 then none else some (i, u i)).map fun q => q.2 * f q.1).sum =
      (L.map fun i => u i * f i).sum := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [beq_iff_eq] at ih ⊢
    by_cases h : u i = 0
    · simp [List.filterMap_cons, h, ih]
    · simp [List.filterMap_cons, h, ih]

/-- **Compaction keeps the input sum.** -/
theorem compactIT_sum (it : List (ℕ × F)) (f : ℕ → F) :
    ((compactIT it).map fun q => q.2 * f q.1).sum = (it.map fun q => q.2 * f q.1).sum := by
  unfold compactIT
  simp only []
  rw [sum_filterMap_nz, foldl_modify _ f it _ (Array.size_replicate ..) (foldl_max_lt it 0)]
  have h0 : ∀ N i, (Array.replicate N (0 : F)).getD i 0 = 0 := fun N i => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> rfl
  simp only [h0, zero_mul]
  simp

/-! ## A raw template instance in closed form (`tplR_mle`) -/

section Raw
variable {R : Type*} [CommRing R] (ι : F →+* R)

/-- A raw template's terms with the row factor: `(wire, eq(τ_lo, j) · ι c)`. -/
def ttR (s : Mat) (T : List RowT) (eτ : ℕ → R) : List (Wire × R) :=
  T.zipIdx.flatMap fun p => (s.t p.1).map fun t => (t.1, eτ p.2 * ι t.2)

/-- **`tplR_mle`** (`tpl_mle` for raw template rows): an instance at row base `2^A · Xh` and cell
base `2^B · Ch` is `Hτ · (Hσ · LOC + ONE · E(one) + Σ_IT u · E(ins_i))`, when the rows fit `2^A`
and the locals `2^B`. -/
theorem tplR_mle (s : Mat) {n m A B : ℕ} (τ σ : ℕ → R) (T : List RowT) (one : Lin)
    (ins : List Lin) (Xh Ch : ℕ) (hA : A ≤ n) (hB : B ≤ m) (hT : T.length ≤ 2 ^ A)
    (hL : ∀ r ∈ T, ∀ k c, (Wire.loc k, c) ∈ s.t r → k < 2 ^ B) (eτ eσ : ℕ → R)
    (heτ : ∀ j < T.length, eτ j = eqN A τ j) (heσ : ∀ k < 2 ^ B, eσ k = eqN B σ k) :
    rowsVal ι s n m τ σ (instIR T one ins (2 ^ A * Xh) (2 ^ B * Ch)) =
      instClosed ι m σ one ins (gN (n - A) (fun l => τ (A + l)) Xh)
        (gN (m - B) (fun l => σ (B + l)) Ch) (locSum eσ (ttR ι s T eτ))
        (oneSum (ttR ι s T eτ)) (inpList (ttR ι s T eτ)) := by
  set Hτ := gN (n - A) (fun l => τ (A + l)) Xh
  set Hσ := gN (m - B) (fun l => σ (B + l)) Ch
  set cb := 2 ^ B * Ch
  have hloc : ∀ p ∈ ttR ι s T eτ, ∀ k, p.1 = .loc k → gN m σ (cb + k) = eσ k * Hσ := by
    intro p hp k hk
    simp only [ttR, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨q, hq, ⟨w, c⟩, hwc, rfl⟩ := hp
    simp only at hk; subst hk
    have hk' := hL _ (zipIdx_mem hq).1 _ _ hwc
    rw [gN_split hB _ _ hk', heσ k hk']
  have hrow : ∀ p ∈ T.zipIdx,
      gN n τ (2 ^ A * Xh + p.2) * linE ι m σ (s.r (instRow one ins cb p.1)) =
      Hτ * ((s.t p.1).map fun t => eτ p.2 * ι t.2 * wireE ι m σ one ins cb t.1).sum := by
    intro p hp
    have hj := (zipIdx_mem hp).2
    rw [gN_split hA _ _ (lt_of_lt_of_le hj hT), Mat.r_inst, linE_instLin, ← heτ _ hj,
      mul_comm (eτ _), mul_assoc, ← List.sum_map_mul_left]
    simp only [mul_assoc]; rfl
  unfold instClosed
  rw [← partition ι m σ one ins cb eσ Hσ _ hloc, rowsVal, instIR, List.map_map, ttR,
    sum_flatMap_map]
  simp only [Function.comp_def]
  rw [List.map_congr_left hrow, List.sum_map_mul_left]
  simp only [List.map_map, Function.comp_def]

end Raw

/-! ## Input coefficients as a dense array -/

/-- **One coefficient per input index** (`U[i] = Σ_{(i, u) ∈ IT} u`). -/
def denseIT (it : List (ℕ × F)) : Array F :=
  it.foldl (fun U q => U.modify q.1 (· + q.2))
    (Array.replicate (it.foldl (fun m q => max m (q.1 + 1)) 0) 0)

theorem foldl_modify_size (it : List (ℕ × F)) : ∀ U : Array F,
    (it.foldl (fun U q => U.modify q.1 (· + q.2)) U).size = U.size := by
  induction it with
  | nil => intro U; rfl
  | cons q it ih => intro U; rw [List.foldl_cons, ih, Array.size_modify]

theorem sum_range_ext (g : ℕ → F) (L : ℕ) (h : ∀ i, L ≤ i → g i = 0) :
    ∀ k, ((List.range (L + k)).map g).sum = ((List.range L).map g).sum := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append, ih]; simp [h (L + k) (by omega)]

theorem sum_range_ext' (g : ℕ → F) {L M : ℕ} (hLM : L ≤ M) (h : ∀ i, L ≤ i → g i = 0) :
    ((List.range M).map g).sum = ((List.range L).map g).sum := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hLM; exact sum_range_ext g L h k

/-- **The dense coefficients give the input sum**, over any range covering the inputs read. -/
theorem denseIT_sum (it : List (ℕ × F)) (f : ℕ → F) (M : ℕ) (hM : ∀ i, M ≤ i → f i = 0) :
    (it.map fun q => q.2 * f q.1).sum = ((List.range M).map fun i => (denseIT it).getD i 0 * f i).sum := by
  set N := it.foldl (fun m q => max m (q.1 + 1)) 0
  have h0 : ∀ i, (Array.replicate N (0 : F)).getD i 0 = 0 := fun i => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> rfl
  have hf := foldl_modify N f it (Array.replicate N 0) (Array.size_replicate ..) (foldl_max_lt it 0)
  simp only [h0, zero_mul, List.map_const', List.sum_replicate, smul_zero, zero_add] at hf
  rw [← hf]
  change ((List.range N).map fun i => (denseIT it).getD i 0 * f i).sum = _
  have hs : (denseIT it).size = N := by rw [denseIT, foldl_modify_size, Array.size_replicate]
  have hU : ∀ i, N ≤ i → (denseIT it).getD i 0 * f i = 0 := fun i hi => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; simp
  have hV : ∀ i, M ≤ i → (denseIT it).getD i 0 * f i = 0 := fun i hi => by simp [hM i hi]
  rw [← sum_range_ext' _ (le_max_left N M) hU, sum_range_ext' _ (le_max_right N M) hV]

/-- **The input sum split into shared and own inputs.** -/
theorem sum_split (U : Array F) (E : Lin → F) (hE : E [] = 0) (sh own : List Lin) :
    ((List.range (sh.length + own.length)).map fun i => U.getD i 0 * E ((sh ++ own).getD i [])).sum =
      ((List.range sh.length).map fun i => U.getD i 0 * E (sh.getD i [])).sum +
        ((List.range own.length).map fun j => U.getD (sh.length + j) 0 * E (own.getD j [])).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    rw [List.getD_append _ _ _ _ (List.mem_range.1 hi)]
  · refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-! ## The high `eq` factors by tables -/

/-- `eq(t_[A, S), ·)` for every `A ≤ S` that a key needs (`need[A]`; the others are left empty). -/
def hiTabs (t : ℕ → F) (S : ℕ) (need : Array Bool) : Array (Array F) :=
  (Array.range (S + 1)).map fun A => if need.getD A false then loTab (S - A) (fun l => t (A + l)) else #[]

/-- **`eq(t_[A, n), x)`**: a lookup in `hiTabs`' row `A` times one in the table of `t_[S, n)` (one
product), `gNL` when `A > S` or the row was not built. -/
def hfac (tabs : Array (Array F)) (need : Array Bool) (hi : Array F) (S n : ℕ) (t : ℕ → F) (A x : ℕ) :
    F :=
  if A ≤ S ∧ need.getD A false = true then
    (tabs.getD A #[]).getD (x % 2 ^ (S - A)) 0 * hi.getD (x / 2 ^ (S - A)) 0
  else gNL (n - A) (fun l => t (A + l)) x

theorem hfac_eq (t : ℕ → F) {S n : ℕ} (hS : S ≤ n) (need : Array Bool) (A x : ℕ) :
    hfac (hiTabs t S need) need (loTab (n - S) fun l => t (S + l)) S n t A x =
      gN (n - A) (fun l => t (A + l)) x := by
  unfold hfac
  split_ifs with h
  · have ht : (hiTabs t S need).getD A #[] = loTab (S - A) fun l => t (A + l) := by
      have h2 := h.2
      simp only [hiTabs, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
        show A < S + 1 by omega, if_true, Option.map_some, Option.getD_some] at h2 ⊢
      rw [if_pos h2]
    rw [ht, ← splitE_eq (m := n - A) (s := S - A) (by omega)]
    simp only [splitE, splitAt]
    have e1 : n - A - (S - A) = n - S := by omega
    have e2 : (fun l => t (A + (S - A + l))) = fun l => t (S + l) := funext fun l => by
      congr 1; omega
    rw [e1, e2]
  · rw [gNL_eq]

/-! ## Prepared pieces and their values -/

/-- A key's prepared values for matrix `s` (once per evaluation, shared by the two slots). -/
structure KP where
  loc : F
  one : F
  u : Array F

/-- A key's preparation from its row and cell tables. -/
def kprepT (s : Mat) (eτ eσ : ℕ → F) (K : Key) : KP :=
  let tt := ttR (RingHom.id F) s K.rows eτ
  ⟨locSum eσ tt, oneSum tt, denseIT (inpList tt)⟩

/-- **A key's preparation**: its local part, `one` part and dense input coefficients. -/
def kprep (s : Mat) (t u : ℕ → F) (K : Key) : KP :=
  kprepT s (getD0 (loTab K.A t)) (getD0 (loTab K.B u)) K


/-! ## Triples -/

/-- A triple of values. -/
abbrev F3 := F × F × F

@[inline] def add3 (x y : F3) : F3 := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)

/-- `Σ_{x ∈ l} f x` over triples. -/
def sum3 {α : Type*} (f : α → F3) (l : List α) : F3 := l.foldl (fun a x => add3 a (f x)) (0, 0, 0)

theorem sum3_eq {α : Type*} (f : α → F3) (l : List α) :
    sum3 f l = (sumL (fun x => (f x).1) l, sumL (fun x => (f x).2.1) l, sumL (fun x => (f x).2.2) l) := by
  suffices ∀ a : F3, l.foldl (fun a x => add3 a (f x)) a =
      (a.1 + sumL (fun x => (f x).1) l, a.2.1 + sumL (fun x => (f x).2.1) l,
        a.2.2 + sumL (fun x => (f x).2.2) l) by
    simpa [sum3] using this (0, 0, 0)
  induction l with
  | nil => intro a; simp [sumL]
  | cons x l ih => intro a; rw [List.foldl_cons, ih]; simp only [add3, sumL_eq, List.map_cons,
      List.sum_cons]; simp only [add_assoc]

/-! ## Own inputs -/

/-- `Σ_j U[j0 + j] · E(g_j)`. -/
def ownSum (U : Array F) (slo shi : Array F) : ℕ → List GForm → F
  | _, [] => 0
  | j, g :: gs => U.getD j 0 * glVal slo shi g + ownSum U slo shi (j + 1) gs

theorem getD_map' {α β : Type*} (a : Array α) (f : α → β) (k : ℕ) (d : α) :
    (a.map f).getD k (f d) = f (a.getD k d) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]; cases a[k]? <;> rfl

theorem ownSum_eq (U slo shi : Array F) (E : Lin → F) (hE : ∀ l, glVal slo shi (grp 4096 l) = E l) :
    ∀ (own : List Lin) (j0 : ℕ), ownSum U slo shi j0 (own.map (grp 4096)) =
      ((List.range own.length).map fun j => U.getD (j0 + j) 0 * E (own.getD j [])).sum
  | [], _ => rfl
  | a :: own, j0 => by
    rw [List.map_cons, ownSum, ownSum_eq U slo shi E hE own (j0 + 1), List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, hE]
    simp only [Nat.add_zero, List.getD_cons_zero, Function.comp_def, List.getD_cons_succ,
      Nat.add_assoc, Nat.add_comm 1]

theorem linE_glVal (u : ℕ → F) (l : Lin) :
    glVal (loTab 12 u) (loTab 11 fun l => u (12 + l)) (grp 4096 l) = linE (RingHom.id F) 23 u l := by
  rw [glVal_grp, ← linEI_eq]; congr 1; exact splitE_eq (m := 23) (s := 12) (by norm_num) u

end TEval
end FR

end G6_FRVIRTplGrp

section G6_FRVIRTplRun

-- New for `flock-recursive` (BLUEPRINT §10 changes 22 (d), revision 3.15; stage S-E11, track
-- L-circ).

/-!
# The evaluator's run class and the fast key preparation

BLUEPRINT §10 changes 22 (d). Two changes to `evalM`'s cost, neither to its value:

* **Runs** (the per-chunk aligned-shift input class). An instance's own inputs `j … j + len − 1`
  whose forms are the cells `2^B·ch + r + t` (`t < len`, `r + len ≤ 2^B`) contribute
  `Σ_t U[j + t]·eq(σ, 2^B·ch + r + t) = eq(σ_{≥B}, ch) · Σ_t U[j + t]·eq(σ_{<B}, r + t)`
  (`gN_split`). The inner sum depends only on the key's **pattern** `(j, r, len, B)`, so it is
  computed once per key and slot (`runIn`); an instance pays one `hfac` per run. `prepOwn` emits a
  run only where the forms check (`runCh`): correctness does not depend on the pattern table, which
  the plan's search (`patsFor`, untrusted) builds from the instances.
* **The keys' preparation** (`kprepF`): one product per row and matrix (the row factor times the
  row's local sum), none for a unit coefficient (characteristic 2: `−1 = 1`), and the `eq` tables
  of the keys' bits built once per evaluation (`preTabs`). `kprepF_eq`: it is `kprepT`.
-/

namespace FR
namespace TEval
open Circ Tpl

/-! ## The fast key preparation -/

/-- `w · x`, with no product when `x = 0`. -/
@[inline] def mulNZ (w x : F) : F := if x == 0 then 0 else w * x

theorem mulNZ_eq (w x : F) : mulNZ w x = w * x := by
  unfold mulNZ; split_ifs with h
  · rw [beq_iff_eq.1 h, mul_zero]
  · rfl

/-- A row form's local part `Σ c · eσ(k)`. -/
def locRow (eσ : ℕ → F) (l : LinT) : F :=
  sumL (fun t => match t.1 with | .loc k => cmulF t.2 (eσ k) | _ => 0) l

/-- A row form's `one` part. -/
def oneRow (l : LinT) : F := sumL (fun t => match t.1 with | .one => t.2 | _ => 0) l

def inpStep (m : ℕ) (t : Wire × F) : ℕ := match t.1 with | .inp i => max m (i + 1) | _ => m

/-- The number of input indices matrix `s` of the rows reads. -/
def inpN (s : Mat) (T : List RowT) : ℕ := T.zipIdx.foldl (fun m p => (s.t p.1).foldl inpStep m) 0

def uStep (w : F) (U : Array F) (t : Wire × F) : Array F :=
  match t.1 with | .inp i => U.modify i (· + cmulF t.2 w) | _ => U

/-- The dense input coefficients, row by row. -/
def inpU (s : Mat) (T : List RowT) (eτ : ℕ → F) : Array F :=
  T.zipIdx.foldl (fun U p => (s.t p.1).foldl (uStep (eτ p.2)) U) (Array.replicate (inpN s T) 0)

/-- **A key's preparation, fast.** -/
def kprepF (s : Mat) (eτ eσ : ℕ → F) (K : Key) : KP :=
  ⟨sumL (fun p => mulNZ (eτ p.2) (locRow eσ (s.t p.1))) K.rows.zipIdx,
   sumL (fun p => mulNZ (eτ p.2) (oneRow (s.t p.1))) K.rows.zipIdx, inpU s K.rows eτ⟩

/-- The input terms of rows `L`, by matrix `s` and row factor `eτ`. -/
abbrev ttL (s : Mat) (eτ : ℕ → F) (L : List (RowT × ℕ)) : List (Wire × F) :=
  L.flatMap fun p => (s.t p.1).map fun t => (t.1, eτ p.2 * t.2)

theorem inpList_append (a b : List (Wire × F)) : inpList (a ++ b) = inpList a ++ inpList b := by
  simp [inpList, List.filterMap_append]

theorem foldl_inpN_row (w : F) : ∀ (l : LinT) (m : ℕ),
    (inpList (l.map fun t => (t.1, w * t.2))).foldl (fun m q => max m (q.1 + 1)) m = l.foldl inpStep m
  | [], _ => rfl
  | ⟨wi, c⟩ :: l, m => by
    cases wi <;> simp only [List.map_cons, inpList, List.filterMap_cons, List.foldl_cons, inpStep] <;>
      exact foldl_inpN_row w l _

theorem foldl_inpN (s : Mat) (eτ : ℕ → F) : ∀ (L : List (RowT × ℕ)) (m : ℕ),
    (inpList (ttL s eτ L)).foldl (fun m q => max m (q.1 + 1)) m =
      L.foldl (fun m p => (s.t p.1).foldl inpStep m) m
  | [], _ => rfl
  | p :: L, m => by
    rw [ttL, List.flatMap_cons, inpList_append, List.foldl_append, foldl_inpN_row, List.foldl_cons]
    exact foldl_inpN s eτ L _

theorem foldl_inpU_row (w : F) : ∀ (l : LinT) (U : Array F),
    (inpList (l.map fun t => (t.1, w * t.2))).foldl (fun U q => U.modify q.1 (· + q.2)) U =
      l.foldl (uStep w) U
  | [], _ => rfl
  | ⟨wi, c⟩ :: l, U => by
    cases wi <;> simp only [List.map_cons, inpList, List.filterMap_cons, List.foldl_cons, uStep]
    · exact foldl_inpU_row w l _
    · rw [cmulF_eq, mul_comm c w]; exact foldl_inpU_row w l _
    · exact foldl_inpU_row w l _

theorem foldl_inpU (s : Mat) (eτ : ℕ → F) : ∀ (L : List (RowT × ℕ)) (U : Array F),
    (inpList (ttL s eτ L)).foldl (fun U q => U.modify q.1 (· + q.2)) U =
      L.foldl (fun U p => (s.t p.1).foldl (uStep (eτ p.2)) U) U
  | [], _ => rfl
  | p :: L, U => by
    rw [ttL, List.flatMap_cons, inpList_append, List.foldl_append, foldl_inpU_row, List.foldl_cons]
    exact foldl_inpU s eτ L _

theorem ttR_id (s : Mat) (T : List RowT) (eτ : ℕ → F) : ttR (RingHom.id F) s T eτ = ttL s eτ T.zipIdx := by
  simp [ttR, ttL]

theorem locSum_append (eσ : ℕ → F) (a b : List (Wire × F)) :
    locSum eσ (a ++ b) = locSum eσ a + locSum eσ b := by simp [locSum]

theorem oneSum_append (a b : List (Wire × F)) : oneSum (a ++ b) = oneSum a + oneSum b := by
  simp [oneSum]

theorem locRow_eq (eσ : ℕ → F) (w : F) (l : LinT) :
    locSum eσ (l.map fun t => (t.1, w * t.2)) = mulNZ w (locRow eσ l) := by
  rw [mulNZ_eq, locRow, sumL_eq, ← List.sum_map_mul_left, locSum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun ⟨wi, c⟩ _ => ?_)
  cases wi <;> simp [cmulF_eq, mul_assoc]

theorem oneRow_eq (w : F) (l : LinT) :
    oneSum (l.map fun t => (t.1, w * t.2)) = mulNZ w (oneRow l) := by
  rw [mulNZ_eq, oneRow, sumL_eq, ← List.sum_map_mul_left, oneSum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun ⟨wi, c⟩ _ => ?_)
  cases wi <;> simp

theorem locSum_ttL (s : Mat) (eτ eσ : ℕ → F) : ∀ L : List (RowT × ℕ),
    locSum eσ (ttL s eτ L) = (L.map fun p => mulNZ (eτ p.2) (locRow eσ (s.t p.1))).sum
  | [] => rfl
  | p :: L => by rw [ttL, List.flatMap_cons, locSum_append, locRow_eq, ← ttL, locSum_ttL s eτ eσ L]; rfl

theorem oneSum_ttL (s : Mat) (eτ : ℕ → F) : ∀ L : List (RowT × ℕ),
    oneSum (ttL s eτ L) = (L.map fun p => mulNZ (eτ p.2) (oneRow (s.t p.1))).sum
  | [] => rfl
  | p :: L => by rw [ttL, List.flatMap_cons, oneSum_append, oneRow_eq, ← ttL, oneSum_ttL s eτ L]; rfl

/-- **`kprepF` is `kprepT`.** -/
theorem kprepF_eq (s : Mat) (eτ eσ : ℕ → F) (K : Key) : kprepF s eτ eσ K = kprepT s eτ eσ K := by
  simp only [kprepF, kprepT, ttR_id]
  congr 1
  · rw [locSum_ttL, sumL_eq]
  · rw [oneSum_ttL, sumL_eq]
  · rw [denseIT, inpU, inpN, foldl_inpN, foldl_inpU]

/-! ## The three matrices' preparations in one pass (S-T1) -/

/-- One matrix's running preparation `(loc, one, U)`. -/
abbrev KS := F × F × Array F

/-- One term of a row form: its local part, its `one` part, its input coefficient (row factor `w`). -/
@[inline] def tStep (eσ : ℕ → F) (w : F) (x : KS) (t : Wire × F) : KS :=
  match t.1 with
  | .loc k => (x.1 + cmulF t.2 (eσ k), x.2.1, x.2.2)
  | .one => (x.1, x.2.1 + t.2, x.2.2)
  | .inp i => (x.1, x.2.1, x.2.2.modify i (· + cmulF t.2 w))

/-- Row `r` (row factor `w`) added to matrix `s`'s running preparation, its form read once. -/
@[inline] def kp1 (s : Mat) (eσ : ℕ → F) (w : F) (r : RowT) (x : KS) : KS :=
  let y := (s.t r).foldl (tStep eσ w) (0, 0, x.2.2)
  (x.1 + mulNZ w y.1, x.2.1 + mulNZ w y.2.1, y.2.2)

theorem foldl_tStep (eσ : ℕ → F) (w : F) : ∀ (l : LinT) (x : KS),
    l.foldl (tStep eσ w) x =
      (l.foldl (fun a t => a + match t.1 with | .loc k => cmulF t.2 (eσ k) | _ => 0) x.1,
       l.foldl (fun a t => a + match t.1 with | .one => t.2 | _ => 0) x.2.1, l.foldl (uStep w) x.2.2)
  | [], _ => rfl
  | t :: l, x => by
    rw [List.foldl_cons, foldl_tStep eσ w l, List.foldl_cons, List.foldl_cons, List.foldl_cons]
    obtain ⟨wi, c⟩ := t
    cases wi <;> simp [tStep, uStep]

theorem kp1_eq (s : Mat) (eσ : ℕ → F) (w : F) (r : RowT) (x : KS) :
    kp1 s eσ w r x = (x.1 + mulNZ w (locRow eσ (s.t r)), x.2.1 + mulNZ w (oneRow (s.t r)),
      (s.t r).foldl (uStep w) x.2.2) := by
  simp only [kp1, foldl_tStep, locRow, oneRow, sumL]

/-- The rows from index `i`, once, for the three matrices. -/
def kpGo (eτ eσ : ℕ → F) : ℕ → List RowT → KS × KS × KS → KS × KS × KS
  | _, [], st => st
  | i, r :: rs, st =>
    let w := eτ i
    kpGo eτ eσ (i + 1) rs (kp1 .a eσ w r st.1, kp1 .b eσ w r st.2.1, kp1 .c eσ w r st.2.2)

/-- The number of inputs matrix `s` reads (`inpN` without the index). -/
def inpNF (s : Mat) (T : List RowT) : ℕ := T.foldl (fun m r => (s.t r).foldl inpStep m) 0

/-- **A key's three preparations in one pass over its rows** (`kprep3F_eq`). -/
def kprep3F (eτ eσ : ℕ → F) (K : Key) : KP × KP × KP :=
  let st := kpGo eτ eσ 0 K.rows ((0, 0, Array.replicate (inpNF .a K.rows) 0),
    (0, 0, Array.replicate (inpNF .b K.rows) 0), (0, 0, Array.replicate (inpNF .c K.rows) 0))
  (⟨st.1.1, st.1.2.1, st.1.2.2⟩, ⟨st.2.1.1, st.2.1.2.1, st.2.1.2.2⟩,
    ⟨st.2.2.1, st.2.2.2.1, st.2.2.2.2⟩)

/-- One matrix's part of the pass: its three folds over the indexed rows. -/
def kOne (s : Mat) (eτ eσ : ℕ → F) (n : ℕ) (rs : List RowT) (x : KS) : KS :=
  ((rs.zipIdx n).foldl (fun a p => a + mulNZ (eτ p.2) (locRow eσ (s.t p.1))) x.1,
   (rs.zipIdx n).foldl (fun a p => a + mulNZ (eτ p.2) (oneRow (s.t p.1))) x.2.1,
   (rs.zipIdx n).foldl (fun U p => (s.t p.1).foldl (uStep (eτ p.2)) U) x.2.2)

theorem kpGo_eq (eτ eσ : ℕ → F) : ∀ (rs : List RowT) (n : ℕ) (st : KS × KS × KS),
    kpGo eτ eσ n rs st = (kOne .a eτ eσ n rs st.1, kOne .b eτ eσ n rs st.2.1, kOne .c eτ eσ n rs st.2.2)
  | [], _, _ => rfl
  | r :: rs, n, st => by
    rw [kpGo, kpGo_eq eτ eσ rs (n + 1)]
    simp only [kOne, kp1_eq, List.zipIdx_cons, List.foldl_cons]

theorem foldl_zipIdx_fst {α β : Type*} (g : β → α → β) : ∀ (T : List α) (n : ℕ) (m : β),
    (T.zipIdx n).foldl (fun m p => g m p.1) m = T.foldl g m
  | [], _, _ => rfl
  | a :: T, n, m => by rw [List.zipIdx_cons, List.foldl_cons, List.foldl_cons, foldl_zipIdx_fst g T]

theorem inpNF_eq (s : Mat) (T : List RowT) : inpNF s T = inpN s T :=
  (foldl_zipIdx_fst (fun m r => (s.t r).foldl inpStep m) T 0 0).symm

/-- **The one pass is the three preparations.** -/
theorem kprep3F_eq (eτ eσ : ℕ → F) (K : Key) :
    kprep3F eτ eσ K = (kprepF .a eτ eσ K, kprepF .b eτ eσ K, kprepF .c eτ eσ K) := by
  simp only [kprep3F, kpGo_eq, kOne, kprepF, sumL, inpU, inpNF_eq]

/-! ## The keys' `eq` tables, once per evaluation -/

/-- `eq(t_{<A}, ·)` for every `A` with `need[A]` (the others empty). -/
def preTabs (t : ℕ → F) (need : Array Bool) : Array (Array F) :=
  (Array.range need.size).map fun A => if need.getD A false then loTab A t else #[]

/-- The table of `A` bits: from `preTabs` when built, else computed. -/
def tabOr (P : Array (Array F)) (need : Array Bool) (t : ℕ → F) (A : ℕ) : Array F :=
  if need.getD A false then P.getD A #[] else loTab A t

theorem getD_true {need : Array Bool} {A : ℕ} (h : need.getD A false = true) : A < need.size := by
  by_contra h'
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

theorem tabOr_eq (t : ℕ → F) (need : Array Bool) (A : ℕ) : tabOr (preTabs t need) need t A = loTab A t := by
  unfold tabOr; split_ifs with h
  · have h3 : need[A]'(getD_true h) = true := by
      simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (getD_true h)] using h
    simp [preTabs, Array.getD_eq_getD_getElem?, getD_true h, h3]
  · rfl

/-- The bits `< m` that some key has as `A` (resp. `B`), or `B` of a pattern in `pats`. -/
def needAll (keys : Array Key) (f : Key → ℕ) (m : ℕ) (extra : List ℕ := []) : Array Bool :=
  (Array.range m).map fun A => keys.any (f · == A) || extra.contains A

/-! ## Runs -/

/-- **A run pattern**: own inputs `j0 … j0 + len − 1` read the cells `2^B·ch + r + t`. -/
structure Pat where
  j0 : ℕ
  r : ℕ
  len : ℕ
  B : ℕ
  deriving BEq, Hashable

/-- The empty pattern (a lookup's default; never valid). -/
def dpat : Pat := ⟨0, 0, 0, 0⟩

/-- A valid pattern: a nonempty run inside one aligned chunk of at most `2^12` cells. -/
def Pat.ok (p : Pat) : Prop := 1 ≤ p.len ∧ p.B ≤ 12 ∧ p.r + p.len ≤ 2 ^ p.B

/-- A prepared own input: a grouped form, or a run (pattern index, chunk). -/
inductive OwnP where
  | g (f : GForm)
  | run (i ch : ℕ)

/-- The one-cell forms of the cells `c, c + 1, …`. -/
def cellsFrom (c len : ℕ) : List Lin := (List.range len).map fun t => [(c + t, 1)]

/-- **The run check**: the forms `ls` (own input `j` on) start with pattern `p`'s run; its chunk. -/
def runCh (p : Pat) (j : ℕ) (ls : List Lin) : Option ℕ :=
  match ls with
  | [(c, _)] :: _ =>
    if p.j0 == j && decide (1 ≤ p.len) && decide (p.B ≤ 12) && decide (p.r + p.len ≤ 2 ^ p.B) &&
      c % 2 ^ p.B == p.r && eqL (ls.take p.len) (cellsFrom c p.len) then some (c / 2 ^ p.B) else none
  | _ => none

theorem runCh_spec {p : Pat} {j : ℕ} {ls : List Lin} {ch : ℕ} (h : runCh p j ls = some ch) :
    p.j0 = j ∧ p.ok ∧ ls = cellsFrom (2 ^ p.B * ch + p.r) p.len ++ ls.drop p.len := by
  unfold runCh at h
  split at h
  · rename_i c u rest
    split_ifs at h with hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    refine ⟨h1, ⟨h2, h3, h4⟩, ?_⟩
    have hc' : 2 ^ p.B * (c / 2 ^ p.B) + p.r = c := by rw [← h5]; exact Nat.div_add_mod c _
    rw [hc', ← eqL_eq h6, List.take_append_drop]
  · cases h

/-- The first pattern of `ix` whose run starts here. -/
def findRun (ps : Array Pat) (j : ℕ) (ls : List Lin) : List ℕ → Option (ℕ × ℕ)
  | [] => none
  | i :: is => match runCh (ps.getD i dpat) j ls with
    | some ch => some (i, ch)
    | none => findRun ps j ls is

theorem findRun_spec {ps : Array Pat} {j : ℕ} {ls : List Lin} :
    ∀ {ix : List ℕ} {i ch : ℕ}, findRun ps j ls ix = some (i, ch) → runCh (ps.getD i dpat) j ls = some ch
  | [], _, _, h => by cases h
  | i' :: is, i, ch, h => by
    unfold findRun at h
    split at h
    · rename_i ch' hc; cases h; exact hc
    · exact findRun_spec h

theorem findRun_len {ps : Array Pat} {j : ℕ} {ls : List Lin} {ix : List ℕ} {i ch : ℕ}
    (h : findRun ps j ls ix = some (i, ch)) : 1 ≤ (ps.getD i dpat).len :=
  (runCh_spec (findRun_spec h)).2.1.1

/-- **An instance's own forms, prepared** (own input `j` on): a run where a pattern of `ps` (tried
in the order `ix`) checks, else the grouped form. -/
def prepOwn (ps : Array Pat) (ix : List ℕ) (j : ℕ) (ls : List Lin) : List OwnP :=
  match ls with
  | [] => []
  | l :: rest =>
    match h : findRun ps j (l :: rest) ix with
    | some (i, ch) =>
      .run i ch :: prepOwn ps ix (j + (ps.getD i dpat).len) ((l :: rest).drop (ps.getD i dpat).len)
    | none => .g (grp 4096 l) :: prepOwn ps ix (j + 1) rest
termination_by ls.length
decreasing_by
  · have := findRun_len h; simp only [List.length_drop, List.length_cons]; omega
  · simp

/-- **The own inputs' value** with runs: `inr[i]` is pattern `i`'s inner sum, `hf B ch` the high
factor `eq(σ_{≥B}, ch)`. -/
def ownSumP (U slo shi inr : Array F) (hf : ℕ → ℕ → F) (ps : Array Pat) : ℕ → List OwnP → F
  | _, [] => 0
  | j, .g f :: os => U.getD j 0 * glVal slo shi f + ownSumP U slo shi inr hf ps (j + 1) os
  | j, .run i ch :: os => hf (ps.getD i dpat).B ch * inr.getD i 0 +
      ownSumP U slo shi inr hf ps (j + (ps.getD i dpat).len) os

/-- **A pattern's inner sum** `Σ_t U[j + j0 + t] · lt[r + t]` (`j`: the key's shared inputs). -/
def runIn (U lt : Array F) (j : ℕ) (p : Pat) : F :=
  sumL (fun t => U.getD (j + p.j0 + t) 0 * lt.getD (p.r + t) 0) (List.range p.len)

/-- The inner sums of a key's patterns. -/
def inrOf (U : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) : Array F :=
  ps.map fun p => runIn U (lt p.B) j p

theorem inrOf_getD {U : Array F} {lt : ℕ → Array F} {j : ℕ} {ps : Array Pat} {i : ℕ}
    (h : (ps.getD i dpat).ok) :
    (inrOf U lt j ps).getD i 0 = runIn U (lt (ps.getD i dpat).B) j (ps.getD i dpat) := by
  have hi : i < ps.size := by
    by_contra h'
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h
    exact absurd h.1 (by simp [dpat])
  simp [inrOf, Array.getD_eq_getD_getElem?, hi]

theorem ownSum_append (U slo shi : Array F) :
    ∀ (a b : List GForm) (j : ℕ), ownSum U slo shi j (a ++ b) =
      ownSum U slo shi j a + ownSum U slo shi (j + a.length) b
  | [], b, j => by simp [ownSum]
  | x :: a, b, j => by
    rw [List.cons_append, ownSum, ownSum, ownSum_append U slo shi a b (j + 1), List.length_cons]
    rw [show j + 1 + a.length = j + (a.length + 1) by omega, add_assoc]

/-- **A run's value**: `Σ_t U[j + t] · E(cell (2^B·ch + r + t)) = eq(σ_{≥B}, ch) · runIn`. -/
theorem run_val (U slo shi : Array F) (u : ℕ → F)
    (hE : ∀ l, glVal slo shi (grp 4096 l) = linE (RingHom.id F) 23 u l) (p : Pat) (hp : p.ok)
    (j ch : ℕ) :
    ownSum U slo shi (j + p.j0) ((cellsFrom (2 ^ p.B * ch + p.r) p.len).map (grp 4096)) =
      gN (23 - p.B) (fun l => u (p.B + l)) ch * runIn U (loTab p.B u) j p := by
  obtain ⟨_, hB, hr⟩ := hp
  rw [ownSum_eq U slo shi _ hE, runIn, sumL_eq, ← List.sum_map_mul_left, cellsFrom, List.length_map,
    List.length_range]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have ht' := List.mem_range.1 ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht', Option.map_some,
    Option.getD_some, loTab_getD _ _ (by omega)]
  simp only [linE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, map_one, one_mul]
  rw [show 2 ^ p.B * ch + p.r + t = 2 ^ p.B * ch + (p.r + t) by omega,
    gN_split (by omega) _ _ (by omega)]
  ring

/-- **`ownSumP` of the prepared forms is `ownSum` of the forms**, for any pattern table (`j0`: the
key's shared inputs; `inr` the patterns' inner sums, `hf` the high factor). -/
theorem ownSumP_eq (U slo shi inr : Array F) (hf : ℕ → ℕ → F) (ps : Array Pat) (ix : List ℕ)
    (u : ℕ → F) (j0 : ℕ) (hE : ∀ l, glVal slo shi (grp 4096 l) = linE (RingHom.id F) 23 u l)
    (hhf : ∀ B ch, B ≤ 12 → hf B ch = gN (23 - B) (fun l => u (B + l)) ch)
    (hin : ∀ i, (ps.getD i dpat).ok →
      inr.getD i 0 = runIn U (loTab (ps.getD i dpat).B u) j0 (ps.getD i dpat)) :
    ∀ (n : ℕ) (own : List Lin), own.length = n → ∀ j : ℕ,
      ownSumP U slo shi inr hf ps (j0 + j) (prepOwn ps ix j own) =
        ownSum U slo shi (j0 + j) (own.map (grp 4096)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro own hn j
    match own with
    | [] => rw [prepOwn]; rfl
    | l :: rest =>
      rw [prepOwn]
      split
      · rename_i i ch h
        obtain ⟨hj, hok, hls⟩ := runCh_spec (findRun_spec h)
        have hlen := findRun_len h
        set p := ps.getD i dpat
        have hm : (l :: rest).map (grp 4096) = (cellsFrom (2 ^ p.B * ch + p.r) p.len).map (grp 4096) ++
            ((l :: rest).drop p.len).map (grp 4096) := by
          conv_lhs => rw [hls]
          rw [List.map_append]
        rw [ownSumP, hm, ownSum_append, List.length_map, cellsFrom, List.length_map, List.length_range,
          ← cellsFrom, add_assoc, ih _ (by simp only [List.length_drop, List.length_cons] at hn ⊢; omega) _ rfl,
          ← hj, run_val U slo shi u hE p hok j0 ch, hhf _ _ hok.2.1, hin i hok]
      · rw [ownSumP, List.map_cons, ownSum, add_assoc,
          ih _ (by simp only [List.length_cons] at hn; omega) _ rfl]

/-! ## The three matrices -/

/-- The own inputs of the three matrices, with runs. -/
def ownSumP3 (Ua Ub Uc slo shi : Array F) (inr : Array F3) (hf : ℕ → ℕ → F) (ps : Array Pat) :
    ℕ → List OwnP → F3
  | _, [] => (0, 0, 0)
  | j, .g f :: os =>
    let e := glVal slo shi f
    add3 (Ua.getD j 0 * e, Ub.getD j 0 * e, Uc.getD j 0 * e) (ownSumP3 Ua Ub Uc slo shi inr hf ps (j + 1) os)
  | j, .run i ch :: os =>
    let p := ps.getD i dpat
    let h := hf p.B ch
    let v := inr.getD i (0, 0, 0)
    add3 (h * v.1, h * v.2.1, h * v.2.2) (ownSumP3 Ua Ub Uc slo shi inr hf ps (j + p.len) os)

theorem getD_map3 (inr : Array F3) (f : F3 → F) (hf : f (0, 0, 0) = 0) (i : ℕ) :
    (inr.map f).getD i 0 = f (inr.getD i (0, 0, 0)) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases inr[i]? <;> simp [hf]

theorem ownSumP3_eq (Ua Ub Uc slo shi : Array F) (inr : Array F3) (hf : ℕ → ℕ → F) (ps : Array Pat) :
    ∀ (j : ℕ) (os : List OwnP), ownSumP3 Ua Ub Uc slo shi inr hf ps j os =
      (ownSumP Ua slo shi (inr.map (·.1)) hf ps j os, ownSumP Ub slo shi (inr.map (·.2.1)) hf ps j os,
        ownSumP Uc slo shi (inr.map (·.2.2)) hf ps j os)
  | _, [] => rfl
  | j, .g f :: os => by rw [ownSumP3, ownSumP3_eq Ua Ub Uc slo shi inr hf ps (j + 1) os]; rfl
  | j, .run i ch :: os => by
    rw [ownSumP3, ownSumP3_eq Ua Ub Uc slo shi inr hf ps _ os]
    simp only [ownSumP, add3, getD_map3 inr (·.1) rfl, getD_map3 inr (·.2.1) rfl,
      getD_map3 inr (·.2.2) rfl]

/-- The three inner sums of a pattern (one table lookup each). -/
def runIn3 (Ua Ub Uc lt : Array F) (j : ℕ) (p : Pat) : F3 :=
  sum3 (fun t => let e := lt.getD (p.r + t) 0; let q := j + p.j0 + t
    (Ua.getD q 0 * e, Ub.getD q 0 * e, Uc.getD q 0 * e)) (List.range p.len)

def inrOf3 (Ua Ub Uc : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) : Array F3 :=
  ps.map fun p => runIn3 Ua Ub Uc (lt p.B) j p

theorem inrOf3_map1 (Ua Ub Uc : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) :
    (inrOf3 Ua Ub Uc lt j ps).map (·.1) = inrOf Ua lt j ps := by
  simp [inrOf3, inrOf, Function.comp_def, runIn3, sum3_eq, runIn]

theorem inrOf3_map2 (Ua Ub Uc : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) :
    (inrOf3 Ua Ub Uc lt j ps).map (·.2.1) = inrOf Ub lt j ps := by
  simp [inrOf3, inrOf, Function.comp_def, runIn3, sum3_eq, runIn]

theorem inrOf3_map3 (Ua Ub Uc : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) :
    (inrOf3 Ua Ub Uc lt j ps).map (·.2.2) = inrOf Uc lt j ps := by
  simp [inrOf3, inrOf, Function.comp_def, runIn3, sum3_eq, runIn]

theorem range_getD_inr (pats : Array (Array Pat)) (U : ℕ → Array F) (lt : ℕ → Array F) (J : ℕ → ℕ)
    (k : ℕ) : ((Array.range pats.size).map fun k => inrOf (U k) lt (J k) (pats.getD k #[])).getD k #[] =
      inrOf (U k) lt (J k) (pats.getD k #[]) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split_ifs with h
  · rfl
  · rw [Array.getElem?_eq_none (by omega)]; simp [inrOf]

theorem range_getD_inr3 (pats : Array (Array Pat)) (Ua Ub Uc : ℕ → Array F) (lt : ℕ → Array F)
    (J : ℕ → ℕ) (k : ℕ) :
    ((Array.range pats.size).map fun k => inrOf3 (Ua k) (Ub k) (Uc k) lt (J k) (pats.getD k #[])).getD k #[] =
      inrOf3 (Ua k) (Ub k) (Uc k) lt (J k) (pats.getD k #[]) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split_ifs with h
  · rfl
  · rw [Array.getElem?_eq_none (by omega)]; simp [inrOf3]

/-! ## The search for patterns (untrusted: `prepOwn` checks every run) -/

/-- The runs of one instance's own forms at chunk bits `B`: maximal runs of consecutive one-cell
forms (coefficient `1`) inside one aligned chunk, of length at least 2. -/
def runsOf (B : ℕ) (own : List Lin) : List Pat :=
  let W := 2 ^ B
  let fl := fun (cur : Option (ℕ × ℕ × ℕ)) (acc : List Pat) => match cur with
    | some (j0, c0, len) => if 2 ≤ len then (⟨j0, c0 % W, len, B⟩ : Pat) :: acc else acc
    | none => acc
  let r := own.foldl (fun (q : ℕ × Option (ℕ × ℕ × ℕ) × List Pat) l =>
    match l with
    | [(c, u)] =>
      if u == 1 then
        match q.2.1 with
        | some (j0, c0, len) =>
          if c == c0 + len && c % W != 0 then (q.1 + 1, some (j0, c0, len + 1), q.2.2)
          else (q.1 + 1, some (q.1, c, 1), fl q.2.1 q.2.2)
        | none => (q.1 + 1, some (q.1, c, 1), q.2.2)
      else (q.1 + 1, none, fl q.2.1 q.2.2)
    | _ => (q.1 + 1, none, fl q.2.1 q.2.2)) (0, none, [])
  (fl r.2.1 r.2.2).reverse

/-- The distinct values of a list, in order. -/
def dedupP (l : List Pat) : List Pat :=
  (l.foldl (fun (q : Std.HashSet Pat × List Pat) p =>
    if q.1.contains p then q else (q.1.insert p, p :: q.2)) ({}, [])).2.reverse

/-- **A key's patterns**: the chunk bits `B ∈ [2, 9]` of least estimated cost (4 products per run
and per own input outside a run, 6 per pattern entry: three matrices, two slots), or none. -/
def patsFor (insts : List (List Lin)) : Array Pat :=
  let own := insts.foldl (fun n o => n + o.length) 0
  let best := [2, 3, 4, 5, 6, 7, 8, 9].foldl (fun (q : ℕ × List Pat) B =>
    let rs := insts.map (runsOf B)
    let nr := rs.foldl (fun n l => n + l.length) 0
    let cov := rs.foldl (fun n l => n + l.foldl (fun m p => m + p.len) 0) 0
    let ds := dedupP rs.flatten
    let cost := 4 * nr + 4 * (own - cov) + 6 * ds.foldl (fun m p => m + p.len) 0
    if cost < q.1 then (cost, ds) else q) (4 * own, [])
  best.2.toArray

/-- **The plan's pattern tables**, per key, from the instances of both slots. -/
def mkPats (nk : ℕ) (pcs : List Piece) : Array (Array Pat) :=
  let insts := pcs.foldl (fun (a : Array (List (List Lin))) p => match p with
    | .ins k _ _ own => if k < a.size then a.modify k (own :: ·) else a
    | .sp _ => a) (Array.replicate nk [])
  insts.map patsFor

/-! ## Controls -/

/-- (+) A run of three cells at offset 1 of a 4-cell chunk is found. -/
theorem runCh_pos : runCh ⟨0, 1, 3, 2⟩ 0 [[(9, 1)], [(10, 1)], [(11, 1)]] = some 2 := by
  simp [runCh, cellsFrom, eqL, List.range_succ]

/-- (−) A run that crosses its chunk is refused (cells 10, 11, 12 at `B = 2`: `1 + 3 > 4`). -/
theorem runCh_cross : runCh ⟨0, 2, 3, 2⟩ 0 [[(10, 1)], [(11, 1)], [(12, 1)]] = none := by
  simp [runCh]

/-- (−) A gap in the cells is refused. -/
theorem runCh_gap : runCh ⟨0, 1, 3, 2⟩ 0 [[(9, 1)], [(10, 1)], [(12, 1)]] = none := by
  simp [runCh, cellsFrom, eqL, List.range_succ]

end TEval
end FR

end G6_FRVIRTplRun
