-- New for `flock-recursive` (BLUEPRINT §10 changes 17, revision 3.12 item 3; stage S-E5, track
-- L-circ).
import FRVIRTplEval

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
  (`FRVIRCompile.alignOf`); a block runs from its aligned start to its closing `assertEq`. The
  tensor `eqTable` gives one block per `hi` index. A block's rows are abstracted (`absRows`): cells
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
an aligned op and closes after the next `assertEq`; tensor `eqTable`s add their product blocks.
Returned last first. -/
def segsGo (X : Ext) (P : Params) : CS → List Op → Option (ℕ × ℕ × ℕ) → List Seg → List Seg
  | _, [], _, acc => acc
  | cs, op :: ops, cur, acc =>
    let a := alignOf op ops
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
    | .assertEq .., some (r0, c0, b) => segsGo X P cs2 ops none (⟨r0, cs2.nrows, c0, b⟩ :: acc)
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

/-- A key's cell bits in a layout. -/
def _root_.FR.Circ.TLay.bits (L : TLay) (k : TKey) : ℕ :=
  match L.find? (·.1 == k) with
  | some (_, _, _, b) => b
  | none => 0

/-- A template instance's proto-piece. -/
def tinPP (L : TLay) (one : Lin) (off : ℕ) (t : TKey × ℕ × List Lin) : PP :=
  let T := tplOf t.1
  let r : RawI := ⟨T.rows, t.2.2.toArray, off + L.rb t.1 + t.2.1 * 2 ^ T.rbits, L.cb t.1 t.2.1,
    T.rbits, L.bits t.1⟩
  if r.aligned then .raw r (tinIRows L one off t) else .sp (tinIRows L one off t)

/-- A slot's proto-pieces. -/
def slotPPs (X : Ext) (P : Params) (base : ℕ) (ops : List Op) (L : TLay) (one : Lin) (off : ℕ)
    (cs : CS) : Array PP :=
  let segs := (segsGo X P (CS.init base) ops none []).reverse
  (skelPPs cs.rowList.toArray off segs ++ cs.tins.map (tinPP L one off)).toArray

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
def inputKinds (mem : List (ℕ × RawI)) : Array IK × List (ℕ × List Lin × List Lin) :=
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
      match d 0, d 1 with
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

/-- An instance's own forms. -/
def ownOf (ks : Array IK) (r : RawI) : List Lin :=
  (List.range ks.size).filterMap fun i => match ks[i]? with
    | some (IK.own _) => some (r.ins.getD i [])
    | _ => none

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
  let ana := mems.map inputKinds
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
