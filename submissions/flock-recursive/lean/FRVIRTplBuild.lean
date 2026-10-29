-- New for `flock-recursive` (BLUEPRINT §4.4's plan text, B-16: the plan ≤ 2 s per process; stage
-- S-E13, track L-circ).
import FRVIRTplRun

/-!
# The plan's construction without the row comparison

`FRVIRTplFast.mkPlan` (S-E5 … S-E11) checked the plan at run time: it materialised both slots'
indexed rows (`slotIRows`, 2 × 428k) and the pieces' rows and compared them (`eqL`). This module
builds the same kind of plan with **proofs** in place of the comparison:

* **the proto-pieces' rows are the slot's rows** (`slotRP_rows`), by a generic argument over any
  compiled state and layout: the skeleton's blocks and gaps cover its rows in order, a block's
  abstraction (`absRowsV`) instantiates back to its rows, a template instance is cut into its
  whole rows, its split head and tail, or its blocks (`reT`, the walk's `G` blocks and the 64-row
  chunks), each of which instantiates back to the instance's rows;
* **a piece's rows are its proto-piece's** (`toPiece_rows`): the untrusted grouping proposes a key
  and own inputs for each proto-piece, and `toPiece` keeps the instance only if a check costing the
  key's input count (not its rows) passes — the proto-piece's template is the key's (`withPtrEq`:
  the same object for a template's instances), and every input reads what the key's rewritten input
  reads (`insOk`).

The compile runs once per layout pass, with a template memo (`compMS`: each key's template built
once) and the skeleton's blocks recorded in the same pass.
-/

namespace FR
namespace TEval
open Circ Tpl

/-! ## The compile with a template memo, recording the skeleton's blocks -/

/-- A template from a memo (`tplOf`'s for a key it lacks). -/
def tlook (M : List (TKey × Tpl)) (k : TKey) : Tpl :=
  match M.find? (·.1 == k) with
  | some p => p.2
  | none => tplOf k

/-- A memo holds `tplOf`'s templates. -/
def MOk (M : List (TKey × Tpl)) : Prop := ∀ p ∈ M, p.2 = tplOf p.1

theorem tlook_eq {M : List (TKey × Tpl)} (h : MOk M) : tlook M = tplOf := by
  funext k; unfold tlook; split
  · rename_i p hp
    rw [h p (List.mem_of_find?_eq_some hp), eq_of_beq (List.find?_eq_some_iff_append.1 hp).1]
  · rfl

/-- The memo after an op: its instance's template added (once per key). -/
def memoAdd (M : List (TKey × Tpl)) : Option (TKey × List Lin) → List (TKey × Tpl)
  | some (k, _) => if M.any (·.1 == k) then M else (k, tplOf k) :: M
  | none => M

theorem memoAdd_ok {M : List (TKey × Tpl)} (h : MOk M) (t : Option (TKey × List Lin)) :
    MOk (memoAdd M t) := by
  unfold memoAdd; split
  · split_ifs
    · exact h
    · intro p hp; rcases List.mem_cons.1 hp with rfl | hp
      · rfl
      · exact h p hp
  · exact h

/-- **The compile with a template memo, recording the skeleton's blocks** (`segsGo`'s, in the
same pass; `compMSX_eq`: its state is `compileFromX`'s), for a family of template extensions `X`
(3.x's `tplExt`, or a revision's `tplExtF F`; S-E12d). -/
def compMSX (X : TCtx → Ext) (L : TLay) (P : Params) : List (TKey × Tpl) → CS → List Op →
    Option (ℕ × ℕ × ℕ) →
    List Seg → CS × List Seg × List (TKey × Tpl)
  | M, cs, [], _, acc => (cs, acc, M)
  | M, cs, op :: ops, cur, acc =>
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
    -- the op's key first (with empty templates: cheap), so that its template is built once
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P cs' op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P cs' op
    let M := memoAdd M o.tin
    let cs2 := cs'.add op o
    match op, cur with
    | .assertEq .., some (r0, c0, b) => compMSX X L P M cs2 ops none (⟨r0, cs2.nrows, c0, b⟩ :: acc)
    | _, _ => compMSX X L P M cs2 ops cur acc

theorem compMSX_eq (X : TCtx → Ext) (L : TLay) (P : Params) : ∀ (ops : List Op)
    (M : List (TKey × Tpl)) (cs : CS) (cur : Option (ℕ × ℕ × ℕ)) (acc : List Seg), MOk M →
    (compMSX X L P M cs ops cur acc).1 = compileFromX (X L.ctx) P cs ops ∧
      MOk (compMSX X L P M cs ops cur acc).2.2
  | [], _, _, _, _, h => ⟨rfl, h⟩
  | op :: ops, M, cs, cur, acc, h => by
    have hc : ∀ x, (⟨tlook (memoAdd M x), L.cb⟩ : TCtx) = L.ctx := fun x => by
      rw [tlook_eq (memoAdd_ok h x)]; rfl
    rw [compileFromX_cons]
    simp only [compMSX, hc]
    split <;> exact compMSX_eq X L P ops _ _ _ _ (memoAdd_ok (memoAdd_ok h _) _)

/-- **`compMSX` from a fresh state is `compileX`.** -/
theorem compMSX_T (X : TCtx → Ext) (L : TLay) (P : Params) (base : ℕ) (ops : List Op)
    {M : List (TKey × Tpl)} (h : MOk M) :
    (compMSX X L P M (CS.init base) ops none []).1 = compileX (X L.ctx) P base ops ∧
      MOk (compMSX X L P M (CS.init base) ops none []).2.2 :=
  compMSX_eq X L P ops M _ none [] h

/-- **3.x's plan compile** (`compMSX` at `tplExt`). -/
def compMS (L : TLay) (P : Params) : List (TKey × Tpl) → CS → List Op → Option (ℕ × ℕ × ℕ) →
    List Seg → CS × List Seg × List (TKey × Tpl) := compMSX tplExt L P

/-- 3.x's instance is `compMSX`'s at `tplExt` by definition. -/
theorem compMS_rfl : compMS = compMSX tplExt := rfl

theorem compMS_eq (L : TLay) (P : Params) (ops : List Op) (M : List (TKey × Tpl)) (cs : CS)
    (cur : Option (ℕ × ℕ × ℕ)) (acc : List Seg) (h : MOk M) :
    (compMS L P M cs ops cur acc).1 = compileFromX (tplExt L.ctx) P cs ops ∧
      MOk (compMS L P M cs ops cur acc).2.2 :=
  compMSX_eq tplExt L P ops M cs cur acc h

/-! ## The layout from per-key data -/

/-- `mkLay` with each key's row count, cell region bits and locals given by `info`. -/
def mkLayI (info : TKey → ℕ × ℕ × ℕ) (r0 c0 : ℕ) : List (TKey × ℕ) → TLay
  | [] => []
  | (k, n) :: ks =>
    let nr := (info k).1; let rbk := Nat.size (nr - 1); let cr := (info k).2.1
    let rb := alignUp r0 (match splitOf k with
      | some (a, _) => a
      | none => if isWalk k then gBits else if 12 < rbk then 6 else rbk)
    let cb := alignUp c0 (if isWalk k then gBits else cr)
    let re := match splitOf k with
      | some (a, b) => rb + (n + 2 ^ (a - b) - 1) / 2 ^ (a - b) * ((2 ^ (a - b) + 1) * 2 ^ a)
      | none => rb + (n - 1) * 2 ^ rbk + nr
    (k, rb, cb, cr) :: mkLayI info re
      (if isWalk k then cb + (n - 1) * 2 ^ cr + (info k).2.2 else cb + n * 2 ^ cr) ks

theorem mkLayI_eq (info : TKey → ℕ × ℕ × ℕ)
    (h : ∀ k, info k = ((tRows k).length, cregion k, tNlocs k)) :
    ∀ (ks : List (TKey × ℕ)) (r0 c0 : ℕ), mkLayI info r0 c0 ks = mkLay r0 c0 ks
  | [], _, _ => rfl
  | (k, n) :: ks, r0, c0 => by
    unfold mkLayI mkLay; rw [h k]; dsimp only; rw [mkLayI_eq info h ks]; exact rfl

/-! ## Per-key data, computed once per process -/

/-- A block's input source: an input of the template, or one of its locals (outside the block). -/
inductive Src where
  | inp (i : ℕ)
  | loc (k : ℕ)
  deriving DecidableEq, Hashable

/-- The input form of a source, for an instance's inputs `ins` and cell base `cb`. -/
def srcLin (ins : Array Lin) (cb : ℕ) : Src → Lin
  | .inp i => ins.getD i []
  | .loc k => Lin.cell (cb + k)

/-- The state of a re-templating: the sources numbered by first appearance. -/
structure ReSt where
  idx : Std.HashMap Src ℕ
  src : Array Src

/-- A source's input number (a new one unless the memo's entry is confirmed by the array). -/
def reNew (st : ReSt) (s : Src) : ℕ × ReSt :=
  match st.idx[s]? with
  | some j => if st.src[j]? == some s then (j, st) else
      (st.src.size, ⟨st.idx.insert s st.src.size, st.src.push s⟩)
  | none => (st.src.size, ⟨st.idx.insert s st.src.size, st.src.push s⟩)

/-- A wire of a block whose local window is `[w, w + W)`. -/
def reWire (w W : ℕ) (st : ReSt) : Wire → Wire × ReSt
  | .one => (.one, st)
  | .loc k => if w ≤ k ∧ k < w + W then (.loc (k - w), st) else
      let r := reNew st (.loc k); (.inp r.1, r.2)
  | .inp i => let r := reNew st (.inp i); (.inp r.1, r.2)

def reLin (w W : ℕ) : ReSt → LinT → LinT × ReSt
  | st, [] => ([], st)
  | st, t :: l => let u := reWire w W st t.1; let r := reLin w W u.2 l; ((u.1, t.2) :: r.1, r.2)

def reRows (w W : ℕ) : ReSt → List RowT → List RowT × ReSt
  | st, [] => ([], st)
  | st, row :: rows =>
    let a := reLin w W st row.a
    let b := reLin w W a.2 row.b
    let c := reLin w W b.2 row.c
    let r := reRows w W c.2 rows
    (⟨a.1, b.1, c.1⟩ :: r.1, r.2)

/-- **A block of template rows re-templated** over the local window `[w, w + W)`: locals in the
window become the block's locals, every other local and input a block input (`Src`). -/
def reT (w W : ℕ) (rows : List RowT) : List RowT × Array Src :=
  let r := reRows w W ⟨{}, #[]⟩ rows
  (r.1, r.2.src)

/-- A re-templated block: its rows, sources and hash (the hash only groups). -/
structure Blk where
  T : List RowT
  src : Array Src
  h : UInt64

/-- A wire as a block input source. -/
def srcOf : Wire → Option Src
  | .loc k => some (.loc k)
  | .inp i => some (.inp i)
  | .one => none

/-- Match a template block's term against a known block's term (window from local `w`): a local
at `w + k`, `one`, or an input whose source is set at its first appearance and checked after. -/
def matchTermT (w : ℕ) (srcs : Array (Option Src)) (u t : Wire × F) : Option (Array (Option Src)) :=
  if u.2 == t.2 then
    match u.1 with
    | .one => if t.1 == .one then some srcs else none
    | .loc k => if t.1 == .loc (w + k) then some srcs else none
    | .inp j => match srcOf t.1 with
      | some s => match srcs[j]? with
        | some (some s') => if s' == s then some srcs else none
        | some none => some (srcs.setIfInBounds j (some s))
        | none => none
      | none => none
  else none

def matchLinT (w : ℕ) : Array (Option Src) → LinT → LinT → Option (Array (Option Src))
  | srcs, [], [] => some srcs
  | srcs, u :: us, t :: ts => (matchTermT w srcs u t).bind fun c => matchLinT w c us ts
  | _, _, _ => none

def matchRowsT (w : ℕ) : Array (Option Src) → List RowT → List RowT → Option (Array (Option Src))
  | srcs, [], [] => some srcs
  | srcs, r :: rs, row :: rows =>
    (matchLinT w srcs r.a row.a).bind fun c => (matchLinT w c r.b row.b).bind fun c =>
      (matchLinT w c r.c row.c).bind fun c => matchRowsT w c rs rows
  | _, _, _ => none

/-- **A template block matched against a known block** `T` with `n` inputs: its sources. -/
def reMatch (T : List RowT) (n w : ℕ) (rows : List RowT) : Option (Array Src) :=
  (matchRowsT w (Array.replicate n none) T rows).map fun s => s.map fun o => o.getD (.inp 0)

/-- Known template blocks: rows, input count, hash. -/
abbrev BReps := List (List RowT × ℕ × UInt64)

/-- The first known block that a block (window from local `w`) is an instance of. -/
def tryBReps (w : ℕ) (rows : List RowT) : BReps → Option (List RowT × UInt64 × Array Src)
  | [] => none
  | (T, n, h) :: rs =>
    match reMatch T n w rows with
    | some src => some (T, h, src)
    | none => tryBReps w rows rs

/-- **Block `c` of a template's rows** (`S` rows): matched against the known blocks (their object
shared, so that the piece check compares pointers), else re-templated over its own `S` locals and
remembered. -/
def mkBlk (S c : ℕ) (reps : BReps) (rows : List RowT) : Blk × BReps :=
  match tryBReps (S * c) rows reps with
  | some (T, h, src) => (⟨T, src, h⟩, reps)
  | none =>
    let r := reT (S * c) S rows
    let h := hash r.1
    (⟨r.1, r.2, h⟩, (r.1, r.2.size, h) :: reps)

/-- **The blocks of a template's rows** `l`: `n` blocks of `S` rows from block `c`. -/
def mkBlks (S : ℕ) : ℕ → ℕ → BReps → List RowT → List Blk
  | 0, _, _, _ => []
  | n + 1, c, reps, l =>
    let b := mkBlk S c reps (l.take S)
    b.1 :: mkBlks S n (c + 1) b.2 (l.drop S)

/-- The block size of a key cut into blocks (`tinPP`'s): the walk's `2^gBits`, a template of more
than `2^12` rows `64`, otherwise none. -/
def blkSize (k : TKey) (rb : ℕ) : Option ℕ :=
  match splitOf k with
  | some _ => none
  | none => if isWalk k then some (2 ^ gBits) else if 12 < rb then some 64 else none

/-- **A key's data**: its template's rows, row bits, cell region, locals, and (for a split key) its
head and tail, (for a blocked key) its re-templated blocks; the hashes only group. -/
structure KM where
  k : TKey
  rows : List RowT
  rb : ℕ
  cr : ℕ
  nl : ℕ
  h : UInt64
  hd : List RowT
  tl : List RowT
  hh : UInt64
  ht : UInt64
  blks : List Blk

/-- **A key's rows, row bits, cell region and locals**, its template built once
(`keyInfo_eq`). -/
def keyInfo (k : TKey) : List RowT × ℕ × ℕ × ℕ :=
  if isWalk14 k then (tplWalk14Rows, tplWalk14RB, tplWalk14CB, tplWalk14NL) else
    let T := tplOf k
    let rows := T.rows
    let cb := cbitsOf T rows
    let cr := match k with
      | .dotKF n => max cb (Nat.size (3 * n + 1))
      | .tensorW n => max cb (Nat.size (5 * n + logNMax))
      | .tensorWK ns => max cb (Nat.size (twkLocs ns + logNMax))
      | _ => cb
    (rows, Nat.size (rows.length - 1), cr, nlocs T.gates)

theorem keyInfo_eq (k : TKey) : keyInfo k = (tRows k, tRbits k, cregion k, tNlocs k) := by
  unfold keyInfo tRows tRbits tNlocs cregion tCbits
  split_ifs with h
  · cases k <;> simp_all [isWalk14]
  · simp only [cbitsOf_rows]
    cases k <;> simp_all [Tpl.rbits]

def mkKM (k : TKey) : KM :=
  let ki := keyInfo k
  let rows := ki.1
  let rb := ki.2.1
  match splitOf k with
  | some (a, _) =>
    let hd := rows.take (2 ^ a); let tl := rows.drop (2 ^ a)
    ⟨k, rows, rb, ki.2.2.1, ki.2.2.2, 0, hd, tl, hash hd, hash tl, []⟩
  | none =>
    match blkSize k rb with
    | some S => ⟨k, rows, rb, ki.2.2.1, ki.2.2.2, 0, [], [], 0, 0, mkBlks S (rows.length / S) 0 [] rows⟩
    | none => ⟨k, rows, rb, ki.2.2.1, ki.2.2.2, hash rows, [], [], 0, 0, []⟩

/-- A key's data from a memo (computed for a key it lacks). -/
def kmOf (Ms : List KM) (k : TKey) : KM :=
  match Ms.find? (·.k == k) with
  | some e => e
  | none => mkKM k

theorem mkKM_k (k : TKey) : (mkKM k).k = k := by
  unfold mkKM; split
  · rfl
  · dsimp only; split <;> rfl

theorem kmOf_map (ks : List TKey) (k : TKey) : kmOf (ks.map mkKM) k = mkKM k := by
  unfold kmOf; split
  · rename_i e he
    obtain ⟨k', -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some he)
    have := eq_of_beq (List.find?_eq_some_iff_append.1 he).1; rw [mkKM_k] at this; rw [this]
  · rfl

/-! ## Proto-pieces -/

/-- **A proto-piece**: sparse rows, or a raw instance (template rows `T`, input forms, row base,
cell base, row and cell bits; `h` the hash of `T`, which only groups). -/
inductive RP where
  | sp (rows : List (ℕ × Row))
  | raw (T : List RowT) (ins : Array Lin) (X cb A B : ℕ) (h : UInt64)

/-- A proto-piece's indexed rows. -/
def RP.rows (one : Lin) : RP → List (ℕ × Row)
  | .sp rs => rs
  | .raw T ins X cb _ _ _ => instIR T one ins.toList X cb

/-- A raw instance if aligned (`RawI.aligned`), else its rows. -/
def mkRaw (one : Lin) (T : List RowT) (ins : Array Lin) (X cb A B : ℕ) (h : UInt64) : RP :=
  if X % 2 ^ A == 0 && cb % 2 ^ B == 0 && decide (A ≤ 21) && decide (B ≤ 23) then
    .raw T ins X cb A B h
  else .sp (instIR T one ins.toList X cb)

/-- The abstraction's state with a confirmed lookup (`absTerm`'s, the input cells numbered by first
appearance). -/
def absTermV (c0 W : ℕ) (st : AbsSt) (t : ℕ × F) : (Wire × F) × AbsSt :=
  if c0 ≤ t.1 ∧ t.1 < c0 + W then ((.loc (t.1 - c0), t.2), st)
  else match st.idx[t.1]? with
    | some i => if st.cells[i]? == some t.1 then ((.inp i, t.2), st) else
        ((.inp st.cells.size, t.2), ⟨st.idx.insert t.1 st.cells.size, st.cells.push t.1⟩)
    | none => ((.inp st.cells.size, t.2), ⟨st.idx.insert t.1 st.cells.size, st.cells.push t.1⟩)

def absLinV (c0 W : ℕ) : AbsSt → Lin → LinT × AbsSt
  | st, [] => ([], st)
  | st, t :: l => let u := absTermV c0 W st t; let r := absLinV c0 W u.2 l; (u.1 :: r.1, r.2)

def absRowsR (c0 W : ℕ) : AbsSt → List Row → List RowT × AbsSt
  | st, [] => ([], st)
  | st, row :: rows =>
    let a := absLinV c0 W st row.a
    let b := absLinV c0 W a.2 row.b
    let c := absLinV c0 W b.2 row.c
    let r := absRowsR c0 W c.2 rows
    (⟨a.1, b.1, c.1⟩ :: r.1, r.2)

/-- **A skeleton block's abstraction** over the cell window `[c0, c0 + W)`. -/
def absRowsV (c0 W : ℕ) (rows : List Row) : List RowT × Array ℕ :=
  let r := absRowsR c0 W ⟨{}, #[]⟩ rows
  (r.1, r.2.cells)

/-- Rows `[a, b)` of the skeleton, indexed from `off`. -/
def skRun (sk : Array Row) (off a b : ℕ) : List (ℕ × Row) :=
  (List.range (b - a)).map fun i => (off + a + i, sk.getD (a + i) ⟨[], [], []⟩)

/-! ### Matching a skeleton block against a known template (S-E13: no abstraction, no hash) -/

/-- Match a block's term against a template term: a local at the window's cell, or an input whose
cell is set at its first appearance and checked after. -/
def matchTerm (c0 : ℕ) (cells : Array (Option ℕ)) (w : Wire × F) (t : ℕ × F) : Option (Array (Option ℕ)) :=
  if w.2 == t.2 then
    match w.1 with
    | .loc k => if t.1 == c0 + k then some cells else none
    | .inp i => match cells[i]? with
      | some (some c) => if c == t.1 then some cells else none
      | some none => some (cells.setIfInBounds i (some t.1))
      | none => none
    | .one => none
  else none

def matchLin (c0 : ℕ) : Array (Option ℕ) → LinT → Lin → Option (Array (Option ℕ))
  | cells, [], [] => some cells
  | cells, w :: ws, t :: ts => (matchTerm c0 cells w t).bind fun c => matchLin c0 c ws ts
  | _, _, _ => none

def matchRows (c0 : ℕ) : Array (Option ℕ) → List RowT → List Row → Option (Array (Option ℕ))
  | cells, [], [] => some cells
  | cells, r :: rs, row :: rows =>
    (matchLin c0 cells r.a row.a).bind fun c => (matchLin c0 c r.b row.b).bind fun c =>
      (matchLin c0 c r.c row.c).bind fun c => matchRows c0 c rs rows
  | _, _, _ => none

/-- **A block matched against a template** with `n` inputs: its input forms, if it is an instance. -/
def absMatch (T : List RowT) (n c0 : ℕ) (rows : List Row) : Option (Array Lin) :=
  (matchRows c0 (Array.replicate n none) T rows).map fun cells => cells.map fun o => Lin.cell (o.getD 0)

/-- Known skeleton templates by shape (rows, cell bits): the template, its input count, its hash. -/
abbrev Cands := List ((ℕ × ℕ) × List RowT × ℕ × UInt64)

/-- The first known template of a shape that the block is an instance of. -/
def tryCands (c0 : ℕ) (rows : List Row) (key : ℕ × ℕ) : Cands → Option (List RowT × UInt64 × Array Lin)
  | [] => none
  | (k, T, n, h) :: cs =>
    if k == key then
      match absMatch T n c0 rows with
      | some ins => some (T, h, ins)
      | none => tryCands c0 rows key cs
    else tryCands c0 rows key cs

/-- **A skeleton block's proto-piece**: matched against the known templates of its shape (the
template object shared, so that the piece check compares pointers), else abstracted (`absRowsV`) and
remembered. -/
def blockRPC (one : Lin) (cand : Cands) (rows : List Row) (X c0 B : ℕ) : RP × Cands :=
  match tryCands c0 rows (rows.length, B) cand with
  | some (T, h, ins) => (mkRaw one T ins X c0 (Nat.size (rows.length - 1)) B h, cand)
  | none =>
    let ab := absRowsV c0 (2 ^ B) rows
    let h := hash ab.1
    (mkRaw one ab.1 (ab.2.map Lin.cell) X c0 (Nat.size (rows.length - 1)) B h,
      ((rows.length, B), ab.1, ab.2.size, h) :: cand)

/-- The skeleton's proto-pieces from row `p` on (the blocks skipping any that is out of order or out
of range, sparse runs between them), last first. -/
def skelGo (one : Lin) (sk : Array Row) (off : ℕ) : List Seg → List RP → ℕ → Cands → List RP × ℕ × Cands
  | [], acc, p, cand => (acc, p, cand)
  | s :: segs, acc, p, cand =>
    if s.r0 < p ∨ sk.size < s.r1 ∨ s.r1 ≤ s.r0 then skelGo one sk off segs acc p cand else
    let b := blockRPC one cand ((List.range (s.r1 - s.r0)).map fun i => sk.getD (s.r0 + i) ⟨[], [], []⟩)
      (off + s.r0) s.c0 s.B
    skelGo one sk off segs (b.1 :: (if p < s.r0 then RP.sp (skRun sk off p s.r0) :: acc else acc)) s.r1 b.2

/-- **The skeleton's proto-pieces** and the known templates after them. -/
def skelRP (one : Lin) (sk : Array Row) (off : ℕ) (segs : List Seg) (cand : Cands) : List RP × Cands :=
  let r := skelGo one sk off segs [] 0 cand
  ((RP.sp (skRun sk off r.2.1 sk.size) :: r.1).reverse, r.2.2)

/-- The proto-pieces of an instance's blocks (block `c` at rows `X + S·c`, cells `cb + S·c`). -/
def blkRPs (one : Lin) (ia : Array Lin) (cb X S : ℕ) : ℕ → List Blk → List RP
  | _, [] => []
  | c, bk :: bks =>
    mkRaw one bk.T (bk.src.map (srcLin ia cb)) (X + S * c) (cb + S * c) (Nat.size (S - 1))
      (Nat.size (S - 1)) bk.h :: blkRPs one ia cb X S (c + 1) bks

/-- **A template instance's proto-pieces** (`tinPP`'s cut): split keys their head and tail, blocked
keys their blocks and the rest sparse, other keys the whole instance. -/
def tinRP (one : Lin) (Ms : List KM) (L : TLay) (off : ℕ) (t : TKey × ℕ × List Lin) : List RP :=
  let e := kmOf Ms t.1
  let ia := t.2.2.toArray
  let cb := L.cb t.1 t.2.1
  let bb := L.bits t.1
  match splitOf t.1 with
  | some (a, b) =>
    let X0 := off + L.rb t.1
    [mkRaw one e.hd ia (X0 + splitRow a b t.2.1 0) cb a bb e.hh,
     mkRaw one e.tl ia (X0 + splitRow a b t.2.1 (2 ^ a)) cb b bb e.ht]
  | none =>
    let X := off + L.rb t.1 + t.2.1 * 2 ^ e.rb
    match blkSize t.1 e.rb with
    | some S =>
      blkRPs one ia cb X S 0 e.blks ++
      [RP.sp (instIR (e.rows.drop (S * e.blks.length)) one t.2.2 (X + S * e.blks.length) cb)]
    | none => [mkRaw one e.rows ia X cb e.rb bb e.h]

/-- **A slot's proto-pieces**: the skeleton's, then every instance's. -/
def slotRP (one : Lin) (Ms : List KM) (L : TLay) (off : ℕ) (cs : CS) (segs : List Seg) (cand : Cands) :
    Array RP × Cands :=
  let sk := skelRP one cs.rowList.toArray off segs cand
  ((sk.1 ++ cs.tins.flatMap (tinRP one Ms L off)).toArray, sk.2)

/-! ## Keys and the piece check -/

/-- The largest input number of a form, plus one, at least `m`. -/
def maxInpL (l : LinT) (m : ℕ) : ℕ :=
  l.foldr (fun t m => match t.1 with
    | .inp i => max (i + 1) m
    | _ => m) m

/-- The largest input number of a template's rows, plus one. -/
def maxInp (T : List RowT) : ℕ := T.foldr (fun r m => maxInpL (r.a ++ r.b ++ r.c) m) 0

theorem maxInpL_spec : ∀ (l : LinT) (m : ℕ), m ≤ maxInpL l m ∧
    ∀ t ∈ l, ∀ i, t.1 = .inp i → i < maxInpL l m
  | [], m => ⟨le_rfl, by simp⟩
  | t :: l, m => by
    obtain ⟨h1, h2⟩ := maxInpL_spec l m
    simp only [maxInpL, List.foldr_cons] at h1 h2 ⊢
    split
    · rename_i i hi
      refine ⟨h1.trans (le_max_right _ _), fun t' ht' i' hi' => ?_⟩
      rcases List.mem_cons.1 ht' with rfl | ht'
      · rw [hi] at hi'; cases hi'; exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
      · exact (h2 t' ht' i' hi').trans_le (le_max_right _ _)
    · refine ⟨h1, fun t' ht' i' hi' => ?_⟩
      rcases List.mem_cons.1 ht' with rfl | ht'
      · rename_i hn; exact absurd hi' (hn i')
      · exact h2 t' ht' i' hi'

theorem maxInp_spec : ∀ (T : List RowT), ∀ r ∈ T, ∀ t ∈ r.a ++ r.b ++ r.c, ∀ i,
    t.1 = .inp i → i < maxInp T
  | [] => by simp
  | r :: T => by
    intro r' hr' t ht i hi
    simp only [maxInp, List.foldr_cons] at ht ⊢
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact (maxInpL_spec _ _).2 t ht i hi
    · exact (maxInp_spec T r' hr' t ht i hi).trans_le (maxInpL_spec _ _).1

/-- **A key's group data**: the raw template rows, the input kinds, the bits, and a bound on the
input numbers with its proof (so that the untrusted grouping cannot give a wrong one). -/
structure GK where
  T : List RowT
  ks : Array IK
  A : ℕ
  B : ℕ
  n : ℕ
  hn : ∀ r ∈ T, ∀ t ∈ r.a ++ r.b ++ r.c, ∀ i, t.1 = .inp i → i < n

def mkGK (T : List RowT) (ks : Array IK) (A B : ℕ) : GK := ⟨T, ks, A, B, maxInp T, maxInp_spec T⟩

def dGK : GK := mkGK [] #[] 0 0

/-- The evaluator's key of a group: its rows with the inputs rewritten by kind. -/
def mkKey (g : GK) : Key := ⟨g.T.map (rwRow (kindWire g.ks)), g.A, g.B⟩

/-- **The input check**: every input reads, under the key's rewrite, the instance's form. -/
def insOk (ks : Array IK) (n : ℕ) (inp : Array Lin) (ins : Array Lin) (cb : ℕ) : Bool :=
  (List.range n).all fun i => match kindWire ks i with
    | .loc c => ins.getD i [] == Lin.cell (cb + c)
    | .inp j => inp.getD j [] == ins.getD i []
    | .one => false

/-- **The piece of a proto-piece** under the grouping's proposal (key `k`, own inputs `own`): the
instance if the check passes, else the proto-piece's rows. -/
def toPiece (G : Array GK) (sh : Array (List Lin)) (one : Lin) (rp : RP) (k : ℕ) (own : List Lin) :
    Piece :=
  match rp with
  | .sp rs => .sp rs
  | .raw T ins X cb A B _ =>
    let g := G.getD k dGK
    if g.A == A && g.B == B && X % 2 ^ A == 0 && cb % 2 ^ B == 0 &&
        withPtrEq T g.T (fun _ => T == g.T) (fun h => by simp [h]) &&
        insOk g.ks g.n (sh.getD k [] ++ own).toArray ins cb then
      .ins k (X / 2 ^ A) (cb / 2 ^ B) own
    else .sp (instIR T one ins.toList X cb)

/-! ## The grouping (untrusted: `toPiece` checks each proposal) -/

/-- The distinct forms of input `i` in slot `σ`'s members, if at most 16 (`distinctUpTo`'s, stopping
at the 17th). -/
def distinctIn (mem : Array (ℕ × RawI)) (σ i : ℕ) : Option (List Lin) :=
  mem.foldl (fun acc p => acc.bind fun d =>
    if p.1 != σ then some d else
    let v := p.2.ins.getD i []
    if d.contains v then some d else if d.length < 16 then some (d ++ [v]) else none) (some [])

/-- **`inputKinds`, computed per member array** (the same kinds and partition inputs; S-E13: no
column lists): an input is a local if it is one cell at a fixed offset in every member's window, a
partition input if it takes at most 16 values per slot (parts of at least 4 members), else own. -/
def inputKindsF (mem : Array (ℕ × RawI)) (part : Bool := true) :
    Array IK × List (ℕ × List Lin × List Lin) :=
  let n := mem.foldl (fun m p => max m p.2.ins.size) 0
  let n0 := mem.foldl (fun c p => if p.1 == 0 then c + 1 else c) 0
  let n1 := mem.foldl (fun c p => if p.1 == 1 then c + 1 else c) 0
  let r := (List.range n).foldl (fun (q : Array IK × List (ℕ × List Lin × List Lin) × ℕ) i =>
    let lc := match mem[0]? with
      | some p0 => match offIn p0.2.cb (2 ^ p0.2.B) (p0.2.ins.getD i []) with
        | some c => if mem.all (fun p => offIn p.2.cb (2 ^ p.2.B) (p.2.ins.getD i []) == some c) then some c
          else none
        | none => none
      | none => none
    match lc with
    | some c => (q.1.push (IK.loc c), q.2.1, q.2.2)
    | none =>
      match (if part then distinctIn mem 0 i else none), distinctIn mem 1 i with
      | some d0, some d1 =>
        if (d0.length ≤ 1 && d1.length ≤ 1) || (4 * d0.length ≤ n0 && 4 * d1.length ≤ n1) then
          (q.1.push (IK.sh q.2.1.length), q.2.1 ++ [(i, d0, d1)], q.2.2)
        else (q.1.push (IK.own q.2.2), q.2.1, q.2.2 + 1)
      | _, _ => (q.1.push (IK.own q.2.2), q.2.1, q.2.2 + 1)) ((#[] : Array IK), [], 0)
  (r.1.map fun k => match k with
    | .own i => IK.own (r.2.1.length + i)
    | k => k, r.2.1)

/-- The input numbers in own order (`ownOf`'s, once per group). -/
def ownIdx (ks : Array IK) : List ℕ :=
  (((List.range ks.size).filterMap fun i => match ks[i]? with
    | some (IK.own j) => some (j, i)
    | _ => none).mergeSort (fun a b => a.1 ≤ b.1)).map (·.2)

/-- **The grouping** of two slots' proto-pieces (`groupPPs`'s, keyed by the templates' hashes):
the keys' group data, each slot's shared forms, and per proto-piece a proposed key and own inputs. -/
def groupRP (pp0 pp1 : Array RP) : Array GK × Array (List Lin) × Array (List Lin) ×
    Array (Option (ℕ × List Lin)) × Array (Option (ℕ × List Lin)) :=
  let addAll := fun (σ : ℕ) (pps : Array RP)
      (st : Std.HashMap (UInt64 × ℕ × ℕ) ℕ × Array (List (ℕ × RawI))) =>
    pps.foldl (fun st p => match p with
      | .raw T ins X cb A B h =>
        let r : RawI := ⟨T, ins, X, cb, A, B⟩
        match st.1[(h, A, B)]? with
        | some k => (st.1, st.2.modify k ((σ, r) :: ·))
        | none => (st.1.insert (h, A, B) st.2.size, st.2.push [(σ, r)])
      | .sp _ => st) st
  let st := addAll 1 pp1 (addAll 0 pp0 ({}, #[]))
  let mems := st.2.map List.reverse
  let ana := mems.map fun (m : List (ℕ × RawI)) =>
    let ma := m.toArray
    let a := inputKindsF ma
    let labs := m.foldl (fun (acc : List (ℕ × List ℕ)) p =>
      let l := (p.1, partLabel a.2 p.1 p.2); if acc.contains l then acc else l :: acc) []
    let a := if 4 * labs.length ≤ m.length then a else inputKindsF ma false
    match m with
    | (_, r) :: _ => (sortOwn r a.1, a.2)
    | [] => a
  let st2 := (List.range mems.size).foldl (fun (q : Std.HashMap (ℕ × List ℕ) ℕ × Array (ℕ × List ℕ)) g =>
    (mems.getD g []).foldl (fun q m =>
      let lab := partLabel (ana.getD g (#[], [])).2 m.1 m.2
      match q.1[(g, lab)]? with
      | some _ => q
      | none => (q.1.insert (g, lab) q.2.size, q.2.push (g, lab))) q) ({}, #[])
  let gks := st2.2.map fun gl => match mems.getD gl.1 [] with
    | (_, r) :: _ => mkGK r.T (ana.getD gl.1 (#[], [])).1 r.A r.B
    | [] => dGK
  let sh := fun σ => st2.2.map fun gl => partShared (ana.getD gl.1 (#[], [])).2 σ gl.2
  let oidx := ana.map fun a => ownIdx a.1
  let prop := fun (σ : ℕ) (pps : Array RP) => pps.map fun p => match p with
    | .sp _ => none
    | .raw T ins X cb A B h =>
      let r : RawI := ⟨T, ins, X, cb, A, B⟩
      match st.1[(h, A, B)]? with
      | some g =>
        let a := ana.getD g (#[], [])
        let oi := oidx.getD g []
        match st2.1[(g, partLabel a.2 σ r)]? with
        | some k => some (k, oi.map fun i => r.ins.getD i [])
        | none => none
      | none => none
  (gks, sh 0, sh 1, prop 0 pp0, prop 1 pp1)

/-- A slot's pieces from its proto-pieces and the grouping's proposals. -/
def piecesOf (G : Array GK) (sh : Array (List Lin)) (one : Lin) (rps : Array RP)
    (pr : Array (Option (ℕ × List Lin))) : List Piece :=
  (List.range rps.size).map fun i =>
    let rp := rps.getD i (.sp [])
    match pr.getD i none with
    | some (k, own) => toPiece G sh one rp k own
    | none => match rp with
      | .sp rs => .sp rs
      | .raw T ins X cb _ _ _ => .sp (instIR T one ins.toList X cb)

/-! ## Proofs: the proto-pieces' rows are the slot's -/

/-- An instantiated term (`instLin`'s body). -/
def instT (one : Lin) (ins : List Lin) (cb : ℕ) (t : Wire × F) : Lin :=
  match t.1 with
  | .one => one.smul t.2
  | .inp i => (ins.getD i []).smul t.2
  | .loc k => [(cb + k, t.2)]

theorem instLin_nil (one : Lin) (ins : List Lin) (cb : ℕ) : instLin one ins cb [] = [] := rfl

theorem instLin_cons (one : Lin) (ins : List Lin) (cb : ℕ) (t : Wire × F) (l : LinT) :
    instLin one ins cb (t :: l) = instT one ins cb t ++ instLin one ins cb l := rfl

theorem cell_smul (c : ℕ) (a : F) : (Lin.cell c).smul a = [(c, a)] := by
  simp [Lin.cell, Lin.smul]

theorem pre_get {α : Type*} {l m : List α} (h : l <+: m) {i : ℕ} {x : α} (hi : l[i]? = some x) :
    m[i]? = some x := by
  obtain ⟨u, rfl⟩ := h
  have : i < l.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  rw [List.getElem?_append_left this, hi]

theorem pre_push {α : Type*} (a : Array α) (x : α) : a.toList <+: (a.push x).toList := by
  rw [Array.toList_push]; exact List.prefix_append _ _

theorem get_push {α : Type*} (a : Array α) (x : α) : (a.push x).toList[a.size]? = some x := by
  rw [Array.toList_push, List.getElem?_append_right (by simp)]; simp

theorem getD_map_cell {cs : List ℕ} {i c : ℕ} (h : cs[i]? = some c) :
    (cs.map Lin.cell).getD i [] = Lin.cell c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]; rfl

/-! ### The skeleton blocks' abstraction -/

theorem absTermV_spec (one : Lin) (c0 W : ℕ) (st : AbsSt) (t : ℕ × F) :
    st.cells.toList <+: (absTermV c0 W st t).2.cells.toList ∧
    ∀ cs : List ℕ, (absTermV c0 W st t).2.cells.toList <+: cs →
      instT one (cs.map Lin.cell) c0 (absTermV c0 W st t).1 = [t] := by
  have fresh : ∀ cs : List ℕ, (st.cells.push t.1).toList <+: cs →
      instT one (cs.map Lin.cell) c0 (.inp st.cells.size, t.2) = [t] := fun cs h => by
    simp only [instT, getD_map_cell (pre_get h (get_push _ _)), cell_smul]
  unfold absTermV
  split_ifs with hw
  · refine ⟨List.prefix_refl _, fun _ _ => ?_⟩
    simp only [instT, Nat.add_sub_cancel' hw.1]
  · split
    · rename_i i _
      split_ifs with hc
      · refine ⟨List.prefix_refl _, fun cs h => ?_⟩
        have hc' : st.cells.toList[i]? = some t.1 := by
          rw [Array.getElem?_toList]; exact eq_of_beq hc
        simp only [instT, getD_map_cell (pre_get h hc'), cell_smul]
      · exact ⟨pre_push _ _, fresh⟩
    · exact ⟨pre_push _ _, fresh⟩

theorem absLinV_spec (one : Lin) (c0 W : ℕ) : ∀ (l : Lin) (st : AbsSt),
    st.cells.toList <+: (absLinV c0 W st l).2.cells.toList ∧
    ∀ cs : List ℕ, (absLinV c0 W st l).2.cells.toList <+: cs →
      instLin one (cs.map Lin.cell) c0 (absLinV c0 W st l).1 = l
  | [], _ => ⟨List.prefix_refl _, fun _ _ => rfl⟩
  | t :: l, st => by
    obtain ⟨h1, h2⟩ := absTermV_spec one c0 W st t
    obtain ⟨h3, h4⟩ := absLinV_spec one c0 W l (absTermV c0 W st t).2
    refine ⟨h1.trans h3, fun cs h => ?_⟩
    simp only [absLinV, instLin_cons]
    rw [h2 cs (h3.trans h), h4 cs h]; rfl

theorem absRowsR_spec (one : Lin) (c0 W : ℕ) : ∀ (rows : List Row) (st : AbsSt),
    st.cells.toList <+: (absRowsR c0 W st rows).2.cells.toList ∧
    ∀ cs : List ℕ, (absRowsR c0 W st rows).2.cells.toList <+: cs →
      (absRowsR c0 W st rows).1.map (instRow one (cs.map Lin.cell) c0) = rows
  | [], _ => ⟨List.prefix_refl _, fun _ _ => rfl⟩
  | row :: rows, st => by
    obtain ⟨ha, ha'⟩ := absLinV_spec one c0 W row.a st
    obtain ⟨hb, hb'⟩ := absLinV_spec one c0 W row.b (absLinV c0 W st row.a).2
    obtain ⟨hc, hc'⟩ := absLinV_spec one c0 W row.c (absLinV c0 W (absLinV c0 W st row.a).2 row.b).2
    obtain ⟨hr, hr'⟩ := absRowsR_spec one c0 W rows
      (absLinV c0 W (absLinV c0 W (absLinV c0 W st row.a).2 row.b).2 row.c).2
    refine ⟨ha.trans (hb.trans (hc.trans hr)), fun cs h => ?_⟩
    simp only [absRowsR, List.map_cons, hr' cs h]
    rw [instRow, ha' cs (hb.trans (hc.trans (hr.trans h))), hb' cs (hc.trans (hr.trans h)),
      hc' cs (hr.trans h)]

/-- **A skeleton block's abstraction instantiates back to its rows.** -/
theorem absRowsV_inst (one : Lin) (c0 W : ℕ) (rows : List Row) :
    (absRowsV c0 W rows).1.map (instRow one ((absRowsV c0 W rows).2.toList.map Lin.cell) c0) = rows :=
  (absRowsR_spec one c0 W rows _).2 _ (List.prefix_refl _)

/-! ### The template blocks' re-templating -/

theorem reNew_spec (st : ReSt) (s : Src) :
    st.src.toList <+: (reNew st s).2.src.toList ∧ (reNew st s).2.src.toList[(reNew st s).1]? = some s := by
  unfold reNew
  split
  · split_ifs with hc
    · exact ⟨List.prefix_refl _, by rw [Array.getElem?_toList]; exact eq_of_beq hc⟩
    · exact ⟨pre_push _ _, get_push _ _⟩
  · exact ⟨pre_push _ _, get_push _ _⟩

theorem reWire_spec (one : Lin) (ins : Array Lin) (cb w W : ℕ) (st : ReSt) (x : Wire) (a : F) :
    st.src.toList <+: (reWire w W st x).2.src.toList ∧
    ∀ S : List Src, (reWire w W st x).2.src.toList <+: S →
      instT one (S.map (srcLin ins cb)) (cb + w) ((reWire w W st x).1, a) =
        instT one ins.toList cb (x, a) := by
  have hn : ∀ s : Src, ∀ S : List Src, (reNew st s).2.src.toList <+: S →
      (S.map (srcLin ins cb)).getD (reNew st s).1 [] = srcLin ins cb s := fun s S h => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, pre_get h (reNew_spec st s).2]; rfl
  cases x with
  | one => exact ⟨List.prefix_refl _, fun _ _ => rfl⟩
  | loc k =>
    dsimp only [reWire]
    split_ifs with hw
    · refine ⟨List.prefix_refl _, fun _ _ => ?_⟩
      simp only [instT]; congr 2; omega
    · refine ⟨(reNew_spec st _).1, fun S h => ?_⟩
      simp only [instT, hn _ S h, srcLin, cell_smul]
  | inp i =>
    refine ⟨(reNew_spec st _).1, fun S h => ?_⟩
    simp only [reWire, instT, hn _ S h, srcLin, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      Array.getElem?_toList]

theorem reLin_spec (one : Lin) (ins : Array Lin) (cb w W : ℕ) : ∀ (l : LinT) (st : ReSt),
    st.src.toList <+: (reLin w W st l).2.src.toList ∧
    ∀ S : List Src, (reLin w W st l).2.src.toList <+: S →
      instLin one (S.map (srcLin ins cb)) (cb + w) (reLin w W st l).1 = instLin one ins.toList cb l
  | [], _ => ⟨List.prefix_refl _, fun _ _ => rfl⟩
  | t :: l, st => by
    obtain ⟨h1, h2⟩ := reWire_spec one ins cb w W st t.1 t.2
    obtain ⟨h3, h4⟩ := reLin_spec one ins cb w W l (reWire w W st t.1).2
    refine ⟨h1.trans h3, fun S h => ?_⟩
    simp only [reLin, instLin_cons]
    rw [h2 S (h3.trans h), h4 S h]

theorem reRows_spec (one : Lin) (ins : Array Lin) (cb w W : ℕ) : ∀ (rows : List RowT) (st : ReSt),
    st.src.toList <+: (reRows w W st rows).2.src.toList ∧
    ∀ S : List Src, (reRows w W st rows).2.src.toList <+: S →
      (reRows w W st rows).1.map (instRow one (S.map (srcLin ins cb)) (cb + w)) =
        rows.map (instRow one ins.toList cb)
  | [], _ => ⟨List.prefix_refl _, fun _ _ => rfl⟩
  | row :: rows, st => by
    obtain ⟨ha, ha'⟩ := reLin_spec one ins cb w W row.a st
    obtain ⟨hb, hb'⟩ := reLin_spec one ins cb w W row.b (reLin w W st row.a).2
    obtain ⟨hc, hc'⟩ := reLin_spec one ins cb w W row.c (reLin w W (reLin w W st row.a).2 row.b).2
    obtain ⟨hr, hr'⟩ := reRows_spec one ins cb w W rows
      (reLin w W (reLin w W (reLin w W st row.a).2 row.b).2 row.c).2
    refine ⟨ha.trans (hb.trans (hc.trans hr)), fun S h => ?_⟩
    simp only [reRows, List.map_cons, hr' S h]
    rw [instRow, ha' S (hb.trans (hc.trans (hr.trans h))), hb' S (hc.trans (hr.trans h)),
      hc' S (hr.trans h)]; rfl

/-- **A re-templated block instantiates back to the instance's rows.** -/
theorem reT_inst (one : Lin) (ins : Array Lin) (cb w W : ℕ) (rows : List RowT) :
    (reT w W rows).1.map (instRow one ((reT w W rows).2.map (srcLin ins cb)).toList (cb + w)) =
      rows.map (instRow one ins.toList cb) := by
  rw [Array.toList_map]
  exact (reRows_spec one ins cb w W rows _).2 _ (List.prefix_refl _)

/-! ### The skeleton -/

/-- Rows indexed from `X`. -/
def idxR {α : Type*} (X : ℕ) (rows : List α) : List (ℕ × α) := rows.zipIdx.map fun p => (X + p.2, p.1)

theorem idxR_append {α : Type*} (X : ℕ) (a b : List α) :
    idxR X (a ++ b) = idxR X a ++ idxR (X + a.length) b := by
  simp only [idxR, List.zipIdx_append, List.map_append, zero_add, List.map_map]
  congr 1
  rw [List.zipIdx_eq_map_add]
  simp only [List.map_map]
  congr 1; funext p; simp [Function.comp_def, add_assoc]

theorem instIR_eq (T : List RowT) (one : Lin) (ins : List Lin) (X cb : ℕ) :
    instIR T one ins X cb = idxR X (T.map (instRow one ins cb)) := by
  simp only [instIR, idxR, List.zipIdx_map, List.map_map]; rfl

theorem RP.rows_sp (one : Lin) (rs : List (ℕ × Row)) : (RP.sp rs).rows one = rs := rfl

theorem mkRaw_rows (one : Lin) (T : List RowT) (ins : Array Lin) (X cb A B : ℕ) (h : UInt64) :
    (mkRaw one T ins X cb A B h).rows one = instIR T one ins.toList X cb := by
  unfold mkRaw; split <;> rfl

theorem idxR_range {α : Type*} (X n : ℕ) (f : ℕ → α) :
    idxR X ((List.range n).map f) = (List.range n).map fun i => (X + i, f i) := by
  refine List.ext_getElem (by simp [idxR]) fun i h₁ h₂ => ?_
  simp [idxR]

theorem skRun_append (sk : Array Row) (off : ℕ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    skRun sk off a b ++ skRun sk off b c = skRun sk off a c := by
  have : c - a = (b - a) + (c - b) := by omega
  simp only [skRun, this, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Prod.mk.injEq]
  exact ⟨by omega, by rw [show a + (b - a + i) = b + i by omega]⟩

theorem skRun_all (sk : Array Row) (off : ℕ) :
    skRun sk off 0 sk.size = idxR off sk.toList := by
  unfold skRun idxR
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipIdx, zero_add, Nat.sub_zero]
  simp only [List.length_map, List.length_range, Nat.sub_zero] at h₁
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h₁]; simp

/-- `b` extends `a`: same size, every set cell kept. -/
def CExt (a b : Array (Option ℕ)) : Prop :=
  a.size = b.size ∧ ∀ i c : ℕ, a[i]? = some (some c) → b[i]? = some (some c)

theorem CExt.refl (a : Array (Option ℕ)) : CExt a a := ⟨rfl, fun _ _ h => h⟩
theorem CExt.trans {a b c : Array (Option ℕ)} (h1 : CExt a b) (h2 : CExt b c) : CExt a c :=
  ⟨h1.1.trans h2.1, fun i x h => h2.2 i x (h1.2 i x h)⟩

/-- The instantiation of a term with the final cells. -/
theorem matchTerm_spec (one : Lin) (c0 : ℕ) (cells : Array (Option ℕ)) (w : Wire × F) (t : ℕ × F)
    (c' : Array (Option ℕ)) (h : matchTerm c0 cells w t = some c') :
    CExt cells c' ∧ ∀ fin : Array (Option ℕ), CExt c' fin →
      instT one (fin.toList.map fun o => Lin.cell (o.getD 0)) c0 w = [t] := by
  obtain ⟨wv, a⟩ := w; obtain ⟨tc, ta⟩ := t
  unfold matchTerm at h
  split_ifs at h with ha
  have ha' : a = ta := eq_of_beq ha
  subst ha'
  cases wv with
  | one => cases h
  | loc k =>
    simp only at h
    split_ifs at h with hk
    cases h
    refine ⟨CExt.refl _, fun _ _ => ?_⟩
    simp only [instT, eq_of_beq hk]
  | inp i =>
    simp only at h
    have hget : ∀ fin : Array (Option ℕ), fin[i]? = some (some tc) →
        instT one (fin.toList.map fun o => Lin.cell (o.getD 0)) c0 (.inp i, a) = [(tc, a)] := fun fin hf => by
      simp only [instT]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList, hf]
      simp [Lin.cell, Lin.smul]
    split at h
    · rename_i c hc
      split_ifs at h with hct
      cases h
      refine ⟨CExt.refl _, fun fin hf => hget fin (hf.2 i c hc ▸ by rw [eq_of_beq hct])⟩
    · rename_i hc
      cases h
      have hi : i < cells.size := by
        by_contra hn; rw [Array.getElem?_eq_none (by omega)] at hc; cases hc
      refine ⟨⟨by simp, fun j x hj => ?_⟩, fun fin hf => hget fin (hf.2 i tc (by
        simp [Array.getElem?_setIfInBounds, hi]))⟩
      by_cases hji : j = i
      · subst hji; rw [hc] at hj; cases hj
      · rw [Array.getElem?_setIfInBounds, if_neg (Ne.symm hji)]; exact hj
    · cases h

theorem matchLin_spec (one : Lin) (c0 : ℕ) : ∀ (ws : LinT) (ts : Lin) (cells c' : Array (Option ℕ)),
    matchLin c0 cells ws ts = some c' →
    CExt cells c' ∧ ∀ fin : Array (Option ℕ), CExt c' fin →
      instLin one (fin.toList.map fun o => Lin.cell (o.getD 0)) c0 ws = ts
  | [], [], _, _, h => by cases h; exact ⟨CExt.refl _, fun _ _ => rfl⟩
  | w :: ws, t :: ts, cells, c', h => by
    simp only [matchLin, Option.bind_eq_some_iff] at h
    obtain ⟨c1, h1, h2⟩ := h
    obtain ⟨e1, f1⟩ := matchTerm_spec one c0 cells w t c1 h1
    obtain ⟨e2, f2⟩ := matchLin_spec one c0 ws ts c1 c' h2
    refine ⟨e1.trans e2, fun fin hf => ?_⟩
    rw [instLin_cons, f1 fin (e2.trans hf), f2 fin hf]; rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

theorem matchRows_spec (one : Lin) (c0 : ℕ) : ∀ (T : List RowT) (rows : List Row)
    (cells c' : Array (Option ℕ)), matchRows c0 cells T rows = some c' →
    CExt cells c' ∧ ∀ fin : Array (Option ℕ), CExt c' fin →
      T.map (instRow one (fin.toList.map fun o => Lin.cell (o.getD 0)) c0) = rows
  | [], [], _, _, h => by cases h; exact ⟨CExt.refl _, fun _ _ => rfl⟩
  | r :: rs, row :: rows, cells, c', h => by
    simp only [matchRows, Option.bind_eq_some_iff] at h
    obtain ⟨ca, ha, cb, hb, cc, hc, hr⟩ := h
    obtain ⟨ea, fa⟩ := matchLin_spec one c0 _ _ _ _ ha
    obtain ⟨eb, fb⟩ := matchLin_spec one c0 _ _ _ _ hb
    obtain ⟨ec, fc⟩ := matchLin_spec one c0 _ _ _ _ hc
    obtain ⟨er, fr⟩ := matchRows_spec one c0 rs rows cc c' hr
    refine ⟨ea.trans (eb.trans (ec.trans er)), fun fin hf => ?_⟩
    rw [List.map_cons, fr fin hf, instRow, fa fin (eb.trans (ec.trans (er.trans hf))),
      fb fin (ec.trans (er.trans hf)), fc fin (er.trans hf)]
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

/-- **A matched block instantiates back to its rows.** -/
theorem absMatch_inst (one : Lin) {T : List RowT} {n c0 : ℕ} {rows : List Row} {ins : Array Lin}
    (h : absMatch T n c0 rows = some ins) : T.map (instRow one ins.toList c0) = rows := by
  simp only [absMatch, Option.map_eq_some_iff] at h
  obtain ⟨cells, hc, rfl⟩ := h
  rw [Array.toList_map]
  exact (matchRows_spec one c0 T rows _ cells hc).2 cells (CExt.refl _)

theorem tryCands_spec (one : Lin) (c0 : ℕ) (rows : List Row) (key : ℕ × ℕ) :
    ∀ (cs : Cands) {T : List RowT} {h : UInt64} {ins : Array Lin},
      tryCands c0 rows key cs = some (T, h, ins) → T.map (instRow one ins.toList c0) = rows
  | [], _, _, _, hc => by cases hc
  | (k, T', n, h') :: cs, T, h, ins, hc => by
    unfold tryCands at hc
    split_ifs at hc
    · split at hc
      · rename_i ins' hm
        cases hc; exact absMatch_inst one hm
      · exact tryCands_spec one c0 rows key cs hc
    · exact tryCands_spec one c0 rows key cs hc

theorem blockRPC_rows (one : Lin) (cand : Cands) (rows : List Row) (X c0 B : ℕ) :
    (blockRPC one cand rows X c0 B).1.rows one = idxR X rows := by
  unfold blockRPC
  split
  · rename_i T h ins hc
    simp only [mkRaw_rows, instIR_eq, tryCands_spec one c0 rows _ cand hc]
  · simp only [mkRaw_rows, instIR_eq, Array.toList_map, absRowsV_inst]

theorem skelGo_rows (one : Lin) (sk : Array Row) (off : ℕ) :
    ∀ (segs : List Seg) (acc : List RP) (p : ℕ) (cand : Cands), p ≤ sk.size →
      acc.reverse.flatMap (RP.rows one) = skRun sk off 0 p →
      (skelGo one sk off segs acc p cand).2.1 ≤ sk.size ∧
        (skelGo one sk off segs acc p cand).1.reverse.flatMap (RP.rows one) =
          skRun sk off 0 (skelGo one sk off segs acc p cand).2.1
  | [], _, _, _, h1, h2 => ⟨h1, h2⟩
  | s :: segs, acc, p, cand, h1, h2 => by
    unfold skelGo
    by_cases hb : s.r0 < p ∨ sk.size < s.r1 ∨ s.r1 ≤ s.r0
    · rw [if_pos hb]; exact skelGo_rows one sk off segs acc p cand h1 h2
    · rw [if_neg hb]
      refine skelGo_rows one sk off segs _ _ _ (by omega) ?_
      have hblk : (blockRPC one cand ((List.range (s.r1 - s.r0)).map fun i => sk.getD (s.r0 + i) ⟨[], [], []⟩)
          (off + s.r0) s.c0 s.B).1.rows one = skRun sk off s.r0 s.r1 := by
        rw [blockRPC_rows, idxR_range]; rfl
      have hq : skRun sk off 0 p ++ skRun sk off p s.r0 ++ skRun sk off s.r0 s.r1 =
          skRun sk off 0 s.r1 := by
        rw [skRun_append sk off (Nat.zero_le _) (by omega),
          skRun_append sk off (Nat.zero_le _) (by omega)]
      by_cases hg : p < s.r0
      · simp only [hg, ite_true, List.reverse_cons, List.flatMap_append, h2, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, hblk, RP.rows_sp, ← hq, List.append_assoc]
      · have : skRun sk off p s.r0 = [] := by simp [skRun, show s.r0 - p = 0 by omega]
        simp only [hg, ite_false, List.reverse_cons, List.flatMap_append, h2, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, hblk, ← hq, this]

/-- **The skeleton's proto-pieces have the skeleton's rows**, for any blocks and known templates. -/
theorem skelRP_rows (one : Lin) (sk : Array Row) (off : ℕ) (segs : List Seg) (cand : Cands) :
    (skelRP one sk off segs cand).1.flatMap (RP.rows one) = idxR off sk.toList := by
  obtain ⟨h1, h2⟩ := skelGo_rows one sk off segs [] 0 cand (Nat.zero_le _) rfl
  simp only [skelRP, List.reverse_cons, List.flatMap_append, h2, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, RP.rows_sp]
  rw [skRun_append sk off (Nat.zero_le _) h1, skRun_all]

/-! ### Template instances -/

theorem idxR_map {α β : Type*} (Y : ℕ) (l : List α) (f : α → β) :
    idxR Y (l.map f) = l.zipIdx.map fun p => (Y + p.2, f p.1) := by
  simp only [idxR, List.zipIdx_map, List.map_map]; rfl

theorem mkKM_rows (k : TKey) : (mkKM k).rows = tRows k ∧ (mkKM k).rb = tRbits k := by
  have h := keyInfo_eq k
  unfold mkKM; split
  · simp [h]
  · dsimp only; split <;> simp [h]

theorem mkKM_split {k : TKey} {a b : ℕ} (hs : splitOf k = some (a, b)) :
    (mkKM k).hd = (tRows k).take (2 ^ a) ∧ (mkKM k).tl = (tRows k).drop (2 ^ a) := by
  have h := keyInfo_eq k
  unfold mkKM; rw [hs]; simp [h]

theorem mkKM_blks {k : TKey} {S : ℕ} (hs : splitOf k = none) (hb : blkSize k (tRbits k) = some S) :
    (mkKM k).blks = mkBlks S ((tRows k).length / S) 0 [] (tRows k) := by
  have h := keyInfo_eq k
  unfold mkKM; rw [hs]; dsimp only; rw [h]; dsimp only; rw [hb]

theorem mkBlks_length (S : ℕ) : ∀ (n c : ℕ) (reps : BReps) (l : List RowT),
    (mkBlks S n c reps l).length = n
  | 0, _, _, _ => rfl
  | n + 1, c, reps, l => by rw [mkBlks, List.length_cons, mkBlks_length S n]

/-- `b` extends `a` (sources). -/
def SExt (a b : Array (Option Src)) : Prop :=
  a.size = b.size ∧ ∀ (i : ℕ) (x : Src), a[i]? = some (some x) → b[i]? = some (some x)

theorem SExt.refl (a : Array (Option Src)) : SExt a a := ⟨rfl, fun _ _ h => h⟩
theorem SExt.trans {a b c : Array (Option Src)} (h1 : SExt a b) (h2 : SExt b c) : SExt a c :=
  ⟨h1.1.trans h2.1, fun i x h => h2.2 i x (h1.2 i x h)⟩

theorem matchTermT_spec (one : Lin) (ins : Array Lin) (cb w : ℕ) (srcs : Array (Option Src))
    (u t : Wire × F) (c' : Array (Option Src)) (h : matchTermT w srcs u t = some c') :
    SExt srcs c' ∧ ∀ fin : Array (Option Src), SExt c' fin →
      instT one ((fin.map fun o => o.getD (.inp 0)).toList.map (srcLin ins cb)) (cb + w) u =
        instT one ins.toList cb t := by
  obtain ⟨wu, a⟩ := u; obtain ⟨wt, b⟩ := t
  unfold matchTermT at h
  dsimp only at h
  by_cases ha : (a == b) = true
  swap; · rw [if_neg ha] at h; cases h
  rw [if_pos ha] at h
  have ha' : a = b := eq_of_beq ha
  subst ha'
  cases wu with
  | one =>
    simp only at h
    by_cases h1 : (wt == Wire.one) = true
    · rw [if_pos h1] at h; cases h; rw [eq_of_beq h1]; exact ⟨SExt.refl _, fun _ _ => rfl⟩
    · rw [if_neg h1] at h; cases h
  | loc k =>
    simp only at h
    by_cases h1 : (wt == Wire.loc (w + k)) = true
    swap; · rw [if_neg h1] at h; cases h
    rw [if_pos h1] at h
    cases h; rw [eq_of_beq h1]
    refine ⟨SExt.refl _, fun _ _ => ?_⟩
    simp only [instT, add_assoc]
  | inp j =>
    simp only at h
    have hget : ∀ (s : Src), srcOf wt = some s → ∀ fin : Array (Option Src), fin[j]? = some (some s) →
        instT one ((fin.map fun o => o.getD (.inp 0)).toList.map (srcLin ins cb)) (cb + w) (.inp j, a) =
          instT one ins.toList cb (wt, a) := fun s hs fin hf => by
      simp only [instT]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.toList_map, List.getElem?_map,
        Array.getElem?_toList, hf]
      cases wt with
      | one => cases hs
      | loc k' => cases hs; simp [srcLin, Lin.cell, Lin.smul]
      | inp i' => cases hs; simp [srcLin, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    split at h
    · rename_i s hs
      split at h
      · rename_i s' hs'
        split_ifs at h with he
        cases h
        exact ⟨SExt.refl _, fun fin hf => hget s hs fin (by rw [← eq_of_beq he]; exact hf.2 j s' hs')⟩
      · rename_i hn
        cases h
        have hj : j < srcs.size := by
          by_contra hc; rw [Array.getElem?_eq_none (by omega)] at hn; cases hn
        refine ⟨⟨by simp, fun i x hi => ?_⟩, fun fin hf => hget s hs fin (hf.2 j s (by
          simp [Array.getElem?_setIfInBounds, hj]))⟩
        by_cases hij : i = j
        · subst hij; rw [hn] at hi; cases hi
        · rw [Array.getElem?_setIfInBounds, if_neg (Ne.symm hij)]; exact hi
      · cases h
    · cases h

theorem matchLinT_spec (one : Lin) (ins : Array Lin) (cb w : ℕ) : ∀ (us ts : LinT)
    (srcs c' : Array (Option Src)), matchLinT w srcs us ts = some c' →
    SExt srcs c' ∧ ∀ fin : Array (Option Src), SExt c' fin →
      instLin one ((fin.map fun o => o.getD (.inp 0)).toList.map (srcLin ins cb)) (cb + w) us =
        instLin one ins.toList cb ts
  | [], [], _, _, h => by cases h; exact ⟨SExt.refl _, fun _ _ => rfl⟩
  | u :: us, t :: ts, srcs, c', h => by
    simp only [matchLinT, Option.bind_eq_some_iff] at h
    obtain ⟨c1, h1, h2⟩ := h
    obtain ⟨e1, f1⟩ := matchTermT_spec one ins cb w srcs u t c1 h1
    obtain ⟨e2, f2⟩ := matchLinT_spec one ins cb w us ts c1 c' h2
    refine ⟨e1.trans e2, fun fin hf => ?_⟩
    rw [instLin_cons, instLin_cons, f1 fin (e2.trans hf), f2 fin hf]
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

theorem matchRowsT_spec (one : Lin) (ins : Array Lin) (cb w : ℕ) : ∀ (T rows : List RowT)
    (srcs c' : Array (Option Src)), matchRowsT w srcs T rows = some c' →
    SExt srcs c' ∧ ∀ fin : Array (Option Src), SExt c' fin →
      T.map (instRow one ((fin.map fun o => o.getD (.inp 0)).toList.map (srcLin ins cb)) (cb + w)) =
        rows.map (instRow one ins.toList cb)
  | [], [], _, _, h => by cases h; exact ⟨SExt.refl _, fun _ _ => rfl⟩
  | r :: rs, row :: rows, srcs, c', h => by
    simp only [matchRowsT, Option.bind_eq_some_iff] at h
    obtain ⟨ca, ha, cb', hb, cc, hc, hr⟩ := h
    obtain ⟨ea, fa⟩ := matchLinT_spec one ins cb w _ _ _ _ ha
    obtain ⟨eb, fb⟩ := matchLinT_spec one ins cb w _ _ _ _ hb
    obtain ⟨ec, fc⟩ := matchLinT_spec one ins cb w _ _ _ _ hc
    obtain ⟨er, fr⟩ := matchRowsT_spec one ins cb w rs rows cc c' hr
    refine ⟨ea.trans (eb.trans (ec.trans er)), fun fin hf => ?_⟩
    rw [List.map_cons, List.map_cons, fr fin hf, instRow, instRow,
      fa fin (eb.trans (ec.trans (er.trans hf))), fb fin (ec.trans (er.trans hf)), fc fin (er.trans hf)]
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

theorem reMatch_inst (one : Lin) (ins : Array Lin) (cb : ℕ) {T : List RowT} {n w : ℕ}
    {rows : List RowT} {src : Array Src} (h : reMatch T n w rows = some src) :
    T.map (instRow one (src.map (srcLin ins cb)).toList (cb + w)) = rows.map (instRow one ins.toList cb) := by
  simp only [reMatch, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  rw [Array.toList_map]
  exact (matchRowsT_spec one ins cb w T rows _ s hs).2 s (SExt.refl _)

theorem tryBReps_spec (one : Lin) (ins : Array Lin) (cb w : ℕ) (rows : List RowT) :
    ∀ (rs : BReps) {T : List RowT} {h : UInt64} {src : Array Src}, tryBReps w rows rs = some (T, h, src) →
      T.map (instRow one (src.map (srcLin ins cb)).toList (cb + w)) = rows.map (instRow one ins.toList cb)
  | [], _, _, _, hc => by cases hc
  | (T', n, h') :: rs, T, h, src, hc => by
    unfold tryBReps at hc
    split at hc
    · rename_i src' hm; cases hc; exact reMatch_inst one ins cb hm
    · exact tryBReps_spec one ins cb w rows rs hc

theorem mkBlk_inst (one : Lin) (ins : Array Lin) (cb S c : ℕ) (reps : BReps) (rows : List RowT) :
    (mkBlk S c reps rows).1.T.map
        (instRow one ((mkBlk S c reps rows).1.src.map (srcLin ins cb)).toList (cb + S * c)) =
      rows.map (instRow one ins.toList cb) := by
  unfold mkBlk; split
  · rename_i T h src hc; exact tryBReps_spec one ins cb _ rows reps hc
  · exact reT_inst one ins cb (S * c) S rows

/-- **The blocks' proto-pieces have the instance's rows** (`n` blocks of `S` rows from block `c`,
then the rest). -/
theorem blk_rows (one : Lin) (ia : Array Lin) (cb X S : ℕ) :
    ∀ (n c : ℕ) (reps : BReps) (l : List RowT), n * S ≤ l.length →
    (blkRPs one ia cb X S c (mkBlks S n c reps l)).flatMap (RP.rows one) ++
        idxR (X + S * (c + n)) ((l.drop (S * n)).map (instRow one ia.toList cb)) =
      idxR (X + S * c) (l.map (instRow one ia.toList cb))
  | 0, c, _, l, _ => by simp [mkBlks, blkRPs]
  | n + 1, c, reps, l, hl => by
    have ih := blk_rows one ia cb X S n (c + 1) (mkBlk S c reps (l.take S)).2
      (l.drop S) (by rw [List.length_drop]; rw [Nat.succ_mul] at hl; omega)
    simp only [mkBlks, blkRPs, List.flatMap_cons, mkRaw_rows, instIR_eq, mkBlk_inst, List.append_assoc]
    rw [List.drop_drop, show S + S * n = S * (n + 1) by ring, show c + 1 + n = c + (n + 1) by ring] at ih
    rw [ih]
    have : (List.map (instRow one ia.toList cb) (List.take S l)).length = S := by
      rw [List.length_map, List.length_take]; rw [Nat.succ_mul] at hl; omega
    conv_rhs => rw [← List.take_append_drop S l]
    rw [List.map_append, idxR_append, this, show X + S * c + S = X + S * (c + 1) by ring]

theorem splitRow_lo (a b i : ℕ) {j : ℕ} (hj : j < 2 ^ a) :
    splitRow a b i j = splitRow a b i 0 + j := by
  unfold splitRow; simp only [hj, ite_true, Nat.pos_of_ne_zero (NeZero.ne (2 ^ a))]; omega

theorem splitRow_hi (a b i j : ℕ) : splitRow a b i (2 ^ a + j) = splitRow a b i (2 ^ a) + j := by
  unfold splitRow; simp only [show ¬ 2 ^ a + j < 2 ^ a by omega, lt_irrefl, ite_false]; omega

theorem split_rows {α β : Type*} (R : List α) (f : α → β) (g : ℕ → ℕ) (n Y Z : ℕ)
    (hlo : ∀ j < n, g j = Y + j) (hhi : ∀ j, g (n + j) = Z + j) :
    R.zipIdx.map (fun p => (g p.2, f p.1)) = idxR Y ((R.take n).map f) ++ idxR Z ((R.drop n).map f) := by
  rw [idxR_map, idxR_map]
  conv_lhs => rw [← List.take_append_drop n R]
  rw [List.zipIdx_append, List.map_append]
  congr 1
  · refine List.map_congr_left fun p hp => ?_
    have := (List.mem_zipIdx hp).2.1; simp only [zero_add, List.length_take] at this
    rw [hlo _ (by omega)]
  · by_cases hn : n ≤ R.length
    · rw [List.zipIdx_eq_map_add, List.map_map]
      refine List.map_congr_left fun p _ => ?_
      simp only [Function.comp_apply, zero_add, List.length_take, Nat.min_eq_left hn]
      rw [hhi]
    · rw [List.drop_eq_nil_of_le (by omega)]; rfl

/-- **A template instance's proto-pieces have its rows.** -/
theorem tinRP_rows (one : Lin) (ks : List TKey) (L : TLay) (off : ℕ) (t : TKey × ℕ × List Lin) :
    (tinRP one (ks.map mkKM) L off t).flatMap (RP.rows one) = tinIRows L one off t := by
  obtain ⟨hr, hrb⟩ := mkKM_rows t.1
  have hA : ∀ r, instRowA one t.2.2.toArray (L.cb t.1 t.2.1) r = instRow one t.2.2 (L.cb t.1 t.2.1) r :=
    instRowA_eq one t.2.2 _
  unfold tinRP tinIRows
  simp only [kmOf_map, hA]
  cases hs : splitOf t.1 with
  | some ab =>
    obtain ⟨a, b⟩ := ab
    obtain ⟨hh, ht⟩ := mkKM_split hs
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, mkRaw_rows, instIR_eq, hh, ht,
      List.toList_toArray]
    rw [split_rows (tRows t.1) (instRow one t.2.2 (L.cb t.1 t.2.1))
      (fun j => off + L.rb t.1 + splitRow a b t.2.1 j) (2 ^ a)
      (off + L.rb t.1 + splitRow a b t.2.1 0) (off + L.rb t.1 + splitRow a b t.2.1 (2 ^ a))
      (fun j hj => by simp only [splitRow_lo a b t.2.1 hj]; ring)
      (fun j => by simp only [splitRow_hi]; ring)]
  | none =>
    simp only [hrb]
    cases hb : blkSize t.1 (tRbits t.1) with
    | some S =>
      simp only [mkKM_blks hs hb, mkBlks_length, hr, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, RP.rows_sp, instIR_eq, List.toList_toArray]
      have := blk_rows one t.2.2.toArray (L.cb t.1 t.2.1) (off + L.rb t.1 + t.2.1 * 2 ^ tRbits t.1) S
        ((tRows t.1).length / S) 0 [] (tRows t.1) (Nat.div_mul_le_self _ _)
      simp only [List.toList_toArray, zero_add, mul_zero, add_zero] at this
      rw [this, idxR_map]
    | none =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, mkRaw_rows, instIR, hr,
        List.toList_toArray]

/-- **A slot's proto-pieces have the slot's rows.** -/
theorem slotRP_rows (one : Lin) (ks : List TKey) (L : TLay) (off : ℕ) (cs : CS) (segs : List Seg)
    (cand : Cands) :
    (slotRP one (ks.map mkKM) L off cs segs cand).1.toList.flatMap (RP.rows one) = slotIRows L one off cs := by
  simp only [slotRP, List.toList_toArray, List.flatMap_append, skelRP_rows, List.flatMap_assoc,
    tinRP_rows, slotIRows, idxR]

/-! ### The piece check -/

theorem getD_toList {α : Type*} (a : Array α) (i : ℕ) (d : α) : a.toList.getD i d = a.getD i d := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- Under the input check, a key's rewritten term reads what the instance's term reads. -/
theorem rw_instT (ks : Array IK) (n : ℕ) (inp ins : Array Lin) (cb : ℕ) (one : Lin)
    (hok : insOk ks n inp ins cb = true) (t : Wire × F) (ht : ∀ i, t.1 = .inp i → i < n) :
    instT one inp.toList cb (rwWire (kindWire ks) t.1, t.2) = instT one ins.toList cb t := by
  obtain ⟨w, a⟩ := t
  cases w with
  | one => rfl
  | loc k => rfl
  | inp i =>
    have hi := List.all_eq_true.1 hok i (List.mem_range.2 (ht i rfl))
    simp only [rwWire, instT, getD_toList]
    revert hi
    cases kindWire ks i with
    | loc c => intro hi; simp only [instT]; rw [eq_of_beq hi, cell_smul]
    | inp j => intro hi; simp only [instT, getD_toList]; rw [eq_of_beq hi]
    | one => intro hi; cases hi

theorem rw_instLin (ks : Array IK) (n : ℕ) (inp ins : Array Lin) (cb : ℕ) (one : Lin)
    (hok : insOk ks n inp ins cb = true) :
    ∀ l : LinT, (∀ t ∈ l, ∀ i, t.1 = .inp i → i < n) →
      instLin one inp.toList cb (rwLin (kindWire ks) l) = instLin one ins.toList cb l
  | [], _ => rfl
  | t :: l, h => by
    simp only [rwLin, List.map_cons] at *
    rw [instLin_cons, instLin_cons, rw_instT ks n inp ins cb one hok t (h t (List.mem_cons_self ..)),
      ← rwLin, rw_instLin ks n inp ins cb one hok l fun t' ht' => h t' (List.mem_cons_of_mem _ ht')]

theorem getD_mapK (G : Array GK) (k : ℕ) : (G.map mkKey).getD k dkey = mkKey (G.getD k dGK) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases G[k]? <;> rfl

/-- **A piece has its proto-piece's rows**, whatever the grouping proposed. -/
theorem toPiece_rows (G : Array GK) (sh : Array (List Lin)) (one : Lin) (rp : RP) (k : ℕ)
    (own : List Lin) : (toPiece G sh one rp k own).rows (G.map mkKey) sh one = rp.rows one := by
  cases rp with
  | sp rs => rfl
  | raw T ins X cb A B h =>
    dsimp only [toPiece]
    split_ifs with hc
    · simp only [Bool.and_eq_true, beq_iff_eq, withPtrEq] at hc
      obtain ⟨⟨⟨⟨⟨hA, hB⟩, hX⟩, hcb⟩, hT⟩, hok⟩ := hc
      subst hT
      simp only [Piece.rows, getD_mapK, mkKey, hA, hB, RP.rows,
        Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hX), Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hcb),
        instIR_eq, List.map_map]
      congr 1
      refine List.map_congr_left fun r hr => ?_
      have hn := (G.getD k dGK).hn r hr
      have hok' := hok
      rw [← @List.toList_toArray _ (sh.getD k [] ++ own)]
      simp only [Function.comp_apply, rwRow, instRow]
      rw [rw_instLin _ _ _ _ _ _ hok' _ fun t ht => hn t (by simp [ht]),
        rw_instLin _ _ _ _ _ _ hok' _ fun t ht => hn t (by simp [ht]),
        rw_instLin _ _ _ _ _ _ hok' _ fun t ht => hn t (by simp [ht])]
    · rfl

/-- **A slot's pieces have its proto-pieces' rows.** -/
theorem piecesOf_rows (G : Array GK) (sh : Array (List Lin)) (one : Lin) (rps : Array RP)
    (pr : Array (Option (ℕ × List Lin))) :
    (piecesOf G sh one rps pr).flatMap (Piece.rows (G.map mkKey) sh one) =
      rps.toList.flatMap (RP.rows one) := by
  have he : ∀ (rp : RP) (o : Option (ℕ × List Lin)),
      (match o with
        | some (k, own) => toPiece G sh one rp k own
        | none => match rp with
          | .sp rs => .sp rs
          | .raw T ins X cb _ _ _ => .sp (instIR T one ins.toList X cb)).rows (G.map mkKey) sh one =
        rp.rows one := fun rp o => by
    rcases o with _ | ⟨k, own⟩
    · cases rp <;> rfl
    · exact toPiece_rows G sh one rp k own
  have hl : (List.range rps.size).map (fun i => rps.getD i (.sp [])) = rps.toList :=
    List.ext_getElem (by simp) fun i h₁ h₂ => by
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using h₁)]; rfl
  rw [← hl, List.flatMap_map]
  simp only [piecesOf, List.flatMap_map, he]

/-! ## Controls -/

/-- (+) The input check accepts an input that is the local's cell. -/
theorem insOk_pos : insOk #[IK.loc 0, IK.own 0] 2 #[[(7, 1)]] #[[(4, 1)], [(7, 1)]] 4 = true := by
  decide

/-- (−) It refuses an input that is another cell than the local's. -/
theorem insOk_neg : insOk #[IK.loc 0] 1 #[] #[[(5, 1)]] 4 = false := by decide

/-- (−) It refuses an own input whose form differs from the instance's. -/
theorem insOk_neg_own : insOk #[IK.own 0] 1 #[[(8, 1)]] #[[(7, 1)]] 0 = false := by decide

/-- The one-row key and template of the piece controls: `a = loc 0`, `b = inp 0`, `c = []`. -/
def ctlT : List RowT := [⟨[(.loc 0, 1)], [(.inp 0, 1)], []⟩]

/-- (+) A proposal whose template and inputs check becomes an instance. -/
theorem toPiece_pos : (toPiece #[mkGK ctlT #[IK.own 0] 0 0] #[[]] [] (.raw ctlT #[[(9, 1)]] 0 0 0 0 0) 0
    [[(9, 1)]]) matches .ins .. := by decide

/-- (−) A proposal with another template is refused: the proto-piece's rows are kept. -/
theorem toPiece_neg : (toPiece #[mkGK [] #[IK.own 0] 0 0] #[[]] [] (.raw ctlT #[[(9, 1)]] 0 0 0 0 0) 0
    [[(9, 1)]]) matches .sp .. := by decide

/-- (−) A proposal with a wrong own input is refused. -/
theorem toPiece_neg_own : (toPiece #[mkGK ctlT #[IK.own 0] 0 0] #[[]] [] (.raw ctlT #[[(9, 1)]] 0 0 0 0 0) 0
    [[(8, 1)]]) matches .sp .. := by decide

/-- (+) `maxInp` bounds the inputs; (−) locals do not count. -/
theorem maxInp_ctl : maxInp [⟨[(.inp 3, 1)], [(.loc 9, 1)], []⟩] = 4 ∧
    maxInp [⟨[(.loc 7, 1)], [], []⟩] = 0 := by decide

/-- (+) A block that is an instance of a template matches it (its input cell recorded);
(−) one whose local is another cell does not. -/
theorem absMatch_ctl : absMatch ctlT 1 10 [⟨[(10, 1)], [(3, 1)], []⟩] = some #[[(3, 1)]] ∧
    absMatch ctlT 1 10 [⟨[(11, 1)], [(3, 1)], []⟩] = none := by decide +kernel


/-- (+) A template block matches a known one (a local outside the window becomes a source);
(−) a block reading another local does not. -/
theorem reMatch_ctl : reMatch ctlT 1 4 [⟨[(.loc 4, 1)], [(.loc 1, 1)], []⟩] = some #[.loc 1] ∧
    reMatch ctlT 1 4 [⟨[(.loc 5, 1)], [(.loc 1, 1)], []⟩] = none := by decide +kernel

end TEval
end FR
