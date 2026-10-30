-- G6: this module also holds the former modules `FRVIRTplBuild` (one section each, in import order).
import FRVIRTplRun

section G6_FRVIRTplBuild

-- New for `flock-recursive` (BLUEPRINT §4.4's plan text, B-16: the plan ≤ 2 s per process; stage
-- S-E13, track L-circ).

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
    -- the op's key first (with empty templates: cheap), so that its template is built once
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P cs' op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P cs' op
    let M := memoAdd M o.tin
    let cs2 := cs'.add op o
    match op, cur with
    | .assertEq .., some (r0, c0, b) => compMSX X L P M cs2 ops none (cutBlock r0 cs2.nrows c0 b acc)
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
    let rb := alignUp r0 (match splitOfN k nr with
      | some (a, _) => a
      | none => if isWalk k then gBits else if 12 < rbk then 6 else rbk)
    let cb := alignUp c0 (if isWalk k then gBits else cr)
    let re := match splitOfN k nr with
      | some (a, b) => rb + splitEnd a b n
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

/-- The block size of an unsplit key cut into blocks (`tinPP`'s): the walk's `2^gBits`, a template
of more than `2^12` rows `64`, otherwise none (B0: it no longer reads `splitOf`, which every caller
consults first, so that an instance does not rebuild its template's rows). -/
def blkSize (k : TKey) (rb : ℕ) : Option ℕ :=
  if isWalk k then some (2 ^ gBits) else if 12 < rb then some 64 else none

/-- A wire with its local moved by `d` (B2″: a packed window's member). -/
def shW (d : ℕ) : Wire → Wire
  | .loc k => .loc (d + k)
  | w => w

/-- Template rows with their locals moved by `d`. -/
def shRows (d : ℕ) (T : List RowT) : List RowT :=
  T.map fun r => ⟨r.a.map (fun t => (shW d t.1, t.2)), r.b.map (fun t => (shW d t.1, t.2)),
    r.c.map (fun t => (shW d t.1, t.2))⟩

/-- **A packed key's members** (B2″): its cell field `f` (`w + 64·g`) and, per member `j < g`, its
rows (a split key's head) and its tail with their locals moved by `j·cS f`, with their hashes (built
once per key, so that a member's instances share one object: `toPiece`'s `withPtrEq`). -/
structure PK where
  f : ℕ
  a : Array (List RowT × UInt64)
  b : Array (List RowT × UInt64)

/-- The members of `T` for the cell field `f`. -/
def mkPK (f : ℕ) (T : List RowT) : Array (List RowT × UInt64) :=
  (Array.range (cG f)).map fun j => let S := shRows (j * cS f) T; (S, hash S)

/-- A key's members under the packing policy (`packOfN`), for rows `A` and tail `B`. -/
def pkOf (k : TKey) (cr u : ℕ) (A B : List RowT) : Option PK :=
  (packOfN k cr u).map fun p => ⟨p.1 + 64 * p.2, mkPK (p.1 + 64 * p.2) A, mkPK (p.1 + 64 * p.2) B⟩

/-- **A key's data**: its template's rows, row bits, cell region, locals, and (for a split key) its
head and tail, (for a blocked key) its re-templated blocks, (for a packed key) its members; the
hashes only group. -/
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
  /-- Its split (`splitOf k`, computed once with the key: B0). -/
  sp : Option (ℕ × ℕ)
  /-- A split key's head and tail inputs (`rowsInps`; `hd`/`tl` are renumbered by them: B0). -/
  hdI : List ℕ
  tlI : List ℕ
  /-- Its members, if packed (B2″). -/
  pk : Option PK

/-- The inputs template rows read, without repeats (B0: a split key's head and tail each carry
only theirs, so that a half's own inputs are not the whole instance's). -/
def rowsInps (T : List RowT) : List ℕ :=
  (T.flatMap fun r => r.a ++ r.b ++ r.c).filterMap (fun t => match t.1 with
    | .inp i => some i
    | _ => none) |>.dedup

/-- A wire with its input renumbered by its place in `ix`. -/
def renW (ix : List ℕ) : Wire → Wire
  | .inp i => .inp (ix.idxOf i)
  | w => w

/-- Template rows with their inputs renumbered by `ix`. -/
def renRows (ix : List ℕ) (T : List RowT) : List RowT :=
  T.map fun r => ⟨r.a.map (fun t => (renW ix t.1, t.2)), r.b.map (fun t => (renW ix t.1, t.2)),
    r.c.map (fun t => (renW ix t.1, t.2))⟩

/-- The inputs `ix` of an instance (input forms `ins`). -/
def insOf (ix : List ℕ) (ins : List Lin) : List Lin := ix.map fun i => ins.getD i []

theorem instLin_ren (one : Lin) (ins : List Lin) (cb : ℕ) (ix : List ℕ) (l : LinT)
    (h : ∀ t ∈ l, ∀ i, t.1 = .inp i → i ∈ ix) :
    instLin one (insOf ix ins) cb (l.map fun t => (renW ix t.1, t.2)) = instLin one ins cb l := by
  unfold instLin
  rw [List.flatMap_map]
  refine List.flatMap_congr fun t ht => ?_
  obtain ⟨w, c⟩ := t
  cases w with
  | inp i =>
    have hi := h _ ht i rfl
    simp only [renW, insOf, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hi), List.getElem_idxOf, Option.map_some,
      Option.getD_some]
  | one => rfl
  | loc k => rfl

/-- **Renumbered rows instantiate to the same rows** with the inputs they read. -/
theorem ren_rows (one : Lin) (ins : List Lin) (cb : ℕ) (T : List RowT) :
    (renRows (rowsInps T) T).map (instRow one (insOf (rowsInps T) ins) cb) = T.map (instRow one ins cb) := by
  unfold renRows
  rw [List.map_map]
  refine List.map_congr_left fun r hr => ?_
  have hm : ∀ l, (l = r.a ∨ l = r.b ∨ l = r.c) → ∀ t ∈ l, ∀ i, t.1 = .inp i → i ∈ rowsInps T := by
    rintro l hl t ht i hi
    unfold rowsInps
    rw [List.mem_dedup, List.mem_filterMap]
    refine ⟨t, List.mem_flatMap.2 ⟨r, hr, ?_⟩, by rw [hi]⟩
    rcases hl with rfl | rfl | rfl <;> simp [ht]
  simp only [Function.comp_apply, instRow,
    instLin_ren one ins cb _ r.a (hm _ (Or.inl rfl)), instLin_ren one ins cb _ r.b (hm _ (Or.inr (Or.inl rfl))),
    instLin_ren one ins cb _ r.c (hm _ (Or.inr (Or.inr rfl)))]

/-- (+) A row reading inputs 5 and 2 is renumbered to 0 and 1; (−) a local stays a local. -/
theorem renRows_ctl :
    rowsInps [⟨[(.inp 5, 1)], [(.loc 3, 1), (.inp 2, 1)], [(.inp 5, 1)]⟩] = [2, 5] ∧
      renRows [5, 2] [⟨[(.inp 5, 1)], [(.loc 3, 1), (.inp 2, 1)], []⟩] =
        [⟨[(.inp 0, 1)], [(.loc 3, 1), (.inp 1, 1)], []⟩] := by
  constructor <;> decide

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
  let u := usedN k rows ki.2.2.2
  match splitOfN k rows.length with
  | some (a, b) =>
    let hd0 := rows.take (2 ^ a); let tl0 := rows.drop (2 ^ a)
    let hi := rowsInps hd0; let ti := rowsInps tl0
    let hd := renRows hi hd0; let tl := renRows ti tl0
    ⟨k, rows, rb, ki.2.2.1, ki.2.2.2, 0, hd, tl, hash hd, hash tl, [], some (a, b), hi, ti,
      pkOf k ki.2.2.1 u hd tl⟩
  | none =>
    match blkSize k rb with
    | some S => ⟨k, rows, rb, ki.2.2.1, ki.2.2.2, 0, [], [], 0, 0, mkBlks S (rows.length / S) 0 [] rows, none,
        [], [], none⟩
    | none => ⟨k, rows, rb, ki.2.2.1, ki.2.2.2, hash rows, [], [], 0, 0, [], none, [], [],
        pkOf k ki.2.2.1 u rows []⟩

/-- A key's data from a memo (computed for a key it lacks). -/
def kmOf (Ms : List KM) (k : TKey) : KM :=
  match Ms.find? (·.k == k) with
  | some e => e
  | none => mkKM k

theorem mkKM_k (k : TKey) : (mkKM k).k = k := by
  unfold mkKM; dsimp only; split
  · rfl
  · split <;> rfl

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

/-- `instIR` with the inputs in an array (constant-time lookups; `instIRA_eq`; INIT: the
unaligned tails' rows at plan init). -/
def instIRA (T : List RowT) (one : Lin) (ins : Array Lin) (X cb : ℕ) : List (ℕ × Row) :=
  T.zipIdx.map fun p => (X + p.2, instRowA one ins cb p.1)

theorem instIRA_eq (T : List RowT) (one : Lin) (ins : List Lin) (X cb : ℕ) :
    instIRA T one ins.toArray X cb = instIR T one ins X cb := by
  simp only [instIRA, instIR, instRowA_eq]

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

/-- A key's members if the layout packs it as the key's data does (else the instance is laid out
as unpacked, or the layout is stale: `tinRPu`). -/
def pkSel (e : KM) (f : ℕ) : Option PK :=
  match e.pk with
  | some P => if P.f == f then some P else none
  | none => none

/-- **A packed instance's proto-pieces** (B2″): as `tinRPu`'s, each over its member's rows at its
window's base `L.gb` with the window's bits (so that the members' instances are keys). -/
def tinRPp (one : Lin) (e : KM) (P : PK) (L : TLay) (off : ℕ) (t : TKey × ℕ × List Lin) : List RP :=
  let j := t.2.1 % cG P.f
  let gb := L.gb t.1 t.2.1
  let bb := L.bits t.1
  let ma := P.a.getD j ([], 0)
  match e.sp with
  | some (a, b) =>
    let X0 := off + L.rb t.1
    let mb := P.b.getD j ([], 0)
    [mkRaw one ma.1 (insOf e.hdI t.2.2).toArray (X0 + splitRow a b t.2.1 0) gb a bb ma.2,
     mkRaw one mb.1 (insOf e.tlI t.2.2).toArray (X0 + splitRow a b t.2.1 (2 ^ a)) gb b bb mb.2]
  | none => [mkRaw one ma.1 t.2.2.toArray (off + L.rb t.1 + t.2.1 * 2 ^ e.rb) gb e.rb bb ma.2]

/-- **A template instance's proto-pieces** (`tinPP`'s cut): split keys their head and tail, blocked
keys their blocks and the rest sparse, other keys the whole instance. -/
def tinRPu (one : Lin) (Ms : List KM) (L : TLay) (off : ℕ) (t : TKey × ℕ × List Lin) : List RP :=
  let e := kmOf Ms t.1
  let ia := t.2.2.toArray
  let cb := L.cb t.1 t.2.1
  let bb := L.bits t.1
  match e.sp with
  | some (a, b) =>
    let X0 := off + L.rb t.1
    [mkRaw one e.hd (insOf e.hdI t.2.2).toArray (X0 + splitRow a b t.2.1 0) cb a bb e.hh,
     mkRaw one e.tl (insOf e.tlI t.2.2).toArray (X0 + splitRow a b t.2.1 (2 ^ a)) cb b bb e.ht]
  | none =>
    let X := off + L.rb t.1 + t.2.1 * 2 ^ e.rb
    match blkSize t.1 e.rb with
    | some S =>
      blkRPs one ia cb X S 0 e.blks ++
      [RP.sp (instIRA (e.rows.drop (S * e.blks.length)) one ia (X + S * e.blks.length) cb)]
    | none => [mkRaw one e.rows ia X cb e.rb bb e.h]

/-- **A template instance's proto-pieces**: a packed key's as its member's (`tinRPp`), any other's
as `tinRPu`. -/
def tinRP (one : Lin) (Ms : List KM) (L : TLay) (off : ℕ) (t : TKey × ℕ × List Lin) : List RP :=
  let e := kmOf Ms t.1
  match pkSel e (L.cf t.1) with
  | some P => if (e.sp.isNone && (blkSize t.1 e.rb).isSome) then tinRPu one Ms L off t
      else tinRPp one e P L off t
  | none => tinRPu one Ms L off t

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
  -- the shared inputs accumulate reversed, with their count (INIT: `q ++ [_]` and `length` per input
  -- were quadratic in a group's inputs); the result is the same
  let r := (List.range n).foldl (fun (q : Array IK × List (ℕ × List Lin × List Lin) × ℕ × ℕ) i =>
    let lc := match mem[0]? with
      | some p0 => match offIn p0.2.cb (2 ^ p0.2.B) (p0.2.ins.getD i []) with
        | some c => if mem.all (fun p => offIn p.2.cb (2 ^ p.2.B) (p.2.ins.getD i []) == some c) then some c
          else none
        | none => none
      | none => none
    match lc with
    | some c => (q.1.push (IK.loc c), q.2.1, q.2.2.1, q.2.2.2)
    | none =>
      match (if part then distinctIn mem 0 i else none), distinctIn mem 1 i with
      | some d0, some d1 =>
        if (d0.length ≤ 1 && d1.length ≤ 1) || (4 * d0.length ≤ n0 && 4 * d1.length ≤ n1) then
          (q.1.push (IK.sh q.2.2.2), (i, d0, d1) :: q.2.1, q.2.2.1, q.2.2.2 + 1)
        else (q.1.push (IK.own q.2.2.1), q.2.1, q.2.2.1 + 1, q.2.2.2)
      | _, _ => (q.1.push (IK.own q.2.2.1), q.2.1, q.2.2.1 + 1, q.2.2.2)) ((#[] : Array IK), [], 0, 0)
  (r.1.map fun k => match k with
    | .own i => IK.own (r.2.2.2 + i)
    | k => k, r.2.1.reverse)

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
  unfold mkKM; dsimp only; split
  · simp [h]
  · split <;> simp [h]

/-- `mkKM`'s split is `splitOf`, from the rows it built once. -/
theorem keyInfo_split (k : TKey) : splitOfN k (keyInfo k).1.length = splitOf k := by
  rw [keyInfo_eq]; rfl

theorem mkKM_sp (k : TKey) : (mkKM k).sp = splitOf k := by
  rw [← keyInfo_split k]; unfold mkKM; dsimp only; split
  · rename_i h; exact h.symm
  · rename_i h; split <;> exact h.symm

theorem mkKM_split {k : TKey} {a b : ℕ} (hs : splitOf k = some (a, b)) :
    (mkKM k).hd = renRows (rowsInps ((tRows k).take (2 ^ a))) ((tRows k).take (2 ^ a)) ∧
      (mkKM k).tl = renRows (rowsInps ((tRows k).drop (2 ^ a))) ((tRows k).drop (2 ^ a)) ∧
      (mkKM k).hdI = rowsInps ((tRows k).take (2 ^ a)) ∧ (mkKM k).tlI = rowsInps ((tRows k).drop (2 ^ a)) := by
  have h := keyInfo_eq k
  rw [← keyInfo_split k] at hs
  unfold mkKM; dsimp only; rw [hs]; simp [h]

theorem mkKM_blks {k : TKey} {S : ℕ} (hs : splitOf k = none) (hb : blkSize k (tRbits k) = some S) :
    (mkKM k).blks = mkBlks S ((tRows k).length / S) 0 [] (tRows k) := by
  have h := keyInfo_eq k
  rw [← keyInfo_split k] at hs
  unfold mkKM; dsimp only; rw [hs]; dsimp only; rw [h]; dsimp only; rw [hb]

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

/-- An unpacked instance's proto-pieces have its rows. -/
theorem tinRPu_rows (one : Lin) (ks : List TKey) (L : TLay) (off : ℕ) (t : TKey × ℕ × List Lin) :
    (tinRPu one (ks.map mkKM) L off t).flatMap (RP.rows one) = tinIRows L one off t := by
  obtain ⟨hr, hrb⟩ := mkKM_rows t.1
  have hA : ∀ r, instRowA one t.2.2.toArray (L.cb t.1 t.2.1) r = instRow one t.2.2 (L.cb t.1 t.2.1) r :=
    instRowA_eq one t.2.2 _
  unfold tinRPu tinIRows
  simp only [kmOf_map, hA, mkKM_sp, instIRA_eq]
  cases hs : splitOf t.1 with
  | some ab =>
    obtain ⟨a, b⟩ := ab
    obtain ⟨hh, ht, hhI, htI⟩ := mkKM_split hs
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, mkRaw_rows, instIR_eq, hh, ht,
      hhI, htI, List.toList_toArray, ren_rows]
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

/-- **Moved locals instantiate at the moved cell base.** -/
theorem shRows_inst (one : Lin) (ins : List Lin) (cb d : ℕ) (T : List RowT) :
    (shRows d T).map (instRow one ins cb) = T.map (instRow one ins (cb + d)) := by
  have hl : ∀ l : LinT, instLin one ins cb (l.map fun t => (shW d t.1, t.2)) = instLin one ins (cb + d) l := by
    intro l
    unfold instLin
    rw [List.flatMap_map]
    refine List.flatMap_congr fun t _ => ?_
    obtain ⟨w, c⟩ := t
    cases w <;> simp [shW, add_assoc]
  simp only [shRows, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, instRow, hl]

theorem mkPK_get (f : ℕ) (T : List RowT) {j : ℕ} (hj : j < cG f) :
    ((mkPK f T).getD j ([], 0)).1 = shRows (j * cS f) T := by
  simp [mkPK, Array.getD_eq_getD_getElem?, hj]

theorem pkOf_get {k : TKey} {cr u : ℕ} {A B : List RowT} {P : PK} (h : pkOf k cr u A B = some P)
    {j : ℕ} (hj : j < cG P.f) :
    (P.a.getD j ([], 0)).1 = shRows (j * cS P.f) A ∧ (P.b.getD j ([], 0)).1 = shRows (j * cS P.f) B := by
  unfold pkOf at h
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨mkPK_get _ _ hj, mkPK_get _ _ hj⟩

/-- A key's members are its rows' (a split key's head's) and its tail's, moved. -/
theorem mkKM_pk {k : TKey} {P : PK} (h : (mkKM k).pk = some P) :
    ∃ cr u, pkOf k cr u (match (mkKM k).sp with
      | some _ => (mkKM k).hd
      | none => (mkKM k).rows) (mkKM k).tl = some P := by
  revert h; unfold mkKM; dsimp only; split
  · exact fun h => ⟨_, _, h⟩
  · split
    · intro h; cases h
    · exact fun h => ⟨_, _, h⟩

theorem TLay.cb_eq (L : TLay) (k : TKey) (i : ℕ) : L.cb k i = L.gb k i + i % cG (L.cf k) * cS (L.cf k) := by
  unfold TLay.cb TLay.mo TLay.cf
  cases List.find? (fun x => x.1 == k) L <;> simp [cG, Nat.mod_one]

theorem pkSel_spec {e : KM} {f : ℕ} {P : PK} (h : pkSel e f = some P) : e.pk = some P ∧ P.f = f := by
  unfold pkSel at h; split at h
  · split_ifs at h with hf; cases h; exact ⟨by assumption, eq_of_beq hf⟩
  · cases h

/-- A packed instance's proto-pieces have its unpacked proto-pieces' rows. -/
theorem tinRPp_rows (one : Lin) (ks : List TKey) (L : TLay) (off : ℕ) (t : TKey × ℕ × List Lin) {P : PK}
    (hP : pkSel (mkKM t.1) (L.cf t.1) = some P)
    (hg : ¬ ((mkKM t.1).sp.isNone && (blkSize t.1 (mkKM t.1).rb).isSome) = true) :
    (tinRPp one (mkKM t.1) P L off t).flatMap (RP.rows one) =
      (tinRPu one (ks.map mkKM) L off t).flatMap (RP.rows one) := by
  obtain ⟨hpk, hf⟩ := pkSel_spec hP
  obtain ⟨cr, u, hc⟩ := mkKM_pk hpk
  have hj : t.2.1 % cG P.f < cG P.f := Nat.mod_lt _ (by unfold cG; omega)
  have hcb := TLay.cb_eq L t.1 t.2.1
  rw [← hf] at hcb
  unfold tinRPp tinRPu
  simp only [kmOf_map]
  cases hs : (mkKM t.1).sp with
  | some ab =>
    obtain ⟨a, b⟩ := ab
    simp only [hs] at hc
    obtain ⟨ha, hb⟩ := pkOf_get hc hj
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, mkRaw_rows, instIR_eq, ha, hb,
      shRows_inst, hcb]
  | none =>
    simp only [hs] at hc hg
    obtain ⟨ha, -⟩ := pkOf_get hc hj
    have hbk : blkSize t.1 (mkKM t.1).rb = none := by
      revert hg; cases blkSize t.1 (mkKM t.1).rb <;> simp
    simp only [hbk, List.flatMap_cons, List.flatMap_nil, List.append_nil, mkRaw_rows, instIR_eq, ha,
      shRows_inst, hcb]

/-- **A template instance's proto-pieces have its rows.** -/
theorem tinRP_rows (one : Lin) (ks : List TKey) (L : TLay) (off : ℕ) (t : TKey × ℕ × List Lin) :
    (tinRP one (ks.map mkKM) L off t).flatMap (RP.rows one) = tinIRows L one off t := by
  rw [← tinRPu_rows one ks L off t]
  unfold tinRP
  simp only [kmOf_map]
  split
  · rename_i P hP
    split_ifs with hg
    · rfl
    · exact tinRPp_rows one ks L off t hP hg
  · rfl

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

end G6_FRVIRTplBuild

section G6_FRVIRTplFast

-- New for `flock-recursive` (BLUEPRINT §10 changes 17, revision 3.12 item 3; stage S-E4, track
-- L-circ). The node section (`Plan`, `planOf`, `nodeIRows`, `evalMT`, `evalMKT`) moved here from
-- `FRVIRTplEval` (S-E3); `evalMT` is now the flat evaluation. S-E11: the first half is
-- `FRVIRTplGrp`; the run class and the fast key preparation are `FRVIRTplRun`. S-E13: `planOf` is
-- built from `FRVIRTplBuild`'s proved pieces (no run-time row comparison), slot 1's layout is
-- slot 0's shifted when it fits.

namespace FR
namespace TEval
open Circ Tpl

/-- A prepared piece: grouped sparse rows, or an instance with its prepared own inputs. -/
inductive PPc where
  | sp (g : GRows)
  | ins (k xh ch : ℕ) (own : List OwnP)

/-- A row with some entry (the alignment's padding rows have none). -/
def nonEmpty (p : ℕ × Row) : Bool := !(p.2.a.isEmpty && p.2.b.isEmpty && p.2.c.isEmpty)

/-- A piece, prepared (`pats`: the run patterns per key, `FRVIRTplRun`). -/
def prepPiece (pats : Array (Array Pat)) : Piece → PPc
  | .sp rs => .sp (grows 2048 4096 (rs.filter nonEmpty))
  | .ins k xh ch own =>
    .ins k xh ch (prepOwn (pats.getD k #[]) (List.range (pats.getD k #[]).size) 0 own)

/-- **The tables of an evaluation point** (computed once, shared by the matrices and slots): `eq(τ,
·)` over `n` coordinates and `eq(σ, ·)` over 23, split at `2^11` and `2^12`, the per-key low tables,
and `E(one)`. -/
structure Tb where
  tlo : Array F
  thi : Array F
  slo : Array F
  shi : Array F
  nt : Array Bool
  ns : Array Bool
  ttab : Array (Array F)
  stab : Array (Array F)
  e1 : F
  /-- The keys' low tables `eq(τ_{<A}, ·)`, `eq(σ_{<B}, ·)` (S-E11), with their bits. -/
  lt : Array Bool
  lu : Array Bool
  pt : Array (Array F)
  pu : Array (Array F)

/-- The tables (`nt`, `ns`: the row and cell bits some key or run has; `lt`, `lu`: the low tables'
bits). -/
def tbOf (n : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) : Tb :=
  let slo := loTab 12 u; let shi := loTab 11 fun l => u (12 + l)
  ⟨loTab 11 t, loTab (n - 11) fun l => t (11 + l), slo, shi, nt, ns, hiTabs t 11 nt, hiTabs u 12 ns,
    glVal slo shi (grp 4096 one), lt, lu, preTabs t lt, preTabs u lu⟩

/-- The bits `< m` that some key has as `A` (resp. `B`). -/
def needA (keys : Array Key) (m : ℕ) : Array Bool := (Array.range m).map fun A => keys.any (·.A == A)
def needB (keys : Array Key) (m : ℕ) : Array Bool := (Array.range m).map fun B => keys.any (·.B == B)

/-- **The evaluation context** of a slot and a matrix (`n`: the row coordinates). -/
structure ECtx where
  n : ℕ
  tb : Tb
  t : ℕ → F
  u : ℕ → F
  keys : Array Key
  kp : Array KP
  dkp : KP
  /-- Each key's shared value in the slot. -/
  sv : Array F
  /-- Each key's number of shared inputs in the slot. -/
  nsh : Array ℕ
  /-- Each key's run patterns and their inner sums. -/
  ps : Array (Array Pat)
  inr : Array (Array F)

/-- The high factor of a run, `eq(σ_{≥B}, ch)`. -/
@[inline] def hfS (tb : Tb) (u : ℕ → F) (B x : ℕ) : F := hfac tb.stab tb.ns tb.shi 12 23 u B x

/-- **A prepared piece's value** for matrix `s` (the specification of `ppv3`). -/
def ppv (s : Mat) (c : ECtx) : PPc → F
  | .sp g => growsVal s c.tb.tlo c.tb.thi c.tb.slo c.tb.shi g
  | .ins k xh ch own =>
    hfac c.tb.ttab c.tb.nt c.tb.thi 11 c.n c.t (c.keys.getD k dkey).A xh *
      (hfac c.tb.stab c.tb.ns c.tb.shi 12 23 c.u (c.keys.getD k dkey).B ch * (c.kp.getD k c.dkp).loc +
        (c.kp.getD k c.dkp).one * c.tb.e1 + c.sv.getD k 0 +
        ownSumP (c.kp.getD k c.dkp).u c.tb.slo c.tb.shi (c.inr.getD k #[]) (hfS c.tb c.u)
          (c.ps.getD k #[]) (c.nsh.getD k 0) own)

/-- **A slot's context** (`gsh`: its shared forms, grouped; `pats`: the run patterns). -/
def ectx (s : Mat) (n : ℕ) (tb : Tb) (t u : ℕ → F) (keys : Array Key) (kp : Array KP)
    (gsh : Array (List GForm)) (pats : Array (Array Pat)) : ECtx :=
  let dkp := kprep s t u dkey
  ⟨n, tb, t, u, keys, kp, dkp,
    (Array.range gsh.size).map (fun k => ownSum (kp.getD k dkp).u tb.slo tb.shi 0 (gsh.getD k [])),
    gsh.map List.length, pats,
    (Array.range pats.size).map fun k =>
      inrOf (kp.getD k dkp).u (tabOr tb.pu tb.lu u) ((gsh.map List.length).getD k 0) (pats.getD k #[])⟩

/-- A slot's value: the sum of its pieces'. -/
def slotV (s : Mat) (c : ECtx) (pps : List PPc) : F := sumL (ppv s c) pps

/-! ## Correctness of the pieces' values -/

/-- **Empty rows add nothing.** -/
theorem rowsValI_filter (s : Mat) (gt gs : ℕ → F) (rs : List (ℕ × Row)) :
    rowsValI (RingHom.id F) s gt gs (rs.filter nonEmpty) = rowsValI (RingHom.id F) s gt gs rs := by
  simp only [rowsValI, sumL_eq]
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rw [List.filter_cons]
    split_ifs with h
    · simp [ih]
    · have h' : p.2.a.isEmpty = true ∧ p.2.b.isEmpty = true ∧ p.2.c.isEmpty = true := by
        simpa [nonEmpty, and_assoc] using h
      have hm : s.r p.2 = [] := by
        cases s <;> simp only [Mat.r] <;> simp only [List.isEmpty_iff] at h' <;> simp [h']
      rw [List.map_cons, List.sum_cons, ← ih, hm]
      simp [linEI, sumL_eq]

theorem key_ok {n : ℕ} {keys : Array Key} (hk : keys.all (Key.ok n) = true) (k : ℕ) :
    (keys.getD k dkey).ok n = true := by
  rw [Array.getD_eq_getD_getElem?]
  rcases h : keys[k]? with _ | K
  · simp [Key.ok, dkey]
  · obtain ⟨hk', hK⟩ := Array.getElem?_eq_some_iff.1 h
    exact hK ▸ (Array.all_eq_true.1 hk) k hk'

theorem locOk_mem {B : ℕ} {l : LinT} (h : locOk B l = true) {k : ℕ} {c : F}
    (hm : (Wire.loc k, c) ∈ l) : k < 2 ^ B := by
  have := List.all_eq_true.1 h _ hm
  simpa using this

theorem Key.ok_spec {n : ℕ} {K : Key} (h : K.ok n = true) :
    K.A ≤ n ∧ K.B ≤ 23 ∧ K.rows.length ≤ 2 ^ K.A ∧
      ∀ s : Mat, ∀ r ∈ K.rows, ∀ k c, (Wire.loc k, c) ∈ s.t r → k < 2 ^ K.B := by
  simp only [Key.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun s r hr k c hm => ?_⟩
  obtain ⟨⟨ha, hb⟩, hc⟩ := h4 r hr
  cases s
  · exact locOk_mem ha hm
  · exact locOk_mem hb hm
  · exact locOk_mem hc hm

/-- **The own inputs with runs** at an evaluation's tables are the own inputs' value. -/
theorem ownSumP_tb (n : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) (U : Array F)
    (ps : Array Pat) (J : ℕ) (own : List Lin) :
    ownSumP U (tbOf n t u one nt ns lt lu).slo (tbOf n t u one nt ns lt lu).shi
        (inrOf U (tabOr (tbOf n t u one nt ns lt lu).pu (tbOf n t u one nt ns lt lu).lu u) J ps)
        (hfS (tbOf n t u one nt ns lt lu) u) ps J (prepOwn ps (List.range ps.size) 0 own) =
      ownSum U (loTab 12 u) (loTab 11 fun l => u (12 + l)) J (own.map (grp 4096)) := by
  have h := ownSumP_eq U (loTab 12 u) (loTab 11 fun l => u (12 + l))
    (inrOf U (tabOr (preTabs u lu) lu u) J ps) (hfS (tbOf n t u one nt ns lt lu) u) ps
    (List.range ps.size) u J (linE_glVal u)
    (fun B ch _ => by simp only [hfS, tbOf]; exact hfac_eq u (S := 12) (n := 23) (by norm_num) ns B ch)
    (fun i hi => by rw [inrOf_getD hi, tabOr_eq]) own.length own rfl 0
  simp only [tbOf, Nat.add_zero] at h ⊢
  exact h

/-- **A piece's value is its rows' sparse value** (`tplR_mle` for an instance). -/
theorem ppv_eq (s : Mat) {n : ℕ} (hn : 11 ≤ n) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool)
    (keys : Array Key) (sh : Array (List Lin)) (pats : Array (Array Pat))
    (hk : keys.all (Key.ok n) = true) (p : Piece) :
    ppv s (ectx s n (tbOf n t u one nt ns lt lu) t u keys (keys.map (kprep s t u))
        (sh.map (·.map (grp 4096))) pats) (prepPiece pats p) =
      rowsVal (RingHom.id F) s n 23 t u (p.rows keys sh one) := by
  have hE : ∀ l, glVal (loTab 12 u) (loTab 11 fun l => u (12 + l)) (grp 4096 l) =
      linE (RingHom.id F) 23 u l := linE_glVal u
  cases p with
  | sp rs =>
    simp only [prepPiece, ppv, ectx, tbOf, Piece.rows]
    have h1 : splitAt (loTab 11 t) (loTab (n - 11) fun l => t (11 + l)) 2048 = gN n t :=
      splitE_eq (m := n) (s := 11) hn t
    have h2 : splitAt (loTab 12 u) (loTab 11 fun l => u (12 + l)) 4096 = gN 23 u :=
      splitE_eq (m := 23) (s := 12) (by norm_num) u
    rw [growsVal_grows, h1, h2, rowsValI_filter, rowsValI_eq]
  | ins k xh ch own =>
    obtain ⟨hA, hB, hT, hL⟩ := Key.ok_spec (key_ok hk k)
    set K := keys.getD k dkey with hK
    simp only [prepPiece, ppv, ectx, Piece.rows, range_getD_inr]
    rw [ownSumP_tb]
    simp only [tbOf]
    rw [← hK, tplR_mle (RingHom.id F) s t u K.rows one _ xh ch hA hB hT (hL s)
      (getD0 (loTab K.A t)) (getD0 (loTab K.B u))
      (fun j hj => loTab_getD _ _ (lt_of_lt_of_le hj hT)) (fun j hj => loTab_getD _ _ hj)]
    have hP : (keys.map (kprep s t u)).getD k (kprep s t u dkey) = kprep s t u K := getD_map' ..
    rw [hP, hfac_eq t (S := 11) (n := n) hn, hfac_eq u (S := 12) (n := 23) (by norm_num)]
    have hsh : (sh.map (·.map (grp 4096))).getD k [] = (sh.getD k []).map (grp 4096) :=
      getD_map' sh (·.map (grp 4096)) k []
    have hn' : ((sh.map (·.map (grp 4096))).map List.length).getD k 0 = (sh.getD k []).length := by
      rw [show (0 : ℕ) = List.length ([] : List GForm) from rfl, getD_map', hsh, List.length_map]
    have hsv : ((Array.range (sh.map (·.map (grp 4096))).size).map fun k' =>
        ownSum ((keys.map (kprep s t u)).getD k' (kprep s t u dkey)).u (loTab 12 u)
          (loTab 11 fun l => u (12 + l)) 0 ((sh.map (·.map (grp 4096))).getD k' [])).getD k 0 =
        ((List.range (sh.getD k []).length).map fun i =>
          (kprep s t u K).u.getD i 0 * linE (RingHom.id F) 23 u ((sh.getD k []).getD i [])).sum := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
      split_ifs with hks
      · simp only [Option.map_some, Option.getD_some]
        rw [hP, hsh, ownSum_eq _ _ _ _ hE]; simp
      · have : sh.getD k [] = [] := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hks)]; rfl
        simp [this]
    rw [hn', hsv, ownSum_eq _ _ _ _ hE, hE]
    unfold instClosed
    simp only [kprep, kprepT]
    rw [denseIT_sum _ (fun i => linE (RingHom.id F) 23 u ((sh.getD k [] ++ own).getD i []))
      ((sh.getD k []).length + own.length) (fun i hi => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hi)]; rfl),
      sum_split _ _ rfl]
    ring

/-- **A slot's value is its pieces' rows' sparse value.** -/
theorem slotV_eq (s : Mat) {n : ℕ} (hn : 11 ≤ n) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool)
    (keys : Array Key) (sh : Array (List Lin)) (pats : Array (Array Pat))
    (hk : keys.all (Key.ok n) = true) (pcs : List Piece) :
    slotV s (ectx s n (tbOf n t u one nt ns lt lu) t u keys (keys.map (kprep s t u))
        (sh.map (·.map (grp 4096))) pats) (pcs.map (prepPiece pats)) =
      rowsVal (RingHom.id F) s n 23 t u (pcs.flatMap (Piece.rows keys sh one)) := by
  rw [slotV, sumL_eq, rowsVal_flatMap, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun p _ => ppv_eq s hn t u one nt ns lt lu keys sh pats hk p)

/-! ## The three matrices in one pass

`ppv3` computes a piece's `A`, `B` and `C` values together: the high `eq` factors, the own and
shared inputs' `E` values and the sparse rows' row factors are computed once for the three. -/

/-- The three matrices' values of grouped rows. -/
def growsVal3 (tlo thi slo shi : Array F) (G : GRows) : F3 :=
  sum3 (fun h =>
    let x := sum3 (fun r => let w := tlo.getD r.lo 0
      (rowMul slo shi w r.a, rowMul slo shi w r.b, rowMul slo shi w r.c)) h.2
    let y := thi.getD h.1 0
    (y * x.1, y * x.2.1, y * x.2.2)) G

theorem growsVal3_eq (tlo thi slo shi : Array F) (G : GRows) :
    growsVal3 tlo thi slo shi G = (growsVal .a tlo thi slo shi G, growsVal .b tlo thi slo shi G,
      growsVal .c tlo thi slo shi G) := by
  simp only [growsVal3, sum3_eq, growsVal, rInner, GRow.m]

/-- The own inputs of the three matrices: `E(g_j)` once. -/
def ownSum3 (Ua Ub Uc : Array F) (slo shi : Array F) : ℕ → List GForm → F3
  | _, [] => (0, 0, 0)
  | j, g :: gs =>
    let e := glVal slo shi g
    add3 (Ua.getD j 0 * e, Ub.getD j 0 * e, Uc.getD j 0 * e) (ownSum3 Ua Ub Uc slo shi (j + 1) gs)

theorem ownSum3_eq (Ua Ub Uc slo shi : Array F) : ∀ (j : ℕ) (g : List GForm),
    ownSum3 Ua Ub Uc slo shi j g = (ownSum Ua slo shi j g, ownSum Ub slo shi j g, ownSum Uc slo shi j g)
  | _, [] => rfl
  | j, g :: gs => by rw [ownSum3, ownSum3_eq Ua Ub Uc slo shi (j + 1) gs]; rfl

/-- The three preparations of a key. -/
abbrev KP3 := KP × KP × KP

/-- **The three preparations** (`kprepF`), the key's two tables from the evaluation's `tb`. -/
def kprep3 (tb : Tb) (t u : ℕ → F) (K : Key) : KP3 :=
  let eτ := getD0 (tabOr tb.pt tb.lt t K.A); let eσ := getD0 (tabOr tb.pu tb.lu u K.B)
  kprep3F eτ eσ K

theorem kprep3_eq (n : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) (K : Key) :
    kprep3 (tbOf n t u one nt ns lt lu) t u K = (kprep .a t u K, kprep .b t u K, kprep .c t u K) := by
  simp only [kprep3, tbOf, tabOr_eq, kprep3F_eq, kprepF_eq, kprep]

/-- **A slot's context for the three matrices.** -/
structure ECtx3 where
  n : ℕ
  tb : Tb
  t : ℕ → F
  u : ℕ → F
  keys : Array Key
  kp : Array KP3
  dkp : KP3
  sv : Array F3
  nsh : Array ℕ
  ps : Array (Array Pat)
  inr : Array (Array F3)
  /-- Each key's `one` coefficients times `E(one)`, once per slot (B0: not once per piece). -/
  ce : Array F3
  dce : F3

/-- The patterns' inner sums of a slot: they depend on the slot's shared forms only through their
numbers `nl` (S-T1: so slots with equal numbers share them, `nodeV3`). -/
def inr3 (tb : Tb) (u : ℕ → F) (kp : Array KP3) (dkp : KP3) (nl : Array ℕ)
    (pats : Array (Array Pat)) : Array (Array F3) :=
  (Array.range pats.size).map fun k => let P := kp.getD k dkp
    inrOf3 P.1.u P.2.1.u P.2.2.u (tabOr tb.pu tb.lu u) (nl.getD k 0) (pats.getD k #[])

/-- A key's `one` coefficients times `E(one)`. -/
def ceOf (tb : Tb) (P : KP3) : F3 := (P.1.one * tb.e1, P.2.1.one * tb.e1, P.2.2.one * tb.e1)

/-- A slot's context with its patterns' inner sums given. -/
def ectx3W (n : ℕ) (tb : Tb) (t u : ℕ → F) (keys : Array Key) (kp : Array KP3)
    (gsh : Array (List GForm)) (pats : Array (Array Pat)) (inr : Array (Array F3)) : ECtx3 :=
  let dkp := kprep3 tb t u dkey
  ⟨n, tb, t, u, keys, kp, dkp,
    (Array.range gsh.size).map (fun k => let P := kp.getD k dkp
      ownSum3 P.1.u P.2.1.u P.2.2.u tb.slo tb.shi 0 (gsh.getD k [])),
    gsh.map List.length, pats, inr, kp.map (ceOf tb), ceOf tb dkp⟩

def ectx3 (n : ℕ) (tb : Tb) (t u : ℕ → F) (keys : Array Key) (kp : Array KP3)
    (gsh : Array (List GForm)) (pats : Array (Array Pat)) : ECtx3 :=
  ectx3W n tb t u keys kp gsh pats (inr3 tb u kp (kprep3 tb t u dkey) (gsh.map List.length) pats)

/-- **A prepared piece's three values.** -/
def ppv3 (c : ECtx3) : PPc → F3
  | .sp g => growsVal3 c.tb.tlo c.tb.thi c.tb.slo c.tb.shi g
  | .ins k xh ch own =>
    let K := c.keys.getD k dkey; let P := c.kp.getD k c.dkp
    let h1 := hfac c.tb.ttab c.tb.nt c.tb.thi 11 c.n c.t K.A xh
    let h2 := hfac c.tb.stab c.tb.ns c.tb.shi 12 23 c.u K.B ch
    let sv := c.sv.getD k (0, 0, 0)
    let e := c.ce.getD k c.dce
    let o := ownSumP3 P.1.u P.2.1.u P.2.2.u c.tb.slo c.tb.shi (c.inr.getD k #[]) (hfS c.tb c.u)
      (c.ps.getD k #[]) (c.nsh.getD k 0) own
    (h1 * (h2 * P.1.loc + e.1 + sv.1 + o.1),
     h1 * (h2 * P.2.1.loc + e.2.1 + sv.2.1 + o.2.1),
     h1 * (h2 * P.2.2.loc + e.2.2 + sv.2.2 + o.2.2))

def slotV3 (c : ECtx3) (pps : List PPc) : F3 := sum3 (ppv3 c) pps

theorem kp3_getD (n : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) (keys : Array Key)
    (k : ℕ) :
    (keys.map (kprep3 (tbOf n t u one nt ns lt lu) t u)).getD k (kprep3 (tbOf n t u one nt ns lt lu) t u dkey) =
      ((keys.map (kprep .a t u)).getD k (kprep .a t u dkey),
       (keys.map (kprep .b t u)).getD k (kprep .b t u dkey),
       (keys.map (kprep .c t u)).getD k (kprep .c t u dkey)) := by
  rw [getD_map' keys (kprep3 _ t u), getD_map', getD_map', getD_map', kprep3_eq]

theorem getD_range3 (f g h : ℕ → F) (n k : ℕ) :
    ((Array.range n).map fun k => (f k, g k, h k)).getD k (0, 0, 0) =
      (((Array.range n).map f).getD k 0, ((Array.range n).map g).getD k 0,
        ((Array.range n).map h).getD k 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split_ifs <;> rfl

/-- **The one-pass value is the three values.** -/
theorem slotV3_eq (n n' : ℕ) (t u : ℕ → F) (one : Lin) (nt ns lt lu : Array Bool) (keys : Array Key)
    (g : Array (List GForm)) (pats : Array (Array Pat)) (pps : List PPc) :
    slotV3 (ectx3 n (tbOf n' t u one nt ns lt lu) t u keys
        (keys.map (kprep3 (tbOf n' t u one nt ns lt lu) t u)) g pats) pps =
      (slotV .a (ectx .a n (tbOf n' t u one nt ns lt lu) t u keys (keys.map (kprep .a t u)) g pats) pps,
       slotV .b (ectx .b n (tbOf n' t u one nt ns lt lu) t u keys (keys.map (kprep .b t u)) g pats) pps,
       slotV .c (ectx .c n (tbOf n' t u one nt ns lt lu) t u keys (keys.map (kprep .c t u)) g pats) pps) := by
  simp only [slotV3, slotV, sum3_eq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;>
    refine congrArg (sumL · pps) (funext fun p => ?_) <;>
    cases p <;> simp only [ppv3, ectx3, ectx3W, inr3, getD_map'] <;>
    simp only [ppv3, ppv, ectx3, ectx3W, inr3, ectx, growsVal3_eq, ceOf, kp3_getD, kprep3_eq, getD_map',
      ownSum3_eq, getD_range3,
      ownSumP3_eq, range_getD_inr, range_getD_inr3, inrOf3_map1, inrOf3_map2, inrOf3_map3]

/-! ## The node -/

/-- Slot `σ`'s selector forms. -/
def slotP (σ : ℕ) : Params := muxP Layout.oneCell (Layout.selCells σ)

/-- A layout's cells shifted by `d`. -/
def shiftLay (d : ℕ) (L : TLay) : TLay := L.map fun e => (e.1, e.2.1, e.2.2.1 + d, e.2.2.2)

/-- The keys of a compiled state's instances, in order. -/
def tinKeys (cs : CS) : List TKey := cs.tins.map (·.1)

/-- **A shifted layout fits** a compiled state `c` laid out with it: `c` has the rows, the cells
(shifted by `d`) and the instance sequence of the state `z` the layout was made from. -/
def slotLayOk (z c : CS) (d : ℕ) : Bool :=
  c.nrows == z.nrows && c.next == z.next + d && tinKeys c == tinKeys z

/-- (+) A shifted layout moves the cell bases only. -/
theorem shiftLay_ctl : shiftLay 4 [(.zero, 1, 2, 3)] = [(.zero, 1, 6, 3)] := rfl

/-- (+) A state fits the layout of the same state shifted by `d`; (−) not with another row count, nor
with a cell shift other than `d`. -/
theorem slotLayOk_ctl : slotLayOk (CS.init 5) (CS.init 9) 4 = true ∧
    slotLayOk (CS.init 5) { CS.init 9 with nrows := 1 } 4 = false ∧
    slotLayOk (CS.init 5) (CS.init 9) 3 = false := by decide

/-- Slot 0's layout: the two-pass compile's (`layOf`). -/
def slotLay0 (fin : Finals) : TLay := layOf (slotP 0) (Layout.slotBase 0) (gen fin .mux).ops

/-- Slot `σ ≥ 1`'s layout from slot 0's `l0`: `l0` with its cells shifted to the slot's base if the
slot's compile with it fits (`slotLayOk`: the same rows, cells and instances as slot 0's first pass,
so the groups sit after the slot's skeleton, each sized for its instances), else its own `layOf`. -/
def slotLayS (fin : Finals) (σ : ℕ) (l0 : TLay) : TLay :=
  bif slotLayOk (compileT [] (slotP 0) (Layout.slotBase 0) (gen fin .mux).ops)
      (compileT (shiftLay (Layout.slotBase σ - Layout.slotBase 0) l0) (slotP σ) (Layout.slotBase σ)
        (gen fin .mux).ops) (Layout.slotBase σ - Layout.slotBase 0)
    then shiftLay (Layout.slotBase σ - Layout.slotBase 0) l0
    else layOf (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- **Slot `σ`'s layout** (S-E13: slot `σ ≥ 1` reuses slot 0's when it fits, `slotLayS`, sparing a
compile pass per process). The layout only places the instances: soundness does not depend on it
(`compileT_sound` holds for every layout). -/
def slotLay (fin : Finals) (σ : ℕ) : TLay :=
  if σ = 0 then slotLay0 fin else slotLayS fin σ (slotLay0 fin)

theorem slotLay_zero (fin : Finals) : slotLay fin 0 = slotLay0 fin := if_pos rfl

theorem slotLay_one (fin : Finals) : slotLay fin 1 = slotLayS fin 1 (slotLay0 fin) :=
  if_neg one_ne_zero

/-- **Slot `σ`'s compiled program with the templates** (`compileT (gen fin .mux)`). -/
def slotCST (fin : Finals) (σ : ℕ) : CS :=
  compileT (slotLay fin σ) (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- M's `one` form. -/
abbrev oneL : Lin := Lin.cell Layout.oneCell

/-- **The node's plan** (computed once per node): both slots' layouts and compiled programs, the
keys, each slot's shared forms and pieces — whose rows are the slot's indexed rows (`ok`) — and
their prepared forms. -/
structure Plan where
  lay : ℕ → TLay
  cs : ℕ → CS
  keys : Array Key
  sh0 : Array (List Lin)
  sh1 : Array (List Lin)
  pc0 : List Piece
  pc1 : List Piece
  ok : keys.all (Key.ok 21) = true ∧
    pc0.flatMap (Piece.rows keys sh0 oneL) = slotIRows (lay 0) oneL 0 (cs 0) ∧
    pc1.flatMap (Piece.rows keys sh1 oneL) = slotIRows (lay 1) oneL Layout.slotM (cs 1)
  g0 : Array (List GForm)
  g1 : Array (List GForm)
  p0 : List PPc
  p1 : List PPc
  hg0 : g0 = sh0.map (·.map (grp 4096))
  hg1 : g1 = sh1.map (·.map (grp 4096))
  /-- The run patterns per key (any table: `prepOwn` checks every run) and their chunk bits. -/
  pats : Array (Array Pat)
  pbs : List ℕ
  hp0 : p0 = pc0.map (prepPiece pats)
  hp1 : p1 = pc1.map (prepPiece pats)

/-- The chunk bits of the patterns. -/
def patBits (pats : Array (Array Pat)) : List ℕ :=
  pats.foldl (fun l ps => ps.foldl (fun l p => if l.contains p.B then l else p.B :: l) l) []

/-- A plan from its parts. -/
def mkPlanOf (l0 l1 : TLay) (c0 c1 : CS) (keys : Array Key) (sh0 sh1 : Array (List Lin))
    (pc0 pc1 : List Piece) (pats : Array (Array Pat)) (ok : keys.all (Key.ok 21) = true ∧
      pc0.flatMap (Piece.rows keys sh0 oneL) = slotIRows l0 oneL 0 c0 ∧
      pc1.flatMap (Piece.rows keys sh1 oneL) = slotIRows l1 oneL Layout.slotM c1) : Plan where
  lay σ := if σ = 0 then l0 else l1
  cs σ := if σ = 0 then c0 else c1
  keys := keys
  sh0 := sh0
  sh1 := sh1
  pc0 := pc0
  pc1 := pc1
  ok := by simpa using ok
  g0 := sh0.map (·.map (grp 4096))
  g1 := sh1.map (·.map (grp 4096))
  pats := pats
  pbs := patBits pats
  p0 := pc0.map (prepPiece pats)
  p1 := pc1.map (prepPiece pats)
  hg0 := rfl
  hg1 := rfl
  hp0 := rfl
  hp1 := rfl

/-- **The plan of two laid-out, compiled slots** from the search's data: kept if the keys are well
formed and the pieces' rows are the slots' rows (checked here, once), else one sparse piece per
slot. -/
def mkPlan (l0 l1 : TLay) (c0 c1 : CS)
    (d : Array Key × Array (List Lin) × Array (List Lin) × List Piece × List Piece) : Plan :=
  if h : (d.1.all (Key.ok 21) && eqL (d.2.2.2.1.flatMap (Piece.rows d.1 d.2.1 oneL))
      (slotIRows l0 oneL 0 c0) &&
      eqL (d.2.2.2.2.flatMap (Piece.rows d.1 d.2.2.1 oneL)) (slotIRows l1 oneL Layout.slotM c1)) = true
  then
    mkPlanOf l0 l1 c0 c1 d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2
      (mkPats d.1.size (d.2.2.2.1 ++ d.2.2.2.2)) (by
      simp only [Bool.and_eq_true] at h
      exact ⟨h.1.1, eqL_eq h.1.2, eqL_eq h.2⟩)
  else
    mkPlanOf l0 l1 c0 c1 #[] #[] #[] [.sp (slotIRows l0 oneL 0 c0)]
      [.sp (slotIRows l1 oneL Layout.slotM c1)] #[] (by simp [Piece.rows])

/-- **The node's plan, checked at run time** (S-E5 … S-E11: both slots' rows compared with the
pieces'); superseded by `planOf`, kept for the dev probes' comparison. -/
def planOfChk (fin : Finals) : Plan :=
  let ops := (gen fin .mux).ops
  let l0 := slotLay fin 0; let l1 := slotLay fin 1
  let c0 := compileT l0 (slotP 0) (Layout.slotBase 0) ops
  let c1 := compileT l1 (slotP 1) (Layout.slotBase 1) ops
  mkPlan l0 l1 c0 c1 (groupPPs
    (slotPPs (tplExt l0.ctx) (slotP 0) (Layout.slotBase 0) ops l0 oneL 0 c0)
    (slotPPs (tplExt l1.ctx) (slotP 1) (Layout.slotBase 1) ops l1 oneL Layout.slotM c1))

/-! ## The plan from proved pieces (S-E13) -/


/-- The key data of a compiled state's keys (computed once per process). -/
def kmsOf (z : CS) : List KM := (keyCounts z.tins).map fun p => mkKM p.1

/-- The layout data of a key, from the key data. -/
def infoOf (kms : List KM) (k : TKey) : ℕ × ℕ × ℕ :=
  let e := kmOf kms k; (e.rows.length, e.cr, e.nl)

/-- A layout, its compiled state and blocks. -/
def withLay (l : TLay) (r : CS × List Seg × List (TKey × Tpl)) : TLay × CS × List Seg := (l, r.1, r.2.1)

theorem withLay_1 (l : TLay) (r : CS × List Seg × List (TKey × Tpl)) : (withLay l r).1 = l := rfl
theorem withLay_2 (l : TLay) (r : CS × List Seg × List (TKey × Tpl)) : (withLay l r).2.1 = r.1 := rfl

/-- Slot 1 compiled at layout `l`. -/
def comp1 (ops : List Op) (M : List (TKey × Tpl)) (l : TLay) : TLay × CS × List Seg :=
  withLay l (compMS l (slotP 1) M (CS.init (Layout.slotBase 1)) ops none [])

/-- Slot 1's own layout from its first pass `z1`. -/
def lay1 (kms : List KM) (z1 : CS) : TLay := mkLayI (infoOf kms) z1.nrows z1.next (keyCounts z1.tins)

/-- Slot 1's own two passes. -/
def slot1Own (ops : List Op) (kms : List KM) (M : List (TKey × Tpl)) : TLay × CS × List Seg :=
  comp1 ops M (lay1 kms (compMS [] (slotP 1) M (CS.init (Layout.slotBase 1)) ops none []).1)

/-- Slot 1 at slot 0's layout shifted (`r1`), kept if it fits, else slot 1's own passes. -/
def slot1Pick (ops : List Op) (z0 : CS) (kms : List KM) (l0 : TLay) (M : List (TKey × Tpl))
    (r1 : CS × List Seg × List (TKey × Tpl)) : TLay × CS × List Seg :=
  bif slotLayOk z0 r1.1 (Layout.slotBase 1 - Layout.slotBase 0)
    then withLay (shiftLay (Layout.slotBase 1 - Layout.slotBase 0) l0) r1 else slot1Own ops kms M

/-- **Slot 1's layout, compiled state and blocks**: slot 0's layout `l0` shifted, if slot 1's compile
with it fits (`slotLayOk`), else slot 1's own two passes. (No `let`s: the proofs rewrite with the
equations only, so that the kernel never reduces the choice.) -/
def slot1Of (ops : List Op) (z0 : CS) (kms : List KM) (l0 : TLay) (M : List (TKey × Tpl)) :
    TLay × CS × List Seg :=
  slot1Pick ops z0 kms l0 M
    (compMS (shiftLay (Layout.slotBase 1 - Layout.slotBase 0) l0) (slotP 1) M
      (CS.init (Layout.slotBase 1)) ops none [])

/-- **The plan's data** (S-E13): both slots compiled with a template memo (the skeleton's blocks
recorded in the same pass; slot 1 with slot 0's layout shifted when it fits), their proto-pieces
(`slotRP`), the grouping, and each slot's checked pieces. -/
def planData (fin : Finals) :
    Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece :=
  let ops := (gen fin .mux).ops
  let z0 := compMS [] (slotP 0) [] (CS.init (Layout.slotBase 0)) ops none []
  let kms := kmsOf z0.1
  let l0 := mkLayI (infoOf kms) z0.1.nrows z0.1.next (keyCounts z0.1.tins)
  let r0 := compMS l0 (slotP 0) z0.2.2 (CS.init (Layout.slotBase 0)) ops none []
  let s1 := slot1Of ops z0.1 kms l0 r0.2.2
  let p0 := slotRP oneL kms l0 0 r0.1 r0.2.1.reverse []
  let rps0 := p0.1
  let rps1 := (slotRP oneL kms s1.1 Layout.slotM s1.2.1 s1.2.2.reverse p0.2).1
  let g := groupRP rps0 rps1
  (g.1, g.2.1, g.2.2.1, piecesOf g.1 g.2.1 oneL rps0 g.2.2.2.1, piecesOf g.1 g.2.2.1 oneL rps1 g.2.2.2.2)

theorem mkKM_info (k : TKey) :
    ((mkKM k).rows.length, (mkKM k).cr, (mkKM k).nl) = ((tRows k).length, cregion k, tNlocs k) := by
  have h := keyInfo_eq k
  unfold mkKM; dsimp only; split
  · simp [h]
  · split <;> simp [h]

theorem compMS_T (L : TLay) (P : Params) (base : ℕ) (ops : List Op) {M : List (TKey × Tpl)} (h : MOk M) :
    (compMS L P M (CS.init base) ops none []).1 = compileT L P base ops ∧
      MOk (compMS L P M (CS.init base) ops none []).2.2 :=
  compMS_eq L P ops M _ none [] h

theorem kmsOf_eq (z : CS) : kmsOf z = ((keyCounts z.tins).map Prod.fst).map mkKM := by
  rw [kmsOf, List.map_map]; rfl

theorem infoOf_eq (z : CS) (k : TKey) : infoOf (kmsOf z) k = ((tRows k).length, cregion k, tNlocs k) := by
  rw [infoOf, kmsOf_eq, kmOf_map, mkKM_info]

/-- A layout from the two passes' first: `layOf`. -/
theorem lay_eq (z : CS) (P : Params) (base : ℕ) (ops : List Op) (hz : z = compileT [] P base ops)
    (z' : CS) : mkLayI (infoOf (kmsOf z')) z.nrows z.next (keyCounts z.tins) = layOf P base ops := by
  rw [mkLayI_eq _ (infoOf_eq z'), layOf, hz]

theorem slot1Own_spec (fin : Finals) (z0 : CS) {M : List (TKey × Tpl)} (hM : MOk M) :
    (slot1Own (gen fin .mux).ops (kmsOf z0) M).1 = layOf (slotP 1) (Layout.slotBase 1) (gen fin .mux).ops ∧
      (slot1Own (gen fin .mux).ops (kmsOf z0) M).2.1 =
        compileT (layOf (slotP 1) (Layout.slotBase 1) (gen fin .mux).ops) (slotP 1) (Layout.slotBase 1)
          (gen fin .mux).ops := by
  obtain ⟨hz1, -⟩ := compMS_T [] (slotP 1) (Layout.slotBase 1) (gen fin .mux).ops hM
  have hl := lay_eq _ (slotP 1) (Layout.slotBase 1) (gen fin .mux).ops hz1 z0
  rw [← lay1] at hl
  rw [slot1Own, hl, comp1, withLay_1, withLay_2]
  exact ⟨rfl, (compMS_T _ (slotP 1) (Layout.slotBase 1) (gen fin .mux).ops hM).1⟩

theorem slot1Of_spec (fin : Finals) (z0 : CS) {M : List (TKey × Tpl)} (hM : MOk M) :
    (slot1Of (gen fin .mux).ops (compileT [] (slotP 0) (Layout.slotBase 0) (gen fin .mux).ops)
        (kmsOf z0) (slotLay0 fin) M).1 = slotLay fin 1 ∧
      (slot1Of (gen fin .mux).ops (compileT [] (slotP 0) (Layout.slotBase 0) (gen fin .mux).ops)
        (kmsOf z0) (slotLay0 fin) M).2.1 = slotCST fin 1 := by
  obtain ⟨hr1, -⟩ := compMS_T (shiftLay (Layout.slotBase 1 - Layout.slotBase 0) (slotLay0 fin))
    (slotP 1) (Layout.slotBase 1) (gen fin .mux).ops hM
  obtain ⟨ho1, ho2⟩ := slot1Own_spec fin z0 hM
  rw [slot1Of, slot1Pick, Bool.apply_cond Prod.fst, Bool.apply_cond (fun x : TLay × CS × List Seg => x.2.1),
    withLay_1, withLay_2, ho1, ho2, hr1, slotCST, slotLay_one, slotLayS,
    ← Bool.apply_cond (fun L => compileT L (slotP 1) (Layout.slotBase 1) (gen fin .mux).ops)]
  exact ⟨rfl, rfl⟩

/-- **The plan's data are the slots' rows**: slot `σ`'s pieces have the rows of `slotCST fin σ` at
`slotLay fin σ`. -/
theorem planData_rows (fin : Finals) :
    (planData fin).2.2.2.1.flatMap (Piece.rows ((planData fin).1.map mkKey) (planData fin).2.1 oneL) =
        slotIRows (slotLay fin 0) oneL 0 (slotCST fin 0) ∧
      (planData fin).2.2.2.2.flatMap (Piece.rows ((planData fin).1.map mkKey) (planData fin).2.2.1 oneL) =
        slotIRows (slotLay fin 1) oneL Layout.slotM (slotCST fin 1) := by
  simp only [planData, piecesOf_rows]
  obtain ⟨hz0, mz0⟩ := compMS_T [] (slotP 0) (Layout.slotBase 0) (gen fin .mux).ops (M := []) (by simp [MOk])
  have hl0 := lay_eq _ (slotP 0) (Layout.slotBase 0) (gen fin .mux).ops hz0
    (compMS [] (slotP 0) [] (CS.init (Layout.slotBase 0)) (gen fin .mux).ops none []).1
  rw [← slotLay0] at hl0
  obtain ⟨hr0, mr0⟩ := compMS_T (mkLayI (infoOf (kmsOf (compMS [] (slotP 0) [] (CS.init (Layout.slotBase 0))
      (gen fin .mux).ops none []).1)) (compMS [] (slotP 0) [] (CS.init (Layout.slotBase 0)) (gen fin .mux).ops none []).1.nrows
      (compMS [] (slotP 0) [] (CS.init (Layout.slotBase 0)) (gen fin .mux).ops none []).1.next
      (keyCounts (compMS [] (slotP 0) [] (CS.init (Layout.slotBase 0)) (gen fin .mux).ops none []).1.tins))
    (slotP 0) (Layout.slotBase 0) (gen fin .mux).ops mz0
  rw [hl0] at hr0 ⊢
  obtain ⟨h1, h2⟩ := slot1Of_spec fin (compMS [] (slotP 0) [] (CS.init (Layout.slotBase 0)) (gen fin .mux).ops none []).1 mr0
  rw [← hz0, hl0] at h1 h2
  rw [h1, h2, kmsOf_eq, slotRP_rows, slotRP_rows, hr0, slotCST, slotLay_zero]
  exact ⟨rfl, rfl⟩

/-- A plan at `slotLay fin`, `slotCST fin` from its pieces (the prepared forms derived). -/
def mkPlanF (fin : Finals) (keys : Array Key) (sh0 sh1 : Array (List Lin)) (pc0 pc1 : List Piece)
    (pats : Array (Array Pat)) (ok : keys.all (Key.ok 21) = true ∧
      pc0.flatMap (Piece.rows keys sh0 oneL) = slotIRows (slotLay fin 0) oneL 0 (slotCST fin 0) ∧
      pc1.flatMap (Piece.rows keys sh1 oneL) = slotIRows (slotLay fin 1) oneL Layout.slotM (slotCST fin 1)) :
    Plan where
  lay := slotLay fin
  cs := slotCST fin
  keys := keys
  sh0 := sh0
  sh1 := sh1
  pc0 := pc0
  pc1 := pc1
  ok := ok
  g0 := sh0.map (·.map (grp 4096))
  g1 := sh1.map (·.map (grp 4096))
  pats := pats
  pbs := patBits pats
  p0 := pc0.map (prepPiece pats)
  p1 := pc1.map (prepPiece pats)
  hg0 := rfl
  hg1 := rfl
  hp0 := rfl
  hp1 := rfl

theorem mkPlanF_lay (fin : Finals) (keys : Array Key) (sh0 sh1 : Array (List Lin)) (pc0 pc1 : List Piece)
    (pats : Array (Array Pat)) (ok) :
    (mkPlanF fin keys sh0 sh1 pc0 pc1 pats ok).lay = slotLay fin ∧
      (mkPlanF fin keys sh0 sh1 pc0 pc1 pats ok).cs = slotCST fin := by
  unfold mkPlanF; dsimp only; exact ⟨rfl, rfl⟩

def planOfD (fin : Finals)
    (d : Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece)
    (hd : d = planData fin) : Plan :=
  if h : (d.1.map mkKey).all (Key.ok 21) = true then
    mkPlanF fin (d.1.map mkKey) d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2
      (mkPats (d.1.map mkKey).size (d.2.2.2.1 ++ d.2.2.2.2))
      ⟨h, by subst hd; exact (planData_rows fin).1, by subst hd; exact (planData_rows fin).2⟩
  else
    mkPlanF fin #[] #[] #[] [.sp (slotIRows (slotLay fin 0) oneL 0 (slotCST fin 0))]
      [.sp (slotIRows (slotLay fin 1) oneL Layout.slotM (slotCST fin 1))] #[]
      ⟨by simp, List.flatMap_singleton .., List.flatMap_singleton ..⟩

/-- **The node's plan** (S-E13; once per process, `FRNodePlan.nodePlan`): `planData`'s keys, shared
forms and pieces, whose rows are the slots' rows by proof (`planData_rows`), not by a run-time
comparison; the run patterns from both slots' pieces (`mkPats`; any patterns are sound: `prepOwn`
checks each run); one sparse piece per slot if a key is not well formed. -/
def planOf (fin : Finals) : Plan := planOfD fin (planData fin) rfl

/-- The plan's slots are `slotLay` and `slotCST` (for S-G: `nodeIRows (planOf fin)` is
`nodeIRows_planOf`). -/
theorem planOfD_lay (fin : Finals) (d : Array GK × Array (List Lin) × Array (List Lin) × List Piece ×
    List Piece) (hd : d = planData fin) : (planOfD fin d hd).lay = slotLay fin ∧
      (planOfD fin d hd).cs = slotCST fin := by
  unfold planOfD; split <;> exact mkPlanF_lay ..

theorem planOf_lay (fin : Finals) : (planOf fin).lay = slotLay fin := (planOfD_lay fin _ rfl).1

theorem planOf_cs (fin : Finals) : (planOf fin).cs = slotCST fin := (planOfD_lay fin _ rfl).2

/-- **The node's indexed M rows**: slot `σ`'s at offset `σ · 2^20`. -/
def nodeIRows (pl : Plan) : List (ℕ × Row) :=
  slotIRows (pl.lay 0) oneL 0 (pl.cs 0) ++ slotIRows (pl.lay 1) oneL Layout.slotM (pl.cs 1)

/-- **The node's indexed M rows are both slots' templated compile** (S-G's `truthE` is stated over
`nodeIRows (planOf fin)`). -/
theorem nodeIRows_planOf (fin : Finals) :
    nodeIRows (planOf fin) = slotIRows (slotLay fin 0) oneL 0 (slotCST fin 0) ++
      slotIRows (slotLay fin 1) oneL Layout.slotM (slotCST fin 1) := by
  rw [nodeIRows, planOf_lay, planOf_cs]

/-- The node's value of matrix `s`, given the tables (the specification of `nodeV3`). -/
def nodeV (pl : Plan) (s : Mat) (t u : ℕ → F) (tb : Tb) : F :=
  let kp := pl.keys.map (kprep s t u)
  slotV s (ectx s 21 tb t u pl.keys kp pl.g0 pl.pats) pl.p0 +
    slotV s (ectx s 21 tb t u pl.keys kp pl.g1 pl.pats) pl.p1

theorem nodeV_eq (pl : Plan) (s : Mat) (t u : ℕ → F) (nt ns lt lu : Array Bool) :
    nodeV pl s t u (tbOf 21 t u oneL nt ns lt lu) = rowsVal (RingHom.id F) s 21 23 t u (nodeIRows pl) := by
  simp only [nodeV, nodeIRows]
  rw [pl.hg0, pl.hg1, pl.hp0, pl.hp1, slotV_eq _ (by norm_num) _ _ _ _ _ _ _ _ _ _ pl.ok.1,
    slotV_eq _ (by norm_num) _ _ _ _ _ _ _ _ _ _ pl.ok.1, pl.ok.2.1, pl.ok.2.2, rowsVal_append]

/-- The node's three matrices in one pass per slot. -/
def nodeV3 (pl : Plan) (t u : ℕ → F) (tb : Tb) : F3 :=
  let kp := pl.keys.map (kprep3 tb t u)
  let dkp := kprep3 tb t u dkey
  let n0 := pl.g0.map List.length; let n1 := pl.g1.map List.length
  let i0 := inr3 tb u kp dkp n0 pl.pats
  add3 (slotV3 (ectx3W 21 tb t u pl.keys kp pl.g0 pl.pats i0) pl.p0)
    (slotV3 (ectx3W 21 tb t u pl.keys kp pl.g1 pl.pats
      (if n1 = n0 then i0 else inr3 tb u kp dkp n1 pl.pats)) pl.p1)

/-- `nodeV3` is the two slots' `slotV3` (the inner sums shared when the slots' numbers agree). -/
theorem nodeV3_slots (pl : Plan) (t u : ℕ → F) (tb : Tb) : nodeV3 pl t u tb =
    add3 (slotV3 (ectx3 21 tb t u pl.keys (pl.keys.map (kprep3 tb t u)) pl.g0 pl.pats) pl.p0)
      (slotV3 (ectx3 21 tb t u pl.keys (pl.keys.map (kprep3 tb t u)) pl.g1 pl.pats) pl.p1) := by
  simp only [nodeV3, ectx3]
  split_ifs with h
  · rw [h]
  · rfl

theorem nodeV3_eq (pl : Plan) (t u : ℕ → F) (nt ns lt lu : Array Bool) :
    nodeV3 pl t u (tbOf 21 t u oneL nt ns lt lu) =
      (nodeV pl .a t u (tbOf 21 t u oneL nt ns lt lu), nodeV pl .b t u (tbOf 21 t u oneL nt ns lt lu),
        nodeV pl .c t u (tbOf 21 t u oneL nt ns lt lu)) := by
  simp only [nodeV3_slots, nodeV, slotV3_eq, add3]

/-- The tables' bit sets for keys `keys` and run chunk bits `pbs`. -/
def tbOfK (n : ℕ) (t u : ℕ → F) (keys : Array Key) (pbs : List ℕ) : Tb :=
  tbOf n t u oneL (needAll keys (·.A) 12) (needAll keys (·.B) 13 pbs) (needAll keys (·.A) (n + 1))
    (needAll keys (·.B) 24 pbs)

/-- **`evalM`** (revision 3.12; S-E5; S-E11: runs, the fast key preparation): the node's three M
matrices at `(τ, σ)`, the pieces of both slots in closed form or sparse, the three matrices in one
pass; the tables are computed once. -/
def evalMT (pl : Plan) (τ σ : Array F) : F × F × F :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  nodeV3 pl t u (tbOfK 21 t u pl.keys pl.pbs)

/-- **`evalM`'s specification**: the MLEs of the node's M matrices (`FRVIREval.matMLE`). -/
noncomputable def evalMS (pl : Plan) (τ σ : Array F) : F × F × F :=
  (Eval.matMLE (entriesI .a (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .b (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .c (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ))

/-- **`evalM_eq`** (A.11: the instances' `tplR_mle` and the sparse pieces' `sparse_eq`). -/
theorem evalMT_eq (pl : Plan) (τ σ : Array F) : evalMT pl τ σ = evalMS pl τ σ := by
  simp only [evalMT, tbOfK, evalMS, nodeV3_eq, nodeV_eq, rowsVal_F, Eval.sparse_eq]

/-! ## `evalL`: L's rows (revision 3.13: at the full 23-coordinate point) -/

/-- **L's plan**: L's rows (indexed by position, 15 row coordinates) in aligned blocks of `2^6`. -/
structure LPlan where
  rows : List Row
  keys : Array Key
  sh : Array (List Lin)
  pc : List Piece
  ok : keys.all (Key.ok 15) = true ∧
    pc.flatMap (Piece.rows keys sh oneL) = rows.zipIdx.map fun p => (p.2, p.1)
  g : Array (List GForm)
  p : List PPc
  hg : g = sh.map (·.map (grp 4096))
  hp : p = pc.map (prepPiece #[])

def mkLPlanOf (rows : List Row) (keys : Array Key) (sh : Array (List Lin)) (pc : List Piece)
    (ok : keys.all (Key.ok 15) = true ∧
      pc.flatMap (Piece.rows keys sh oneL) = rows.zipIdx.map fun p => (p.2, p.1)) : LPlan :=
  ⟨rows, keys, sh, pc, ok, sh.map (·.map (grp 4096)), pc.map (prepPiece #[]), rfl, rfl⟩

/-- **L's plan** from its rows (checked as the node's). -/
def planL (rows : List Row) : LPlan :=
  let d := groupPPs (listPPs 6 rows) #[]
  let tgt := rows.zipIdx.map fun p => (p.2, p.1)
  if h : (d.1.all (Key.ok 15) && eqL (d.2.2.2.1.flatMap (Piece.rows d.1 d.2.1 oneL)) tgt) = true then
    mkLPlanOf rows d.1 d.2.1 d.2.2.2.1 (by
      simp only [Bool.and_eq_true] at h; exact ⟨h.1, eqL_eq h.2⟩)
  else mkLPlanOf rows #[] #[] [.sp tgt] (by simp [Piece.rows, tgt])

/-- L's plan keeps its rows. -/
theorem planL_rows (rows : List Row) : (planL rows).rows = rows := by
  simp only [planL]; split <;> rfl

/-- **`evalL`, templated**: L's three matrices at `(τ, σ)` (15 and 23 coordinates). -/
def evalLT (pl : LPlan) (τ σ : Array F) : F × F × F :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  let tb := tbOfK 15 t u pl.keys []
  slotV3 (ectx3 15 tb t u pl.keys (pl.keys.map (kprep3 tb t u)) pl.g #[]) pl.p

theorem entriesOf_eq (sel : Mat) (rows : List Row) :
    Eval.entriesOf sel.r rows = entriesI sel (rows.zipIdx.map fun p => (p.2, p.1)) := by
  simp only [Eval.entriesOf, entriesI, List.flatMap_map]

/-- **`evalL_eq`**: the templated `evalL` is the MLE of L's rows (`FRVIREval.evalRowsSpec`). -/
theorem evalLT_eq (pl : LPlan) (τ σ : Array F) : evalLT pl τ σ = Eval.evalRowsSpec 15 23 pl.rows τ σ := by
  simp only [evalLT, tbOfK, slotV3_eq, Eval.evalRowsSpec]
  rw [pl.hg, pl.hp]
  simp only [slotV_eq _ (by norm_num : 11 ≤ 15) _ _ _ _ _ _ _ _ _ _ pl.ok.1, pl.ok.2, rowsVal_F,
    Eval.sparse_eq]
  simp only [← entriesOf_eq]
  rfl

end TEval
end FR

end G6_FRVIRTplFast
