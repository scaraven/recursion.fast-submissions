-- New for lvm6 (WP LAY): `Φ_Q`'s class table (PHI-decision R3), its start-up guard, and the cost model `phiCost`
-- that CD-8 v2 (`PhiBudget`) bounded (v4 bounds the entries only).
import Lvm6LayI
import Lvm6TyProg
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# The class table of `Φ_Q` and its cost

`Φ_Q(pt) = Σ_e c_e·eq(pt, o + 4(x + 2^20·y))` (`PhiQFE`). With the instance layout (`Lvm6LayI`) the entries of a
class's instances repeat: instance `j` of a class with geometry `g` holds the entries
`(o, g.xb + j·2^a + i, y, c)` of one **template** `(o, i, d, w, c)`, where `y` is
* `d = 0`: `g.yb + j·2^b + w` (a word of the same instance),
* `d = 1`: `g.yb + (j − 1)·2^b + w` (a word of the previous instance; no entry at `j = 0`),
* `d = 2`: `w` (a fixed word: the constant `1`, the gate).

Since `xb`, `yb` are aligned (`CGeom.okB`), `eq(pt, idx)` factors into the low bits (`i`, `w`), the instance bits
(`j`) and the high bits, so a class costs one pass over its template plus `O(n)` for `Σ_j eq(x_j)·eq(y_j)`.

* **`PhiCls`**: the classes (geometry and template) and the remaining entries `rest`; `PhiCls.ents` the expansion.
* **`mkCls es geo wb`**: the table of the entries `es` (merged by `(o, x, y)`): per class the template is every key
  present in a majority of its instances, the instances lacking a template key get a correcting entry in `rest`
  (characteristic 2: `c + c = 0`), every other entry is in `rest`.
* **`clsOkB T es`** (the start-up guard, untimed): the geometries are aligned, the templates fit, and the
  expansion equals `es` entry by entry after merging. Then the class evaluator's value is `PhiQFE`'s (the
  evaluator's theorem; owner TWT).
* **`phiCost T`**: the products of the class evaluator on `T` (PHI-decision §1–§2: R1's cover form with twin
  merging, R2's affine `W` rule, R3's templates); CD-8 bounds it. Calibrated against the Python model of the
  same rules on the exported table (LAY.md).

**LAY3 (PHI-decision v2, levers A2 and A3).**
* **Aligned externals** (`d = 3`): a template entry reading the word `w + j·2^s` of instance `j` (`w`'s bits
  `[s, s + ⌈log₂ n⌉)` zero), so `Σ_j eq(x_mid, j)·eq(y_[s, s+⌈log₂ n⌉), j)` is one more sum per class and stride
  and the entry is `O(1)`. `mkCls` finds them among the external entries (a majority of the instances).
* **Loop classes** (`LCls`, season 1's loop blocks, `Lvm6LayI.LGeom`): a template entry `⟨o, r, w, ss, c⟩` is the
  entries `(o, xb + r·2^l + jf, w + Σ_d ss_d·i_d, c)` for every iteration `jf` (`i = unflat dims jf`). Its kind
  (`LEnt.kind`, PHIV's encoding: the loop is a class of `2^l` one-slot instances `jf`, word `w + f·jf` for a flat
  stride `f`): **0 own** (`f = 1`, `w` aligned to `2^l`: `Σ_j eq(x_lo, j)·eq(y_lo, j) = Π_{b<l} eq(x_b, y_b)`,
  `l` products shared by all loops), **2 fixed** (`f = 0`: `Σ_j eq(x_lo, j) = 1`), **3 aligned** (`f = 2^e`,
  `e ≥ 1`, bits `[e, e + l)` of `w` clear: `Π_b eq(x_b, y_{e+b})`, `l` products per distinct `(e, l)`),
  **4 strided** (any other stride, e.g. `Q_link`'s stream reads at stride 13, or strides that are not one flat
  stride: per iteration until WP STR's carry kind; exported as `REST` lines).
  `mkCls … loops` finds the templates (an entry at iteration 0, its strides from the unit steps of each
  dimension, every iteration present with the same coefficient); every other entry of a loop's slots is `rest`.
-/

set_option autoImplicit false

namespace Lvm6.Phi

open Lvm Lvm.Loop Lvm.Typed Lvm6.LayI

/-- A template entry: matrix `o`, slot offset `i`, word kind `d` (`0` same instance, `1` previous, `2` fixed),
word `w` (offset, or the word itself at `d = 2`), coefficient `c`. -/
structure CEnt where
  o : ℕ
  i : ℕ
  d : ℕ
  w : ℕ
  c : FE2
  /-- LAY3: `log₂` of the word stride of an aligned external (`d = 3`). -/
  s : ℕ := 0
  deriving Inhabited

/-- A class: its geometry and its template. -/
structure PCls where
  g : CGeom
  tpl : List CEnt
  deriving Inhabited

/-- **A loop template entry** (LAY3): matrix `o`, constraint rank `r`, word `w + Σ_d ss_d·i_d` at iteration
`jf` (`i = unflat dims jf`), coefficient `c`. -/
structure LEnt where
  o : ℕ
  r : ℕ
  w : ℕ
  ss : List ℕ
  c : FE2
  deriving Inhabited

/-- **A loop class** (LAY3): a loop block's geometry and its template. -/
structure LCls where
  g : LGeom
  tpl : List LEnt
  deriving Inhabited

/-- **The class table of `Φ_Q`**: the classes, the other entries, and the twin words' base (`Lvm6LayI`'s R2);
LAY3: the loop classes. -/
structure PhiCls where
  cls : List PCls
  rest : List EntT
  wb : ℕ
  lcls : List LCls := []
  deriving Inhabited

/-- The entries of instance `j` of a class. -/
def PCls.instEnts (k : PCls) (j : ℕ) : List EntT :=
  k.tpl.filterMap fun e ↦
    let x := k.g.xb + j * 2 ^ k.g.a + e.i
    if e.d = 2 then some ⟨e.o, x, e.w, e.c⟩
    else if e.d = 3 then some ⟨e.o, x, e.w + j * 2 ^ e.s, e.c⟩
    else if e.d ≤ j then some ⟨e.o, x, k.g.yb + (j - e.d) * 2 ^ k.g.b + e.w, e.c⟩ else none

/-- The entries of a class. -/
def PCls.ents (k : PCls) : List EntT := (List.range k.g.n).flatMap k.instEnts

/-- A loop entry's word at iteration `jf`. -/
def LEnt.y (g : LGeom) (e : LEnt) (jf : ℕ) : ℕ := e.w + dot e.ss (unflat g.dims jf)

/-- The entries of a loop class. -/
def LCls.ents (k : LCls) : List EntT :=
  (List.range (2 ^ k.g.l)).flatMap fun jf ↦ k.tpl.map fun e ↦ ⟨e.o, k.g.xb + e.r * 2 ^ k.g.l + jf, e.y k.g jf, e.c⟩

/-- **The expansion of the table.** -/
def PhiCls.ents (T : PhiCls) : List EntT := T.cls.flatMap PCls.ents ++ T.lcls.flatMap LCls.ents ++ T.rest

/-! ## Merging (characteristic 2) -/

/-- A coefficient's key. -/
def ck (c : FE2) : UInt64 × UInt64 := (c.re.val, c.im.val)

/-- `X`. -/
def fX : FE2 := ⟨0, 1⟩

/-- The entries summed by `(o, x, y)`. -/
def mergeE (es : List EntT) : Std.HashMap (ℕ × ℕ × ℕ) FE2 :=
  es.foldl (fun m e ↦ m.insert (e.o, e.x, e.y) (m.getD (e.o, e.x, e.y) 0 + e.c)) {}

/-- The merged entries without zeros. -/
def mergedL (es : List EntT) : List EntT :=
  (mergeE es).fold (fun l k c ↦ if c == 0 then l else ⟨k.1, k.2.1, k.2.2, c⟩ :: l) []

/-! ## The guard -/

/-- A template fits its geometry. -/
def PCls.tplOkB (k : PCls) : Bool :=
  k.tpl.all fun e ↦ decide (e.o < 4) && decide (e.i < 2 ^ k.g.a) && decide (e.d ≤ 3) &&
    (e.d ≥ 2 || decide (e.w < 2 ^ k.g.b)) &&
    (e.d != 3 || (e.w / 2 ^ e.s) % 2 ^ clog2 k.g.n == 0)

/-- The flat strides of a loop's index (`jf` itself): `2^(dims_<d)`. -/
def natSs (dims : List ℕ) : List ℕ := (List.range dims.length).map fun d ↦ 2 ^ (dims.take d).sum

/-- `s` is a power of two. -/
def pow2B (s : ℕ) : Bool := s != 0 && 2 ^ Nat.log2 s == s

/-- The flat stride `f` of a loop entry, if its strides are `f·2^(dims_<d)` on every nonempty dimension. -/
def flatS (g : LGeom) (e : LEnt) : Option ℕ :=
  let ns := natSs g.dims
  let f := match (List.range g.dims.length).find? (fun d ↦ g.dims.getD d 0 != 0) with
    | some d => e.ss.getD d 0 / ns.getD d 1
    | none => 0
  if e.ss.length == g.dims.length &&
      (List.range g.dims.length).all (fun d ↦ g.dims.getD d 0 == 0 || e.ss.getD d 0 == f * ns.getD d 1) then
    some f else none

/-- **A loop entry's kind**: 0 own, 2 fixed word, 3 aligned, 4 strided (module doc). -/
def LEnt.kind (g : LGeom) (e : LEnt) : ℕ :=
  match flatS g e with
  | some 0 => 2
  | some 1 => if e.w % 2 ^ g.l == 0 then 0 else 4
  | some f => if pow2B f && (e.w / f) % 2 ^ g.l == 0 then 3 else 4
  | none => 4

/-- A loop class fits: `dims.sum = l`, `xb` aligned, below `2^xVars`, templates on its ranks, words below
`2^yVars`. -/
def LCls.okB (k : LCls) : Bool :=
  k.g.dims.sum == k.g.l && k.g.xb % 2 ^ (k.g.l + clog2 k.g.nc) == 0 &&
    decide (k.g.xb + k.g.nc * 2 ^ k.g.l ≤ 2 ^ xVars) &&
    k.tpl.all fun e ↦ decide (e.o < 4) && decide (e.r < k.g.nc) && e.ss.length == k.g.dims.length &&
      decide (e.y k.g (2 ^ k.g.l - 1) < 2 ^ yVars)

/-- **The start-up guard**: aligned geometries, fitting templates, and `T.ents` equals `es` after merging
(in characteristic 2: every merged sum of `es ++ T.ents` is zero). -/
def clsOkB (T : PhiCls) (es : List EntT) : Bool :=
  T.cls.all (fun k ↦ k.g.okB && k.tplOkB) && T.lcls.all LCls.okB &&
    (mergeE (es ++ T.ents)).fold (fun ok _ c ↦ ok && c == 0) true

/-! ## The table of a list of entries -/

/-- Where an entry lies in a class: `(instance, template entry)`. -/
def place (g : CGeom) (e : EntT) : Option (ℕ × CEnt) :=
  if e.x < g.xb || g.xb + g.n * 2 ^ g.a ≤ e.x then none else
  let j := (e.x - g.xb) / 2 ^ g.a
  let i := (e.x - g.xb) % 2 ^ g.a
  let y0 := g.yb + j * 2 ^ g.b
  if y0 ≤ e.y && e.y < y0 + 2 ^ g.b then some (j, ⟨e.o, i, 0, e.y - y0, e.c, 0⟩)
  else if 1 ≤ j && y0 - 2 ^ g.b ≤ e.y && e.y < y0 then some (j, ⟨e.o, i, 1, e.y - (y0 - 2 ^ g.b), e.c, 0⟩)
  else some (j, ⟨e.o, i, 2, e.y, e.c, 0⟩)

/-- A template entry's key. -/
def CEnt.key (e : CEnt) : ℕ × ℕ × ℕ × ℕ × UInt64 × UInt64 := (e.o, e.i, e.d, e.w, ck e.c)

/-- The loop holding slot `x`: binary search on the geometries sorted by `xb` (`(xb, top, index)`). -/
def loopAt (srt : Array (ℕ × ℕ × ℕ)) (x : ℕ) : Option ℕ := Id.run do
  let mut lo := 0
  let mut hi := srt.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      let (b, t, k) := srt.getD mid (0, 0, 0)
      if x < b then hi := mid
      else if t ≤ x then lo := mid + 1
      else return some k
  return none

/-- The loop geometries sorted by `xb`, as `(xb, top, index)`. -/
def loopSrt (loops : List LGeom) : Array (ℕ × ℕ × ℕ) :=
  ((List.range loops.length).map fun k ↦
    let g := loops.getD k default
    (g.xb, g.xb + g.nc * 2 ^ g.l, k)).toArray.qsort fun a b ↦ a.1 < b.1

/-- **The loop templates** (LAY3) of merged entries `es` on the loop geometries: per entry at iteration `0`, the
candidate strides from the entries with the same matrix and coefficient at the unit step of each dimension, the
first combination present at every iteration (and not yet taken). Returns the classes and the entries of the
loops' slots left over. -/
def mkLCls (es : List EntT) (loops : List LGeom) : List LCls × List EntT := Id.run do
  let m : Std.HashMap (ℕ × ℕ × ℕ) FE2 := es.foldl (fun m e ↦ m.insert (e.o, e.x, e.y) e.c) {}
  let byS : Std.HashMap (ℕ × ℕ) (List ℕ) := es.foldl (fun m e ↦ m.insert (e.o, e.x) (e.y :: m.getD (e.o, e.x) [])) {}
  let mut used : Std.HashSet (ℕ × ℕ × ℕ) := {}
  let mut out : Array LCls := #[]
  let srt := loopSrt loops
  let mut buck : Array (Array EntT) := Array.replicate loops.length #[]
  for e in es do
    match loopAt srt e.x with
    | some k =>
      let g := loops.getD k default
      if (e.x - g.xb) % 2 ^ g.l == 0 then buck := buck.modify k (·.push e)
    | none => pure ()
  for kk in [0:loops.length] do
    let g := loops.getD kk default
    let n := 2 ^ g.l
    let us := natSs g.dims
    let e0s := buck.getD kk #[]
    let mut tpl : Array LEnt := #[]
    for e in e0s do
      if used.contains (e.o, e.x, e.y) then continue
      -- per dimension: the candidate strides
      let cands : List (List ℕ) := (List.range g.dims.length).map fun d ↦
        if g.dims.getD d 0 == 0 then [0] else
        ((byS.getD (e.o, e.x + us.getD d 0) []).filter fun y ↦
          decide (e.y ≤ y) && m.get? (e.o, e.x + us.getD d 0, y) == some e.c).map (· - e.y)
      let combos : List (List ℕ) := (cands.foldr (fun cs acc ↦ (cs.flatMap fun c ↦ acc.map (c :: ·)).take 16) [[]])
      let ok (ss : List ℕ) : Bool := (List.range n).all fun jf ↦
        let y := e.y + dot ss (unflat g.dims jf)
        m.get? (e.o, e.x + jf, y) == some e.c && !used.contains (e.o, e.x + jf, y)
      match combos.find? ok with
      | some ss =>
        tpl := tpl.push ⟨e.o, (e.x - g.xb) / n, e.y, ss, e.c⟩
        for jf in [0:n] do
          used := used.insert (e.o, e.x + jf, e.y + dot ss (unflat g.dims jf))
      | none => pure ()
    out := out.push ⟨g, tpl.toList⟩
  return (out.toList, es.filter fun e ↦ (loopAt srt e.x).isSome && !used.contains (e.o, e.x, e.y))

/-- **The class table** of the entries `es` for the classes `geo` (twin base `wb`); LAY3: the loop classes of
`loops` (`mkLCls`) and the aligned externals (`d = 3`). -/
def mkCls (es : List EntT) (geo : List CGeom) (wb : ℕ) (loops : List LGeom := []) : PhiCls := Id.run do
  let gs := geo.toArray
  let srt := loopSrt loops
  let inL (x : ℕ) : Bool := (loopAt srt x).isSome
  let ml := mergedL es
  let (lc, lrest) := mkLCls (ml.filter fun e ↦ inL e.x) loops
  let mut per : Array (Array (ℕ × CEnt)) := Array.replicate gs.size #[]
  let mut rest : Array EntT := lrest.toArray
  for e in ml do
    if inL e.x then continue
    match (List.range gs.size).findSome? fun k ↦ (place (gs.getD k default) e).map (k, ·) with
    | some (k, je) => per := per.modify k (·.push je)
    | none => rest := rest.push e
  let mut cls : Array PCls := #[]
  for k in [0:gs.size] do
    let g := gs.getD k default
    let mut cnt : Std.HashMap (ℕ × ℕ × ℕ × ℕ × UInt64 × UInt64) (ℕ × CEnt) := {}
    let mut seen : Std.HashSet (ℕ × ℕ × ℕ × ℕ × ℕ × UInt64 × UInt64) := {}
    for (j, ce) in per.getD k #[] do
      cnt := cnt.insert ce.key ((cnt.getD ce.key (0, ce)).1 + 1, ce)
      seen := seen.insert (j, ce.key)
    -- the majority keys (`d = 1`: among the instances `j ≥ 1`)
    let tpl := cnt.fold (fun l _ v ↦
      let m := if v.2.d = 1 then g.n - 1 else g.n
      if 2 * v.1 > m then v.2 :: l else l) []
    let tk : Std.HashSet (ℕ × ℕ × ℕ × ℕ × UInt64 × UInt64) := tpl.foldl (fun s e ↦ s.insert e.key) {}
    -- LAY3: aligned externals among the other fixed-word entries, grouped by `(o, i, c)`
    let mut grp : Std.HashMap (ℕ × ℕ × UInt64 × UInt64) (FE2 × Array (ℕ × ℕ)) := {}
    if g.n ≥ 2 then
      for (j, ce) in per.getD k #[] do
        if ce.d == 2 && !tk.contains ce.key then
          grp := grp.insert (ce.o, ce.i, ck ce.c) (ce.c, ((grp.getD (ce.o, ce.i, ck ce.c) (ce.c, #[])).2.push (j, ce.w)))
    let mut tpl3 : Array CEnt := #[]
    let mut took : Std.HashSet (ℕ × ℕ × ℕ × ℕ × ℕ × UInt64 × UInt64) := {}
    if g.n ≥ 2 then
      for (key, cjy) in grp.toList do
        let jy := cjy.2
        let js := ((jy.map (·.1)).qsort (· < ·)).toList.eraseDups
        if js.length * 2 ≤ g.n then continue
        let j0 := js.getD 0 0
        let j1 := js.getD 1 0
        let y0s := (jy.filter (·.1 == j0)).map (·.2)
        let y1s := (jy.filter (·.1 == j1)).map (·.2)
        let c : Option FE2 := some cjy.1
        let mut done := false
        for y0 in y0s do
          for y1 in y1s do
            if done then continue
            if !(y0 < y1 && (y1 - y0) % (j1 - j0) == 0) then continue
            let st := (y1 - y0) / (j1 - j0)
            if !(pow2B st && j0 * st ≤ y0) then continue
            let w0 := y0 - j0 * st
            let s := Nat.log2 st
            if (w0 / 2 ^ s) % 2 ^ clog2 g.n != 0 then continue
            let hit := js.filter fun j ↦ jy.any fun p ↦ p.1 == j && p.2 == w0 + j * st
            if 2 * hit.length > g.n then
              tpl3 := tpl3.push ⟨key.1, key.2.1, 3, w0, c.getD 0, s⟩
              for j in hit do
                took := took.insert (j, key.1, key.2.1, 2, w0 + j * st, key.2.2.1, key.2.2.2)
              done := true
    for (j, ce) in per.getD k #[] do
      if !tk.contains ce.key && !took.contains (j, ce.key) then
        rest := rest.push ((PCls.instEnts ⟨g, [ce]⟩ j).headD default)
    for j in [0:g.n] do
      for ce in tpl do
        if (ce.d ≤ j || ce.d = 2) && !seen.contains (j, ce.key) then
          rest := rest.push ((PCls.instEnts ⟨g, [ce]⟩ j).headD default)
      for ce in tpl3 do
        if !took.contains (j, ce.o, ce.i, 2, ce.w + j * 2 ^ ce.s, (ck ce.c).1, (ck ce.c).2) then
          rest := rest.push ((PCls.instEnts ⟨g, [ce]⟩ j).headD default)
    cls := cls.push ⟨g, tpl ++ tpl3.toList⟩
  return ⟨cls.toList, rest.toList, wb, lc⟩

/-! ## One-instance block classes (LAY2) -/

/-- **One-instance block classes** for the loose program slots (LAY2): every aligned `2^A`-slot block below
`L.slotsP` holding the slot of an entry of `es` outside the classes `L.geo`, as a class of one instance (R2 makes
its words the aligned `2^(A+1)` block from `L.wb + 2·xb`). `mkCls` puts an entry in the first geometry whose
slots hold it, so with `L.geo` listed first a block takes only its loose slots' entries; then its local entries
are evaluated off the shared low tables (no per-slot or per-cell table product). Untrusted: `clsOkB` checks. -/
def blockGeo (L : LayI) (es : List EntT) (A : ℕ) : List CGeom := Id.run do
  let gs := (L.geo.map (·.2)).toArray
  let inCls (x : ℕ) : Bool := gs.any fun g ↦ decide (g.xb ≤ x ∧ x < g.xb + g.n * 2 ^ g.a)
  let mut ks : Std.HashSet ℕ := {}
  let mut seen : Std.HashSet ℕ := {}
  for e in es do
    if e.x < L.slotsP && !ks.contains (e.x / 2 ^ A) && !seen.contains e.x then
      seen := seen.insert e.x
      if !inCls e.x then ks := ks.insert (e.x / 2 ^ A)
  let kl := (ks.toArray.qsort (· < ·)).toList
  return kl.map fun k ↦ ⟨k * 2 ^ A, A, L.wb + 2 * (k * 2 ^ A), A + 1, 1⟩

/-! ## The cost model (`V`'s products, R1's cover form) -/

/-- The split `eq` tables of the general entries (PHI-decision §1: `2^11 + 2^11` on the low 22 coordinates,
`2^11 + 2^10` on the 21 word coordinates). -/
def splitTab : ℕ := 7168

/-- Products of affine twin runs: the slots `xs` (sorted) of `W` twins on an affine rule over `v` slot coordinates
(a run's closed-form prefix sums `6v`; a gap of at most 16 slots inside a run is subtracted, 3 products a slot). -/
def costW (v : ℕ) (xs : List ℕ) : ℕ :=
  (xs.foldl (fun (acc : ℕ × Option ℕ) x ↦ match acc.2 with
    | none => (acc.1 + 6 * v, some x)
    | some p => if x ≤ p + 17 then (acc.1 + 3 * (x - p - 1), some x) else (acc.1 + 6 * v, some x)) (0, none)).1

/-- An entry as `(matrix, slot, word, coefficient)`. -/
abbrev Ent4 := ℕ × ℕ × ℕ × FE2

/-- **Twin merging** (R1): the entries grouped by `(o, slot)`; an aligned twin `(y, c)`, `(y + 1, c·X)` (`y` even)
is one item on the cell `(y/2, true)` with coefficient `c` (the factor `(1 + b₀) + X·b₀` is taken out once), any
other word `y` an item on `(y, false)`. Returns `(o, slot, cell, coefficient)`. -/
def twinItems (es : List Ent4) : List (ℕ × ℕ × (ℕ × Bool) × FE2) :=
  let m : Std.HashMap (ℕ × ℕ × ℕ) FE2 := es.foldl (fun m (o, x, y, c) ↦ m.insert (o, x, y) c) {}
  es.filterMap fun (o, x, y, c) ↦
    if y % 2 = 0 && m.get? (o, x, y + 1) == some (c * fX) then some (o, x, (y / 2, true), c)
    else if y % 2 = 1 && (m.get? (o, x, y - 1)).any (fun c' ↦ c' * fX == c) then none
    else some (o, x, (y, false), c)

/-- **The cover-form products** of entries (R1): with `tabs`, one product per distinct slot (`eq` of the slot off
the split tables) and per distinct cell; per matrix, one product per group of a cover of its (slot, cell) edges,
each edge grouped on its side of larger degree (an unproved hint for `V`: any grouping is a permutation of the
sum); one product per coefficient other than `1`. -/
def costCover (tabs : Bool) (es : List Ent4) : ℕ := Id.run do
  let its := twinItems es
  let mut xs : Std.HashSet ℕ := {}
  let mut ys : Std.HashSet (ℕ × Bool) := {}
  let mut dx : Std.HashMap (ℕ × ℕ) ℕ := {}
  let mut dy : Std.HashMap (ℕ × ℕ × Bool) ℕ := {}
  let mut n := 0
  for (o, x, k, c) in its do
    xs := xs.insert x
    ys := ys.insert k
    dx := dx.insert (o, x) (dx.getD (o, x) 0 + 1)
    dy := dy.insert (o, k.1, k.2) (dy.getD (o, k.1, k.2) 0 + 1)
    if c != 1 then n := n + 1
  let mut gx : Std.HashSet (ℕ × ℕ) := {}
  let mut gy : Std.HashSet (ℕ × ℕ × Bool) := {}
  for (o, x, k, _) in its do
    if dx.getD (o, x) 0 ≥ dy.getD (o, k.1, k.2) 0 then gx := gx.insert (o, x) else gy := gy.insert (o, k.1, k.2)
  return (if tabs then xs.size + ys.size else 0) + gx.size + gy.size + n

/-- The `W` twins of the entries on the rule `word = base + 2·slot` (`(1, X)` at `(base + 2x, base + 2x + 1)`):
their slots (sorted), and the other entries. -/
def splitW (base : ℕ) (es : List Ent4) : List ℕ × List Ent4 :=
  let m : Std.HashMap (ℕ × ℕ) FE2 :=
    es.foldl (fun m (o, x, y, c) ↦ if o = 3 then m.insert (x, y) c else m) {}
  let isW (x : ℕ) : Bool := m.get? (x, base + 2 * x) == some 1 && m.get? (x, base + 2 * x + 1) == some fX
  let ws := (es.filterMap fun (o, x, y, _) ↦ if o = 3 && y = base + 2 * x && isW x then some x else none)
  let others := es.filter fun (o, x, y, _) ↦ !(o = 3 && (y = base + 2 * x || y = base + 2 * x + 1) && isW x)
  ((ws.toArray.qsort (· < ·)).toList, others)

/-- **A class's products**: `Σ_j eq(x_j)·eq(y_j)` (`3n` with its `eq` tables), the previous-instance and fixed
sums (`n` each if used), the template's `W` twins as affine runs over `a` coordinates, the cover form of the
instance-relative entries (their slots and cells are low-table lookups), the cover form of the fixed-word entries
with one product per distinct fixed word; LAY3: per stride of the aligned externals one more `n`-term sum, their
cover form with one product per distinct base word. -/
def PCls.cost (k : PCls) : ℕ :=
  let rel := k.tpl.filter (·.d < 2)
  let fix := k.tpl.filter (·.d = 2)
  let al := k.tpl.filter (·.d = 3)
  let alS : Std.HashSet ℕ := al.foldl (fun s e ↦ s.insert e.s) {}
  let alW : Std.HashSet (ℕ × ℕ) := al.foldl (fun s e ↦ s.insert (e.w, e.s)) {}
  let (ws, rel0) := splitW 0 ((rel.filter (·.d = 0)).map fun e ↦ (e.o, e.i, e.w, e.c))
  let rel1 := (rel.filter (·.d = 1)).map fun e ↦ (e.o + 4, e.i, e.w, e.c)
  let fixW : Std.HashSet ℕ := fix.foldl (fun s e ↦ s.insert e.w) {}
  3 * k.g.n + 6 + (if rel1.isEmpty then 0 else k.g.n) + (if fix.isEmpty then 0 else k.g.n) +
    costW k.g.a ws + costCover false (rel0 ++ rel1) +
    costCover false (fix.map fun e ↦ (e.o, e.i, e.w, e.c)) + fixW.size +
    k.g.n * alS.size + costCover false (al.map fun e ↦ (e.o, e.i, e.w, e.c)) + alW.size

/-- **A loop class's products** (LAY3): 6, two per template row (its slot's high bits off the split tables),
per entry one product (two with a coefficient other than `1`), plus by kind: own entries two per distinct word
block `w / 2^l` (the shared `Σ_j eq(x_lo, j)·eq(y_lo, j)` is `phiCost`'s), fixed words one per distinct word,
aligned entries two per distinct base word (the closed-form factors are `phiCost`'s),
strided entries two per iteration (until WP STR's carry kind). -/
def LCls.cost (k : LCls) : ℕ :=
  let rs : Std.HashSet ℕ := k.tpl.foldl (fun s e ↦ s.insert e.r) {}
  let kd := k.tpl.map fun e ↦ (e, e.kind k.g)
  let wOwn : Std.HashSet ℕ := kd.foldl (fun s p ↦ if p.2 = 0 then s.insert (p.1.w / 2 ^ k.g.l) else s) {}
  let wFix : Std.HashSet ℕ := kd.foldl (fun s p ↦ if p.2 = 2 then s.insert p.1.w else s) {}
  let wAl : Std.HashSet ℕ := kd.foldl (fun s p ↦ if p.2 = 3 then s.insert p.1.w else s) {}
  6 + 2 * rs.size + 2 * wOwn.size + wFix.size + 2 * wAl.size +
    (kd.map fun p ↦ 1 + (if p.1.c == 1 then 0 else 1) +
      (if p.2 = 4 then 2 * 2 ^ k.g.l else 0)).sum

/-- The loop classes' shared factors (LAY3): the own sum `Π_{b<l} eq(x_b, y_b)` for the largest `l` (its
prefixes serve every smaller `l`), and per distinct `e` of the aligned entries `Π_{b<l} eq(x_b, y_{e+b})` for the
largest `l` with that `e`. -/
def loopShared (ls : List LCls) : ℕ :=
  let lOwn := ls.foldl (fun m k ↦ if k.tpl.any (fun e ↦ e.kind k.g = 0) then max m k.g.l else m) 0
  let fs : Std.HashMap ℕ ℕ := ls.foldl (fun s k ↦ k.tpl.foldl (fun s e ↦
    if e.kind k.g = 3 then
      let lg := Nat.log2 ((flatS k.g e).getD 1)
      s.insert lg (max (s.getD lg 0) k.g.l)
    else s) s) {}
  lOwn + fs.fold (fun n _ l ↦ n + l) 0

/-- **`Φ_Q`'s products on the class table** (CD-8 bounds it; LAY3: the loop classes and their shared factors): the split tables, the classes' shared low
tables (`2^a`, `2^(b−1)`), the classes, the `W` twins of `rest` on R2's rule as affine runs over the 20 slot
coordinates, the cover form of the other entries. -/
def phiCost (T : PhiCls) : ℕ :=
  let am := T.cls.foldl (fun m k ↦ max m k.g.a) 0
  let bm := T.cls.foldl (fun m k ↦ max m k.g.b) 0
  let (ws, others) := splitW T.wb (T.rest.map fun e ↦ (e.o, e.x, e.y, e.c))
  splitTab + (if T.cls.isEmpty then 0 else 2 ^ am + 2 ^ (bm - 1)) + (T.cls.map PCls.cost).sum +
    (T.lcls.map LCls.cost).sum + loopShared T.lcls + costW xVars ws + costCover true others

end Lvm6.Phi
