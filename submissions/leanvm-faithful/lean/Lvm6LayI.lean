-- New for lvm6 (WP LAY): the node circuit's layout under PHI-decision R2 (`cell(x) = x`) and R3 (uniform
-- instance blocks). A layout solver beside `mkLayD`; its result is a `Lay`, checked by `Lay.okB Q`.
import LvmTypedLay
import Std.Data.HashMap

/-!
# The instance layout `mkLayI` (PHI-decision R2, R3)

`mkLayD` splits each block's slots and words into binary chunks, largest first, so the repeated gadget instances
(the 24 Keccak layer checks) land at unrelated places. `mkLayI` lays a program of glue blocks (`dims = []`, the
builder's unrolled programs) by two rules:

* **R2, `cell(x) = x`.** The constraint rows of a block take increasing slots (LAY4: per-block first fit,
  below). A row's `K` results take the words
  `wb + 2x` and `wb + 2x + 1` of the last constraint row's slot `x` (an `E2` twin pair: the first row is the
  constraint row, the second has no slot). So every twin's `W` entries are `(3, x, wb + 2x, 1)` and
  `(3, x, wb + 2x + 1, X)`: one affine rule for the whole program (a closed-form prefix sum in `V`). A check-only
  slot leaves its two words unused (a dummy cell).
* **R3, instance classes.** An `IMark` names the program rows `[lo, hi)` as one instance of class `cls` (one
  generator call). The instances of a class are consecutive in program order; instance `j` of a class of `n`
  takes the slots `xb + j·2^a + i` (`2^a` ≥ its constraint rows, `xb` a multiple of `2^(a + ⌈log₂ n⌉)`), so by R2
  its words are `yb + j·2^b + w` with `yb = wb + 2xb`, `b = a + 1`. A mark's anchors (`subs`) start its later
  parts at slot offsets common to the class (layer 0's first-claim prefix is not the other layers' prefix, and
  without the anchor it would shift layer 0's whole body). An entry inside an instance then depends on `j`
  only through `xb + j·2^a`, `yb + j·2^b`, and `Φ_Q` sums a class as one template (`Lvm6PhiCls`).
* **Loop blocks** (LAY3: season 1's `Q_link`/`Q_sig` loops, `dims ≠ []`, `2^l` iterations): one constraint
  chunk, rank `r` at iteration `jf` at slot `xb + r·2^l + jf` (`xb` aligned to `2^(l + ⌈log₂ nc⌉)`, above the
  glue slots), its committed `K` results in binary chunks of ranks (`chunksOf`), rank `k` of a chunk at word
  `base + (k − s0)·2^l + jf` (each chunk an aligned committed item). `LGeom` records the geometry for `Φ_Q`'s loop
  classes (`Lvm6PhiCls.LCls`). A static `readd` (QLT) is an alias; any other `readd` (the caps') is committed
  (the mini-bus proves it), as in `mkLayD`.
* **Multi-part instances** (LAY3, lever A5): `IMark.ext` lists further row ranges of the same instance, later in
  program order (CC8's glue step `colsGW` for position `k` after `valAtW`'s instance `k`); they are the
  instance's later parts, at the class's common part offsets, so their reads of the earlier part's words are the
  instance's own words.
* **Auxiliary blocks** (the PoW rows): `auxCls k` puts aux block `k` (with its word region `k`) in a class; its rows
  take slots `xb + j·2^a + r` above the program's, its free words `yb + j·2^b + w` in the committed region.

The committed region holds the twin words `[wb, wb + 2^t)`, the auxiliary word regions and the committed inputs
(each item a power of two, aligned, `packSeq`); the virtual inputs and the word `1` lie above it, as in `mkLayD`.
`CGeom` records each class's geometry for the class table of `Φ_Q`. The solver is not trusted: `Lay.okB Q`
checks the result, and the class table's guard (`Lvm6.Phi.clsOkB`) checks the geometry against the entries.

**HARs.** Nothing here touches a generator or a program: `Q` is the same, only the words and slots move. Every
HAR speaks of cells (`Mem`), so no HAR changes; the layout facts the wiring bridge needs are `Lay.okB Q` (as for
`mkLayD`).
-/

set_option autoImplicit false

namespace Lvm6.LayI

open Lvm.Loop Lvm.Typed

/-- **An instance mark**: the program's rows `[lo, hi)` (global template rows, blocks in order) are one
instance of class `cls`. -/
structure IMark where
  /-- The class. -/
  cls : ℕ
  /-- The first row. -/
  lo : ℕ
  /-- The row after the last. -/
  hi : ℕ
  /-- Anchors: the rows (in `(lo, hi)`, increasing) where the instance's parts after the first start. Part `k`
  of every instance of the class starts at the same slot offset (the largest constraint-row count of the earlier
  parts over the instances), so a part that differs between instances does not shift the parts after it. -/
  subs : List ℕ := []
  /-- LAY3: further row ranges `[lo', hi')` of the instance (after `hi`, increasing), each one more part. -/
  ext : List (ℕ × ℕ) := []
  deriving Repr, Inhabited, BEq

/-- **A class's geometry**: instance `j < n` at the slots `xb + j·2^a + i` (`i < 2^a`) and the words
`yb + j·2^b + w` (`w < 2^b`). -/
structure CGeom where
  /-- The first slot. -/
  xb : ℕ
  /-- `log₂` of the slot stride. -/
  a : ℕ
  /-- The first word. -/
  yb : ℕ
  /-- `log₂` of the word stride. -/
  b : ℕ
  /-- The instances. -/
  n : ℕ
  deriving Repr, Inhabited, BEq, DecidableEq

/-- **The geometry is aligned and fits**: `xb`, `yb` are multiples of the class's region sizes, and the regions fit
`2^20 × 2^21` (the template evaluator's factorisation `eq(x_lo, i)·eq(x_mid, j)·eq(x_hi, ·)`). -/
def CGeom.okB (g : CGeom) : Bool :=
  g.xb % 2 ^ (g.a + clog2 g.n) == 0 && g.yb % 2 ^ (g.b + clog2 g.n) == 0 &&
    decide (g.xb + g.n * 2 ^ g.a ≤ 2 ^ xVars) && decide (g.yb + g.n * 2 ^ g.b ≤ 2 ^ yVars)

/-- **A loop block's geometry** (LAY3): block `blk`, `nc` constraint ranks, rank `r` at iteration `jf < 2^l`
at slot `xb + r·2^l + jf`; `dims` the loop dimensions (`dims.sum = l`, the first dimension lowest in `jf`). -/
structure LGeom where
  /-- The block. -/
  blk : ℕ
  /-- The first slot. -/
  xb : ℕ
  /-- `log₂` of the iterations. -/
  l : ℕ
  /-- The loop dimensions. -/
  dims : List ℕ
  /-- The constraint ranks. -/
  nc : ℕ
  deriving Repr, Inhabited, BEq

/-- The solver's result: the layout, the classes' geometries `(class, geometry)`, the twin words' base `wb`, the
program's slot extent and `log₂` of the committed region. -/
structure LayI where
  /-- The layout. -/
  lay : Lay
  /-- The classes' geometries. -/
  geo : List (ℕ × CGeom)
  /-- The twin words' base: a constraint row at slot `x` writes the words `wb + 2x`, `wb + 2x + 1`. -/
  wb : ℕ
  /-- The program's slot extent. -/
  slotsP : ℕ
  /-- `log₂` of the committed region. -/
  comLog : ℕ
  /-- LAY3: the loop blocks' geometries. -/
  loops : List LGeom := []
  deriving Inhabited

/-- Round `x` up to a multiple of `2^k`. -/
def alignUp (x k : ℕ) : ℕ := (x + 2 ^ k - 1) / 2 ^ k * 2 ^ k

/-- **First fit** (LAY4): the lowest start `x ≥ c` aligned to `2^al` with `[x, x + len)` free, in the free
intervals `free` (sorted, disjoint, below `top`; every slot from `top` up is free), scanning from interval `k0`.
Returns the start, the free intervals after the allocation, the new `top`, and the interval to scan from next. -/
def firstFit (free : Array (ℕ × ℕ)) (top c len al k0 : ℕ) : ℕ × Array (ℕ × ℕ) × ℕ × ℕ := Id.run do
  for k in [k0:free.size] do
    let (s, e) := free.getD k (0, 0)
    if c < e then
      let x := alignUp (max s c) al
      if x + len ≤ e then
        if x == s then
          if x + len == e then return (x, free.extract 0 k ++ free.extract (k + 1) free.size, top, k)
          else return (x, free.set! k (x + len, e), top, k)
        else
          if x + len == e then return (x, free.set! k (s, x), top, k + 1)
          else return (x, free.extract 0 k ++ #[(s, x), (x + len, e)] ++ free.extract (k + 1) free.size, top, k + 1)
  let x := alignUp (max top c) al
  let fr := if top < x then free.push (top, x) else free
  return (x, fr, x + len, fr.size)

/-- **The instance layout** of `Q` (glue blocks only, no `E` writers): R2 and R3 above, the marks sorted and
disjoint, a class's instances consecutive; `auxCls k` the class of auxiliary block `k` (aux block `k` uses word
region `k`); the committed region at least `2^comLogMin` words. -/
def mkLayI (Q : Program) (S : LSpec) (marks : List IMark) (auxCls : List (Option ℕ)) (comLogMin : ℕ) :
    Except String LayI := do
  let qb := Q.blocks.toArray
  let nB := qb.size
  if !(qb.all fun B ↦ B.tw .E == 0) then throw "mkLayI: an E writer"
  let isLoop (b : ℕ) : Bool := !(qb.getD b default).dims.isEmpty
  -- the program's rows in order: (block, template row, row)
  let mut rows : Array (ℕ × ℕ × Row) := #[]
  for b in [0:nB] do
    let tp := (qb.getD b default).tpl.toArray
    for t in [0:tp.size] do
      rows := rows.push (b, t, tp.getD t default)
  let nR := rows.size
  -- marks: sorted, disjoint, non-empty; a class's instances consecutive; every row in at most one part
  let ms := marks.toArray
  let nCls := (ms.foldl (fun (m : ℕ) (k : IMark) ↦ max m (k.cls + 1)) 0).max
    (auxCls.foldl (fun (m : ℕ) (o : Option ℕ) ↦ match o with | some c => max m (c + 1) | none => m) 0)
  let mut instIx : Array ℕ := #[]
  let mut cnt : Array ℕ := Array.replicate nCls 0
  let mut partMax : Array (Array ℕ) := Array.replicate nCls #[]
  let mut lastM : Array (Option ℕ) := Array.replicate nCls none
  -- the owner of each row: (mark, part)
  let mut own : Array (Option (ℕ × ℕ)) := Array.replicate nR none
  for k in [0:ms.size] do
    let m := ms.getD k default
    if !(m.lo < m.hi && m.hi ≤ nR) then throw s!"mkLayI: mark {k} empty or past the rows"
    if k > 0 && (ms.getD (k - 1) default).hi > m.lo then throw s!"mkLayI: marks {k - 1}, {k} overlap"
    match lastM.getD m.cls none with
    | some k' => if !(k' + 1 == k && (ms.getD k' default).hi == m.lo) then
        throw s!"mkLayI: class {m.cls}'s instances are not consecutive (mark {k})"
    | none => pure ()
    lastM := lastM.set! m.cls (some k)
    instIx := instIx.push (cnt.getD m.cls 0)
    cnt := cnt.set! m.cls (cnt.getD m.cls 0 + 1)
    -- the parts: `[lo, subs…, hi)`, then the `ext` ranges
    let cuts := m.lo :: m.subs ++ [m.hi]
    if !(List.range (cuts.length - 1)).all (fun i ↦ cuts.getD i 0 < cuts.getD (i + 1) 0) then
      throw s!"mkLayI: mark {k}'s anchors are not increasing inside it"
    let rgs : List (ℕ × ℕ) := (List.range (cuts.length - 1)).map (fun i ↦ (cuts.getD i 0, cuts.getD (i + 1) 0)) ++
      m.ext
    if !(m.ext.all fun e ↦ decide (e.1 < e.2 ∧ e.2 ≤ nR)) then throw s!"mkLayI: mark {k}'s ext ranges"
    if !(List.range rgs.length).all (fun i ↦ i == 0 || decide ((rgs.getD (i - 1) (0, 0)).2 ≤ (rgs.getD i (0, 0)).1))
      then throw s!"mkLayI: mark {k}'s parts are not increasing"
    for pi in [0:rgs.length] do
      let (lo, hi) := rgs.getD pi (0, 0)
      for g in [lo:hi] do
        if (own.getD g none).isSome then throw s!"mkLayI: row {g} in two parts (mark {k})"
        if isLoop (rows.getD g default).1 then throw s!"mkLayI: mark {k} holds a loop block's row {g}"
        own := own.set! g (some (k, pi))
    let pc := rgs.map fun (lo, hi) ↦
      ((List.range (hi - lo)).filter fun r ↦ Row.isCon (rows.getD (lo + r) default).2.2).length
    let pm := partMax.getD m.cls #[]
    if instIx.getD k 0 > 0 && pm.size != pc.length then throw s!"mkLayI: mark {k}'s parts differ from its class's"
    partMax := partMax.set! m.cls ((Array.range pc.length).map fun i ↦ max (pm.getD i 0) (pc.getD i 0))
  -- part `i`'s slot offset in its class's instances
  let partOff (c i : ℕ) : ℕ := ((partMax.getD c #[]).toList.take i).sum
  let aOf (c : ℕ) : ℕ := clog2 ((partMax.getD c #[]).toList.sum)
  -- slots (R2, R3) and word offsets `2x + k`; loop blocks' rows are laid below
  let mut slotOf : Array ℕ := Array.replicate nR 0
  let mut wordOf : Array ℕ := Array.replicate nR 0
  let mut xb : Array ℕ := Array.replicate nCls 0
  let mut placed : Array Bool := Array.replicate nCls false
  -- LAY4: per-block first fit. `Lay.okB` (`chunksCover`) wants each block's constraint rows at slots increasing
  -- with their rank, so a block keeps a cursor; a class's region (`n·2^a`, aligned to `2^(a + ⌈log₂ n⌉)`) and a
  -- loose row take the lowest free place at or after it, and the alignment gaps one block leaves are free for the
  -- blocks laid after it. A class's instances may straddle consecutive glue blocks (`toProgram` cuts glue at
  -- `2^16` rows), so the runs of consecutive glue blocks are laid whole, in program order, the run with the most
  -- rows first (then by position).
  let bStart : Array ℕ := K.psumA (qb.map fun B ↦ B.tpl.length) 0
  let mut runs : Array (Array ℕ) := #[]
  let mut run : Array ℕ := #[]
  for b in [0:nB] do
    if isLoop b then
      if !run.isEmpty then runs := runs.push run
      run := #[]
    else run := run.push b
  if !run.isEmpty then runs := runs.push run
  let rRows (rn : Array ℕ) : ℕ := rn.foldl (fun n b ↦ n + (qb.getD b default).tpl.length) 0
  let bord := (runs.qsort fun u v ↦ rRows u > rRows v || (rRows u == rRows v && u.getD 0 0 < v.getD 0 0)).flatMap id
  let mut free : Array (ℕ × ℕ) := #[]
  let mut top := 0
  -- the next slot of each (mark, part)
  let mut nxt : Std.HashMap (ℕ × ℕ) ℕ := {}
  for b in bord do
    let mut cur := 0
    let mut hint := 0
    let g0 := bStart.getD b 0
    for g in [g0:g0 + (qb.getD b default).tpl.length] do
      let (_, _, r) := rows.getD g default
      match own.getD g none with
      | some (k, pi) =>
        let m := ms.getD k default
        let a := aOf m.cls
        if !(placed.getD m.cls false) then
          let (x, fr, tp, h) := firstFit free top cur (cnt.getD m.cls 0 * 2 ^ a) (a + clog2 (cnt.getD m.cls 0)) hint
          free := fr
          top := tp
          hint := h
          xb := xb.set! m.cls x
          placed := placed.set! m.cls true
        cur := max cur (xb.getD m.cls 0 + cnt.getD m.cls 0 * 2 ^ a)
        if Row.isCon r then
          let base := xb.getD m.cls 0 + instIx.getD k 0 * 2 ^ a + partOff m.cls pi
          let s := nxt.getD (k, pi) base
          nxt := nxt.insert (k, pi) (s + 1)
          slotOf := slotOf.set! g s
      | none =>
        if Row.isCon r then
          let (x, fr, tp, h) := firstFit free top cur 1 0 hint
          free := fr
          top := tp
          hint := h
          slotOf := slotOf.set! g x
          cur := x + 1
  let xp := top
  let mut used := 0
  let mut lastSlot : Option ℕ := none
  for g in [0:nR] do
    let (b, t, r) := rows.getD g default
    if isLoop b then
      lastSlot := none
      continue
    if Row.isCon r then
      lastSlot := some (slotOf.getD g 0)
      used := 0
    let isAlias := match r.op, S.aliasOf b t with
      | .readd .., some _ => true
      | _, _ => false
    if r.writes == some .K && !isAlias then
      match lastSlot with
      | none => throw s!"mkLayI: a result before the first constraint row (row {g})"
      | some s =>
        if used ≥ 2 then throw s!"mkLayI: a third result at slot {s} (row {g})"
        wordOf := wordOf.set! g (2 * s + used)
        used := used + 1
  let slotsP := xp
  -- the loop blocks: constraint chunks above the glue slots (largest first), committed `K` rank chunks
  let mut lnc : Array ℕ := Array.replicate nB 0
  let mut lnk : Array ℕ := Array.replicate nB 0
  for b in [0:nB] do
    if isLoop b then
      let B := qb.getD b default
      let tp := B.tpl.toArray
      lnc := lnc.set! b (tp.foldl (fun n r ↦ if Row.isCon r then n + 1 else n) 0)
      let mut nk := 0
      for t in [0:tp.size] do
        let r := tp.getD t default
        if r.writes == some .K then
          match r.op, S.aliasOf b t with
          | .readd .., some _ => pure ()
          | _, _ => nk := nk + 1
      lnk := lnk.set! b nk
  let lsz (b : ℕ) : ℕ := (qb.getD b default).lsize + clog2 (lnc.getD b 0)
  let lord := ((List.range nB).filter fun b ↦ isLoop b && lnc.getD b 0 > 0).toArray.qsort
    fun a c ↦ lsz a > lsz c || (lsz a == lsz c && a < c)
  let mut lxb : Array ℕ := Array.replicate nB 0
  let mut xl := slotsP
  for b in lord do
    let x := alignUp xl (lsz b)
    lxb := lxb.set! b x
    xl := x + lnc.getD b 0 * 2 ^ (qb.getD b default).lsize
  let loops : List LGeom := lord.toList.map fun b ↦
    ⟨b, lxb.getD b 0, (qb.getD b default).lsize, (qb.getD b default).dims, lnc.getD b 0⟩
  -- the committed items: the twin words, the auxiliary word regions (per class one item), committed inputs
  let auxW := S.auxWords.toArray
  let ac := auxCls.toArray
  let mut aCnt : Array ℕ := Array.replicate nCls 0
  let mut aMaxW : Array ℕ := Array.replicate nCls 0
  let mut aJ : Array ℕ := #[]
  for k in [0:auxW.size] do
    match ac.getD k none with
    | some c =>
      aJ := aJ.push (aCnt.getD c 0)
      aCnt := aCnt.set! c (aCnt.getD c 0 + 1)
      aMaxW := aMaxW.set! c (max (aMaxW.getD c 0) (auxW.getD k 0))
    | none => aJ := aJ.push 0
  let inK := S.inK.toArray
  let laneOf (k : ℕ) : ℕ := S.inLanes.getD k 1
  let isCom (k : ℕ) : Bool := (inK.getD k (0, 0, .com)).2.2 == .com
  -- item ids: 0 twin words; 1 + c aux class c; 1 + nCls + k loose aux region k; then committed inputs
  let mut citems : Array (ℕ × ℕ × Bool) := #[(0, clog2 (2 * slotsP), false)]
  for c in [0:nCls] do
    if aCnt.getD c 0 > 0 then
      citems := citems.push (1 + c, clog2 (aMaxW.getD c 0) + clog2 (aCnt.getD c 0), false)
  for k in [0:auxW.size] do
    if (ac.getD k none).isNone then citems := citems.push (1 + nCls + k, clog2 (auxW.getD k 0), false)
  let inId (k l : ℕ) : ℕ := 1 + nCls + auxW.size + 64 * k + l
  let mut vitems : Array (ℕ × ℕ × Bool) := #[]
  for k in [0:inK.size] do
    let (lo, hi, _) := inK.getD k (0, 0, .com)
    let ls := laneOf k
    for l in [0:max ls 1] do
      let it := (inId k l, clog2 ((hi - lo) / max ls 1), false)
      if isCom k then citems := citems.push it else vitems := vitems.push it
  let oneId := inId inK.size 0
  vitems := vitems.push (oneId, 0, false)
  -- LAY3: the loop blocks' committed `K` rank chunks (item `loopId b c`)
  let loopId (b c : ℕ) : ℕ := inId (inK.size + 1 + b) c
  for b in lord do
    let l := (qb.getD b default).lsize
    for (c, (_, n)) in (chunksOf (lnk.getD b 0)).zipIdx.map (fun (x, i) ↦ (i, x)) do
      citems := citems.push (loopId b c, l + clog2 n, false)
  let (cbase, cext) := packSeq citems
  let comLog := max comLogMin (clog2 cext)
  let (vbase, _) := packSeq vitems
  let vb (i : ℕ) : ℕ := 2 ^ comLog + vbase.getD i 0
  let wb := cbase.getD 0 0
  let auxBase (k : ℕ) : ℕ := match ac.getD k none with
    | some c => cbase.getD (1 + c) 0 + aJ.getD k 0 * 2 ^ clog2 (aMaxW.getD c 0)
    | none => cbase.getD (1 + nCls + k) 0
  let inBase (k l : ℕ) : ℕ := if isCom k then cbase.getD (inId k l) 0 else vb (inId k l)
  -- the blocks: sources, constraint ranks, word chunks; the constraint chunks
  let stK := K.psumA (qb.map fun B ↦ B.tw .K * B.size) Q.nInK
  let stE := K.psumA (qb.map fun B ↦ B.tw .E * B.size) Q.nInE
  let mut blocks : Array BLay := #[]
  let mut xcs : Array XChunk := #[]
  let mut g := 0
  for b in [0:nB] do
    let B := qb.getD b default
    let tp := B.tpl.toArray
    if isLoop b then
      -- LAY3: a loop block (one constraint chunk, the committed ranks in binary chunks)
      let l := B.lsize
      let mut crL : Array (Option ℕ) := #[]
      let mut sKL : Array CSrc := #[]
      let mut nc := 0
      let mut nk := 0
      for t in [0:tp.size] do
        let r := tp.getD t default
        crL := crL.push (if Row.isCon r then some nc else none)
        if Row.isCon r then nc := nc + 1
        if r.writes == some .K then
          match r.op, S.aliasOf b t with
          | .readd .., some tg => sKL := sKL.push (.alias tg)
          | _, _ =>
            sKL := sKL.push (.slot nk)
            nk := nk + 1
      let chL : List RChunk := (chunksOf nk).zipIdx.map fun ((s0, n), c) ↦ ⟨s0, n, [cbase.getD (loopId b c) 0]⟩
      if nc > 0 then xcs := xcs.push ⟨b, l, 0, nc, lxb.getD b 0⟩
      blocks := blocks.push ⟨B.dims, stK.getD b 0, stE.getD b 0, B.tw .K, B.tw .E, sKL.toList, [], chL, [],
        crL.toList⟩
      g := g + tp.size
      continue
    let mut cr : Array (Option ℕ) := #[]
    let mut sK : Array CSrc := #[]
    let mut ch : Array RChunk := #[]
    let mut ncon := 0
    let mut nk := 0
    let mut xr0 := 0
    let mut xbs := 0
    let mut xn := 0
    let mut cs0 := 0
    let mut cbw := 0
    let mut cn := 0
    for t in [0:tp.size] do
      let r := tp.getD t default
      if Row.isCon r then
        cr := cr.push (some ncon)
        let s := slotOf.getD g 0
        if xn > 0 && xbs + xn == s then xn := xn + 1
        else
          if xn > 0 then xcs := xcs.push ⟨b, 0, xr0, xn, xbs⟩
          xr0 := ncon
          xbs := s
          xn := 1
        ncon := ncon + 1
      else cr := cr.push none
      if r.writes == some .K then
        match r.op, S.aliasOf b t with
        | .readd .., some tg => sK := sK.push (.alias tg)
        | _, _ =>
          sK := sK.push (.slot nk)
          let w := wb + wordOf.getD g 0
          if cn > 0 && cbw + cn == w then cn := cn + 1
          else
            if cn > 0 then ch := ch.push ⟨cs0, cn, [cbw]⟩
            cs0 := nk
            cbw := w
            cn := 1
          nk := nk + 1
      g := g + 1
    if xn > 0 then xcs := xcs.push ⟨b, 0, xr0, xn, xbs⟩
    if cn > 0 then ch := ch.push ⟨cs0, cn, [cbw]⟩
    blocks := blocks.push ⟨B.dims, stK.getD b 0, stE.getD b 0, B.tw .K, B.tw .E, sK.toList, [], ch.toList, [],
      cr.toList⟩
  -- the auxiliary blocks on their word regions; their slots above the program's
  let aux := (S.auxOf auxBase).toArray
  if !ac.isEmpty && aux.size != auxW.size then throw "mkLayI: aux blocks and word regions differ"
  let mut aRows : Array ℕ := Array.replicate nCls 0
  for k in [0:aux.size] do
    match ac.getD k none with
    | some c =>
      let A := aux.getD k default
      if A.l != 0 then throw s!"mkLayI: aux block {k} of a class is looped"
      aRows := aRows.set! c (max (aRows.getD c 0) A.rows.length)
    | none => pure ()
  let mut axb : Array (Option ℕ) := Array.replicate nCls none
  let mut xq := xl
  for k in [0:aux.size] do
    let A := aux.getD k default
    match ac.getD k none with
    | some c =>
      let a := clog2 (aRows.getD c 0)
      if (axb.getD c none).isNone then
        let x := alignUp xq (a + clog2 (aCnt.getD c 0))
        xq := x + aCnt.getD c 0 * 2 ^ a
        axb := axb.set! c (some x)
      let base := (axb.getD c none).getD 0
      if A.rows.length > 0 then xcs := xcs.push ⟨nB + k, 0, 0, A.rows.length, base + aJ.getD k 0 * 2 ^ a⟩
    | none =>
      if A.rows.length > 0 then
        let x := alignUp xq A.l
        xcs := xcs.push ⟨nB + k, A.l, 0, A.rows.length, x⟩
        xq := x + A.rows.length * 2 ^ A.l
  let xsS := xcs.qsort fun a b ↦ a.base < b.base
  -- input regions, the word `1`, the word regions
  let inp : List DReg := (List.range inK.size).map fun k ↦
    let (lo, hi, _) := inK.getD k (0, 0, .com)
    if laneOf k ≤ 1 then ⟨.K, lo, hi - lo, [inBase k 0], 1, []⟩
    else
      let lb := (List.range (laneOf k)).map fun l ↦ inBase k l
      ⟨.K, lo, hi - lo, [lb.headD 0], laneOf k, lb⟩
  let mut ys : Array YReg := #[]
  for k in [0:inK.size] do
    let (lo, hi, src) := inK.getD k (0, 0, .com)
    if !isCom k then
      for l in [0:max (laneOf k) 1] do
        ys := ys.push ⟨inBase k l, clog2 ((hi - lo) / max (laneOf k) 1), src⟩
  ys := ys.push ⟨vb oneId, 0, .one⟩
  let ysS := #[(⟨0, comLog, .com⟩ : YReg)] ++ ys.qsort fun a b ↦ a.base < b.base
  -- the classes' geometries: program classes (`yb = wb + 2xb`, `b = a + 1`), then auxiliary classes
  let mut geo : Array (ℕ × CGeom) := #[]
  for c in [0:nCls] do
    if cnt.getD c 0 > 0 then
      geo := geo.push (c, ⟨xb.getD c 0, aOf c, wb + 2 * xb.getD c 0, aOf c + 1, cnt.getD c 0⟩)
    else if aCnt.getD c 0 > 0 then
      geo := geo.push (c, ⟨(axb.getD c none).getD 0, clog2 (aRows.getD c 0), cbase.getD (1 + c) 0,
        clog2 (aMaxW.getD c 0), aCnt.getD c 0⟩)
  let lay : Lay := ⟨Q.nInK, Q.nInE, inp, [], blocks.toList, aux.toList, xsS.toList, vb oneId, ysS.toList, S.cst⟩
  return ⟨lay, geo.toList, wb, slotsP, comLog, loops⟩

end Lvm6.LayI
