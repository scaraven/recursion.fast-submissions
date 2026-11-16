-- New for lvm2 (roll 8 = B1, B1-K; B-DES §1.1 with B1-G0a's corrections 1–2): the layout solver `mkLay` of a
-- LoopIR program: binary-chunked slot regions with iteration bits low, dense regions in cell order to a fixpoint,
-- the `E` space with its three limb copies, the input regions, the `BITS` rows as auxiliary blocks, and the
-- constraint chunks. Adapted from B1-W's probe (§4, §7b) onto `LvmTypedLayout.Lay`.
import LvmWiring

/-!
# The layout solver

* `LSpec`: what the program alone does not say: the input cells' regions and sources (`S_flat`, `σ′`, the `KS`
  aliases, `PUB`, `QLT` virtual; the `BITS` outputs committed), the static `readd`s' targets (QLT), the auxiliary
  word regions and blocks (the `BITS` rows, B1-Q's `bitsAux`, given the regions' bases).
* **`mkLayD Q S dense`**: the layout with the given dense cell intervals. Per block and type, the committed
  writers' slots are split into power-of-two chunks (`chunksOf`, B1-P1P2 §5.1); chunk `(s0, 2^a)` of a block with
  `2^l` iterations holds `2^(a+l)` words, slot `s` at iteration `jf` at `base + (s − s0)·2^l + jf`. `E` chunks
  are packed into an `E` space of `2^e` words, repeated per limb (`m·2^e`); the `E` block's last quarter takes
  small `K` regions. The committed items (the `E` block, the `K` chunks, the dense regions, the `BITS` words and
  outputs) fill one aligned committed region `[0, 2^comLog)` (one claim on `C_main`); the virtual items lie above
  it. Constraint rows: the same chunking on the constraint ranks. Every item is a power of two,
  placed largest first, so every base is aligned.
* **`mkLay Q S`**: the dense intervals to a fixpoint: a read that is not affine through the chunked layout (its
  term fits only points or many sub-cubes) and spans several slots or blocks makes the blocks it reads dense
  (B1-P1P2 §2, choice 1).
* `layStats`: words (committed, dense, padded), slots, the `y` and `x` extents.

The result is checked by `Lay.okB Q` (and the cache by `PhiCache.okB`); the solver is not trusted.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-! ## The specification -/

/-- **The layout's specification** beyond the program. -/
structure LSpec where
  /-- The input `K` cells `[lo, hi)` and their source. -/
  inK : List (ℕ × ℕ × YSrc)
  /-- The targets of block `b`'s template row `t` if it is a static `readd` (QLT), per iteration. -/
  aliasOf : ℕ → ℕ → Option (List ℕ)
  /-- The words of each auxiliary word region (the `BITS` bit words). -/
  auxWords : List ℕ
  /-- The auxiliary blocks (the `BITS` rows), given the regions' bases. -/
  auxOf : (ℕ → ℕ) → List ABlk
  /-- The constant input cells (QLT in `Φ_Q`): `(lo, values)`; no words. -/
  cst : List (ℕ × List FK)
  /-- B1-IX: per input region (`inK`'s order), its row-major lanes (`1`: the cells in order; `R > 1`: cell
  `lo + R·x + l` is lane `l`'s row `x`, each lane its own aligned word region, `DReg.laneBases`). -/
  inLanes : List ℕ := []

instance : Inhabited LSpec := ⟨⟨[], fun _ _ ↦ none, [], fun _ ↦ [], [], []⟩⟩

/-! ## Helpers -/

/-- `⌈log₂ n⌉`. -/
def clog2 (n : ℕ) : ℕ := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- The binary decomposition of `n` slots into chunks `(s0, 2^a)`, largest first. -/
def chunksOf (n : ℕ) : List (ℕ × ℕ) := Id.run do
  let mut out : Array (ℕ × ℕ) := #[]
  let mut s0 := 0
  for i in [0:64] do
    let a := 63 - i
    if (n >>> a) &&& 1 == 1 then
      out := out.push (s0, 2 ^ a)
      s0 := s0 + 2 ^ a
  return out.toList

/-- Sequential placement of power-of-two items, largest first (aligned, no gaps). An item with `hole` set
reserves its last quarter for later smaller items. Returns the bases (by item id) and the extent. -/
def packSeq (items : Array (ℕ × ℕ × Bool)) : Array ℕ × ℕ := Id.run do
  let sorted := items.qsort fun a b ↦ a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1)
  let mut base := Array.replicate (items.foldl (fun m it ↦ max m (it.1 + 1)) 0) 0
  let mut ptr := 0
  let mut hp := 0
  let mut he := 0
  for it in sorted do
    let sz := 2 ^ it.2.1
    if it.2.2 then
      base := base.set! it.1 ptr
      hp := ptr + 3 * (sz / 4)
      he := ptr + sz
      ptr := ptr + sz
    else if hp + sz ≤ he then
      base := base.set! it.1 hp
      hp := hp + sz
    else
      base := base.set! it.1 ptr
      ptr := ptr + sz
  return (base, ptr)

/-- First-fit placement of power-of-two items `(id, log size)`, largest first, into the free intervals `free`
(aligned inside them), else at the top (from `top`, aligned). Returns the bases (by id) and the extent. -/
def packFF (items : Array (ℕ × ℕ)) (free : List (ℕ × ℕ)) (top : ℕ) : Array ℕ × ℕ := Id.run do
  let sorted := items.qsort fun a b ↦ a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
  let mut base := Array.replicate (items.foldl (fun m it ↦ max m (it.1 + 1)) 0) 0
  let mut fr : Array (ℕ × ℕ) := free.toArray
  let mut ptr := top
  for (id, lg) in sorted do
    let sz := 2 ^ lg
    let mut placed := false
    for k in [0:fr.size] do
      if !placed then
        let (a, b) := fr.getD k (0, 0)
        let a' := (a + sz - 1) / sz * sz
        if a' + sz ≤ b then
          base := base.set! id a'
          -- the interval's left gap stays free, the rest shrinks
          fr := (fr.set! k (a' + sz, b)).push (a, a')
          placed := true
    if !placed then
      let a' := (ptr + sz - 1) / sz * sz
      base := base.set! id a'
      if a' > ptr then fr := fr.push (ptr, a')
      ptr := a' + sz
  return (base, ptr)

/-! ## The layout with given dense intervals -/

/-- A `y` item of the solver. -/
inductive YItem where
  /-- Committed chunk `c` of block `b`, type `τ`. -/
  | ch (b : ℕ) (τ : Ty) (c : ℕ)
  /-- Dense interval `k`. -/
  | dn (k : ℕ)
  /-- Input region `k`. -/
  | inp (k : ℕ)
  /-- Lane `l` of input region `k` (`LSpec.inLanes`). -/
  | inpL (k l : ℕ)
  /-- `BITS` table `k`'s bit columns. -/
  | bits (k : ℕ)
  /-- The constant `1`. -/
  | one
  deriving BEq, Inhabited

/-- Solver statistics. -/
structure LayStats where
  /-- Committed words, dense (cells × limbs). -/
  wDense : ℕ
  /-- Committed words, padded (the committed regions' sizes). -/
  wPad : ℕ
  /-- Constraint rows. -/
  rows : ℕ
  /-- Constraint slots (padded). -/
  slots : ℕ
  /-- The `y` extent. -/
  yExt : ℕ
  /-- `log₂` of the committed region. -/
  comLog : ℕ
  /-- The `x` extent. -/
  xExt : ℕ
  /-- `log₂` of the `E` space. -/
  e : ℕ
  deriving Repr, Inhabited

/-- **The layout of `Q` with the dense cell intervals `dints`** (sorted, disjoint `(τ, lo, hi)`). -/
def mkLayD (Q : Program) (S : LSpec) (dints : Array (Ty × ℕ × ℕ)) : Lay × LayStats := Id.run do
  let qb := Q.blocks.toArray
  let nB := qb.size
  let stK := K.psumA (qb.map fun B ↦ B.tw .K * B.size) Q.nInK
  let stE := K.psumA (qb.map fun B ↦ B.tw .E * B.size) Q.nInE
  -- the dense interval of a block's τ results, if any
  let dOf (τ : Ty) (b : ℕ) : Option ℕ :=
    let lo := if τ == .K then stK.getD b 0 else stE.getD b 0
    (List.range dints.size).find? fun k ↦
      let (τ', l, h) := dints.getD k (.K, 0, 0)
      τ' == τ && decide (l ≤ lo ∧ lo < h)
  -- per block: the writers' sources, committed slot counts, constraint ranks
  let mut srcK : Array (List CSrc) := #[]
  let mut srcE : Array (List CSrc) := #[]
  let mut nComK : Array ℕ := #[]
  let mut nComE : Array ℕ := #[]
  let mut crs : Array (List (Option ℕ)) := #[]
  let mut nCon : Array ℕ := #[]
  for b in [0:nB] do
    let B := qb.getD b default
    let mut sK : Array CSrc := #[]
    let mut sE : Array CSrc := #[]
    let mut cr : Array (Option ℕ) := #[]
    let mut nk := 0
    let mut ne := 0
    let mut nc := 0
    let tp := B.tpl.toArray
    for t in [0:tp.size] do
      let r := tp.getD t default
      cr := cr.push (if Row.isCon r then some nc else none)
      if Row.isCon r then nc := nc + 1
      match r.writes with
      | some .K =>
        match r.op, S.aliasOf b t with
        | .readd .., some tg => sK := sK.push (.alias tg)
        | _, _ =>
          sK := sK.push (.slot nk)
          nk := nk + 1
      | some .E =>
        if r.op.kind == .loadE then sE := sE.push (.load r.args)
        else
          sE := sE.push (.slot ne)
          ne := ne + 1
      | none => pure ()
    srcK := srcK.push sK.toList
    srcE := srcE.push sE.toList
    nComK := nComK.push nk
    nComE := nComE.push ne
    crs := crs.push cr.toList
    nCon := nCon.push nc
  -- y items: (id, log size, isE)
  let mut items : Array (YItem × ℕ × Bool) := #[]
  for b in [0:nB] do
    let B := qb.getD b default
    let l := B.lsize
    if (dOf .K b).isNone then
      for (c, (_, n)) in (chunksOf (nComK.getD b 0)).zipIdx.map (fun (x, i) ↦ (i, x)) do
        items := items.push (.ch b .K c, l + clog2 n, false)
    if (dOf .E b).isNone then
      for (c, (_, n)) in (chunksOf (nComE.getD b 0)).zipIdx.map (fun (x, i) ↦ (i, x)) do
        items := items.push (.ch b .E c, l + clog2 n, true)
  for k in [0:dints.size] do
    let (τ, lo, hi) := dints.getD k (.K, 0, 0)
    items := items.push (.dn k, clog2 (hi - lo), τ == .E)
  let inK := S.inK.toArray
  let laneOf (k : ℕ) : ℕ := S.inLanes.getD k 1
  for k in [0:inK.size] do
    let (lo, hi, _) := inK.getD k (0, 0, .com)
    if laneOf k ≤ 1 then items := items.push (.inp k, clog2 (hi - lo), false)
    else
      for l in [0:laneOf k] do
        items := items.push (.inpL k l, clog2 ((hi - lo) / laneOf k), false)
  let auxW := S.auxWords.toArray
  for k in [0:auxW.size] do
    items := items.push (.bits k, clog2 (auxW.getD k 0), false)
  items := items.push (.one, 0, false)
  let virt (it : YItem) : Bool :=
    match it with
    | .inp k => (inK.getD k (0, 0, .com)).2.2 != .com
    | .inpL k _ => (inK.getD k (0, 0, .com)).2.2 != .com
    | .one => true
    | _ => false
  -- the E space
  let eIdx := (List.range items.size).filter fun i ↦ (items.getD i default).2.2
  let (ebase, eext) := packSeq (eIdx.toArray.map fun i ↦ (i, (items.getD i default).2.1, false))
  let e := clog2 eext
  -- the committed region `[0, 2^comLog)`: the E block (id = items.size) and the committed K items; then the
  -- virtual items above it
  let kIdx := (List.range items.size).filter fun i ↦ !(items.getD i default).2.2 && !virt (items.getD i default).1
  let vIdx := (List.range items.size).filter fun i ↦ virt (items.getD i default).1
  -- the E block at 0 (`4·2^e`); the K items first-fit into its free parts: each limb copy's tail past the E
  -- space's extent, and the fourth quarter
  let eTop := if eIdx.isEmpty then 0 else 4 * 2 ^ e
  let eFree : List (ℕ × ℕ) := if eIdx.isEmpty then [] else
    [(eext, 2 ^ e), (2 ^ e + eext, 2 * 2 ^ e), (2 * 2 ^ e + eext, 3 * 2 ^ e), (3 * 2 ^ e, 4 * 2 ^ e)]
  let (cbaseK, cext) := packFF (kIdx.toArray.map fun i ↦ (i, (items.getD i default).2.1)) eFree eTop
  let comLog := clog2 cext
  let (vbase, vext) := packSeq (vIdx.toArray.map fun i ↦ (i, (items.getD i default).2.1, false))
  let yext := 2 ^ comLog + vext
  let eb := 0
  -- limb-m base of item i
  let baseOf (i m : ℕ) : ℕ :=
    if (items.getD i default).2.2 then eb + m * 2 ^ e + ebase.getD i 0
    else if virt (items.getD i default).1 then 2 ^ comLog + vbase.getD i 0 else cbaseK.getD i 0
  let idOf (it : YItem) : ℕ := (List.range items.size).find? (fun i ↦ (items.getD i default).1 == it) |>.getD 0
  -- block layouts
  let mut blocks : Array BLay := #[]
  let mut wPad := 0
  let mut wDense := 0
  for b in [0:nB] do
    let B := qb.getD b default
    let l := B.lsize
    let mkCh (τ : Ty) (n : ℕ) : List RChunk :=
      if (dOf τ b).isSome then [] else
      (chunksOf n).zipIdx.map fun ((s0, m), c) ↦
        let i := idOf (.ch b τ c)
        ⟨s0, m, (List.range τ.limbs).map (baseOf i)⟩
    let chK := mkCh .K (nComK.getD b 0)
    let chE := mkCh .E (nComE.getD b 0)
    wPad := wPad + (chK.map fun c ↦ c.n * 2 ^ l).sum + 3 * (chE.map fun c ↦ c.n * 2 ^ l).sum
    wDense := wDense + (nComK.getD b 0 + 3 * nComE.getD b 0) * 2 ^ l
    blocks := blocks.push ⟨B.dims, stK.getD b 0, stE.getD b 0, B.tw .K, B.tw .E, srcK.getD b [], srcE.getD b [],
      chK, chE, crs.getD b []⟩
  -- dense and input regions
  let dense : List DReg := (List.range dints.size).map fun k ↦
    let (τ, lo, hi) := dints.getD k (.K, 0, 0)
    let i := idOf (.dn k)
    ⟨τ, lo, hi - lo, (List.range τ.limbs).map (baseOf i), 1, []⟩
  for k in [0:dints.size] do
    let (τ, lo, hi) := dints.getD k (.K, 0, 0)
    wPad := wPad + τ.limbs * 2 ^ clog2 (hi - lo)
  let inp : List DReg := (List.range inK.size).map fun k ↦
    let (lo, hi, _) := inK.getD k (0, 0, .com)
    if laneOf k ≤ 1 then ⟨.K, lo, hi - lo, [baseOf (idOf (.inp k)) 0], 1, []⟩
    else
      let lb := (List.range (laneOf k)).map fun l ↦ baseOf (idOf (.inpL k l)) 0
      ⟨.K, lo, hi - lo, [lb.headD 0], laneOf k, lb⟩
  -- the auxiliary blocks (`BITS` rows) on their word regions
  let aux := (S.auxOf fun k ↦ baseOf (idOf (.bits k)) 0).toArray
  for k in [0:auxW.size] do
    wPad := wPad + 2 ^ clog2 (auxW.getD k 0)
    wDense := wDense + auxW.getD k 0
  -- constraint chunks: blocks then auxiliary blocks; x items (id, log size)
  let mut xcs : Array XChunk := #[]
  for b in [0:nB] do
    let l := (qb.getD b default).lsize
    for (r0, n) in chunksOf (nCon.getD b 0) do
      xcs := xcs.push ⟨b, l, r0, n, 0⟩
  for k in [0:aux.size] do
    let A := aux.getD k default
    for (r0, n) in chunksOf A.rows.length do
      xcs := xcs.push ⟨nB + k, A.l, r0, n, 0⟩
  let (xbase, xext) := packSeq ((Array.range xcs.size).map fun i ↦
    let c := xcs.getD i default
    (i, c.l + clog2 c.n, false))
  let xsS := ((Array.range xcs.size).map fun i ↦ { xcs.getD i default with base := xbase.getD i 0 }).qsort
    fun a b ↦ a.base < b.base
  -- y regions: the committed region, then the virtual items
  let ysS := #[(⟨0, comLog, .com⟩ : YReg)] ++ (vIdx.toArray.map (fun i ↦
    let (it, lg, _) := items.getD i default
    (⟨2 ^ comLog + vbase.getD i 0, lg, match it with
      | .inp k => (inK.getD k (0, 0, .com)).2.2
      | .inpL k _ => (inK.getD k (0, 0, .com)).2.2
      | _ => .one⟩ : YReg))).qsort fun a b ↦ a.base < b.base
  let one := baseOf (idOf .one) 0
  let rows := nCon.foldl (· + ·) 0 + (aux.toList.map fun A ↦ A.rows.length * 2 ^ A.l).sum
  let slots := xsS.foldl (fun s c ↦ s + c.n * 2 ^ c.l) 0
  (⟨Q.nInK, Q.nInE, inp, dense, blocks.toList, aux.toList, xsS.toList, one, ysS.toList, S.cst⟩,
    ⟨wDense, wPad, rows, slots, yext, comLog, xext, e⟩)

/-! ## Dense intervals to a fixpoint -/

/-- The argument of entry `idx` of a template row (its operand list position), if the entry is an operand's. -/
def entArg (r : Row) (idx : ℕ) : Option ℕ :=
  let lm (k : ℕ) : ℕ := (r.args.getD k default).ty.limbs
  let walk (ks : List ℕ) : Option ℕ := Id.run do
    let mut acc := 0
    for k in ks do
      if idx < acc + lm k then return some k
      acc := acc + lm k
    return none
  match r.op with
  | .muladd => walk [0, 1, 2]
  | .lin .. => walk [0, 1]
  | .assert0 => walk [1, 0]
  | .fixmul => walk [0, 1]
  | _ => none

/-- Whether a term's class is a poor fit (points or many sub-cubes over at least 16 iterations). -/
def poorFit (t : CTerm) : Bool :=
  t.l ≥ 4 && match t.cls with
    | .point _ => true
    | .split ps => ps.length * 8 > 2 ^ t.l
    | _ => false

/-- The cell intervals of the poorly fitted reads, extended to the whole blocks they touch. -/
def denseInts (Q : Program) (lay : Lay) : Array (Ty × ℕ × ℕ) := Id.run do
  let ts := K.deriveTerms Q lay
  let qb := Q.blocks.toArray
  let F := K.FL.ofLay Q lay
  let mut out : Array (Ty × ℕ × ℕ) := #[]
  for t in ts do
    if !poorFit t then continue
    match t.src with
    | .row b r =>
      let B := qb.getD b default
      let row := B.tpl.getD r default
      match entArg row t.idx with
      | none => pure ()
      | some k =>
        let a := row.args.getD k default
        let lo := a.base
        let hi := a.base + dot a.strides (B.dims.map fun d ↦ 2 ^ d - 1)
        -- whole blocks of the read's type, committed writers only (no `loadE`, no alias)
        match F.owner a.ty lo, F.owner a.ty hi with
        | some b1, some b2 =>
          if b1 == b2 && lo == hi then pure () else
          let B1 := F.bl.getD b1 default
          let B2 := F.bl.getD b2 default
          let allCom := (List.range (b2 + 1 - b1)).all fun i ↦
            ((F.bl.getD (b1 + i) default).src a.ty).all fun s ↦ match s with | .slot _ => true | _ => false
          if allCom then out := out.push (a.ty, B1.st a.ty, B2.st a.ty + B2.tw a.ty * 2 ^ B2.l)
        | _, _ => pure ()
    | .aux .. => pure ()
  return out

/-- Merge intervals (per type, sorted, overlapping or touching merged). -/
def mergeInts (iv : Array (Ty × ℕ × ℕ)) : Array (Ty × ℕ × ℕ) := Id.run do
  let mut out : Array (Ty × ℕ × ℕ) := #[]
  for τ in [Ty.K, Ty.E] do
    let xs := (iv.filter (·.1 == τ)).qsort fun a b ↦ a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)
    for (_, lo, hi) in xs do
      let (τ', _, h') := out.back?.getD (.K, 0, 0)
      if out.size > 0 && τ' == τ && lo < h' then
        out := out.modify (out.size - 1) fun e ↦ (e.1, e.2.1, max e.2.2 hi)
      else out := out.push (τ, lo, hi)
  return out

/-- **The layout of `Q`**: the dense intervals to a fixpoint (at most `rounds`). -/
def mkLayR (Q : Program) (S : LSpec) (rounds : ℕ) : Lay × LayStats × Array (Ty × ℕ × ℕ) := Id.run do
  let mut dints : Array (Ty × ℕ × ℕ) := #[]
  let mut L := mkLayD Q S dints
  for _ in [0:rounds] do
    let m := mergeInts (dints ++ denseInts Q L.1)
    if m == dints then break
    dints := m
    L := mkLayD Q S dints
  return (L.1, L.2, dints)

/-- **The layout of `Q`** (dense intervals to a fixpoint, at most 8 rounds). -/
def mkLay (Q : Program) (S : LSpec) : Lay := (mkLayR Q S 8).1

end Lvm.Typed

namespace Lvm.Typed

/-! ## The dump for the prover (B1-P) -/

open Lvm.Loop

/-- A cell source in the dump: `s <slot>`, `l` (a `loadE`: limb `m` is operand `m`'s `K` word), `a <first target>
<stride>` (an alias; targets listed in full when not affine). -/
def csrcDump : CSrc → String
  | .slot s => s!"s {s}"
  | .load _ => "l"
  | .alias tg => "a " ++ " ".intercalate (tg.map toString)

/-- **The layout as text** (one line per item; `LvmTypedLayout`'s formulas read it): `N nInK nInE one`, `Y base log
src`, `I lo n bases…` (input regions), `D ty lo n bases…` (dense regions), `C lo n` (constant cells), per block
`B b dims… | stK stE twK twE`, `SK`/`SE` its writers' sources, `HK`/`HE s0 n bases…` its chunks, `R` its constraint
ranks, then `X blk l r0 n base` (constraint chunks) and `A k l` + `O o kind args… w` (auxiliary rows). A word of
limb `m` of slot `s` at iteration `jf` is `bases[m] + (s − s0)·2^l + jf`; a constraint at rank `r`, iteration `jf`
is `base + (r − r0)·2^l + jf`. -/
def layDump (lay : Lay) : String := Id.run do
  let ns (l : List ℕ) : String := " ".intercalate (l.map toString)
  let ty (t : Ty) : String := if t == .K then "K" else "E"
  let mut out : Array String := #[s!"N {lay.nInK} {lay.nInE} {lay.one}"]
  for r in lay.yregs do
    out := out.push s!"Y {r.base} {r.log} {repr r.src}"
  for d in lay.inp do
    -- B1-IX: a lane-split region (`lanes > 1`): `I lo n base0 | L lanes laneBase_0 … laneBase_{lanes−1}`
    out := out.push (s!"I {d.lo} {d.n} {ns d.bases}" ++ if d.lanes ≤ 1 then "" else s!" | L {d.lanes} {ns d.laneBases}")
  for d in lay.dense do
    out := out.push s!"D {ty d.ty} {d.lo} {d.n} {ns d.bases}"
  for c in lay.cst do
    out := out.push s!"C {c.1} {c.2.length}"
  for (B, b) in lay.blocks.zipIdx do
    out := out.push s!"B {b} {ns B.dims} | {B.stK} {B.stE} {B.twK} {B.twE}"
    out := out.push ("SK " ++ " ; ".intercalate (B.srcK.map csrcDump))
    out := out.push ("SE " ++ " ; ".intercalate (B.srcE.map csrcDump))
    for c in B.chK do
      out := out.push s!"HK {c.s0} {c.n} {ns c.bases}"
    for c in B.chE do
      out := out.push s!"HE {c.s0} {c.n} {ns c.bases}"
    out := out.push ("R " ++ ns (B.cr.map fun o ↦ o.getD 999999999))
  for c in lay.xs do
    out := out.push s!"X {c.blk} {c.l} {c.r0} {c.n} {c.base}"
  for (A, k) in lay.aux.zipIdx do
    out := out.push s!"A {k} {A.l} {A.rows.length}"
    for r in A.rows do
      for (o, a, w) in r.ops do
        let ad := match a with
          | .word b s => s!"w {b} {s}"
          | .cell a => s!"c {ty a.ty} {a.base} {ns a.strides}"
          | .one => "1"
        out := out.push s!"O {o} {ad} {w.c₀.val} {w.c₁.val} {w.c₂.val}"
      out := out.push "."
  return "\n".intercalate out.toList ++ "\n"

end Lvm.Typed
