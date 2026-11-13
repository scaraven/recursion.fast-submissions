-- New for lvm2 (roll 8 = B1, B1-K): the matrices' entries read through array caches of the layout (`FL`), and the
-- operand classes fitted to them (`deriveTerms`): `LvmWiring`'s `cacheW` and the class check `PhiCache.okB` run on
-- these, natively, once per program.
import LvmWiringKT

/-!
# Fast entries and class fitting

`LvmWiring.instEnts` reads the layout through `List` searches (`Lay.owner?`, `Lay.xchunk?`, `Program.start`): exact,
but quadratic in the block count per entry. `FL` caches the same data in arrays (block starts as prefix sums,
the owners as a sorted interval array, each block's constraint chunks), and `FL.rowEnts`/`FL.auxEnts` compute a
row's entries with the same formulas (**`rowEnts_eq`**, statement in `LvmWiring`, L-A).

**Fitting.** A term's words `ys[jf]` over its row's iterations are fitted, in order, to: an affine map of the
iteration bits (`fitAff`, K1 or K3); a shift on one loop dimension or on the flat index (`fitShift`, K2); a
split into aligned sub-cubes on which the map is affine (`fitSplit`); else points. Every fit is verified on
every iteration, and the class check re-verifies the result, so the fit is a heuristic and not trusted.
-/

set_option autoImplicit false

namespace Lvm.Typed.K

open Lvm.Loop

/-! ## The layout's caches -/

/-- The layout in arrays. -/
structure FL where
  /-- The program. -/
  Q : Program
  /-- The layout. -/
  lay : Lay
  /-- The program's blocks. -/
  qb : Array Block
  /-- Their templates. -/
  tpls : Array (Array Row)
  /-- The layout's block copies. -/
  bl : Array BLay
  /-- `Q.start .K b`, `Q.start .E b`. -/
  stK : Array ℕ
  /-- `Q.start .E b`. -/
  stE : Array ℕ
  /-- Per block and template row, `rank .K t`. -/
  rkK : Array (Array ℕ)
  /-- `rank .E t`. -/
  rkE : Array (Array ℕ)
  /-- The owners of `K` result cells: `(lo, hi, b)` sorted. -/
  ownK : Array (ℕ × ℕ × ℕ)
  /-- The owners of `E` result cells. -/
  ownE : Array (ℕ × ℕ × ℕ)
  /-- The dense and input regions (`lay.dense ++ lay.inp`, in order). -/
  dregs : Array DReg
  /-- Per block (and auxiliary block `nB + k`), its constraint chunks in `lay.xs` order. -/
  xch : Array (Array XChunk)
  /-- Per block, `srcK` as an array. -/
  srcKA : Array (Array CSrc)
  /-- Per block, `srcE` as an array. -/
  srcEA : Array (Array CSrc)
  /-- Per block, `cr` as an array. -/
  crA : Array (Array (Option ℕ))
  /-- The constant regions `(lo, values)` as arrays. -/
  cstA : Array (ℕ × Array FK)

/-- Prefix sums. -/
def psumA (xs : Array ℕ) (a : ℕ) : Array ℕ := Id.run do
  let mut out : Array ℕ := Array.mkEmpty (xs.size + 1)
  let mut s := a
  for x in xs do
    out := out.push s
    s := s + x
  out := out.push s
  return out

/-- **The caches of `(Q, lay)`.** -/
def FL.ofLay (Q : Program) (lay : Lay) : FL :=
  let qb := Q.blocks.toArray
  let tpls := qb.map (·.tpl.toArray)
  let bl := lay.blocks.toArray
  let stK := psumA (qb.map fun B ↦ B.tw .K * B.size) Q.nInK
  let stE := psumA (qb.map fun B ↦ B.tw .E * B.size) Q.nInE
  let rk (τ : Ty) : Array (Array ℕ) := tpls.map fun tp ↦ psumA (tp.map (Row.w τ)) 0
  let own (τ : Ty) : Array (ℕ × ℕ × ℕ) := Id.run do
    let mut out : Array (ℕ × ℕ × ℕ) := #[]
    for b in [0:bl.size] do
      let B := bl.getD b default
      if B.tw τ > 0 then out := out.push (B.st τ, B.st τ + B.tw τ * 2 ^ B.l, b)
    return out
  let nB := bl.size
  let nX := nB + lay.aux.length
  let xch : Array (Array XChunk) := Id.run do
    let mut out : Array (Array XChunk) := Array.replicate nX #[]
    for c in lay.xs do
      if c.blk < nX then out := out.modify c.blk (·.push c)
    return out
  ⟨Q, lay, qb, tpls, bl, stK, stE, rk .K, rk .E, own .K, own .E, (lay.dense ++ lay.inp).toArray, xch,
    bl.map (·.srcK.toArray), bl.map (·.srcE.toArray), bl.map (·.cr.toArray),
    (lay.cst.map fun r ↦ (r.1, r.2.toArray)).toArray⟩

namespace FL

variable (F : FL)

/-- The first owner interval holding `n` (binary search on sorted, disjoint intervals; else linear). -/
def owner (τ : Ty) (n : ℕ) : Option ℕ := Id.run do
  let a := if τ == .K then F.ownK else F.ownE
  let mut lo := 0
  let mut hi := a.size
  let mut guard := a.size + 1
  while lo < hi && guard > 0 do
    let mid := (lo + hi) / 2
    let (l, h, b) := a.getD mid (0, 0, 0)
    if n < l then hi := mid
    else if n ≥ h then lo := mid + 1
    else return some b
    guard := guard - 1
  return none

/-- `lay.cst?`. -/
def cst (n : ℕ) : Option FK :=
  (F.cstA.find? fun r ↦ decide (r.1 ≤ n ∧ n < r.1 + r.2.size)).map fun r ↦ r.2.getD (n - r.1) 0

/-- `lay.dreg?`. -/
def dreg (τ : Ty) (n : ℕ) : Option DReg := F.dregs.find? fun d ↦ d.ty == τ && decide (d.lo ≤ n ∧ n < d.lo + d.n)

/-- `lay.wordD`. -/
def wordD (τ : Ty) (n m : ℕ) : ℕ :=
  match F.dreg τ n with
  | some d => d.word n m
  | none => 0

/-- `lay.wordC`. -/
def wordC (B : BLay) (τ : Ty) (n s jf m : ℕ) : ℕ :=
  match F.dreg τ n with
  | some d => d.word n m
  | none => B.slotWord τ s jf m

/-- `lay.wordK`. -/
def wordK (n : ℕ) : ℕ :=
  match F.owner .K n with
  | some b =>
    let B := F.bl.getD b default
    let off := n - B.stK
    match (F.srcKA.getD b #[]).getD (off % B.twK) default with
    | .slot s => F.wordC B .K n s (off / B.twK) 0
    | .alias tgt => F.wordD .K (tgt.getD (off / B.twK) 0) 0
    | .load _ => 0
  | none => F.wordD .K n 0

/-- `lay.wordE`. -/
def wordE (n m : ℕ) : ℕ :=
  match F.owner .E n with
  | some b =>
    let B := F.bl.getD b default
    let off := n - B.stE
    match (F.srcEA.getD b #[]).getD (off % B.twE) default with
    | .slot s => F.wordC B .E n s (off / B.twE) m
    | .load args => F.wordK ((args.getD m default).at (unflat B.dims (off / B.twE)))
    | .alias _ => 0
  | none => F.wordD .E n m

/-- `lay.cellEnts`. -/
def cellEnts (τ : Ty) (n : ℕ) (w : FE) : List (ℕ × FE) :=
  match τ with
  | .K => match F.cst n with
    | some v => [(F.lay.one, w * FE.ofK v)]
    | none => [(F.wordK n, w)]
  | .E => [(F.wordE n 0, w), (F.wordE n 1, w * FE.y), (F.wordE n 2, w * FE.y * FE.y)]

/-- `lay.slotR` on block `b`'s chunks. -/
def slotR (b r jf : ℕ) : ℕ :=
  match (F.xch.getD b #[]).find? fun c ↦ decide (c.r0 ≤ r ∧ r < c.r0 + c.n) with
  | some c => c.base + (r - c.r0) * 2 ^ c.l + jf
  | none => 0

/-- **The entries of template row `t` of block `b` at iteration `jf`** (`LvmWiring.rowEnts`). -/
def rowEnts (b t jf : ℕ) : List Ent :=
  let Bq := F.qb.getD b default
  let B := F.bl.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => F.slotR b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    F.cellEnts a.ty (a.at j) w
  let ck := F.stK.getD b 0 + Bq.tw .K * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + Bq.tw .E * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := F.cellEnts row.ty (match row.ty with | .K => ck | .E => ce) 1
  match row.op with
  | .muladd => tagE 0 x (arg 0 1) ++ tagE 1 x (arg 1 1) ++ tagE 2 x (arg 2 1) ++ tagE 3 x res
  | .lin k k' => tagE 2 x (arg 0 1 ++ arg 1 (FE.ofK k) ++ [(F.lay.one, FE.ofK k')]) ++ tagE 3 x res
  | .assert0 => tagE 0 x (arg 1 1) ++ tagE 1 x (arg 0 1)
  | .fixmul => tagE 2 x (arg 0 (FE.ofK (F.Q.fixMat j)) ++ arg 1 1) ++ tagE 3 x res
  | _ => []

/-- The entries of row `r` of auxiliary block `k` at iteration `j` (`LvmWiring.auxRowEnts`). -/
def auxEnts (k r j : ℕ) : List Ent :=
  let x := F.slotR (F.bl.size + k) r j
  ((F.lay.aux.getD k default).rows.getD r default).ops.flatMap fun e ↦
    tagE e.1 x (match e.2.1 with
      | .word base stride => [(base + stride * j, e.2.2)]
      | .cell a => F.cellEnts a.ty (a.at [j]) e.2.2
      | .one => [(F.lay.one, e.2.2)])

/-- A source's entries. -/
def srcEnts : TSrc → ℕ → List Ent
  | .row b t, jf => F.rowEnts b t jf
  | .aux k r, j => F.auxEnts k r j

/-- A source's `log₂` iterations. -/
def srcL : TSrc → ℕ
  | .row b _ => (F.qb.getD b default).lsize
  | .aux k _ => (F.lay.aux.getD k default).l

/-! ### Cell words with one owner search (B1-IX-S; `LvmQTypedSWire.cellEntsF_eq`) -/

/-- `owner`'s binary search, structural on the guard (`LvmWiring.fl_bsLoop`'s recursion, without loop state). -/
def bsRec (a : Array (ℕ × ℕ × ℕ)) (n : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | _, _, 0 => none
  | lo, hi, g + 1 =>
    if lo < hi then
      let p := a.getD ((lo + hi) / 2) (0, 0, 0)
      if n < p.1 then bsRec a n lo ((lo + hi) / 2) g
      else if p.2.1 ≤ n then bsRec a n ((lo + hi) / 2 + 1) hi g
      else some p.2.2
    else none

/-- `owner` by `bsRec`. -/
def ownerF (τ : Ty) (n : ℕ) : Option ℕ :=
  let a := if τ == .K then F.ownK else F.ownE
  bsRec a n 0 a.size (a.size + 1)

/-- `wordK` on `ownerF`. -/
def wordKF (n : ℕ) : ℕ :=
  match F.ownerF .K n with
  | some b =>
    let B := F.bl.getD b default
    let off := n - B.stK
    match (F.srcKA.getD b #[]).getD (off % B.twK) default with
    | .slot s => F.wordC B .K n s (off / B.twK) 0
    | .alias tgt => F.wordD .K (tgt.getD (off / B.twK) 0) 0
    | .load _ => 0
  | none => F.wordD .K n 0

/-- The words of an `E` cell's three limbs (`wordE n 0`, `1`, `2`) with one owner search. -/
def wordE3 (n : ℕ) : ℕ × ℕ × ℕ :=
  match F.ownerF .E n with
  | some b =>
    let B := F.bl.getD b default
    let off := n - B.stE
    match (F.srcEA.getD b #[]).getD (off % B.twE) default with
    | .slot s => (F.wordC B .E n s (off / B.twE) 0, F.wordC B .E n s (off / B.twE) 1,
        F.wordC B .E n s (off / B.twE) 2)
    | .load args =>
      let j := unflat B.dims (off / B.twE)
      (F.wordKF ((args.getD 0 default).at j), F.wordKF ((args.getD 1 default).at j),
        F.wordKF ((args.getD 2 default).at j))
    | .alias _ => (0, 0, 0)
  | none => (F.wordD .E n 0, F.wordD .E n 1, F.wordD .E n 2)

/-- `cellEnts` on `wordKF` and `wordE3`. -/
def cellEntsF (τ : Ty) (n : ℕ) (w : FE) : List (ℕ × FE) :=
  match τ with
  | .K => match F.cst n with
    | some v => [(F.lay.one, w * FE.ofK v)]
    | none => [(F.wordKF n, w)]
  | .E =>
    let ws := F.wordE3 n
    let wy := w * FE.y
    [(ws.1, w), (ws.2.1, wy), (ws.2.2, wy * FE.y)]

end FL

/-! ## The entries with the writer counts cached (B1-IX-S)

`FL.rowEnts` recomputes `Block.tw` (a sum over the template) at every entry: quadratic in the template (at P20
blocks of 2,384 and 7,069 template rows took 45 of the enumeration's 51 s). `FLF` adds the blocks' writer
counts as arrays; `FLF.rowEnts` is `FL.rowEnts` with them and the cell words of `FL.cellEntsF` (one owner
search per cell; `LvmQTypedSWire.flf_srcEnts`: the same entries). -/

/-- `FL` with every block's writers per iteration (`Block.tw`) as arrays. -/
structure FLF where
  /-- The caches. -/
  F : FL
  /-- `(qb[b]).tw .K`. -/
  twK : Array ℕ
  /-- `(qb[b]).tw .E`. -/
  twE : Array ℕ

/-- **The caches of `(Q, lay)`, with the writer counts.** -/
def FLF.ofLay (Q : Program) (lay : Lay) : FLF :=
  let F := FL.ofLay Q lay
  ⟨F, F.qb.map (·.tw .K), F.qb.map (·.tw .E)⟩

namespace FLF

variable (G : FLF)

/-- `FL.rowEnts`, the writer counts read from the arrays. -/
def rowEnts (b t jf : ℕ) : List Ent :=
  let F := G.F
  let Bq := F.qb.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => F.slotR b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    F.cellEntsF a.ty (a.at j) w
  let ck := F.stK.getD b 0 + G.twK.getD b 0 * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + G.twE.getD b 0 * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := F.cellEntsF row.ty (match row.ty with | .K => ck | .E => ce) 1
  match row.op with
  | .muladd => tagE 0 x (arg 0 1) ++ tagE 1 x (arg 1 1) ++ tagE 2 x (arg 2 1) ++ tagE 3 x res
  | .lin k k' => tagE 2 x (arg 0 1 ++ arg 1 (FE.ofK k) ++ [(F.lay.one, FE.ofK k')]) ++ tagE 3 x res
  | .assert0 => tagE 0 x (arg 1 1) ++ tagE 1 x (arg 0 1)
  | .fixmul => tagE 2 x (arg 0 (FE.ofK (F.Q.fixMat j)) ++ arg 1 1) ++ tagE 3 x res
  | _ => []

/-- `FL.auxEnts` on `cellEntsF`. -/
def auxEnts (k r j : ℕ) : List Ent :=
  let F := G.F
  let x := F.slotR (F.bl.size + k) r j
  ((F.lay.aux.getD k default).rows.getD r default).ops.flatMap fun e ↦
    tagE e.1 x (match e.2.1 with
      | .word base stride => [(base + stride * j, e.2.2)]
      | .cell a => F.cellEntsF a.ty (a.at [j]) e.2.2
      | .one => [(F.lay.one, e.2.2)])

/-- A source's entries (`FL.srcEnts`). -/
def srcEnts : TSrc → ℕ → List Ent
  | .row b t, jf => G.rowEnts b t jf
  | .aux k r, j => G.auxEnts k r j

end FLF

/-! ## The terms' words in one pass (B1-IX-S) -/

/-- `Σ_k [bit (i + k) of jf]·cs[k]` in one pass (`Aff.at` sums over `List.range` with `getD`: quadratic in the
iteration bits). -/
def affAtGo (jf : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, i => (if jf.testBit i then c else 0) + affAtGo jf cs (i + 1)

/-- `Aff.at` in one pass (`LvmQTypedSWire.aff_atF`). -/
def _root_.Lvm.Typed.Aff.atF (a : Aff) (jf : ℕ) : ℕ := a.y0 + affAtGo jf a.coef 0

/-- `OpClass.at` with `Aff.atF` (`LvmQTypedSWire.opClass_atF`). -/
def _root_.Lvm.Typed.OpClass.atF : OpClass → ℕ → ℕ
  | .aff a, jf => a.atF jf
  | .shift p n sh ini, jf => if (jf / 2 ^ p) % 2 ^ n = 0 then ini.atF jf else sh.atF (jf - 2 ^ p)
  | c, jf => c.at jf

/-- `CTerm.at` with `OpClass.atF` (`LvmQTypedSWire.cterm_atF`). -/
def _root_.Lvm.Typed.CTerm.atF (c : CTerm) (jf : ℕ) : Ent := ⟨c.o, c.x0 + jf, c.cls.atF jf, c.wAt jf⟩

/-! ## Entry counts (they do not depend on the iteration) -/

/-- The entries of a template row. -/
def rowEntCount (r : Row) : ℕ :=
  let a (k : ℕ) : ℕ := (r.args.getD k default).ty.limbs
  match r.op with
  | .muladd => a 0 + a 1 + a 2 + r.ty.limbs
  | .lin .. => a 0 + a 1 + 1 + r.ty.limbs
  | .assert0 => a 1 + a 0
  | .fixmul => a 0 + a 1 + r.ty.limbs
  | _ => 0

/-- The entries of an auxiliary row. -/
def auxEntCount (r : ARow) : ℕ :=
  (r.ops.map fun e ↦ match e.2.1 with
    | .cell a => a.ty.limbs
    | _ => 1).sum

/-! ## Fitting a word sequence to a class -/

/-- The lowest set bit's index. -/
def lowBit (jf : ℕ) : ℕ := Id.run do
  let mut i := 0
  while i < 64 && !jf.testBit i do
    i := i + 1
  return i

/-- An affine fit of `f` on the sub-cube `k0 + [0, 2^a)` (free bits `[0, a)`): `y0 = f k0`,
`coef_i = f(k0 + 2^i) − y0`, verified at every point. -/
def fitAffOn (f : ℕ → ℕ) (k0 a : ℕ) : Option (ℕ × Array ℕ) := Id.run do
  let y0 := f k0
  let mut co : Array ℕ := Array.mkEmpty a
  for i in [0:a] do
    let v := f (k0 + 2 ^ i)
    if v < y0 then return none
    co := co.push (v - y0)
  -- f(k0 + j) = f(k0 + j − lowbit) + coef_lowbit
  let mut vals : Array ℕ := Array.mkEmpty (2 ^ a)
  vals := vals.push y0
  for j in [1:2 ^ a] do
    let lb := lowBit j
    let v := vals.getD (j - 2 ^ lb) 0 + co.getD lb 0
    if f (k0 + j) != v then return none
    vals := vals.push v
  return some (y0, co)

/-- **An affine fit** over the whole cube. -/
def fitAff (ys : Array ℕ) (l : ℕ) : Option Aff :=
  (fitAffOn (fun j ↦ ys.getD j 0) 0 l).map fun (y0, co) ↦ ⟨y0, co.toList⟩

/-- An affine fit on the iterations whose field `[p, p + n)` is `0` (field coefficients `0`). -/
def fitIni (ys : Array ℕ) (l p n : ℕ) : Option Aff := Id.run do
  let y0 := ys.getD 0 0
  let mut co : Array ℕ := #[]
  for i in [0:l] do
    if i ≥ p && i < p + n then co := co.push 0
    else
      let v := ys.getD (2 ^ i) 0
      if v < y0 then return none
      co := co.push (v - y0)
  let a : Aff := ⟨y0, co.toList⟩
  for jf in [0:2 ^ l] do
    if (jf / 2 ^ p) % 2 ^ n == 0 && ys.getD jf 0 != a.atF jf then return none
  return some a

/-- An affine fit of `jf' ↦ ys[jf' + 2^p]` on the iterations whose field is at most `2^n − 2`. -/
def fitSh (ys : Array ℕ) (l p n : ℕ) : Option Aff := Id.run do
  let g (jf' : ℕ) : ℕ := ys.getD (jf' + 2 ^ p) 0
  let y0 := g 0
  let mut co : Array ℕ := #[]
  for i in [0:l] do
    -- bit `i` alone: in the domain unless it is the field's top bit with `n = 1`
    if i ≥ p && i < p + n && 2 ^ (i - p) > 2 ^ n - 2 then co := co.push 0
    else
      let v := g (2 ^ i)
      if v < y0 then return none
      co := co.push (v - y0)
  let a : Aff := ⟨y0, co.toList⟩
  for jf in [0:2 ^ l] do
    if (jf / 2 ^ p) % 2 ^ n != 0 && ys.getD jf 0 != a.atF (jf - 2 ^ p) then return none
  return some a

/-- **A shift fit** on field `[p, p + n)`. -/
def fitShift (ys : Array ℕ) (l p n : ℕ) : Option OpClass :=
  match fitSh ys l p n, fitIni ys l p n with
  | some sh, some ini => some (.shift p n sh ini)
  | _, _ => none

/-- Aligned sub-cubes on which `f` is affine: `(k0, a, y0, coef)` (recursive halving on the high bits; the
recursion is on `a`). -/
def splitParts (f : ℕ → ℕ) (k0 : ℕ) : ℕ → ℕ → Option (List (ℕ × ℕ × ℕ × Array ℕ))
  | a, budget =>
    if budget == 0 then none else
    match fitAffOn f k0 a with
    | some (y0, co) => some [(k0, a, y0, co)]
    | none =>
      match a with
      | 0 => none
      | a' + 1 =>
        match splitParts f k0 a' (budget - 1) with
        | none => none
        | some l1 =>
          match splitParts f (k0 + 2 ^ a') a' (budget - 1 - l1.length) with
          | none => none
          | some l2 => some (l1 ++ l2)

/-- **A split fit** with at most `maxParts` parts. -/
def fitSplit (ys : Array ℕ) (l maxParts : ℕ) : Option OpClass :=
  match splitParts (fun j ↦ ys.getD j 0) 0 l maxParts with
  | none => none
  | some ps =>
    if ps.length > maxParts then none else
    some (.split (ps.map fun (k0, a, y0, co) ↦
      (((List.range l).filter (· ≥ a)).map fun i ↦ (i, k0.testBit i),
        (⟨y0, (List.range l).map fun i ↦ if i < a then co.getD i 0 else 0⟩ : Aff))))

/-- The candidate shift fields of a block: each loop dimension's bits, and the flat index. -/
def fields (dims : List ℕ) : List (ℕ × ℕ) :=
  let l := dims.sum
  let ds := (List.range dims.length).map fun d ↦ ((dims.take d).sum, dims.getD d 0)
  (ds ++ [(0, l)]).filter (fun (pn : ℕ × ℕ) ↦ pn.2 ≥ 1) |>.reverse

/-- **The class of a word sequence**: affine, else a shift on a candidate field, else a split, else points. -/
def fitClass (ys : Array ℕ) (l : ℕ) (flds : List (ℕ × ℕ)) : OpClass :=
  match fitAff ys l with
  | some a => .aff a
  | none =>
    match flds.findSome? fun (p, n) ↦ fitShift ys l p n with
    | some c => c
    | none =>
      match (if l ≥ 4 then fitSplit ys l (2 ^ l / 8) else none) with
      | some c => c
      | none => .point ys.toList

/-! ## The terms -/

/-- The terms of row `s` (`2^l` iterations, `cnt` entries) from an entry function `ents` (as arrays): its entries at
every iteration, fitted entry by entry. -/
def rowTermsG (ents : TSrc → ℕ → Array Ent) (s : TSrc) (l cnt : ℕ) (flds : List (ℕ × ℕ)) : Array CTerm := Id.run do
  if cnt == 0 then return #[]
  let es : Array (Array Ent) := (Array.range (2 ^ l)).map fun jf ↦ ents s jf
  let e0 := es.getD 0 #[]
  let mut out : Array CTerm := Array.mkEmpty cnt
  for k in [0:cnt] do
    let ek := e0.getD k default
    let ys : Array ℕ := es.map fun e ↦ (e.getD k default).y
    let ws : Array FE := es.map fun e ↦ (e.getD k default).c
    let wv : List FE := if ws.all (· == ek.c) then [] else ws.toList
    out := out.push ⟨s, k, l, ek.o, ek.c, ek.x, fitClass ys l flds, wv⟩
  return out

/-- The terms of one row (its entries at every iteration, fitted entry by entry). -/
def FL.rowTerms (F : FL) (s : TSrc) (cnt : ℕ) (flds : List (ℕ × ℕ)) : Array CTerm :=
  rowTermsG (fun s jf ↦ (F.srcEnts s jf).toArray) s (F.srcL s) cnt flds

/-- **The terms** of the program and layout cached in `F`, the entries read from `ents` (as arrays), in the canonical
order (rows, then entry positions). -/
def deriveTermsG (ents : TSrc → ℕ → Array Ent) (F : FL) : Array CTerm := Id.run do
  let mut out : Array CTerm := #[]
  for b in [0:F.qb.size] do
    let Bq := F.qb.getD b default
    let flds := fields Bq.dims
    let tp := F.tpls.getD b #[]
    for t in [0:tp.size] do
      out := out ++ rowTermsG ents (.row b t) (F.srcL (.row b t)) (rowEntCount (tp.getD t default)) flds
  for k in [0:F.lay.aux.length] do
    let A := F.lay.aux.getD k default
    for r in [0:A.rows.length] do
      out := out ++ rowTermsG ents (.aux k r) (F.srcL (.aux k r)) (auxEntCount (A.rows.getD r default)) [(0, A.l)]
  return out

/-- **The terms of `(Q, lay)`**, in the canonical order (rows, then entry positions): `deriveTermsG` on the
entries of `FLF` (B1-IX-S; `LvmQTypedSWire.deriveTerms_eq`: the same terms as on `FL`'s). -/
def deriveTerms (Q : Program) (lay : Lay) : Array CTerm :=
  let G := FLF.ofLay Q lay
  deriveTermsG (fun s jf ↦ (G.srcEnts s jf).toArray) G.F

/-- **The check of the terms against the entries**, by enumeration on the caches: every term is its row's
entry at every iteration. -/
def checkTerms (Q : Program) (lay : Lay) (ts : Array CTerm) : Bool := Id.run do
  let F := FL.ofLay Q lay
  let mut i := 0
  while i < ts.size do
    -- the terms of one row are consecutive: enumerate the row's entries once
    let t0 := ts.getD i default
    let mut j := i
    while j < ts.size && (ts.getD j default).src == t0.src do
      j := j + 1
    for jf in [0:2 ^ t0.l] do
      let es := (F.srcEnts t0.src jf).toArray
      for k in [i:j] do
        let t := ts.getD k default
        if !(es.getD t.idx default == t.at jf) then return false
    i := j
  return true

/-- `checkTerms` on an entry function `ents` (B1-IX-S: `checkTerms Q lay = checkTermsG (FL.ofLay Q lay).srcEnts`,
`LvmQTypedSWire.checkTerms_eqG`). -/
def checkTermsG (ents : TSrc → ℕ → List Ent) (ts : Array CTerm) : Bool := Id.run do
  let mut i := 0
  while i < ts.size do
    let t0 := ts.getD i default
    let mut j := i
    while j < ts.size && (ts.getD j default).src == t0.src do
      j := j + 1
    for jf in [0:2 ^ t0.l] do
      let es := (ents t0.src jf).toArray
      for k in [i:j] do
        let t := ts.getD k default
        if !(es.getD t.idx default == t.at jf) then return false
    i := j
  return true

/-- `checkTermsG` on an entry-array function `ents` and a term evaluation `atF` (`checkTermsG ents =
checkTermsGA (fun s jf ↦ (ents s jf).toArray) CTerm.at`, `LvmQTypedSWire.checkTermsG_eqA`). -/
def checkTermsGA (ents : TSrc → ℕ → Array Ent) (atF : CTerm → ℕ → Ent) (ts : Array CTerm) : Bool := Id.run do
  let mut i := 0
  while i < ts.size do
    let t0 := ts.getD i default
    let mut j := i
    while j < ts.size && (ts.getD j default).src == t0.src do
      j := j + 1
    for jf in [0:2 ^ t0.l] do
      let es := ents t0.src jf
      for k in [i:j] do
        let t := ts.getD k default
        if !(es.getD t.idx default == atF t jf) then return false
    i := j
  return true

/-- **`checkTerms` on `FLF`'s entries** and the one-pass words (B1-IX-S; `LvmQTypedSWire.checkTermsF_eq`: it is
`checkTerms`). -/
def checkTermsF (Q : Program) (lay : Lay) (ts : Array CTerm) : Bool :=
  let G := FLF.ofLay Q lay
  checkTermsGA (fun s jf ↦ (G.srcEnts s jf).toArray) CTerm.atF ts

end Lvm.Typed.K
