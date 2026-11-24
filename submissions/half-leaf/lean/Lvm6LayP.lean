-- New for lvm6 (WP ST-1, STARTUP-decision §2–§3): the layout as data. `LayP` (the layout's parameters, PFW style),
-- its byte codec (LEB128) and lowercase hex, `layOfP`, and the class hints `HintP`. The exporter writes the hex into
-- `Lvm6DataLay*` / `Lvm6DataHint` modules (`def … : String := "…"`); the node decodes them at start-up.
import Lvm6LayI

/-!
# The layout as data (`LayP`, ST-1)

`mkLayI` becomes an exporter-only tool: the exporter encodes the layout it found, the node decodes it. Nothing is
proved about the decoded layout; the guard's `lay.okB Q` decides it, as for `mkLayI`'s result.

* **`BlkP`**: a block's layout without what follows from its order: `dims`, `stK`, `stE`, `twK`, `twE`, per template
  row whether it is a constraint row (`con`; its rank is the number of earlier constraint rows), per `K` and `E`
  result in order `none` (a slot: numbered among the non-alias results) or `some tgt` (an alias), the word chunks.
  **`BlkP.toBLay`**, **`BlkP.ofBLay`** (`none` on a `load` source, which `mkLayI` never makes).
* **`LayP`**: `nInK`, `nInE`, `one`, the input and dense regions, the word regions, the constraint chunks, the
  blocks, and per auxiliary block its word base `auxBase` (the auxiliary blocks themselves and the constants are
  rebuilt from the generators' specifications: `layOfP p aux cst`). **`LayP.ofLay`**, **`layOfP`**, and
  **`LayP.sameB p lay`**: `layOfP p lay.aux lay.cst` agrees with `lay` field by field (the exporter's roundtrip).
* **The codec**: LEB128 natural numbers in a `ByteArray`, lists as length and elements, Booleans packed 8 a byte
  (the constraint-row and alias masks), the aliases' targets after their mask;
  lowercase hex (`toHexStr`, `ofHexStr`). **`LayP.toHex`**, **`LayP.ofHex`**; the decoder fails (`none`) on a short
  or malformed string.
* **`HintP`**: the class hints in the format agreed with PHIV6 for ST-4 (`HCls` over global row ranges, `HLoop` by
  block, `HSRun` by slot range, `HBlk` by slot window, `HGath`, `HBits`, `W` bases), with the same codec. **`writeDataModules`**: the exporter's writer of `def <name><k> : String := "…"` chunk modules and their
  concatenation module.
-/

set_option autoImplicit false

namespace Lvm6.LayData

open Lvm Lvm.Loop Lvm.Typed Lvm6.LayI

/-! ## Parameters -/

/-- **A block's layout parameters.** -/
structure BlkP where
  dims : List ℕ
  stK : ℕ
  stE : ℕ
  twK : ℕ
  twE : ℕ
  /-- Per template row: a constraint row. -/
  con : List Bool
  /-- Per `K` result in order: a slot (`none`) or an alias's targets. -/
  srcK : List (Option (List ℕ))
  /-- Per `E` result in order. -/
  srcE : List (Option (List ℕ))
  chK : List RChunk
  chE : List RChunk
  deriving DecidableEq, Repr, Inhabited

/-- **The layout's parameters.** -/
structure LayP where
  nInK : ℕ
  nInE : ℕ
  one : ℕ
  inp : List DReg
  dense : List DReg
  yregs : List YReg
  xs : List XChunk
  blocks : List BlkP
  /-- The word base of each auxiliary block (its first row's first word operand). -/
  auxBase : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The constraint ranks of a template's rows (`some r` at the `r`-th constraint row). -/
def crOf (con : List Bool) : List (Option ℕ) :=
  (con.foldl (fun (acc : Array (Option ℕ) × ℕ) c ↦ if c then (acc.1.push (some acc.2), acc.2 + 1)
    else (acc.1.push none, acc.2)) (#[], 0)).1.toList

/-- The sources of a block's results (slots numbered among the non-alias results). -/
def srcOf (s : List (Option (List ℕ))) : List CSrc :=
  (s.foldl (fun (acc : Array CSrc × ℕ) o ↦ match o with
    | some t => (acc.1.push (.alias t), acc.2)
    | none => (acc.1.push (.slot acc.2), acc.2 + 1)) (#[], 0)).1.toList

/-- **A block's layout** from its parameters. -/
def BlkP.toBLay (b : BlkP) : BLay :=
  ⟨b.dims, b.stK, b.stE, b.twK, b.twE, srcOf b.srcK, srcOf b.srcE, b.chK, b.chE, crOf b.con⟩

/-- The source list as parameters (`none` on a `load`). -/
def srcP (s : List CSrc) : Option (List (Option (List ℕ))) :=
  s.mapM fun c ↦ match c with
    | .slot _ => some none
    | .alias t => some (some t)
    | .load _ => none

/-- **A block's parameters** (`none` on a `load` source). The roundtrip `sameB` checks the slot numbering. -/
def BlkP.ofBLay (B : BLay) : Option BlkP := do
  let sk ← srcP B.srcK
  let se ← srcP B.srcE
  pure ⟨B.dims, B.stK, B.stE, B.twK, B.twE, B.cr.map Option.isSome, sk, se, B.chK, B.chE⟩

/-- An auxiliary block's word base: its first row's first word operand. -/
def auxBw (b : ABlk) : ℕ :=
  match b.rows.head? with
  | some r => match r.ops.head? with
    | some (_, .word w _, _) => w
    | _ => 0
  | none => 0

/-- **The parameters of a layout.** -/
def LayP.ofLay (lay : Lay) : Except String LayP := do
  let bs ← match lay.blocks.mapM BlkP.ofBLay with
    | some bs => pure bs
    | none => throw "LayP.ofLay: a block has a load source"
  pure ⟨lay.nInK, lay.nInE, lay.one, lay.inp, lay.dense, lay.yregs, lay.xs, bs, lay.aux.map auxBw⟩

/-- **The layout of the parameters**, with the auxiliary blocks and the constants from the generators. -/
def layOfP (p : LayP) (aux : List ABlk) (cst : List (ℕ × List FK)) : Lay :=
  ⟨p.nInK, p.nInE, p.inp, p.dense, p.blocks.map BlkP.toBLay, aux, p.xs, p.one, p.yregs, cst⟩

/-- Entry `k` of an array of word bases (`0` past it). -/
def auxBaseArr (a : Array ℕ) (k : ℕ) : ℕ := a.getD k 0

/-- The word base of auxiliary block `k` (G0: an `Array`, built once per layout, not `List.getD` per block). -/
def auxBaseOfP (p : LayP) : ℕ → ℕ := auxBaseArr p.auxBase.toArray

/-- **The exporter's roundtrip**: the layout rebuilt from `p` (with `lay`'s own auxiliary blocks and constants) is
`lay`, field by field, and `p`'s bases are those of `lay`'s auxiliary blocks. -/
def LayP.sameB (p : LayP) (lay : Lay) : Bool :=
  let l := layOfP p lay.aux lay.cst
  l.nInK == lay.nInK && l.nInE == lay.nInE && l.one == lay.one && l.inp == lay.inp && l.dense == lay.dense &&
    l.yregs == lay.yregs && l.xs == lay.xs && l.blocks == lay.blocks && p.auxBase == lay.aux.map auxBw

/-! ## The codec -/

/-- A byte writer. -/
abbrev W := ByteArray

def wNat (w : W) (n : ℕ) : W := Id.run do
  let mut b := w
  let mut x := n
  for _ in [0:12] do
    if x < 128 then
      return b.push x.toUInt8
    b := b.push ((x % 128) + 128).toUInt8
    x := x / 128
  -- beyond 84 bits: the rest as one more group chain
  for _ in [0:64] do
    if x < 128 then
      return b.push x.toUInt8
    b := b.push ((x % 128) + 128).toUInt8
    x := x / 128
  return b.push 0

def wList {α : Type} (f : W → α → W) (w : W) (l : List α) : W := l.foldl f (wNat w l.length)

def wBools (w : W) (l : List Bool) : W := Id.run do
  let mut b := wNat w l.length
  let a := l.toArray
  for k in [0:(a.size + 7) / 8] do
    let mut v : ℕ := 0
    for i in [0:8] do
      if a.getD (8 * k + i) false then v := v + 2 ^ i
    b := b.push v.toUInt8
  return b

def wOpt {α : Type} (f : W → α → W) (w : W) : Option α → W
  | none => w.push 0
  | some a => f (w.push 1) a

def tyCode : Ty → ℕ | .K => 0 | .E => 1
def srcCode : YSrc → ℕ | .com => 0 | .sflat => 1 | .pub => 2 | .sigma => 3 | .ks => 4 | .qlt => 5 | .one => 6

def wDReg (w : W) (d : DReg) : W :=
  wList wNat (wNat (wList wNat (wNat (wNat (wNat w (tyCode d.ty)) d.lo) d.n) d.bases) d.lanes) d.laneBases
def wYReg (w : W) (r : YReg) : W := wNat (wNat (wNat w r.base) r.log) (srcCode r.src)
def wX (w : W) (c : XChunk) : W := wNat (wNat (wNat (wNat (wNat w c.blk) c.l) c.r0) c.n) c.base
def wR (w : W) (c : RChunk) : W := wList wNat (wNat (wNat w c.s0) c.n) c.bases
/-- A list of naturals as zigzag deltas (alias targets are mostly increasing by small steps). -/
def wDeltas (w : W) (l : List ℕ) : W :=
  (l.foldl (fun (acc : W × ℕ) x ↦ (wNat acc.1 (if x ≥ acc.2 then 2 * (x - acc.2) else 2 * (acc.2 - x) - 1), x))
    (wNat w l.length, 0)).1

/-- Result sources: a packed alias mask, then the aliases' targets in order (as deltas). -/
def wSrc (w : W) (s : List (Option (List ℕ))) : W :=
  wList wDeltas (wBools w (s.map Option.isSome)) (s.filterMap id)

def wBlk (w : W) (b : BlkP) : W :=
  let w := wNat (wNat (wNat (wNat (wList wNat w b.dims) b.stK) b.stE) b.twK) b.twE
  let w := wBools w b.con
  let w := wSrc w b.srcK
  let w := wSrc w b.srcE
  wList wR (wList wR w b.chK) b.chE

/-- **The parameters' bytes** (a format tag `1` first). -/
def LayP.bytes (p : LayP) : ByteArray :=
  let w := wNat (wNat (wNat (wNat ByteArray.empty 1) p.nInK) p.nInE) p.one
  let w := wList wDReg (wList wDReg w p.inp) p.dense
  let w := wList wYReg w p.yregs
  let w := wList wX w p.xs
  let w := wList wBlk w p.blocks
  wList wNat w p.auxBase

/-- A byte reader: the bytes and a position. -/
abbrev R := StateT ℕ (Except String)

def rByte (bs : ByteArray) : R ℕ := do
  let i ← get
  if h : i < bs.size then
    set (i + 1)
    pure bs[i].toNat
  else throw "short"

def rNat (bs : ByteArray) : R ℕ := do
  let mut x : ℕ := 0
  let mut sh : ℕ := 1
  for _ in [0:76] do
    let b ← rByte bs
    if b < 128 then
      return x + sh * b
    x := x + sh * (b - 128)
    sh := sh * 128
  throw "varint"

def rList {α : Type} (f : R α) (bs : ByteArray) : R (List α) := do
  let n ← rNat bs
  let mut out : Array α := Array.mkEmpty n
  for _ in [0:n] do
    out := out.push (← f)
  return out.toList

/-- SU2: the bits read at once (bit `k % 8` of byte `i + k / 8`), the same result and failure as a byte loop. -/
def rBools (bs : ByteArray) : R (List Bool) := do
  let n ← rNat bs
  let i ← get
  let nb := (n + 7) / 8
  if i + nb ≤ bs.size then
    set (i + nb)
    pure ((List.range n).map fun k ↦ (bs.get! (i + k / 8) >>> (k % 8).toUInt8) &&& 1 == 1)
  else throw "short"

def rOpt {α : Type} (f : R α) (bs : ByteArray) : R (Option α) := do
  let t ← rByte bs
  if t == 0 then pure none else some <$> f

def tyOf : ℕ → Ty | 0 => .K | _ => .E
def srcOfCode : ℕ → YSrc
  | 0 => .com | 1 => .sflat | 2 => .pub | 3 => .sigma | 4 => .ks | 5 => .qlt | _ => .one

def rDReg (bs : ByteArray) : R DReg := do
  let ty ← rNat bs
  let lo ← rNat bs
  let n ← rNat bs
  let bases ← rList (rNat bs) bs
  let lanes ← rNat bs
  let lb ← rList (rNat bs) bs
  pure ⟨tyOf ty, lo, n, bases, lanes, lb⟩
def rYReg (bs : ByteArray) : R YReg := do
  let b ← rNat bs
  let l ← rNat bs
  let s ← rNat bs
  pure ⟨b, l, srcOfCode s⟩
def rX (bs : ByteArray) : R XChunk := do
  let blk ← rNat bs
  let l ← rNat bs
  let r0 ← rNat bs
  let n ← rNat bs
  let base ← rNat bs
  pure ⟨blk, l, r0, n, base⟩
def rR (bs : ByteArray) : R RChunk := do
  let s0 ← rNat bs
  let n ← rNat bs
  let b ← rList (rNat bs) bs
  pure ⟨s0, n, b⟩
def rDeltas (bs : ByteArray) : R (List ℕ) := do
  let n ← rNat bs
  let mut out : Array ℕ := Array.mkEmpty n
  let mut prev : ℕ := 0
  for _ in [0:n] do
    let z ← rNat bs
    let x := if z % 2 == 0 then prev + z / 2 else prev - (z + 1) / 2
    out := out.push x
    prev := x
  return out.toList

def rSrc (bs : ByteArray) : R (List (Option (List ℕ))) := do
  let m ← rBools bs
  let al := (← rList (rDeltas bs) bs).toArray
  let mut out : Array (Option (List ℕ)) := Array.mkEmpty m.length
  let mut k := 0
  for b in m do
    if b then
      out := out.push (some (al.getD k []))
      k := k + 1
    else out := out.push none
  if k != al.size then throw "LayP: alias count"
  return out.toList

def rBlk (bs : ByteArray) : R BlkP := do
  let dims ← rList (rNat bs) bs
  let stK ← rNat bs
  let stE ← rNat bs
  let twK ← rNat bs
  let twE ← rNat bs
  let con ← rBools bs
  let sk ← rSrc bs
  let se ← rSrc bs
  let chK ← rList (rR bs) bs
  let chE ← rList (rR bs) bs
  pure ⟨dims, stK, stE, twK, twE, con, sk, se, chK, chE⟩

/-- **The parameters from their bytes.** -/
def LayP.ofBytes (bs : ByteArray) : Except String LayP := do
  let (p, _) ← (do
    let tag ← rNat bs
    if tag != 1 then throw "LayP: format tag"
    let nInK ← rNat bs
    let nInE ← rNat bs
    let one ← rNat bs
    let inp ← rList (rDReg bs) bs
    let dense ← rList (rDReg bs) bs
    let yregs ← rList (rYReg bs) bs
    let xs ← rList (rX bs) bs
    let blocks ← rList (rBlk bs) bs
    let ab ← rList (rNat bs) bs
    pure (⟨nInK, nInE, one, inp, dense, yregs, xs, blocks, ab⟩ : LayP) : R LayP).run 0
  pure p

/-! ## Hex -/

def hexDigit (v : ℕ) : Char := if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)

/-- **Lowercase hex** of bytes. -/
def toHexStr (bs : ByteArray) : String := Id.run do
  let mut s : String := ""
  for i in [0:bs.size] do
    let b := bs.get! i
    s := (s.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))
  return s

def nib (c : UInt8) : Option ℕ :=
  if 48 ≤ c && c ≤ 57 then some (c.toNat - 48) else if 97 ≤ c && c ≤ 102 then some (c.toNat - 87) else none

/-- `ofHexStr`'s loop (SU2: tail-recursive on the bytes left, `none` at the first non-hex character). -/
def ofHexGo (u : ByteArray) : ℕ → ℕ → ByteArray → Option ByteArray
  | 0, _, out => some out
  | fuel + 1, k, out =>
    match nib (u.get! k), nib (u.get! (k + 1)) with
    | some a, some b => ofHexGo u fuel (k + 2) (out.push (16 * a + b).toUInt8)
    | _, _ => none

/-- **Bytes of lowercase hex** (`none` on an odd length or another character). -/
def ofHexStr (s : String) : Option ByteArray :=
  let u := s.toUTF8
  if u.size % 2 != 0 then none else ofHexGo u (u.size / 2) 0 (ByteArray.emptyWithCapacity (u.size / 2))

def LayP.toHex (p : LayP) : String := toHexStr p.bytes

/-- **The parameters from their hex** (the node's start-up decode). -/
def LayP.ofHex (s : String) : Option LayP :=
  match ofHexStr s with
  | some bs => match LayP.ofBytes bs with
    | .ok p => some p
    | .error _ => none
  | none => none

/-! ## Class hints (the HINTS format agreed with PHIV6 for ST-4's `ptOfRows`) -/

/-- A class: instance `j` is the global template rows `[g0 + j·len, g0 + (j+1)·len)`, at the geometry
`xb a yb b` (`n` instances). -/
structure HCls where
  g0 : ℕ
  len : ℕ
  n : ℕ
  xb : ℕ
  a : ℕ
  yb : ℕ
  b : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- A loop class or affine kind: block `blk`'s loop geometry. -/
structure HLoop where
  blk : ℕ
  xb : ℕ
  l : ℕ
  nc : ℕ
  dims : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Strided runs on the slots `[x0, x1)`: `n` iteration bits at slot bit `p`, word stride `R`. -/
structure HSRun where
  x0 : ℕ
  x1 : ℕ
  p : ℕ
  n : ℕ
  R : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- A one-instance block class on the slot window `[xb, xb + 2^A)`. -/
structure HBlk where
  xb : ℕ
  A : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Gathers of block `blk`'s template rows `[r0, r1)` (`2^l` iterations). -/
structure HGath where
  blk : ℕ
  r0 : ℕ
  r1 : ℕ
  l : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- A `BITS`/PoW auxiliary class: aux blocks `[j0, j0 + n)`, `nb` bits. -/
structure HBits where
  blk : ℕ
  j0 : ℕ
  n : ℕ
  nb : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- **The class hints**: per kind its records; `w` the `W` runs' twin bases. -/
structure HintP where
  cls : List HCls
  loops : List HLoop
  sruns : List HSRun
  blks : List HBlk
  gaths : List HGath
  bits : List HBits
  w : List ℕ
  deriving DecidableEq, Repr, Inhabited

def wNats (w : W) (l : List ℕ) : W := l.foldl wNat w

def HintP.bytes (h : HintP) : ByteArray :=
  let w := wNat ByteArray.empty 2
  let w := wList (fun w c ↦ wNats w [c.g0, c.len, c.n, c.xb, c.a, c.yb, c.b]) w h.cls
  let w := wList (fun w c ↦ wList wNat (wNats w [c.blk, c.xb, c.l, c.nc]) c.dims) w h.loops
  let w := wList (fun w c ↦ wNats w [c.x0, c.x1, c.p, c.n, c.R]) w h.sruns
  let w := wList (fun w c ↦ wNats w [c.xb, c.A]) w h.blks
  let w := wList (fun w c ↦ wNats w [c.blk, c.r0, c.r1, c.l]) w h.gaths
  let w := wList (fun w c ↦ wNats w [c.blk, c.j0, c.n, c.nb]) w h.bits
  wList wNat w h.w

def HintP.ofBytes (bs : ByteArray) : Except String HintP := do
  let (h, _) ← (do
    let tag ← rNat bs
    if tag != 2 then throw "HintP: format tag"
    let cls ← rList (do pure (⟨← rNat bs, ← rNat bs, ← rNat bs, ← rNat bs, ← rNat bs, ← rNat bs, ← rNat bs⟩ : HCls)) bs
    let loops ← rList (do
      let blk ← rNat bs
      let xb ← rNat bs
      let l ← rNat bs
      let nc ← rNat bs
      let dims ← rList (rNat bs) bs
      pure (⟨blk, xb, l, nc, dims⟩ : HLoop)) bs
    let sruns ← rList (do pure (⟨← rNat bs, ← rNat bs, ← rNat bs, ← rNat bs, ← rNat bs⟩ : HSRun)) bs
    let blks ← rList (do pure (⟨← rNat bs, ← rNat bs⟩ : HBlk)) bs
    let gaths ← rList (do pure (⟨← rNat bs, ← rNat bs, ← rNat bs, ← rNat bs⟩ : HGath)) bs
    let bits ← rList (do pure (⟨← rNat bs, ← rNat bs, ← rNat bs, ← rNat bs⟩ : HBits)) bs
    let w ← rList (rNat bs) bs
    pure (⟨cls, loops, sruns, blks, gaths, bits, w⟩ : HintP) : R HintP).run 0
  pure h

/-- The loop hints of a solved layout (`L.loops`). The other kinds are the exporter's (`mkClsF`'s decisions). -/
def HintP.loopsOf (L : LayI) : List HLoop := L.loops.map fun g ↦ ⟨g.blk, g.xb, g.l, g.nc, g.dims⟩

def HintP.toHex (h : HintP) : String := toHexStr h.bytes

def HintP.ofHex (s : String) : Option HintP :=
  match ofHexStr s with
  | some bs => match HintP.ofBytes bs with
    | .ok h => some h
    | .error _ => none
  | none => none

/-! ## The data modules -/

/-- **Write `bs` in hex as data modules** `<dir>/<pfx><k>.lean` (`def <name><k> : String := "…"`, at most `chunk`
hex characters each, no imports) and `<dir>/<pfx>.lean` (`def <name> : String := <name>0 ++ …`). Returns the file
names. -/
def writeDataModules (dir pfx name : String) (bs : ByteArray) (chunk : ℕ := 512 * 1024) : IO (List String) := do
  let cb := chunk / 2
  let n := (bs.size + cb - 1) / cb
  let mut files : Array String := #[]
  for k in [0:max n 1] do
    let part := toHexStr (bs.extract (k * cb) (min bs.size ((k + 1) * cb)))
    let f := s!"{dir}/{pfx}{k}.lean"
    IO.FS.writeFile f s!"-- Generated by the lvm6 exporter (ST-1): layout data, lowercase hex. Do not edit.\n\nnamespace Lvm6.Data\n\ndef {name}{k} : String := \"{part}\"\n\nend Lvm6.Data\n"
    files := files.push f
  let imps := String.join ((List.range (max n 1)).map fun k ↦ s!"import {pfx}{k}\n")
  let body := String.intercalate " ++ " ((List.range (max n 1)).map fun k ↦ s!"{name}{k}")
  let f := s!"{dir}/{pfx}.lean"
  IO.FS.writeFile f s!"-- Generated by the lvm6 exporter (ST-1). Do not edit.\n{imps}\nnamespace Lvm6.Data\n\ndef {name} : String := {body}\n\nend Lvm6.Data\n"
  return (files.push f).toList

end Lvm6.LayData
