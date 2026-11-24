-- New for lvm6 (ST-4, STARTUP2 P4): the embedded class table's reader. Untrusted: `phiChk` checks whatever it decodes.
import Lvm6VPhiPT
import Lvm6PhiStrF
import Lvm6PhiCls

/-!
# Reading the embedded class table

The exporter's `.cls` (PHICLS 3) is embedded as lowercase hex (`Lvm6DataPhi`, format PHB 1, `phb.py`):
`varint 0x5048`, `varint 1`; a dictionary (`varint D`, then `D` little-endian 8-byte words); `varint L` lines, each
`varint n` and `n` tokens (`4k + 1`: keyword `k`; `4v`: the number `v`; `4d + 2`: dictionary word `d`).
`PT.ofHex` decodes with index loops (no `StateT`, no `Except`) and builds the table as the bench's `loadPT` does
(`PT.ofLines`, `restH`). No proof: a wrong byte makes `phiChk` false.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-- Keyword `k`'s token value (`0 PHICLS 1 WB 2 CLASSES 3 CLASS 4 LOOPS 5 LOOP 6 GATHERS 7 GATHER 8 SRUNS 9 SRUN
10 REST 11 END`). -/
def kwTok (k : Nat) : Nat := 4611686018427387904 + k

/-- Whether a line starts with keyword `k`. -/
def isKw (l : Array Nat) (k : Nat) : Bool := l.getD 0 0 == kwTok k

/-- A hex digit's value (`0` for any other byte). -/
@[inline] def hexNib (c : UInt8) : UInt8 :=
  if c ≤ 57 then c - 48 else c - 87

/-- `hexToBytes`'s loop (tail-recursive on the bytes left). -/
def hexGo (u : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | fuel + 1, k, out => hexGo u fuel (k + 2) (out.push (hexNib (u.get! k) * 16 + hexNib (u.get! (k + 1))))

/-- **Bytes of lowercase hex** (one tail-recursive pass). -/
def hexToBytes (s : String) : ByteArray :=
  let u := s.toUTF8
  hexGo u (u.size / 2) 0 (ByteArray.emptyWithCapacity (u.size / 2))

/-- A LEB128 varint at `i`: (value, next index). -/
@[inline] def rdVar (b : ByteArray) (i : Nat) : Nat × Nat := Id.run do
  let mut v : UInt64 := 0
  let mut sh : UInt64 := 0
  let mut j := i
  while j < b.size do
    let c := b.get! j
    v := v ||| ((c &&& 127).toUInt64 <<< sh)
    sh := sh + 7
    j := j + 1
    if c < 128 then break
  return (v.toNat, j)

/-- A little-endian 8-byte word at `i`. -/
@[inline] def rdW64 (b : ByteArray) (i : Nat) : Nat := Id.run do
  let mut v : UInt64 := 0
  for k in [0:8] do
    v := v ||| ((b.get! (i + k)).toUInt64 <<< (8 * k).toUInt64)
  return v.toNat

/-- The token loop of `phbLines`: varint bytes from `i` (`v`, `sh` the varint so far), `left` tokens left in the
line `l`; tail-recursive on `fuel` (the bytes left), so its scalars stay unboxed. -/
def phbGo (b : ByteArray) (dict : Array Nat) (nl : Nat) : Nat → Nat → UInt64 → UInt64 → Nat → Array Nat →
    Array (Array Nat) → Array (Array Nat)
  | 0, _, _, _, _, _, out => out
  | fuel + 1, i, v, sh, left, l, out =>
    if out.size ≥ nl || i ≥ b.size then out else
    let c := b.get! i
    let v := v ||| ((c &&& 127).toUInt64 <<< sh)
    if c ≥ 128 then phbGo b dict nl fuel (i + 1) v (sh + 7) left l out
    else if left == 0 then
      if v == 0 then phbGo b dict nl fuel (i + 1) 0 0 0 #[] (out.push #[])
      else phbGo b dict nl fuel (i + 1) 0 0 v.toNat (Array.mkEmpty v.toNat) out
    else
      let tv := if v % 4 == 1 then kwTok (v / 4).toNat
        else if v % 4 == 2 then dict.getD (v / 4).toNat 0 else (v / 4).toNat
      let l := l.push tv
      if left == 1 then phbGo b dict nl fuel (i + 1) 0 0 0 #[] (out.push l)
      else phbGo b dict nl fuel (i + 1) 0 0 (left - 1) l out

/-- **The lines of a PHB 1 byte string** (keywords as `kwTok`). SU2: one tail-recursive pass over the token
bytes, varints in `UInt64` (no `Nat` powers; a varint past 64 bits wraps, which `phiChk` rejects). -/
def phbLines (b : ByteArray) : Array (Array Nat) := Id.run do
  let (_, i0) := rdVar b 0
  let (_, i1) := rdVar b i0
  let (nd, i2) := rdVar b i1
  let mut i := i2
  let mut dict : Array Nat := Array.mkEmpty nd
  for _ in [0:nd] do
    dict := dict.push (rdW64 b i)
    i := i + 8
  let (nl, i3) := rdVar b i
  return phbGo b dict nl (b.size - i3) i3 0 0 0 #[] (Array.mkEmpty nl)

/-- The bench's `mkGK` (a gather kind from loop lines). -/
def mkGKL (l : Nat) (ls : Array (Nat × Nat × Nat × Nat × FE2)) : GK := Id.run do
  let mut rows : Array (Nat × Nat × Nat × Nat) := #[]
  let mut gh : Array Nat := #[]
  let mut go : Array Nat := #[0]
  let mut cw : Array Nat := #[]
  let mut co : Array Nat := #[0]
  let mut lj : Array Nat := #[]
  let mut lk : Array Nat := #[]
  let mut cv : ByteArray := ByteArray.empty
  let mut nv := 0
  let mut cI : Std.HashMap (UInt64 × UInt64) Nat := {}
  let mut q := 0
  while q < ls.size do
    let (x0, o, _) := ls[q]!
    let mut q1 := q
    while q1 < ls.size && ls[q1]!.1 == x0 && ls[q1]!.2.1 == o do q1 := q1 + 1
    let row0 := ls.extract q q1
    let srt := Id.run do
      let mut ok := true
      for j in [1:row0.size] do
        if row0[j]!.2.2.2.1 < row0[j - 1]!.2.2.2.1 then ok := false
      return ok
    let row := if srt then row0 else row0.qsort fun a b => a.2.2.2.1 < b.2.2.2.1
    q := q1
    let g0 := gh.size
    let mut k := 0
    while k < row.size do
      let h := row[k]!.2.2.2.1 / 2048
      gh := gh.push h
      while k < row.size && row[k]!.2.2.2.1 / 2048 == h do
        let y := row[k]!.2.2.2.1
        cw := cw.push (y % 2048)
        while k < row.size && row[k]!.2.2.2.1 == y do
          let c := row[k]!.2.2.2.2
          lj := lj.push row[k]!.2.2.1
          if c == 1 then lk := lk.push 0
          else
            match cI.get? (c.re.val, c.im.val) with
            | some x => lk := lk.push x
            | none =>
              for j in [0:8] do cv := cv.push (c.re.val >>> (8 * j).toUInt64).toUInt8
              for j in [0:8] do cv := cv.push (c.im.val >>> (8 * j).toUInt64).toUInt8
              nv := nv + 1
              cI := cI.insert (c.re.val, c.im.val) nv
              lk := lk.push nv
          k := k + 1
        co := co.push lj.size
      go := go.push cw.size
    rows := rows.push (x0, o, g0, gh.size)
  return ⟨l, rows, gh, go, cw, co, lj, lk, cv⟩

/-- The bench's `recogBits`. -/
def recogBitsL (xb a yb bb n : Nat) (tpl : Array Lvm6.Phi.CEnt) : Option (BKB × Array Lvm6.Phi.CEnt) := Id.run do
  let key (e : Lvm6.Phi.CEnt) : Nat × Nat × Nat × Nat := (e.o, e.i, e.d, e.w)
  let mut cm : Std.HashMap (Nat × Nat × Nat × Nat) FE2 := {}
  for e in tpl do cm := cm.insert (key e) e.c
  let bo := ((tpl.filter fun e => e.i == 0 && e.d == 0 && e.w == 0 && e.c == 1).map (·.o)).toList.eraseDups
  if bo.isEmpty then return none
  let has (o i w : Nat) (c : FE2) : Bool := cm.get? (o, i, 0, w) == some c
  let mut nb := 0
  while nb < 2 ^ (min a bb) && bo.all (fun o => has o nb nb 1) do nb := nb + 1
  if nb < 8 then return none
  let β := Nat.log2 (nb - 1) + 1
  let isB (e : Lvm6.Phi.CEnt) : Bool := e.d == 0 && e.i == e.w && e.w < nb && e.c == 1 && bo.contains e.o
  let cands := tpl.filter fun e => e.d == 0 && e.w == 1 && !isB e
  for c in cands do
    let g := c.c
    if (List.range nb).all fun z => has c.o c.i z (gpw g z) then
      let isW (e : Lvm6.Phi.CEnt) : Bool := e.d == 0 && e.o == c.o && e.i == c.i && e.w < nb && e.c == gpw g e.w
      let L := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1
      return some (⟨xb, a, yb, bb, n, L, β, nb, bo, c.i, c.o, g⟩, tpl.filter fun e => !(isB e || isW e))
  return none

/-! ## SU2: packed keys

`(o, x, y)` with `o < 16`, `x < 2^20`, `y < 2^21` packs into `o·2^41 + x·2^21 + y` (a scalar `Nat`), with an entry
index `< 2^18` below it for sorting (`< 2^63`). Each fast builder checks the bounds and otherwise falls back to the
reference (`mkCov`, `mkRCov`, …). -/

/-- The packed `(o, x, y)`. -/
@[inline] def pk3 (o x y : Nat) : Nat := (o * 1048576 + x) * 2097152 + y

/-- The packing applies (`o < 16`, `x < 2^20`, `y < 2^21`). -/
@[inline] def pk3Ok (o x y : Nat) : Bool := o < 16 && x < 1048576 && y < 2097152

/-- One LSD radix pass on the 11-bit digit at `sh` (stable). -/
def radixPass (a : Array Nat) (sh : Nat) : Array Nat := Id.run do
  let mut cnt : Array Nat := Array.replicate 2049 0
  for v in a do
    let d := (v >>> sh) % 2048
    cnt := cnt.set! (d + 1) (cnt[d + 1]! + 1)
  for d in [0:2048] do
    cnt := cnt.set! (d + 1) (cnt[d + 1]! + cnt[d]!)
  let mut out : Array Nat := Array.replicate a.size 0
  for v in a do
    let d := (v >>> sh) % 2048
    let p := cnt[d]!
    out := out.set! p v
    cnt := cnt.set! d (p + 1)
  return out

/-- **Sort an array of naturals below `2^64`** (LSD radix on 11-bit digits for large arrays, `qsort` below 4096 or
for a larger maximum). -/
def sortNat (a : Array Nat) : Array Nat := Id.run do
  if a.size < 4096 then return a.qsort (· < ·)
  let mx := a.foldl max 0
  if mx ≥ 2 ^ 64 then return a.qsort (· < ·)
  let mut r := a
  let mut sh := 0
  while sh < 64 && mx >>> sh > 0 do
    r := radixPass r sh
    sh := sh + 11
  return r

/-- The first position in `[lo, hi)` of the sorted `ks` whose entry is `≥ t` (bisection, `fuel` steps). -/
def lowerB (ks : Array Nat) (t : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let m := (lo + hi) / 2
      if ks[m]! < t then lowerB ks t fuel (m + 1) hi else lowerB ks t fuel lo m
    else lo

/-- In the sorted `key·2^18 + index` array `ks`: the index of the last entry with key `key` (as a `HashMap` built
in index order would keep it). -/
def lastOf (ks : Array Nat) (key : Nat) : Option Nat :=
  let p := lowerB ks ((key + 1) * 262144) 64 0 ks.size
  if p == 0 then none else
    let k := ks[p - 1]!
    if k / 262144 == key then some (k % 262144) else none

/-- The distinct values of `a`, sorted. -/
def sortDedup (a : Array Nat) : Array Nat := Id.run do
  let s := sortNat a
  let mut out : Array Nat := Array.mkEmpty s.size
  for h : j in [0:s.size] do
    if j == 0 || s[j] != s[j - 1]! then out := out.push s[j]
  return out

/-- `x`'s index in the sorted distinct `a`. -/
@[inline] def idxOfS (a : Array Nat) (x : Nat) : Nat := lowerB a x 64 0 a.size

/-- A lookup table for the sorted distinct `a`: dense (`x - a[0]` ↦ index) when the range is small, else
bisection. -/
structure IdxTab where
  a : Array Nat
  lo : Nat
  dense : Array Nat
  useD : Bool

def IdxTab.mk' (a : Array Nat) : IdxTab :=
  let lo := a.getD 0 0
  let hi := a.back?.getD 0
  if a.size > 0 && hi - lo < 4 * a.size + 4096 then
    let d := Id.run do
      let mut d : Array Nat := Array.replicate (hi - lo + 1) 0
      for h : i in [0:a.size] do
        d := d.set! (a[i] - lo) i
      return d
    ⟨a, lo, d, true⟩
  else ⟨a, lo, #[], false⟩

@[inline] def IdxTab.get (t : IdxTab) (x : Nat) : Nat :=
  if t.useD then t.dense.getD (x - t.lo) 0 else idxOfS t.a x

/-- **`mkCov` on presorted keys** `ks` (`pk3 o x y · 2^18 + i`, sorted) of the entries `es`: the same pairs and
singles; the slot and word tables sorted (not in order of first use), groups by sorting. Same cover up to the
order of the tables and groups. -/
def mkCovS (es : Array EntT) (ks : Array Nat) : Cov := Id.run do
  let mut edges : Array (Array Nat) := Array.replicate 8 #[]
  let mut sgl : Array CSgl := #[]
  let mut skip := false
  for h : q in [0:ks.size] do
    if skip then
      skip := false
    else
      let k := ks[q]
      let e := es[k % 262144]!
      let key := k / 262144
      let pairs := e.c == 1 && e.o < 4 && e.y + 1 < 2097152 &&
        (match ks[q + 1]? with
          | some k' => k' / 262144 == key + 1 && (es[k' % 262144]!).c == xF
          | none => false)
      if pairs then
        let al := e.y % 2 == 0
        let β := 2 * e.o + (if al then 1 else 0)
        let cl := if al then e.y / 2 else (e.y - 1) / 2
        edges := edges.modify β (·.push (e.x * 2097152 + cl))
        skip := true
      else
        sgl := sgl.push ⟨e.o, e.x, e.c, e.y⟩
  let allE := edges.flatten
  let slots := sortDedup (allE.map (· / 2097152))
  let als := sortDedup ((List.range 4).toArray.flatMap fun o => edges[2 * o + 1]!.map (· % 2097152))
  let ods := sortDedup ((List.range 4).toArray.flatMap fun o => edges[2 * o]!.map (· % 2097152))
  let tS := IdxTab.mk' slots
  let tA := IdxTab.mk' als
  let tO := IdxTab.mk' ods
  let mut rowsB : Array (Array CGrp) := #[]
  let mut colsB : Array (Array CGrp) := #[]
  for β in [0:8] do
    let ed := edges[β]!
    let al := β % 2 == 1
    let tC := if al then tA else tO
    -- the edges of a bucket are in `(x, y)` order: slots are runs; words sorted once
    let nr := Id.run do
      let mut c := 0
      for h : j in [0:ed.size] do
        if j == 0 || ed[j] / 2097152 != ed[j - 1]! / 2097152 then c := c + 1
      return c
    let byCl := sortNat ((Array.range ed.size).map fun j => (ed[j]! % 2097152) * 262144 + j)
    let nc := Id.run do
      let mut c := 0
      for h : j in [0:byCl.size] do
        if j == 0 || byCl[j] / 262144 != byCl[j - 1]! / 262144 then c := c + 1
      return c
    let byRow := nr ≤ nc
    let ord := if byRow then (Array.range ed.size).map fun j => (ed[j]! / 2097152) * 262144 + j else byCl
    let mut gs : Array CGrp := #[]
    let mut q := 0
    while q < ord.size do
      let g := ord[q]! / 262144
      let mut mem : Array CMem := #[]
      while q < ord.size && ord[q]! / 262144 == g do
        let v := ed[ord[q]! % 262144]!
        mem := mem.push (if byRow then ⟨tC.get (v % 2097152), v % 2097152⟩
          else ⟨tS.get (v / 2097152), v / 2097152⟩)
        q := q + 1
      gs := gs.push ⟨if byRow then tS.get g else tC.get g, g, mem⟩
    if byRow then
      rowsB := rowsB.push gs; colsB := colsB.push #[]
    else
      rowsB := rowsB.push #[]; colsB := colsB.push gs
  return ⟨slots, als, ods, rowsB, colsB, sgl⟩

/-- The sorted packed keys of `es` (`pk3 o x y · 2^18 + i`). -/
def pkSort (es : Array EntT) : Array Nat := Id.run do
  let mut ks : Array Nat := Array.mkEmpty es.size
  for h : i in [0:es.size] do
    let e := es[i]
    ks := ks.push (pk3 e.o e.x e.y * 262144 + i)
  return sortNat ks

/-- Every entry packs, and there are fewer than `2^18`. -/
def pkAll (es : Array EntT) : Bool := es.size < 262144 && es.all fun e => pk3Ok e.o e.x e.y

/-- **`mkRCov`, packed** (the reference when an entry does not pack): one sort; the `W` lookups by bisection. -/
def mkRCovF (es : Array EntT) (runs : Bool) : RCov := Id.run do
  if !pkAll es then return mkRCov es.toList runs
  let ks := pkSort es
  if !runs then return ⟨FCov.ofCov (mkCovS es ks), #[]⟩
  let cOf (o x y : Nat) : Option FE2 :=
    if pk3Ok o x y then (lastOf ks (pk3 o x y)).map fun i => (es[i]!).c else none
  let isW (x : ℕ) : Bool := cOf 3 x (2 * x) == some 1 && cOf 3 x (2 * x + 1) == some xF
  let ws := sortNat (es.filterMap fun e => if e.o == 3 && e.y == 2 * e.x && isW e.x then some e.x else none)
  let wOut (e : EntT) : Bool := e.o == 3 && (e.y == 2 * e.x || e.y == 2 * e.x + 1) && isW e.x
  let ks' := ks.filter fun k => !wOut es[k % 262144]!
  let mut runs : Array (ℕ × ℕ) := #[]
  for x in ws do
    match runs.back? with
    | some (s, e) => if e == x then runs := runs.pop.push (s, x + 1) else if e < x + 1 then runs := runs.push (x, x + 1)
    | none => runs := runs.push (x, x + 1)
  return ⟨FCov.ofCov (mkCovS es ks'), runs⟩

/-- `recogBitsL` on sorted packed keys `((o·2^12 + i)·4 + d)·2^21 + w` (the reference when an entry does not pack). -/
def recogBitsLF (xb a yb bb n : Nat) (tpl : Array Lvm6.Phi.CEnt) : Option (BKB × Array Lvm6.Phi.CEnt) := Id.run do
  let ok (o i d w : Nat) : Bool := o < 16 && i < 4096 && d < 4 && w < 2097152
  if !(tpl.size < 262144 && tpl.all fun e => ok e.o e.i e.d e.w) then return recogBitsL xb a yb bb n tpl
  let key (o i d w : Nat) : Nat := ((o * 4096 + i) * 4 + d) * 2097152 + w
  let mut ks : Array Nat := Array.mkEmpty tpl.size
  for h : q in [0:tpl.size] do
    let e := tpl[q]
    ks := ks.push (key e.o e.i e.d e.w * 262144 + q)
  ks := sortNat ks
  let bo := ((tpl.filter fun e => e.i == 0 && e.d == 0 && e.w == 0 && e.c == 1).map (·.o)).toList.eraseDups
  if bo.isEmpty then return none
  let has (o i w : Nat) (c : FE2) : Bool := ok o i 0 w && ((lastOf ks (key o i 0 w)).map fun q => (tpl[q]!).c) == some c
  let mut nb := 0
  while nb < 2 ^ (min a bb) && bo.all (fun o => has o nb nb 1) do nb := nb + 1
  if nb < 8 then return none
  let β := Nat.log2 (nb - 1) + 1
  let isB (e : Lvm6.Phi.CEnt) : Bool := e.d == 0 && e.i == e.w && e.w < nb && e.c == 1 && bo.contains e.o
  let cands := tpl.filter fun e => e.d == 0 && e.w == 1 && !isB e
  for c in cands do
    let g := c.c
    if (List.range nb).all fun z => has c.o c.i z (gpw g z) then
      let isW (e : Lvm6.Phi.CEnt) : Bool := e.d == 0 && e.o == c.o && e.i == c.i && e.w < nb && e.c == gpw g e.w
      let L := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1
      return some (⟨xb, a, yb, bb, n, L, β, nb, bo, c.i, c.o, g⟩, tpl.filter fun e => !(isB e || isW e))
  return none

/-- **`PT.ofCls`, packed** (`mkRCovF`). -/
def PT.ofClsF (cls : Array Lvm6.Phi.PCls) (rest : Array EntT) (wb : ℕ) : PT :=
  let cs := cls.map fun k =>
    let part (d : ℕ) : Array EntT := (k.tpl.toArray.filter (·.d == d)).map fun e => ⟨e.o, e.i, e.w, e.c⟩
    (⟨k.g.xb, k.g.a, k.g.yb, k.g.b, k.g.n, (if k.g.n ≤ 1 then 0 else Nat.log2 (k.g.n - 1) + 1),
      mkRCovF (part 0) true, mkRCovF (part 1) false, mkRCovF (part 2) false⟩ : CTpl)
  ⟨cs, mkRCovF rest (wb == 0), #[], #[], #[], #[], ⟨#[]⟩⟩

/-- PHIV7: a line's sort key for `AK.rowW2`: fixed lines by `(o, y)`, then strided lines by `(ek, o, y)` (equal high
word parts end up adjacent). Packed, so lexicographic only for `o < 1024`, `y < 2^21`; past that the grouping is
still correct, only less effective. -/
def aeKey (t : AE) : Nat := ((if t.fx then 0 else 1 + t.ek) * 1024 + t.o) * 2097152 + t.y

/-- PHIV7: each row's lines sorted by group (`AK.rowW2` flushes once per group). Only permutes `AK.ents`. -/
def AK.sortRows (k : AK) : AK :=
  { k with rows := k.rows.map fun r => (r.1, r.2.qsort fun s t => aeKey s < aeKey t) }

/-- PHIV7: a cover's singles sorted by `(o, key y)` (`sglSumK` flushes once per group), ties by `(y, x)` (few
distinct keys: no long runs of equal keys for `qsort`). Only permutes the entries. -/
def RCov.sortSgl (key : Nat → Nat) (rc : RCov) : RCov :=
  { rc with fc := { rc.fc with sgl := rc.fc.sgl.qsort fun s t =>
    s.o < t.o || (s.o == t.o && (key s.y < key t.y || (key s.y == key t.y &&
      (s.y < t.y || (s.y == t.y && s.x < t.x))))) } }

/-- PHIV7: a class's singles sorted: `t0`, `t1` by `(o, y % 2)`, `t2` by `(o, y / 2048)`. -/
def CTpl.sortSgl (k : CTpl) : CTpl where
  xb := k.xb
  a := k.a
  yb := k.yb
  bb := k.bb
  n := k.n
  L := k.L
  t0 := k.t0.sortSgl fun y => y % 2
  t1 := k.t1.sortSgl fun y => y % 2
  t2 := k.t2.sortSgl fun y => y / 2048

/-- **The class table of a `.cls`'s lines** (the bench's `loadPT`, `restH`). -/
def PT.ofLines (ls : Array (Array Nat)) (rmode : Nat := 2) : PT := Id.run do
  let nums (l : Array Nat) : Array Nat := l
  let hdr (l : Array Nat) : Array Nat := l.extract 1 l.size
  let fe2 (a b : Nat) : FE2 := ⟨⟨a.toUInt64⟩, ⟨b.toUInt64⟩⟩
  let ver := (hdr ls[0]!)[0]!
  let wb := (hdr ls[1]!)[0]!
  let nc := (hdr ls[2]!)[0]!
  let mut i := 3
  let mut cls : Array Lvm6.Phi.PCls := #[]
  let mut aks : Array AK := #[]
  let mut bks : Array BKB := #[]
  let mut extra : Array EntT := #[]
  for _ in [0:nc] do
    let h := hdr ls[i]!
    i := i + 1
    let (xb, a, yb, bb, n) := (h[0]!, h[1]!, h[2]!, h[3]!, h[4]!)
    let L := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1
    let mut tpl : Array Lvm6.Phi.CEnt := #[]
    let mut ext : List (Nat × Nat × Nat × Nat × FE2 × Nat) := []
    for _ in [0:h[5]!] do
      let v := nums ls[i]!
      let sv := if ver ≥ 2 then v[6]! else 0
      let (o, ii, d, w, c) := (v[0]!, v[1]!, v[2]!, v[3]!, fe2 v[4]! v[5]!)
      if a == 0 && bb == 0 then
        if d == 1 then
          for j in [1:n] do extra := extra.push ⟨o, xb + j + ii, yb + (j - 1) + w, c⟩
        else ext := ext ++ [(o, xb + ii, (if d == 2 then 2 else 3), (if d == 2 then w else yb + w), c, (if d == 3 then sv else 0))]
      else if d == 3 then ext := ext ++ [(o, xb + ii, 3, w, c, sv)]
      else tpl := tpl.push { o := o, i := ii, d := d, w := w, c := c }
      i := i + 1
    if a == 0 && bb == 0 then aks := aks.push (AK.ofEnts 0 L n ext)
    else if bb == 0 || a + L > 20 || bb + L > 21 || xb % 2 ^ (a + L) != 0 || yb % 2 ^ (bb + L) != 0 then
      -- ST-4: a class `CTpl.okB` rejects (e.g. a one-word block, `b = 0`) is expanded into the rest
      for e in tpl do
        for j in [0:n] do
          let x := xb + j * 2 ^ a + e.i
          let y := if e.d == 0 then yb + j * 2 ^ bb + e.w else if e.d == 1 then yb + (j - 1) * 2 ^ bb + e.w else e.w
          if e.d != 1 || j ≥ 1 then extra := extra.push ⟨e.o, x, y, e.c⟩
      if !ext.isEmpty then aks := aks.push (AK.ofEnts a L n ext)
    else
      let tplR := match recogBitsLF xb a yb bb n tpl with
        | some (k, rest) => (some k, rest)
        | none => (none, tpl)
      if let some k := tplR.1 then bks := bks.push k
      if !tplR.2.isEmpty then cls := cls.push ⟨⟨xb, a, yb, bb, n⟩, tplR.2.toList⟩
      if !ext.isEmpty then aks := aks.push (AK.ofEnts a L n ext)
  -- PHIV3: `LOOPS m` (PHICLS 2): per loop with strided entries `LOOP blk xb l nc D d_1 … d_D t`, then `t` lines
  -- `o r w c0 c1 ss_1 … ss_D`; grouped per `(ss_1, ss_2)` into `strLoopF` runs (`D ≤ 2`).
  let mut strs : Array SRunF := #[]
  if isKw ls[i]! 4 then
    let nl := (hdr ls[i]!)[0]!
    i := i + 1
    for _ in [0:nl] do
      let h := hdr ls[i]!
      i := i + 1
      let xb := h[1]!
      let l := h[2]!
      let ncr := h[3]!
      let D := h[4]!
      let t := h[5 + D]!
      let hb := if ncr ≤ 1 then 0 else Nat.log2 (ncr - 1) + 1
      let mut grp : Array ((Nat × Nat) × Array (FE2 × Nat × Nat × Nat)) := #[]
      for _ in [0:t] do
        let v := nums ls[i]!
        i := i + 1
        let key := (v.getD 5 0, v.getD 6 0)
        let rd : FE2 × Nat × Nat × Nat := (fe2 v[3]! v[4]!, v[0]!, v[1]!, v[2]!)
        match grp.findIdx? (·.1 == key) with
        | some j => grp := grp.modify j fun g => (g.1, g.2.push rd)
        | none => grp := grp.push (key, #[rd])
      let (a, n) := if D == 1 then (0, h[5]!) else (h[5]!, h[6]!)
      for g in grp do
        let (R₁, R) := if D == 1 then (0, g.1.1) else (g.1.1, g.1.2)
        strs := strs.push (strLoopF xb a n hb R₁ R g.2.toList)
  -- PHIV3: `GATHERS g` (PHICLS 3, LAY4's lever G): per loop `GATHER blk xb l nc t`, then `t` lines `o r j y c0 c1`
  -- (slot `xb + r·2^l + j`, word `y`); one gather kind per loop, rows per `(r, o)`, columns per word.
  let mut gks : Array GK := #[]
  if isKw ls[i]! 6 then
    let ng := (hdr ls[i]!)[0]!
    i := i + 1
    for _ in [0:ng] do
      let h := hdr ls[i]!
      i := i + 1
      let xb := h[1]!
      let l := h[2]!
      let t := h[4]!
      -- PHIV4: the loop's lines `(x₀, o, j, y, c)`, rows per consecutive `(x₀, o)` (`mkGK`)
      let mut gl : Array (Nat × Nat × Nat × Nat × FE2) := #[]
      for _ in [0:t] do
        let v := nums ls[i]!
        i := i + 1
        gl := gl.push (xb + v[1]! * 2 ^ l, v[0]!, v[2]!, v[3]!, fe2 v[4]! v[5]!)
      gks := gks.push (mkGKL l gl)
  -- PHIV5: `SRUNS m` (LAY5, STR's explicit runs): per run `SRUN p n R g`, then `g` groups `s k`, each with `k` atom
  -- lines `o x₀ c0 c1`: entries `(c, o, x₀ + 2^p·j, s + R·j)`, `j < 2^n`. Factored as `SRunF` (a hint): template rows
  -- `x₀ / 2^(p+n)` in one aligned block of `2^hb`, atoms `(template, x₀ % 2^p)`.
  if isKw ls[i]! 8 then
    let nsr := (hdr ls[i]!)[0]!
    i := i + 1
    for _ in [0:nsr] do
      let h := hdr ls[i]!
      i := i + 1
      let (p, n, R, g) := (h[0]!, h[1]!, h[2]!, h[3]!)
      let mut grpE : Array (Nat × Array (FE2 × Nat × Nat)) := #[]
      for _ in [0:g] do
        let sk := nums ls[i]!
        i := i + 1
        let mut ats : Array (FE2 × Nat × Nat) := #[]
        for _ in [0:sk[1]!] do
          let v := nums ls[i]!
          i := i + 1
          ats := ats.push (fe2 v[2]! v[3]!, v[0]!, v[1]!)
        grpE := grpE.push (sk[0]!, ats)
      let rowsA := grpE.flatMap fun gr => gr.2.map fun a => a.2.2 / 2 ^ (p + n)
      let lo := rowsA.foldl min (rowsA.getD 0 0)
      let hi := rowsA.foldl max 0
      let hb := (List.range 21).find? (fun b => lo / 2 ^ b == hi / 2 ^ b) |>.getD 20
      let mut tpl : Array (FE2 × Nat × Nat) := #[]
      let mut grp : Array (Nat × Array (Nat × Nat)) := #[]
      for gr in grpE do
        let mut ek : Array (Nat × Nat) := #[]
        for a in gr.2 do
          let r := a.2.2 / 2 ^ (p + n) % 2 ^ hb
          let key : FE2 × Nat × Nat := (a.1, a.2.1, r)
          let e := (tpl.findIdx? (· == key)).getD tpl.size
          if e == tpl.size then tpl := tpl.push key
          ek := ek.push (e, a.2.2 % 2 ^ p)
        grp := grp.push (gr.1, ek)
      strs := strs.push ⟨p, n, R, hb, lo / 2 ^ hb, tpl, grp⟩
  let nr := (hdr ls[i]!)[0]!
  i := i + 1
  let mut rest : Array EntT := #[]
  for _ in [0:nr] do
    let v := nums ls[i]!
    rest := rest.push ⟨v[0]!, v[1]!, v[2]!, fe2 v[3]! v[4]!⟩
    i := i + 1
  -- PHIV5 (`rmode` 1): the `REST` entries as one gather kind with `l = 11` (rows `(x / 2^11, o)`), not the cover;
  -- (`rmode` 2): only the entries the cover would leave single (not a `(1, X)` pair at words `y, y + 1`, not a `W` run)
  if rmode ≥ 1 && rest.size > 0 && pkAll rest then
    -- SU2: the reference's step on packed keys (`pk3`), the gather rows sorted on `(x / 2^11, o)` keys
    let cm : Std.HashMap Nat FE2 := rest.foldl (fun m e => m.insert (pk3 e.o e.x e.y) e.c) {}
    let get (o x y : Nat) : Option FE2 := if pk3Ok o x y then cm.get? (pk3 o x y) else none
    let isW (x : Nat) : Bool := get 3 x (2 * x) == some 1 && get 3 x (2 * x + 1) == some xF
    let paired (e : EntT) : Bool := (e.o < 4 && e.c == 1 && get e.o e.x (e.y + 1) == some xF) ||
      (e.o < 4 && e.c == xF && e.y > 0 && get e.o e.x (e.y - 1) == some 1) ||
      (e.o == 3 && (e.y == 2 * e.x || e.y == 2 * e.x + 1) && isW e.x)
    let toG := if rmode == 1 then rest else rest.filter fun e => !paired e
    let keep := if rmode == 1 then #[] else rest.filter paired
    if toG.size > 0 then
      let mut ks : Array Nat := Array.mkEmpty toG.size
      for h : q in [0:toG.size] do
        let e := toG[q]
        ks := ks.push (((((e.x / 2048) * 16 + e.o) * 2097152 + e.y) * 262144) + q)
      ks := sortNat ks
      let gl := ks.map fun k => let e := toG[k % 262144]!; (e.x / 2048 * 2048, e.o, e.x % 2048, e.y, e.c)
      gks := gks.push (mkGKL 11 gl)
    rest := keep
  else if rmode ≥ 1 && rest.size > 0 then
      let key (o x y : Nat) : Nat × Nat × Nat := (o, x, y)
      let cm : Std.HashMap (Nat × Nat × Nat) FE2 := rest.foldl (fun m e => m.insert (key e.o e.x e.y) e.c) {}
      let isW (x : Nat) : Bool := cm.get? (3, x, 2 * x) == some 1 && cm.get? (3, x, 2 * x + 1) == some xF
      let paired (e : EntT) : Bool := (e.o < 4 && e.c == 1 && cm.get? (key e.o e.x (e.y + 1)) == some xF) ||
        (e.o < 4 && e.c == xF && e.y > 0 && cm.get? (key e.o e.x (e.y - 1)) == some 1) ||
        (e.o == 3 && (e.y == 2 * e.x || e.y == 2 * e.x + 1) && isW e.x)
      let toG := if rmode == 1 then rest else rest.filter fun e => !paired e
      let keep := if rmode == 1 then #[] else rest.filter paired
      if toG.size > 0 then
        let gl := (toG.map fun e => (e.x / 2048 * 2048, e.o, e.x % 2048, e.y, e.c)).qsort fun a b =>
          a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
        gks := gks.push (mkGKL 11 gl)
      rest := keep
  let P := PT.ofClsF cls (rest ++ extra) wb
  -- PHIV7: the singles sorted for the grouped sums of `PT.evalW7` (`CTpl.val2`, `rsumK`)
  let P := { P with cls := P.cls.map CTpl.sortSgl, rest := P.rest.sortSgl fun y => y / 2048 }
  return { P with ak := aks.map AK.sortRows, str := strs, gk := gks, bk := bks, rk := ⟨#[]⟩ }


/-- **The embedded class table from its hex.** -/
def PT.ofHex (s : String) : PT := PT.ofLines (phbLines (hexToBytes s))

end Lvm6.V
