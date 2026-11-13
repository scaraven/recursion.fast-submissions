-- New for lvm2 (roll 8 = B1, B1-K): the compiler of `Φ_Q`'s terms (`CTerm`, with their operand classes) to the
-- compiled evaluator `LvmWiringK.Comp`: K1 terms (and K2's shifted half, the sub-cubes of splits and the points)
-- become atoms, K3 terms become carry-automaton passes. Static; run once per program.
import LvmWiringK
import Std.Data.HashMap

/-!
# The compiler `compileT`

A term `w · eq(κ, o) · Σ_{jf < 2^l} eq(r_x, x0 + jf) · eq(r_y, f(jf))` (with `x0` aligned to `2^l`) is cut into
pieces, each one of:

* **an atom** `w · K · eq(κ, o) · eq(r_x[l:], x0 ≫ l) · eq_{¬M}(r_y, y0)`, where the kernel `K` is a product of
  one-bit factors over the iteration bits (`KF.pair` for a bit that `f` copies to `y` bit `j`, `KF.fixX` for a bit
  fixed by a sub-cube, `KF.succ` for K2's shifted field) and `M` the set of `y` bits the kernel reads; a point is
  an atom with the empty kernel, `x = x0 + jf` and `y = f(jf)`;
* **a pass member** (K3, `f` affine but not a bit injection): the automaton runs over the longest run of
  iteration bits whose coefficients are `R·2^k`; the other free bits are enumerated into the initial states.

The `x` and `y` keys are looked up in `eq` tables over the complement of the kernel's bits, cut at
`xCut`/`yCut` so that each table has at most `2^11` entries. Atoms are sorted by their keys, so `evalRuns` pays one
product per distinct key prefix.

**`compileT_eq`** (statement, L-A): on well-formed terms (`TermWF`), `evalC (compileT ts) pt` is the sum of the
terms' sums.
-/

set_option autoImplicit false

namespace Lvm.Typed.K

open Lvm.Loop

/-! ## A term's sum (the semantics the compiler preserves) -/

/-- `eq(pt, idx)` of a term's entry at `jf`, weighted: the term's contribution at one iteration. -/
def termAt (t : CTerm) (pt : List FE) (jf : ℕ) : FE := t.wAt jf * eqW pt (t.at jf).idx

/-- **A term's sum** over its iterations. -/
def termSum (t : CTerm) (pt : List FE) : FE :=
  (List.range (2 ^ t.l)).foldr (fun jf acc ↦ termAt t pt jf + acc) 0

/-- **A well-formed term**: matrix `o < 4`; its slots `x0 + jf` aligned and below `2^xVars`. -/
def TermWF (t : CTerm) : Prop := t.o < 4 ∧ t.x0 % 2 ^ t.l = 0 ∧ t.x0 + 2 ^ t.l ≤ 2 ^ xVars

/-- The check of `TermWF`. -/
def termWFB (t : CTerm) : Bool := decide (t.o < 4) && t.x0 % 2 ^ t.l == 0 && decide (t.x0 + 2 ^ t.l ≤ 2 ^ xVars)

/-! ## Bit helpers -/

/-- `log₂` of a power of two. -/
def log2 (c : ℕ) : ℕ := Nat.log2 c

/-- Whether `c` is a power of two. -/
def isPow2 (c : ℕ) : Bool := c != 0 && c &&& (c - 1) == 0

/-- Whether `u0 + Σ bit_i·c_i` (over the listed coefficients) is a bit injection: the nonzero coefficients are
distinct powers of two, none overlapping `u0`. -/
def injOk (u0 : ℕ) (cs : List ℕ) : Bool :=
  (cs.foldl (fun (acc : Option ℕ) c ↦ acc.bind fun u ↦
    if c == 0 then some u else if isPow2 c && u &&& c == 0 then some (u ||| c) else none) (some u0)).isSome

/-- The maximal runs of bits in `[0, N)` outside `mask`, cut at the multiples of `cut`: `(lo, n)`. -/
def runsOut (N cut : ℕ) (mask : ℕ → Bool) : List (ℕ × ℕ) := Id.run do
  let mut out : Array (ℕ × ℕ) := #[]
  let mut b := 0
  while b < N do
    if mask b then
      b := b + 1
    else
      let lo := b
      let mut e := b + 1
      while e < N && !mask e && e % cut != 0 do
        e := e + 1
      out := out.push (lo, e - lo)
      b := e
  return out.toList

/-! ## The compiler's state -/

/-- `x` tables are cut at `2^10`, `y` tables at `2^11`. -/
abbrev xCut : ℕ := 10
/-- The `y` cut. -/
abbrev yCut : ℕ := 11

/-- A table key for the compiler's dedup. -/
inductive TKey where
  | eqx (bits : List ℕ)
  | eqy (bits : List ℕ)
  deriving BEq, Hashable, Inhabited

/-- The compiler's state: tables, kernels, atoms, pass members. -/
structure CS where
  /-- The table recipes so far (`0`: one, `1`: `κ`'s masks, `2`: the kernels, `3`/`4`: the memoised `x`/`y`
  keys, filled at the end). -/
  tabs : Array TRec := #[.one, .kap, .ker #[], .prod #[], .prod #[]]
  /-- The memoised `x` keys. -/
  xm : Array (List (ℕ × ℕ)) := #[]
  /-- Their dedup. -/
  xmi : Std.HashMap (List (ℕ × ℕ)) ℕ := {}
  /-- The memoised `y` keys. -/
  ym : Array (List (ℕ × ℕ)) := #[]
  /-- Their dedup. -/
  ymi : Std.HashMap (List (ℕ × ℕ)) ℕ := {}
  /-- Dedup of the `eq` tables. -/
  tix : Std.HashMap TKey ℕ := {}
  /-- The kernels. -/
  kers : Array (List KF) := #[]
  /-- Dedup of the kernels. -/
  kix : Std.HashMap (List KF) ℕ := {}
  /-- The atoms. -/
  atoms : Array Atom := #[]
  /-- The pass members, by pass key `(xs, R, limb)`. -/
  pm : Std.HashMap (List ℕ × ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ × FE)) := {}
  deriving Inhabited

namespace CS

/-- The id of an `eq` table. -/
def tab (s : CS) (k : TKey) : CS × ℕ :=
  match s.tix[k]? with
  | some i => (s, i)
  | none =>
    let r := match k with
      | .eqx bs => TRec.eqx bs
      | .eqy bs => TRec.eqy bs
    ({ s with tabs := s.tabs.push r, tix := s.tix.insert k s.tabs.size }, s.tabs.size)

/-- The id of a kernel. -/
def ker (s : CS) (fs : List KF) : CS × ℕ :=
  match s.kix[fs]? with
  | some i => (s, i)
  | none => ({ s with kers := s.kers.push fs, kix := s.kix.insert fs s.kers.size }, s.kers.size)

/-- `a₀, b₀, a₁, b₁, …` (the longer list's tail at the end). -/
def interleave {α : Type} : List α → List α → List α
  | a :: as, b :: bs => a :: b :: interleave as bs
  | as, [] => as
  | [], bs => bs

/-- The memo index of an `x` key list. -/
def memoX (s : CS) (ks : List (ℕ × ℕ)) : CS × ℕ :=
  match s.xmi[ks]? with
  | some i => (s, i)
  | none => ({ s with xm := s.xm.push ks, xmi := s.xmi.insert ks s.xm.size }, s.xm.size)

/-- The memo index of a `y` key list. -/
def memoY (s : CS) (ks : List (ℕ × ℕ)) : CS × ℕ :=
  match s.ymi[ks]? with
  | some i => (s, i)
  | none => ({ s with ym := s.ym.push ks, ymi := s.ymi.insert ks s.ym.size }, s.ym.size)

/-- The keys of value `v` on the bits of `[0, N)` outside `mask` (`eqx` if `isX`): the bits below `cut`, then
those above (each group one table, `pext`-indexed). -/
def rangeKeys (s : CS) (isX : Bool) (N cut : ℕ) (mask : ℕ → Bool) (v : ℕ) : CS × List (ℕ × ℕ) :=
  let free := (List.range N).filter (!mask ·)
  let groups := [free.filter (· < cut), free.filter (· ≥ cut)].filter (!·.isEmpty)
  groups.foldl (fun (acc : CS × List (ℕ × ℕ)) bs ↦
    let (s', t) := acc.1.tab (if isX then .eqx bs else .eqy bs)
    (s', acc.2 ++ [(t, pext v bs)])) (s, [])

/-- Add an atom: kernel `fs`, selector `o`, the `x` value off the bits `< xm` (or every bit for a point), the
`y` value off the kernel's `y` bits `ym`, weight `w`; with `lim = some e` a merged `E` cell (the limb factor at
`y` bits `e, e+1`, which the words leave `0`). -/
def addAtom (s : CS) (fs : List KF) (o : ℕ) (xm : ℕ) (x : ℕ) (ym : List ℕ) (y : ℕ) (w : FE)
    (lim : Option ℕ := none) : CS :=
  let (fs, ym) := match lim with
    | some e => (fs ++ [KF.limb e], ym ++ [e, e + 1])
    | none => (fs, ym)
  let (s, kid) := if fs.isEmpty then (s, 0) else s.ker fs
  let (s, xk) := s.rangeKeys true xVars xCut (fun b ↦ b < xm) x
  let (s, yk) := s.rangeKeys false yVars yCut (fun b ↦ ym.contains b) y
  -- levels: kernel, selector, then the ranges high first, `x` and `y` interleaved (padded to a common depth
  -- by `padTo`)
  let kk : ℕ × ℕ := if fs.isEmpty then (0, 0) else (2, kid)
  { s with atoms := s.atoms.push ⟨(([kk, (1, 1 <<< o)] : List (ℕ × ℕ)) ++ interleave xk.reverse yk.reverse).toArray, w⟩ }

/-- Add a pass member: automaton bits `xs` with stride `R`, initial state `st`, selector `o`, the `x` value off
the automaton's bits, weight `w`. A merged `E` cell (`lim = some e`) stays merged when the automaton stops below
bit `e`; else its three limbs are added. -/
def addMember (s : CS) (xs : List ℕ) (R st o x : ℕ) (w : FE) (lim : Option ℕ := none) : CS :=
  let push (key : List ℕ × ℕ × Option ℕ) (ms : List (ℕ × FE)) : CS :=
    { s with pm := s.pm.insert key (ms.foldl (fun a (st, w) ↦ a.push (st, o, x, w)) (s.pm.getD key #[])) }
  match lim with
  | some e =>
    if xs.length ≤ e then push (xs, R, some e) [(st, w)]
    else push (xs, R, none) [(st, w), (st + 2 ^ e, w * FE.y), (st + 2 * 2 ^ e, w * FE.y * FE.y)]
  | none => push (xs, R, none) [(st, w)]

end CS

/-! ## Pieces of a term -/

/-- An affine map on a sub-cube: the iteration bits `< l` not in `fix` are free; `fix` fixes the others. -/
structure SubAff where
  /-- `log₂` of the iterations. -/
  l : ℕ
  /-- The fixed bits and their values. -/
  fix : List (ℕ × Bool)
  /-- The word at the sub-cube's first iteration. -/
  y0 : ℕ
  /-- The free bits and their coefficients. -/
  free : List (ℕ × ℕ)
  deriving Inhabited

/-- The sub-cube of `a` fixing `fix` (the fixed bits' coefficients fold into `y0`). -/
def subAff (l : ℕ) (a : Aff) (fix : List (ℕ × Bool)) : SubAff :=
  let isFix (i : ℕ) : Bool := fix.any (·.1 == i)
  ⟨l, fix, a.y0 + (fix.map fun (i, b) ↦ if b then a.coef.getD i 0 else 0).sum,
    ((List.range l).filter (!isFix ·)).map fun i ↦ (i, a.coef.getD i 0)⟩

/-- The longest run of free bits with coefficients `R·2^k` (consecutive iteration bits): `(bits, R)`. -/
def autoRun (free : List (ℕ × ℕ)) : List ℕ × ℕ := Id.run do
  let fa := free.toArray
  let mut best : List ℕ × ℕ := ([], 0)
  let mut i := 0
  while i < fa.size do
    let (b0, c0) := fa.getD i (0, 0)
    let mut j := i + 1
    while j < fa.size && (fa.getD j (0, 0)).1 == b0 + (j - i) && (fa.getD j (0, 0)).2 == c0 * 2 ^ (j - i) do
      j := j + 1
    if j - i > best.1.length && c0 != 0 then
      best := ((List.range (j - i)).map (b0 + ·), c0)
    i := j
  return best

/-- **A sub-cube's pieces**: an atom if it is a bit injection, else pass members (the automaton over
`autoRun`, the other free bits enumerated). `o`, `w`, `x0` are the term's. -/
def CS.addSub (s : CS) (o : ℕ) (w : FE) (x0 : ℕ) (q : SubAff) (lim : Option ℕ := none) : CS :=
  if injOk q.y0 (q.free.map (·.2)) then
    let pairs := q.free.filter fun (_, c) ↦ c != 0 && log2 c < yVars
    let fs := q.fix.map (fun (i, b) ↦ KF.fixX i b) ++ pairs.map fun (i, c) ↦ KF.pair i (log2 c)
    s.addAtom fs o q.l (x0 >>> q.l <<< q.l) (pairs.map fun (_, c) ↦ log2 c) q.y0 w lim
  else
    let (xs, R) := autoRun q.free
    let inner := q.free.filter fun (i, _) ↦ !xs.contains i
    let fixX := (q.fix.map fun (i, b) ↦ if b then 2 ^ i else 0).sum
    (List.range (2 ^ inner.length)).foldl (fun s m ↦
      let bs := (List.range inner.length).filter m.testBit
      let ds := bs.map fun k ↦ inner.getD k (0, 0)
      s.addMember xs R (q.y0 + (ds.map (·.2)).sum) o (x0 + fixX + (ds.map (2 ^ ·.1)).sum) w lim) s

/-- The points of a term: one atom per iteration. -/
def CS.addPoints (s : CS) (t : CTerm) (lim : Option ℕ := none) : CS :=
  (List.range (2 ^ t.l)).foldl (fun s jf ↦ s.addAtom [] t.o 0 (t.x0 + jf) [] (t.cls.at jf) t.w lim) s

/-- **A term with varying weights**: the aligned sub-cubes `k0 + [0, 2^a)` on which word and weight are constant
(recursive halving); each is an atom whose kernel fixes the high iteration bits (a point when `a = 0`). -/
def CS.addVarying (s : CTerm → CS → CS) (t : CTerm) (s0 : CS) : CS :=
  let rec go (fuel k0 a : ℕ) (s : CS) : CS :=
    let same := (List.range (2 ^ a)).all fun j ↦ t.cls.at (k0 + j) == t.cls.at k0 && t.wAt (k0 + j) == t.wAt k0
    match fuel with
    | 0 => s
    | fuel + 1 =>
      if same || a == 0 then
        let w := t.wAt k0
        if w == 0 then s
        else if a == 0 then s.addAtom [] t.o 0 (t.x0 + k0) [] (t.cls.at k0) w
        else
          let fs := ((List.range t.l).filter (· ≥ a)).map fun i ↦ KF.fixX i (k0.testBit i)
          s.addAtom fs t.o t.l t.x0 [] (t.cls.at k0) w
      else go fuel (k0 + 2 ^ (a - 1)) (a - 1) (go fuel k0 (a - 1) s)
  go (t.l + 1) 0 t.l s0

/-- K2's shifted half is a product kernel when `sh` copies the field `[p, p + n)` to `y` bits `[q, q + n)` and the
other bits inject: `some (q, pairs)`. -/
def shiftOk (l p n : ℕ) (sh : Aff) : Option (ℕ × List (ℕ × ℕ)) :=
  let c := sh.coef.getD p 0
  if !isPow2 c || n < 2 then none else
    let q := log2 c
    let fieldOk := (List.range n).all fun k ↦ sh.coef.getD (p + k) 0 == 2 ^ (q + k)
    let others := ((List.range l).filter fun i ↦ i < p || i ≥ p + n).map fun i ↦ (i, sh.coef.getD i 0)
    if fieldOk && q + n ≤ yVars && injOk sh.y0 (others.map (·.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)) then
      some (q, others)
    else none

/-- Whether the parts of a split are disjoint and cover the cube (so the first match is the only one). -/
def splitOk (l : ℕ) (parts : List (List (ℕ × Bool) × Aff)) : Bool :=
  let ok1 := parts.all fun pq ↦ pq.1.all (·.1 < l) && (pq.1.map (·.1)).Nodup
  let disj := (List.range parts.length).all fun i ↦ (List.range i).all fun j ↦
    let a := (parts.getD i default).1
    let b := (parts.getD j default).1
    a.any fun (k, v) ↦ b.any fun (k', v') ↦ k == k' && v != v'
  let cover := (parts.map fun pq ↦ 2 ^ (l - pq.1.length)).sum == 2 ^ l
  ok1 && disj && cover

/-- **A term's pieces.** Ill-formed terms (`TermWF` fails) are not compiled (their check fails anyway). -/
def CS.addTerm (s : CS) (t : CTerm) (lim : Option ℕ := none) : CS :=
  if !termWFB t then s else
  if !t.wv.isEmpty then CS.addVarying (fun _ s ↦ s) t s else
  if t.w == 0 then s else
  match t.cls with
  | .aff a => s.addSub t.o t.w t.x0 (subAff t.l a []) lim
  | .split parts =>
    if splitOk t.l parts then
      parts.foldl (fun s (fix, a) ↦ s.addSub t.o t.w t.x0 (subAff t.l a fix) lim) s
    else s.addPoints t lim
  | .shift p n sh ini =>
    if p + n > t.l || n = 0 then s.addPoints t lim else
    let field := (List.range n).map fun k ↦ (p + k, false)
    let s := s.addSub t.o t.w t.x0 (subAff t.l ini field) lim
    if n == 1 then
      -- field bit `1`: `sh` at the iteration with the bit cleared
      let sh' : Aff := ⟨sh.y0, (List.range t.l).map fun i ↦ if i == p then 0 else sh.coef.getD i 0⟩
      s.addSub t.o t.w t.x0 (subAff t.l sh' [(p, true)]) lim
    else
      match shiftOk t.l p n sh with
      | some (q, others) =>
        let pairs := others.filter fun (_, c) ↦ c != 0 && log2 c < yVars
        let fs := KF.succ ((List.range n).map (p + ·)) ((List.range n).map (q + ·)) ::
          pairs.map fun (i, c) ↦ KF.pair i (log2 c)
        s.addAtom fs t.o t.l t.x0 ((List.range n).map (q + ·) ++ pairs.map fun (_, c) ↦ log2 c) sh.y0 t.w lim
      | none =>
        -- the shifted half as points (iterations with the field `≥ 1`)
        (List.range (2 ^ t.l)).foldl (fun s jf ↦
          if (jf / 2 ^ p) % 2 ^ n == 0 then s
          else s.addAtom [] t.o 0 (t.x0 + jf) [] (sh.at (jf - 2 ^ p)) t.w lim) s
  | .point _ => s.addPoints t lim

/-- The class with every word moved by `d`. -/
def _root_.Lvm.Typed.OpClass.addY (d : ℕ) : OpClass → OpClass
  | .aff a => .aff ⟨a.y0 + d, a.coef⟩
  | .shift p n sh ini => .shift p n ⟨sh.y0 + d, sh.coef⟩ ⟨ini.y0 + d, ini.coef⟩
  | .split ps => .split (ps.map fun (f, a) ↦ (f, ⟨a.y0 + d, a.coef⟩))
  | .point ys => .point (ys.map (· + d))

/-- **A merged `E` cell**: three consecutive terms of a row, the limbs `m < 3` of one cell (words `+ m·2^e`,
weights `w·y^m`), whose limb-0 words leave bits `e, e+1` at `0`: its limb bit `e`. The words are checked at every
iteration (L-A: `addY` alone does not move a `point` class's missing entries nor a `split`'s uncovered iterations). -/
def limbOf (t0 t1 t2 : CTerm) : Option ℕ :=
  let y0 := t0.cls.at 0
  let y1 := t1.cls.at 0
  if !(t0.wv.isEmpty && t1.wv.isEmpty && t2.wv.isEmpty && t1.src == t0.src && t2.src == t0.src && t1.idx == t0.idx + 1 && t2.idx == t0.idx + 2 &&
      t1.o == t0.o && t2.o == t0.o && t1.x0 == t0.x0 && t2.x0 == t0.x0 && t1.l == t0.l && t2.l == t0.l) then none
  else if y1 < y0 || !isPow2 (y1 - y0) then none else
  let d := y1 - y0
  let e := log2 d
  if e + 1 < yVars && t1.w == t0.w * FE.y && t2.w == t0.w * FE.y * FE.y &&
      t1.cls == OpClass.addY d t0.cls && t2.cls == OpClass.addY (2 * d) t0.cls &&
      (List.range (2 ^ t0.l)).all (fun jf ↦ (t0.cls.at jf >>> e) % 4 == 0 &&
        t1.cls.at jf == t0.cls.at jf + d && t2.cls.at jf == t0.cls.at jf + 2 * d) then some e else none

/-- The terms with the `E` cells merged: `(term, limb)`. -/
def mergeLimbs (ts : Array CTerm) : Array (CTerm × Option ℕ) := Id.run do
  let mut out : Array (CTerm × Option ℕ) := Array.mkEmpty ts.size
  let mut i := 0
  while i < ts.size do
    let t0 := ts.getD i default
    match (if i + 2 < ts.size then limbOf t0 (ts.getD (i + 1) default) (ts.getD (i + 2) default) else none) with
    | some e =>
      out := out.push (t0, some e)
      i := i + 3
    | none =>
      out := out.push (t0, none)
      i := i + 1
  return out

/-- **Geometric runs** (B1-Q's `BITS` word and output rows: `Σ_z coef(z)·β_z` with `coef(z) = x^{z+k}`):
`2^b` consecutive terms of a row, equal but in their first word (`y0 + z·2^q`, bits `[q, q + b)` of `y0` zero) and
their weight (`w·g^z`, `g ∈ K`), bit injections: one atom whose kernel carries `KF.ypow (q + i) (g^(2^i))`. -/
def geoOf (ts : Array CTerm) (i : ℕ) : Option (ℕ × ℕ × FK) := Id.run do
  let t0 := ts.getD i default
  let t1 := ts.getD (i + 1) default
  let some a := (match t0.cls with | .aff a => some a | _ => none) | return none
  if !(t0.wv.isEmpty && termWFB t0 && a.coef.length == t0.l && injOk a.y0 a.coef) then return none
  if !(t0.w.c₁ == 0 && t0.w.c₂ == 0 && !(t0.w.c₀ == 0) && t1.w.c₁ == 0 && t1.w.c₂ == 0) then return none
  let g := t1.w.c₀ * t0.w.c₀⁻¹
  let y1 := t1.cls.at 0
  if y1 ≤ a.y0 || !isPow2 (y1 - a.y0) then return none
  let q := log2 (y1 - a.y0)
  let member (z : ℕ) : Bool :=
    let t := ts.getD (i + z) default
    i + z < ts.size && t.src == t0.src && t.idx == t0.idx + z && t.o == t0.o && t.x0 == t0.x0 && t.l == t0.l &&
      t.wv.isEmpty && t.cls == .aff ⟨a.y0 + z * 2 ^ q, a.coef⟩ && t.w == t0.w * FE.ofK (g ^ z)
  let ok (b : ℕ) : Bool := (a.y0 >>> q) % 2 ^ b == 0 && q + b ≤ yVars && (List.range (2 ^ b)).all member &&
    injOk a.y0 (a.coef ++ (List.range b).map fun k ↦ 2 ^ (q + k))
  let b := ((List.range 7).reverse.find? ok).getD 0
  return if b == 0 then none else some (q, b, g)

/-- The terms with the geometric runs taken out: `(rest, runs)`, a run `(first term, q, b, g)`. -/
def mergeGeo (ts : Array CTerm) : Array CTerm × Array (CTerm × ℕ × ℕ × FK) := Id.run do
  let mut rest : Array CTerm := #[]
  let mut runs : Array (CTerm × ℕ × ℕ × FK) := #[]
  let mut i := 0
  while i < ts.size do
    match geoOf ts i with
    | some (q, b, g) =>
      runs := runs.push (ts.getD i default, q, b, g)
      i := i + 2 ^ b
    | none =>
      rest := rest.push (ts.getD i default)
      i := i + 1
  return (rest, runs)

/-- A geometric run's atom. -/
def CS.addGeo (s : CS) (r : CTerm × ℕ × ℕ × FK) : CS :=
  let (t, q, b, g) := r
  let a : Aff := match t.cls with | .aff a => a | _ => default
  let pairs := ((List.range t.l).map fun i ↦ (i, a.coef.getD i 0)).filter fun (_, c) ↦ c != 0 && log2 c < yVars
  let fs := pairs.map (fun (i, c) ↦ KF.pair i (log2 c)) ++ (List.range b).map fun k ↦ KF.ypow (q + k) (g ^ (2 ^ k))
  s.addAtom fs t.o t.l t.x0 (pairs.map (fun (_, c) ↦ log2 c) ++ (List.range b).map (q + ·)) a.y0 t.w

/-- **Slot-run merging**: affine terms equal but in their slot and first word, at slots `x0 + m·2^l` (`m < 2^k`,
`x0` aligned to `2^(l+k)`) with words `y0 + m·d`, are one term over `l + k` iteration bits (the slot's next bits
are the iteration's: `x0 + m·2^l + jf`). Unrolled rows (B1-Q's 64 booleanity rows of a `BITS` chunk, a gadget's
copies) collapse to one kernel. -/
def runMerge (ps : Array (CTerm × Option ℕ)) : Array (CTerm × Option ℕ) := Id.run do
  let mut grp : Std.HashMap (ℕ × FE × ℕ × List ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ)) := {}
  let mut out : Array (CTerm × Option ℕ) := #[]
  for i in [0:ps.size] do
    let (t, lim) := ps.getD i default
    match t.cls with
    | .aff a =>
      if t.wv.isEmpty && termWFB t && a.coef.length == t.l then
        let key := (t.o, t.w, t.l, a.coef, lim)
        grp := grp.insert key ((grp.getD key #[]).push (t.x0, a.y0, i))
      else out := out.push (t, lim)
    | _ => out := out.push (t, lim)
  for (_, g) in grp.toList do
    let g := g.qsort fun a b ↦ a.1 < b.1
    let mut i := 0
    while i < g.size do
      let (x0, y0, ix) := g.getD i (0, 0, 0)
      let (t, lim) := ps.getD ix default
      let a : Aff := match t.cls with | .aff a => a | _ => default
      let d := (g.getD (i + 1) (0, 0, 0)).2.1 - y0
      let ok (k : ℕ) : Bool :=
        x0 % 2 ^ (t.l + k) == 0 && i + 2 ^ k ≤ g.size && x0 + 2 ^ (t.l + k) ≤ 2 ^ xVars &&
          (List.range (2 ^ k)).all fun m ↦
            let (x', y', _) := g.getD (i + m) (0, 0, 0)
            x' == x0 + m * 2 ^ t.l && y' ≥ y0 && y' == y0 + m * d
      -- only when the merged map stays a bit injection (else the automaton would cost more than the atoms)
      let k1 (k : ℕ) : Bool := injOk y0 (a.coef ++ (List.range k).map (d * 2 ^ ·))
      let k := ((List.range 13).reverse.find? fun k ↦ ok k && k1 k).getD 0
      if k == 0 then out := out.push (t, lim)
      else
        out := out.push ({ t with l := t.l + k, cls := .aff ⟨y0, a.coef ++ (List.range k).map (d * 2 ^ ·)⟩ }, lim)
      i := i + 2 ^ k
  return out

/-! ## Sorting and the result -/

/-- Lexicographic order on keys. -/
def keysLt (a b : Array (ℕ × ℕ)) : Bool := Id.run do
  for i in [0:min a.size b.size] do
    let x := a.getD i (0, 0)
    let y := b.getD i (0, 0)
    if x.1 < y.1 then return true
    if x.1 > y.1 then return false
    if x.2 < y.2 then return true
    if x.2 > y.2 then return false
  return a.size < b.size

/-- Lexicographic order on keys, level `kl` (the selector) compared last. -/
def keysLtK (kl : ℕ) (a b : Array (ℕ × ℕ)) : Bool :=
  let perm (k : Array (ℕ × ℕ)) : Array (ℕ × ℕ) := (k.extract 0 kl ++ k.extract (kl + 1) k.size).push (k.getD kl (0, 0))
  keysLt (perm a) (perm b)

/-- **Merge atoms**: equal keys add their weights (zero sums drop: characteristic-2 cancellations); then atoms
equal but in the selector, with equal weights, merge their selector masks (level `kl`). Sorted at the end. -/
def mergeAtoms (kl : ℕ) (as : Array Atom) : Array Atom := Id.run do
  let srt := as.qsort fun a b ↦ keysLtK kl a.keys b.keys
  let mut m1 : Array Atom := #[]
  for a in srt do
    match m1.back? with
    | some b =>
      if b.keys == a.keys then m1 := m1.modify (m1.size - 1) fun b ↦ { b with w := b.w + a.w }
      else m1 := m1.push a
    | none => m1 := m1.push a
  let m1f := m1.filter fun a ↦ !(a.w == 0)
  let without (k : Array (ℕ × ℕ)) : Array (ℕ × ℕ) := k.extract 0 kl ++ k.extract (kl + 1) k.size
  let mut m2 : Array Atom := #[]
  for a in m1f do
    match m2.back? with
    | some b =>
      let mb := (b.keys.getD kl (0, 0)).2
      let ma := (a.keys.getD kl (0, 0)).2
      if without b.keys == without a.keys && b.w == a.w && mb &&& ma == 0 then
        m2 := m2.modify (m2.size - 1) fun b ↦ { b with keys := b.keys.set! kl (1, mb ||| ma) }
      else m2 := m2.push a
    | none => m2 := m2.push a
  return m2.qsort fun a b ↦ keysLt a.keys b.keys

/-- Pad every atom's keys with trivial keys to depth `D`. -/
def padTo (D : ℕ) (as : Array Atom) : Array Atom :=
  as.map fun a ↦ ⟨a.keys ++ Array.replicate (D - a.keys.size) (0, 0), a.w⟩

/-- The products of flat code (a weighted leaf, a keyed close). -/
def codeCost (c : Code) : ℕ := Id.run do
  let mut n := 0
  for k in [0:c.op.size] do
    let o := c.op.getD k 0
    if (o == 2 && c.wi.getD k 0 != 0) || (o == 1 && c.ta.getD k 0 != 0) then n := n + 1
  return n

/-- The automaton's products from the sorted distinct initial states (`autoStepP`'s count), and the final states'
count. -/
def simAuto (R n : ℕ) (st0 : Array ℕ) : ℕ × ℕ := Id.run do
  let mut st := st0
  let mut cost := 0
  for _ in [0:n] do
    let half (sh : ℕ) : Array (ℕ × Bool) := Id.run do
      let mut out : Array (ℕ × Bool) := #[]
      let mut i := 0
      while i < st.size do
        let c := st.getD i 0
        if (c + sh) % 2 == 0 && i + 1 < st.size && st.getD (i + 1) 0 == c + 1 then
          out := out.push ((c + sh) / 2, true); i := i + 2
        else
          out := out.push ((c + sh) / 2, false); i := i + 1
      return out
    let as := half 0
    let bs := half R
    cost := cost + 1 + (as.filter (·.2)).size + (bs.filter (·.2)).size
    let mut out : Array ℕ := #[]
    let mut i := 0
    let mut j := 0
    while i < as.size || j < bs.size do
      let (ta, pa) := as.getD i (0, false)
      let (tb, pb) := bs.getD j (0, false)
      if j ≥ bs.size || (i < as.size && ta < tb) then
        cost := cost + 1; out := out.push ta; i := i + 1
      else if i ≥ as.size || tb < ta then
        cost := cost + 1; out := out.push tb; j := j + 1
      else
        cost := cost + (if !pa && !pb then 2 else (if pa then 0 else 1) + (if pb then 0 else 1) + 1)
        out := out.push ta; i := i + 1; j := j + 1
    st := out
  return (cost, st.size)

/-- **A pass from its members** `(state, o, x, w)`, or their points when the simulated automaton costs more
(B1-P1P2 §3: "a group is enumerated as points when that is cheaper"). The finish tables cover `y`'s bits past
`n` (and past the limb bits of a merged cell). -/
def CS.mkPass (s : CS) (xs : List ℕ) (R : ℕ) (lim : Option ℕ) (raw : Array (ℕ × ℕ × ℕ × FE)) :
    CS × Option Pass :=
  let n := xs.length
  let sts := (raw.map (·.1)).qsort (· < ·)
  let dst := sts.foldl (fun (a : Array ℕ) c ↦ if a.back? == some c then a else a.push c) #[]
  let (ca, nf) := simAuto R n dst
  -- the points' exact cost: their atoms alone, merged and sorted, as code
  let pts (s : CS) : CS := raw.foldl (fun s (st, o, x, w) ↦
      (List.range (2 ^ n)).foldl (fun s j ↦
        let xx := x + ((List.range n).map fun k ↦ if j.testBit k then 2 ^ xs.getD k 0 else 0).sum
        s.addAtom [] o 0 xx [] (st + R * j) w lim) s) s
  let sp := pts { s with atoms := #[] }
  let pcost := if raw.size * 2 ^ n > 200000 then raw.size * 2 ^ n else
    let D := sp.atoms.foldl (fun d a ↦ max d a.keys.size) 0
    codeCost (atomCodeG (mergeAtoms 1 (padTo D sp.atoms)) D)
  if ca + 2 * nf + raw.size > pcost then (pts s, none)
  else
  let masked (b : ℕ) : Bool := b < n || (match lim with | some e => b == e || b == e + 1 | none => false)
  let free := (List.range yVars).filter (!masked ·)
  let groups := [free.filter (· < yCut), free.filter (· ≥ yCut)].filter (!·.isEmpty)
  let (s, fin) := groups.foldl (fun (acc : CS × Array (ℕ × List ℕ)) bs ↦
    let (s', t) := acc.1.tab (.eqy bs)
    (s', acc.2.push (t, bs.map (· - n)))) (s, #[])
  let (s, mem) := raw.foldl (fun (acc : CS × Array Atom) (st, o, x, w) ↦
    let (s', xk) := acc.1.rangeKeys true xVars xCut (fun b ↦ xs.contains b) x
    (s', acc.2.push ⟨(#[(0, st), (1, 1 <<< o)] ++ xk.reverse.toArray), w⟩)) (s, #[])
  let D := mem.foldl (fun d a ↦ max d a.keys.size) 0
  let ms := mergeAtoms 1 (padTo D mem)
  (s, some ⟨xs.toArray, R, ms, D, fin, lim, initCodeG ms D, none⟩)

/-- **The compiler.** -/
def compileT (ts : Array CTerm) : Comp :=
  let (rest, geos) := mergeGeo ts
  let s := geos.foldl CS.addGeo ({} : CS)
  let s := (runMerge (mergeLimbs rest)).foldl (fun s (t, lim) ↦ s.addTerm t lim) s
  let (s, ps) := s.pm.toList.foldl (fun (acc : CS × Array Pass) ((xs, R, lim), mem) ↦
    let (s', p) := acc.1.mkPass xs R lim mem
    (s', match p with | some p => acc.2.push p | none => acc.2)) (s, #[])
  let D := s.atoms.foldl (fun d a ↦ max d a.keys.size) 0
  let as := mergeAtoms 1 (padTo D s.atoms)
  let tabs := ((s.tabs.set! 2 (.ker s.kers)).set! 3 (.prod s.xm)).set! 4 (.prod s.ym)
  let code := atomCodeG as D
  { tabs, atoms := as, depth := D, passes := ps.map (fun p ↦ { p with fcode := fuse tabs p.code }), code,
    fcode := fuse tabs code }




/-! ## L-A: the proof of `compileT_eq` -/

open private Array.qpartition.loop from Init.Data.Array.QSort.Basic

open private Array.qsort.sort from Init.Data.Array.QSort.Basic

/-! ## `Array.qsort`: permutation, size and sortedness -/

/-- `w` is `v` with the positions in `[lo, hi]` permuted among themselves. -/
def qs_R {α : Type} {n : ℕ} (lo hi : ℕ) (v w : Vector α n) : Prop :=
  w.toList.Perm v.toList ∧ (∀ j (hj : j < n), (j < lo ∨ hi < j) → w[j] = v[j]) ∧
    (∀ j (hj : j < n), lo ≤ j → j ≤ hi → ∃ j', ∃ hj' : j' < n, lo ≤ j' ∧ j' ≤ hi ∧ w[j] = v[j'])

theorem qs_R_refl {α : Type} {n : ℕ} (lo hi : ℕ) (v : Vector α n) : qs_R lo hi v v :=
  ⟨List.Perm.refl _, fun _ _ _ ↦ rfl, fun j hj h1 h2 ↦ ⟨j, hj, h1, h2, rfl⟩⟩

theorem qs_R_trans {α : Type} {n : ℕ} {lo hi : ℕ} {u v w : Vector α n} (h₁ : qs_R lo hi u v)
    (h₂ : qs_R lo hi v w) : qs_R lo hi u w := by
  obtain ⟨p1, f1, m1⟩ := h₁
  obtain ⟨p2, f2, m2⟩ := h₂
  refine ⟨p2.trans p1, fun j hj h ↦ (f2 j hj h).trans (f1 j hj h), fun j hj h1 h2 ↦ ?_⟩
  obtain ⟨j', hj', a1, a2, e⟩ := m2 j hj h1 h2
  obtain ⟨j'', hj'', b1, b2, e'⟩ := m1 j' hj' a1 a2
  exact ⟨j'', hj'', b1, b2, e.trans e'⟩

theorem qs_R_mono {α : Type} {n : ℕ} {lo hi lo' hi' : ℕ} {v w : Vector α n} (h : qs_R lo' hi' v w)
    (hl : lo ≤ lo') (hh : hi' ≤ hi) : qs_R lo hi v w := by
  obtain ⟨p, f, m⟩ := h
  refine ⟨p, fun j hj h ↦ f j hj (by omega), fun j hj h1 h2 ↦ ?_⟩
  by_cases hin : lo' ≤ j ∧ j ≤ hi'
  · obtain ⟨j', hj', a1, a2, e⟩ := m j hj hin.1 hin.2
    exact ⟨j', hj', by omega, by omega, e⟩
  · exact ⟨j, hj, h1, h2, f j hj (by omega)⟩

theorem qs_R_swap {α : Type} {n : ℕ} {lo hi : ℕ} (v : Vector α n) (i k : ℕ) (hi' : i < n) (hk : k < n)
    (h1 : lo ≤ i) (h2 : i ≤ hi) (h3 : lo ≤ k) (h4 : k ≤ hi) : qs_R lo hi v (v.swap i k hi' hk) := by
  refine ⟨(Vector.swap_perm hi' hk).toList, fun j hj h ↦ ?_, fun j hj a1 a2 ↦ ?_⟩
  · rw [Vector.getElem_swap]
    split_ifs <;> first | rfl | omega
  · rw [Vector.getElem_swap]
    split_ifs
    · exact ⟨k, hk, h3, h4, rfl⟩
    · exact ⟨i, hi', h1, h2, rfl⟩
    · exact ⟨j, hj, a1, a2, rfl⟩

/-- The postcondition of a partition of `[lo, hi]` of `as`. -/
def qs_part {α : Type} {n : ℕ} (lt : α → α → Bool) (lo hi : ℕ) (hhi : hi < n) (as : Vector α n)
    (r : {m // lo ≤ m ∧ m ≤ hi} × Vector α n) : Prop :=
  qs_R lo hi as r.2 ∧
    (∀ j (hj : j < n), lo ≤ j → j < r.1.1 →
      lt r.2[j] (r.2[r.1.1]'(Nat.lt_of_le_of_lt r.1.2.2 hhi)) = true) ∧
    (∀ j (hj : j < n), r.1.1 < j → j ≤ hi →
      lt r.2[j] (r.2[r.1.1]'(Nat.lt_of_le_of_lt r.1.2.2 hhi)) = false)

theorem qs_part_of_R {α : Type} {n : ℕ} {lt : α → α → Bool} {lo hi : ℕ} {hhi : hi < n}
    {u v : Vector α n} {r : {m // lo ≤ m ∧ m ≤ hi} × Vector α n} (h : qs_R lo hi u v)
    (hp : qs_part lt lo hi hhi v r) : qs_part lt lo hi hhi u r :=
  ⟨qs_R_trans h hp.1, hp.2⟩

theorem qs_loop_part {α : Type} {n : ℕ} (lt : α → α → Bool) (lo hi : ℕ) (hhi : hi < n) (pivot : α)
    (as : Vector α n) (i k : ℕ) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) (hpiv : as[hi] = pivot)
    (h1 : ∀ j (hj : j < n), lo ≤ j → j < i → lt as[j] pivot = true)
    (h2 : ∀ j (hj : j < n), i ≤ j → j < k → lt as[j] pivot = false) :
    qs_part lt lo hi hhi as (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w) := by
  rw [Array.qpartition.loop.eq_def]
  by_cases h : k < hi
  · rw [dite_eq_left h]
    by_cases hl : lt as[k] pivot = true
    · rw [ite_eq_left hl]
      refine qs_part_of_R (qs_R_swap as i k (by omega) (by omega) ilo (by omega) (by omega) (by omega))
        (qs_loop_part lt lo hi hhi pivot _ (i + 1) (k + 1) _ _ _ ?_ ?_ ?_)
      · rw [Vector.getElem_swap]; split_ifs <;> omega
      · intro j hj a1 a2
        rw [Vector.getElem_swap]
        split_ifs with e1 e2
        · exact hl
        · omega
        · exact h1 j hj a1 (by omega)
      · intro j hj a1 a2
        rw [Vector.getElem_swap]
        split_ifs with e1 e2
        · omega
        · exact h2 i (by omega) le_rfl (by omega)
        · exact h2 j hj (by omega) (by omega)
    · rw [ite_eq_right hl]
      refine qs_loop_part lt lo hi hhi pivot as i (k + 1) _ _ _ hpiv h1 ?_
      intro j hj a1 a2
      by_cases e : j = k
      · subst e; simpa using hl
      · exact h2 j hj a1 (by omega)
  · rw [dite_eq_right h]
    have hk : k = hi := by omega
    refine ⟨qs_R_swap as i hi (by omega) hhi ilo (by omega) (by omega) le_rfl, ?_, ?_⟩
    · intro j hj a1 a2
      dsimp only at a2
      simp only [Vector.getElem_swap, ite_true]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), hpiv]
      exact h1 j hj a1 a2
    · intro j hj a1 a2
      dsimp only at a1
      simp only [Vector.getElem_swap, ite_true]
      rw [ite_eq_right (by omega), hpiv]
      split_ifs with e
      · exact h2 i (by omega) le_rfl (by omega)
      · exact h2 j hj (by omega) (by omega)
termination_by hi - k

theorem qs_loop_lt_hi {α : Type} {n : ℕ} (lt : α → α → Bool) (lo hi : ℕ) (hhi : hi < n) (pivot : α)
    (as : Vector α n) (i k : ℕ) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi)
    (h : i < k ∨ ∃ j, ∃ hj : j < n, k ≤ j ∧ j < hi ∧ lt as[j] pivot = false) :
    (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).1.1 < hi := by
  rw [Array.qpartition.loop.eq_def]
  by_cases hk : k < hi
  · rw [dite_eq_left hk]
    by_cases hl : lt as[k] pivot = true
    · rw [ite_eq_left hl]
      refine qs_loop_lt_hi lt lo hi hhi pivot _ (i + 1) (k + 1) _ _ _ ?_
      rcases h with h | ⟨j, hj, a1, a2, a3⟩
      · exact Or.inl (by omega)
      · right
        have hjk : j ≠ k := by rintro rfl; simp [hl] at a3
        refine ⟨j, hj, by omega, a2, ?_⟩
        rw [Vector.getElem_swap, ite_eq_right (by omega), ite_eq_right hjk]
        exact a3
    · rw [ite_eq_right hl]
      exact qs_loop_lt_hi lt lo hi hhi pivot as i (k + 1) _ _ _ (Or.inl (by omega))
  · rw [dite_eq_right hk]
    show i < hi
    rcases h with h | ⟨j, hj, a1, a2, a3⟩ <;> omega
termination_by hi - k

theorem qs_R_ite_swap {α : Type} {n : ℕ} {lo hi : ℕ} {v w : Vector α n} (h : qs_R lo hi v w) (c : Prop)
    [Decidable c] (i k : ℕ) (hi' : i < n) (hk : k < n) (h1 : lo ≤ i) (h2 : i ≤ hi) (h3 : lo ≤ k)
    (h4 : k ≤ hi) : qs_R lo hi v (if c then w.swap i k hi' hk else w) := by
  split_ifs
  · exact qs_R_trans h (qs_R_swap w i k hi' hk h1 h2 h3 h4)
  · exact h

theorem qs_ite_swap_not_lt {α : Type} {n : ℕ} (lt : α → α → Bool)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) (v : Vector α n) (a b : ℕ) (ha : a < n)
    (hb : b < n) (hab : a ≠ b) :
    lt (if lt v[a] v[b] = true then v.swap a b ha hb else v)[a]
      (if lt v[a] v[b] = true then v.swap a b ha hb else v)[b] = false := by
  by_cases hc : lt v[a] v[b] = true
  · simp only [hc, ite_true, Vector.getElem_swap]
    rw [ite_eq_right (Ne.symm hab)]
    exact hasymm _ _ hc
  · rw [ite_eq_right hc]
    simpa using hc

theorem qs_qpartition_part {α : Type} {n : ℕ} (lt : α → α → Bool) (as : Vector α n) (lo hi : ℕ)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    qs_part lt lo hi hhi as (Array.qpartition as lt lo hi w hlo hhi) := by
  unfold Array.qpartition
  dsimp only
  refine qs_part_of_R ?_ (qs_loop_part lt lo hi hhi _ _ lo lo _ _ _ rfl
    (fun j _ a b ↦ absurd b (by omega)) (fun j _ a b ↦ absurd b (by omega)))
  refine qs_R_ite_swap (qs_R_ite_swap (qs_R_ite_swap (qs_R_refl lo hi as) _ _ _ _ _ ?_ ?_ ?_ ?_)
    _ _ _ _ _ ?_ ?_ ?_ ?_) _ _ _ _ _ ?_ ?_ ?_ ?_ <;> omega

theorem qs_qpartition_lt_hi {α : Type} {n : ℕ} (lt : α → α → Bool)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) (as : Vector α n) (lo hi : ℕ)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (h : lo < hi) :
    (Array.qpartition as lt lo hi w hlo hhi).1.1 < hi := by
  unfold Array.qpartition
  dsimp only
  apply qs_loop_lt_hi
  right
  exact ⟨(lo + hi) / 2, by omega, by omega, by omega,
    qs_ite_swap_not_lt lt hasymm _ _ _ _ _ (by omega)⟩

theorem qs_sort_R {α : Type} (lt : α → α → Bool) {n : ℕ} (as : Vector α n) (lo hi : ℕ) (w : lo ≤ hi)
    (hlo : lo < n) (hhi : hi < n) : qs_R lo hi as (Array.qsort.sort lt as lo hi w hlo hhi) := by
  rw [Array.qsort.sort.eq_def]
  split
  · rename_i h₁
    have hp := qs_qpartition_part lt as lo hi w hlo hhi
    split
    rename_i mid hmid b heq
    rw [heq] at hp
    split
    · exact hp.1
    · rename_i h₂
      exact qs_R_trans hp.1 (qs_R_trans (qs_R_mono (qs_sort_R lt b lo mid _ _ _) le_rfl (by omega))
        (qs_R_mono (qs_sort_R lt _ (mid + 1) hi _ _ _) (by omega) le_rfl))
  · exact qs_R_refl _ _ _
termination_by hi - lo

theorem qs_sort_sorted {α : Type} (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) {n : ℕ} (as : Vector α n) (lo hi : ℕ)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (i j : ℕ) (hi' : i < n) (hj : j < n)
    (a1 : lo ≤ i) (a2 : i < j) (a3 : j ≤ hi) :
    lt (Array.qsort.sort lt as lo hi w hlo hhi)[j] (Array.qsort.sort lt as lo hi w hlo hhi)[i] = false := by
  rw [Array.qsort.sort.eq_def]
  split
  · rename_i h₁
    have hp := qs_qpartition_part lt as lo hi w hlo hhi
    have hlt := qs_qpartition_lt_hi lt hasymm as lo hi w hlo hhi h₁
    split
    rename_i mid hmid b heq
    rw [heq] at hp hlt
    dsimp only [qs_part] at hp hlt
    split
    · omega
    · rename_i h₂
      have Rc := qs_sort_R lt b lo mid hmid.1 hlo (by omega)
      have Rd := qs_sort_R lt (Array.qsort.sort lt b lo mid hmid.1 hlo (by omega)) (mid + 1) hi
        (by omega) (by omega) hhi
      by_cases hA : mid + 1 ≤ i
      · exact qs_sort_sorted lt htrans hasymm _ (mid + 1) hi _ _ _ i j hi' hj hA a2 a3
      by_cases hB : j ≤ mid
      · rw [Rd.2.1 i hi' (by omega), Rd.2.1 j hj (by omega)]
        exact qs_sort_sorted lt htrans hasymm b lo mid _ _ _ i j hi' hj a1 a2 hB
      · rw [Rd.2.1 i hi' (by omega)]
        obtain ⟨i', hi'', b1, b2, ei⟩ := Rc.2.2 i hi' a1 (by omega)
        obtain ⟨j', hj', c1, c2, ej⟩ := Rd.2.2 j hj (by omega) a3
        rw [ei, ej, Rc.2.1 j' hj' (by omega)]
        have hr := hp.2.2 j' hj' (by omega) c2
        by_cases e : i' = mid
        · subst e; exact hr
        · have hl := hp.2.1 i' hi'' b1 (by omega)
          cases hc : lt b[j'] b[i']
          · rfl
          · rw [htrans _ _ _ hc hl] at hr; exact hr
  · omega
termination_by hi - lo

theorem qs_qsort_perm {α : Type} (as : Array α) (lt : α → α → Bool) :
    (as.qsort lt).toList.Perm as.toList := by
  unfold Array.qsort
  split
  · exact List.Perm.refl _
  · exact (qs_sort_R lt as.toVector _ _ _ _ _).1

theorem qs_qsort_size {α : Type} (as : Array α) (lt : α → α → Bool) : (as.qsort lt).size = as.size := by
  unfold Array.qsort
  split
  · rfl
  · simp

theorem qs_qsort_sorted {α : Type} (as : Array α) (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) :
    (as.qsort lt).toList.Pairwise fun a b ↦ lt b a = false := by
  unfold Array.qsort
  split
  · rename_i h
    simp [Array.eq_empty_of_size_eq_zero h]
  · rename_i h
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [Array.length_toList, Vector.size_toArray] at hi hj
    simp only [Array.getElem_toList, Vector.getElem_toArray]
    exact qs_sort_sorted lt htrans hasymm as.toVector _ _ _ _ _ i j hi hj (by omega) hij (by omega)

/-! ## `keysLt` is the strict lexicographic order on `List (ℕ × ℕ)` -/

/-- The body of `keysLt`'s loop, verbatim. -/
def qs_kbody (a b : Array (ℕ × ℕ)) (i : ℕ) (_s : Option Bool × Unit) :
    Id (ForInStep (Option Bool × Unit)) :=
  let x := a.getD i (0, 0)
  let y := b.getD i (0, 0)
  if x.1 < y.1 then pure (ForInStep.done (some true, ()))
  else if x.1 > y.1 then pure (ForInStep.done (some false, ()))
  else if x.2 < y.2 then pure (ForInStep.done (some true, ()))
  else if x.2 > y.2 then pure (ForInStep.done (some false, ()))
  else pure (ForInStep.yield (none, ()))

theorem qs_keysLt_eq (a b : Array (ℕ × ℕ)) :
    keysLt a b = (match (forIn (m := Id) [:min a.size b.size] ((none : Option Bool), ())
      (qs_kbody a b)).run.1 with
      | some r => r
      | none => decide (a.size < b.size)) := by
  unfold keysLt
  simp only [Id.run_bind]
  unfold qs_kbody
  generalize (forIn (m := Id) [:min a.size b.size] ((none : Option Bool), ()) _).run = r
  rcases r with ⟨_ | _, _⟩ <;> rfl

theorem qs_kres (a b : Array (ℕ × ℕ)) (k : ℕ) : ∀ s, s + k = min a.size b.size →
    ((match (forIn (m := Id) (List.range' s k) ((none : Option Bool), ()) (qs_kbody a b)).run.1 with
      | some r => r
      | none => decide (a.size < b.size)) = true ↔
      List.Lex (Prod.Lex (· < ·) (· < ·)) (a.toList.drop s) (b.toList.drop s)) := by
  induction k with
  | zero =>
    intro s hs
    have ha : (a.toList.drop s).length = a.size - s := by simp
    have hb : (b.toList.drop s).length = b.size - s := by simp
    simp only [List.range'_zero, List.forIn_nil, Id.run_pure]
    cases hA : a.toList.drop s <;> cases hB : b.toList.drop s <;> simp [hA, hB] at ha hb ⊢ <;> omega
  | succ k ih =>
    intro s hs
    have hsa : s < a.size := by omega
    have hsb : s < b.size := by omega
    rw [List.range'_succ, List.forIn_cons,
      List.drop_eq_getElem_cons (l := a.toList) (i := s) (by simpa using hsa),
      List.drop_eq_getElem_cons (l := b.toList) (i := s) (by simpa using hsb),
      List.cons_lex_cons_iff, ← ih (s + 1) (by omega)]
    simp only [qs_kbody, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsa,
      Array.getElem?_eq_getElem hsb, Option.getD_some, Array.getElem_toList, Prod.lex_def, Id.run_bind]
    by_cases h1 : a[s].1 < b[s].1
    · simp [h1]
    by_cases h2 : a[s].1 > b[s].1
    · have hne : a[s] ≠ b[s] := fun e ↦ by rw [e] at h2; omega
      simp [h1, h2, hne]; omega
    by_cases h3 : a[s].2 < b[s].2
    · simp [h1, h2, h3]; omega
    by_cases h4 : a[s].2 > b[s].2
    · have hne : a[s] ≠ b[s] := fun e ↦ by rw [e] at h4; omega
      simp [h1, h2, h3, h4, hne]
    have e : a[s] = b[s] := Prod.ext (by omega) (by omega)
    simp [e]

theorem qs_keysLt_iff (a b : Array (ℕ × ℕ)) :
    keysLt a b = true ↔ List.Lex (Prod.Lex (· < ·) (· < ·)) a.toList b.toList := by
  rw [qs_keysLt_eq, Std.Legacy.Range.forIn_eq_forIn_range']
  have := qs_kres a b (min a.size b.size) 0 (by omega)
  simpa [Std.Legacy.Range.size] using this

theorem qs_prodLex_trans {x y z : ℕ × ℕ} (h₁ : Prod.Lex (· < ·) (· < ·) x y)
    (h₂ : Prod.Lex (· < ·) (· < ·) y z) : Prod.Lex (· < ·) (· < ·) x z := by
  rw [Prod.lex_def] at *
  omega

theorem qs_keysLt_trans (a b c : Array (ℕ × ℕ)) :
    keysLt a b = true → keysLt b c = true → keysLt a c = true := by
  simp only [qs_keysLt_iff]
  exact fun h₁ h₂ ↦ List.lex_trans qs_prodLex_trans h₁ h₂

theorem qs_keysLt_asymm (a b : Array (ℕ × ℕ)) : keysLt a b = true → keysLt b a = false := by
  intro h
  rw [qs_keysLt_iff] at h
  rw [Bool.eq_false_iff, ne_eq, qs_keysLt_iff]
  exact List.lex_asymm (fun {x y} h₁ h₂ ↦ by rw [Prod.lex_def] at h₁ h₂; omega) h

theorem qs_sorted_head (l : List Atom) (h : l.Pairwise fun a b ↦ keysLt b.keys a.keys = false)
    (hne : ∀ a ∈ l, 0 < a.keys.size) :
    l.Pairwise fun a b ↦ (a.keys.getD 0 (0,0)).1 < (b.keys.getD 0 (0,0)).1 ∨
      ((a.keys.getD 0 (0,0)).1 = (b.keys.getD 0 (0,0)).1 ∧
        (a.keys.getD 0 (0,0)).2 ≤ (b.keys.getD 0 (0,0)).2) := by
  refine h.imp_of_mem fun {a b} ha hb hab ↦ ?_
  have hA := hne a ha
  have hB := hne b hb
  have h0 : ¬ List.Lex (Prod.Lex (· < ·) (· < ·)) b.keys.toList a.keys.toList := by
    rw [← qs_keysLt_iff, hab]
    simp
  have eA := List.drop_eq_getElem_cons (l := a.keys.toList) (i := 0) (by simpa using hA)
  have eB := List.drop_eq_getElem_cons (l := b.keys.toList) (i := 0) (by simpa using hB)
  rw [List.drop_zero] at eA eB
  rw [eA, eB, List.cons_lex_cons_iff] at h0
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hA, Array.getElem?_eq_getElem hB,
    Option.getD_some]
  simp only [Array.getElem_toList, Prod.lex_def] at h0
  omega

theorem qs_keysLtK_trans (kl : ℕ) (a b c : Array (ℕ × ℕ)) :
    keysLtK kl a b = true → keysLtK kl b c = true → keysLtK kl a c = true :=
  qs_keysLt_trans _ _ _

theorem qs_keysLtK_asymm (kl : ℕ) (a b : Array (ℕ × ℕ)) :
    keysLtK kl a b = true → keysLtK kl b a = false :=
  qs_keysLt_asymm _ _

/-- The use in `mergeAtoms`: the final sort is sorted. -/
example (m2 : Array Atom) :
    (m2.qsort fun a b ↦ keysLt a.keys b.keys).toList.Pairwise
      fun a b ↦ keysLt b.keys a.keys = false :=
  qs_qsort_sorted m2 _ (fun a b c ↦ qs_keysLt_trans a.keys b.keys c.keys)
    (fun a b ↦ qs_keysLt_asymm a.keys b.keys)


/-! ## Semantics -/

/-- `eq(pt, idx)` of the entry `(o, x, y)`. -/
def ct_E (pt : List FE) (o x y : ℕ) : FE := eqW pt (o + 4 * (x + 2 ^ xVars * y))

/-- With a merged `E` cell (`lim = some e`): the three limbs `y + m·2^e`, weights `y^m`. -/
def ct_EL (pt : List FE) (lim : Option ℕ) (o x y : ℕ) : FE :=
  match lim with
  | none => ct_E pt o x y
  | some e => ct_E pt o x y + FE.y * ct_E pt o x (y + 2 ^ e) + FE.y * FE.y * ct_E pt o x (y + 2 * 2 ^ e)

/-- A term with its limb merge: the sum it stands for. -/
def ct_pairSum (pt : List FE) (p : CTerm × Option ℕ) : FE :=
  ((List.range (2 ^ p.1.l)).map fun jf ↦ p.1.wAt jf * ct_EL pt p.2 p.1.o (p.1.x0 + jf) (p.1.cls.at jf)).sum

/-- A limb merge is valid: constant weight, the limb bits free in every word. -/
def ct_LimOk (t : CTerm) : Option ℕ → Prop
  | none => True
  | some e => t.wv = [] ∧ e + 1 < yVars ∧ ∀ jf < 2 ^ t.l, (t.cls.at jf >>> e) % 4 = 0

/-- The affine map of an `aff` class (`default` otherwise). -/
def ct_affOf : OpClass → Aff
  | .aff a => a
  | _ => default

/-- A geometric run's sum. -/
def ct_geoSum (pt : List FE) (r : CTerm × ℕ × ℕ × FK) : FE :=
  let (t, q, b, g) := r
  let a := ct_affOf t.cls
  ((List.range (2 ^ b)).map fun z ↦ ((List.range (2 ^ t.l)).map fun jf ↦
    t.w * FE.ofK (g ^ z) * ct_E pt t.o (t.x0 + jf) (a.at jf + z * 2 ^ q)).sum).sum

/-- A geometric run is valid (what `geoOf` checks). -/
def ct_GeoOk (r : CTerm × ℕ × ℕ × FK) : Prop :=
  let (t, q, b, _) := r
  ∃ a, t.cls = .aff a ∧ t.wv = [] ∧ TermWF t ∧ a.coef.length = t.l ∧
    injOk a.y0 (a.coef ++ (List.range b).map fun k ↦ 2 ^ (q + k)) = true ∧
    (a.y0 >>> q) % 2 ^ b = 0 ∧ q + b ≤ yVars

/-- A pass member's sum: `(st, o, x, w)` over the automaton's `2^n` steps. -/
def ct_memSem (pt : List FE) (key : List ℕ × ℕ × Option ℕ) (m : ℕ × ℕ × ℕ × FE) : FE :=
  ((List.range (2 ^ key.1.length)).map fun j ↦
    m.2.2.2 * ct_EL pt key.2.2 m.2.1
      (m.2.2.1 + ((List.range key.1.length).map fun k ↦ if j.testBit k then 2 ^ key.1.getD k 0 else 0).sum)
      (m.1 + key.2.1 * j)).sum

/-- A pass member is valid. -/
def ct_MemOk (key : List ℕ × ℕ × Option ℕ) (m : ℕ × ℕ × ℕ × FE) : Prop :=
  m.2.1 < 4 ∧ key.1.Pairwise (· < ·) ∧ (∀ b ∈ key.1, b < xVars) ∧ (∀ b ∈ key.1, m.2.2.1.testBit b = false) ∧
    m.2.2.1 < 2 ^ xVars ∧
    (match key.2.2 with
     | none => True
     | some e => key.1.length ≤ e ∧ e + 1 < yVars ∧ ∀ j < 2 ^ key.1.length, ((m.1 + key.2.1 * j) >>> e) % 4 = 0)

/-! ## The compiler state's invariants -/

/-- The masks' value. -/
def ct_kapV (P : Pt) (m : ℕ) : FE :=
  ((List.range 4).map fun o ↦ if m.testBit o then eqW (sub P.kap 0 2) o else 0).sum

/-- **Tables consistent with a state**: every key the state can have made has its value. -/
def ct_Cons (P : Pt) (s : CS) (T : Array (Array FE)) : Prop :=
  keyVal T (0, 0) = 1 ∧
  (∀ m < 16, keyVal T (1, m) = ct_kapV P m) ∧
  (∀ (i : ℕ) (fs : List KF), s.kers[i]? = some fs → keyVal T (2, i) = kerVal P fs) ∧
  (∀ (t : ℕ) (bits : List ℕ), s.tabs[t]? = some (.eqx bits) → ∀ v < 2 ^ bits.length,
    keyVal T (t, v) = eqW (bits.map fun b ↦ P.rx.getD b 0) v) ∧
  (∀ (t : ℕ) (bits : List ℕ), s.tabs[t]? = some (.eqy bits) → ∀ v < 2 ^ bits.length,
    keyVal T (t, v) = eqW (bits.map fun b ↦ P.ry.getD b 0) v)

/-- A bit list of one table group: sorted, inside `[0, cut)` or `[cut, N)`. -/
def ct_GrpOk (N cut : ℕ) (bits : List ℕ) : Prop :=
  bits.Pairwise (· < ·) ∧ ((∀ b ∈ bits, b < cut) ∨ (∀ b ∈ bits, cut ≤ b ∧ b < N))

/-- The recipe of a table key. -/
def ct_rec : TKey → TRec
  | .eqx bs => .eqx bs
  | .eqy bs => .eqy bs

/-- An atom's keys are well shaped: a selector `(1, m < 16)` at level 1, trivial keys `(0, 0)`. -/
def ct_AtomOk (a : Atom) : Prop :=
  2 ≤ a.keys.size ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧ (a.keys.getD 1 (0, 0)).2 < 16 ∧
    ∀ k ∈ a.keys, k.1 = 0 → k.2 = 0

/-- **The state invariant.** -/
structure ct_WF (s : CS) : Prop where
  size : 5 ≤ s.tabs.size
  t0 : s.tabs[0]? = some .one
  t1 : s.tabs[1]? = some .kap
  eqx : ∀ (t : ℕ) (bits : List ℕ), s.tabs[t]? = some (.eqx bits) → 5 ≤ t ∧ ct_GrpOk xVars xCut bits
  eqy : ∀ (t : ℕ) (bits : List ℕ), s.tabs[t]? = some (.eqy bits) → 5 ≤ t ∧ ct_GrpOk yVars yCut bits
  tix : ∀ (k : TKey) (i : ℕ), s.tix[k]? = some i → s.tabs[i]? = some (ct_rec k)
  kix : ∀ (fs : List KF) (i : ℕ), s.kix[fs]? = some i → s.kers[i]? = some fs
  atoms : ∀ a ∈ s.atoms, ct_AtomOk a
  pm : ∀ (k : List ℕ × ℕ × Option ℕ) (ms : Array (ℕ × ℕ × ℕ × FE)), s.pm[k]? = some ms → ∀ m ∈ ms, ct_MemOk k m

/-- `s'` extends `s`: its tables and kernels start with `s`'s. -/
def ct_Le (s s' : CS) : Prop :=
  (∀ (i : ℕ) (r : TRec), s.tabs[i]? = some r → s'.tabs[i]? = some r) ∧
    (∀ (i : ℕ) (fs : List KF), s.kers[i]? = some fs → s'.kers[i]? = some fs)

/-- The atoms' sum. -/
def ct_aSum (T : Array (Array FE)) (s : CS) : FE := (s.atoms.toList.map (atomVal T)).sum

/-- The pass members' sum. -/
def ct_pmSum (pt : List FE) (s : CS) : FE :=
  (s.pm.toList.map fun km ↦ (km.2.toList.map (ct_memSem pt km.1)).sum).sum

/-- **A step adds `V`**: invariants kept, the state extended, and every consistent table sees `V` more. -/
def ct_Adds (pt : List FE) (s s' : CS) (V : FE) : Prop :=
  ct_WF s' ∧ ct_Le s s' ∧ ∀ T, ct_Cons (Pt.ofList pt) s' T →
    ct_aSum T s' + ct_pmSum pt s' = ct_aSum T s + ct_pmSum pt s + V

/-! ## Framework lemmas (C7) -/

theorem ct_Le_refl (s : CS) : ct_Le s s := ⟨fun _ _ h ↦ h, fun _ _ h ↦ h⟩

theorem ct_Le_trans {s₁ s₂ s₃ : CS} (h₁ : ct_Le s₁ s₂) (h₂ : ct_Le s₂ s₃) : ct_Le s₁ s₃ :=
  ⟨fun i r h ↦ h₂.1 i r (h₁.1 i r h), fun i fs h ↦ h₂.2 i fs (h₁.2 i fs h)⟩

theorem ct_Cons_mono {P : Pt} {s s' : CS} {T : Array (Array FE)} (h : ct_Le s s') (hc : ct_Cons P s' T) :
    ct_Cons P s T :=
  ⟨hc.1, hc.2.1, fun i fs hi ↦ hc.2.2.1 i fs (h.2 i fs hi), fun t bits ht ↦ hc.2.2.2.1 t bits (h.1 t _ ht),
    fun t bits ht ↦ hc.2.2.2.2 t bits (h.1 t _ ht)⟩

theorem ct_Adds_trans {pt : List FE} {s₁ s₂ s₃ : CS} {V₁ V₂ : FE} (h₁ : ct_Adds pt s₁ s₂ V₁)
    (h₂ : ct_Adds pt s₂ s₃ V₂) : ct_Adds pt s₁ s₃ (V₁ + V₂) := by
  refine ⟨h₂.1, ct_Le_trans h₁.2.1 h₂.2.1, fun T hT ↦ ?_⟩
  rw [h₂.2.2 T hT, h₁.2.2 T (ct_Cons_mono h₂.2.1 hT)]
  ring

theorem ct_Adds_refl {pt : List FE} {s : CS} (h : ct_WF s) : ct_Adds pt s s 0 :=
  ⟨h, ct_Le_refl s, fun _ _ ↦ by ring⟩

theorem ct_Adds_congr {pt : List FE} {s s' : CS} {V V' : FE} (h : ct_Adds pt s s' V) (e : V = V') :
    ct_Adds pt s s' V' := e ▸ h

/-- A fold of steps. -/
theorem ct_Adds_foldl {α : Type} (pt : List FE) (f : CS → α → CS) (v : α → FE) (P : α → Prop)
    (hf : ∀ s a, ct_WF s → P a → ct_Adds pt s (f s a) (v a)) :
    ∀ (l : List α) (s : CS), ct_WF s → (∀ a ∈ l, P a) → ct_Adds pt s (l.foldl f s) (l.map v).sum := by
  intro l
  induction l with
  | nil => intro s hs _; simpa using ct_Adds_refl (pt := pt) hs
  | cons a l ih =>
    intro s hs hl
    have h1 := hf s a hs (hl a (by simp))
    have h2 := ih (f s a) h1.1 (fun b hb ↦ hl b (by simp [hb]))
    simpa [List.foldl_cons, List.map_cons, List.sum_cons] using ct_Adds_trans h1 h2

/-- The empty state. -/
theorem ct_WF_empty : ct_WF ({} : CS) := by
  refine ⟨by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t bits h
    match t with
    | 0 | 1 | 2 | 3 | 4 => simp at h
    | _ + 5 => simp at h
  · intro t bits h
    match t with
    | 0 | 1 | 2 | 3 | 4 => simp at h
    | _ + 5 => simp at h
  · intro k i h; simp at h
  · intro fs i h; simp at h
  · intro a ha; simp at ha
  · intro k ms h; simp at h

theorem ct_pmSum_empty (pt : List FE) : ct_pmSum pt ({} : CS) = 0 := by
  simp [ct_pmSum]

theorem ct_aSum_empty (T : Array (Array FE)) : ct_aSum T ({} : CS) = 0 := by
  simp [ct_aSum]

/-! ## Shared algebra and state operations (C0; black boxes for C1–C6) -/

/-- `eq` on the listed coordinates of `r` at the bits of `v`. -/
def ct_eqOn (r : Array FE) (bits : List ℕ) (v : ℕ) : FE := (bits.map fun b ↦ eq1 (r.getD b 0) (v.testBit b)).prod

theorem c0a_eqW_range (r : Array FE) (n : ℕ) : ∀ (lo v : ℕ),
    eqW ((List.range n).map fun k ↦ r.getD (lo + k) 0) v =
      ((List.range n).map fun k ↦ eq1 (r.getD (lo + k) 0) (v.testBit k)).prod := by
  induction n with
  | zero => intro lo v; simp [eqW]
  | succ n ih =>
    intro lo v
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.prod_cons, eqW, List.map_map, List.map_map]
    have e1 : (List.range n).map ((fun k ↦ r.getD (lo + k) 0) ∘ Nat.succ) =
        (List.range n).map fun k ↦ r.getD (lo + 1 + k) 0 :=
      List.map_congr_left (fun k _ ↦ by simp only [Function.comp_apply]; congr 1; omega)
    have e2 : (List.range n).map ((fun k ↦ eq1 (r.getD (lo + k) 0) (v.testBit k)) ∘ Nat.succ) =
        (List.range n).map fun k ↦ eq1 (r.getD (lo + 1 + k) 0) ((v / 2).testBit k) :=
      List.map_congr_left (fun k _ ↦ by
        simp only [Function.comp_apply, Nat.testBit_div_two]; congr 2; omega)
    rw [e1, e2, ih (lo + 1) (v / 2), Nat.testBit_zero]
    by_cases h : v % 2 = 1 <;> simp [h, eq1]

theorem ct_eqW_sub (r : Array FE) (n v : ℕ) : eqW (sub r 0 n) v = ct_eqOn r (List.range n) v := by
  simpa [sub, ct_eqOn] using c0a_eqW_range r n 0 v

theorem ct_eqOn_append (r : Array FE) (A B : List ℕ) (v : ℕ) :
    ct_eqOn r (A ++ B) v = ct_eqOn r A v * ct_eqOn r B v := by
  simp [ct_eqOn, List.prod_append]

theorem ct_eqOn_perm (r : Array FE) {A B : List ℕ} (h : A.Perm B) (v : ℕ) : ct_eqOn r A v = ct_eqOn r B v :=
  (h.map _).prod_eq

theorem ct_eqOn_congr (r : Array FE) (A : List ℕ) (v v' : ℕ) (h : ∀ b ∈ A, v.testBit b = v'.testBit b) :
    ct_eqOn r A v = ct_eqOn r A v' := by
  unfold ct_eqOn
  rw [List.map_congr_left (fun b hb ↦ by rw [h b hb])]

theorem c0a_sub_self (L : List FE) : sub L.toArray 0 L.length = L := by
  apply List.ext_getElem (by simp [sub])
  intro i h1 h2
  simp [sub, Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem h2]

/-- `eq` of `pt` at an entry index splits into the selector, the slot and the word (bits of the word past
`yVars` are ignored). -/
theorem ct_E_split (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (o x y : ℕ) (ho : o < 4)
    (hx : x < 2 ^ xVars) :
    ct_E pt o x y = eqW (sub (Pt.ofList pt).kap 0 2) o * ct_eqOn (Pt.ofList pt).rx (List.range xVars) x *
      ct_eqOn (Pt.ofList pt).ry (List.range yVars) y := by
  set A := pt.take 2 with hA
  set B := (pt.drop 2).take xVars with hB
  set C := (pt.drop (2 + xVars)).take yVars with hC
  have hAl : A.length = 2 := by simp only [hA, List.length_take, hpt]; omega
  have hBl : B.length = xVars := by simp only [hB, List.length_take, List.length_drop, hpt]; omega
  have hCl : C.length = yVars := by simp only [hC, List.length_take, List.length_drop, hpt]; omega
  have hsplit : pt = A ++ (B ++ C) := by
    have e1 : pt.drop (2 + xVars) = C := by
      rw [hC, List.take_of_length_le (by simp only [List.length_drop, hpt]; omega)]
    have e2 : (pt.drop 2).drop xVars = pt.drop (2 + xVars) := by simp [List.drop_drop]
    calc pt = A ++ pt.drop 2 := (List.take_append_drop _ _).symm
      _ = A ++ (B ++ (pt.drop 2).drop xVars) := by rw [hB, List.take_append_drop xVars (pt.drop 2)]
      _ = A ++ (B ++ C) := by rw [e2, e1]
  have hkap : (Pt.ofList pt).kap = A.toArray := rfl
  have hrx : (Pt.ofList pt).rx = B.toArray := rfl
  have hry : (Pt.ofList pt).ry = C.toArray := rfl
  rw [hkap, hrx, hry, ← ct_eqW_sub, ← ct_eqW_sub, ← hAl, ← hBl, ← hCl, c0a_sub_self, c0a_sub_self,
    c0a_sub_self, ct_E]
  conv_lhs => rw [hsplit]
  rw [show (4 : ℕ) = 2 ^ A.length by rw [hAl]; rfl, tab_eqW_append _ _ _ _ (by rw [hAl]; omega), ← hBl,
    tab_eqW_append _ _ _ _ (by rw [hBl]; exact hx)]
  ring

/-- The sum over the cube of a product of one-bit factors. -/
theorem ct_sum_prod_bits (l : ℕ) (f : ℕ → Bool → FE) :
    ((List.range (2 ^ l)).map fun jf ↦ ((List.range l).map fun i ↦ f i (jf.testBit i)).prod).sum =
      ((List.range l).map fun i ↦ f i false + f i true).prod := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ, mul_two, List.range_add (n := 2 ^ l) (m := 2 ^ l), List.map_append, List.sum_append,
      List.map_map]
    simp only [List.range_succ (n := l), List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one]
    have e1 : ((List.range (2 ^ l)).map fun jf ↦
        ((List.range l).map fun i ↦ f i (jf.testBit i)).prod * f l (jf.testBit l)) =
        (List.range (2 ^ l)).map fun jf ↦ ((List.range l).map fun i ↦ f i (jf.testBit i)).prod * f l false := by
      apply List.map_congr_left
      intro jf hjf
      rw [Nat.testBit_lt_two_pow (List.mem_range.1 hjf)]
    have e2 : ((List.range (2 ^ l)).map ((fun jf ↦
        ((List.range l).map fun i ↦ f i (jf.testBit i)).prod * f l (jf.testBit l)) ∘ (2 ^ l + ·))) =
        (List.range (2 ^ l)).map fun jf ↦ ((List.range l).map fun i ↦ f i (jf.testBit i)).prod * f l true := by
      apply List.map_congr_left
      intro jf hjf
      have hj := List.mem_range.1 hjf
      simp only [Function.comp_apply, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj, Bool.not_false]
      congr 1
      apply congrArg
      apply List.map_congr_left
      intro i hi
      rw [Nat.testBit_two_pow_add_gt (List.mem_range.1 hi)]
    rw [e1, e2, List.sum_map_mul_right, List.sum_map_mul_right, ih]
    ring

/-- The selector key's value. -/
theorem ct_kapV_single (P : Pt) (o : ℕ) (ho : o < 4) : ct_kapV P (1 <<< o) = eqW (sub P.kap 0 2) o := by
  simp only [ct_kapV, Nat.one_shiftLeft, Nat.testBit_two_pow]
  interval_cases o <;> simp [List.range_succ]

/-- The kernel of an atom with its limb factor. -/
def ct_limFs (fs : List KF) : Option ℕ → List KF
  | some e => fs ++ [KF.limb e]
  | none => fs

/-- The kernel's `y` bits with the limb bits. -/
def ct_limYm (ym : List ℕ) : Option ℕ → List ℕ
  | some e => ym ++ [e, e + 1]
  | none => ym

/-- The `x` bits an atom keys: those at or above `xm`. -/
def ct_xFree (xm : ℕ) : List ℕ := (List.range xVars).filter fun b ↦ !decide (b < xm)

/-- The `y` bits an atom keys: those not in `ym`. -/
def ct_yFree (ym : List ℕ) : List ℕ := (List.range yVars).filter fun b ↦ !ym.contains b

theorem c0b_eqOn_perm (r : Array FE) {A B : List ℕ} (h : A.Perm B) (v : ℕ) : ct_eqOn r A v = ct_eqOn r B v :=
  (h.map _).prod_eq

theorem c0b_kapV_single (P : Pt) (o : ℕ) (ho : o < 4) : ct_kapV P (1 <<< o) = eqW (sub P.kap 0 2) o := by
  interval_cases o <;> simp +decide [ct_kapV, List.range_succ]

instance c0b_lawfulBEq_TKey : LawfulBEq TKey where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp only [BEq.beq] at h <;> unfold instBEqTKey.beq at h <;> simp_all
  rfl {a} := by cases a <;> simp only [BEq.beq] <;> unfold instBEqTKey.beq <;> simp

theorem c0b_get_push {α : Type} (a : Array α) (x y : α) (i : ℕ) (h : a[i]? = some y) : (a.push x)[i]? = some y := by
  have hi : i < a.size := by
    by_contra hc; rw [Array.getElem?_eq_none (by omega)] at h; exact absurd h (by simp)
  rw [Array.getElem?_push, ite_eq_right_iff.mpr (fun h' ↦ absurd h' (by omega)), h]

theorem c0b_tab_new (s : CS) (hs : ct_WF s) (k : TKey)
    (hk : match k with | .eqx bs => ct_GrpOk xVars xCut bs | .eqy bs => ct_GrpOk yVars yCut bs) (r : TRec)
    (hr : r = ct_rec k) :
    ct_WF { s with tabs := s.tabs.push r, tix := s.tix.insert k s.tabs.size } ∧
      ct_Le s { s with tabs := s.tabs.push r, tix := s.tix.insert k s.tabs.size } ∧
      5 ≤ s.tabs.size ∧ (s.tabs.push r)[s.tabs.size]? = some (ct_rec k) := by
  subst hr
  have hsz := hs.size
  have hnew : ∀ (t : ℕ) (r : TRec), (s.tabs.push (ct_rec k))[t]? = some r →
      (t = s.tabs.size ∧ r = ct_rec k) ∨ s.tabs[t]? = some r := by
    intro t r ht
    rw [Array.getElem?_push] at ht
    split_ifs at ht with h1
    · exact Or.inl ⟨h1, (Option.some.inj ht).symm⟩
    · exact Or.inr ht
  refine ⟨⟨by simp; omega, c0b_get_push _ _ _ _ hs.t0, c0b_get_push _ _ _ _ hs.t1, ?_, ?_, ?_, hs.kix, hs.atoms,
    hs.pm⟩, ⟨fun i r hi ↦ c0b_get_push _ _ _ _ hi, fun _ _ h ↦ h⟩, hsz, by simp⟩
  · intro t bits ht
    rcases hnew t _ ht with ⟨rfl, hr⟩ | ho
    · cases k with
      | eqx bs => cases hr; exact ⟨hsz, hk⟩
      | eqy bs => cases hr
    · exact hs.eqx t bits ho
  · intro t bits ht
    rcases hnew t _ ht with ⟨rfl, hr⟩ | ho
    · cases k with
      | eqx bs => cases hr
      | eqy bs => cases hr; exact ⟨hsz, hk⟩
    · exact hs.eqy t bits ho
  · intro k' i hk'
    simp only at hk'
    rw [Std.HashMap.getElem?_insert] at hk'
    split_ifs at hk' with he
    · cases hk'
      rw [← eq_of_beq he]
      simp
    · exact c0b_get_push _ _ _ _ (hs.tix k' i hk')

theorem ct_tab (s : CS) (hs : ct_WF s) (k : TKey)
    (hk : match k with | .eqx bs => ct_GrpOk xVars xCut bs | .eqy bs => ct_GrpOk yVars yCut bs) :
    ct_WF (s.tab k).1 ∧ ct_Le s (s.tab k).1 ∧ (s.tab k).1.atoms = s.atoms ∧ (s.tab k).1.pm = s.pm ∧
      (s.tab k).1.kers = s.kers ∧ 5 ≤ (s.tab k).2 ∧ (s.tab k).1.tabs[(s.tab k).2]? = some (ct_rec k) := by
  unfold CS.tab
  cases h : s.tix[k]? with
  | some i =>
    have hi := hs.tix k i h
    refine ⟨hs, ct_Le_refl s, rfl, rfl, rfl, ?_, hi⟩
    cases k with
    | eqx bs => exact (hs.eqx i bs hi).1
    | eqy bs => exact (hs.eqy i bs hi).1
  | none =>
    cases k with
    | eqx bs =>
      obtain ⟨h1, h2, h3, h4⟩ := c0b_tab_new s hs (.eqx bs) hk _ rfl
      exact ⟨h1, h2, rfl, rfl, rfl, h3, h4⟩
    | eqy bs =>
      obtain ⟨h1, h2, h3, h4⟩ := c0b_tab_new s hs (.eqy bs) hk _ rfl
      exact ⟨h1, h2, rfl, rfl, rfl, h3, h4⟩

theorem ct_ker (s : CS) (hs : ct_WF s) (fs : List KF) :
    ct_WF (s.ker fs).1 ∧ ct_Le s (s.ker fs).1 ∧ (s.ker fs).1.atoms = s.atoms ∧ (s.ker fs).1.pm = s.pm ∧
      (s.ker fs).1.tabs = s.tabs ∧ (s.ker fs).1.kers[(s.ker fs).2]? = some fs := by
  unfold CS.ker
  cases h : s.kix[fs]? with
  | some i => exact ⟨hs, ct_Le_refl s, rfl, rfl, rfl, hs.kix fs i h⟩
  | none =>
    refine ⟨⟨hs.size, hs.t0, hs.t1, hs.eqx, hs.eqy, hs.tix, ?_, hs.atoms, hs.pm⟩,
      ⟨fun _ _ h ↦ h, fun i r hi ↦ c0b_get_push _ _ _ _ hi⟩, rfl, rfl, rfl, by simp⟩
    intro fs' i hk'
    simp only at hk'
    rw [Std.HashMap.getElem?_insert] at hk'
    split_ifs at hk' with he
    · cases hk'
      rw [← eq_of_beq he]
      simp
    · exact c0b_get_push _ _ _ _ (hs.kix fs' i hk')

theorem c0b_pextGo_succ (v : ℕ) : ∀ (bs : List ℕ) (k : ℕ), pextGo v (k + 1) bs = 2 * pextGo v k bs
  | [], _ => rfl
  | b :: bs, k => by
    simp only [pextGo]
    rw [c0b_pextGo_succ v bs (k + 1)]
    split <;> simp [Nat.shiftLeft_eq, pow_succ]; ring

theorem c0b_pext_cons (v b : ℕ) (bs : List ℕ) :
    pext v (b :: bs) = (if v.testBit b then 1 else 0) + 2 * pext v bs := by
  simp only [pext, pextGo, c0b_pextGo_succ]
  split <;> simp

theorem c0b_pext_lt (v : ℕ) : ∀ bs : List ℕ, pext v bs < 2 ^ bs.length
  | [] => by simp [pext, pextGo]
  | b :: bs => by
    rw [c0b_pext_cons]
    have := c0b_pext_lt v bs
    simp only [List.length_cons, pow_succ]
    split <;> omega

theorem c0b_eqW_pext (r : Array FE) (v : ℕ) :
    ∀ bs : List ℕ, eqW (bs.map fun b ↦ r.getD b 0) (pext v bs) = ct_eqOn r bs v
  | [] => by simp [eqW, ct_eqOn]
  | b :: bs => by
    rw [c0b_pext_cons, List.map_cons, eqW]
    have ih := c0b_eqW_pext r v bs
    simp only [ct_eqOn, List.map_cons, List.prod_cons, eq1] at ih ⊢
    cases v.testBit b
    · have h1 : (0 + 2 * pext v bs) % 2 = 0 := by omega
      have h2 : (0 + 2 * pext v bs) / 2 = pext v bs := by omega
      simp only [Bool.false_eq_true, ite_false, h1, h2, ih]
      simp
    · have h1 : (1 + 2 * pext v bs) % 2 = 1 := by omega
      have h2 : (1 + 2 * pext v bs) / 2 = pext v bs := by omega
      simp only [ite_true, h1, h2, ih]

theorem c0b_prod_filter_ne {α : Type} (f : List α → FE) (hf : f [] = 1) :
    ∀ G : List (List α), ((G.filter (!·.isEmpty)).map f).prod = (G.map f).prod
  | [] => rfl
  | g :: G => by
    cases g with
    | nil => simp [hf, c0b_prod_filter_ne f hf G]
    | cons a g => simp [c0b_prod_filter_ne f hf G]

/-- The hypothesis of `ct_tab`. -/
def c0b_hk (k : TKey) : Prop := match k with | .eqx bs => ct_GrpOk xVars xCut bs | .eqy bs => ct_GrpOk yVars yCut bs

/-- `rangeKeys`'s step. -/
def c0b_rkF (isX : Bool) (v : ℕ) (acc : CS × List (ℕ × ℕ)) (bs : List ℕ) : CS × List (ℕ × ℕ) :=
  let (s', t) := acc.1.tab (if isX then .eqx bs else .eqy bs)
  (s', acc.2 ++ [(t, pext v bs)])

theorem c0b_keyVal (P : Pt) (s : CS) (T : Array (Array FE)) (hc : ct_Cons P s T) (isX : Bool) (t : ℕ)
    (bs : List ℕ) (v : ℕ) (ht : s.tabs[t]? = some (ct_rec (if isX then .eqx bs else .eqy bs))) :
    keyVal T (t, pext v bs) = ct_eqOn (if isX then P.rx else P.ry) bs v := by
  cases isX
  · simp only [Bool.false_eq_true, ite_false, ct_rec] at ht ⊢
    rw [hc.2.2.2.2 t bs ht _ (c0b_pext_lt v bs), c0b_eqW_pext]
  · simp only [ite_true, ct_rec] at ht ⊢
    rw [hc.2.2.2.1 t bs ht _ (c0b_pext_lt v bs), c0b_eqW_pext]

theorem c0b_rk_fold (P : Pt) (isX : Bool) (v : ℕ) :
    ∀ (G : List (List ℕ)) (s : CS) (acc : List (ℕ × ℕ)), ct_WF s →
      (∀ bs ∈ G, c0b_hk (if isX then .eqx bs else .eqy bs)) →
      ct_WF (G.foldl (c0b_rkF isX v) (s, acc)).1 ∧ ct_Le s (G.foldl (c0b_rkF isX v) (s, acc)).1 ∧
      (G.foldl (c0b_rkF isX v) (s, acc)).1.atoms = s.atoms ∧ (G.foldl (c0b_rkF isX v) (s, acc)).1.pm = s.pm ∧
      ∃ ks, (G.foldl (c0b_rkF isX v) (s, acc)).2 = acc ++ ks ∧ (∀ k ∈ ks, 5 ≤ k.1) ∧
        ∀ T, ct_Cons P (G.foldl (c0b_rkF isX v) (s, acc)).1 T →
          (ks.map (keyVal T)).prod = (G.map fun bs ↦ ct_eqOn (if isX then P.rx else P.ry) bs v).prod := by
  intro G
  induction G with
  | nil =>
    intro s acc hs _
    exact ⟨hs, ct_Le_refl s, rfl, rfl, [], by simp, by simp, fun _ _ ↦ by simp⟩
  | cons bs G ih =>
    intro s acc hs hG
    obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := ct_tab s hs (if isX then .eqx bs else .eqy bs) (hG bs (by simp))
    have hstep : c0b_rkF isX v (s, acc) bs =
        ((s.tab (if isX then .eqx bs else .eqy bs)).1, acc ++ [((s.tab (if isX then .eqx bs else .eqy bs)).2, pext v bs)]) := rfl
    simp only [List.foldl_cons, hstep]
    generalize s.tab (if isX then .eqx bs else .eqy bs) = q at h1 h2 h3 h4 h6 h7
    obtain ⟨g1, g2, g3, g4, ks, g5, g6, g7⟩ := ih q.1 (acc ++ [(q.2, pext v bs)]) h1 (fun b hb ↦ hG b (by simp [hb]))
    refine ⟨g1, ct_Le_trans h2 g2, g3.trans h3, g4.trans h4, (q.2, pext v bs) :: ks, by simp [g5], ?_, ?_⟩
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact h6
      · exact g6 k hk
    · intro T hT
      simp only [List.map_cons, List.prod_cons]
      rw [g7 T hT, c0b_keyVal P q.1 T (ct_Cons_mono g2 hT) isX q.2 bs v h7]

theorem c0b_grp (N cut : ℕ) (mask : ℕ → Bool) :
    ∀ bs ∈ [((List.range N).filter (!mask ·)).filter (· < cut), ((List.range N).filter (!mask ·)).filter (· ≥ cut)].filter
      (!·.isEmpty), ct_GrpOk N cut bs := by
  intro bs hbs
  have hsort : ((List.range N).filter (!mask ·)).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hbs
  rcases hbs.1 with rfl | rfl
  · refine ⟨hsort.filter _, Or.inl fun b hb ↦ ?_⟩
    simp only [List.mem_filter] at hb
    simpa using hb.2
  · refine ⟨hsort.filter _, Or.inr fun b hb ↦ ?_⟩
    simp only [List.mem_filter, List.mem_range] at hb
    exact ⟨by simpa using hb.2, hb.1.1⟩

theorem c0b_rangeKeys (P : Pt) (s : CS) (hs : ct_WF s) (isX : Bool) (N cut : ℕ) (mask : ℕ → Bool) (v : ℕ)
    (hG : ∀ bs, ct_GrpOk N cut bs → c0b_hk (if isX then .eqx bs else .eqy bs)) :
    ct_WF (s.rangeKeys isX N cut mask v).1 ∧ ct_Le s (s.rangeKeys isX N cut mask v).1 ∧
      (s.rangeKeys isX N cut mask v).1.atoms = s.atoms ∧ (s.rangeKeys isX N cut mask v).1.pm = s.pm ∧
      (∀ k ∈ (s.rangeKeys isX N cut mask v).2, 5 ≤ k.1) ∧
      ∀ T, ct_Cons P (s.rangeKeys isX N cut mask v).1 T →
        ((s.rangeKeys isX N cut mask v).2.map (keyVal T)).prod =
          ct_eqOn (if isX then P.rx else P.ry) ((List.range N).filter fun b ↦ !mask b) v := by
  have e : s.rangeKeys isX N cut mask v = ([((List.range N).filter (!mask ·)).filter (· < cut),
      ((List.range N).filter (!mask ·)).filter (· ≥ cut)].filter (!·.isEmpty)).foldl (c0b_rkF isX v) (s, []) := rfl
  rw [e]
  obtain ⟨g1, g2, g3, g4, ks, g5, g6, g7⟩ := c0b_rk_fold P isX v _ s [] hs
    (fun bs hbs ↦ hG bs (c0b_grp N cut mask bs hbs))
  simp only [List.nil_append] at g5
  rw [g5]
  refine ⟨g1, g2, g3, g4, g6, fun T hT ↦ ?_⟩
  rw [g7 T hT, c0b_prod_filter_ne _ (by simp [ct_eqOn])]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← ct_eqOn_append]
  apply c0b_eqOn_perm
  have := List.filter_append_perm (fun b ↦ decide (b < cut)) ((List.range N).filter fun b ↦ !mask b)
  rwa [List.filter_congr (p := fun b ↦ !decide (b < cut)) (q := fun b ↦ decide (b ≥ cut)) (by intro x _; by_cases h : x < cut <;> simp [h]; omega)]
    at this

theorem ct_rangeKeysX (P : Pt) (s : CS) (hs : ct_WF s) (mask : ℕ → Bool) (v : ℕ) :
    ct_WF (s.rangeKeys true xVars xCut mask v).1 ∧ ct_Le s (s.rangeKeys true xVars xCut mask v).1 ∧
      (s.rangeKeys true xVars xCut mask v).1.atoms = s.atoms ∧ (s.rangeKeys true xVars xCut mask v).1.pm = s.pm ∧
      (∀ k ∈ (s.rangeKeys true xVars xCut mask v).2, 5 ≤ k.1) ∧
      ∀ T, ct_Cons P (s.rangeKeys true xVars xCut mask v).1 T →
        ((s.rangeKeys true xVars xCut mask v).2.map (keyVal T)).prod =
          ct_eqOn P.rx ((List.range xVars).filter fun b ↦ !mask b) v :=
  c0b_rangeKeys P s hs true xVars xCut mask v (fun _ h ↦ h)

theorem ct_rangeKeysY (P : Pt) (s : CS) (hs : ct_WF s) (mask : ℕ → Bool) (v : ℕ) :
    ct_WF (s.rangeKeys false yVars yCut mask v).1 ∧ ct_Le s (s.rangeKeys false yVars yCut mask v).1 ∧
      (s.rangeKeys false yVars yCut mask v).1.atoms = s.atoms ∧ (s.rangeKeys false yVars yCut mask v).1.pm = s.pm ∧
      (∀ k ∈ (s.rangeKeys false yVars yCut mask v).2, 5 ≤ k.1) ∧
      ∀ T, ct_Cons P (s.rangeKeys false yVars yCut mask v).1 T →
        ((s.rangeKeys false yVars yCut mask v).2.map (keyVal T)).prod =
          ct_eqOn P.ry ((List.range yVars).filter fun b ↦ !mask b) v :=
  c0b_rangeKeys P s hs false yVars yCut mask v (fun _ h ↦ h)

def c0b_atomCore (s : CS) (fs : List KF) (o xm x : ℕ) (ym : List ℕ) (y : ℕ) (w : FE) : CS :=
  let q1 := if fs.isEmpty then (s, 0) else s.ker fs
  let q2 := q1.1.rangeKeys true xVars xCut (fun b ↦ b < xm) x
  let q3 := q2.1.rangeKeys false yVars yCut (fun b ↦ ym.contains b) y
  let kk : ℕ × ℕ := if fs.isEmpty then (0, 0) else (2, q1.2)
  { q3.1 with atoms := q3.1.atoms.push ⟨(([kk, (1, 1 <<< o)] : List (ℕ × ℕ)) ++ CS.interleave q2.2.reverse q3.2.reverse).toArray, w⟩ }

theorem c0b_interleave_perm {α : Type} : ∀ (a b : List α), (CS.interleave a b).Perm (a ++ b)
  | [], [] => by simp [CS.interleave]
  | [], _ :: _ => by simp [CS.interleave]
  | _ :: _, [] => by simp [CS.interleave]
  | x :: xs, y :: ys => by
    simp only [CS.interleave, List.cons_append]
    exact List.Perm.cons x ((List.Perm.cons y (c0b_interleave_perm xs ys)).trans List.perm_middle.symm)

theorem c0b_foldl_mul (f : ℕ × ℕ → FE) : ∀ (l : List (ℕ × ℕ)) (w : FE),
    l.foldl (fun acc k ↦ acc * f k) w = w * (l.map f).prod
  | [], w => by simp
  | k :: l, w => by simp only [List.foldl_cons, c0b_foldl_mul f l, List.map_cons, List.prod_cons]; ring

theorem c0b_atomVal (T : Array (Array FE)) (l : List (ℕ × ℕ)) (w : FE) :
    atomVal T ⟨l.toArray, w⟩ = w * (l.map (keyVal T)).prod := by
  simp only [atomVal, List.foldl_toArray']
  exact c0b_foldl_mul _ l w

/-- Pushing a well-shaped atom. -/
theorem c0b_atom_push (pt : List FE) (s s3 : CS) (hs3 : ct_WF s3) (hle : ct_Le s s3) (hat : s3.atoms = s.atoms)
    (hpm : s3.pm = s.pm) (keys : List (ℕ × ℕ)) (w V : FE) (hok : ct_AtomOk ⟨keys.toArray, w⟩)
    (hval : ∀ T, ct_Cons (Pt.ofList pt) s3 T → w * (keys.map (keyVal T)).prod = V) :
    ct_Adds pt s { s3 with atoms := s3.atoms.push ⟨keys.toArray, w⟩ } V := by
  refine ⟨⟨hs3.size, hs3.t0, hs3.t1, hs3.eqx, hs3.eqy, hs3.tix, hs3.kix, ?_, hs3.pm⟩, hle, fun T hT ↦ ?_⟩
  · intro a ha
    rcases Array.mem_push.mp ha with ha | rfl
    · exact hs3.atoms a ha
    · exact hok
  · have e1 : ct_aSum T { s3 with atoms := s3.atoms.push ⟨keys.toArray, w⟩ } = ct_aSum T s + V := by
      simp only [ct_aSum, Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, hat, c0b_atomVal, hval T hT]
    have e2 : ct_pmSum pt { s3 with atoms := s3.atoms.push ⟨keys.toArray, w⟩ } = ct_pmSum pt s := by
      simp only [ct_pmSum, hpm]
    rw [e1, e2]; ring

/-- The kernel step of an atom. -/
theorem c0b_kerStep (s : CS) (hs : ct_WF s) (fs : List KF) :
    ct_WF (if fs.isEmpty then (s, 0) else s.ker fs).1 ∧ ct_Le s (if fs.isEmpty then (s, 0) else s.ker fs).1 ∧
      (if fs.isEmpty then (s, 0) else s.ker fs).1.atoms = s.atoms ∧
      (if fs.isEmpty then (s, 0) else s.ker fs).1.pm = s.pm ∧
      (fs.isEmpty = false → (if fs.isEmpty then (s, 0) else s.ker fs).1.kers[(if fs.isEmpty then (s, 0) else s.ker fs).2]? = some fs) := by
  cases h : fs.isEmpty
  · obtain ⟨h1, h2, h3, h4, -, h6⟩ := ct_ker s hs fs
    exact ⟨h1, h2, h3, h4, fun _ ↦ h6⟩
  · exact ⟨hs, ct_Le_refl s, rfl, rfl, fun h' ↦ absurd h' (by simp)⟩

theorem c0b_shift_lt (o : ℕ) (ho : o < 4) : 1 <<< o < 16 := by
  interval_cases o <;> decide

theorem c0b_addAtomCore (pt : List FE) (s : CS) (hs : ct_WF s) (fs : List KF) (o xm x : ℕ) (ym : List ℕ) (y : ℕ)
    (w : FE) (ho : o < 4) :
    ct_Adds pt s (c0b_atomCore s fs o xm x ym y w)
      (w * eqW (sub (Pt.ofList pt).kap 0 2) o * kerVal (Pt.ofList pt) fs *
        ct_eqOn (Pt.ofList pt).rx (ct_xFree xm) x * ct_eqOn (Pt.ofList pt).ry (ct_yFree ym) y) := by
  dsimp only [c0b_atomCore]
  obtain ⟨a1, a2, a3, a4, a5⟩ := c0b_kerStep s hs fs
  generalize (if fs.isEmpty then (s, 0) else s.ker fs) = q1 at a1 a2 a3 a4 a5 ⊢
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := ct_rangeKeysX (Pt.ofList pt) q1.1 a1 (fun b ↦ b < xm) x
  generalize q1.1.rangeKeys true xVars xCut (fun b ↦ b < xm) x = q2 at b1 b2 b3 b4 b5 b6 ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ct_rangeKeysY (Pt.ofList pt) q2.1 b1 (fun b ↦ ym.contains b) y
  generalize q2.1.rangeKeys false yVars yCut (fun b ↦ ym.contains b) y = q3 at c1 c2 c3 c4 c5 c6 ⊢
  have hperm : (CS.interleave q2.2.reverse q3.2.reverse).Perm (q2.2 ++ q3.2) :=
    (c0b_interleave_perm _ _).trans (List.reverse_perm _ |>.append (List.reverse_perm _))
  apply c0b_atom_push pt s q3.1 c1 (ct_Le_trans a2 (ct_Le_trans b2 c2)) (c3.trans (b3.trans a3)) (c4.trans (b4.trans a4))
  · refine ⟨by simp, by simp, by simpa using c0b_shift_lt o ho, ?_⟩
    intro k hk hk0
    simp only [List.mem_toArray, List.cons_append, List.mem_cons] at hk
    rcases hk with rfl | rfl | hk
    · cases h : fs.isEmpty <;> simp_all
    · simp at hk0
    · rcases List.mem_append.mp (hperm.mem_iff.mp hk) with hk | hk
      · have := b5 k hk; omega
      · have := c5 k hk; omega
  · intro T hT
    have hT2 : ct_Cons (Pt.ofList pt) q2.1 T := ct_Cons_mono c2 hT
    have hT1 : ct_Cons (Pt.ofList pt) q1.1 T := ct_Cons_mono b2 hT2
    have hkk : keyVal T (if fs.isEmpty then (0, 0) else (2, q1.2)) = kerVal (Pt.ofList pt) fs := by
      cases h : fs.isEmpty
      · exact hT1.2.2.1 q1.2 fs (a5 h)
      · have : fs = [] := List.isEmpty_iff.mp h
        subst this
        simpa [kerVal] using hT1.1
    have hsel : keyVal T (1, 1 <<< o) = eqW (sub (Pt.ofList pt).kap 0 2) o := by
      rw [hT.2.1 _ (c0b_shift_lt o ho), c0b_kapV_single _ o ho]
    simp only [List.cons_append, List.map_cons, List.prod_cons, hkk, hsel, (hperm.map (keyVal T)).prod_eq,
      List.map_append, List.prod_append, b6 T hT2, c6 T hT, List.map_nil, List.prod_nil]
    simp only [ct_xFree, ct_yFree]
    ring

/-- **An atom.** -/
theorem ct_addAtom (pt : List FE) (s : CS) (hs : ct_WF s) (fs : List KF) (o xm x : ℕ) (ym : List ℕ) (y : ℕ)
    (w : FE) (lim : Option ℕ) (ho : o < 4) :
    ct_Adds pt s (s.addAtom fs o xm x ym y w lim)
      (w * eqW (sub (Pt.ofList pt).kap 0 2) o * kerVal (Pt.ofList pt) (ct_limFs fs lim) *
        ct_eqOn (Pt.ofList pt).rx (ct_xFree xm) x * ct_eqOn (Pt.ofList pt).ry (ct_yFree (ct_limYm ym lim)) y) := by
  have e : s.addAtom fs o xm x ym y w lim = c0b_atomCore s (ct_limFs fs lim) o xm x (ct_limYm ym lim) y w := by
    cases lim <;> rfl
  rw [e]
  exact c0b_addAtomCore pt s hs _ o xm x _ y w ho

theorem c0b_filter_key {K β : Type} [BEq K] [Hashable K] [LawfulBEq K] (m : Std.HashMap K β) (k : K) :
    (m.toList.filter fun x ↦ k == x.1) = match m[k]? with | some v => [(k, v)] | none => [] := by
  have hmem : ∀ x ∈ m.toList.filter (fun x ↦ k == x.1), x.1 = k ∧ m[k]? = some x.2 := by
    intro x hx
    rw [List.mem_filter] at hx
    have e : x.1 = k := (eq_of_beq hx.2).symm
    refine ⟨e, ?_⟩
    rw [← e]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx.1
  have hpw : (m.toList.filter fun x ↦ k == x.1).Pairwise (fun a b ↦ (a.1 == b.1) = false) :=
    (Std.HashMap.distinct_keys_toList (m := m)).filter _
  cases h : m[k]? with
  | none =>
    simp only
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have := (hmem x hx).2
    rw [h] at this
    exact absurd this (by simp)
  | some v =>
    simp only
    have hin : (k, v) ∈ m.toList.filter fun x ↦ k == x.1 := by
      rw [List.mem_filter]
      exact ⟨Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h, by simp⟩
    generalize m.toList.filter (fun x ↦ k == x.1) = l at hmem hpw hin
    match l, hmem, hpw, hin with
    | [], _, _, hin => simp at hin
    | [a], hmem, _, hin =>
      simp only [List.mem_singleton] at hin
      rw [hin]
    | a :: b :: t, hmem, hpw, _ =>
      have h1 := (hmem a (by simp)).1
      have h2 := (hmem b (by simp)).1
      have := List.rel_of_pairwise_cons hpw (a' := b) (by simp)
      rw [h1, h2] at this
      simp at this

/-- The sum over a hash map of arrays after an insert. -/
theorem c0b_sum_insert {K α : Type} [BEq K] [Hashable K] [LawfulBEq K] (m : Std.HashMap K (Array α))
    (F : K → α → FE) (k : K) (a : Array α) :
    ((m.insert k a).toList.map fun km ↦ (km.2.toList.map (F km.1)).sum).sum + ((m.getD k #[]).toList.map (F k)).sum =
      (m.toList.map fun km ↦ (km.2.toList.map (F km.1)).sum).sum + (a.toList.map (F k)).sum := by
  set g : K × Array α → FE := fun km ↦ (km.2.toList.map (F km.1)).sum with hg
  rw [((Std.HashMap.toList_insert_perm (m := m) (k := k) (v := a)).map g).sum_eq]
  have hp := ((List.filter_append_perm (fun x : K × Array α ↦ k == x.1) m.toList).map g).sum_eq
  rw [← hp, c0b_filter_key, List.filter_congr (q := fun x : K × Array α ↦ !(k == x.1)) (by intro x _; simp)]
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases m[k]? <;> simp [hg] <;> ring

theorem c0b_fold_push (o x : ℕ) : ∀ (ms : List (ℕ × FE)) (A : Array (ℕ × ℕ × ℕ × FE)),
    (ms.foldl (fun a (p : ℕ × FE) ↦ a.push (p.1, o, x, p.2)) A).toList = A.toList ++ ms.map fun p ↦ (p.1, o, x, p.2)
  | [], A => by simp
  | p :: ms, A => by
    simp only [List.foldl_cons, c0b_fold_push o x ms, Array.toList_push, List.map_cons, List.append_assoc,
      List.singleton_append]

/-- Inserting pass members. -/
theorem c0b_push (pt : List FE) (s : CS) (hs : ct_WF s) (key : List ℕ × ℕ × Option ℕ) (o x : ℕ)
    (ms : List (ℕ × FE)) (hms : ∀ p ∈ ms, ct_MemOk key (p.1, o, x, p.2)) :
    ct_Adds pt s { s with pm := s.pm.insert key (ms.foldl (fun a (p : ℕ × FE) ↦ a.push (p.1, o, x, p.2))
      (s.pm.getD key #[])) } ((ms.map fun p ↦ ct_memSem pt key (p.1, o, x, p.2)).sum) := by
  refine ⟨⟨hs.size, hs.t0, hs.t1, hs.eqx, hs.eqy, hs.tix, hs.kix, hs.atoms, ?_⟩, ct_Le_refl s, fun T _ ↦ ?_⟩
  · intro k' ms' hk' m hm
    simp only at hk'
    rw [Std.HashMap.getElem?_insert] at hk'
    split_ifs at hk' with he
    · cases hk'
      have e := eq_of_beq he
      subst e
      rw [← Array.mem_toList_iff, c0b_fold_push, List.mem_append] at hm
      rcases hm with hm | hm
      · rw [Std.HashMap.getD_eq_getD_getElem?] at hm
        cases h : s.pm[key]? with
        | none => rw [h] at hm; simp at hm
        | some old => rw [h] at hm; exact hs.pm key old h m (Array.mem_toList_iff.mp hm)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
        exact hms p hp
    · exact hs.pm k' ms' hk' m hm
  · have h := c0b_sum_insert s.pm (ct_memSem pt) key
      (ms.foldl (fun a (p : ℕ × FE) ↦ a.push (p.1, o, x, p.2)) (s.pm.getD key #[]))
    rw [c0b_fold_push, List.map_append, List.sum_append, List.map_map] at h
    have e : ct_pmSum pt { s with pm := s.pm.insert key (ms.foldl (fun a (p : ℕ × FE) ↦ a.push (p.1, o, x, p.2))
        (s.pm.getD key #[])) } = ct_pmSum pt s + (ms.map fun p ↦ ct_memSem pt key (p.1, o, x, p.2)).sum := by
      simp only [ct_pmSum]
      have h' := h
      simp only [Function.comp_def] at h'
      linear_combination h'
    rw [e]
    simp only [ct_aSum]
    ring

theorem c0b_memSem_limb (pt : List FE) (xs : List ℕ) (R st o x e : ℕ) (w : FE) :
    ct_memSem pt (xs, R, some e) (st, o, x, w) =
      ct_memSem pt (xs, R, none) (st, o, x, w) + ct_memSem pt (xs, R, none) (st + 2 ^ e, o, x, w * FE.y) +
        ct_memSem pt (xs, R, none) (st + 2 * 2 ^ e, o, x, w * FE.y * FE.y) := by
  simp only [ct_memSem, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [ct_EL]
  rw [show st + 2 ^ e + R * j = st + R * j + 2 ^ e by ring, show st + 2 * 2 ^ e + R * j = st + R * j + 2 * 2 ^ e by ring]
  ring

/-- **A pass member.** -/
theorem ct_addMember (pt : List FE) (s : CS) (hs : ct_WF s) (xs : List ℕ) (R st o x : ℕ) (w : FE)
    (lim : Option ℕ) (hok : ct_MemOk (xs, R, none) (st, o, x, w))
    (hlim : match lim with
      | none => True
      | some e => e + 1 < yVars ∧ ∀ j < 2 ^ xs.length, ((st + R * j) >>> e) % 4 = 0) :
    ct_Adds pt s (s.addMember xs R st o x w lim) (ct_memSem pt (xs, R, lim) (st, o, x, w)) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hok
  have hnone : ∀ st' w', ct_MemOk (xs, R, none) (st', o, x, w') := fun _ _ ↦ ⟨h1, h2, h3, h4, h5, trivial⟩
  unfold CS.addMember
  cases lim with
  | none =>
    exact ct_Adds_congr (c0b_push pt s hs (xs, R, none) o x [(st, w)] (by simp [hnone])) (by simp)
  | some e =>
    dsimp only
    split_ifs with he
    · have hm : ct_MemOk (xs, R, some e) (st, o, x, w) := ⟨h1, h2, h3, h4, h5, he, hlim⟩
      exact ct_Adds_congr (c0b_push pt s hs (xs, R, some e) o x [(st, w)]
        (fun p hp ↦ by rw [List.mem_singleton] at hp; subst hp; exact hm)) (by simp)
    · refine ct_Adds_congr (c0b_push pt s hs (xs, R, none) o x
        [(st, w), (st + 2 ^ e, w * FE.y), (st + 2 * 2 ^ e, w * FE.y * FE.y)] (by simp [hnone])) ?_
      rw [c0b_memSem_limb]
      simp [add_assoc]

/-! ## The merge loops as folds -/

/-- One step of a merge loop: merge `a` into the last atom `b` (by `H b a`) if `C b a`, else push it. -/
def c4_mstep (C : Atom → Atom → Bool) (H : Atom → Atom → Atom → Atom) (m : Array Atom) (a : Atom) : Array Atom :=
  match m.back? with
  | some b => if C b a then m.modify (m.size - 1) (H b a) else m.push a
  | none => m.push a

/-- The first merge: equal keys add weights. -/
def c4_C1 (b a : Atom) : Bool := b.keys == a.keys

def c4_H1 (_ a : Atom) (b : Atom) : Atom := { keys := b.keys, w := b.w + a.w }

/-- The keys without the selector level. -/
def c4_wo (k : Array (ℕ × ℕ)) : Array (ℕ × ℕ) := k.extract 0 1 ++ k.extract (1 + 1)

/-- The second merge: equal but the selector, equal weights, disjoint masks. -/
def c4_C3 (b a : Atom) : Bool :=
  c4_wo b.keys == c4_wo a.keys && b.w == a.w && (b.keys.getD 1 (0, 0)).2 &&& (a.keys.getD 1 (0, 0)).2 == 0

def c4_H3 (b a : Atom) (b1 : Atom) : Atom :=
  { keys := b1.keys.set! 1 (1, (b.keys.getD 1 (0, 0)).2 ||| (a.keys.getD 1 (0, 0)).2), w := b1.w }

theorem c4_forIn_arr {α β : Type} (xs : Array α) (init : β) (B : α → β → Id (ForInStep β))
    (F : β → α → β) (hB : ∀ a b, B a b = pure (ForInStep.yield (F b a))) :
    forIn xs init B = pure (xs.foldl F init) := by
  have : B = fun a b ↦ pure (ForInStep.yield (F b a)) := funext fun a ↦ funext fun b ↦ hB a b
  subst this
  simp

theorem c4_mergeAtoms_eq (as : Array Atom) :
    mergeAtoms 1 as = ((Array.filter (fun a ↦ !a.w == 0)
      ((as.qsort fun a b ↦ keysLtK 1 a.keys b.keys).foldl (c4_mstep c4_C1 c4_H1) #[])).foldl
        (c4_mstep c4_C3 c4_H3) #[]).qsort fun a b ↦ keysLt a.keys b.keys := by
  unfold mergeAtoms
  simp only [Id.run]
  rw [c4_forIn_arr _ _ _ (c4_mstep c4_C1 c4_H1)
    (by
      intro a s; unfold c4_mstep; cases s.back?
      · rfl
      · exact (apply_ite (fun x : Array Atom ↦ (pure (ForInStep.yield x) : Id _)) _ _ _).symm)]
  simp only [pure_bind]
  rw [c4_forIn_arr _ _ _ (c4_mstep c4_C3 c4_H3)
    (by
      intro a s; unfold c4_mstep; cases s.back?
      · rfl
      · exact (apply_ite (fun x : Array Atom ↦ (pure (ForInStep.yield x) : Id _)) _ _ _).symm)]
  rfl

theorem c4_modify_last (m : Array Atom) (b : Atom) (g : Atom → Atom) (h : m.back? = some b) :
    ∃ l, m.toList = l ++ [b] ∧ (m.modify (m.size - 1) g).toList = l ++ [g b] := by
  have h' : m.toList.getLast? = some b := by rw [Array.getLast?_toList]; exact h
  refine ⟨m.toList.dropLast, (List.dropLast_append_getLast? _ h').symm, ?_⟩
  rw [Array.toList_modify]
  conv => lhs; rw [← List.dropLast_append_getLast? _ h']
  have : m.size - 1 = m.toList.dropLast.length := by simp
  rw [this, List.modify_eq_take_cons_drop (by simp)]
  simp

/-- **A merge loop** keeps a key property `Q` and the sum of `V`, if each merge does. -/
theorem c4_fold (Q : Atom → Prop) (V : Atom → FE) (C : Atom → Atom → Bool) (H : Atom → Atom → Atom → Atom)
    (hH : ∀ b a, Q b → Q a → C b a = true → Q (H b a b) ∧ V (H b a b) = V b + V a) :
    ∀ (l : List Atom) (m : Array Atom), (∀ x ∈ m, Q x) → (∀ a ∈ l, Q a) →
      (∀ x ∈ l.foldl (c4_mstep C H) m, Q x) ∧
        ((l.foldl (c4_mstep C H) m).toList.map V).sum = (m.toList.map V).sum + (l.map V).sum := by
  intro l
  induction l with
  | nil => intro m hm _; simpa using hm
  | cons a l ih =>
    intro m hm hl
    have ha : Q a := hl a (by simp)
    have hl' : ∀ x ∈ l, Q x := fun x hx ↦ hl x (by simp [hx])
    rw [List.foldl_cons]
    have hstep : (∀ x ∈ c4_mstep C H m a, Q x) ∧
        ((c4_mstep C H m a).toList.map V).sum = (m.toList.map V).sum + V a := by
      unfold c4_mstep
      rcases hb : m.back? with _ | b
      · simp only
        refine ⟨fun x hx ↦ ?_, by simp⟩
        rcases Array.mem_push.1 hx with hx | hx
        · exact hm x hx
        · exact hx ▸ ha
      · simp only
        split_ifs with hc
        · obtain ⟨L, hL, hL'⟩ := c4_modify_last m b (H b a) hb
          have hQb : Q b := hm b (by rw [← Array.mem_toList_iff, hL]; simp)
          obtain ⟨hQ, hV⟩ := hH b a hQb ha hc
          refine ⟨fun x hx ↦ ?_, ?_⟩
          · rw [← Array.mem_toList_iff, hL'] at hx
            rcases List.mem_append.1 hx with hx | hx
            · exact hm x (by rw [← Array.mem_toList_iff, hL]; simp [hx])
            · simp at hx; exact hx ▸ hQ
          · rw [hL', hL]; simp [hV]; ring
        · refine ⟨fun x hx ↦ ?_, by simp⟩
          rcases Array.mem_push.1 hx with hx | hx
          · exact hm x hx
          · exact hx ▸ ha
    obtain ⟨h1, h2⟩ := ih _ hstep.1 hl'
    refine ⟨h1, ?_⟩
    rw [h2, hstep.2]; simp; ring

/-! ## Atom values -/

theorem c4_atomVal (T : Array (Array FE)) (a : Atom) :
    atomVal T a = a.w * (a.keys.toList.map (keyVal T)).prod := by
  unfold atomVal
  rw [← Array.foldl_toList]
  generalize a.w = w
  induction a.keys.toList generalizing w with
  | nil => simp
  | cons k ks ih => simp only [List.foldl_cons, List.map_cons, List.prod_cons]; rw [ih]; ring

theorem c4_kapV_or (P : Pt) (x y : ℕ) (h : x &&& y = 0) :
    ct_kapV P (x ||| y) = ct_kapV P x + ct_kapV P y := by
  unfold ct_kapV
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro o _
  have := congrArg (fun z ↦ z.testBit o) h
  simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff] at this
  rw [Nat.testBit_or]
  rcases this with h1 | h1 <;> simp [h1]

theorem c4_split (T : Array (Array FE)) (k : Array (ℕ × ℕ)) (hk : 1 < k.size) :
    (k.toList.map (keyVal T)).prod = keyVal T (k.getD 1 (0, 0)) * ((c4_wo k).toList.map (keyVal T)).prod := by
  rcases k with ⟨_ | ⟨x0, _ | ⟨x1, r⟩⟩⟩
  · simp at hk
  · simp at hk
  · simp [c4_wo, List.extract]
    ring

theorem c4_wo_set (k : Array (ℕ × ℕ)) (x : ℕ × ℕ) : c4_wo (k.set! 1 x) = c4_wo k := by
  rcases k with ⟨_ | ⟨x0, _ | ⟨x1, r⟩⟩⟩ <;> simp [c4_wo, List.extract, Array.set!_eq_setIfInBounds]

/-! ## The merges keep the shape and the sum -/

/-- The kept shape: depth `D`, the selector, the other keys of an input atom. -/
def c4_Q (as : Array Atom) (D : ℕ) (a : Atom) : Prop :=
  a.keys.size = D ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧ (a.keys.getD 1 (0, 0)).2 < 16 ∧
    ∃ b ∈ as, ∀ i, i ≠ 1 → a.keys.getD i (0, 0) = b.keys.getD i (0, 0)

theorem c4_one_lt (k : Array (ℕ × ℕ)) (h : (k.getD 1 (0, 0)).1 = 1) : 1 < k.size := by
  by_contra hc
  have : k.getD 1 (0, 0) = (0, 0) := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hc)]
  rw [this] at h
  exact absurd h (by decide)

theorem c4_step1 (T : Array (Array FE)) (as : Array Atom) (D : ℕ) (b a : Atom) (hb : c4_Q as D b)
    (_ : c4_Q as D a) (hc : c4_C1 b a = true) :
    c4_Q as D (c4_H1 b a b) ∧ atomVal T (c4_H1 b a b) = atomVal T b + atomVal T a := by
  refine ⟨hb, ?_⟩
  have hk : b.keys = a.keys := by simpa [c4_C1] using hc
  simp only [c4_atomVal, c4_H1, hk]
  ring

theorem c4_step3 (P : Pt) (T : Array (Array FE)) (hk : ∀ m < 16, keyVal T (1, m) = ct_kapV P m)
    (as : Array Atom) (D : ℕ) (b a : Atom) (hb : c4_Q as D b) (ha : c4_Q as D a) (hc : c4_C3 b a = true) :
    c4_Q as D (c4_H3 b a b) ∧ atomVal T (c4_H3 b a b) = atomVal T b + atomVal T a := by
  obtain ⟨hbD, hb1, hb16, c, hc0, hcb⟩ := hb
  obtain ⟨haD, ha1, ha16, -⟩ := ha
  have hc' := hc
  simp only [c4_C3, Bool.and_eq_true] at hc'
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc'
  rw [beq_iff_eq] at h1 h3
  rw [code_beq_iff] at h2
  have hbl := c4_one_lt _ hb1
  have hal := c4_one_lt _ ha1
  set mb := (b.keys.getD 1 (0, 0)).2
  set ma := (a.keys.getD 1 (0, 0)).2
  have hbk : b.keys.getD 1 (0, 0) = (1, mb) := Prod.ext hb1 rfl
  have hak : a.keys.getD 1 (0, 0) = (1, ma) := Prod.ext ha1 rfl
  have h16 : mb ||| ma < 16 := Nat.or_lt_two_pow (n := 4) hb16 ha16
  have hset : (b.keys.set! 1 (1, mb ||| ma)).getD 1 (0, 0) = (1, mb ||| ma) := by
    simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, hbl]
  have hsz : (b.keys.set! 1 (1, mb ||| ma)).size = b.keys.size := by simp [Array.set!_eq_setIfInBounds]
  refine ⟨⟨by simp only [c4_H3]; rw [hsz, hbD], by simp only [c4_H3]; rw [hset],
    by simp only [c4_H3]; rw [hset]; exact h16, c, hc0, fun i hi ↦ ?_⟩, ?_⟩
  · simp only [c4_H3]
    rw [← hcb i hi]
    simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Ne.symm hi]
  · simp only [c4_atomVal, c4_H3]
    rw [c4_split T _ (by rw [hsz]; exact hbl), c4_split T _ hbl, c4_split T _ hal, c4_wo_set, hset, hbk, hak,
      ← h1, ← h2, hk _ h16, hk _ hb16, hk _ ha16, c4_kapV_or P _ _ h3]
    ring

theorem c4_filter (T : Array (Array FE)) (l : List Atom) :
    ((l.filter fun a ↦ !a.w == 0).map (atomVal T)).sum = (l.map (atomVal T)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : (a.w == 0) = true
    · have : a.w = 0 := (code_beq_iff _ _).1 h
      simp only [List.filter_cons, h, Bool.not_true, Bool.false_eq_true, ite_false, List.map_cons,
        List.sum_cons, ih]
      rw [c4_atomVal, this, zero_mul, zero_add]
    · simp [h, ih]

theorem c4_pad_getD (k : Array (ℕ × ℕ)) (n i : ℕ) :
    (k ++ Array.replicate n (0, 0)).getD i (0, 0) = k.getD i (0, 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split_ifs with h
  · rfl
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt h), Array.getElem?_replicate]
    split_ifs <;> rfl

theorem c4_perm (Q : Atom → Prop) (V : Atom → FE) (xs ys : Array Atom) (h : xs.toList.Perm ys.toList)
    (hQ : ∀ x ∈ ys, Q x) : (∀ x ∈ xs, Q x) ∧ (xs.toList.map V).sum = (ys.toList.map V).sum :=
  ⟨fun x hx ↦ hQ x (Array.mem_toList_iff.1 (h.mem_iff.1 (Array.mem_toList_iff.2 hx))), (h.map V).sum_eq⟩

/-- **The final atoms** (C4): padding and merging keep the sum and the keys but the selector level; the result is
sorted. -/
theorem ct_mergeAtoms (P : Pt) (T : Array (Array FE)) (hT : keyVal T (0, 0) = 1)
    (hk : ∀ m < 16, keyVal T (1, m) = ct_kapV P m) (as : Array Atom) (D : ℕ)
    (hD : ∀ a ∈ as, a.keys.size ≤ D)
    (hsel : ∀ a ∈ as, 2 ≤ a.keys.size ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧ (a.keys.getD 1 (0, 0)).2 < 16) :
    (∀ a ∈ mergeAtoms 1 (padTo D as), a.keys.size = D ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧
        (a.keys.getD 1 (0, 0)).2 < 16 ∧ ∃ b ∈ as, ∀ i, i ≠ 1 → a.keys.getD i (0, 0) = b.keys.getD i (0, 0)) ∧
      ((mergeAtoms 1 (padTo D as)).toList.map (atomVal T)).sum = (as.toList.map (atomVal T)).sum ∧
      (mergeAtoms 1 (padTo D as)).toList.Pairwise fun a b ↦ keysLt b.keys a.keys = false := by
  -- padding
  have hQp : ∀ x ∈ padTo D as, c4_Q as D x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Array.mem_map.1 hx
    obtain ⟨-, h1, h16⟩ := hsel a ha
    refine ⟨by simp; have := hD a ha; omega, by rw [c4_pad_getD]; exact h1, by rw [c4_pad_getD]; exact h16,
      a, ha, fun i _ ↦ c4_pad_getD _ _ _⟩
  have hVp : ((padTo D as).toList.map (atomVal T)).sum = (as.toList.map (atomVal T)).sum := by
    unfold padTo
    rw [Array.toList_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    simp [c4_atomVal, Array.toList_append, List.prod_append, hT]
  rw [c4_mergeAtoms_eq]
  set lt1 : Atom → Atom → Bool := fun a b ↦ keysLtK 1 a.keys b.keys
  set lt : Atom → Atom → Bool := fun a b ↦ keysLt a.keys b.keys
  -- the first sort
  obtain ⟨hQ1, hV1⟩ := c4_perm (c4_Q as D) (atomVal T) _ _ (qs_qsort_perm (padTo D as) lt1) hQp
  -- the weight merge
  rw [← Array.foldl_toList]
  obtain ⟨hQ2, hV2⟩ := c4_fold (c4_Q as D) (atomVal T) c4_C1 c4_H1 (c4_step1 T as D)
    ((padTo D as).qsort lt1).toList #[] (by simp) (fun a ha ↦ hQ1 a (Array.mem_toList_iff.1 ha))
  -- the filter and the mask merge
  rw [← Array.foldl_toList]
  obtain ⟨hQ3, hV3⟩ := c4_fold (c4_Q as D) (atomVal T) c4_C3 c4_H3 (c4_step3 P T hk as D)
    (Array.filter (fun a ↦ !a.w == 0)
      (List.foldl (c4_mstep c4_C1 c4_H1) #[] ((padTo D as).qsort lt1).toList)).toList #[] (by simp)
    (fun a ha ↦ hQ2 a (Array.mem_of_mem_filter (Array.mem_toList_iff.1 ha)))
  -- the final sort
  obtain ⟨hQ4, hV4⟩ := c4_perm (c4_Q as D) (atomVal T) _ _ (qs_qsort_perm _ lt) hQ3
  refine ⟨hQ4, ?_, qs_qsort_sorted _ lt (fun a b c ↦ qs_keysLt_trans a.keys b.keys c.keys)
    (fun a b ↦ qs_keysLt_asymm a.keys b.keys)⟩
  rw [hV4, hV3, Array.toList_filter, c4_filter, hV2, hV1, hVp]
  simp

/-- The trivial keys of merged atoms (from `ct_mergeAtoms`). -/
theorem ct_mergeAtoms_h0 (as : Array Atom) (D : ℕ) (ha : ∀ a ∈ as, ct_AtomOk a)
    (h : ∀ a ∈ mergeAtoms 1 (padTo D as), a.keys.size = D ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧
        (a.keys.getD 1 (0, 0)).2 < 16 ∧ ∃ b ∈ as, ∀ i, i ≠ 1 → a.keys.getD i (0, 0) = b.keys.getD i (0, 0)) :
    ∀ a ∈ mergeAtoms 1 (padTo D as), ∀ k ∈ a.keys, k.1 = 0 → k.2 = 0 := by
  intro a ha' k hk hk0
  obtain ⟨-, h1, -, b, hb, hbk⟩ := h a ha'
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hk
  have hai : a.keys.getD i (0, 0) = a.keys[i] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  by_cases i1 : i = 1
  · subst i1
    rw [hai] at h1
    omega
  · rw [← hai, hbk i i1]
    by_cases hib : i < b.keys.size
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hib, Option.getD_some]
      have hmem : b.keys[i] ∈ b.keys := Array.getElem_mem hib
      rw [← hai, hbk i i1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hib, Option.getD_some] at hk0
      exact (ha b hb).2.2.2 _ hmem hk0
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl

theorem c0a_foldl_max (l : List Atom) : ∀ (d : ℕ),
    d ≤ l.foldl (fun d a ↦ max d a.keys.size) d ∧ ∀ a ∈ l, a.keys.size ≤ l.foldl (fun d a ↦ max d a.keys.size) d := by
  induction l with
  | nil => intro d; simp
  | cons b l ih =>
    intro d
    obtain ⟨h1, h2⟩ := ih (max d b.keys.size)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨le_trans (le_max_left _ _) h1, fun a ha ↦ ?_⟩
    rcases ha with rfl | ha
    · exact le_trans (le_max_right _ _) h1
    · exact h2 a ha

/-- A bound by the fold of `max`. -/
theorem ct_le_foldl_max (as : Array Atom) : ∀ a ∈ as, a.keys.size ≤ as.foldl (fun d a ↦ max d a.keys.size) 0 := by
  intro a ha
  rw [← Array.foldl_toList]
  exact (c0a_foldl_max as.toList 0).2 a (Array.mem_toList_iff.2 ha)

/-! ## The pieces (C1–C6) -/

/-- Whether iteration `jf` lies in the sub-cube fixing `fix`. -/
def ct_inFix (fix : List (ℕ × Bool)) (jf : ℕ) : Bool := fix.all fun bv ↦ jf.testBit bv.1 == bv.2

/-! ### Bits -/

theorem c1_testBit_add_two_pow (u k j : ℕ) (hk : u.testBit k = false) :
    (u + 2 ^ k).testBit j = (u.testBit j || decide (j = k)) := by
  have h1 : u = 2 ^ k * (u / 2 ^ k) + u % 2 ^ k := (Nat.div_add_mod u (2 ^ k)).symm
  have hr : u % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have h2 : (u / 2 ^ k) % 2 = 0 := by
    have := Nat.testBit_div_two_pow (n := k) u 0
    rw [Nat.zero_add, hk, Nat.testBit_zero] at this
    simpa using this
  have h3 : u + 2 ^ k = 2 ^ k * (u / 2 ^ k + 1) + u % 2 ^ k := by
    conv_lhs => rw [h1]
    ring
  rw [h3, Nat.testBit_two_pow_mul_add _ hr]
  conv_rhs => rw [h1, Nat.testBit_two_pow_mul_add _ hr]
  by_cases hj : j < k
  · simp [hj, show j ≠ k by omega]
  · simp only [hj, ite_false]
    obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
    rw [Nat.add_sub_cancel_left]
    cases d with
    | zero => simp [Nat.testBit_zero]; omega
    | succ d =>
      rw [Nat.testBit_add_one, Nat.testBit_add_one]
      have : (u / 2 ^ k + 1) / 2 = u / 2 ^ k / 2 := by omega
      simp [this]

theorem c1_isPow2 (c : ℕ) (h : isPow2 c = true) : c = 2 ^ log2 c := by
  simp only [isPow2, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨k, hk⟩ := Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mp h
  subst hk
  simp [log2, Nat.log2_two_pow]

theorem c1_pow2_bit (c : ℕ) (h : isPow2 c = true) : c.testBit (log2 c) = true := by
  have : ∀ k, c = 2 ^ k → c.testBit k = true := fun k hk ↦ by rw [hk]; exact Nat.testBit_two_pow_self
  exact this _ (c1_isPow2 c h)

theorem c1_testBit_mod4 (v e : ℕ) (h : (v >>> e) % 4 = 0) :
    v.testBit e = false ∧ v.testBit (e + 1) = false := by
  have h0 := Nat.testBit_shiftRight (i := e) v (j := 0)
  have h1 := Nat.testBit_shiftRight (i := e) v (j := 1)
  rw [Nat.add_zero] at h0
  rw [← h0, ← h1, Nat.testBit_add_one, Nat.testBit_zero, Nat.testBit_zero]
  generalize v >>> e = n at *
  constructor <;> simp only [decide_eq_false_iff_not] <;> omega

theorem c1_limb_bits (v0 e m : ℕ) (h : (v0 >>> e) % 4 = 0) (hm : m < 4) (j : ℕ) :
    (v0 + m * 2 ^ e).testBit j =
      if j = e then m.testBit 0 else if j = e + 1 then m.testBit 1 else v0.testBit j := by
  have hn : v0 >>> e = v0 / 2 ^ e := Nat.shiftRight_eq_div_pow v0 e
  rw [hn] at h
  have hr : v0 % 2 ^ e < 2 ^ e := Nat.mod_lt _ (Nat.two_pow_pos e)
  have h1 : v0 = 2 ^ e * (2 ^ 2 * (v0 / 2 ^ e / 4) + 0) + v0 % 2 ^ e := by
    have := Nat.div_add_mod v0 (2 ^ e)
    have h4 : v0 / 2 ^ e = 4 * (v0 / 2 ^ e / 4) := by omega
    rw [h4] at this
    simp only [Nat.add_zero]
    norm_num
    omega
  have h3 : v0 + m * 2 ^ e = 2 ^ e * (2 ^ 2 * (v0 / 2 ^ e / 4) + m) + v0 % 2 ^ e := by
    conv_lhs => rw [h1]
    ring
  rw [h3, Nat.testBit_two_pow_mul_add _ hr]
  conv_rhs => rw [h1, Nat.testBit_two_pow_mul_add _ hr]
  rw [Nat.testBit_two_pow_mul_add _ (by norm_num : (0:ℕ) < 2 ^ 2),
    Nat.testBit_two_pow_mul_add _ (by norm_num; omega : m < 2 ^ 2)]
  by_cases hj : j < e
  · simp [hj, show j ≠ e by omega, show j ≠ e + 1 by omega]
  · obtain ⟨d, rfl⟩ : ∃ d, j = e + d := ⟨j - e, by omega⟩
    simp only [hj, ite_false, Nat.add_sub_cancel_left]
    rcases d with _ | _ | d
    · simp
    · simp
    · simp only [show e + (d + 2) ≠ e by omega, show e + (d + 2) ≠ e + 1 by omega, ite_false,
        show ¬ (d + 2 < 2) by omega, Nat.zero_testBit]

/-- A number with prescribed bits below `n`. -/
def c1_ofBits (h : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ n * (if h n then 1 else 0) + c1_ofBits h n

theorem c1_ofBits_spec (h : ℕ → Bool) (n : ℕ) :
    c1_ofBits h n < 2 ^ n ∧ ∀ i, (c1_ofBits h n).testBit i = (decide (i < n) && h i) := by
  induction n with
  | zero => simp [c1_ofBits]
  | succ n ih =>
    obtain ⟨hlt, hb⟩ := ih
    refine ⟨?_, fun i ↦ ?_⟩
    · simp only [c1_ofBits, pow_succ]
      split <;> omega
    · simp only [c1_ofBits]
      rw [Nat.testBit_two_pow_mul_add _ hlt, hb]
      by_cases hi : i < n
      · simp [hi, show i < n + 1 by omega]
      · simp only [hi, ite_false]
        obtain ⟨d, rfl⟩ : ∃ d, i = n + d := ⟨i - n, by omega⟩
        rw [Nat.add_sub_cancel_left]
        rcases d with _ | d
        · split <;> simp_all
        · have : ¬ (n + (d + 1) < n + 1) := by omega
          simp only [this, decide_false, Bool.false_and]
          split <;> simp [Nat.testBit_add_one]

theorem c1_injOk_cons (U c : ℕ) (cs : List ℕ) :
    injOk U (c :: cs) = if c = 0 then injOk U cs else (isPow2 c && U &&& c == 0) && injOk (U ||| c) cs := by
  have hnone : ∀ (f : Option ℕ → ℕ → Option ℕ), (∀ c, f none c = none) → ∀ cs : List ℕ,
      cs.foldl f none = none := by
    intro f hf cs
    induction cs with
    | nil => rfl
    | cons c cs ih => rw [List.foldl_cons, hf, ih]
  unfold injOk
  simp only [List.foldl_cons, Option.bind_some]
  by_cases h0 : c = 0
  · simp [h0]
  · simp only [h0, ite_false, beq_iff_eq]
    by_cases h1 : (isPow2 c && U &&& c == 0) = true
    · rw [if_pos h1, h1, Bool.true_and]
    · rw [if_neg h1, hnone _ (fun _ ↦ rfl)]
      simp only [Bool.not_eq_true] at h1
      simp [h1]

theorem c1_injOk_mem : ∀ (cs : List ℕ) (U : ℕ), injOk U cs = true → ∀ c ∈ cs, c ≠ 0 →
    isPow2 c = true ∧ U &&& c = 0 := by
  intro cs
  induction cs with
  | nil => simp
  | cons c0 cs ih =>
    intro U hU c hc hc0
    rw [c1_injOk_cons] at hU
    have hsub : ∀ V, V &&& c = 0 → isPow2 c = true → U &&& V = U → isPow2 c = true ∧ U &&& c = 0 := by
      intro V hV hp hUV
      refine ⟨hp, ?_⟩
      apply Nat.eq_of_testBit_eq
      intro j
      have h1 := congrArg (fun x ↦ x.testBit j) hV
      have h2 := congrArg (fun x ↦ x.testBit j) hUV
      simp only [Nat.testBit_and, Nat.zero_testBit] at h1 h2 ⊢
      cases hu : U.testBit j <;> cases hv : V.testBit j <;> simp_all
    by_cases h0 : c0 = 0
    · rw [if_pos h0] at hU
      rcases List.mem_cons.mp hc with rfl | hc
      · exact absurd h0 hc0
      · exact ih U hU c hc hc0
    · rw [if_neg h0] at hU
      simp only [Bool.and_eq_true, beq_iff_eq] at hU
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hU.1.1, hU.1.2⟩
      · obtain ⟨hp, hV⟩ := ih _ hU.2 c hc hc0
        refine hsub _ hV hp ?_
        apply Nat.eq_of_testBit_eq
        intro j
        simp only [Nat.testBit_and, Nat.testBit_or]
        cases U.testBit j <;> simp

/-- The word on the free bits: `Σ_{(i,c) ∈ F} bit_i(jf)·c`. -/
def c1_S (F : List (ℕ × ℕ)) (jf : ℕ) : ℕ := (F.map fun p ↦ if jf.testBit p.1 then p.2 else 0).sum

theorem c1_step (U u c : ℕ) (b : Bool) (hp : isPow2 c = true) (hU : U &&& c = 0)
    (huU : ∀ k, u.testBit k = true → U.testBit k = true) :
    (∀ k, (u + if b then c else 0).testBit k = true → (U ||| c).testBit k = true) ∧
      ∀ j, (u + if b then c else 0).testBit j = (u.testBit j || (b && decide (j = log2 c))) := by
  have hc := c1_isPow2 c hp
  have hUk : U.testBit (log2 c) = false := by
    have := congrArg (fun x ↦ x.testBit (log2 c)) hU
    simp only [Nat.testBit_and, Nat.zero_testBit] at this
    rw [c1_pow2_bit c hp, Bool.and_true] at this
    exact this
  have huk : u.testBit (log2 c) = false := by
    cases h : u.testBit (log2 c)
    · rfl
    · rw [huU _ h] at hUk; exact hUk
  have hbit : ∀ j, (u + if b then c else 0).testBit j = (u.testBit j || (b && decide (j = log2 c))) := by
    intro j
    cases b
    · simp
    · simp only [if_true, Bool.true_and]
      rw [hc, c1_testBit_add_two_pow _ _ _ huk, ← hc]
  refine ⟨fun k hk ↦ ?_, hbit⟩
  rw [hbit] at hk
  rw [Nat.testBit_or]
  rcases Bool.or_eq_true_iff.mp hk with h | h
  · rw [huU k h]; rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.2, c1_pow2_bit c hp, Bool.or_true]

theorem c1_bit_miss (jf : ℕ) : ∀ (F : List (ℕ × ℕ)) (u U : ℕ), injOk U (F.map (·.2)) = true →
    (∀ k, u.testBit k = true → U.testBit k = true) → ∀ j, (∀ p ∈ F, p.2 ≠ 2 ^ j) →
    (u + c1_S F jf).testBit j = u.testBit j := by
  intro F
  induction F with
  | nil => simp [c1_S]
  | cons p F ih =>
    intro u U hU huU j hj
    simp only [List.map_cons] at hU
    rw [c1_injOk_cons] at hU
    have hS : u + c1_S (p :: F) jf = (u + if jf.testBit p.1 then p.2 else 0) + c1_S F jf := by
      simp [c1_S, List.map_cons, List.sum_cons, Nat.add_assoc]
    rw [hS]
    by_cases h0 : p.2 = 0
    · rw [if_pos h0] at hU
      simp only [h0, ite_self, Nat.add_zero]
      exact ih u U hU huU j (fun q hq ↦ hj q (List.mem_cons_of_mem _ hq))
    · rw [if_neg h0] at hU
      simp only [Bool.and_eq_true, beq_iff_eq] at hU
      obtain ⟨h1, h2⟩ := c1_step U u p.2 (jf.testBit p.1) hU.1.1 hU.1.2 huU
      rw [ih _ _ hU.2 h1 j (fun q hq ↦ hj q (List.mem_cons_of_mem _ hq)), h2]
      have : j ≠ log2 p.2 := by
        intro hjl
        apply hj p (List.mem_cons_self ..)
        rw [hjl]; exact c1_isPow2 _ hU.1.1
      simp [this]

theorem c1_bit_hit (jf : ℕ) : ∀ (F : List (ℕ × ℕ)) (u U : ℕ), injOk U (F.map (·.2)) = true →
    (∀ k, u.testBit k = true → U.testBit k = true) → ∀ p ∈ F, p.2 ≠ 0 →
    (u + c1_S F jf).testBit (log2 p.2) = jf.testBit p.1 := by
  intro F
  induction F with
  | nil => simp
  | cons p0 F ih =>
    intro u U hU huU p hp hp0
    simp only [List.map_cons] at hU
    rw [c1_injOk_cons] at hU
    have hS : u + c1_S (p0 :: F) jf = (u + if jf.testBit p0.1 then p0.2 else 0) + c1_S F jf := by
      simp [c1_S, List.map_cons, List.sum_cons, Nat.add_assoc]
    rw [hS]
    by_cases h0 : p0.2 = 0
    · rw [if_pos h0] at hU
      simp only [h0, ite_self, Nat.add_zero]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact absurd h0 hp0
      · exact ih u U hU huU p hp hp0
    · rw [if_neg h0] at hU
      simp only [Bool.and_eq_true, beq_iff_eq] at hU
      obtain ⟨h1, h2⟩ := c1_step U u p0.2 (jf.testBit p0.1) hU.1.1 hU.1.2 huU
      rcases List.mem_cons.mp hp with rfl | hp
      · rw [c1_bit_miss jf F _ _ hU.2 h1, h2]
        · have : u.testBit (log2 p.2) = false := by
            have hc := c1_isPow2 _ hU.1.1
            have := congrArg (fun x ↦ x.testBit (log2 p.2)) hU.1.2
            simp only [Nat.testBit_and, Nat.zero_testBit] at this
            rw [c1_pow2_bit _ hU.1.1, Bool.and_true] at this
            cases h : u.testBit (log2 p.2)
            · rfl
            · rw [huU _ h] at this; exact this
          simp [this]
        · intro q hq hqe
          have hq0 : q.2 ≠ 0 := by rw [hqe]; exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
          obtain ⟨-, hV⟩ := c1_injOk_mem _ _ hU.2 q.2 (List.mem_map_of_mem hq) hq0
          have := congrArg (fun x ↦ x.testBit (log2 p.2)) hV
          simp only [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_or] at this
          rw [hqe, Nat.testBit_two_pow_self, c1_pow2_bit _ hU.1.1] at this
          simp at this
      · exact ih _ _ hU.2 h1 p hp hp0

/-! ### Lists -/

theorem c1_kerVal_eq (P : Pt) (fs : List KF) : kerVal P fs = (fs.map (kfVal P)).prod := by
  have : ∀ (c : FE) (fs : List KF), fs.foldl (fun acc f ↦ acc * kfVal P f) c = c * (fs.map (kfVal P)).prod := by
    intro c fs
    induction fs generalizing c with
    | nil => simp
    | cons f fs ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]
  rw [kerVal, this, one_mul]

@[to_additive]

theorem c1_prod_range_ite {M : Type} [CommMonoid M] (k : ℕ) (x : M) :
    ∀ l, ((List.range l).map fun i ↦ if (k == i) = true then x else 1).prod = if k < l then x else 1 := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    by_cases h : k < l
    · simp [h, show k < l + 1 by omega, show k ≠ l by omega]
    · by_cases h' : k = l
      · simp [h']
      · simp [h, h', show ¬ k < l + 1 by omega]

@[to_additive c1_regroup_sum]

theorem c1_regroup {β M : Type} [CommMonoid M] (l : ℕ) (φ : ℕ × β → M) :
    ∀ (L : List (ℕ × β)), (∀ p ∈ L, p.1 < l) →
      ((List.range l).map fun i ↦ ((L.filter fun p ↦ p.1 == i).map φ).prod).prod = (L.map φ).prod := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih =>
    intro h
    have h1 : ∀ i, (((a :: L).filter fun p ↦ p.1 == i).map φ).prod =
        (if (a.1 == i) = true then φ a else 1) * ((L.filter fun p ↦ p.1 == i).map φ).prod := by
      intro i
      rw [List.filter_cons]
      split <;> simp
    simp only [h1]
    rw [List.prod_map_mul, c1_prod_range_ite, ih (fun p hp ↦ h p (List.mem_cons_of_mem _ hp)),
      if_pos (h a (List.mem_cons_self ..)), List.map_cons, List.prod_cons]

theorem c1_filter_single {β : Type} (L : List (ℕ × β)) (hn : (L.map (·.1)).Nodup) (p : ℕ × β) (hp : p ∈ L) :
    (L.filter fun q ↦ q.1 == p.1) = [p] := by
  induction L with
  | nil => simp at hp
  | cons a L ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rw [List.filter_cons]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [beq_self_eq_true, if_true, List.cons.injEq, true_and]
      rw [List.filter_eq_nil_iff]
      intro q hq
      simp only [beq_iff_eq]
      intro he
      exact hn.1 ⟨q, hq, he⟩
    · have hne : (a.1 == p.1) = false := by
        simp only [beq_eq_false_iff_ne]
        intro he
        exact hn.1 ⟨p, hp, he.symm⟩
      rw [hne]
      exact ih hn.2 hp

theorem c1_filter_nil {β : Type} (L : List (ℕ × β)) (i : ℕ) (h : ∀ q ∈ L, q.1 ≠ i) :
    (L.filter fun q ↦ q.1 == i) = [] := by
  rw [List.filter_eq_nil_iff]
  intro q hq
  simpa using h q hq

theorem c1_inFix_prod (jf : ℕ) (fix : List (ℕ × Bool)) :
    (if ct_inFix fix jf = true then (1 : FE) else 0) =
      (fix.map fun p ↦ if jf.testBit p.1 = p.2 then (1 : FE) else 0).prod := by
  induction fix with
  | nil => simp [ct_inFix]
  | cons a fix ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    simp only [ct_inFix, List.all_cons, Bool.and_eq_true, beq_iff_eq]
    by_cases h1 : jf.testBit a.1 = a.2 <;> by_cases h2 : (fix.all fun bv ↦ jf.testBit bv.1 == bv.2) = true <;>
      simp [h1, h2]

theorem c1_inFix_iff (jf : ℕ) (fix : List (ℕ × Bool)) :
    ct_inFix fix jf = true ↔ ∀ q ∈ fix, jf.testBit q.1 = q.2 := by
  simp [ct_inFix]

/-! ### The kernel: the sum over the sub-cube of the per-bit factors -/

theorem c1_core (P : Pt) (l : ℕ) (fix : List (ℕ × Bool)) (prs : List (ℕ × ℕ))
    (hfk : ∀ p ∈ fix, p.1 < l) (hpk : ∀ p ∈ prs, p.1 < l) (hfn : (fix.map (·.1)).Nodup)
    (hpn : (prs.map (·.1)).Nodup) (hdis : ∀ p ∈ fix, ∀ q ∈ prs, p.1 ≠ q.1) :
    ((List.range (2 ^ l)).map fun jf ↦ (if ct_inFix fix jf = true then (1 : FE) else 0) *
        ct_eqOn P.rx (List.range l) jf * (prs.map fun p ↦ eq1 (P.ry.getD p.2 0) (jf.testBit p.1)).prod).sum =
      kerVal P (fix.map (fun p ↦ KF.fixX p.1 p.2) ++ prs.map fun p ↦ KF.pair p.1 p.2) := by
  set f : ℕ → Bool → FE := fun i b ↦
    ((fix.filter fun p ↦ p.1 == i).map fun p ↦ if b = p.2 then (1 : FE) else 0).prod *
      eq1 (P.rx.getD i 0) b * ((prs.filter fun p ↦ p.1 == i).map fun p ↦ eq1 (P.ry.getD p.2 0) b).prod with hf
  have hstep1 : ∀ jf, (if ct_inFix fix jf = true then (1 : FE) else 0) *
        ct_eqOn P.rx (List.range l) jf * (prs.map fun p ↦ eq1 (P.ry.getD p.2 0) (jf.testBit p.1)).prod =
      ((List.range l).map fun i ↦ f i (jf.testBit i)).prod := by
    intro jf
    have hA : ∀ i, ((fix.filter fun p ↦ p.1 == i).map fun p ↦ if jf.testBit p.1 = p.2 then (1 : FE) else 0) =
        ((fix.filter fun p ↦ p.1 == i).map fun p ↦ if jf.testBit i = p.2 then (1 : FE) else 0) := by
      intro i
      apply List.map_congr_left
      intro p hp
      simp only [List.mem_filter, beq_iff_eq] at hp
      rw [hp.2]
    have hC : ∀ i, ((prs.filter fun p ↦ p.1 == i).map fun p ↦ eq1 (P.ry.getD p.2 0) (jf.testBit p.1)) =
        ((prs.filter fun p ↦ p.1 == i).map fun p ↦ eq1 (P.ry.getD p.2 0) (jf.testBit i)) := by
      intro i
      apply List.map_congr_left
      intro p hp
      simp only [List.mem_filter, beq_iff_eq] at hp
      rw [hp.2]
    rw [c1_inFix_prod, ← c1_regroup l (fun p ↦ if jf.testBit p.1 = p.2 then (1 : FE) else 0) fix hfk,
      ← c1_regroup l (fun p ↦ eq1 (P.ry.getD p.2 0) (jf.testBit p.1)) prs hpk]
    simp only [hf, List.prod_map_mul, hA, hC, ct_eqOn]
  rw [List.map_congr_left (fun jf _ ↦ hstep1 jf), ct_sum_prod_bits]
  have h2 : (2 : FE) = 0 := CharTwo.two_eq_zero
  have hF : ∀ i, f i false + f i true =
      ((fix.filter fun p ↦ p.1 == i).map fun p ↦ kfVal P (KF.fixX p.1 p.2)).prod *
        ((prs.filter fun p ↦ p.1 == i).map fun p ↦ kfVal P (KF.pair p.1 p.2)).prod := by
    intro i
    by_cases hA : ∃ p ∈ fix, p.1 = i
    · obtain ⟨p, hp, rfl⟩ := hA
      rw [hf]
      simp only
      rw [c1_filter_single fix hfn p hp, c1_filter_nil prs p.1 (fun q hq he ↦ hdis p hp q hq he.symm)]
      obtain ⟨i, b⟩ := p
      cases b <;> simp [kfVal, eq1]
    · by_cases hB : ∃ q ∈ prs, q.1 = i
      · obtain ⟨q, hq, rfl⟩ := hB
        rw [hf]
        simp only
        rw [c1_filter_single prs hpn q hq, c1_filter_nil fix q.1 (fun p hp he ↦ hdis p hp q hq he)]
        simp only [List.map_nil, List.prod_nil, List.map_cons, List.prod_cons, mul_one, one_mul, eq1, kfVal,
          Bool.false_eq_true, if_false, if_true]
        linear_combination (P.rx.getD q.1 0 * P.ry.getD q.2 0) * h2
      · simp only [not_exists, not_and] at hA hB
        rw [hf]
        simp only
        rw [c1_filter_nil fix i hA, c1_filter_nil prs i hB]
        simp [eq1]
  simp only [hF, List.prod_map_mul]
  rw [c1_regroup l _ fix hfk, c1_regroup l _ prs hpk, c1_kerVal_eq, List.map_append, List.prod_append,
    List.map_map, List.map_map]
  rfl

/-! ### The sub-cube -/

theorem c1_mk (l : ℕ) (fix : List (ℕ × Bool)) (hfk : ∀ p ∈ fix, p.1 < l) (hfn : (fix.map (·.1)).Nodup)
    (g : ℕ → Bool) :
    ∃ jf < 2 ^ l, ct_inFix fix jf = true ∧ ∀ i < l, (∀ q ∈ fix, q.1 ≠ i) → jf.testBit i = g i := by
  let h : ℕ → Bool := fun i ↦
    if fix.any (fun q ↦ q.1 == i && q.2) then true else if fix.any (fun q ↦ q.1 == i) then false else g i
  obtain ⟨hlt, hb⟩ := c1_ofBits_spec h l
  refine ⟨c1_ofBits h l, hlt, ?_, ?_⟩
  · rw [c1_inFix_iff]
    intro q hq
    rw [hb, decide_eq_true (hfk q hq), Bool.true_and]
    obtain ⟨i, b⟩ := q
    cases b
    · have h1 : (fix.any fun q ↦ q.1 == i && q.2) = false := by
        rw [List.any_eq_false]
        intro q' hq'
        simp only [Bool.and_eq_true, beq_iff_eq, not_and, Bool.not_eq_true]
        intro he
        have := List.inj_on_of_nodup_map hfn hq' hq he
        rw [this]
      have h2 : (fix.any fun q ↦ q.1 == i) = true := List.any_eq_true.mpr ⟨_, hq, by simp⟩
      simp only [h, h1, h2]
      rfl
    · have h1 : (fix.any fun q ↦ q.1 == i && q.2) = true := List.any_eq_true.mpr ⟨_, hq, by simp⟩
      simp only [h, h1, if_true]
  · intro i hi hn
    rw [hb, decide_eq_true hi, Bool.true_and]
    have h1 : (fix.any fun q ↦ q.1 == i && q.2) = false := by
      rw [List.any_eq_false]; intro q hq; simp [hn q hq]
    have h2 : (fix.any fun q ↦ q.1 == i) = false := by
      rw [List.any_eq_false]; intro q hq; simp [hn q hq]
    simp only [h, h1, h2, Bool.false_eq_true, ite_false]

theorem c1_sum_range_ext (h : ℕ → ℕ) (n : ℕ) (hz : ∀ i, n ≤ i → h i = 0) :
    ∀ d, ((List.range (n + d)).map h).sum = ((List.range n).map h).sum := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append, ih]
    simp [hz (n + d) (by omega)]

theorem c1_sum_filter_eq {α : Type} (L : List α) (p : α → Bool) (h : α → ℕ) :
    ((L.filter p).map h).sum = (L.map fun i ↦ if p i = true then h i else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filter_cons]
    split <;> simp_all

theorem c1_sum_filter_split {α : Type} (L : List α) (p : α → Bool) (h : α → ℕ) :
    (L.map h).sum = ((L.filter p).map h).sum + ((L.filter fun x ↦ !p x).map h).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filter_cons, List.filter_cons]
    cases hp : p a <;> simp [ih] <;> omega

theorem c1_at (l : ℕ) (a : Aff) (fix : List (ℕ × Bool)) (hfk : ∀ p ∈ fix, p.1 < l)
    (hfn : (fix.map (·.1)).Nodup) (jf : ℕ) (hjf : jf < 2 ^ l) (hin : ct_inFix fix jf = true) :
    a.at jf = (subAff l a fix).y0 + c1_S (subAff l a fix).free jf := by
  rw [c1_inFix_iff] at hin
  set h : ℕ → ℕ := fun i ↦ if jf.testBit i then a.coef.getD i 0 else 0 with hh
  have hat : a.at jf = a.y0 + ((List.range a.coef.length).map h).sum := rfl
  have hz1 : ∀ i, a.coef.length ≤ i → h i = 0 := by
    intro i hi
    show (if _ then a.coef.getD i 0 else 0) = 0
    rw [List.getD_eq_default _ _ hi, ite_self]
  have hz2 : ∀ i, l ≤ i → h i = 0 := by
    intro i hi
    have : jf.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hjf (Nat.pow_le_pow_right (by norm_num) hi))
    simp [hh, this]
  have hrange : ((List.range a.coef.length).map h).sum = ((List.range l).map h).sum := by
    rw [← c1_sum_range_ext h _ hz1 l, Nat.add_comm, c1_sum_range_ext h _ hz2]
  let isFix : ℕ → Bool := fun i ↦ fix.any (·.1 == i)
  rw [hat, hrange, c1_sum_filter_split _ isFix h]
  simp only [subAff, c1_S, List.map_map]
  rw [Nat.add_assoc]
  congr 2
  rw [c1_sum_filter_eq, ← c1_regroup_sum l _ fix hfk]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hA : ∃ q ∈ fix, q.1 = i
  · obtain ⟨q, hq, rfl⟩ := hA
    rw [c1_filter_single fix hfn q hq]
    have h1 : isFix q.1 = true := List.any_eq_true.mpr ⟨q, hq, by simp⟩
    simp only [h1, if_true, hh, hin q hq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
  · simp only [not_exists, not_and] at hA
    rw [c1_filter_nil fix i hA]
    have h1 : isFix i = false := by
      rw [List.any_eq_false]; intro q hq; simpa using hA q hq
    simp [h1]

/-! ### The `x` and `y` factors -/

theorem c1_eqOn_x (r : Array FE) (x0 l jf : ℕ) (hx : x0 % 2 ^ l = 0) (hl : l ≤ xVars) (hjf : jf < 2 ^ l) :
    ct_eqOn r (List.range xVars) (x0 + jf) = ct_eqOn r (List.range l) jf * ct_eqOn r (ct_xFree l) x0 := by
  have hperm : (List.range xVars).Perm (List.range l ++ ct_xFree l) := by
    have h1 := List.filter_append_perm (fun b ↦ decide (b < l)) (List.range xVars)
    have h2 : ((List.range xVars).filter fun b ↦ decide (b < l)).Perm (List.range l) := by
      rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) List.nodup_range]
      intro b
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      omega
    exact (h1.symm.trans (h2.append_right _))
  rw [ct_eqOn_perm r hperm, ct_eqOn_append]
  have hk : x0 = 2 ^ l * (x0 / 2 ^ l) + 0 := by
    have := Nat.div_add_mod x0 (2 ^ l); omega
  have hk' : x0 + jf = 2 ^ l * (x0 / 2 ^ l) + jf := by omega
  congr 1
  · apply ct_eqOn_congr
    intro b hb
    rw [List.mem_range] at hb
    rw [hk', Nat.testBit_two_pow_mul_add _ hjf]
    simp [hb]
  · apply ct_eqOn_congr
    intro b hb
    simp only [ct_xFree, List.mem_filter, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not] at hb
    rw [hk', Nat.testBit_two_pow_mul_add _ hjf]
    conv_rhs => rw [hk, Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos l)]
    simp [hb.2]

theorem c1_eqOn_y (r : Array FE) (M : List ℕ) (hM : M.Nodup) (hMr : ∀ j ∈ M, j < yVars) (v y0 : ℕ)
    (hv : ∀ j < yVars, j ∉ M → v.testBit j = y0.testBit j) :
    ct_eqOn r (List.range yVars) v = ct_eqOn r M v * ct_eqOn r (ct_yFree M) y0 := by
  have hperm : (List.range yVars).Perm (M ++ ct_yFree M) := by
    have h1 := List.filter_append_perm (fun b ↦ M.contains b) (List.range yVars)
    have h2 : ((List.range yVars).filter fun b ↦ M.contains b).Perm M := by
      rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hM]
      intro b
      simp only [List.mem_filter, List.mem_range, List.contains_iff_mem]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hMr b h, h⟩
    exact (h1.symm.trans (h2.append_right _))
  rw [ct_eqOn_perm r hperm, ct_eqOn_append]
  congr 1
  apply ct_eqOn_congr
  intro b hb
  simp only [ct_yFree, List.mem_filter, List.mem_range, Bool.not_eq_true'] at hb
  refine hv b hb.1 (fun hm ↦ ?_)
  have := List.contains_iff_mem.mpr hm
  rw [hb.2] at this
  exact Bool.false_ne_true this

/-- `addSub`'s injective case (C1). -/
theorem ct_addSub_inj (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s)
    (o : ℕ) (w : FE) (x0 l : ℕ) (a : Aff) (fix : List (ℕ × Bool)) (lim : Option ℕ)
    (ho : o < 4) (hx : x0 % 2 ^ l = 0) (hxl : x0 + 2 ^ l ≤ 2 ^ xVars)
    (hfix : (∀ bv ∈ fix, bv.1 < l) ∧ (fix.map (·.1)).Nodup)
    (hlim : match lim with
      | none => True
      | some e => e + 1 < yVars ∧ ∀ jf < 2 ^ l, ct_inFix fix jf = true → (a.at jf >>> e) % 4 = 0)
    (hinj : injOk (subAff l a fix).y0 ((subAff l a fix).free.map (·.2)) = true) :
    ct_Adds pt s (s.addSub o w x0 (subAff l a fix) lim)
      ((List.range (2 ^ l)).map fun jf ↦
        if ct_inFix fix jf then w * ct_EL pt lim o (x0 + jf) (a.at jf) else 0).sum := by
  obtain ⟨hfk, hfn⟩ := hfix
  have hxs : x0 >>> l <<< l = x0 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hx)
  set F := (subAff l a fix).free with hF
  set y0 := (subAff l a fix).y0 with hy0
  set pairs := F.filter fun (_, c) ↦ c != 0 && log2 c < yVars with hpairs
  set ym := pairs.map fun (_, c) ↦ log2 c with hym
  set fs := fix.map (fun (i, b) ↦ KF.fixX i b) ++ pairs.map fun (i, c) ↦ KF.pair i (log2 c) with hfs
  have hstep : s.addSub o w x0 (subAff l a fix) lim = s.addAtom fs o l x0 ym y0 w lim := by
    simp only [CS.addSub, ← hF, ← hy0, hinj, if_true]
    have h1 : (subAff l a fix).l = l := rfl
    have h2 : (subAff l a fix).fix = fix := rfl
    rw [h1, h2, hxs]
  rw [hstep]
  refine ct_Adds_congr (ct_addAtom pt s hs fs o l x0 ym y0 w lim ho) ?_
  set P := Pt.ofList pt with hP
  have hl : l ≤ xVars := by
    have h2 : 2 ^ l ≤ 2 ^ xVars := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  -- the free bits
  have hFkeys : F.map (·.1) = (List.range l).filter (fun i ↦ !fix.any (·.1 == i)) := by
    simp [hF, subAff, List.map_map, Function.comp_def]
  have hF1 : (F.map (·.1)).Nodup := by rw [hFkeys]; exact List.nodup_range.filter _
  have hFmem : ∀ p ∈ F, p.1 < l ∧ ∀ r ∈ fix, r.1 ≠ p.1 := by
    intro p hp
    have h1 : p.1 ∈ F.map (·.1) := List.mem_map_of_mem hp
    rw [hFkeys] at h1
    simp only [List.mem_filter, List.mem_range, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at h1
    exact ⟨h1.1, fun r hr he ↦ h1.2 r hr he⟩
  have hPmem : ∀ p ∈ pairs, p ∈ F ∧ p.2 ≠ 0 ∧ log2 p.2 < yVars := by
    intro p hp
    rw [hpairs, List.mem_filter] at hp
    obtain ⟨i, c⟩ := p
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  have hP2 : (pairs.map (·.1)).Nodup := hF1.sublist (List.Sublist.map _ List.filter_sublist)
  have hhit : ∀ jf, ∀ p ∈ pairs, (y0 + c1_S F jf).testBit (log2 p.2) = jf.testBit p.1 :=
    fun jf p hp ↦ c1_bit_hit jf F y0 y0 hinj (fun _ h ↦ h) p (hPmem p hp).1 (hPmem p hp).2.1
  have hmiss : ∀ jf, ∀ j < yVars, j ∉ ym → (y0 + c1_S F jf).testBit j = y0.testBit j := by
    intro jf j hj hjm
    apply c1_bit_miss jf F y0 y0 hinj (fun _ h ↦ h) j
    intro p hp hpe
    apply hjm
    have hp0 : p.2 ≠ 0 := by rw [hpe]; positivity
    have hlog : log2 p.2 = j := by rw [hpe]; exact Nat.log2_two_pow
    have hpp : p ∈ pairs := by
      rw [hpairs, List.mem_filter]
      refine ⟨hp, ?_⟩
      obtain ⟨i, c⟩ := p
      simp only at hp0 hlog ⊢
      simp [hp0, hlog, hj]
    rw [hym, List.mem_map]
    exact ⟨p, hpp, by obtain ⟨i, c⟩ := p; simpa using hlog⟩
  have hymn : ym.Nodup := by
    rw [hym]
    refine List.Nodup.map_on ?_ (List.Nodup.of_map _ hP2)
    intro p hp p' hp' he
    by_contra hne
    have hk : p.1 ≠ p'.1 := fun hk ↦ hne (List.inj_on_of_nodup_map hP2 hp hp' hk)
    have e1 := hhit (2 ^ p.1) p hp
    have e2 := hhit (2 ^ p.1) p' hp'
    obtain ⟨i, c⟩ := p
    obtain ⟨i', c'⟩ := p'
    simp only at he hk e1 e2
    rw [he, e2] at e1
    simp [Nat.testBit_two_pow] at e1
    exact hk e1
  have hymr : ∀ j ∈ ym, j < yVars := by
    intro j hj
    rw [hym, List.mem_map] at hj
    obtain ⟨p, hp, rfl⟩ := hj
    obtain ⟨i, c⟩ := p
    exact (hPmem _ hp).2.2
  have hat : ∀ jf < 2 ^ l, ct_inFix fix jf = true → a.at jf = y0 + c1_S F jf :=
    fun jf hjf hin ↦ c1_at l a fix hfk hfn jf hjf hin
  have hYp : ∀ v jf : ℕ, (∀ p ∈ pairs, v.testBit (log2 p.2) = jf.testBit p.1) →
      ct_eqOn P.ry ym v = (pairs.map fun p ↦ eq1 (P.ry.getD (log2 p.2) 0) (jf.testBit p.1)).prod := by
    intro v jf hv
    simp only [ct_eqOn, hym, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    obtain ⟨i, c⟩ := p
    simp only [Function.comp_apply]
    rw [hv _ hp]
  -- the kernel
  set prs := pairs.map fun p ↦ (p.1, log2 p.2) with hprs
  have hcore := c1_core P l fix prs hfk
    (by
      intro p hp
      rw [hprs, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact (hFmem q (hPmem q hq).1).1) hfn
    (by rw [hprs, List.map_map]; exact hP2)
    (by
      intro p hp r hr
      rw [hprs, List.mem_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      exact (hFmem q (hPmem q hq).1).2 p hp)
  have hprs_prod : ∀ jf : ℕ, (prs.map fun p ↦ eq1 (P.ry.getD p.2 0) (jf.testBit p.1)).prod =
      (pairs.map fun p ↦ eq1 (P.ry.getD (log2 p.2) 0) (jf.testBit p.1)).prod := by
    intro jf
    simp only [hprs, List.map_map]
    rfl
  have hker : kerVal P fs = kerVal P (fix.map (fun p ↦ KF.fixX p.1 p.2) ++ prs.map fun p ↦ KF.pair p.1 p.2) := by
    simp only [hfs, hprs, List.map_map]
    rfl
  have hE : ∀ jf < 2 ^ l, ∀ v, ct_E pt o (x0 + jf) v = eqW (sub P.kap 0 2) o *
      (ct_eqOn P.rx (List.range l) jf * ct_eqOn P.rx (ct_xFree l) x0) * ct_eqOn P.ry (List.range yVars) v := by
    intro jf hjf v
    rw [ct_E_split pt hpt o (x0 + jf) v ho (by omega), c1_eqOn_x _ x0 l jf hx hl hjf]
  cases lim with
  | none =>
    simp only [ct_limFs, ct_limYm, ct_EL]
    have hterm : ∀ jf ∈ List.range (2 ^ l),
        (if ct_inFix fix jf = true then w * ct_E pt o (x0 + jf) (a.at jf) else 0) =
          (w * eqW (sub P.kap 0 2) o * ct_eqOn P.rx (ct_xFree l) x0 * ct_eqOn P.ry (ct_yFree ym) y0) *
            ((if ct_inFix fix jf = true then (1 : FE) else 0) * ct_eqOn P.rx (List.range l) jf *
              (prs.map fun p ↦ eq1 (P.ry.getD p.2 0) (jf.testBit p.1)).prod) := by
      intro jf hjf
      rw [List.mem_range] at hjf
      by_cases hin : ct_inFix fix jf = true
      · rw [if_pos hin, if_pos hin, hE jf hjf, hat jf hjf hin, c1_eqOn_y P.ry ym hymn hymr _ y0 (hmiss jf),
          hYp _ jf (hhit jf), hprs_prod]
        ring
      · rw [if_neg hin, if_neg hin]
        ring
    rw [List.map_congr_left hterm, List.sum_map_mul_left, hcore, ← hker]
    ring
  | some e =>
    obtain ⟨he, hlim⟩ := hlim
    obtain ⟨jf1, hjf1, hin1, hb1⟩ := c1_mk l fix hfk hfn (fun _ ↦ true)
    have hne : ∀ p ∈ pairs, log2 p.2 ≠ e ∧ log2 p.2 ≠ e + 1 := by
      intro p hp
      have h1 := hhit jf1 p hp
      rw [← hat jf1 hjf1 hin1, hb1 p.1 (hFmem p (hPmem p hp).1).1 (hFmem p (hPmem p hp).1).2] at h1
      obtain ⟨h2, h3⟩ := c1_testBit_mod4 _ _ (hlim jf1 hjf1 hin1)
      constructor
      · intro hq
        rw [hq, h2] at h1
        exact Bool.false_ne_true h1
      · intro hq
        rw [hq, h3] at h1
        exact Bool.false_ne_true h1
    have hymne : ∀ j ∈ ym, j ≠ e ∧ j ≠ e + 1 := by
      intro j hj
      rw [hym, List.mem_map] at hj
      obtain ⟨p, hp, rfl⟩ := hj
      obtain ⟨i, c⟩ := p
      exact hne _ hp
    have hMn : (ym ++ [e, e + 1]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hymn, by simp, ?_⟩
      intro j hj k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact (hymne j hj).1
      · exact (hymne j hj).2
    have hMr : ∀ j ∈ ym ++ [e, e + 1], j < yVars := by
      intro j hj
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · exact hymr j hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        omega
    have hY : ∀ jf < 2 ^ l, ct_inFix fix jf = true → ∀ m < 4,
        ct_eqOn P.ry (List.range yVars) (a.at jf + m * 2 ^ e) =
          (pairs.map fun p ↦ eq1 (P.ry.getD (log2 p.2) 0) (jf.testBit p.1)).prod *
            (eq1 (P.ry.getD e 0) (m.testBit 0) * eq1 (P.ry.getD (e + 1) 0) (m.testBit 1)) *
            ct_eqOn P.ry (ct_yFree (ym ++ [e, e + 1])) y0 := by
      intro jf hjf hin m hm
      have hb := c1_limb_bits (a.at jf) e m (hlim jf hjf hin) hm
      have hv : ∀ j < yVars, j ∉ ym ++ [e, e + 1] → (a.at jf + m * 2 ^ e).testBit j = y0.testBit j := by
        intro j hj hjM
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          not_or] at hjM
        rw [hb, if_neg hjM.2.1, if_neg hjM.2.2, hat jf hjf hin, hmiss jf j hj hjM.1]
      have hp : ∀ p ∈ pairs, (a.at jf + m * 2 ^ e).testBit (log2 p.2) = jf.testBit p.1 := by
        intro p hp
        rw [hb, if_neg (hne p hp).1, if_neg (hne p hp).2, hat jf hjf hin, hhit jf p hp]
      rw [c1_eqOn_y P.ry _ hMn hMr _ y0 hv, ct_eqOn_append, hYp _ jf hp]
      simp only [ct_eqOn, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hb, if_true,
        show e + 1 ≠ e by omega, if_false]
    simp only [ct_limFs, ct_limYm, ct_EL]
    have t00 : (0 : ℕ).testBit 0 = false := by decide
    have t01 : (0 : ℕ).testBit 1 = false := by decide
    have t10 : (1 : ℕ).testBit 0 = true := by decide
    have t11 : (1 : ℕ).testBit 1 = false := by decide
    have t20 : (2 : ℕ).testBit 0 = false := by decide
    have t21 : (2 : ℕ).testBit 1 = true := by decide
    have hterm : ∀ jf ∈ List.range (2 ^ l),
        (if ct_inFix fix jf = true then w * (ct_E pt o (x0 + jf) (a.at jf) +
          FE.y * ct_E pt o (x0 + jf) (a.at jf + 2 ^ e) + FE.y * FE.y * ct_E pt o (x0 + jf) (a.at jf + 2 * 2 ^ e))
          else 0) =
          (w * eqW (sub P.kap 0 2) o * ct_eqOn P.rx (ct_xFree l) x0 *
            ct_eqOn P.ry (ct_yFree (ym ++ [e, e + 1])) y0 * limbVal (P.ry.getD e 0) (P.ry.getD (e + 1) 0)) *
            ((if ct_inFix fix jf = true then (1 : FE) else 0) * ct_eqOn P.rx (List.range l) jf *
              (prs.map fun p ↦ eq1 (P.ry.getD p.2 0) (jf.testBit p.1)).prod) := by
      intro jf hjf
      rw [List.mem_range] at hjf
      by_cases hin : ct_inFix fix jf = true
      · have h0 := hY jf hjf hin 0 (by norm_num)
        have h1 := hY jf hjf hin 1 (by norm_num)
        have h2 := hY jf hjf hin 2 (by norm_num)
        rw [Nat.zero_mul, Nat.add_zero] at h0
        rw [Nat.one_mul] at h1
        rw [if_pos hin, if_pos hin, hE jf hjf, hE jf hjf, hE jf hjf, h0, h1, h2, hprs_prod]
        simp only [t00, t01, t10, t11, t20, t21, eq1, limbVal, if_true, Bool.false_eq_true, ite_false]
        ring
      · rw [if_neg hin, if_neg hin]
        ring
    rw [List.map_congr_left hterm, List.sum_map_mul_left, hcore, ← hker, c1_kerVal_eq, List.map_append,
      List.prod_append, ← c1_kerVal_eq]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, kfVal]
    ring

theorem c2_loop {β : Type} (f : Unit → β → Id (ForInStep β)) (μ : β → ℕ) (P Q : β → Prop)
    (h : ∀ b, P b → match (f () b).run with
      | .done b' => Q b'
      | .yield b' => P b' ∧ μ b' < μ b)
    (b : β) (hb : P b) : Q (forIn Lean.Loop.mk b f).run := by
  induction hm : μ b using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    have := h b hb
    rw [show forIn Lean.Loop.mk b f = Lean.Loop.forIn Lean.Loop.mk b f from rfl,
      Lean.Loop.forIn_eq_of_monadTail]
    revert this
    rcases hf : (f () b).run with b' | b' <;> intro this
    · simp only [Id.run] at hf ⊢; rw [hf]; exact this
    · simp only [Id.run] at hf ⊢; rw [hf]; exact ih _ (hm ▸ this.2) b' this.1 rfl

/-- What `autoRun` returns: a run of consecutive free bits `b0 + t` with coefficients `R·2^t`. -/
def c2_RunOk (free : List (ℕ × ℕ)) (best : List ℕ × ℕ) : Prop :=
  ∃ b0 n, best.1 = (List.range n).map (b0 + ·) ∧ ∀ t < n, (b0 + t, best.2 * 2 ^ t) ∈ free

theorem c2_autoRun (free : List (ℕ × ℕ)) : c2_RunOk free (autoRun free) := by
  unfold autoRun
  refine c2_loop _ (fun st : (List ℕ × ℕ) × ℕ => free.toArray.size - st.2) (fun st : (List ℕ × ℕ) × ℕ => c2_RunOk free st.1)
    (fun st : (List ℕ × ℕ) × ℕ => c2_RunOk free st.1) ?_ _ ⟨0, 0, rfl, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  rintro ⟨best, i⟩ hb
  dsimp only
  by_cases hi : i < free.toArray.size
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hi)]
    have hgD : (if h : i < free.toArray.size then free.toArray.getInternal i h else (0, 0)) =
        free.toArray.getD i (0, 0) := rfl
    generalize hg : (if h : i < free.toArray.size then free.toArray.getInternal i h else (0, 0)) = g at hgD
    obtain ⟨b0, c0⟩ := g
    dsimp only
    simp only [Id.run_bind]
    generalize hJ : forIn (m := Id) Lean.Loop.mk (i + 1) _ = J
    have hin : i < J.run ∧ J.run ≤ free.toArray.size ∧
        ∀ t < J.run - i, free.toArray.getD (i + t) (0, 0) = (b0 + t, c0 * 2 ^ t) := by
      rw [← hJ]
      refine c2_loop _ (fun j => free.toArray.size - j) (fun j => i < j ∧ j ≤ free.toArray.size ∧
          ∀ t < j - i, free.toArray.getD (i + t) (0, 0) = (b0 + t, c0 * 2 ^ t))
        (fun j => i < j ∧ j ≤ free.toArray.size ∧
          ∀ t < j - i, free.toArray.getD (i + t) (0, 0) = (b0 + t, c0 * 2 ^ t)) ?_ _ ?_
      · rintro j ⟨hij, hjs, hj⟩
        by_cases hc : (decide (j < free.toArray.size) && (free.toArray.getD j (0, 0)).1 == b0 + (j - i) &&
              (free.toArray.getD j (0, 0)).2 == c0 * 2 ^ (j - i)) = true
        · simp only [hc, ↓reduceIte]
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
          refine ⟨⟨by omega, by omega, fun t ht => ?_⟩, by omega⟩
          by_cases htj : t < j - i
          · exact hj t htj
          · have : i + t = j := by omega
            rw [this, Prod.ext_iff]
            exact ⟨by rw [hc2]; omega, by rw [hc3]; congr 2; omega⟩
        · simp only [hc, ↓reduceIte, Bool.false_eq_true]
          exact ⟨hij, hjs, hj⟩
      · refine ⟨by omega, by omega, fun t ht => ?_⟩
        have : t = 0 := by omega
        subst this
        simpa using hgD.symm
    obtain ⟨hin1, hin2, hin3⟩ := hin
    have hmem : ∀ t < J.run - i, (b0 + t, c0 * 2 ^ t) ∈ free := by
      intro t ht
      rw [← hin3 t ht, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some, List.getElem_toArray]
      exact List.getElem_mem _
    by_cases hc : (decide (J.run - i > best.1.length) && c0 != 0) = true
    · simp only [hc, ↓reduceIte]
      exact ⟨⟨b0, J.run - i, rfl, hmem⟩, by omega⟩
    · simp only [hc, ↓reduceIte, Bool.false_eq_true]
      exact ⟨hb, by omega⟩
  · simp only [hi, ↓reduceIte]; exact hb

def c2_cp : Option Bool → Bool → Bool
  | none, _ => true
  | some b, v => b == v

def c2_cs {V M : Type} [AddCommMonoid V] [AddCommMonoid M] : List (V × Option Bool) → (V → M) → M
  | [], F => F 0
  | (g, none) :: G, F => c2_cs G F + c2_cs G (fun v => F (g + v))
  | (_, some false) :: G, F => c2_cs G F
  | (g, some true) :: G, F => c2_cs G (fun v => F (g + v))

def c2_ok : List (Option Bool) → ℕ → Bool
  | [], _ => true
  | s :: S, n => c2_cp s (decide (n % 2 = 1)) && c2_ok S (n / 2)

def c2_vs {V : Type} [AddCommMonoid V] : List V → ℕ → V
  | [], _ => 0
  | g :: G, n => (if n % 2 = 1 then g else 0) + c2_vs G (n / 2)

theorem c2_sum_range_two_mul {M : Type} [AddCommMonoid M] (H : ℕ → M) (N : ℕ) :
    ((List.range (2 * N)).map H).sum = ((List.range N).map fun x => H (2 * x) + H (2 * x + 1)).sum := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, List.range_succ, List.range_succ, List.range_succ]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      add_zero] at ih ⊢
    rw [ih, add_assoc]

theorem c2_cs_enum {V M : Type} [AddCommMonoid V] [AddCommMonoid M] :
    ∀ (G : List (V × Option Bool)) (F : V → M),
    ((List.range (2 ^ G.length)).map fun n =>
      if c2_ok (G.map (·.2)) n = true then F (c2_vs (G.map (·.1)) n) else 0).sum = c2_cs G F := by
  intro G
  induction G with
  | nil => intro F; simp [c2_ok, c2_vs, c2_cs]
  | cons p G ih =>
    intro F
    obtain ⟨g, st⟩ := p
    rw [List.length_cons, pow_succ, mul_comm, c2_sum_range_two_mul]
    have e0 : ∀ x : ℕ, (2 * x) % 2 = 0 ∧ (2 * x) / 2 = x ∧ (2 * x + 1) % 2 = 1 ∧ (2 * x + 1) / 2 = x :=
      fun x => ⟨by omega, by omega, by omega, by omega⟩
    simp only [List.map_cons, c2_ok, c2_vs, e0, List.sum_map_add]
    rcases st with _ | _ | _
    · simp only [c2_cp, Bool.true_and, c2_cs, ← ih]
      simp
    · simp only [c2_cp, c2_cs, ← ih]
      simp
    · simp only [c2_cp, c2_cs, ← ih]
      simp

theorem c2_cs_congr {V M : Type} [AddCommMonoid V] [AddCommMonoid M] (G : List (V × Option Bool))
    (F F' : V → M) (h : ∀ v, F v = F' v) : c2_cs G F = c2_cs G F' := by
  rw [funext h]

theorem c2_cs_perm {V M : Type} [AddCommMonoid V] [AddCommMonoid M] {G G' : List (V × Option Bool)}
    (h : G.Perm G') : ∀ F : V → M, c2_cs G F = c2_cs G' F := by
  induction h with
  | nil => intro F; rfl
  | cons p _ ih =>
    intro F
    obtain ⟨g, st⟩ := p
    rcases st with _ | _ | _ <;> simp only [c2_cs, ih]
  | swap p q G =>
    intro F
    obtain ⟨g, st⟩ := p
    obtain ⟨g', st'⟩ := q
    rcases st with _ | _ | _ <;> rcases st' with _ | _ | _ <;> simp only [c2_cs, add_left_comm g g'] <;>
      abel
  | trans _ _ ih1 ih2 => intro F; rw [ih1, ih2]

theorem c2_cs_append {V M : Type} [AddCommMonoid V] [AddCommMonoid M] (A B : List (V × Option Bool)) :
    ∀ F : V → M, c2_cs (A ++ B) F = c2_cs A (fun u => c2_cs B (fun v => F (u + v))) := by
  induction A with
  | nil => intro F; simp [c2_cs]
  | cons p A ih =>
    intro F
    obtain ⟨g, st⟩ := p
    rcases st with _ | _ | _ <;> simp only [List.cons_append, c2_cs, ih, add_assoc]

theorem c2_cs_fixed {V M : Type} [AddCommMonoid V] [AddCommMonoid M] {ι : Type} (c : ι → V)
    (L : List (ι × Bool)) : ∀ F : V → M,
    c2_cs (L.map fun p => (c p.1, some p.2)) F = F ((L.map fun p => if p.2 then c p.1 else 0).sum) := by
  induction L with
  | nil => intro F; simp [c2_cs]
  | cons p L ih =>
    intro F
    obtain ⟨i, b⟩ := p
    cases b <;> simp [c2_cs, ih]

theorem c2_ok_iff : ∀ (S : List (Option Bool)) (n : ℕ),
    c2_ok S n = true ↔ ∀ k < S.length, c2_cp (S.getD k none) (n.testBit k) = true := by
  intro S
  induction S with
  | nil => intro n; simp [c2_ok]
  | cons s S ih =>
    intro n
    simp only [c2_ok, Bool.and_eq_true, ih, List.length_cons]
    constructor
    · rintro ⟨h0, h1⟩ k hk
      rcases k with _ | k
      · simpa [Nat.testBit_zero] using h0
      · simpa [Nat.testBit_add_one] using h1 k (by omega)
    · intro h
      refine ⟨by simpa [Nat.testBit_zero] using h 0 (by omega), fun k hk => ?_⟩
      simpa [Nat.testBit_add_one] using h (k + 1) (by omega)

theorem c2_vs_eq {V : Type} [AddCommMonoid V] : ∀ (G : List V) (n : ℕ),
    c2_vs G n = ((List.range G.length).map fun k => if n.testBit k then G.getD k 0 else 0).sum := by
  intro G
  induction G with
  | nil => intro n; simp [c2_vs]
  | cons g G ih =>
    intro n
    rw [List.length_cons, List.sum_range_succ', c2_vs, ih]
    simp [Nat.testBit_zero, Nat.testBit_add_one]

def c2_stat : List (ℕ × Bool) → ℕ → Option Bool
  | [], _ => none
  | (i, b) :: fix, k => if i = k then some b else c2_stat fix k

theorem c2_stat_some : ∀ (fix : List (ℕ × Bool)) (k : ℕ) (b : Bool), c2_stat fix k = some b → (k, b) ∈ fix := by
  intro fix
  induction fix with
  | nil => intro k b h; simp [c2_stat] at h
  | cons p fix ih =>
    intro k b h
    obtain ⟨i, b'⟩ := p
    simp only [c2_stat] at h
    split_ifs at h with hik
    · cases h; subst hik; simp
    · exact List.mem_cons_of_mem _ (ih k b h)

theorem c2_stat_mem : ∀ (fix : List (ℕ × Bool)), (fix.map (·.1)).Nodup → ∀ (k : ℕ) (b : Bool),
    (k, b) ∈ fix → c2_stat fix k = some b := by
  intro fix
  induction fix with
  | nil => intro _ k b h; simp at h
  | cons p fix ih =>
    intro hn k b h
    obtain ⟨i, b'⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    simp only [c2_stat]
    rcases List.mem_cons.mp h with h | h
    · cases h; simp
    · have hik : i ≠ k := by
        rintro rfl; exact hn.1 ⟨(i, b), h, rfl⟩
      simp only [hik, ↓reduceIte]
      exact ih hn.2 k b h

theorem c2_stat_none : ∀ (fix : List (ℕ × Bool)) (k : ℕ),
    c2_stat fix k = none ↔ (fix.any (·.1 == k)) = false := by
  intro fix
  induction fix with
  | nil => intro k; simp [c2_stat]
  | cons p fix ih =>
    intro k
    obtain ⟨i, b'⟩ := p
    simp only [c2_stat, List.any_cons]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik, ih]

theorem c2_perm_idx (l : ℕ) (fix : List (ℕ × Bool)) (hfix : (∀ bv ∈ fix, bv.1 < l) ∧ (fix.map (·.1)).Nodup) :
    ((List.range l).map fun k => (k, c2_stat fix k)).Perm
      (fix.map (fun p => (p.1, some p.2)) ++
        ((List.range l).filter (fun i => !fix.any (·.1 == i))).map (fun k => (k, (none : Option Bool)))) := by
  have hfn : fix.Nodup := List.Nodup.of_map _ hfix.2
  rw [List.perm_ext_iff_of_nodup]
  · rintro ⟨k, s⟩
    simp only [List.mem_map, List.mem_range, List.mem_append, List.mem_filter, Prod.mk.injEq,
      Bool.not_eq_true']
    constructor
    · rintro ⟨k', hk', rfl, rfl⟩
      rcases hs : c2_stat fix k' with _ | b
      · exact Or.inr ⟨k', ⟨hk', (c2_stat_none fix k').mp hs⟩, rfl, rfl⟩
      · exact Or.inl ⟨(k', b), c2_stat_some fix k' b hs, rfl, rfl⟩
    · rintro (⟨p, hp, rfl, rfl⟩ | ⟨k', ⟨hk', hn⟩, rfl, rfl⟩)
      · exact ⟨p.1, hfix.1 p hp, rfl, c2_stat_mem fix hfix.2 p.1 p.2 hp⟩
      · exact ⟨k', hk', rfl, (c2_stat_none fix k').mpr hn⟩
  · exact List.nodup_range.map fun a b h => (Prod.mk.inj h).1
  · rw [List.nodup_append]
    refine ⟨hfn.map fun p q h => ?_, (List.nodup_range.filter _).map fun a b h => (Prod.mk.inj h).1, ?_⟩
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      exact Prod.ext h.1 h.2
    · intro x hx y hy hxy
      simp only [List.mem_map] at hx hy
      obtain ⟨p, -, rfl⟩ := hx
      obtain ⟨k, -, rfl⟩ := hy
      simp at hxy

theorem c2_perm_free (FB xs : List ℕ) (hFB : FB.Nodup) (hxs : xs.Nodup) (hxsF : ∀ b ∈ xs, b ∈ FB) :
    (FB.filter (fun i => !xs.contains i) ++ xs).Perm FB := by
  have h1 : (FB.filter (fun i => xs.contains i)).Perm xs := by
    rw [List.perm_ext_iff_of_nodup (hFB.filter _) hxs]
    intro b
    simp only [List.mem_filter, List.contains_iff_mem]
    exact ⟨fun h => h.2, fun h => ⟨hxsF b h, h⟩⟩
  have h2 := List.filter_append_perm (fun i => !xs.contains i) FB
  simp only [Bool.not_not] at h2
  exact (List.Perm.append_left _ h1.symm).trans h2

theorem c2_getD_map_range {α : Type} (f : ℕ → α) (l k : ℕ) (d : α) (hk : k < l) :
    ((List.range l).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem c2_inFix_eq (l : ℕ) (fix : List (ℕ × Bool)) (hfix : (∀ bv ∈ fix, bv.1 < l) ∧ (fix.map (·.1)).Nodup)
    (jf : ℕ) : ct_inFix fix jf = c2_ok ((List.range l).map (c2_stat fix)) jf := by
  rw [Bool.eq_iff_iff, c2_ok_iff, ct_inFix, List.all_eq_true]
  simp only [List.length_map, List.length_range]
  constructor
  · intro h k hk
    rw [c2_getD_map_range _ _ _ _ hk]
    rcases hs : c2_stat fix k with _ | b
    · rfl
    · have := h _ (c2_stat_some fix k b hs)
      simp only [beq_iff_eq] at this
      simp [c2_cp, this]
  · intro h bv hbv
    have := h bv.1 (hfix.1 bv hbv)
    rw [c2_getD_map_range _ _ _ _ (hfix.1 bv hbv), c2_stat_mem fix hfix.2 bv.1 bv.2 hbv] at this
    simp only [c2_cp, beq_iff_eq] at this
    simp [this]

theorem c2_ok_none {α : Type} : ∀ (L : List α) (n : ℕ), c2_ok (L.map fun _ => (none : Option Bool)) n = true := by
  intro L
  induction L with
  | nil => intro n; rfl
  | cons a L ih => intro n; simp only [List.map_cons, c2_ok, c2_cp, Bool.true_and, ih]

theorem c2_vs_map {V : Type} [AddCommMonoid V] (c : ℕ → V) (L : List ℕ) (n : ℕ) :
    c2_vs (L.map c) n = ((List.range L.length).map fun k => if n.testBit k then c (L.getD k 0) else 0).sum := by
  rw [c2_vs_eq, List.length_map]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  rw [List.mem_range] at hk
  simp [List.getD_eq_getElem?_getD, hk]

/-- A sum over the cube with all free entries: the plain enumeration. -/
theorem c2_cs_free {V M : Type} [AddCommMonoid V] [AddCommMonoid M] (c : ℕ → V) (L : List ℕ) (F : V → M) :
    c2_cs (L.map fun k => (c k, (none : Option Bool))) F =
      ((List.range (2 ^ L.length)).map fun m =>
        F (((List.range L.length).map fun k => if m.testBit k then c (L.getD k 0) else 0).sum)).sum := by
  rw [← c2_cs_enum, List.length_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  rw [List.map_map, List.map_map]
  have e1 : ((fun p : V × Option Bool => p.2) ∘ fun k => (c k, (none : Option Bool))) = fun _ => none := rfl
  have e2 : ((fun p : V × Option Bool => p.1) ∘ fun k => (c k, (none : Option Bool))) = c := rfl
  rw [e1, e2, c2_ok_none, c2_vs_map]; rfl

/-- **The re-indexing**: the sub-cube's iterations are the fixed bits' values, the inner bits and the run. -/
theorem c2_reindex {V M : Type} [AddCommMonoid V] [AddCommMonoid M] (c : ℕ → V) (F : V → M) (l : ℕ)
    (fix : List (ℕ × Bool)) (hfix : (∀ bv ∈ fix, bv.1 < l) ∧ (fix.map (·.1)).Nodup) (xs : List ℕ)
    (hxs : xs.Nodup) (hxsF : ∀ b ∈ xs, b ∈ (List.range l).filter (fun i => !fix.any (·.1 == i))) :
    ((List.range (2 ^ l)).map fun jf =>
      if ct_inFix fix jf = true then F (((List.range l).map fun k => if jf.testBit k then c k else 0).sum)
      else 0).sum =
    ((List.range (2 ^ (((List.range l).filter (fun i => !fix.any (·.1 == i))).filter
        (fun i => !xs.contains i)).length)).map fun m =>
      ((List.range (2 ^ xs.length)).map fun j =>
        F ((fix.map fun p => if p.2 then c p.1 else 0).sum +
          ((List.range (((List.range l).filter (fun i => !fix.any (·.1 == i))).filter
              (fun i => !xs.contains i)).length).map fun k =>
            if m.testBit k then c ((((List.range l).filter (fun i => !fix.any (·.1 == i))).filter
              (fun i => !xs.contains i)).getD k 0) else 0).sum +
          ((List.range xs.length).map fun t => if j.testBit t then c (xs.getD t 0) else 0).sum)).sum).sum := by
  set FB := (List.range l).filter (fun i => !fix.any (·.1 == i)) with hFB
  set IB := FB.filter (fun i => !xs.contains i) with hIB
  set S := (List.range l).map fun k => (c k, c2_stat fix k) with hS
  have hL : ((List.range (2 ^ l)).map fun jf =>
      if ct_inFix fix jf = true then F (((List.range l).map fun k => if jf.testBit k then c k else 0).sum)
      else 0).sum = c2_cs S F := by
    rw [← c2_cs_enum]
    have e1 : S.length = l := by simp [hS]
    have e2 : S.map (·.2) = (List.range l).map (c2_stat fix) := by simp [hS]
    have e3 : S.map (·.1) = (List.range l).map c := by simp [hS]
    rw [e1, e2, e3]
    congr 1
    refine List.map_congr_left fun jf _ => ?_
    rw [c2_inFix_eq l fix hfix, c2_vs_map]
    congr 2
    simp only [List.length_range]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    simp [List.getD_eq_getElem?_getD, hk]
  have hP : S.Perm ((fix.map fun p => (c p.1, some p.2)) ++
      ((IB.map fun k => (c k, (none : Option Bool))) ++ (xs.map fun k => (c k, (none : Option Bool))))) := by
    have h1 := (c2_perm_idx l fix hfix).map (fun p : ℕ × Option Bool => (c p.1, p.2))
    have h2 := (c2_perm_free FB xs ((List.nodup_range).filter _) hxs hxsF).symm.map
      (fun k => (c k, (none : Option Bool)))
    simp only [List.map_map, List.map_append] at h1 h2
    rw [hS]
    refine h1.trans (List.Perm.append_left _ h2)
  rw [hL, c2_cs_perm hP, c2_cs_append, c2_cs_fixed, c2_cs_append, c2_cs_free]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  rw [c2_cs_free]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  rw [add_assoc]

theorem c2_prod_sum {α : Type} (L : List α) (f : α → ℕ × ℕ) :
    (L.map f).sum = ((L.map fun x => (f x).1).sum, (L.map fun x => (f x).2).sum) := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

theorem c2_bits_sum : ∀ (l jf : ℕ), jf < 2 ^ l →
    ((List.range l).map fun k => if jf.testBit k then 2 ^ k else 0).sum = jf := by
  intro l
  induction l with
  | zero => intro jf h; simp at h ⊢; omega
  | succ l ih =>
    intro jf h
    rw [List.sum_range_succ']
    have e : ∀ i, (if jf.testBit (i.succ) = true then 2 ^ i.succ else 0) =
        2 * (if (jf / 2).testBit i = true then 2 ^ i else 0) := by
      intro i; rw [Nat.succ_eq_add_one, Nat.testBit_add_one, pow_succ]; split_ifs <;> ring
    simp only [e, List.sum_map_mul_left]
    rw [ih (jf / 2) (by rw [pow_succ] at h; omega), Nat.testBit_zero]
    split_ifs with h1 <;> simp at h1 <;> omega

theorem c2_sum_range_le {M : Type} [AddCommMonoid M] (f : ℕ → M) (N N' : ℕ) (hN : N ≤ N')
    (h : ∀ k, N ≤ k → k < N' → f k = 0) : ((List.range N').map f).sum = ((List.range N).map f).sum := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rw [List.sum_eq_zero (l := List.map (f ∘ fun x => N + x) (List.range d)), add_zero]
  intro x hx
  simp only [List.mem_map, List.mem_range, Function.comp] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact h _ (by omega) (by omega)

theorem c2_at_eq (a : Aff) (l jf : ℕ) (h : jf < 2 ^ l) :
    a.at jf = a.y0 + ((List.range l).map fun k => if jf.testBit k then a.coef.getD k 0 else 0).sum := by
  rw [Aff.at]
  congr 1
  have h0 : ∀ k, l ≤ k ∨ a.coef.length ≤ k →
      (if jf.testBit k then a.coef.getD k 0 else 0) = 0 := by
    intro k hk
    rcases hk with hk | hk
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      rfl
    · simp [List.getD_eq_getElem?_getD, hk]
  rw [← c2_sum_range_le _ a.coef.length (max a.coef.length l) (le_max_left _ _)
      (fun k hk1 hk2 => h0 k (Or.inr (by omega))),
    ← c2_sum_range_le _ l (max a.coef.length l) (le_max_right _ _) (fun k hk1 hk2 => h0 k (Or.inl (by omega)))]

/-- The free bits of the sub-cube. -/
def c2_FB (l : ℕ) (fix : List (ℕ × Bool)) : List ℕ := (List.range l).filter (fun i => !fix.any (·.1 == i))

/-- The inner (enumerated) bits. -/
def c2_IB (l : ℕ) (fix : List (ℕ × Bool)) (xs : List ℕ) : List ℕ := (c2_FB l fix).filter (fun i => !xs.contains i)

/-- The re-indexing on words: the slot and the word with coefficients `κ`. -/
theorem c2_reindex2 {M : Type} [AddCommMonoid M] (κ : ℕ → ℕ) (F : ℕ × ℕ → M) (l : ℕ)
    (fix : List (ℕ × Bool)) (hfix : (∀ bv ∈ fix, bv.1 < l) ∧ (fix.map (·.1)).Nodup) (xs : List ℕ)
    (hxs : xs.Nodup) (hxsF : ∀ b ∈ xs, b ∈ c2_FB l fix) :
    ((List.range (2 ^ l)).map fun jf =>
      if ct_inFix fix jf = true then F (jf, ((List.range l).map fun k => if jf.testBit k then κ k else 0).sum)
      else 0).sum =
    ((List.range (2 ^ (c2_IB l fix xs).length)).map fun m =>
      ((List.range (2 ^ xs.length)).map fun j =>
        F ((fix.map fun p => if p.2 then 2 ^ p.1 else 0).sum +
            ((List.range (c2_IB l fix xs).length).map fun k =>
              if m.testBit k then 2 ^ ((c2_IB l fix xs).getD k 0) else 0).sum +
            ((List.range xs.length).map fun t => if j.testBit t then 2 ^ (xs.getD t 0) else 0).sum,
          (fix.map fun p => if p.2 then κ p.1 else 0).sum +
            ((List.range (c2_IB l fix xs).length).map fun k =>
              if m.testBit k then κ ((c2_IB l fix xs).getD k 0) else 0).sum +
            ((List.range xs.length).map fun t => if j.testBit t then κ (xs.getD t 0) else 0).sum)).sum).sum := by
  have h := c2_reindex (fun k => (2 ^ k, κ k)) F l fix hfix xs hxs hxsF
  unfold c2_IB c2_FB
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    refine List.map_congr_left fun jf hjf => ?_
    rw [List.mem_range] at hjf
    congr 2
    rw [c2_prod_sum]
    simp only [apply_ite Prod.fst, apply_ite Prod.snd, Prod.fst_zero, Prod.snd_zero]
    rw [c2_bits_sum l jf hjf]
  · congr 1
    refine List.map_congr_left fun m _ => ?_
    congr 1
    refine List.map_congr_left fun j _ => ?_
    congr 1
    simp only [c2_prod_sum, apply_ite Prod.fst, apply_ite Prod.snd, Prod.fst_zero, Prod.snd_zero,
      Prod.mk_add_mk]

theorem c2_sum_filter (L : List ℕ) (p : ℕ → Bool) (f : ℕ → ℕ) :
    ((L.filter p).map f).sum = (L.map fun k => if p k then f k else 0).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => by_cases hp : p x <;> simp [hp, ih]

theorem c2_ds (L : List ℕ) (h : ℕ → ℕ) (f : ℕ × ℕ → ℕ) (m : ℕ) :
    ((((List.range (L.map fun i => (i, h i)).length).filter m.testBit).map
      fun k => (L.map fun i => (i, h i)).getD k (0, 0)).map f).sum =
    ((List.range L.length).map fun k => if m.testBit k then f (L.getD k 0, h (L.getD k 0)) else 0).sum := by
  rw [List.map_map, c2_sum_filter, List.length_map]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  rw [List.mem_range] at hk
  simp [List.getD_eq_getElem?_getD, hk]

theorem c2_sum_zero {A B : ℕ} {G : ℕ → ℕ → ℕ}
    (h : ((List.range A).map fun m => ((List.range B).map fun j => G m j).sum).sum = 0) :
    ∀ m < A, ∀ j < B, G m j = 0 := by
  intro m hm j hj
  rw [List.sum_eq_zero_iff] at h
  have h1 := h _ (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)
  rw [List.sum_eq_zero_iff] at h1
  exact h1 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

theorem c2_sum_ite_zero {α : Type} (L : List α) (p : α → Prop) [DecidablePred p] (f : α → ℕ)
    (h : ∀ x ∈ L, p x → f x = 0) : (L.map fun x => if p x then f x else 0).sum = 0 := by
  rw [List.sum_eq_zero_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  split_ifs with hp
  · exact h x hx hp
  · rfl

theorem c2_sum_single (g : ℕ → ℕ) (b : ℕ) : ∀ N, b < N →
    ((List.range N).map fun k => if k = b then g k else 0).sum = g b := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro h
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hb : b < N
    · rw [ih hb]; simp [show N ≠ b by omega]
    · have hbN : b = N := by omega
      subst hbN
      rw [c2_sum_ite_zero _ _ _ (fun k hk hkb => absurd hkb (by simp at hk; omega))]
      simp

theorem c2_testBit_add (x0 y l b : ℕ) (hx : x0 % 2 ^ l = 0) (hy : y < 2 ^ l) (hb : b < l) :
    (x0 + y).testBit b = y.testBit b := by
  have h1 := Nat.testBit_mod_two_pow (x0 + y) l b
  have h2 : (x0 + y) % 2 ^ l = y := by
    rw [Nat.add_mod, hx, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hy]
  rw [h2] at h1
  simp only [hb, decide_true, Bool.true_and] at h1
  exact h1.symm

/-- `addSub`'s carry-automaton case (C2). -/
theorem ct_addSub_K3 (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s)
    (o : ℕ) (w : FE) (x0 l : ℕ) (a : Aff) (fix : List (ℕ × Bool)) (lim : Option ℕ)
    (ho : o < 4) (hx : x0 % 2 ^ l = 0) (hxl : x0 + 2 ^ l ≤ 2 ^ xVars)
    (hfix : (∀ bv ∈ fix, bv.1 < l) ∧ (fix.map (·.1)).Nodup)
    (hlim : match lim with
      | none => True
      | some e => e + 1 < yVars ∧ ∀ jf < 2 ^ l, ct_inFix fix jf = true → (a.at jf >>> e) % 4 = 0)
    (hinj : injOk (subAff l a fix).y0 ((subAff l a fix).free.map (·.2)) = false) :
    ct_Adds pt s (s.addSub o w x0 (subAff l a fix) lim)
      ((List.range (2 ^ l)).map fun jf ↦
        if ct_inFix fix jf then w * ct_EL pt lim o (x0 + jf) (a.at jf) else 0).sum := by
  rw [CS.addSub, ite_eq_right_iff.mpr (fun h => absurd (hinj ▸ h) (by decide))]
  rcases hA : autoRun (subAff l a fix).free with ⟨xs, R⟩
  dsimp only
  obtain ⟨b0, n, hxs0, hR0⟩ := c2_autoRun (subAff l a fix).free
  rw [hA] at hxs0 hR0
  dsimp only at hxs0 hR0
  have hfree : (subAff l a fix).free = (c2_FB l fix).map (fun i => (i, a.coef.getD i 0)) := rfl
  have hinner : (subAff l a fix).free.filter (fun x => !xs.contains x.1) =
      (c2_IB l fix xs).map (fun i => (i, a.coef.getD i 0)) := by
    rw [hfree, List.filter_map]; rfl
  have hy0 : (subAff l a fix).y0 = a.y0 + (fix.map fun p => if p.2 then a.coef.getD p.1 0 else 0).sum := rfl
  have hfixq : (subAff l a fix).fix = fix := rfl
  -- the run
  have hxlen : xs.length = n := by rw [hxs0]; simp
  have hxget : ∀ t < n, xs.getD t 0 = b0 + t := by
    intro t ht; rw [hxs0]; simp [List.getD_eq_getElem?_getD, ht]
  have hxsnd : xs.Nodup := by
    rw [hxs0]; exact List.nodup_range.map (fun u v huv => by simpa using huv)
  have hrun : ∀ t < n, b0 + t ∈ c2_FB l fix ∧ a.coef.getD (b0 + t) 0 = R * 2 ^ t := by
    intro t ht
    have := hR0 t ht
    rw [hfree, List.mem_map] at this
    obtain ⟨i, hi, hie⟩ := this
    simp only [Prod.mk.injEq] at hie
    obtain ⟨rfl, h2⟩ := hie
    exact ⟨hi, h2⟩
  have hxsF : ∀ b ∈ xs, b ∈ c2_FB l fix := by
    intro b hb
    rw [hxs0, List.mem_map] at hb
    obtain ⟨t, ht, rfl⟩ := hb
    exact (hrun t (List.mem_range.mp ht)).1
  have hxsY : ∀ j < 2 ^ xs.length,
      ((List.range xs.length).map fun t => if j.testBit t then a.coef.getD (xs.getD t 0) 0 else 0).sum = R * j := by
    intro j hj
    conv_rhs => rw [← c2_bits_sum xs.length j hj]
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [List.mem_range, hxlen] at ht
    rw [hxget t ht, (hrun t ht).2]
    split_ifs <;> simp
  rw [hinner, hfixq, hy0]
  simp only [c2_ds]
  simp only [List.length_map]
  have hR := fun {M : Type} [AddCommMonoid M] (κ : ℕ → ℕ) (F : ℕ × ℕ → M) =>
    c2_reindex2 κ F l fix hfix xs hxsnd hxsF
  refine ct_Adds_congr (ct_Adds_foldl pt _ (fun m => ct_memSem pt (xs, R, lim)
      (a.y0 + (fix.map fun p => if p.2 = true then a.coef.getD p.1 0 else 0).sum +
        ((List.range (c2_IB l fix xs).length).map fun k =>
          if m.testBit k = true then a.coef.getD ((c2_IB l fix xs).getD k 0) 0 else 0).sum, o,
       x0 + (fix.map fun x => if x.2 = true then 2 ^ x.1 else 0).sum +
        ((List.range (c2_IB l fix xs).length).map fun k =>
          if m.testBit k = true then 2 ^ (c2_IB l fix xs).getD k 0 else 0).sum, w))
    (fun m => m < 2 ^ (c2_IB l fix xs).length) ?_ _ s hs (fun m hm => List.mem_range.mp hm)) ?_
  · intro s' m hs' hm
    have hj0 : (0 : ℕ) < 2 ^ xs.length := Nat.two_pow_pos _
    have hz : ∀ (g : ℕ → ℕ), ((List.range xs.length).map fun t => if (0 : ℕ).testBit t then g t else 0).sum = 0 :=
      fun g => by simp
    -- the slot offset is below `2^l`
    have hB := c2_sum_zero (((hR (fun _ => 0) (fun u : ℕ × ℕ => if u.1 < 2 ^ l then 0 else 1)).symm.trans
      (c2_sum_ite_zero _ _ _ (fun jf hjf _ => by simp [List.mem_range.mp hjf])))) m hm 0 hj0
    simp only [hz, add_zero, ite_eq_left_iff, not_lt, one_ne_zero, imp_false, not_le] at hB
    -- the run's bits are clear in the slot
    have hT : ∀ b ∈ xs, ((fix.map fun x : ℕ × Bool => if x.2 = true then 2 ^ x.1 else 0).sum +
        ((List.range (c2_IB l fix xs).length).map fun k =>
          if m.testBit k = true then 2 ^ (c2_IB l fix xs).getD k 0 else 0).sum).testBit b = false := by
      intro b hb
      have hbF := hxsF b hb
      simp only [c2_FB, List.mem_filter, List.mem_range, Bool.not_eq_true', List.any_eq_false,
        beq_iff_eq] at hbF
      have H := c2_sum_zero (((hR (fun k => if k = b then 1 else 0)
        (fun u : ℕ × ℕ => if u.1.testBit b = decide (u.2 = 1) then 0 else 1)).symm.trans
        (c2_sum_ite_zero _ _ _ (fun jf hjf _ => by
          have e : ((List.range l).map fun k => if jf.testBit k = true then (if k = b then 1 else 0) else 0).sum =
              if jf.testBit b then 1 else 0 := by
            rw [← c2_sum_single (fun k => if jf.testBit k then 1 else 0) b l hbF.1]
            congr 1
            refine List.map_congr_left fun k _ => ?_
            by_cases hkb : k = b <;> simp [hkb]
          rw [e]; cases jf.testBit b <;> simp)))) m hm 0 hj0
      have e1 : (fix.map fun p => if p.2 = true then (if p.1 = b then 1 else 0) else 0).sum = 0 :=
        c2_sum_ite_zero _ _ _ (fun p hp _ => by
          split_ifs with h
          · exact absurd h (hbF.2 p hp)
          · rfl)
      have e2 : ((List.range (c2_IB l fix xs).length).map fun k =>
          if m.testBit k = true then (if (c2_IB l fix xs).getD k 0 = b then 1 else 0) else 0).sum = 0 :=
        c2_sum_ite_zero _ _ _ (fun k hk _ => by
          rw [List.mem_range] at hk
          have hmem : (c2_IB l fix xs).getD k 0 ∈ c2_IB l fix xs := by
            rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
          generalize (c2_IB l fix xs).getD k 0 = z at hmem ⊢
          simp only [c2_IB, List.mem_filter, Bool.not_eq_true'] at hmem
          split_ifs with h
          · subst h; simp [hb] at hmem
          · rfl)
      simp only [hz, add_zero, e1, e2] at H
      simpa using H
    refine ct_addMember pt s' hs' xs R _ o _ w lim ⟨ho, ?_, ?_, ?_, ?_, trivial⟩ ?_
    · rw [hxs0]; exact List.pairwise_map.mpr (List.pairwise_lt_range.imp (by omega))
    · intro b hb
      have hbF := hxsF b hb
      simp only [c2_FB, List.mem_filter, List.mem_range] at hbF
      have : 2 ^ b < 2 ^ xVars := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hbF.1) (by omega)
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    · intro b hb
      have hbF := hxsF b hb
      simp only [c2_FB, List.mem_filter, List.mem_range] at hbF
      dsimp only
      rw [Nat.add_assoc x0, c2_testBit_add _ _ l b hx hB hbF.1, hT b hb]
    · dsimp only
      omega
    · rcases lim with _ | e
      · trivial
      · refine ⟨hlim.1, fun j hj => ?_⟩
        have H := c2_sum_zero (((hR (fun k => a.coef.getD k 0)
          (fun u : ℕ × ℕ => if ((a.y0 + u.2) >>> e) % 4 = 0 then 0 else 1)).symm.trans
          (c2_sum_ite_zero _ _ _ (fun jf hjf hin => by
            rw [← c2_at_eq a l jf (List.mem_range.mp hjf)]
            simp only [hlim.2 jf (List.mem_range.mp hjf) hin, ↓reduceIte])))) m hm j hj
        rw [hxsY j hj] at H
        simp only [ite_eq_left_iff, one_ne_zero, imp_false, not_not] at H
        simpa only [add_assoc] using H
  · have e1 : ((List.range (2 ^ l)).map fun jf ↦
        if ct_inFix fix jf then w * ct_EL pt lim o (x0 + jf) (a.at jf) else 0) =
        ((List.range (2 ^ l)).map fun jf ↦ if ct_inFix fix jf = true then
          (fun u : ℕ × ℕ => w * ct_EL pt lim o (x0 + u.1) (a.y0 + u.2))
            (jf, ((List.range l).map fun k => if jf.testBit k then a.coef.getD k 0 else 0).sum) else 0) := by
      refine List.map_congr_left fun jf hjf => ?_
      rw [c2_at_eq a l jf (List.mem_range.mp hjf)]
    rw [e1, hR (fun k => a.coef.getD k 0) (fun u : ℕ × ℕ => w * ct_EL pt lim o (x0 + u.1) (a.y0 + u.2))]
    congr 1
    refine List.map_congr_left fun m _ => ?_
    simp only [ct_memSem]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [hxsY j (List.mem_range.mp hj)]
    simp only [add_assoc]

/-- **A sub-cube's pieces** (C1: the injective atom; C2: the pass members). -/
theorem ct_addSub (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s)
    (o : ℕ) (w : FE) (x0 l : ℕ) (a : Aff) (fix : List (ℕ × Bool)) (lim : Option ℕ)
    (ho : o < 4) (hx : x0 % 2 ^ l = 0) (hxl : x0 + 2 ^ l ≤ 2 ^ xVars)
    (hfix : (∀ bv ∈ fix, bv.1 < l) ∧ (fix.map (·.1)).Nodup)
    (hlim : match lim with
      | none => True
      | some e => e + 1 < yVars ∧ ∀ jf < 2 ^ l, ct_inFix fix jf = true → (a.at jf >>> e) % 4 = 0) :
    ct_Adds pt s (s.addSub o w x0 (subAff l a fix) lim)
      ((List.range (2 ^ l)).map fun jf ↦
        if ct_inFix fix jf then w * ct_EL pt lim o (x0 + jf) (a.at jf) else 0).sum := by
  cases hinj : injOk (subAff l a fix).y0 ((subAff l a fix).free.map (·.2))
  · exact ct_addSub_K3 pt hpt s hs o w x0 l a fix lim ho hx hxl hfix hlim hinj
  · exact ct_addSub_inj pt hpt s hs o w x0 l a fix lim ho hx hxl hfix hlim hinj

/-! ## C6 generic helpers -/

theorem c6_FE_eq_of_beq {a b : FE} (h : (a == b) = true) : a = b := by
  obtain ⟨a0, a1, a2⟩ := a; obtain ⟨b0, b1, b2⟩ := b
  have h' : ((a0 == b0 && a1 == b1) && a2 == b2) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  rw [eq_of_beq h1, eq_of_beq h2, eq_of_beq h3]

theorem c6_lsum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem c6_lprod {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

theorem c6_lprod_filter {M : Type*} [CommMonoid M] (P : ℕ → Bool) (f : ℕ → M) (n : ℕ) :
    (((List.range n).filter P).map f).prod = ∏ i ∈ Finset.range n, if P i = true then f i else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
    cases h : P n <;> simp [h]

theorem c6_lsum_filter {M : Type*} [AddCommMonoid M] (P : ℕ → Bool) (f : ℕ → M) (n : ℕ) :
    (((List.range n).filter P).map f).sum = ∑ i ∈ Finset.range n, if P i = true then f i else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    cases h : P n <;> simp [h]

theorem c6_sum_prod_bits {R : Type*} [CommSemiring R] (l : ℕ) (f : ℕ → Bool → R) :
    ∑ jf ∈ Finset.range (2 ^ l), ∏ i ∈ Finset.range l, f i (jf.testBit i) =
      ∏ i ∈ Finset.range l, (f i false + f i true) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ, mul_two, Finset.sum_range_add, Finset.prod_range_succ, mul_add, ← ih,
      Finset.sum_mul, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl; intro jf hjf
      rw [Finset.mem_range] at hjf
      rw [Finset.prod_range_succ, Nat.testBit_lt_two_pow hjf]
    · apply Finset.sum_congr rfl; intro jf hjf
      rw [Finset.mem_range] at hjf
      rw [Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hjf]
      congr 1
      apply Finset.prod_congr rfl; intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.testBit_two_pow_add_gt hi]

theorem c6_tb_add {x j L : ℕ} (hx : x % 2 ^ L = 0) (hj : j < 2 ^ L) (i : ℕ) :
    (x + j).testBit i = if i < L then j.testBit i else x.testBit i := by
  obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero hx
  rw [Nat.testBit_two_pow_mul_add m hj]
  have h0 := Nat.testBit_two_pow_mul_add m (Nat.two_pow_pos L) i
  simp only [Nat.add_zero] at h0
  split_ifs with h
  · rfl
  · rw [h0, if_neg h]

theorem c6_eqOn_range (r : Array FE) (N v : ℕ) :
    ct_eqOn r (List.range N) v = ∏ i ∈ Finset.range N, eq1 (r.getD i 0) (v.testBit i) :=
  c6_lprod _ _

theorem c6_eqOn_filter (r : Array FE) (N : ℕ) (P : ℕ → Bool) (v : ℕ) :
    ct_eqOn r ((List.range N).filter P) v =
      ∏ i ∈ Finset.range N, if P i = true then eq1 (r.getD i 0) (v.testBit i) else 1 :=
  c6_lprod_filter _ _ _

theorem c6_prod_lt {M : Type*} [CommMonoid M] {N L : ℕ} (h : L ≤ N) (f : ℕ → M) :
    ∏ i ∈ Finset.range N, (if i < L then f i else 1) = ∏ i ∈ Finset.range L, f i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.prod_range_add]
  rw [Finset.prod_congr rfl (fun i hi ↦ if_pos (Finset.mem_range.mp hi)),
    Finset.prod_congr rfl (fun i _ ↦ if_neg (by omega : ¬ L + i < L)), Finset.prod_const_one, mul_one]

theorem c6_foldl_mul {α : Type} (g : α → FE) (fs : List α) (a : FE) :
    fs.foldl (fun acc f ↦ acc * g f) a = a * (fs.map g).prod := by
  induction fs generalizing a with
  | nil => simp
  | cons f fs ih => simp only [List.foldl_cons, ih, List.map_cons, List.prod_cons]; ring

theorem c6_kerVal (P : Pt) (fs : List KF) : kerVal P fs = (fs.map (kfVal P)).prod := by
  rw [kerVal, c6_foldl_mul, one_mul]

theorem c6_eqW_map (f : ℕ → FE) (n u : ℕ) :
    eqW ((List.range n).map f) u = ∏ k ∈ Finset.range n, eq1 (f k) (u.testBit k) := by
  induction n generalizing f u with
  | zero => simp [eqW]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, eqW, Finset.prod_range_succ']
    have := ih (f ∘ Nat.succ) (u / 2)
    rw [this, mul_comm]
    congr 1
    · apply Finset.prod_congr rfl; intro k _
      simp [Nat.testBit_add_one]
    · simp [eq1, Nat.testBit_zero]

theorem c6_limb_tb {y e m : ℕ} (hy : (y >>> e) % 4 = 0) (hm : m < 4) (b : ℕ) :
    (y + m * 2 ^ e).testBit b =
      if b = e then m.testBit 0 else if b = e + 1 then m.testBit 1 else y.testBit b := by
  have hd : y = 2 ^ e * (y >>> e) + y % 2 ^ e := by
    rw [Nat.shiftRight_eq_div_pow]; exact (Nat.div_add_mod y (2 ^ e)).symm
  have h4 : (y >>> e) % 2 ^ 2 = 0 := by simpa using hy
  have e1 : y + m * 2 ^ e = 2 ^ e * ((y >>> e) + m) + y % 2 ^ e := by
    conv_lhs => rw [hd]
    ring
  rw [e1, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos e)), c6_tb_add h4 (by simpa using hm)]
  conv_rhs => rw [hd, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos e))]
  by_cases h1 : b < e
  · simp [h1, show b ≠ e by omega, show b ≠ e + 1 by omega]
  · by_cases h2 : b = e
    · subst h2; simp
    · by_cases h3 : b = e + 1
      · subst h3; simp
      · simp [h1, h2, h3, show ¬ (b - e < 2) by omega]

theorem c6_prod_two {N e : ℕ} (h : e + 1 < N) (g : ℕ → FE) :
    ∏ i ∈ Finset.range N, g i =
      g e * g (e + 1) * ∏ i ∈ Finset.range N, (if i = e ∨ i = e + 1 then 1 else g i) := by
  have hs : ∏ i ∈ Finset.range N, (if i = e ∨ i = e + 1 then g i else 1) = g e * g (e + 1) := by
    rw [← Finset.prod_filter]
    have : (Finset.range N).filter (fun i ↦ i = e ∨ i = e + 1) = {e, e + 1} := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [this, Finset.prod_pair (by omega)]
  rw [← hs, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _
  split_ifs <;> simp

theorem c6_limb_eqOn (r : Array FE) {N e y m : ℕ} (he : e + 1 < N) (hy : (y >>> e) % 4 = 0) (hm : m < 4) :
    ct_eqOn r (List.range N) (y + m * 2 ^ e) =
      eq1 (r.getD e 0) (m.testBit 0) * eq1 (r.getD (e + 1) 0) (m.testBit 1) *
        ct_eqOn r ((List.range N).filter fun b ↦ !(([] : List ℕ) ++ [e, e + 1]).contains b) y := by
  rw [c6_eqOn_range, c6_prod_two he, c6_eqOn_filter]
  simp only [c6_limb_tb hy hm, if_true, show e + 1 ≠ e by omega, if_false]
  congr 1
  apply Finset.prod_congr rfl; intro i _
  by_cases h1 : i = e
  · subst h1; simp
  · by_cases h2 : i = e + 1
    · subst h2; simp
    · simp [h1, h2]

/-- `ct_EL` split into the selector, the slot, the limb factor and the word off the limb bits. -/
theorem c6_EL_split (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (lim : Option ℕ) (o x y : ℕ)
    (ho : o < 4) (hx : x < 2 ^ xVars)
    (hl : ∀ e, lim = some e → e + 1 < yVars ∧ (y >>> e) % 4 = 0) :
    ct_EL pt lim o x y = eqW (sub (Pt.ofList pt).kap 0 2) o * ct_eqOn (Pt.ofList pt).rx (List.range xVars) x *
      kerVal (Pt.ofList pt) (ct_limFs [] lim) * ct_eqOn (Pt.ofList pt).ry (ct_yFree (ct_limYm [] lim)) y := by
  cases lim with
  | none =>
    have h1 : ct_yFree (ct_limYm [] none) = List.range yVars := by simp [ct_yFree, ct_limYm]
    have h2 : kerVal (Pt.ofList pt) (ct_limFs [] none) = 1 := rfl
    rw [ct_EL, ct_E_split pt hpt o x y ho hx, h1, h2, mul_one]
  | some e =>
    obtain ⟨he, hy⟩ := hl e rfl
    have hz : ct_yFree (ct_limYm [] (some e)) =
        (List.range yVars).filter fun b ↦ !(([] : List ℕ) ++ [e, e + 1]).contains b := rfl
    have key : ∀ m < 4, ct_E pt o x (y + m * 2 ^ e) =
        eqW (sub (Pt.ofList pt).kap 0 2) o * ct_eqOn (Pt.ofList pt).rx (List.range xVars) x *
          (eq1 ((Pt.ofList pt).ry.getD e 0) (m.testBit 0) * eq1 ((Pt.ofList pt).ry.getD (e + 1) 0) (m.testBit 1)) *
          ct_eqOn (Pt.ofList pt).ry (ct_yFree (ct_limYm [] (some e))) y := by
      intro m hm
      rw [ct_E_split pt hpt o x _ ho hx, c6_limb_eqOn _ he hy hm, hz]
      ring
    have k0 := key 0 (by norm_num); have k1 := key 1 (by norm_num); have k2 := key 2 (by norm_num)
    simp only [zero_mul, add_zero, one_mul] at k0 k1
    have hk : kerVal (Pt.ofList pt) (ct_limFs [] (some e)) =
        limbVal ((Pt.ofList pt).ry.getD e 0) ((Pt.ofList pt).ry.getD (e + 1) 0) := by
      rw [c6_kerVal]; simp [ct_limFs, kfVal]
    rw [ct_EL, k0, k1, k2, hk]
    have b0 : Nat.testBit 0 0 = false := by decide
    have b0' : Nat.testBit 0 1 = false := by decide
    have b1 : Nat.testBit 1 0 = true := by decide
    have b1' : Nat.testBit 1 1 = false := by decide
    have b2 : Nat.testBit 2 0 = false := by decide
    have b3 : Nat.testBit 2 1 = true := by decide
    simp only [limbVal, eq1, b0, b0', b1, b1', b2, b3, if_true, if_false, Bool.false_eq_true]
    ring

/-- **A point** atom. -/
theorem c6_point (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s) (o x y : ℕ)
    (w : FE) (lim : Option ℕ) (ho : o < 4) (hx : x < 2 ^ xVars)
    (hl : ∀ e, lim = some e → e + 1 < yVars ∧ (y >>> e) % 4 = 0) :
    ct_Adds pt s (s.addAtom [] o 0 x [] y w lim) (w * ct_EL pt lim o x y) := by
  refine ct_Adds_congr (ct_addAtom pt s hs [] o 0 x [] y w lim ho) ?_
  rw [c6_EL_split pt hpt lim o x y ho hx hl]
  have : ct_xFree 0 = List.range xVars := by simp [ct_xFree]
  rw [this]; ring

/-- **The points** of a term. -/
theorem c6_addPoints (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s) (t : CTerm)
    (lim : Option ℕ) (ht : TermWF t)
    (hl : ∀ e, lim = some e → e + 1 < yVars ∧ ∀ jf < 2 ^ t.l, (t.cls.at jf >>> e) % 4 = 0) :
    ct_Adds pt s (s.addPoints t lim)
      ((List.range (2 ^ t.l)).map fun jf ↦ t.w * ct_EL pt lim t.o (t.x0 + jf) (t.cls.at jf)).sum := by
  unfold CS.addPoints
  exact ct_Adds_foldl pt (fun s jf ↦ s.addAtom [] t.o 0 (t.x0 + jf) [] (t.cls.at jf) t.w lim) _
    (fun jf ↦ jf < 2 ^ t.l)
    (fun s jf hs hjf ↦ c6_point pt hpt s hs t.o _ _ t.w lim ht.1 (by have := ht.2.2; omega)
      (fun e he ↦ ⟨(hl e he).1, (hl e he).2 jf hjf⟩)) _ s hs (fun jf hjf ↦ List.mem_range.mp hjf)

theorem c6_eq1_sum (r : FE) : eq1 r false + eq1 r true = 1 := by simp [eq1]

theorem c6_prod_eq1_cube (r : Array FE) (a : ℕ) :
    ∑ j ∈ Finset.range (2 ^ a), ∏ i ∈ Finset.range a, eq1 (r.getD i 0) (j.testBit i) = 1 := by
  rw [c6_sum_prod_bits a (fun i b ↦ eq1 (r.getD i 0) b)]
  simp [c6_eq1_sum]

theorem c6_le_of_pow {a b c : ℕ} (h : c + 2 ^ a ≤ 2 ^ b) : a ≤ b := by
  have : 2 ^ a ≤ 2 ^ b := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

/-- The sub-cube `k0 + [0, 2^a)` of the slots: the fixed bits' factors times the high slot bits. -/
theorem c6_cubeX (P : Pt) (x0 l k0 a : ℕ) (hx : x0 % 2 ^ l = 0) (hxl : x0 + 2 ^ l ≤ 2 ^ xVars)
    (hk : k0 % 2 ^ a = 0) (hkl : k0 + 2 ^ a ≤ 2 ^ l) :
    ∑ j ∈ Finset.range (2 ^ a), ct_eqOn P.rx (List.range xVars) (x0 + (k0 + j)) =
      kerVal P (((List.range l).filter (fun x ↦ decide (x ≥ a))).map fun i ↦ KF.fixX i (k0.testBit i)) *
        ct_eqOn P.rx (ct_xFree l) x0 := by
  have hlx : l ≤ xVars := c6_le_of_pow hxl
  have hal : a ≤ l := c6_le_of_pow hkl
  have hfac : ∀ j < 2 ^ a, ct_eqOn P.rx (List.range xVars) (x0 + (k0 + j)) =
      (∏ i ∈ Finset.range xVars, if i < a then eq1 (P.rx.getD i 0) (j.testBit i) else 1) *
      ((∏ i ∈ Finset.range xVars, if i < l then (if decide (i ≥ a) = true then
          eq1 (P.rx.getD i 0) (k0.testBit i) else 1) else 1) *
        ∏ i ∈ Finset.range xVars, if (!decide (i < l)) = true then eq1 (P.rx.getD i 0) (x0.testBit i) else 1) := by
    intro j hj
    rw [c6_eqOn_range, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i _
    rw [c6_tb_add hx (by omega : k0 + j < 2 ^ l), c6_tb_add hk hj]
    by_cases h1 : i < a
    · simp [h1, show i < l by omega]
    · by_cases h2 : i < l
      · simp [h1, h2, show a ≤ i by omega]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j hj ↦ hfac j (Finset.mem_range.mp hj)), ← Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun j _ ↦ c6_prod_lt (show a ≤ xVars by omega) _), c6_prod_eq1_cube, one_mul,
    c6_prod_lt hlx, c6_kerVal, List.map_map, c6_lprod_filter, ct_xFree, c6_eqOn_filter]
  rfl

/-- **The halving recursion** of a term with varying weights. -/
theorem c6_go (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (t : CTerm) (ht : TermWF t) :
    ∀ (fuel k0 a : ℕ) (s : CS), ct_WF s → a < fuel → k0 % 2 ^ a = 0 → k0 + 2 ^ a ≤ 2 ^ t.l →
      ct_Adds pt s (CS.addVarying.go t fuel k0 a s)
        (∑ j ∈ Finset.range (2 ^ a), t.wAt (k0 + j) * ct_E pt t.o (t.x0 + (k0 + j)) (t.cls.at (k0 + j))) := by
  obtain ⟨ho, hx, hxl⟩ := ht
  intro fuel
  induction fuel with
  | zero => intro k0 a s _ ha; omega
  | succ fuel ih =>
    intro k0 a s hs ha hk hkl
    rw [CS.addVarying.go]
    simp only []
    by_cases hsame : (((List.range (2 ^ a)).all fun j ↦ t.cls.at (k0 + j) == t.cls.at k0 &&
        t.wAt (k0 + j) == t.wAt k0) || a == 0) = true
    · rw [if_pos hsame]
      -- word and weight are constant on the sub-cube
      have hconst : ∀ j < 2 ^ a, t.cls.at (k0 + j) = t.cls.at k0 ∧ t.wAt (k0 + j) = t.wAt k0 := by
        intro j hj
        rcases Bool.or_eq_true_iff.mp hsame with h | h
        · have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
          simp only [Bool.and_eq_true, beq_iff_eq] at this
          exact ⟨this.1, c6_FE_eq_of_beq this.2⟩
        · have ha0 : a = 0 := by simpa using h
          subst ha0
          have : j = 0 := by simpa using hj
          subst this; simp
      have hsum : (∑ j ∈ Finset.range (2 ^ a), t.wAt (k0 + j) * ct_E pt t.o (t.x0 + (k0 + j)) (t.cls.at (k0 + j))) =
          t.wAt k0 * ∑ j ∈ Finset.range (2 ^ a), ct_E pt t.o (t.x0 + (k0 + j)) (t.cls.at k0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j hj
        obtain ⟨h1, h2⟩ := hconst j (Finset.mem_range.mp hj)
        rw [h1, h2]
      rw [hsum]
      by_cases hw : (t.wAt k0 == 0) = true
      · rw [if_pos hw, c6_FE_eq_of_beq hw, zero_mul]
        exact ct_Adds_refl hs
      · rw [if_neg hw]
        by_cases ha0 : (a == 0) = true
        · rw [if_pos ha0]
          have ha0' : a = 0 := by simpa using ha0
          subst ha0'
          refine ct_Adds_congr (c6_point pt hpt s hs t.o (t.x0 + k0) (t.cls.at k0) (t.wAt k0) none ho
            (by omega) (fun e he ↦ by cases he)) ?_
          simp [ct_EL]
        · rw [if_neg ha0]
          refine ct_Adds_congr (ct_addAtom pt s hs _ t.o t.l t.x0 [] (t.cls.at k0) (t.wAt k0) none ho) ?_
          rw [Finset.sum_congr rfl (fun j hj ↦ ct_E_split pt hpt t.o (t.x0 + (k0 + j)) (t.cls.at k0) ho
            (by have := Finset.mem_range.mp hj; omega)), ← Finset.sum_mul, ← Finset.mul_sum,
            c6_cubeX _ t.x0 t.l k0 a hx hxl hk hkl]
          have h1 : ct_yFree (ct_limYm [] none) = List.range yVars := by simp [ct_yFree, ct_limYm]
          rw [h1]
          simp only [ct_limFs]
          ring
    · rw [if_neg hsame]
      have ha1 : a ≠ 0 := by
        intro h; apply hsame; simp [h]
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hk1 : k0 % 2 ^ b = 0 := by
        rw [pow_succ] at hk; exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.trans (Dvd.intro _ rfl) (Nat.dvd_of_mod_eq_zero hk))
      have hk2 : (k0 + 2 ^ b) % 2 ^ b = 0 := by rw [Nat.add_mod_right]; exact hk1
      have hp : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [pow_succ]; ring
      have A1 := ih k0 b s hs (by omega) hk1 (by omega)
      have A2 := ih (k0 + 2 ^ b) b _ A1.1 (by omega) hk2 (by omega)
      refine ct_Adds_congr (ct_Adds_trans A1 A2) ?_
      rw [hp, Finset.sum_range_add]
      congr 1
      apply Finset.sum_congr rfl; intro j _
      simp only [add_assoc]

/-! ## Splits -/

theorem c6_sum_swap {M : Type*} [AddCommMonoid M] {α : Type} (L : List α) (N : ℕ) (f : α → ℕ → M) :
    (L.map fun a ↦ ((List.range N).map (f a)).sum).sum =
      ((List.range N).map fun j ↦ (L.map fun a ↦ f a j).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, List.sum_map_add]

theorem c6_inFix_mem {fix : List (ℕ × Bool)} {jf : ℕ} (h : ct_inFix fix jf = true) :
    ∀ bv ∈ fix, jf.testBit bv.1 = bv.2 := by
  intro bv hbv
  have := List.all_eq_true.mp h bv hbv
  simpa using this

theorem c6_pw_eq {α : Type} (M : α → Bool) :
    ∀ (L : List α), L.Pairwise (fun a b ↦ ¬(M a = true ∧ M b = true)) →
      ∀ a ∈ L, ∀ b ∈ L, M a = true → M b = true → a = b := by
  intro L
  induction L with
  | nil => intro _ a ha; simp at ha
  | cons x L ih =>
    intro hp a ha b hb hma hmb
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd ⟨hma, hmb⟩ (hp.1 b hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd ⟨hmb, hma⟩ (hp.1 a ha')
      · exact ih hp.2 a ha' b hb' hma hmb

theorem c6_sum_find {α : Type} {M : Type*} [AddCommMonoid M] (P : α → Bool) (f : α → M) :
    ∀ (L : List α), L.Pairwise (fun a b ↦ ¬(P a = true ∧ P b = true)) → ∀ q, L.find? P = some q →
      (L.map fun a ↦ if P a = true then f a else 0).sum = f q := by
  intro L
  induction L with
  | nil => intro _ q hq; simp at hq
  | cons a L ih =>
    intro hp q hq
    rw [List.pairwise_cons] at hp
    by_cases ha : P a = true
    · rw [List.find?_cons_of_pos ha] at hq
      cases hq
      have h0 : (L.map fun a ↦ if P a = true then f a else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        have : ¬ P b = true := fun h ↦ hp.1 b hb ⟨ha, h⟩
        simp [this]
      simp [ha, h0]
    · rw [List.find?_cons_of_neg ha] at hq
      simp [ha, ih hp.2 q hq]

theorem c6_cnt_le {α : Type} (P : α → Bool) :
    ∀ (L : List α), L.Pairwise (fun a b ↦ ¬(P a = true ∧ P b = true)) →
      (L.map fun a ↦ if P a = true then (1 : ℕ) else 0).sum ≤ 1 := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a L ih =>
    intro hp
    rw [List.pairwise_cons] at hp
    by_cases ha : P a = true
    · have h0 : (L.map fun a ↦ if P a = true then (1 : ℕ) else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        have : ¬ P b = true := fun h ↦ hp.1 b hb ⟨ha, h⟩
        simp [this]
      simp [ha, h0]
    · simpa [ha] using ih hp.2

/-- The factor of bit `i` of the sub-cube's indicator. -/
def c6_g (fix : List (ℕ × Bool)) (i : ℕ) (b : Bool) : ℕ :=
  (fix.map fun bv ↦ if bv.1 = i then (if b = bv.2 then 1 else 0) else 1).prod

theorem c6_inFix_eq_prod (fix : List (ℕ × Bool)) (l : ℕ) (hfix : ∀ bv ∈ fix, bv.1 < l) (jf : ℕ) :
    (if ct_inFix fix jf = true then (1 : ℕ) else 0) = ∏ i ∈ Finset.range l, c6_g fix i (jf.testBit i) := by
  induction fix with
  | nil => simp [c6_g, ct_inFix]
  | cons bv fix ih =>
    have h1 : ∀ i b, c6_g (bv :: fix) i b =
        (if bv.1 = i then (if b = bv.2 then 1 else 0) else 1) * c6_g fix i b := by
      intro i b; simp [c6_g]
    simp only [h1, Finset.prod_mul_distrib, Finset.prod_ite_eq, Finset.mem_range, hfix bv (by simp), if_true]
    rw [← ih (fun b hb ↦ hfix b (by simp [hb]))]
    have hc : ct_inFix (bv :: fix) jf = ((jf.testBit bv.1 == bv.2) && ct_inFix fix jf) := rfl
    rw [hc]
    by_cases hA : jf.testBit bv.1 = bv.2 <;> cases h2' : ct_inFix fix jf <;> simp [hA]

theorem c6_g_one (fix : List (ℕ × Bool)) (i : ℕ) (b : Bool) (h : i ∉ fix.map (·.1)) : c6_g fix i b = 1 := by
  unfold c6_g
  apply List.prod_eq_one
  intro x hx
  obtain ⟨bv, hbv, rfl⟩ := List.mem_map.mp hx
  have : bv.1 ≠ i := fun e ↦ h (List.mem_map.mpr ⟨bv, hbv, e⟩)
  simp [this]

theorem c6_g_sum (fix : List (ℕ × Bool)) (hnd : (fix.map (·.1)).Nodup) (i : ℕ) :
    c6_g fix i false + c6_g fix i true = if i ∈ fix.map (·.1) then 1 else 2 := by
  induction fix with
  | nil => simp [c6_g]
  | cons bv fix ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have h1 : ∀ b, c6_g (bv :: fix) i b =
        (if bv.1 = i then (if b = bv.2 then 1 else 0) else 1) * c6_g fix i b := by
      intro b; simp [c6_g]
    rw [h1, h1]
    by_cases hb : bv.1 = i
    · subst hb
      rw [c6_g_one fix _ _ hnd.1, c6_g_one fix _ _ hnd.1]
      cases bv.2 <;> simp
    · simp only [hb, if_false, one_mul]
      rw [ih hnd.2]
      have : (i ∈ (bv :: fix).map (·.1)) ↔ i ∈ fix.map (·.1) := by
        simp only [List.map_cons, List.mem_cons]
        constructor
        · rintro (h | h)
          · exact absurd h.symm hb
          · exact h
        · exact Or.inr
      by_cases hi : i ∈ List.map (fun x ↦ x.1) fix
      · rw [if_pos hi, if_pos (this.mpr hi)]
      · rw [if_neg hi, if_neg (fun h ↦ hi (this.mp h))]

theorem c6_prod_two_pow (l : ℕ) (K : List ℕ) (hnd : K.Nodup) (hK : ∀ k ∈ K, k < l) :
    ∏ i ∈ Finset.range l, (if i ∈ K then (1 : ℕ) else 2) = 2 ^ (l - K.length) := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.range l) (fun i ↦ i ∈ K)
  have h2 : (Finset.range l).filter (fun i ↦ i ∈ K) = K.toFinset := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hK i h, h⟩⟩
  rw [h2, List.toFinset_card_of_nodup hnd, Finset.card_range] at h1
  omega

theorem c6_cube_card (fix : List (ℕ × Bool)) (l : ℕ) (hfix : ∀ bv ∈ fix, bv.1 < l)
    (hnd : (fix.map (·.1)).Nodup) :
    ∑ jf ∈ Finset.range (2 ^ l), (if ct_inFix fix jf = true then (1 : ℕ) else 0) = 2 ^ (l - fix.length) := by
  rw [Finset.sum_congr rfl (fun jf _ ↦ c6_inFix_eq_prod fix l hfix jf), c6_sum_prod_bits l (c6_g fix)]
  rw [Finset.prod_congr rfl (fun i _ ↦ c6_g_sum fix hnd i), c6_prod_two_pow l _ hnd, List.length_map]
  intro k hk
  obtain ⟨bv, hbv, rfl⟩ := List.mem_map.mp hk
  exact hfix bv hbv

theorem c6_all_one (N : ℕ) (f : ℕ → ℕ) (h1 : ∀ i < N, f i ≤ 1) (hs : ∑ i ∈ Finset.range N, f i = N) :
    ∀ i < N, f i = 1 := by
  intro i hi
  by_contra hne
  have hlt : ∑ j ∈ Finset.range N, f j < ∑ j ∈ Finset.range N, 1 :=
    Finset.sum_lt_sum (fun j hj ↦ h1 j (Finset.mem_range.mp hj))
      ⟨i, Finset.mem_range.mpr hi, by have := h1 i hi; omega⟩
  simp at hlt; omega

/-- **A split** whose parts are disjoint and cover the cube. -/
theorem c6_split (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s) (t : CTerm)
    (lim : Option ℕ) (ht : TermWF t) (parts : List (List (ℕ × Bool) × Aff)) (hc : t.cls = .split parts)
    (hok : splitOk t.l parts = true)
    (hL : ∀ e, lim = some e → e + 1 < yVars ∧ ∀ jf < 2 ^ t.l, (t.cls.at jf >>> e) % 4 = 0) :
    ct_Adds pt s (parts.foldl (fun s x ↦ s.addSub t.o t.w t.x0 (subAff t.l x.2 x.1) lim) s)
      ((List.range (2 ^ t.l)).map fun jf ↦ t.w * ct_EL pt lim t.o (t.x0 + jf) (t.cls.at jf)).sum := by
  simp only [splitOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne, ne_eq, Prod.exists] at hok
  obtain ⟨⟨hok1, hdisj⟩, hcov⟩ := hok
  have hpw : ∀ jf, parts.Pairwise (fun a b ↦ ¬(ct_inFix a.1 jf = true ∧ ct_inFix b.1 jf = true)) := by
    intro jf
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij ⟨hmi, hmj⟩
    obtain ⟨a, b, hab, a1, b1, hab1, he, hne⟩ := hdisj j hj i hij
    rw [List.getD_eq_getElem _ _ hj] at hab
    rw [List.getD_eq_getElem _ _ hi] at hab1
    have e1 := c6_inFix_mem hmj (a, b) hab
    have e2 := c6_inFix_mem hmi (a1, b1) hab1
    simp only at e1 e2
    subst he
    exact hne (e1.symm.trans e2)
  -- every iteration lies in exactly one part
  have hcnt : ∀ jf < 2 ^ t.l, (parts.map fun q ↦ if ct_inFix q.1 jf = true then (1 : ℕ) else 0).sum = 1 := by
    apply c6_all_one (2 ^ t.l) _ (fun jf _ ↦ c6_cnt_le _ parts (hpw jf))
    rw [← c6_lsum, ← c6_sum_swap]
    refine Eq.trans ?_ hcov
    congr 1
    apply List.map_congr_left; intro q hq
    rw [c6_lsum, c6_cube_card q.1 t.l (hok1 q hq).1 (hok1 q hq).2]
  have hfind : ∀ jf < 2 ^ t.l, ∃ q, parts.find? (fun q ↦ ct_inFix q.1 jf) = some q := by
    intro jf hjf
    cases h : parts.find? (fun q ↦ ct_inFix q.1 jf) with
    | some q => exact ⟨q, rfl⟩
    | none =>
      have h0 := List.find?_eq_none.mp h
      have : (parts.map fun q ↦ if ct_inFix q.1 jf = true then (1 : ℕ) else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        simp [h0 b hb]
      rw [hcnt jf hjf] at this; exact absurd this one_ne_zero
  have hat : ∀ pq ∈ parts, ∀ jf < 2 ^ t.l, ct_inFix pq.1 jf = true → t.cls.at jf = pq.2.at jf := by
    intro pq hpq jf hjf hm
    obtain ⟨q, hq⟩ := hfind jf hjf
    have hq' : parts.find? (fun q ↦ q.1.all fun bv ↦ jf.testBit bv.1 == bv.2) = some q := hq
    rw [hc]
    simp only [OpClass.at, hq']
    have hm' : ct_inFix q.1 jf = true := List.find?_some (p := fun (q : List (ℕ × Bool) × Aff) ↦ ct_inFix q.1 jf) hq
    rw [c6_pw_eq (fun q ↦ ct_inFix q.1 jf) parts (hpw jf) q (List.mem_of_find?_eq_some hq) pq hpq hm' hm]
  refine ct_Adds_congr (ct_Adds_foldl pt (fun s x ↦ s.addSub t.o t.w t.x0 (subAff t.l x.2 x.1) lim)
    (fun pq ↦ ((List.range (2 ^ t.l)).map fun jf ↦
      if ct_inFix pq.1 jf then t.w * ct_EL pt lim t.o (t.x0 + jf) (pq.2.at jf) else 0).sum)
    (fun pq ↦ pq ∈ parts) (fun s pq hs hpq ↦ ct_addSub pt hpt s hs t.o t.w t.x0 t.l pq.2 pq.1 lim ht.1 ht.2.1
      ht.2.2 (hok1 pq hpq) ?_) parts s hs (fun _ h ↦ h)) ?_
  · cases lim with
    | none => trivial
    | some e =>
      refine ⟨(hL e rfl).1, fun jf hjf hm ↦ ?_⟩
      rw [← hat pq hpq jf hjf hm]
      exact (hL e rfl).2 jf hjf
  · rw [c6_sum_swap]
    congr 1
    apply List.map_congr_left; intro jf hjf
    have hjf' := List.mem_range.mp hjf
    obtain ⟨q, hq⟩ := hfind jf hjf'
    have hm' : ct_inFix q.1 jf = true := List.find?_some (p := fun (q : List (ℕ × Bool) × Aff) ↦ ct_inFix q.1 jf) hq
    rw [c6_sum_find (fun pq ↦ ct_inFix pq.1 jf) (fun pq ↦ t.w * ct_EL pt lim t.o (t.x0 + jf) (pq.2.at jf))
      parts (hpw jf) q hq, hat q (List.mem_of_find?_eq_some hq) jf hjf' hm']

/-! ## Shifts -/

theorem c6_tbF (jf p n k : ℕ) : (jf / 2 ^ p % 2 ^ n).testBit k = (decide (k < n) && jf.testBit (k + p)) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem c6_F_zero (jf p n : ℕ) :
    jf / 2 ^ p % 2 ^ n = 0 ↔ ct_inFix ((List.range n).map fun k ↦ (p + k, false)) jf = true := by
  simp only [ct_inFix, List.all_map, List.all_eq_true, List.mem_range, Function.comp, beq_iff_eq]
  constructor
  · intro h k hk
    have := c6_tbF jf p n k
    rw [h, Nat.zero_testBit] at this
    simp only [hk, decide_true, Bool.true_and] at this
    rw [add_comm]; exact this.symm
  · intro h
    apply Nat.eq_of_testBit_eq; intro k
    rw [c6_tbF, Nat.zero_testBit]
    by_cases hk : k < n
    · simp only [hk, decide_true, Bool.true_and]; rw [add_comm]; exact h k hk
    · simp [hk]

theorem c6_sub_tb {jf p n : ℕ} (hF : jf / 2 ^ p % 2 ^ n ≠ 0) (i : ℕ) :
    (jf - 2 ^ p).testBit i =
      if p ≤ i ∧ i < p + n then (jf / 2 ^ p % 2 ^ n - 1).testBit (i - p) else jf.testBit i := by
  set F := jf / 2 ^ p % 2 ^ n with hFdef
  set H := jf / 2 ^ p / 2 ^ n
  set R := jf % 2 ^ p
  have hR : R < 2 ^ p := Nat.mod_lt _ (Nat.two_pow_pos p)
  have hFl : F < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have e0 : jf / 2 ^ p = 2 ^ n * H + F := (Nat.div_add_mod _ _).symm
  have e1 : jf = 2 ^ p * (2 ^ n * H + F) + R := by rw [← e0]; exact (Nat.div_add_mod _ _).symm
  have e2 : jf - 2 ^ p = 2 ^ p * (2 ^ n * H + (F - 1)) + R := by
    have : 2 ^ p * (2 ^ n * H + F) = 2 ^ p * (2 ^ n * H + (F - 1)) + 2 ^ p := by
      obtain ⟨F', hF'⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [hF', Nat.add_sub_cancel]; ring
    omega
  rw [e2, Nat.testBit_two_pow_mul_add _ hR, Nat.testBit_two_pow_mul_add _ (by omega : F - 1 < 2 ^ n)]
  conv_rhs => rw [e1, Nat.testBit_two_pow_mul_add _ hR, Nat.testBit_two_pow_mul_add _ hFl]
  by_cases h1 : i < p
  · simp [h1, show ¬ p ≤ i by omega]
  · by_cases h2 : i - p < n
    · simp [h1, h2, show p ≤ i ∧ i < p + n by omega]
    · simp [h1, h2, show ¬ (p ≤ i ∧ i < p + n) by omega]

theorem c6_sum_range_ext {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K N : ℕ) (hK : ∀ i, K ≤ i → f i = 0)
    (hN : ∀ i, N ≤ i → f i = 0) : ∑ i ∈ Finset.range K, f i = ∑ i ∈ Finset.range N, f i := by
  rcases le_total K N with h | h
  · exact Finset.sum_subset (Finset.range_subset_range.mpr h)
      (fun i _ hi ↦ hK i (by simpa using hi))
  · exact (Finset.sum_subset (Finset.range_subset_range.mpr h)
      (fun i _ hi ↦ hN i (by simpa using hi))).symm

theorem c6_at_eq (a : Aff) {jf N : ℕ} (h : jf < 2 ^ N) :
    a.at jf = a.y0 + ∑ i ∈ Finset.range N, if jf.testBit i then a.coef.getD i 0 else 0 := by
  rw [Aff.at, c6_lsum]
  congr 1
  apply c6_sum_range_ext
  · intro i hi; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  · intro i hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hi))]; rfl

theorem c6_cls_shift {t : CTerm} {p n : ℕ} {sh ini : Aff} (hc : t.cls = .shift p n sh ini) (jf : ℕ) :
    t.cls.at jf = if jf / 2 ^ p % 2 ^ n = 0 then ini.at jf else sh.at (jf - 2 ^ p) := by
  rw [hc]; rfl

theorem c6_shift_sum (pt : List FE) (t : CTerm) (lim : Option ℕ) {p n : ℕ} {sh ini : Aff}
    (hc : t.cls = .shift p n sh ini) :
    ((List.range (2 ^ t.l)).map fun jf ↦ t.w * ct_EL pt lim t.o (t.x0 + jf) (t.cls.at jf)).sum =
      ((List.range (2 ^ t.l)).map fun jf ↦
        if jf / 2 ^ p % 2 ^ n = 0 then t.w * ct_EL pt lim t.o (t.x0 + jf) (ini.at jf) else 0).sum +
      ((List.range (2 ^ t.l)).map fun jf ↦
        if jf / 2 ^ p % 2 ^ n = 0 then 0 else t.w * ct_EL pt lim t.o (t.x0 + jf) (sh.at (jf - 2 ^ p))).sum := by
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left; intro jf _
  rw [c6_cls_shift hc]
  split_ifs <;> simp

/-- K2's field-zero half. -/
theorem c6_shift0 (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s) (t : CTerm)
    (lim : Option ℕ) (ht : TermWF t) {p n : ℕ} {sh ini : Aff} (hc : t.cls = .shift p n sh ini)
    (hpn : p + n ≤ t.l)
    (hL : ∀ e, lim = some e → e + 1 < yVars ∧ ∀ jf < 2 ^ t.l, (t.cls.at jf >>> e) % 4 = 0) :
    ct_Adds pt s (s.addSub t.o t.w t.x0 (subAff t.l ini ((List.range n).map fun k ↦ (p + k, false))) lim)
      ((List.range (2 ^ t.l)).map fun jf ↦
        if jf / 2 ^ p % 2 ^ n = 0 then t.w * ct_EL pt lim t.o (t.x0 + jf) (ini.at jf) else 0).sum := by
  have hfix : (∀ bv ∈ (List.range n).map (fun k ↦ (p + k, false)), bv.1 < t.l) ∧
      (((List.range n).map (fun k ↦ (p + k, false))).map (·.1)).Nodup := by
    constructor
    · intro bv hbv
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hbv
      have := List.mem_range.mp hk; simp only; omega
    · rw [List.map_map]
      exact List.Nodup.map (fun a b h ↦ by simpa using h) List.nodup_range
  refine ct_Adds_congr (ct_addSub pt hpt s hs t.o t.w t.x0 t.l ini _ lim ht.1 ht.2.1 ht.2.2 hfix ?_) ?_
  · cases lim with
    | none => trivial
    | some e =>
      refine ⟨(hL e rfl).1, fun jf hjf hm ↦ ?_⟩
      have := (hL e rfl).2 jf hjf
      rwa [c6_cls_shift hc, if_pos ((c6_F_zero jf p n).mpr hm)] at this
  · congr 1
    apply List.map_congr_left; intro jf _
    by_cases h : jf / 2 ^ p % 2 ^ n = 0
    · rw [if_pos h, if_pos ((c6_F_zero jf p n).mp h)]
    · rw [if_neg h, if_neg (fun h' ↦ h ((c6_F_zero jf p n).mpr h'))]

/-- K2's shifted half with a one-bit field. -/
theorem c6_shift1 (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s) (t : CTerm)
    (lim : Option ℕ) (ht : TermWF t) {p : ℕ} {sh ini : Aff} (hc : t.cls = .shift p 1 sh ini)
    (hpn : p + 1 ≤ t.l)
    (hL : ∀ e, lim = some e → e + 1 < yVars ∧ ∀ jf < 2 ^ t.l, (t.cls.at jf >>> e) % 4 = 0) :
    ct_Adds pt s (s.addSub t.o t.w t.x0 (subAff t.l
        { y0 := sh.y0, coef := (List.range t.l).map fun i ↦ if (i == p) = true then 0 else sh.coef.getD i 0 }
        [(p, true)]) lim)
      ((List.range (2 ^ t.l)).map fun jf ↦
        if jf / 2 ^ p % 2 ^ 1 = 0 then 0 else t.w * ct_EL pt lim t.o (t.x0 + jf) (sh.at (jf - 2 ^ p))).sum := by
  have hF : ∀ jf, ct_inFix [(p, true)] jf = true ↔ ¬ jf / 2 ^ p % 2 ^ 1 = 0 := by
    intro jf
    rw [c6_F_zero]
    simp [ct_inFix]
  have hat : ∀ jf < 2 ^ t.l, ct_inFix [(p, true)] jf = true →
      Aff.at { y0 := sh.y0, coef := (List.range t.l).map fun i ↦ if (i == p) = true then 0 else sh.coef.getD i 0 } jf =
        sh.at (jf - 2 ^ p) := by
    intro jf hjf hm
    have hF1 := (hF jf).mp hm
    rw [c6_at_eq _ hjf, c6_at_eq sh (lt_of_le_of_lt (Nat.sub_le _ _) hjf)]
    congr 1
    apply Finset.sum_congr rfl; intro i hi
    have hi' := Finset.mem_range.mp hi
    have hF0 : jf / 2 ^ p % 2 ^ 1 - 1 = 0 := by
      have := Nat.mod_lt (jf / 2 ^ p) (show 2 ^ 1 > 0 by norm_num); omega
    by_cases hip : i = p
    · rw [c6_sub_tb hF1, if_pos (show p ≤ i ∧ i < p + 1 by omega), hF0, Nat.zero_testBit]
      subst hip
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi']
    · rw [c6_sub_tb hF1, if_neg (show ¬ (p ≤ i ∧ i < p + 1) by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi', hip]
  refine ct_Adds_congr (ct_addSub pt hpt s hs t.o t.w t.x0 t.l _ [(p, true)] lim ht.1 ht.2.1 ht.2.2
    ⟨by simpa using hpn, by simp⟩ ?_) ?_
  · cases lim with
    | none => trivial
    | some e =>
      refine ⟨(hL e rfl).1, fun jf hjf hm ↦ ?_⟩
      have := (hL e rfl).2 jf hjf
      rwa [c6_cls_shift hc, if_neg ((hF jf).mp hm), ← hat jf hjf hm] at this
  · congr 1
    apply List.map_congr_left; intro jf hjf
    have hjf' := List.mem_range.mp hjf
    by_cases h : ct_inFix [(p, true)] jf = true
    · rw [if_pos h, if_neg ((hF jf).mp h), hat jf hjf' h]
    · rw [if_neg h, if_pos (by by_contra h'; exact h ((hF jf).mpr h'))]

/-- K2's shifted half as points. -/
theorem c6_shiftPts (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s) (t : CTerm)
    (lim : Option ℕ) (ht : TermWF t) {p n : ℕ} {sh ini : Aff} (hc : t.cls = .shift p n sh ini)
    (hL : ∀ e, lim = some e → e + 1 < yVars ∧ ∀ jf < 2 ^ t.l, (t.cls.at jf >>> e) % 4 = 0) :
    ct_Adds pt s ((List.range (2 ^ t.l)).foldl (fun s jf ↦
          if (jf / 2 ^ p % 2 ^ n == 0) = true then s
          else s.addAtom [] t.o 0 (t.x0 + jf) [] (sh.at (jf - 2 ^ p)) t.w lim) s)
      ((List.range (2 ^ t.l)).map fun jf ↦
        if jf / 2 ^ p % 2 ^ n = 0 then 0 else t.w * ct_EL pt lim t.o (t.x0 + jf) (sh.at (jf - 2 ^ p))).sum := by
  refine ct_Adds_foldl pt _ _ (fun jf ↦ jf < 2 ^ t.l) (fun s jf hs hjf ↦ ?_) _ s hs
    (fun jf hjf ↦ List.mem_range.mp hjf)
  by_cases h : jf / 2 ^ p % 2 ^ n = 0
  · simp only [h, beq_self_eq_true, if_true]
    exact ct_Adds_refl hs
  · simp only [h, if_false, beq_iff_eq]
    refine c6_point pt hpt s hs t.o _ _ t.w lim ht.1 (by have := ht.2.2; omega) (fun e he ↦ ⟨(hL e he).1, ?_⟩)
    have := (hL e he).2 jf hjf
    rwa [c6_cls_shift hc, if_neg h] at this

/-! ## Injective affine words -/

theorem c6_tb_add_pow {x m : ℕ} (hx : x.testBit m = false) (b : ℕ) :
    (x + 2 ^ m).testBit b = (decide (b = m) || x.testBit b) := by
  have hd : x = 2 ^ m * (x / 2 ^ m) + x % 2 ^ m := (Nat.div_add_mod _ _).symm
  have hev : (x / 2 ^ m) % 2 = 0 := by
    have := Nat.testBit_div_two_pow (n := m) x 0
    rw [zero_add, hx, Nat.testBit_zero] at this
    simpa using this
  obtain ⟨h, hh⟩ : ∃ h, x / 2 ^ m = 2 * h := ⟨x / 2 ^ m / 2, by omega⟩
  have hR : x % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
  have e1 : x + 2 ^ m = 2 ^ m * (2 * h + 1) + x % 2 ^ m := by
    conv_lhs => rw [hd]
    rw [hh]; ring
  have e2 : x = 2 ^ m * (2 * h) + x % 2 ^ m := by
    conv_lhs => rw [hd]
    rw [hh]
  rw [e1, Nat.testBit_two_pow_mul_add _ hR]
  conv_rhs => rw [e2, Nat.testBit_two_pow_mul_add _ hR]
  by_cases h1 : b < m
  · simp [h1, show b ≠ m by omega]
  · obtain ⟨k, hk⟩ : ∃ k, b - m = k := ⟨_, rfl⟩
    rw [hk]
    cases k with
    | zero =>
      have : b = m := by omega
      simp [this, Nat.testBit_zero]
    | succ k =>
      rw [Nat.testBit_add_one, Nat.testBit_add_one, show (2 * h + 1) / 2 = h by omega,
        show 2 * h / 2 = h by omega]
      simp [h1, show b ≠ m by omega]

theorem c6_pow2 {c : ℕ} (h : isPow2 c = true) : c = 2 ^ log2 c := by
  simp only [isPow2, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨h0, h1⟩ := h
  have hle := Nat.log2_self_le h0
  have hlt := Nat.lt_log2_self (n := c)
  unfold log2
  by_contra hne
  have hk : ∀ x, 2 ^ c.log2 ≤ x → x < 2 ^ (c.log2 + 1) → x.testBit c.log2 = true := by
    intro x h1 h2
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt_le (k := 1) (by simpa using h1) (by rw [pow_succ] at h2; omega)]
    rfl
  have := congrArg (fun z ↦ z.testBit c.log2) h1
  simp only [Nat.testBit_and, Nat.zero_testBit] at this
  rw [hk c hle hlt, hk (c - 1) (by omega) (by omega)] at this
  exact absurd this (by decide)

theorem c6_injOk_cons (u c : ℕ) (cs : List ℕ) :
    injOk u (c :: cs) =
      if c = 0 then injOk u cs else if isPow2 c = true ∧ u &&& c = 0 then injOk (u ||| c) cs else false := by
  have hnone : ∀ cs : List ℕ, (cs.foldl (fun (acc : Option ℕ) c ↦ acc.bind fun u ↦
      if c == 0 then some u else if isPow2 c && u &&& c == 0 then some (u ||| c) else none) none) = none := by
    intro cs
    induction cs with
    | nil => rfl
    | cons c cs ih => simpa using ih
  unfold injOk
  rw [List.foldl_cons]
  by_cases h0 : c = 0
  · simp [h0]
  · by_cases h1 : isPow2 c = true ∧ u &&& c = 0
    · simp [h0, h1]
    · rw [if_neg h0, if_neg h1]
      have : (some u).bind (fun u ↦ if c == 0 then some u else if isPow2 c && u &&& c == 0 then some (u ||| c)
          else none) = none := by
        simp only [Option.bind_some, beq_iff_eq, h0, if_false, Bool.and_eq_true]
        rw [if_neg h1]
      rw [this, hnone]; rfl

theorem c6_inj_props : ∀ (cs : List ℕ) (u : ℕ), injOk u cs = true →
    ∀ c ∈ cs, c ≠ 0 → isPow2 c = true ∧ u &&& c = 0 := by
  intro cs
  induction cs with
  | nil => intro u _ c hc; simp at hc
  | cons c' cs ih =>
    intro u h c hc hc0
    rw [c6_injOk_cons] at h
    by_cases h0 : c' = 0
    · rw [if_pos h0] at h
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact absurd h0 hc0
      · exact ih u h c hc' hc0
    · rw [if_neg h0] at h
      by_cases h1 : isPow2 c' = true ∧ u &&& c' = 0
      · rw [if_pos h1] at h
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact h1
        · obtain ⟨hp, ha⟩ := ih _ h c hc' hc0
          refine ⟨hp, Nat.eq_of_testBit_eq fun i ↦ ?_⟩
          have := congrArg (fun z ↦ z.testBit i) ha
          simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at this ⊢
          cases h2 : u.testBit i <;> cases h3 : c.testBit i <;> simp_all
      · rw [if_neg h1] at h; exact absurd h (by simp)

theorem c6_tb_add_ite {x m : ℕ} (hx : x.testBit m = false) (β : Bool) (b : ℕ) :
    (x + if β = true then 2 ^ m else 0).testBit b = ((β && decide (b = m)) || x.testBit b) := by
  cases β
  · simp
  · simp [c6_tb_add_pow hx]

theorem c6_eqOn_cons (r : Array FE) (b : ℕ) (Z : List ℕ) (v : ℕ) :
    ct_eqOn r (b :: Z) v = eq1 (r.getD b 0) (v.testBit b) * ct_eqOn r Z v := by
  simp [ct_eqOn]

/-- **The `eq` of an injective affine word**: the bits hit by a coefficient are the selector bits. -/
theorem c6_inj_eqOn (r : Array FE) : ∀ (L : List (ℕ × Bool)) (u u' : ℕ) (Z : List ℕ),
    injOk u (L.map (·.1)) = true → Z.Nodup → (∀ b, u'.testBit b = true → u.testBit b = true) →
    ct_eqOn r Z (u' + (L.map fun cb ↦ if cb.2 = true then cb.1 else 0).sum) =
      ct_eqOn r (Z.filter fun b ↦ !((L.map (·.1)).any (· == 2 ^ b))) u' *
        (L.map fun cb ↦ if cb.1 ≠ 0 ∧ log2 cb.1 ∈ Z then eq1 (r.getD (log2 cb.1) 0) cb.2 else 1).prod := by
  intro L
  induction L with
  | nil => intro u u' Z _ _ _; simp
  | cons cb L ih =>
    obtain ⟨c, β⟩ := cb
    intro u u' Z hinj hnd hsub
    simp only [List.map_cons] at hinj
    rw [c6_injOk_cons] at hinj
    simp only [List.map_cons, List.sum_cons, List.prod_cons, List.any_cons]
    by_cases h0 : c = 0
    · subst h0
      rw [if_pos rfl] at hinj
      have hf : ∀ b : ℕ, ((0 == 2 ^ b) || (L.map (·.1)).any (· == 2 ^ b)) = (L.map (·.1)).any (· == 2 ^ b) := by
        intro b
        have : (0 == 2 ^ b) = false := by
          rw [beq_eq_false_iff_ne]; exact (Nat.two_pow_pos b).ne
        rw [this, Bool.false_or]
      simp only [hf, ite_self, zero_add, ne_eq, not_true, false_and, if_false, one_mul]
      exact ih u u' Z hinj hnd hsub
    · rw [if_neg h0] at hinj
      by_cases h1 : isPow2 c = true ∧ u &&& c = 0
      · rw [if_pos h1] at hinj
        have hcm : c = 2 ^ log2 c := c6_pow2 h1.1
        set m := log2 c with hm
        have hum : u.testBit m = false := by
          have := congrArg (fun z ↦ z.testBit m) h1.2
          simpa [hcm, Nat.testBit_two_pow_self] using this
        have hu'm : u'.testBit m = false := by
          cases h : u'.testBit m
          · rfl
          · rw [hsub m h] at hum; exact absurd hum (by decide)
        have hsub' : ∀ b, (u' + if β = true then c else 0).testBit b = true → (u ||| c).testBit b = true := by
          intro b hb
          rw [hcm, c6_tb_add_ite hu'm] at hb
          rw [Nat.testBit_or, hcm, Nat.testBit_two_pow]
          rcases Bool.or_eq_true_iff.mp hb with h | h
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            simp [h.2]
          · simp [hsub b h]
        have hrest : ∀ b, (L.map (·.1)).any (· == 2 ^ b) = true → b ≠ m := by
          intro b hb hbm
          obtain ⟨c', hc', he⟩ := List.any_eq_true.mp hb
          rw [beq_iff_eq] at he
          have := (c6_inj_props _ _ hinj c' hc' (by rw [he]; exact (Nat.two_pow_pos b).ne')).2
          have := congrArg (fun z ↦ z.testBit m) this
          simp [he, hbm, Nat.testBit_two_pow_self, hcm] at this
        rw [← add_assoc, ih (u ||| c) _ Z hinj hnd hsub']
        have hfl : (Z.filter fun b ↦ !((c == 2 ^ b) || (L.map (·.1)).any (· == 2 ^ b))) =
            (Z.filter fun b ↦ !((L.map (·.1)).any (· == 2 ^ b))).filter fun b ↦ b != m := by
          rw [List.filter_filter]
          apply List.filter_congr; intro b _
          have : (c == 2 ^ b) = (b == m) := by
            rw [hcm]
            cases h : (b == m)
            · rw [beq_eq_false_iff_ne]; intro h'
              have := Nat.pow_right_injective (le_refl 2) h'
              rw [beq_eq_false_iff_ne] at h; exact h this.symm
            · rw [beq_iff_eq] at h; rw [h]; simp
          rw [this]
          cases h : (b == m) <;> simp only [bne, h, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or,
            Bool.true_and, Bool.false_and]
        rw [hfl]
        set Zr := Z.filter fun b ↦ !((L.map (·.1)).any (· == 2 ^ b))
        have hndr : Zr.Nodup := hnd.filter _
        have hoff : ∀ b ∈ Zr.filter (fun b ↦ b != m), (u' + if β = true then c else 0).testBit b = u'.testBit b := by
          intro b hb
          have : b ≠ m := by simpa using (List.mem_filter.mp hb).2
          rw [hcm, c6_tb_add_ite hu'm]; simp [this]
        by_cases hmZ : m ∈ Z
        · have hmZr : m ∈ Zr := by
            refine List.mem_filter.mpr ⟨hmZ, ?_⟩
            cases h : (L.map (·.1)).any (· == 2 ^ m)
            · rfl
            · exact absurd rfl (hrest m h)
          rw [ct_eqOn_perm r (List.perm_cons_erase hmZr), c6_eqOn_cons, hndr.erase_eq_filter,
            ct_eqOn_congr r _ _ _ hoff]
          rw [if_pos (show c ≠ 0 ∧ m ∈ Z from ⟨h0, hmZ⟩)]
          have : (u' + if β = true then c else 0).testBit m = β := by
            rw [hcm, c6_tb_add_ite hu'm]; simp [hu'm]
          rw [this]; ring
        · rw [if_neg (show ¬ (c ≠ 0 ∧ m ∈ Z) from fun h ↦ hmZ h.2), one_mul]
          have hself : Zr.filter (fun b ↦ b != m) = Zr := by
            apply List.filter_eq_self.mpr
            intro b hb
            have : b ≠ m := fun h ↦ hmZ (h ▸ (List.mem_filter.mp hb).1)
            simpa using this
          rw [hself] at hoff ⊢
          rw [ct_eqOn_congr r _ _ _ hoff]
      · rw [if_neg h1] at hinj; exact absurd hinj (by simp)

/-- A hit bit of an injective affine word is set. -/
theorem c6_inj_tb : ∀ (L : List (ℕ × Bool)) (u u' b : ℕ),
    injOk u (L.map (·.1)) = true → (∀ b, u'.testBit b = true → u.testBit b = true) →
    (u'.testBit b = true ∨ (2 ^ b, true) ∈ L) →
    (u' + (L.map fun cb ↦ if cb.2 = true then cb.1 else 0).sum).testBit b = true := by
  intro L
  induction L with
  | nil => intro u u' b _ _ h; simpa using h
  | cons cb L ih =>
    obtain ⟨c, β⟩ := cb
    intro u u' b hinj hsub hb
    simp only [List.map_cons] at hinj
    rw [c6_injOk_cons] at hinj
    simp only [List.map_cons, List.sum_cons]
    by_cases h0 : c = 0
    · subst h0
      rw [if_pos rfl] at hinj
      simp only [ite_self, zero_add]
      refine ih u u' b hinj hsub ?_
      rcases hb with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h | h
        · simp only [Prod.mk.injEq] at h; exact absurd h.1 (Nat.two_pow_pos b).ne'
        · exact Or.inr h
    · rw [if_neg h0] at hinj
      by_cases h1 : isPow2 c = true ∧ u &&& c = 0
      · rw [if_pos h1] at hinj
        have hcm : c = 2 ^ log2 c := c6_pow2 h1.1
        set m := log2 c with hm
        have hum : u.testBit m = false := by
          have := congrArg (fun z ↦ z.testBit m) h1.2
          simpa [hcm, Nat.testBit_two_pow_self] using this
        have hu'm : u'.testBit m = false := by
          cases h : u'.testBit m
          · rfl
          · rw [hsub m h] at hum; exact absurd hum (by decide)
        have hsub' : ∀ b, (u' + if β = true then c else 0).testBit b = true → (u ||| c).testBit b = true := by
          intro b hb
          rw [hcm, c6_tb_add_ite hu'm] at hb
          rw [Nat.testBit_or, hcm, Nat.testBit_two_pow]
          rcases Bool.or_eq_true_iff.mp hb with h | h
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            simp [h.2]
          · simp [hsub b h]
        rw [← add_assoc]
        refine ih (u ||| c) _ b hinj hsub' ?_
        rw [hcm, c6_tb_add_ite hu'm]
        rcases hb with h | h
        · left; simp [h]
        · rcases List.mem_cons.mp h with h | h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨h2, rfl⟩ := h
            left
            rw [hcm] at h2
            have := Nat.pow_right_injective (le_refl 2) h2
            simp [this]
          · exact Or.inr h
      · rw [if_neg h1] at hinj; exact absurd hinj (by simp)

/-! ## The shifted field's sum -/

theorem c6_prod_field {M : Type*} [CommMonoid M] {p n l : ℕ} (h : p + n ≤ l) (g : ℕ → M) :
    ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then g i else 1) = ∏ k ∈ Finset.range n, g (p + k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.prod_range_add, Finset.prod_range_add]
  rw [Finset.prod_congr rfl (fun i hi ↦ if_neg (by have := Finset.mem_range.mp hi; omega :
      ¬ (p ≤ i ∧ i < p + n))),
    Finset.prod_congr rfl (fun i hi ↦ if_pos (by have := Finset.mem_range.mp hi; omega :
      (p ≤ p + i ∧ p + i < p + n))),
    Finset.prod_congr rfl (fun i _ ↦ if_neg (by omega : ¬ (p ≤ p + n + i ∧ p + n + i < p + n)))]
  simp

theorem c6_sum_field {M : Type*} [AddCommMonoid M] {p n l : ℕ} (h : p + n ≤ l) (g : ℕ → M) :
    ∑ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then g i else 0) = ∑ k ∈ Finset.range n, g (p + k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.sum_range_add, Finset.sum_range_add]
  rw [Finset.sum_congr rfl (fun i hi ↦ if_neg (by have := Finset.mem_range.mp hi; omega :
      ¬ (p ≤ i ∧ i < p + n))),
    Finset.sum_congr rfl (fun i hi ↦ if_pos (by have := Finset.mem_range.mp hi; omega :
      (p ≤ p + i ∧ p + i < p + n))),
    Finset.sum_congr rfl (fun i _ ↦ if_neg (by omega : ¬ (p ≤ p + n + i ∧ p + n + i < p + n)))]
  simp

theorem c6_indic (jf p n l : ℕ) (h : p + n ≤ l) (u : ℕ) (hu : u < 2 ^ n) :
    ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then
        (if jf.testBit i = u.testBit (i - p) then (1 : FE) else 0) else 1) =
      if jf / 2 ^ p % 2 ^ n = u then 1 else 0 := by
  rw [c6_prod_field h]
  simp only [Nat.add_sub_cancel_left]
  rw [Finset.prod_boole]
  have hiff : (∀ k ∈ Finset.range n, jf.testBit (p + k) = u.testBit k) ↔ jf / 2 ^ p % 2 ^ n = u := by
    constructor
    · intro hk
      apply Nat.eq_of_testBit_eq; intro k
      rw [c6_tbF]
      by_cases hkn : k < n
      · simp only [hkn, decide_true, Bool.true_and]; rw [add_comm]; exact hk k (Finset.mem_range.mpr hkn)
      · simp only [hkn, decide_false, Bool.false_and]
        exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
    · rintro rfl k hk
      rw [c6_tbF]; simp [Finset.mem_range.mp hk, add_comm]
  simp only [hiff]

/-- **The field's sum**: the indicator of the field value expanded into one-bit factors. -/
theorem c6_engine {p n l : ℕ} (h : p + n ≤ l) (A : ℕ → FE) (gg : ℕ → Bool → FE) :
    ∑ jf ∈ Finset.range (2 ^ l), A (jf / 2 ^ p % 2 ^ n) *
        ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then 1 else gg i (jf.testBit i)) =
      (∑ u ∈ Finset.range (2 ^ n), A u) *
        ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then 1 else gg i false + gg i true) := by
  have hA : ∀ jf, A (jf / 2 ^ p % 2 ^ n) = ∑ u ∈ Finset.range (2 ^ n), A u *
      ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then
        (if jf.testBit i = u.testBit (i - p) then (1 : FE) else 0) else 1) := by
    intro jf
    rw [Finset.sum_congr rfl (fun u hu ↦ by rw [c6_indic jf p n l h u (Finset.mem_range.mp hu)])]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos n)))]
  simp only [hA, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun jf _ ↦ (Finset.prod_mul_distrib).symm)]
  rw [c6_sum_prod_bits l (fun i b ↦ (if p ≤ i ∧ i < p + n then (if b = u.testBit (i - p) then (1 : FE) else 0)
    else 1) * (if p ≤ i ∧ i < p + n then 1 else gg i b))]
  apply Finset.prod_congr rfl; intro i _
  by_cases h1 : p ≤ i ∧ i < p + n
  · simp only [h1, and_self, if_true, mul_one]
    cases u.testBit (i - p) <;> simp
  · simp only [h1, if_false, one_mul]

/-! ## K2's successor atom -/

theorem c6_shiftOk_dec {l p n q : ℕ} {sh : Aff} {others : List (ℕ × ℕ)}
    (hso : shiftOk l p n sh = some (q, others)) :
    (∀ k < n, sh.coef.getD (p + k) 0 = 2 ^ (q + k)) ∧ q + n ≤ yVars ∧
      others = ((List.range l).filter (fun i ↦ decide (i < p) || decide (i ≥ p + n))).map
        (fun i ↦ (i, sh.coef.getD i 0)) ∧
      injOk sh.y0 (others.map (·.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)) = true := by
  unfold shiftOk at hso
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, beq_iff_eq] at hso
  split_ifs at hso with h1 h2
  simp only [Option.some.injEq, Prod.mk.injEq] at hso
  obtain ⟨rfl, rfl⟩ := hso
  exact ⟨h2.1.1, h2.1.2, rfl, h2.2⟩

/-- The selectors of the shifted word: the other bits of `jf`, then the field value `v` (`= F − 1`). -/
def c6_Lw (others : List (ℕ × ℕ)) (q n jf v : ℕ) : List (ℕ × Bool) :=
  others.map (fun x ↦ (x.2, jf.testBit x.1)) ++ (List.range n).map fun k ↦ (2 ^ (q + k), v.testBit k)

theorem c6_Lw_fst (others : List (ℕ × ℕ)) (q n jf v : ℕ) :
    (c6_Lw others q n jf v).map (·.1) = others.map (·.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k) := by
  simp [c6_Lw, Function.comp_def]

theorem c6_Y_eq {l p n q : ℕ} {sh : Aff} {others : List (ℕ × ℕ)} (hpn : p + n ≤ l)
    (hfield : ∀ k < n, sh.coef.getD (p + k) 0 = 2 ^ (q + k))
    (hoth : others = ((List.range l).filter (fun i ↦ decide (i < p) || decide (i ≥ p + n))).map
        (fun i ↦ (i, sh.coef.getD i 0)))
    {jf : ℕ} (hjf : jf < 2 ^ l) (hF : jf / 2 ^ p % 2 ^ n ≠ 0) :
    sh.at (jf - 2 ^ p) = sh.y0 + ((c6_Lw others q n jf (jf / 2 ^ p % 2 ^ n - 1)).map
      fun cb ↦ if cb.2 = true then cb.1 else 0).sum := by
  rw [c6_at_eq sh (lt_of_le_of_lt (Nat.sub_le _ _) hjf)]
  congr 1
  rw [c6_Lw, List.map_append, List.sum_append, hoth, List.map_map, List.map_map, c6_lsum_filter, List.map_map,
    c6_lsum]
  simp only [Function.comp_def]
  have hfs : (∑ k ∈ Finset.range n, if (jf / 2 ^ p % 2 ^ n - 1).testBit k = true then 2 ^ (q + k) else 0) =
      ∑ i ∈ Finset.range l, if p ≤ i ∧ i < p + n then
        (if (jf / 2 ^ p % 2 ^ n - 1).testBit (i - p) = true then 2 ^ (q + (i - p)) else 0) else 0 := by
    rw [c6_sum_field hpn]; simp
  rw [hfs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [c6_sub_tb hF]
  by_cases h1 : p ≤ i ∧ i < p + n
  · have hO : (decide (i < p) || decide (i ≥ p + n)) = false := by simp; omega
    simp only [h1, and_self, if_true, hO, Bool.false_eq_true, if_false, zero_add]
    have := hfield (i - p) (by omega)
    rw [show p + (i - p) = i by omega] at this
    rw [this]
  · have hO : (decide (i < p) || decide (i ≥ p + n)) = true := by simp; omega
    simp only [h1, if_false, hO, if_true, add_zero]

theorem c6_avoid {Y e b : ℕ} (hY : (Y >>> e) % 4 = 0) (hb : Y.testBit b = true) : b ≠ e ∧ b ≠ e + 1 := by
  have key : ∀ j < 2, Y.testBit (e + j) = false := by
    intro j hj
    have h1 : (Y >>> e % 2 ^ 2).testBit j = (Y >>> e).testBit j := by
      rw [Nat.testBit_mod_two_pow]; simp [hj]
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hY, Nat.zero_testBit, Nat.testBit_shiftRight] at h1
    exact h1.symm
  constructor
  · intro h; subst h; have := key 0 (by norm_num); simp at this; rw [this] at hb; exact absurd hb (by decide)
  · intro h; subst h; have := key 1 (by norm_num); rw [this] at hb; exact absurd hb (by decide)

theorem c6_mem_yFree {ym : List ℕ} {b : ℕ} : b ∈ ct_yFree ym ↔ b < yVars ∧ b ∉ ym := by
  simp [ct_yFree]

theorem c6_mem_Z {lim : Option ℕ} {b : ℕ} :
    b ∈ ct_yFree (ct_limYm [] lim) ↔ b < yVars ∧ ∀ e, lim = some e → b ≠ e ∧ b ≠ e + 1 := by
  rw [c6_mem_yFree]
  cases lim with
  | none => simp [ct_limYm]
  | some e => simp [ct_limYm]

theorem c6_two_pow_lt {k n : ℕ} (hk : k < n) (hn : 2 ≤ n) : 2 ^ k + 1 < 2 ^ n := by
  have h1 : 2 ^ k ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have h3 : 2 ≤ 2 ^ (n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The field's `y` bits avoid the limb bits. -/
theorem c6_qZ {l p n q : ℕ} {sh : Aff} {others : List (ℕ × ℕ)} {lim : Option ℕ} (hpn : p + n ≤ l) (hn : 2 ≤ n)
    (hfield : ∀ k < n, sh.coef.getD (p + k) 0 = 2 ^ (q + k)) (hqn : q + n ≤ yVars)
    (hoth : others = ((List.range l).filter (fun i ↦ decide (i < p) || decide (i ≥ p + n))).map
        (fun i ↦ (i, sh.coef.getD i 0)))
    (hinj : injOk sh.y0 (others.map (·.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)) = true)
    (hlimbY : ∀ e, lim = some e → ∀ jf < 2 ^ l, jf / 2 ^ p % 2 ^ n ≠ 0 → (sh.at (jf - 2 ^ p) >>> e) % 4 = 0) :
    ∀ k < n, q + k ∈ ct_yFree (ct_limYm [] lim) := by
  intro k hk
  rw [c6_mem_Z]
  refine ⟨by omega, fun e he ↦ ?_⟩
  have h2k := c6_two_pow_lt hk hn
  have hF0 : 2 ^ p * (2 ^ k + 1) / 2 ^ p % 2 ^ n = 2 ^ k + 1 := by
    rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos p), Nat.mod_eq_of_lt h2k]
  have hjf0 : 2 ^ p * (2 ^ k + 1) < 2 ^ l := by
    calc 2 ^ p * (2 ^ k + 1) < 2 ^ p * 2 ^ n := Nat.mul_lt_mul_of_pos_left h2k (Nat.two_pow_pos p)
      _ = 2 ^ (p + n) := (pow_add 2 p n).symm
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hpn
  have hFne : 2 ^ p * (2 ^ k + 1) / 2 ^ p % 2 ^ n ≠ 0 := by rw [hF0]; exact Nat.succ_ne_zero _
  have htb : (sh.at (2 ^ p * (2 ^ k + 1) - 2 ^ p)).testBit (q + k) = true := by
    rw [c6_Y_eq hpn hfield hoth hjf0 hFne]
    apply c6_inj_tb _ sh.y0 sh.y0 _ (by rw [c6_Lw_fst]; exact hinj) (fun _ h ↦ h)
    right
    rw [c6_Lw]
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, by rw [hF0]; simp [Nat.testBit_two_pow_self]⟩
  exact c6_avoid (hlimbY e he _ hjf0 hFne) htb

/-- The paired `y` bits avoid the limb bits. -/
theorem c6_pZ {l p n q : ℕ} {sh : Aff} {others : List (ℕ × ℕ)} {lim : Option ℕ} (hpn : p + n ≤ l) (hn : 2 ≤ n)
    (hfield : ∀ k < n, sh.coef.getD (p + k) 0 = 2 ^ (q + k))
    (hoth : others = ((List.range l).filter (fun i ↦ decide (i < p) || decide (i ≥ p + n))).map
        (fun i ↦ (i, sh.coef.getD i 0)))
    (hinj : injOk sh.y0 (others.map (·.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)) = true)
    (hlimbY : ∀ e, lim = some e → ∀ jf < 2 ^ l, jf / 2 ^ p % 2 ^ n ≠ 0 → (sh.at (jf - 2 ^ p) >>> e) % 4 = 0) :
    ∀ x ∈ others, x.2 ≠ 0 → log2 x.2 < yVars → log2 x.2 ∈ ct_yFree (ct_limYm [] lim) := by
  intro x hx hx0 hxy
  rw [c6_mem_Z]
  refine ⟨hxy, fun e he ↦ ?_⟩
  have hx' := hx
  rw [hoth] at hx'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
  obtain ⟨hil, hO⟩ := List.mem_filter.mp hi
  have hil' := List.mem_range.mp hil
  have hip : i ≠ p := by intro h; subst h; simp at hO; omega
  simp only at hx0 hxy ⊢
  have hc2 : sh.coef.getD i 0 = 2 ^ log2 (sh.coef.getD i 0) :=
    c6_pow2 (c6_inj_props _ _ hinj _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, hx, rfl⟩)) hx0).1
  have hpi : (2 ^ i).testBit p = false := by rw [Nat.testBit_two_pow]; simpa using hip
  have htbj : ∀ b, (2 ^ i + 2 ^ p).testBit b = (decide (b = p) || decide (i = b)) := by
    intro b; rw [c6_tb_add_pow hpi, Nat.testBit_two_pow]
  have hjf0 : 2 ^ i + 2 ^ p < 2 ^ l := by
    rcases Nat.lt_or_gt_of_ne hip with h | h
    · have h1 : 2 ^ i < 2 ^ p := Nat.pow_lt_pow_right (by norm_num) h
      have h2 : 2 ^ (p + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at h2; omega
    · have h1 : 2 ^ p < 2 ^ i := Nat.pow_lt_pow_right (by norm_num) h
      have h2 : 2 ^ (i + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at h2; omega
  have hFne : (2 ^ i + 2 ^ p) / 2 ^ p % 2 ^ n ≠ 0 := by
    intro h
    have := c6_tbF (2 ^ i + 2 ^ p) p n 0
    rw [h, Nat.zero_testBit, htbj] at this
    simp at this; omega
  have htb : (sh.at (2 ^ i + 2 ^ p - 2 ^ p)).testBit (log2 (sh.coef.getD i 0)) = true := by
    rw [c6_Y_eq hpn hfield hoth hjf0 hFne]
    apply c6_inj_tb _ sh.y0 sh.y0 _ (by rw [c6_Lw_fst]; exact hinj) (fun _ h ↦ h)
    right
    rw [c6_Lw]
    apply List.mem_append_left
    refine List.mem_map.mpr ⟨(i, sh.coef.getD i 0), hx, ?_⟩
    simp only [htbj, decide_true, Bool.or_true]
    rw [← hc2]
  exact c6_avoid (hlimbY e he _ hjf0 hFne) htb

theorem c6_ym_iff {n q : ℕ} {sh : Aff} {others : List (ℕ × ℕ)}
    (hinj : injOk sh.y0 (others.map (·.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)) = true)
    {b : ℕ} (hb : b < yVars) :
    b ∈ (List.range n).map (fun x ↦ q + x) ++ (others.filter fun x ↦ x.2 != 0 && decide (log2 x.2 < yVars)).map
        (fun x ↦ log2 x.2) ↔ 2 ^ b ∈ others.map (·.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k) := by
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_filter, Bool.and_eq_true, bne_iff_ne,
    ne_eq, decide_eq_true_eq]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨x, ⟨hx, hx0, hxy⟩, rfl⟩)
    · exact Or.inr ⟨k, hk, rfl⟩
    · refine Or.inl ⟨x, hx, ?_⟩
      exact c6_pow2 (c6_inj_props _ _ hinj _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, hx, rfl⟩)) hx0).1
  · rintro (⟨x, hx, he⟩ | ⟨k, hk, he⟩)
    · refine Or.inr ⟨x, ⟨hx, by rw [he]; exact (Nat.two_pow_pos b).ne', ?_⟩, ?_⟩
      · rw [he]; unfold log2; rw [Nat.log2_two_pow]; exact hb
      · rw [he]; unfold log2; rw [Nat.log2_two_pow]
    · exact Or.inl ⟨k, hk, Nat.pow_right_injective (le_refl 2) he⟩

theorem c6_Zrest {n q : ℕ} {sh : Aff} {others : List (ℕ × ℕ)} (lim : Option ℕ)
    (hinj : injOk sh.y0 (others.map (·.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)) = true) :
    ct_yFree (ct_limYm ((List.range n).map (fun x ↦ q + x) ++
        (others.filter fun x ↦ x.2 != 0 && decide (log2 x.2 < yVars)).map (fun x ↦ log2 x.2)) lim) =
      (ct_yFree (ct_limYm [] lim)).filter
        (fun b ↦ !((others.map (fun x : ℕ × ℕ ↦ x.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)).any
          (· == 2 ^ b))) := by
  unfold ct_yFree
  rw [List.filter_filter]
  apply List.filter_congr; intro b hb
  have hb' := List.mem_range.mp hb
  have hany : ((others.map (fun x : ℕ × ℕ ↦ x.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)).any (· == 2 ^ b)) =
      ((List.range n).map (fun x ↦ q + x) ++
        (others.filter fun x : ℕ × ℕ ↦ x.2 != 0 && decide (log2 x.2 < yVars)).map (fun x ↦ log2 x.2)).contains b := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_mem, c6_ym_iff hinj hb']
    simp only [beq_iff_eq]
    exact ⟨fun ⟨c, hc, he⟩ ↦ he ▸ hc, fun h ↦ ⟨_, h, rfl⟩⟩
  rw [hany]
  cases lim with
  | none => simp [ct_limYm]
  | some e =>
    simp only [ct_limYm]
    rw [List.contains_append, List.nil_append, Bool.not_or]

theorem c6_xsplit (P : Pt) {x0 l jf : ℕ} (hx : x0 % 2 ^ l = 0) (hxl : x0 + 2 ^ l ≤ 2 ^ xVars) (hjf : jf < 2 ^ l) :
    ct_eqOn P.rx (List.range xVars) (x0 + jf) =
      (∏ i ∈ Finset.range l, eq1 (P.rx.getD i 0) (jf.testBit i)) * ct_eqOn P.rx (ct_xFree l) x0 := by
  have h := c6_cubeX P x0 l jf 0 hx hxl (Nat.mod_one _) (by simpa using hjf)
  simp only [pow_zero, Finset.sum_range_one, add_zero] at h
  rw [h, c6_kerVal, List.map_map, c6_lprod_filter]
  simp [kfVal]

/-- One iteration of K2's shifted half, in the successor kernel's factors. -/
theorem c6_succ_summand (P : Pt) {l p n q : ℕ} {sh : Aff} {others : List (ℕ × ℕ)} (Z : List ℕ) (hZnd : Z.Nodup)
    (hZ : ∀ b ∈ Z, b < yVars) (hpn : p + n ≤ l)
    (hfield : ∀ k < n, sh.coef.getD (p + k) 0 = 2 ^ (q + k))
    (hoth : others = ((List.range l).filter (fun i ↦ decide (i < p) || decide (i ≥ p + n))).map
        (fun i ↦ (i, sh.coef.getD i 0)))
    (hinj : injOk sh.y0 (others.map (·.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)) = true)
    (hqZ : ∀ k < n, q + k ∈ Z) (hpZ : ∀ x ∈ others, x.2 ≠ 0 → log2 x.2 < yVars → log2 x.2 ∈ Z)
    {jf : ℕ} (hjf : jf < 2 ^ l) (hF : jf / 2 ^ p % 2 ^ n ≠ 0) :
    (∏ i ∈ Finset.range l, eq1 (P.rx.getD i 0) (jf.testBit i)) * ct_eqOn P.ry Z (sh.at (jf - 2 ^ p)) =
      ct_eqOn P.ry (Z.filter fun b ↦ !((others.map (fun x : ℕ × ℕ ↦ x.2) ++
          (List.range n).map fun k ↦ 2 ^ (q + k)).any (· == 2 ^ b))) sh.y0 *
        (eqW ((List.range n).map fun k ↦ P.rx.getD (p + k) 0) (jf / 2 ^ p % 2 ^ n) *
          eqW ((List.range n).map fun k ↦ P.ry.getD (q + k) 0) (jf / 2 ^ p % 2 ^ n - 1) *
          ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then 1 else
            eq1 (P.rx.getD i 0) (jf.testBit i) *
              (if (decide (i < p) || decide (i ≥ p + n)) = true ∧ sh.coef.getD i 0 ≠ 0 ∧
                  log2 (sh.coef.getD i 0) < yVars then
                eq1 (P.ry.getD (log2 (sh.coef.getD i 0)) 0) (jf.testBit i) else 1))) := by
  rw [c6_Y_eq hpn hfield hoth hjf hF,
    c6_inj_eqOn P.ry _ sh.y0 sh.y0 Z (by rw [c6_Lw_fst]; exact hinj) hZnd (fun _ h ↦ h), c6_Lw_fst]
  set F := jf / 2 ^ p % 2 ^ n with hFdef
  -- the field's `y` factors
  have hfy : (((List.range n).map fun k ↦ (2 ^ (q + k), (F - 1).testBit k)).map fun cb : ℕ × Bool ↦
      if cb.1 ≠ 0 ∧ log2 cb.1 ∈ Z then eq1 (P.ry.getD (log2 cb.1) 0) cb.2 else 1).prod =
      eqW ((List.range n).map fun k ↦ P.ry.getD (q + k) 0) (F - 1) := by
    rw [List.map_map, c6_lprod, c6_eqW_map]
    apply Finset.prod_congr rfl; intro k hk
    have hk' := Finset.mem_range.mp hk
    have hl2 : log2 (2 ^ (q + k)) = q + k := by unfold log2; exact Nat.log2_two_pow
    simp only [Function.comp, hl2]
    rw [if_pos ⟨(Nat.two_pow_pos _).ne', hqZ k hk'⟩]
  -- the other bits' `y` factors
  have hoy : ((others.map fun x ↦ (x.2, jf.testBit x.1)).map fun cb : ℕ × Bool ↦
      if cb.1 ≠ 0 ∧ log2 cb.1 ∈ Z then eq1 (P.ry.getD (log2 cb.1) 0) cb.2 else 1).prod =
      ∏ i ∈ Finset.range l, if (decide (i < p) || decide (i ≥ p + n)) = true then
        (if sh.coef.getD i 0 ≠ 0 ∧ log2 (sh.coef.getD i 0) ∈ Z then
          eq1 (P.ry.getD (log2 (sh.coef.getD i 0)) 0) (jf.testBit i) else 1) else 1 := by
    rw [List.map_map]
    conv_lhs => rw [hoth]
    rw [List.map_map, c6_lprod_filter]
    rfl
  -- the field's `x` factors
  have hfx : (∏ i ∈ Finset.range l, eq1 (P.rx.getD i 0) (jf.testBit i)) =
      eqW ((List.range n).map fun k ↦ P.rx.getD (p + k) 0) F *
        ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then 1 else eq1 (P.rx.getD i 0) (jf.testBit i)) := by
    have h1 : (∏ i ∈ Finset.range l, eq1 (P.rx.getD i 0) (jf.testBit i)) =
        (∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then eq1 (P.rx.getD i 0) (jf.testBit i) else 1)) *
        ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then 1 else eq1 (P.rx.getD i 0) (jf.testBit i)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      split_ifs <;> simp
    rw [h1, c6_prod_field hpn, c6_eqW_map]
    congr 1
    apply Finset.prod_congr rfl; intro k hk
    rw [hFdef, c6_tbF]
    simp [Finset.mem_range.mp hk, add_comm]
  rw [c6_Lw, List.map_append, List.prod_append, hfy, hoy, hfx]
  have hcomb : (∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then 1 else eq1 (P.rx.getD i 0) (jf.testBit i))) *
      (∏ i ∈ Finset.range l, if (decide (i < p) || decide (i ≥ p + n)) = true then
        (if sh.coef.getD i 0 ≠ 0 ∧ log2 (sh.coef.getD i 0) ∈ Z then
          eq1 (P.ry.getD (log2 (sh.coef.getD i 0)) 0) (jf.testBit i) else 1) else 1) =
      ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then 1 else
            eq1 (P.rx.getD i 0) (jf.testBit i) *
              (if (decide (i < p) || decide (i ≥ p + n)) = true ∧ sh.coef.getD i 0 ≠ 0 ∧
                  log2 (sh.coef.getD i 0) < yVars then
                eq1 (P.ry.getD (log2 (sh.coef.getD i 0)) 0) (jf.testBit i) else 1)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i hi
    have hi' := Finset.mem_range.mp hi
    by_cases h1 : p ≤ i ∧ i < p + n
    · have hO : (decide (i < p) || decide (i ≥ p + n)) = false := by simp; omega
      simp only [h1, and_self, if_true, hO, Bool.false_eq_true, if_false, mul_one]
    · have hO : (decide (i < p) || decide (i ≥ p + n)) = true := by simp; omega
      simp only [h1, if_false, hO, if_true, true_and]
      congr 1
      have hiff : (sh.coef.getD i 0 ≠ 0 ∧ log2 (sh.coef.getD i 0) ∈ Z) ↔
          (sh.coef.getD i 0 ≠ 0 ∧ log2 (sh.coef.getD i 0) < yVars) := by
        have hmem : (i, sh.coef.getD i 0) ∈ others := by
          rw [hoth]; exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr hi', hO⟩, rfl⟩
        exact ⟨fun h ↦ ⟨h.1, hZ _ h.2⟩, fun h ↦ ⟨h.1, hpZ _ hmem h.1 h.2⟩⟩
      simp only [hiff]
  rw [← hcomb]
  ring

theorem c6_kerVal_limFs (P : Pt) (fs : List KF) (lim : Option ℕ) :
    kerVal P (ct_limFs fs lim) = kerVal P fs * kerVal P (ct_limFs [] lim) := by
  cases lim with
  | none => simp [ct_limFs, kerVal]
  | some e => simp [ct_limFs, c6_kerVal, List.map_append, List.prod_append]

theorem c6_sum_A (xs ys : List FE) (n : ℕ) (hx : xs.length = n) (hy : ys.length = n) :
    ∑ u ∈ Finset.range (2 ^ n), (if u = 0 then 0 else eqW xs u * eqW ys (u - 1)) = succVal xs ys := by
  rw [succVal_eq xs ys (by rw [hx, hy]), c6_lsum, hx,
    show 2 ^ n = (2 ^ n - 1) + 1 by have := Nat.two_pow_pos n; omega, Finset.sum_range_succ']
  simp

theorem c6_pairs_ker (P : Pt) (l p n : ℕ) (coef : List ℕ) (others : List (ℕ × ℕ))
    (hoth : others = ((List.range l).filter (fun i ↦ decide (i < p) || decide (i ≥ p + n))).map
        (fun i ↦ (i, coef.getD i 0))) :
    ∏ i ∈ Finset.range l, (if p ≤ i ∧ i < p + n then 1 else
        (eq1 (P.rx.getD i 0) false *
            (if (decide (i < p) || decide (i ≥ p + n)) = true ∧ coef.getD i 0 ≠ 0 ∧ log2 (coef.getD i 0) < yVars then
              eq1 (P.ry.getD (log2 (coef.getD i 0)) 0) false else 1) +
          eq1 (P.rx.getD i 0) true *
            (if (decide (i < p) || decide (i ≥ p + n)) = true ∧ coef.getD i 0 ≠ 0 ∧ log2 (coef.getD i 0) < yVars then
              eq1 (P.ry.getD (log2 (coef.getD i 0)) 0) true else 1))) =
      kerVal P ((others.filter fun x ↦ x.2 != 0 && decide (log2 x.2 < yVars)).map
        fun x ↦ KF.pair x.1 (log2 x.2)) := by
  rw [c6_kerVal, hoth, List.filter_map, List.filter_filter, List.map_map, List.map_map, c6_lprod_filter]
  apply Finset.prod_congr rfl; intro i _
  by_cases h1 : p ≤ i ∧ i < p + n
  · have hO : (decide (i < p) || decide (i ≥ p + n)) = false := by simp; omega
    simp [h1, hO]
  · have hO : (decide (i < p) || decide (i ≥ p + n)) = true := by simp; omega
    simp only [h1, if_false, hO, true_and, Function.comp, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    split_ifs with h2
    · simp only [eq1, kfVal, Bool.false_eq_true, if_false, if_true]
      have h2' : (2 : FE) = 0 := CharTwo.two_eq_zero
      linear_combination (P.rx.getD i 0 * P.ry.getD (log2 (coef.getD i 0)) 0) * h2'
    · simp [eq1]

/-- **K2's successor atom.** -/
theorem c6_shiftSucc (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s) (t : CTerm)
    (lim : Option ℕ) (ht : TermWF t) {p n : ℕ} {sh ini : Aff} {q : ℕ} {others : List (ℕ × ℕ)}
    (hc : t.cls = .shift p n sh ini) (hpn : p + n ≤ t.l) (hn : 2 ≤ n) (hso : shiftOk t.l p n sh = some (q, others))
    (hL : ∀ e, lim = some e → e + 1 < yVars ∧ ∀ jf < 2 ^ t.l, (t.cls.at jf >>> e) % 4 = 0) :
    ct_Adds pt s (s.addAtom (KF.succ ((List.range n).map fun x ↦ p + x) ((List.range n).map fun x ↦ q + x) ::
        (others.filter fun x ↦ x.2 != 0 && decide (log2 x.2 < yVars)).map fun x ↦ KF.pair x.1 (log2 x.2))
        t.o t.l t.x0 ((List.range n).map (fun x ↦ q + x) ++
          (others.filter fun x ↦ x.2 != 0 && decide (log2 x.2 < yVars)).map fun x ↦ log2 x.2) sh.y0 t.w lim)
      ((List.range (2 ^ t.l)).map fun jf ↦
        if jf / 2 ^ p % 2 ^ n = 0 then 0 else t.w * ct_EL pt lim t.o (t.x0 + jf) (sh.at (jf - 2 ^ p))).sum := by
  obtain ⟨hfield, hqn, hoth, hinj⟩ := c6_shiftOk_dec hso
  obtain ⟨ho, hx, hxl⟩ := ht
  have hlimbY : ∀ e, lim = some e → ∀ jf < 2 ^ t.l, jf / 2 ^ p % 2 ^ n ≠ 0 →
      (sh.at (jf - 2 ^ p) >>> e) % 4 = 0 := by
    intro e he jf hjf hF
    have := (hL e he).2 jf hjf
    rwa [c6_cls_shift hc, if_neg hF] at this
  have hZnd : (ct_yFree (ct_limYm [] lim)).Nodup := List.Nodup.filter _ List.nodup_range
  have hZ : ∀ b ∈ ct_yFree (ct_limYm [] lim), b < yVars := fun b hb ↦ (c6_mem_Z.mp hb).1
  have hqZ := c6_qZ hpn hn hfield hqn hoth hinj hlimbY
  have hpZ := c6_pZ hpn hn hfield hoth hinj hlimbY
  have hsum : ((List.range (2 ^ t.l)).map fun jf ↦
      if jf / 2 ^ p % 2 ^ n = 0 then 0 else t.w * ct_EL pt lim t.o (t.x0 + jf) (sh.at (jf - 2 ^ p))).sum =
      t.w * eqW (sub (Pt.ofList pt).kap 0 2) t.o * kerVal (Pt.ofList pt) (ct_limFs [] lim) *
        ct_eqOn (Pt.ofList pt).rx (ct_xFree t.l) t.x0 *
        ct_eqOn (Pt.ofList pt).ry ((ct_yFree (ct_limYm [] lim)).filter fun b ↦
          !((others.map (fun x : ℕ × ℕ ↦ x.2) ++ (List.range n).map fun k ↦ 2 ^ (q + k)).any (· == 2 ^ b))) sh.y0 *
        ∑ jf ∈ Finset.range (2 ^ t.l),
          (fun u ↦ if u = 0 then 0 else
            eqW ((List.range n).map fun k ↦ (Pt.ofList pt).rx.getD (p + k) 0) u *
            eqW ((List.range n).map fun k ↦ (Pt.ofList pt).ry.getD (q + k) 0) (u - 1)) (jf / 2 ^ p % 2 ^ n) *
          ∏ i ∈ Finset.range t.l, (if p ≤ i ∧ i < p + n then 1 else
            (fun i b ↦ eq1 ((Pt.ofList pt).rx.getD i 0) b *
              (if (decide (i < p) || decide (i ≥ p + n)) = true ∧ sh.coef.getD i 0 ≠ 0 ∧
                  log2 (sh.coef.getD i 0) < yVars then
                eq1 ((Pt.ofList pt).ry.getD (log2 (sh.coef.getD i 0)) 0) b else 1)) i (jf.testBit i)) := by
    rw [c6_lsum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro jf hjf
    have hjf' := Finset.mem_range.mp hjf
    by_cases hF : jf / 2 ^ p % 2 ^ n = 0
    · simp [hF]
    · rw [if_neg hF, c6_EL_split pt hpt lim t.o _ _ ho (by omega)
        (fun e he ↦ ⟨(hL e he).1, hlimbY e he jf hjf' hF⟩), c6_xsplit (Pt.ofList pt) hx hxl hjf']
      have hs := c6_succ_summand (Pt.ofList pt) _ hZnd hZ hpn hfield hoth hinj hqZ hpZ hjf' hF
      simp only [hF, if_false]
      calc _ = t.w * eqW (sub (Pt.ofList pt).kap 0 2) t.o * kerVal (Pt.ofList pt) (ct_limFs [] lim) *
            ct_eqOn (Pt.ofList pt).rx (ct_xFree t.l) t.x0 *
            ((∏ i ∈ Finset.range t.l, eq1 ((Pt.ofList pt).rx.getD i 0) (jf.testBit i)) *
              ct_eqOn (Pt.ofList pt).ry (ct_yFree (ct_limYm [] lim)) (sh.at (jf - 2 ^ p))) := by ring
        _ = _ := by rw [hs]; ring
  refine ct_Adds_congr (ct_addAtom pt s hs _ t.o t.l t.x0 _ sh.y0 t.w lim ho) ?_
  rw [hsum, c6_engine hpn (fun u ↦ if u = 0 then 0 else
            eqW ((List.range n).map fun k ↦ (Pt.ofList pt).rx.getD (p + k) 0) u *
            eqW ((List.range n).map fun k ↦ (Pt.ofList pt).ry.getD (q + k) 0) (u - 1))
      (fun i b ↦ eq1 ((Pt.ofList pt).rx.getD i 0) b *
              (if (decide (i < p) || decide (i ≥ p + n)) = true ∧ sh.coef.getD i 0 ≠ 0 ∧
                  log2 (sh.coef.getD i 0) < yVars then
                eq1 ((Pt.ofList pt).ry.getD (log2 (sh.coef.getD i 0)) 0) b else 1))]
  rw [c6_sum_A _ _ n (by simp) (by simp),
    c6_pairs_ker (Pt.ofList pt) t.l p n sh.coef others hoth, c6_kerVal_limFs, c6_Zrest lim hinj]
  have hks : kerVal (Pt.ofList pt) (KF.succ ((List.range n).map fun x ↦ p + x) ((List.range n).map fun x ↦ q + x) ::
        (others.filter fun x ↦ x.2 != 0 && decide (log2 x.2 < yVars)).map fun x ↦ KF.pair x.1 (log2 x.2)) =
      succVal ((List.range n).map fun k ↦ (Pt.ofList pt).rx.getD (p + k) 0)
          ((List.range n).map fun k ↦ (Pt.ofList pt).ry.getD (q + k) 0) *
        kerVal (Pt.ofList pt) ((others.filter fun x ↦ x.2 != 0 && decide (log2 x.2 < yVars)).map
          fun x ↦ KF.pair x.1 (log2 x.2)) := by
    rw [c6_kerVal, List.map_cons, List.prod_cons, ← c6_kerVal]
    simp only [kfVal, List.map_map, Function.comp_def]
  rw [hks]
  ring

/-! ## The target -/

/-- **A term's pieces** (C6). -/
theorem ct_addTerm (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s)
    (t : CTerm) (lim : Option ℕ) (ht : TermWF t) (hl : ct_LimOk t lim) :
    ct_Adds pt s (s.addTerm t lim) (ct_pairSum pt (t, lim)) := by
  have hb : termWFB t = true := by
    obtain ⟨h1, h2, h3⟩ := ht
    simp [termWFB, h1, h2, h3]
  have hL : ∀ e, lim = some e → e + 1 < yVars ∧ ∀ jf < 2 ^ t.l, (t.cls.at jf >>> e) % 4 = 0 := by
    intro e he; subst he; exact hl.2
  unfold CS.addTerm
  simp only [hb, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hwv : t.wv = []
  · have hwAt : ∀ jf, t.wAt jf = t.w := fun jf ↦ by simp [CTerm.wAt, hwv]
    have hps : ct_pairSum pt (t, lim) =
        ((List.range (2 ^ t.l)).map fun jf ↦ t.w * ct_EL pt lim t.o (t.x0 + jf) (t.cls.at jf)).sum := by
      simp only [ct_pairSum, hwAt]
    rw [hps]
    simp only [hwv, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false]
    by_cases hw : (t.w == 0) = true
    · rw [if_pos hw, c6_FE_eq_of_beq hw]
      exact ct_Adds_congr (ct_Adds_refl hs) (by simp)
    · rw [if_neg hw]
      cases hc : t.cls with
      | aff a =>
        simp only []
        refine ct_Adds_congr (ct_addSub pt hpt s hs t.o t.w t.x0 t.l a [] lim ht.1 ht.2.1 ht.2.2
          ⟨by simp, by simp⟩ ?_) ?_
        · cases lim with
          | none => trivial
          | some e =>
            refine ⟨(hL e rfl).1, fun jf hjf _ ↦ ?_⟩
            have := (hL e rfl).2 jf hjf
            rwa [hc] at this
        · congr 1
      | split parts =>
        simp only []
        by_cases hok : splitOk t.l parts = true
        · rw [if_pos hok]
          have h := c6_split pt hpt s hs t lim ht parts hc hok hL
          simp only [hc] at h
          exact h
        · rw [if_neg hok]
          have h := c6_addPoints pt hpt s hs t lim ht hL
          simp only [hc] at h
          exact h
      | shift p n sh ini =>
        simp only []
        by_cases hpn : (decide (p + n > t.l) || decide (n = 0)) = true
        · rw [if_pos hpn]
          have h := c6_addPoints pt hpt s hs t lim ht hL
          simp only [hc] at h
          exact h
        · rw [if_neg hpn]
          have hpn' : p + n ≤ t.l ∧ n ≠ 0 := by simp at hpn; omega
          have A0 := c6_shift0 pt hpt s hs t lim ht hc hpn'.1 hL
          rw [← hc, c6_shift_sum pt t lim hc]
          by_cases h1 : (n == 1) = true
          · rw [if_pos h1]
            have hn1 : n = 1 := by simpa using h1
            subst hn1
            exact ct_Adds_trans A0 (c6_shift1 pt hpt _ A0.1 t lim ht hc hpn'.1 hL)
          · rw [if_neg h1]
            cases hso : shiftOk t.l p n sh with
            | none =>
              simp only []
              exact ct_Adds_trans A0 (c6_shiftPts pt hpt _ A0.1 t lim ht hc hL)
            | some qo =>
              obtain ⟨q, others⟩ := qo
              simp only []
              have hn2 : 2 ≤ n := by
                have : n ≠ 1 := fun h ↦ h1 (by simp [h])
                omega
              exact ct_Adds_trans A0 (c6_shiftSucc pt hpt _ A0.1 t lim ht hc hpn'.1 hn2 hso hL)
      | point ys =>
        have h := c6_addPoints pt hpt s hs t lim ht hL
        simp only [hc] at h ⊢
        exact h
  · have hnone : lim = none := by
      cases lim with
      | none => rfl
      | some e => exact absurd hl.1 hwv
    subst hnone
    have hne : t.wv.isEmpty = false := by
      cases h : t.wv with
      | nil => exact absurd h hwv
      | cons _ _ => rfl
    simp only [hne, Bool.not_false, if_true]
    unfold CS.addVarying
    refine ct_Adds_congr (c6_go pt hpt t ht (t.l + 1) 0 t.l s hs (by omega) (by simp) (by simp)) ?_
    rw [ct_pairSum, c6_lsum]
    simp [ct_EL]

/-! ## `ct_addGeo` -/

theorem c5a_isPow2 {c : ℕ} (h : isPow2 c = true) : c = 2 ^ log2 c := by
  unfold isPow2 at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨k, rfl⟩ := Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mp h
  simp [log2, Nat.log2_two_pow]

theorem c5a_injOk_cons (u c : ℕ) (cs : List ℕ) :
    injOk u (c :: cs) =
      if c = 0 then injOk u cs else if isPow2 c && u &&& c == 0 then injOk (u ||| c) cs else false := by
  have hnone : ∀ l : List ℕ, (l.foldl (fun (acc : Option ℕ) c ↦ acc.bind fun u ↦
      if c == 0 then some u else if isPow2 c && u &&& c == 0 then some (u ||| c) else none) none) = none := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simpa using ih
  unfold injOk
  simp only [List.foldl_cons, Option.bind_some, beq_iff_eq]
  split_ifs <;> simp_all

theorem c5a_testBit_add_pow {u e : ℕ} (hu : u.testBit e = false) (j : ℕ) :
    (u + 2 ^ e).testBit j = (u.testBit j || decide (j = e)) := by
  have hB : u % 2 ^ (e + 1) < 2 ^ e := by
    rw [Nat.mod_pow_succ]
    have : u / 2 ^ e % 2 = 0 := by
      have := Nat.testBit_eq_decide_div_mod_eq (x := u) (i := e)
      rw [hu] at this
      have h2 := Nat.mod_two_eq_zero_or_one (u / 2 ^ e)
      rcases h2 with h2 | h2
      · exact h2
      · rw [h2] at this; simp at this
    rw [this]; simpa using Nat.mod_lt u (Nat.two_pow_pos e)
  have hu' : u = 2 ^ (e + 1) * (u / 2 ^ (e + 1)) + u % 2 ^ (e + 1) := (Nat.div_add_mod u _).symm
  have hlt : u % 2 ^ (e + 1) + 2 ^ e < 2 ^ (e + 1) := by
    have : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have e1 : u + 2 ^ e = 2 ^ (e + 1) * (u / 2 ^ (e + 1)) + (u % 2 ^ (e + 1) + 2 ^ e) := by omega
  rw [e1, Nat.testBit_two_pow_mul_add _ hlt]
  conv => rhs; rw [hu', Nat.testBit_two_pow_mul_add _ (Nat.mod_lt u (Nat.two_pow_pos _))]
  split_ifs with hj
  · have e2 : u % 2 ^ (e + 1) + 2 ^ e = 2 ^ e * 1 + u % 2 ^ (e + 1) := by ring
    rw [e2, Nat.testBit_two_pow_mul_add _ hB]
    split_ifs with hj'
    · simp [show j ≠ e by omega]
    · have : j = e := by omega
      subst this
      simp [Nat.testBit_lt_two_pow hB]
  · simp [show j ≠ e by omega]

theorem c5a_injOk_mono {u u' : ℕ} {cs : List ℕ} (h : injOk u cs = true)
    (hs : ∀ j, u'.testBit j = true → u.testBit j = true) : injOk u' cs = true := by
  induction cs generalizing u u' with
  | nil => rfl
  | cons c cs ih =>
    rw [c5a_injOk_cons] at h ⊢
    by_cases hc : c = 0
    · simp only [hc, ite_true] at h ⊢
      exact ih h hs
    · simp only [hc, ite_false] at h ⊢
      split_ifs at h with h1
      · simp only [Bool.and_eq_true, beq_iff_eq] at h1
        have h2 : u' &&& c = 0 := by
          apply Nat.eq_of_testBit_eq
          intro j
          have := congrArg (Nat.testBit · j) h1.2
          simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff] at this ⊢
          rcases this with h3 | h3
          · left; by_contra h4; simp only [Bool.not_eq_false] at h4; rw [hs j h4] at h3; exact absurd h3 (by simp)
          · right; exact h3
        simp only [h1.1, h2, beq_self_eq_true, Bool.and_self, ite_true]
        refine ih h fun j hj ↦ ?_
        simp only [Nat.testBit_or, Bool.or_eq_true] at hj ⊢
        rcases hj with hj | hj
        · exact Or.inl (hs j hj)
        · exact Or.inr hj

theorem c5a_at_cons (u c : ℕ) (cs : List ℕ) (J : ℕ) :
    Aff.at ⟨u, c :: cs⟩ J = Aff.at ⟨u + (if J.testBit 0 then c else 0), cs⟩ (J / 2) := by
  unfold Aff.at
  simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
    List.getD_cons_zero, List.getD_cons_succ, Function.comp_def, Nat.testBit_div_two]
  ring

theorem c5a_inj_at {u : ℕ} {cs : List ℕ} (h : injOk u cs = true) (J j : ℕ) :
    (Aff.at ⟨u, cs⟩ J).testBit j = true ↔
      u.testBit j = true ∨ ∃ i < cs.length, J.testBit i = true ∧ cs.getD i 0 = 2 ^ j := by
  induction cs generalizing u J with
  | nil => simp [Aff.at]
  | cons c cs ih =>
    have hex : (∃ i < (c :: cs).length, J.testBit i = true ∧ (c :: cs).getD i 0 = 2 ^ j) ↔
        (J.testBit 0 = true ∧ c = 2 ^ j) ∨ ∃ i < cs.length, (J / 2).testBit i = true ∧ cs.getD i 0 = 2 ^ j := by
      constructor
      · rintro ⟨i, hi, h1, h2⟩
        rcases i with _ | i
        · exact Or.inl ⟨h1, by simpa using h2⟩
        · exact Or.inr ⟨i, by simpa using hi, by rwa [Nat.testBit_div_two], by simpa using h2⟩
      · rintro (⟨h1, h2⟩ | ⟨i, hi, h1, h2⟩)
        · exact ⟨0, by simp, h1, by simpa using h2⟩
        · exact ⟨i + 1, by simpa using hi, by rwa [Nat.testBit_div_two] at h1, by simpa using h2⟩
    rw [hex, c5a_at_cons]
    rw [c5a_injOk_cons] at h
    by_cases hc : c = 0
    · simp only [hc, ite_true] at h
      simp only [hc, ite_self, Nat.add_zero]
      rw [ih h]
      have : (0 : ℕ) ≠ 2 ^ j := (Nat.two_pow_pos j).ne
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | ⟨-, h1⟩ | h1)
        · exact Or.inl h1
        · exact absurd h1 this
        · exact Or.inr h1
    · simp only [hc, ite_false] at h
      split_ifs at h with h1
      · simp only [Bool.and_eq_true, beq_iff_eq] at h1
        have hcp := c5a_isPow2 h1.1
        set e := log2 c
        have hue : u.testBit e = false := by
          have := congrArg (Nat.testBit · e) h1.2
          rw [hcp] at this
          simpa [Nat.testBit_and, Nat.testBit_two_pow] using this
        have hbits : ∀ j', (u + if J.testBit 0 then c else 0).testBit j' = true ↔
            u.testBit j' = true ∨ (J.testBit 0 = true ∧ j' = e) := by
          intro j'
          split_ifs with hJ
          · rw [hcp, c5a_testBit_add_pow hue]; simp [hJ]
          · simp [hJ]
        have hmono : injOk (u + if J.testBit 0 then c else 0) cs = true := by
          refine c5a_injOk_mono h fun j' hj' ↦ ?_
          rw [hbits] at hj'
          rcases hj' with hj' | ⟨-, rfl⟩
          · simp [Nat.testBit_or, hj']
          · rw [Nat.testBit_or, hcp]; simp
        rw [ih hmono, hbits]
        have hce : c = 2 ^ j ↔ j = e := by
          rw [hcp]
          constructor
          · intro h; exact (Nat.pow_right_injective (le_refl 2) h).symm
          · rintro rfl; rfl
        rw [hce]
        tauto

theorem c5a_inj_pow {u : ℕ} {cs : List ℕ} (h : injOk u cs = true) :
    ∀ i < cs.length, cs.getD i 0 ≠ 0 → cs.getD i 0 = 2 ^ log2 (cs.getD i 0) ∧
      u.testBit (log2 (cs.getD i 0)) = false := by
  induction cs generalizing u with
  | nil => intro i hi; simp at hi
  | cons c cs ih =>
    intro i hi hne
    rw [c5a_injOk_cons] at h
    by_cases hc : c = 0
    · simp only [hc, ite_true] at h
      rcases i with _ | i
      · simp [hc] at hne
      · simpa using ih h i (by simpa using hi) (by simpa using hne)
    · simp only [hc, ite_false] at h
      split_ifs at h with h1
      · simp only [Bool.and_eq_true, beq_iff_eq] at h1
        rcases i with _ | i
        · simp only [List.getD_cons_zero]
          have hcp := c5a_isPow2 h1.1
          refine ⟨hcp, ?_⟩
          have := congrArg (Nat.testBit · (log2 c)) h1.2
          rw [hcp] at this
          simpa [Nat.testBit_and, Nat.testBit_two_pow, Nat.log2_two_pow, log2] using this
        · simp only [List.getD_cons_succ] at hne ⊢
          obtain ⟨h2, h3⟩ := ih h i (by simpa using hi) hne
          refine ⟨h2, ?_⟩
          simp only [Nat.testBit_or, Bool.or_eq_false_iff] at h3
          exact h3.1

theorem c5a_inj_ne {u : ℕ} {cs : List ℕ} (h : injOk u cs = true) :
    ∀ i i', i < i' → i' < cs.length → cs.getD i 0 ≠ 0 → cs.getD i 0 ≠ cs.getD i' 0 := by
  induction cs generalizing u with
  | nil => intro i i' _ hi; simp at hi
  | cons c cs ih =>
    intro i i' hii hi hne
    rw [c5a_injOk_cons] at h
    by_cases hc : c = 0
    · simp only [hc, ite_true] at h
      rcases i with _ | i
      · simp [hc] at hne
      · rcases i' with _ | i'
        · omega
        · simpa using ih h i i' (by omega) (by simpa using hi) (by simpa using hne)
    · simp only [hc, ite_false] at h
      split_ifs at h with h1
      · simp only [Bool.and_eq_true, beq_iff_eq] at h1
        rcases i' with _ | i'
        · omega
        rcases i with _ | i
        · simp only [List.getD_cons_zero, List.getD_cons_succ]
          intro heq
          have hcp := c5a_isPow2 h1.1
          obtain ⟨-, h3⟩ := c5a_inj_pow h i' (by simpa using hi) (by rw [← heq]; exact hc)
          rw [← heq, Nat.testBit_or] at h3
          rw [hcp] at h3
          simp [log2, Nat.log2_two_pow] at h3
        · simpa using ih h i i' (by omega) (by simpa using hi) (by simpa using hne)

theorem c5a_inj_log_inj {u : ℕ} {cs : List ℕ} (h : injOk u cs = true) {i i' : ℕ} (hi : i < cs.length)
    (hi' : i' < cs.length) (hne : cs.getD i 0 ≠ 0) (hne' : cs.getD i' 0 ≠ 0)
    (hl : log2 (cs.getD i 0) = log2 (cs.getD i' 0)) : i = i' := by
  have e1 := (c5a_inj_pow h i hi hne).1
  have e2 := (c5a_inj_pow h i' hi' hne').1
  have heq : cs.getD i 0 = cs.getD i' 0 := by rw [e1, e2, hl]
  by_contra hii
  rcases Nat.lt_or_gt_of_ne hii with hii | hii
  · exact c5a_inj_ne h i i' hii hi' hne heq
  · exact c5a_inj_ne h i' i hii hi hne' heq.symm

theorem c5a_inj_bit {u : ℕ} {cs : List ℕ} (h : injOk u cs = true) (J : ℕ) {i : ℕ} (hi : i < cs.length)
    (hne : cs.getD i 0 ≠ 0) : (Aff.at ⟨u, cs⟩ J).testBit (log2 (cs.getD i 0)) = J.testBit i := by
  obtain ⟨hp, hu⟩ := c5a_inj_pow h i hi hne
  rw [Bool.eq_iff_iff, c5a_inj_at h, hu]
  constructor
  · rintro (h1 | ⟨i', hi', hJ, heq⟩)
    · exact absurd h1 (by simp)
    · have hne' : cs.getD i' 0 ≠ 0 := by rw [heq]; positivity
      have : i' = i := c5a_inj_log_inj h hi' hi hne' hne (by rw [heq]; simp [log2, Nat.log2_two_pow])
      exact this ▸ hJ
  · intro hJ
    exact Or.inr ⟨i, hi, hJ, hp⟩

theorem c5a_inj_free {u : ℕ} {cs : List ℕ} (h : injOk u cs = true) (J j : ℕ)
    (hj : ∀ i < cs.length, cs.getD i 0 ≠ 0 → log2 (cs.getD i 0) ≠ j) :
    (Aff.at ⟨u, cs⟩ J).testBit j = u.testBit j := by
  rw [Bool.eq_iff_iff, c5a_inj_at h]
  constructor
  · rintro (h1 | ⟨i, hi, -, heq⟩)
    · exact h1
    · exact absurd (by rw [heq]; simp [log2, Nat.log2_two_pow]) (hj i hi (by rw [heq]; positivity))
  · exact Or.inl

theorem c5a_bin_sum (b z : ℕ) : ((List.range b).map fun k ↦ if z.testBit k then 2 ^ k else 0).sum = z % 2 ^ b := by
  induction b with
  | zero => simp [Nat.mod_one]
  | succ b ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Nat.mod_pow_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (z / 2 ^ b) with h | h <;> simp [h]

theorem c5a_pow_bin (g : FK) (b z : ℕ) :
    FE.ofK (g ^ (z % 2 ^ b)) = ((List.range b).map fun k ↦ if z.testBit k then FE.ofK (g ^ 2 ^ k) else 1).prod := by
  induction b with
  | zero => simp [Nat.mod_one]; rfl
  | succ b ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ← ih, Nat.mod_pow_succ, pow_add]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Nat.testBit_eq_decide_div_mod_eq]
    rw [show ∀ x y : FK, FE.ofK (x * y) = FE.ofK x * FE.ofK y from fun x y ↦ map_mul FE.ofKRingHom x y]
    rcases Nat.mod_two_eq_zero_or_one (z / 2 ^ b) with h | h <;> simp [h, show FE.ofK 1 = 1 from rfl]

theorem c5a_sum_mul_left (L : List ℕ) (c : FE) (f : ℕ → FE) :
    (L.map fun x ↦ c * f x).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, mul_add]

theorem c5a_kerVal (P : Pt) (fs : List KF) : kerVal P fs = (fs.map (kfVal P)).prod := by
  have : ∀ acc, fs.foldl (fun acc f ↦ acc * kfVal P f) acc = acc * (fs.map (kfVal P)).prod := by
    induction fs with
    | nil => simp
    | cons f fs ih => intro acc; simp [ih, mul_assoc]
  rw [kerVal, this, one_mul]

/-- The pairs of a geometric run's atom (`CS.addGeo`). -/
def c5a_pairs (l : ℕ) (coef : List ℕ) : List (ℕ × ℕ) :=
  ((List.range l).map fun i ↦ (i, coef.getD i 0)).filter fun x ↦ x.2 != 0 && decide (log2 x.2 < yVars)

theorem c5a_prod_filter (L : List ℕ) (c : ℕ → ℕ) (p : ℕ × ℕ → Bool) (φ : ℕ × ℕ → FE) :
    (((L.map fun i ↦ (i, c i)).filter p).map φ).prod = (L.map fun i ↦ if p (i, c i) then φ (i, c i) else 1).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    by_cases h : p (x, c x) <;> simp [h, ih]

theorem c5a_prod_pairs (l : ℕ) (coef : List ℕ) (φ : ℕ × ℕ → FE) :
    ((c5a_pairs l coef).map φ).prod = ((List.range l).map fun i ↦
      if (coef.getD i 0 != 0 && decide (log2 (coef.getD i 0) < yVars)) then φ (i, coef.getD i 0) else 1).prod :=
  c5a_prod_filter _ _ _ _

theorem c5a_mem_pairs {l : ℕ} {coef : List ℕ} {x : ℕ × ℕ} (hx : x ∈ c5a_pairs l coef) :
    x.1 < l ∧ x.2 = coef.getD x.1 0 ∧ x.2 ≠ 0 ∧ log2 x.2 < yVars := by
  unfold c5a_pairs at hx
  simp only [List.mem_filter, List.mem_map, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hx
  obtain ⟨⟨i, hi, rfl⟩, h1, h2⟩ := hx
  exact ⟨hi, rfl, h1, h2⟩

theorem c5a_testBit_lo_hi {l jf : ℕ} (hjf : jf < 2 ^ l) (z i : ℕ) :
    (jf + 2 ^ l * z).testBit i = if i < l then jf.testBit i else z.testBit (i - l) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hjf]

theorem c5a_at_append (a : Aff) (l q b jf z : ℕ) (hlen : a.coef.length = l) (hjf : jf < 2 ^ l) (hz : z < 2 ^ b) :
    a.at jf + z * 2 ^ q = Aff.at ⟨a.y0, a.coef ++ (List.range b).map fun k ↦ 2 ^ (q + k)⟩ (jf + 2 ^ l * z) := by
  unfold Aff.at
  simp only [List.length_append, List.length_map, List.length_range, hlen, List.range_add, List.map_append,
    List.sum_append, List.map_map]
  have e1 : ((List.range l).map fun i ↦ if (jf + 2 ^ l * z).testBit i then (a.coef ++ (List.range b).map
      fun k ↦ 2 ^ (q + k)).getD i 0 else 0) = (List.range l).map fun i ↦ if jf.testBit i then a.coef.getD i 0 else 0 := by
    refine List.map_congr_left fun i hi ↦ ?_
    have hi : i < l := List.mem_range.mp hi
    have hb : (jf + 2 ^ l * z).testBit i = jf.testBit i := by rw [c5a_testBit_lo_hi hjf]; simp [hi]
    rw [hb, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD]
  have e2 : ((List.range b).map ((fun i ↦ if (jf + 2 ^ l * z).testBit i then (a.coef ++ (List.range b).map
      fun k ↦ 2 ^ (q + k)).getD i 0 else 0) ∘ fun x ↦ l + x)) =
      (List.range b).map fun k ↦ 2 ^ q * if z.testBit k then 2 ^ k else 0 := by
    refine List.map_congr_left fun k hk ↦ ?_
    have hk : k < b := List.mem_range.mp hk
    simp only [Function.comp_apply]
    have hb : (jf + 2 ^ l * z).testBit (l + k) = z.testBit k := by
      rw [c5a_testBit_lo_hi hjf]; simp
    have hg : (a.coef ++ (List.range b).map fun k ↦ 2 ^ (q + k)).getD (l + k) 0 = 2 ^ (q + k) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        show l + k - a.coef.length = k by omega, List.getElem?_map, List.getElem?_range hk]
      rfl
    rw [hb, hg]
    split_ifs <;> simp [Nat.pow_add]
  rw [e1, e2]
  rw [show ((List.range b).map fun k ↦ 2 ^ q * if z.testBit k then 2 ^ k else 0).sum =
      2 ^ q * ((List.range b).map fun k ↦ if z.testBit k then 2 ^ k else 0).sum from List.sum_map_mul_left _ _ _,
    c5a_bin_sum, Nat.mod_eq_of_lt hz]
  ring

theorem c5a_x_split (r : Array FE) (l x0 jf : ℕ) (hx : x0 % 2 ^ l = 0) (hxl : x0 + 2 ^ l ≤ 2 ^ xVars)
    (hjf : jf < 2 ^ l) :
    ct_eqOn r (List.range xVars) (x0 + jf) =
      ((List.range l).map fun i ↦ eq1 (r.getD i 0) (jf.testBit i)).prod * ct_eqOn r (ct_xFree l) x0 := by
  have hl : l ≤ xVars := by
    have : 2 ^ l ≤ 2 ^ xVars := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hr : List.range xVars = List.range l ++ (List.range (xVars - l)).map (l + ·) := by
    rw [← List.range_add, Nat.add_sub_cancel' hl]
  have hfree : ct_xFree l = (List.range (xVars - l)).map (l + ·) := by
    unfold ct_xFree
    rw [hr, List.filter_append, List.filter_eq_nil_iff.mpr (by simp), List.filter_eq_self.mpr (by simp)]
    rfl
  have hx0 : x0 = 2 ^ l * (x0 / 2 ^ l) := by
    have := Nat.div_add_mod x0 (2 ^ l); omega
  have hb : ∀ j, (x0 + jf).testBit j = if j < l then jf.testBit j else (x0 / 2 ^ l).testBit (j - l) := by
    intro j; rw [hx0, Nat.testBit_two_pow_mul_add _ hjf, ← hx0]
  have hb0 : ∀ j, x0.testBit j = if j < l then false else (x0 / 2 ^ l).testBit (j - l) := by
    intro j
    have := Nat.testBit_two_pow_mul_add (x0 / 2 ^ l) (Nat.two_pow_pos l) j
    rw [Nat.add_zero, ← hx0] at this
    rw [this]; simp
  rw [hr, ct_eqOn_append, hfree]
  congr 1
  · unfold ct_eqOn
    exact congrArg List.prod (List.map_congr_left fun i hi ↦ by
      rw [hb]; simp [List.mem_range.mp hi])
  · refine ct_eqOn_congr r _ _ _ fun j hj ↦ ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hj
    rw [hb, hb0]
    simp

theorem c5a_y_split (r : Array FE) (a : Aff) (l q b jf z : ℕ) (hlen : a.coef.length = l)
    (hinj : injOk a.y0 (a.coef ++ (List.range b).map fun k ↦ 2 ^ (q + k)) = true) (hqb : q + b ≤ yVars)
    (hjf : jf < 2 ^ l) (hz : z < 2 ^ b) :
    ct_eqOn r (List.range yVars) (a.at jf + z * 2 ^ q) =
      ((c5a_pairs l a.coef).map fun x ↦ eq1 (r.getD (log2 x.2) 0) (jf.testBit x.1)).prod *
      ((List.range b).map fun k ↦ eq1 (r.getD (q + k) 0) (z.testBit k)).prod *
      ct_eqOn r (ct_yFree ((c5a_pairs l a.coef).map (fun x ↦ log2 x.2) ++ (List.range b).map (q + ·))) a.y0 := by
  rw [c5a_at_append a l q b jf z hlen hjf hz]
  set CS := a.coef ++ (List.range b).map fun k ↦ 2 ^ (q + k) with hCS
  set J := jf + 2 ^ l * z with hJ
  have hCSlen : CS.length = l + b := by simp [hCS, hlen]
  have hlo : ∀ i < l, CS.getD i 0 = a.coef.getD i 0 := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  have hhi : ∀ k < b, CS.getD (l + k) 0 = 2 ^ (q + k) := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      show l + k - a.coef.length = k by omega, List.getElem?_map, List.getElem?_range hk]
    rfl
  have hlog : ∀ k, log2 (2 ^ (q + k)) = q + k := fun k ↦ Nat.log2_two_pow
  have hJlo : ∀ i < l, J.testBit i = jf.testBit i := by
    intro i hi; rw [hJ, c5a_testBit_lo_hi hjf]; simp [hi]
  have hJhi : ∀ k, J.testBit (l + k) = z.testBit k := by
    intro k; rw [hJ, c5a_testBit_lo_hi hjf]; simp
  have hpb : ∀ x ∈ c5a_pairs l a.coef, (Aff.at ⟨a.y0, CS⟩ J).testBit (log2 x.2) = jf.testBit x.1 := by
    intro x hx
    obtain ⟨h1, h2, h3, -⟩ := c5a_mem_pairs hx
    have hne : CS.getD x.1 0 ≠ 0 := by rw [hlo _ h1, ← h2]; exact h3
    have := c5a_inj_bit hinj J (by omega : x.1 < CS.length) hne
    rw [hlo _ h1, ← h2] at this
    rw [this, hJlo _ h1]
  have hgb : ∀ k < b, (Aff.at ⟨a.y0, CS⟩ J).testBit (q + k) = z.testBit k := by
    intro k hk
    have hne : CS.getD (l + k) 0 ≠ 0 := by rw [hhi k hk]; positivity
    have := c5a_inj_bit hinj J (by omega : l + k < CS.length) hne
    rw [hhi k hk, hlog] at this
    rw [this, hJhi]
  set ym := (c5a_pairs l a.coef).map (fun x ↦ log2 x.2) ++ (List.range b).map (q + ·) with hym
  have hmem_ym : ∀ i < CS.length, CS.getD i 0 ≠ 0 → log2 (CS.getD i 0) < yVars → log2 (CS.getD i 0) ∈ ym := by
    intro i hi hne hlt
    by_cases hil : i < l
    · rw [hym, List.mem_append]; left
      rw [hlo i hil] at hne hlt ⊢
      refine List.mem_map.mpr ⟨(i, a.coef.getD i 0), ?_, rfl⟩
      unfold c5a_pairs
      simp only [List.mem_filter, List.mem_map, List.mem_range]
      exact ⟨⟨i, hil, rfl⟩, by simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]; exact ⟨hne, hlt⟩⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = l + k := ⟨i - l, by omega⟩
      rw [hym, List.mem_append]; right
      rw [hhi k (by omega), hlog]
      exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
  have hym_lt : ∀ j ∈ ym, j < yVars := by
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj
      exact (c5a_mem_pairs hx).2.2.2
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      have := List.mem_range.mp hk; omega
  have hnd : ym.Nodup := by
    rw [hym, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · have hpn : (c5a_pairs l a.coef).Nodup := by
        unfold c5a_pairs
        exact (List.nodup_range.map (fun i j h ↦ by simpa using congrArg Prod.fst h)).filter _
      refine hpn.map_on fun x hx y hy hxy ↦ ?_
      obtain ⟨hx1, hx2, hx3, -⟩ := c5a_mem_pairs hx
      obtain ⟨hy1, hy2, hy3, -⟩ := c5a_mem_pairs hy
      have : x.1 = y.1 := by
        refine c5a_inj_log_inj hinj (by omega : x.1 < CS.length) (by omega : y.1 < CS.length) ?_ ?_ ?_
        · rw [hlo _ hx1, ← hx2]; exact hx3
        · rw [hlo _ hy1, ← hy2]; exact hy3
        · rw [hlo _ hx1, hlo _ hy1, ← hx2, ← hy2]; exact hxy
      exact Prod.ext this (by rw [hx2, hy2, this])
    · exact List.nodup_range.map (fun i j h ↦ by simpa using h)
    · intro u hu v hv huv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      have hk := List.mem_range.mp hk
      obtain ⟨hx1, hx2, hx3, -⟩ := c5a_mem_pairs hx
      have := c5a_inj_log_inj hinj (by omega : x.1 < CS.length) (by omega : l + k < CS.length)
        (by rw [hlo _ hx1, ← hx2]; exact hx3) (by rw [hhi k hk]; positivity)
        (by rw [hlo _ hx1, ← hx2, hhi k hk, hlog]; exact huv)
      omega
  have hperm : (List.range yVars).Perm (ym ++ ct_yFree ym) := by
    have h1 := List.filter_append_perm (fun b ↦ ym.contains b) (List.range yVars)
    refine h1.symm.trans (List.Perm.append_right _ ?_)
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd]
    intro j
    simp only [List.mem_filter, List.mem_range, List.contains_iff_mem]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hym_lt j h, h⟩⟩
  have hsplit : ∀ V, ct_eqOn r ym V = ct_eqOn r ((c5a_pairs l a.coef).map (fun x ↦ log2 x.2)) V *
      ct_eqOn r ((List.range b).map (q + ·)) V := fun V ↦ ct_eqOn_append r _ _ V
  rw [ct_eqOn_perm r hperm, ct_eqOn_append, hsplit]
  congr 1
  congr 1
  · unfold ct_eqOn
    rw [List.map_map]
    exact congrArg List.prod (List.map_congr_left fun x hx ↦ by simp [hpb x hx])
  · unfold ct_eqOn
    rw [List.map_map]
    exact congrArg List.prod (List.map_congr_left fun k hk ↦ by simp [hgb k (List.mem_range.mp hk)])
  · refine ct_eqOn_congr r _ _ _ fun j hj ↦ ?_
    unfold ct_yFree at hj
    simp only [List.mem_filter, List.mem_range, Bool.not_eq_true'] at hj
    have hj2 : j ∉ ym := by simpa using hj.2
    refine c5a_inj_free hinj J j fun i hi hne heq ↦ hj2 ?_
    rw [← heq]
    exact hmem_ym i hi hne (by rw [heq]; exact hj.1)

/-- **A geometric run's atom** (C5). -/
theorem ct_addGeo (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s)
    (r : CTerm × ℕ × ℕ × FK) (hr : ct_GeoOk r) :
    ct_Adds pt s (s.addGeo r) (ct_geoSum pt r) := by
  obtain ⟨t, q, b, g⟩ := r
  obtain ⟨a, ha, hwv, htwf, hlen, hinj, hy, hqb⟩ := hr
  obtain ⟨src, idx, l, o, w, x0, cls, wv⟩ := t
  simp only at ha hwv htwf hlen
  subst ha
  obtain ⟨ho, hx, hxl⟩ := htwf
  simp only at ho hx hxl
  show ct_Adds pt s (s.addAtom ((c5a_pairs l a.coef).map (fun x ↦ KF.pair x.1 (log2 x.2)) ++
    (List.range b).map fun k ↦ KF.ypow (q + k) (g ^ (2 ^ k))) o l x0
    ((c5a_pairs l a.coef).map (fun x ↦ log2 x.2) ++ (List.range b).map (q + ·)) a.y0 w none) _
  refine ct_Adds_congr (ct_addAtom pt s hs _ o l x0 _ a.y0 w none ho) ?_
  simp only [ct_limFs, ct_limYm]
  unfold ct_geoSum
  simp only [ct_affOf]
  set C := w * eqW (sub (Pt.ofList pt).kap 0 2) o * ct_eqOn (Pt.ofList pt).rx (ct_xFree l) x0 * ct_eqOn (Pt.ofList pt).ry (ct_yFree ((c5a_pairs l a.coef).map (fun x ↦ log2 x.2) ++ (List.range b).map (q + ·))) a.y0 with hC
  set f : ℕ → Bool → FE := fun i β ↦ eq1 ((Pt.ofList pt).rx.getD i 0) β *
    (if (a.coef.getD i 0 != 0 && decide (log2 (a.coef.getD i 0) < yVars)) then
      eq1 ((Pt.ofList pt).ry.getD (log2 (a.coef.getD i 0)) 0) β else 1) with hf
  set h : ℕ → Bool → FE := fun k β ↦ (if β then FE.ofK (g ^ 2 ^ k) else 1) * eq1 ((Pt.ofList pt).ry.getD (q + k) 0) β with hh
  have hterm : ∀ z < 2 ^ b, ∀ jf < 2 ^ l, w * FE.ofK (g ^ z) * ct_E pt o (x0 + jf) (a.at jf + z * 2 ^ q) =
      (C * ((List.range b).map fun k ↦ h k (z.testBit k)).prod) * ((List.range l).map fun i ↦ f i (jf.testBit i)).prod := by
    intro z hz jf hjf
    rw [ct_E_split pt hpt o _ _ ho (by omega), c5a_x_split _ l x0 jf hx hxl hjf,
      c5a_y_split _ a l q b jf z hlen hinj hqb hjf hz]
    have hg : FE.ofK (g ^ z) = ((List.range b).map fun k ↦ if z.testBit k then FE.ofK (g ^ 2 ^ k) else 1).prod := by
      rw [← c5a_pow_bin, Nat.mod_eq_of_lt hz]
    rw [hg, hf, hh, List.prod_map_mul, List.prod_map_mul, c5a_prod_pairs]
    rw [hC]
    ring
  have hsum : ((List.range (2 ^ b)).map fun z ↦ ((List.range (2 ^ l)).map fun jf ↦
      w * FE.ofK (g ^ z) * ct_E pt o (x0 + jf) (a.at jf + z * 2 ^ q)).sum).sum =
      C * ((List.range (2 ^ b)).map fun z ↦ ((List.range b).map fun k ↦ h k (z.testBit k)).prod).sum *
        ((List.range (2 ^ l)).map fun jf ↦ ((List.range l).map fun i ↦ f i (jf.testBit i)).prod).sum := by
    rw [List.map_congr_left fun z hz ↦ congrArg List.sum (List.map_congr_left fun jf hjf ↦
      hterm z (List.mem_range.mp hz) jf (List.mem_range.mp hjf))]
    simp only [List.sum_map_mul_left, List.sum_map_mul_right]
  rw [hsum, ct_sum_prod_bits l f, ct_sum_prod_bits b h, c5a_kerVal, List.map_append, List.prod_append,
    List.map_map, List.map_map, c5a_prod_pairs]
  have hf2 : ∀ i, f i false + f i true = if (a.coef.getD i 0 != 0 && decide (log2 (a.coef.getD i 0) < yVars)) then
      kfVal (Pt.ofList pt) (KF.pair i (log2 (a.coef.getD i 0))) else 1 := by
    intro i
    rw [hf]
    simp only [eq1, kfVal, Bool.false_eq_true, ite_false, ite_true]
    split_ifs
    · have h2 : (2 : FE) = 0 := CharTwo.two_eq_zero
      linear_combination ((Pt.ofList pt).rx.getD i 0 * (Pt.ofList pt).ry.getD (log2 (a.coef.getD i 0)) 0) * h2
    · ring
  have hh2 : ∀ k, h k false + h k true = kfVal (Pt.ofList pt) (KF.ypow (q + k) (g ^ 2 ^ k)) := by
    intro k
    rw [hh]
    simp only [eq1, kfVal, Bool.false_eq_true, ite_false, ite_true, FE.smulBase_eq_mul]
    ring
  simp only [hf2, hh2, Function.comp_def]
  rw [hC]
  ring

theorem c5a_loop {β : Type} (f : Unit → β → Id (ForInStep β)) (P Q : β → Prop) (μ : β → ℕ)
    (hstep : ∀ s, P s → ∀ s', f () s = ForInStep.yield s' → P s' ∧ μ s' < μ s)
    (hdone : ∀ s, P s → ∀ s', f () s = ForInStep.done s' → Q s')
    (s : β) (hs : P s) : Q (forIn (m := Id) Lean.Loop.mk s f) := by
  induction h : μ s using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    change Q (Lean.Loop.forIn (m := Id) _ _ _)
    rw [Lean.Loop.forIn_eq_of_monadTail]
    cases hf : f () s with
    | done s' => exact hdone s hs s' hf
    | yield s' =>
      obtain ⟨hP, hμ⟩ := hstep s hs s' hf
      exact ih _ (h ▸ hμ) s' hP rfl

theorem c5a_FE_beq {a b : FE} (h : (a == b) = true) : a = b := by
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  change (a0 == b0 && a1 == b1 && a2 == b2) = true at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

theorem c5a_find_getD (p : ℕ → Bool) (L : List ℕ) (h : (L.find? p).getD 0 ≠ 0) :
    p ((L.find? p).getD 0) = true := by
  cases hf : L.find? p with
  | none => simp [hf] at h
  | some b => simpa using List.find?_some hf

/-- What `geoOf` checks when it finds a run. -/
theorem c5a_geoOf_some (ts : Array CTerm) (i q b : ℕ) (g : FK) (h : geoOf ts i = some (q, b, g)) :
    ∃ a, (ts.getD i default).cls = .aff a ∧ (ts.getD i default).wv = [] ∧
      termWFB (ts.getD i default) = true ∧ a.coef.length = (ts.getD i default).l ∧ b ≠ 0 ∧
      (a.y0 >>> q) % 2 ^ b = 0 ∧ q + b ≤ yVars ∧
      injOk a.y0 (a.coef ++ (List.range b).map fun k ↦ 2 ^ (q + k)) = true ∧
      ∀ z < 2 ^ b, i + z < ts.size ∧ (ts.getD (i + z) default).o = (ts.getD i default).o ∧
        (ts.getD (i + z) default).x0 = (ts.getD i default).x0 ∧
        (ts.getD (i + z) default).l = (ts.getD i default).l ∧ (ts.getD (i + z) default).wv = [] ∧
        (ts.getD (i + z) default).cls = .aff ⟨a.y0 + z * 2 ^ q, a.coef⟩ ∧
        (ts.getD (i + z) default).w = (ts.getD i default).w * FE.ofK (g ^ z) := by
  unfold geoOf at h
  simp only [Id.run] at h
  generalize ts.getD i default = t0 at h ⊢
  rcases t0 with ⟨src, idx, l, o, w, x0, cls, wv⟩
  cases cls with
  | aff a => 
    simp only at h
    split_ifs at h with h1 h2 h3 h4
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hb0 := h4
    simp only [beq_iff_eq] at hb0
    have hok := c5a_find_getD _ _ hb0
    rw [Bool.not_eq_true, Bool.not_eq_false'] at h1
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      decide_eq_true_eq, List.isEmpty_iff] at hok h1
    obtain ⟨⟨⟨hy, hqb⟩, hall⟩, hinj⟩ := hok
    refine ⟨a, rfl, h1.1.1.1, h1.1.1.2, h1.1.2, hb0, hy, hqb, hinj, fun z hz ↦ ?_⟩
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz1, -⟩, -⟩, ho⟩, hx⟩, hl⟩, hwv⟩, hcls⟩, hw⟩ := hall z hz
    exact ⟨hz1, ho, hx, hl, hwv, hcls, c5a_FE_beq hw⟩
  | _ => simp at h

theorem c5a_termSum_eq (t : CTerm) (pt : List FE) :
    termSum t pt = ((List.range (2 ^ t.l)).map (termAt t pt)).sum := by
  unfold termSum
  rw [List.sum, List.foldr_map]

theorem c5a_termAt_member (t t0 : CTerm) (a : Aff) (q z : ℕ) (g : FK) (pt : List FE) (jf : ℕ)
    (ho : t.o = t0.o) (hx : t.x0 = t0.x0) (hwv : t.wv = []) (hc : t.cls = .aff ⟨a.y0 + z * 2 ^ q, a.coef⟩)
    (hw : t.w = t0.w * FE.ofK (g ^ z)) :
    termAt t pt jf = t0.w * FE.ofK (g ^ z) * ct_E pt t0.o (t0.x0 + jf) (a.at jf + z * 2 ^ q) := by
  unfold termAt CTerm.wAt CTerm.at Ent.idx ct_E
  rw [hwv, hc, hw, ho, hx]
  simp only [List.isEmpty_nil, ite_true, OpClass.at, Aff.at]
  rw [Nat.add_right_comm a.y0]

theorem c5a_run_sum (ts : Array CTerm) (i q b : ℕ) (g : FK) (pt : List FE) (h : geoOf ts i = some (q, b, g)) :
    ((List.range (2 ^ b)).map fun z ↦ termSum (ts.getD (i + z) default) pt).sum =
      ct_geoSum pt (ts.getD i default, q, b, g) := by
  obtain ⟨a, ha, -, -, -, -, -, -, -, hm⟩ := c5a_geoOf_some ts i q b g h
  unfold ct_geoSum
  simp only [ha, ct_affOf]
  refine congrArg List.sum (List.map_congr_left fun z hz ↦ ?_)
  obtain ⟨-, ho, hx, hl, hwv, hc, hw⟩ := hm z (List.mem_range.mp hz)
  rw [c5a_termSum_eq, hl]
  exact congrArg List.sum <| List.map_congr_left fun jf _ ↦ c5a_termAt_member _ _ a q z g pt jf ho hx hwv hc hw

theorem c5a_take_add {α : Type} [Inhabited α] (ts : Array α) (f : α → FE) (i : ℕ) :
    ∀ n, i + n ≤ ts.size → ((ts.toList.take (i + n)).map f).sum =
      ((ts.toList.take i).map f).sum + ((List.range n).map fun z ↦ f (ts.getD (i + z) default)).sum := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [← Nat.add_assoc, List.take_add_one, List.map_append, List.sum_append, ih (by omega), List.range_succ,
      List.map_append, List.sum_append, add_assoc]
    congr 2
    have hlt : i + n < ts.toList.length := by simp; omega
    rw [List.getElem?_eq_getElem hlt]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hlt)]

theorem c5a_termWF_of (t : CTerm) (h : termWFB t = true) : TermWF t := by
  simpa [termWFB, TermWF, and_assoc] using h

/-- **The geometric runs** (C5). -/
theorem ct_mergeGeo (pt : List FE) (ts : Array CTerm) (hwf : ∀ t ∈ ts, TermWF t) :
    (∀ t ∈ (mergeGeo ts).1, TermWF t) ∧ (∀ r ∈ (mergeGeo ts).2, ct_GeoOk r) ∧
      (ts.toList.map fun t ↦ termSum t pt).sum =
        ((mergeGeo ts).1.toList.map fun t ↦ termSum t pt).sum + ((mergeGeo ts).2.toList.map (ct_geoSum pt)).sum := by
  show (∀ t ∈ (forIn (m := Id) Lean.Loop.mk ((#[] : Array CTerm), (#[] : Array (CTerm × ℕ × ℕ × FK)), 0) _).1,
      TermWF t) ∧
    (∀ r ∈ (forIn (m := Id) Lean.Loop.mk ((#[] : Array CTerm), (#[] : Array (CTerm × ℕ × ℕ × FK)), 0) _).2.1,
      ct_GeoOk r) ∧ _
  refine c5a_loop (Q := fun (s : Array CTerm × Array (CTerm × ℕ × ℕ × FK) × ℕ) ↦ (∀ t ∈ s.1, TermWF t) ∧ (∀ r ∈ s.2.1, ct_GeoOk r) ∧
      (ts.toList.map fun t ↦ termSum t pt).sum =
        (s.1.toList.map fun t ↦ termSum t pt).sum + (s.2.1.toList.map (ct_geoSum pt)).sum) _
    (fun (s : Array CTerm × Array (CTerm × ℕ × ℕ × FK) × ℕ) ↦ s.2.2 ≤ ts.size ∧ (∀ t ∈ s.1, TermWF t) ∧ (∀ r ∈ s.2.1, ct_GeoOk r) ∧
      ((ts.toList.take s.2.2).map fun t ↦ termSum t pt).sum =
        (s.1.toList.map fun t ↦ termSum t pt).sum + (s.2.1.toList.map (ct_geoSum pt)).sum)
    (fun (s : Array CTerm × Array (CTerm × ℕ × ℕ × FK) × ℕ) ↦ ts.size - s.2.2) ?_ ?_ _ ?_
  · rintro ⟨rest, runs, i⟩ ⟨hi, hrest, hruns, hsum⟩ s' hf
    simp only at hf hi hrest hruns hsum
    by_cases hlt : i < ts.size
    · simp only [hlt, ↓reduceIte] at hf
      split at hf
      · rename_i q b g hg
        injection hf with hf
        subst hf
        obtain ⟨a, ha, hwv, hwfb, hlen, hb0, hy, hqb, hinj, hm⟩ := c5a_geoOf_some ts i q b g hg
        have hib : i + 2 ^ b ≤ ts.size := by
          have := (hm (2 ^ b - 1) (by have := Nat.one_le_two_pow (n := b); omega)).1
          have := Nat.one_le_two_pow (n := b); omega
        refine ⟨⟨hib, hrest, ?_, ?_⟩, ?_⟩
        · intro r hr
          rcases Array.mem_push.mp hr with hr | rfl
          · exact hruns r hr
          · exact ⟨a, ha, hwv, c5a_termWF_of _ hwfb, hlen, hinj, hy, hqb⟩
        · simp only
          rw [c5a_take_add ts _ i _ hib, hsum, c5a_run_sum ts i q b g pt hg, Array.toList_push, List.map_append,
            List.sum_append]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          ring
        · have := Nat.one_le_two_pow (n := b)
          simp only
          omega
      · injection hf with hf
        subst hf
        refine ⟨⟨hlt, ?_, hruns, ?_⟩, ?_⟩
        · intro t ht
          rcases Array.mem_push.mp ht with ht | rfl
          · exact hrest t ht
          · exact hwf _ (by rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]; exact Array.getElem_mem hlt)
        · simp only
          rw [c5a_take_add ts _ i 1 hlt, hsum, Array.toList_push, List.map_append, List.sum_append]
          simp only [List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          ring
        · simp only
          omega
    · simp only [hlt, ↓reduceIte] at hf
      cases hf
  · rintro ⟨rest, runs, i⟩ ⟨hi, hrest, hruns, hsum⟩ s' hf
    simp only at hf hi hrest hruns hsum
    by_cases hlt : i < ts.size
    · simp only [hlt, ↓reduceIte] at hf
      split at hf <;> cases hf
    · simp only [hlt, ↓reduceIte] at hf
      injection hf with hf
      subst hf
      have hi' : i = ts.size := by omega
      refine ⟨hrest, hruns, ?_⟩
      rw [← hsum, hi', ← Array.length_toList, List.take_length]
  · exact ⟨Nat.zero_le _, by simp, by simp, by simp⟩

/-! ## General helpers -/

/-- `FE`'s custom `==` is lawful. -/
instance c5b_lawfulBEq_FE : LawfulBEq FE where
  eq_of_beq {a b} h := by
    obtain ⟨a0, a1, a2⟩ := a
    obtain ⟨b0, b1, b2⟩ := b
    change (a0 == b0 && a1 == b1 && a2 == b2) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  rfl {a} := by
    obtain ⟨a0, a1, a2⟩ := a
    change (a0 == a0 && a1 == a1 && a2 == a2) = true
    simp

theorem c5b_while {β : Type} (f : Unit → β → Id (ForInStep β)) (μ : β → ℕ) (P Q : β → Prop)
    (h : ∀ b, P b → match (f () b).run with
      | .done b' => Q b'
      | .yield b' => P b' ∧ μ b' < μ b)
    (b : β) (hb : P b) : Q (forIn Lean.Loop.mk b f).run := by
  induction hm : μ b using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    have := h b hb
    rw [show forIn Lean.Loop.mk b f = Lean.Loop.forIn Lean.Loop.mk b f from rfl,
      Lean.Loop.forIn_eq_of_monadTail]
    revert this
    rcases hf : (f () b).run with b' | b' <;> intro this
    · simp only [Id.run] at hf ⊢; rw [hf]; exact this
    · simp only [Id.run] at hf ⊢; rw [hf]; exact ih _ (hm ▸ this.2) b' this.1 rfl

theorem c5b_forIn_list {α β : Type} (l : List α) (f : α → β → Id (ForInStep β)) (I : ℕ → β → Prop)
    (h : ∀ j (hj : j < l.length) b, I j b → ∃ b', f l[j] b = pure (.yield b') ∧ I (j + 1) b')
    (b : β) (hb : I 0 b) : I l.length (forIn l b f).run := by
  induction l generalizing I b with
  | nil => simpa using hb
  | cons a l ih =>
    obtain ⟨b', hb', hI⟩ := h 0 (by simp) b hb
    simp only [List.getElem_cons_zero] at hb'
    rw [List.forIn_cons, hb']
    exact ih (fun j b ↦ I (j + 1) b) (fun j hj b hb ↦ h (j + 1) (by simp; omega) b hb) b' hI

theorem c5b_sum_getD {α : Type} (a : Array α) (d : α) (f : α → FE) :
    (a.toList.map f).sum = ((List.range a.size).map fun j ↦ f (a.getD j d)).sum := by
  have : (List.range a.size).map (fun j ↦ a.getD j d) = a.toList := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_getElem (by simpa using h1)]
      rfl
  rw [← this, List.map_map]
  rfl

theorem c5b_foldr_sum (l : List ℕ) (f : ℕ → FE) :
    l.foldr (fun jf acc ↦ f jf + acc) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem c5b_termSum (t : CTerm) (pt : List FE) :
    termSum t pt = ((List.range (2 ^ t.l)).map fun jf ↦ t.wAt jf * ct_E pt t.o (t.x0 + jf) (t.cls.at jf)).sum := by
  unfold termSum
  rw [c5b_foldr_sum]
  rfl

theorem c5b_pairSum_none (pt : List FE) (t : CTerm) : ct_pairSum pt (t, none) = termSum t pt := by
  rw [c5b_termSum]
  rfl

theorem c5b_pow2 {d : ℕ} (h : isPow2 d = true) : 2 ^ log2 d = d := by
  unfold isPow2 at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨k, rfl⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo h.1).1 h.2
  simp [log2, Nat.log2_two_pow]

/-! ## The limb merge -/

theorem c5b_limbOf {t0 t1 t2 : CTerm} {e : ℕ} (h : limbOf t0 t1 t2 = some e) :
    t0.wv = [] ∧ t1.wv = [] ∧ t2.wv = [] ∧ t1.o = t0.o ∧ t2.o = t0.o ∧ t1.x0 = t0.x0 ∧ t2.x0 = t0.x0 ∧
      t1.l = t0.l ∧ t2.l = t0.l ∧ t1.w = t0.w * FE.y ∧ t2.w = t0.w * FE.y * FE.y ∧ e + 1 < yVars ∧
      ∀ jf < 2 ^ t0.l, (t0.cls.at jf >>> e) % 4 = 0 ∧ t1.cls.at jf = t0.cls.at jf + 2 ^ e ∧
        t2.cls.at jf = t0.cls.at jf + 2 * 2 ^ e := by
  unfold limbOf at h
  simp only at h
  split_ifs at h with h1 h2 h3
  obtain rfl : log2 (t1.cls.at 0 - t0.cls.at 0) = e := by simpa using h
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h1
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or, Bool.not_eq_false] at h2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range] at h3
  have hp := c5b_pow2 h2.2
  rw [hp]
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h01, h02⟩, h03⟩, -⟩, -⟩, -⟩, -⟩, ho1⟩, ho2⟩, hx1⟩, hx2⟩, hl1⟩, hl2⟩ := h1
  obtain ⟨⟨⟨⟨⟨he, hw1⟩, hw2⟩, -⟩, -⟩, hall⟩ := h3
  refine ⟨h01, h02, h03, ho1, ho2, hx1, hx2, hl1, hl2, hw1, hw2, he, fun jf hjf ↦ ?_⟩
  obtain ⟨⟨a, b⟩, c⟩ := hall jf hjf
  exact ⟨a, b, c⟩

theorem c5b_limb_sum (pt : List FE) {t0 t1 t2 : CTerm} {e : ℕ} (h : limbOf t0 t1 t2 = some e) :
    termSum t0 pt + termSum t1 pt + termSum t2 pt = ct_pairSum pt (t0, some e) := by
  obtain ⟨h01, h02, h03, ho1, ho2, hx1, hx2, hl1, hl2, hw1, hw2, -, hall⟩ := c5b_limbOf h
  rw [c5b_termSum, c5b_termSum, c5b_termSum, hl1, hl2, ← List.sum_map_add, ← List.sum_map_add]
  unfold ct_pairSum ct_EL
  congr 1
  apply List.map_congr_left
  intro jf hjf
  rw [List.mem_range] at hjf
  obtain ⟨-, hy1, hy2⟩ := hall jf hjf
  simp only [CTerm.wAt, h01, h02, h03, List.isEmpty_nil, ite_true, ho1, ho2, hx1, hx2, hw1, hw2, hy1, hy2]
  ring

theorem c5b_limb_ok {t0 t1 t2 : CTerm} {e : ℕ} (h : limbOf t0 t1 t2 = some e) : ct_LimOk t0 (some e) := by
  obtain ⟨h01, -, -, -, -, -, -, -, -, -, -, he, hall⟩ := c5b_limbOf h
  exact ⟨h01, he, fun jf hjf ↦ (hall jf hjf).1⟩

/-- **The limb merge** (C5). -/
theorem ct_mergeLimbs (pt : List FE) (ts : Array CTerm) (hwf : ∀ t ∈ ts, TermWF t) :
    (∀ p ∈ mergeLimbs ts, TermWF p.1 ∧ ct_LimOk p.1 p.2) ∧
      (ts.toList.map fun t ↦ termSum t pt).sum = ((mergeLimbs ts).toList.map (ct_pairSum pt)).sum := by
  have hmem : ∀ i < ts.size, ts.getD i default ∈ ts := fun i hi ↦ by
    simp [Array.getD_eq_getD_getElem?, hi]
  unfold mergeLimbs
  simp only [Id.run]
  refine c5b_while _ (fun s : Array (CTerm × Option ℕ) × ℕ ↦ ts.size - s.2)
    (fun s : Array (CTerm × Option ℕ) × ℕ ↦ s.2 ≤ ts.size ∧ (∀ p ∈ s.1, TermWF p.1 ∧ ct_LimOk p.1 p.2) ∧
      ((List.range s.2).map fun j ↦ termSum (ts.getD j default) pt).sum = (s.1.toList.map (ct_pairSum pt)).sum)
    (fun s : Array (CTerm × Option ℕ) × ℕ ↦ (∀ p ∈ s.1, TermWF p.1 ∧ ct_LimOk p.1 p.2) ∧
      (ts.toList.map fun t ↦ termSum t pt).sum = (s.1.toList.map (ct_pairSum pt)).sum) ?_ _ ?_
  · rintro ⟨out, i⟩ ⟨hi, hok, hsum⟩
    simp only at hi hok hsum ⊢
    by_cases hlt : i < ts.size
    · simp only [hlt, ite_true]
      generalize hm : (if i + 2 < ts.size then limbOf (ts.getD i default) (ts.getD (i + 1) default)
        (ts.getD (i + 2) default) else none) = r
      rcases r with _ | e
      · simp only [Id.run_pure]
        refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
        · intro p hp
          rw [Array.mem_push] at hp
          rcases hp with hp | rfl
          · exact hok p hp
          · exact ⟨hwf _ (hmem i hlt), trivial⟩
        · rw [Array.toList_push, List.map_append, List.sum_append, ← hsum]
          simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero, c5b_pairSum_none]
      · have h2 : i + 2 < ts.size := by
          by_contra hc; simp [hc] at hm
        simp only [h2, ite_true] at hm
        simp only [Id.run_pure]
        refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
        · intro p hp
          rw [Array.mem_push] at hp
          rcases hp with hp | rfl
          · exact hok p hp
          · exact ⟨hwf _ (hmem i hlt), c5b_limb_ok hm⟩
        · rw [Array.toList_push, List.map_append, List.sum_append, ← hsum]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rw [← c5b_limb_sum pt hm, show i + 3 = i + 1 + 1 + 1 by omega]
          simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero]
          ring
    · simp only [hlt, ite_false, Id.run_pure]
      refine ⟨hok, ?_⟩
      rw [← hsum, c5b_sum_getD ts default, show i = ts.size by omega]
  · exact ⟨Nat.zero_le _, by simp, by simp⟩

/-! ## The slot-run merge: algebra -/

theorem c5b_bits_sum (d : ℕ) : ∀ (k m : ℕ), m < 2 ^ k →
    ((List.range k).map fun j ↦ if m.testBit j then d * 2 ^ j else 0).sum = d * m := by
  intro k
  induction k with
  | zero => intro m hm; simp at hm; simp [hm]
  | succ k ih =>
    intro m hm
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have h2 : ((List.range k).map ((fun j ↦ if m.testBit j then d * 2 ^ j else 0) ∘ Nat.succ)) =
        (List.range k).map fun j ↦ 2 * (if (m / 2).testBit j then d * 2 ^ j else 0) := by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp, Nat.testBit_succ, Nat.succ_eq_add_one]
      split_ifs <;> ring
    rw [h2, List.sum_map_mul_left, ih (m / 2) (by rw [pow_succ] at hm; omega)]
    have hm2 : m = 2 * (m / 2) + m % 2 := (Nat.div_add_mod m 2).symm
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · simp only [Nat.testBit_zero, h, zero_ne_one, decide_false, Bool.false_eq_true, ite_false, zero_add]
      conv_rhs => rw [hm2, h]
      ring
    · simp only [Nat.testBit_zero, h, decide_true, ite_true, pow_zero, mul_one]
      conv_rhs => rw [hm2, h]
      ring

theorem c5b_aff_ext (y0 d k m jf L : ℕ) (coef : List ℕ) (hc : coef.length = L) (hm : m < 2 ^ k)
    (hjf : jf < 2 ^ L) :
    Aff.at ⟨y0, coef ++ (List.range k).map (d * 2 ^ ·)⟩ (2 ^ L * m + jf) = Aff.at ⟨y0 + m * d, coef⟩ jf := by
  subst hc
  unfold Aff.at
  simp only [List.length_append, List.length_map, List.length_range]
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  have h1 : (List.range coef.length).map (fun i ↦ if (2 ^ coef.length * m + jf).testBit i then
      (coef ++ (List.range k).map (d * 2 ^ ·)).getD i 0 else 0) =
      (List.range coef.length).map fun i ↦ if jf.testBit i then coef.getD i 0 else 0 := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [Nat.testBit_two_pow_mul_add m hjf]
    simp only [hi, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have h2 : (List.range k).map ((fun i ↦ if (2 ^ coef.length * m + jf).testBit i then
      (coef ++ (List.range k).map (d * 2 ^ ·)).getD i 0 else 0) ∘ (coef.length + ·)) =
      (List.range k).map fun j ↦ if m.testBit j then d * 2 ^ j else 0 := by
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    simp only [Function.comp, Nat.testBit_two_pow_mul_add m hjf, show ¬ coef.length + j < coef.length by omega,
      ite_false, Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (show coef.length ≤ coef.length + j by omega), List.getElem?_map,
      List.getElem?_range hj, Option.map_some, Option.getD_some]
  rw [h1, h2, c5b_bits_sum d k m hm]
  ring

theorem c5b_sum_split (N : ℕ) (F : ℕ → FE) : ∀ M : ℕ, ((List.range (N * M)).map F).sum =
    ((List.range M).map fun m ↦ ((List.range N).map fun jf ↦ F (N * m + jf)).sum).sum := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, List.range_add, List.map_append, List.sum_append, ih, List.range_succ, List.map_append,
      List.sum_append, List.map_map]
    simp [Function.comp_def]

/-- A term, well-formed with a constant weight: the members of a merged run. -/
theorem c5b_pairSum_merge (pt : List FE) (t : CTerm) (lim : Option ℕ) (k d y0 : ℕ) (coef : List ℕ)
    (hwv : t.wv = []) (hc : coef.length = t.l) (G : ℕ → CTerm)
    (hG : ∀ m < 2 ^ k, (G m).wv = [] ∧ (G m).l = t.l ∧ (G m).o = t.o ∧ (G m).w = t.w ∧
      (G m).x0 = t.x0 + m * 2 ^ t.l ∧ (G m).cls = .aff ⟨y0 + m * d, coef⟩) :
    ct_pairSum pt ({ t with l := t.l + k, cls := .aff ⟨y0, coef ++ (List.range k).map (d * 2 ^ ·)⟩ }, lim) =
      ((List.range (2 ^ k)).map fun m ↦ ct_pairSum pt (G m, lim)).sum := by
  unfold ct_pairSum
  simp only
  rw [pow_add, c5b_sum_split]
  congr 1
  apply List.map_congr_left
  intro m hm
  rw [List.mem_range] at hm
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hG m hm
  rw [h2]
  congr 1
  apply List.map_congr_left
  intro jf hjf
  rw [List.mem_range] at hjf
  simp only [CTerm.wAt, hwv, h1, List.isEmpty_nil, ite_true, h3, h4, h5, h6, OpClass.at]
  rw [c5b_aff_ext y0 d k m jf t.l coef hc hm hjf]
  congr 2
  ring

theorem c5b_merge_ok (t : CTerm) (lim : Option ℕ) (k d y0 : ℕ) (coef : List ℕ)
    (hwv : t.wv = []) (hc : coef.length = t.l) (G : ℕ → CTerm)
    (hG : ∀ m < 2 ^ k, (G m).wv = [] ∧ (G m).l = t.l ∧ (G m).o = t.o ∧ (G m).w = t.w ∧
      (G m).x0 = t.x0 + m * 2 ^ t.l ∧ (G m).cls = .aff ⟨y0 + m * d, coef⟩)
    (hGl : ∀ m < 2 ^ k, ct_LimOk (G m) lim) (ho : t.o < 4) (hx : t.x0 % 2 ^ (t.l + k) = 0)
    (hxl : t.x0 + 2 ^ (t.l + k) ≤ 2 ^ xVars) :
    TermWF { t with l := t.l + k, cls := .aff ⟨y0, coef ++ (List.range k).map (d * 2 ^ ·)⟩ } ∧
      ct_LimOk { t with l := t.l + k, cls := .aff ⟨y0, coef ++ (List.range k).map (d * 2 ^ ·)⟩ } lim := by
  refine ⟨⟨ho, hx, hxl⟩, ?_⟩
  cases lim with
  | none => trivial
  | some e =>
    refine ⟨hwv, (hGl 0 (by positivity)).2.1, fun jf' hjf' ↦ ?_⟩
    simp only at hjf' ⊢
    have hpos : 0 < 2 ^ t.l := by positivity
    have hm : jf' / 2 ^ t.l < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, Nat.add_comm]; exact hjf'
    have hj := Nat.div_add_mod jf' (2 ^ t.l)
    obtain ⟨h1, h2, -, -, -, h6⟩ := hG _ hm
    have := (hGl _ hm).2.2 (jf' % 2 ^ t.l) (by rw [h2]; exact Nat.mod_lt _ hpos)
    rw [h6] at this
    simp only [OpClass.at] at this ⊢
    rw [← hj, c5b_aff_ext y0 d k _ _ t.l coef hc hm (Nat.mod_lt _ hpos)]
    exact this

/-! ## The slot-run merge: the loops -/

/-- `runMerge`'s first loop (the buckets and the terms passed through). -/
def c5b_ph1 (ps : Array (CTerm × Option ℕ)) :
    Std.HashMap (ℕ × FE × ℕ × List ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ)) × Array (CTerm × Option ℕ) :=
  Id.run (forIn [0:ps.size] ((∅ : Std.HashMap (ℕ × FE × ℕ × List ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ))),
      (#[] : Array (CTerm × Option ℕ))) fun i r ↦ do
    let (t, lim) := ps.getD i default
    match t.cls with
    | .aff a =>
      if t.wv.isEmpty && termWFB t && a.coef.length == t.l then
        let key := (t.o, t.w, t.l, a.coef, lim)
        pure (ForInStep.yield (r.1.insert key ((r.1.getD key #[]).push (t.x0, a.y0, i)), r.2))
      else pure (ForInStep.yield (r.1, r.2.push (t, lim)))
    | _ => pure (ForInStep.yield (r.1, r.2.push (t, lim))))

/-- The words' step at position `i` of a sorted bucket. -/
def c5b_d (g : Array (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ := (g.getD (i + 1) (0, 0, 0)).2.1 - (g.getD i (0, 0, 0)).2.1

/-- `runMerge`'s `ok k` at position `i` of a sorted bucket. -/
def c5b_ok (ps : Array (CTerm × Option ℕ)) (g : Array (ℕ × ℕ × ℕ)) (i k : ℕ) : Bool :=
  (g.getD i (0, 0, 0)).1 % 2 ^ ((ps.getD (g.getD i (0, 0, 0)).2.2 default).1.l + k) == 0 &&
    i + 2 ^ k ≤ g.size &&
    (g.getD i (0, 0, 0)).1 + 2 ^ ((ps.getD (g.getD i (0, 0, 0)).2.2 default).1.l + k) ≤ 2 ^ xVars &&
    (List.range (2 ^ k)).all fun m ↦
      (g.getD (i + m) (0, 0, 0)).1 == (g.getD i (0, 0, 0)).1 + m * 2 ^ (ps.getD (g.getD i (0, 0, 0)).2.2 default).1.l &&
        (g.getD (i + m) (0, 0, 0)).2.1 ≥ (g.getD i (0, 0, 0)).2.1 &&
        (g.getD (i + m) (0, 0, 0)).2.1 == (g.getD i (0, 0, 0)).2.1 + m * c5b_d g i

/-- `runMerge`'s affine map at position `i` of a sorted bucket. -/
def c5b_a (ps : Array (CTerm × Option ℕ)) (g : Array (ℕ × ℕ × ℕ)) (i : ℕ) : Aff :=
  match (ps.getD (g.getD i (0, 0, 0)).2.2 default).1.cls with | .aff a => a | _ => default

/-- `runMerge`'s `k1 k` at position `i` of a sorted bucket. -/
def c5b_k1 (ps : Array (CTerm × Option ℕ)) (g : Array (ℕ × ℕ × ℕ)) (i k : ℕ) : Bool :=
  injOk (g.getD i (0, 0, 0)).2.1 ((c5b_a ps g i).coef ++ (List.range k).map (c5b_d g i * 2 ^ ·))

/-- The run's exponent `k` at position `i` of a sorted bucket. -/
def c5b_k (ps : Array (CTerm × Option ℕ)) (g : Array (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ :=
  ((List.range 13).reverse.find? fun k ↦ c5b_ok ps g i k && c5b_k1 ps g i k).getD 0

/-- The merged term at position `i` of a sorted bucket. -/
def c5b_merged (ps : Array (CTerm × Option ℕ)) (g : Array (ℕ × ℕ × ℕ)) (i : ℕ) : CTerm :=
  { (ps.getD (g.getD i (0, 0, 0)).2.2 default).1 with
    l := (ps.getD (g.getD i (0, 0, 0)).2.2 default).1.l + c5b_k ps g i,
    cls := .aff ⟨(g.getD i (0, 0, 0)).2.1,
      (c5b_a ps g i).coef ++ (List.range (c5b_k ps g i)).map (c5b_d g i * 2 ^ ·)⟩ }

/-- `runMerge`'s inner loop on one (sorted) bucket. -/
def c5b_inner (ps : Array (CTerm × Option ℕ)) (g : Array (ℕ × ℕ × ℕ)) (out0 : Array (CTerm × Option ℕ)) :
    Array (CTerm × Option ℕ) :=
  (Id.run (forIn Lean.Loop.mk (out0, 0) fun _ (r : Array (CTerm × Option ℕ) × ℕ) ↦
    if r.2 < g.size then
      if c5b_k ps g r.2 == 0 then
        pure (ForInStep.yield (r.1.push (ps.getD (g.getD r.2 (0, 0, 0)).2.2 default), r.2 + 2 ^ c5b_k ps g r.2))
      else
        pure (ForInStep.yield (r.1.push (c5b_merged ps g r.2, (ps.getD (g.getD r.2 (0, 0, 0)).2.2 default).2),
          r.2 + 2 ^ c5b_k ps g r.2))
    else pure (ForInStep.done r))).1

/-- `runMerge`'s second loop. -/
def c5b_ph2 (ps : Array (CTerm × Option ℕ))
    (grp : Std.HashMap (ℕ × FE × ℕ × List ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ))) (out0 : Array (CTerm × Option ℕ)) :
    Array (CTerm × Option ℕ) :=
  Id.run (forIn grp.toList out0 fun x r ↦
    pure (ForInStep.yield (c5b_inner ps (x.2.qsort fun a b ↦ a.1 < b.1) r)))

theorem c5b_runMerge_eq (ps : Array (CTerm × Option ℕ)) :
    runMerge ps = c5b_ph2 ps (c5b_ph1 ps).1 (c5b_ph1 ps).2 := rfl

theorem c5b_forIn_range {β : Type} (n : ℕ) (f : ℕ → β → Id (ForInStep β)) (I : ℕ → β → Prop)
    (h : ∀ j < n, ∀ b, I j b → ∃ b', f j b = pure (.yield b') ∧ I (j + 1) b') (b : β) (hb : I 0 b) :
    I n (forIn [0:n] b f).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have := c5b_forIn_list (List.range' 0 [0:n].size 1) f I (fun j hj b hb ↦ by
    simp only [List.length_range', Std.Legacy.Range.size] at hj
    rw [List.getElem_range']
    simpa using h j (by omega) b hb) b hb
  simpa [Std.Legacy.Range.size] using this

/-- A bucket entry `(x0, y0, ix)` of key `K = (o, w, l, coef, lim)`: term `ix` is affine with these data. -/
def c5b_Ent (ps : Array (CTerm × Option ℕ)) (K : ℕ × FE × ℕ × List ℕ × Option ℕ) (e : ℕ × ℕ × ℕ) : Prop :=
  ∃ t : CTerm, ps.getD e.2.2 default = (t, K.2.2.2.2) ∧ (t, K.2.2.2.2) ∈ ps ∧ t.cls = .aff ⟨e.2.1, K.2.2.2.1⟩ ∧
    t.x0 = e.1 ∧ t.o = K.1 ∧ t.w = K.2.1 ∧ t.l = K.2.2.1 ∧ t.wv = [] ∧ K.2.2.2.1.length = K.2.2.1

/-- The buckets' sum. -/
def c5b_G (f : ℕ × ℕ × ℕ → FE) (m : Std.HashMap (ℕ × FE × ℕ × List ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ))) : FE :=
  (m.toList.map fun kg ↦ (kg.2.toList.map f).sum).sum

theorem c5b_G_insert (f : ℕ × ℕ × ℕ → FE)
    (m : Std.HashMap (ℕ × FE × ℕ × List ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ))) (K : ℕ × FE × ℕ × List ℕ × Option ℕ)
    (e : ℕ × ℕ × ℕ) : c5b_G f (m.insert K ((m.getD K #[]).push e)) = c5b_G f m + f e := by
  unfold c5b_G
  have hP := Std.HashMap.toList_insert_perm (m := m) (k := K) (v := (m.getD K #[]).push e)
  rw [(hP.map _).sum_eq, List.map_cons, List.sum_cons]
  simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rcases hK : m[K]? with _ | g
  · have hd : m.getD K #[] = #[] := by simp [Std.HashMap.getD_eq_getD_getElem?, hK]
    rw [hd, List.filter_eq_self.2]
    · simp only [List.map_nil, List.sum_nil, zero_add]
      ring
    · intro x hx
      simp only [decide_eq_true_eq]
      intro hx1
      rw [beq_iff_eq] at hx1
      subst hx1
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some.1 hx] at hK
      simp at hK
  · have hd : m.getD K #[] = g := by simp [Std.HashMap.getD_eq_getD_getElem?, hK]
    have hE : m.Equiv (m.insert K g) := Std.HashMap.Equiv.of_forall_getElem?_eq fun k ↦ by
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i h; rw [beq_iff_eq] at h; subst h; exact hK
      · rfl
    have hQ := Std.HashMap.toList_insert_perm (m := m) (k := K) (v := g)
    rw [((hE.toList_perm.trans hQ).map _).sum_eq, List.map_cons, List.sum_cons, hd]
    ring

/-- Well-formed with a valid limb merge. -/
def c5b_Good (p : CTerm × Option ℕ) : Prop := TermWF p.1 ∧ ct_LimOk p.1 p.2

theorem c5b_find_getD {p : ℕ → Bool} {l : List ℕ} (h : (l.find? p).getD 0 ≠ 0) :
    p ((l.find? p).getD 0) = true := by
  rcases hf : l.find? p with _ | k
  · rw [hf] at h; exact absurd rfl h
  · simpa using List.find?_some hf

theorem c5b_ok_spec {ps : Array (CTerm × Option ℕ)} {g : Array (ℕ × ℕ × ℕ)} {i : ℕ} (hk : c5b_k ps g i ≠ 0) :
    (g.getD i (0, 0, 0)).1 % 2 ^ ((ps.getD (g.getD i (0, 0, 0)).2.2 default).1.l + c5b_k ps g i) = 0 ∧
      i + 2 ^ c5b_k ps g i ≤ g.size ∧
      (g.getD i (0, 0, 0)).1 + 2 ^ ((ps.getD (g.getD i (0, 0, 0)).2.2 default).1.l + c5b_k ps g i) ≤ 2 ^ xVars ∧
      ∀ m < 2 ^ c5b_k ps g i,
        (g.getD (i + m) (0, 0, 0)).1 = (g.getD i (0, 0, 0)).1 + m * 2 ^ (ps.getD (g.getD i (0, 0, 0)).2.2 default).1.l ∧
        (g.getD (i + m) (0, 0, 0)).2.1 = (g.getD i (0, 0, 0)).2.1 + m * c5b_d g i := by
  have h := c5b_find_getD (p := fun k ↦ c5b_ok ps g i k && c5b_k1 ps g i k) (l := (List.range 13).reverse) hk
  change (c5b_ok ps g i (c5b_k ps g i) && c5b_k1 ps g i (c5b_k ps g i)) = true at h
  rw [Bool.and_eq_true] at h
  have h' := h.1
  unfold c5b_ok at h'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  exact ⟨h1, h2, h3, fun m hm ↦ ⟨(h4 m hm).1.1, (h4 m hm).2⟩⟩

theorem c5b_getD_mem {α : Type} (g : Array α) (d : α) (i : ℕ) (h : i < g.size) : g.getD i d ∈ g := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem c5b_step0 (pt : List FE) (ps : Array (CTerm × Option ℕ)) (hwf : ∀ p ∈ ps, c5b_Good p)
    (K : ℕ × FE × ℕ × List ℕ × Option ℕ) (g : Array (ℕ × ℕ × ℕ)) (hg : ∀ e ∈ g, c5b_Ent ps K e) (i : ℕ)
    (hlt : i < g.size) (hk : (c5b_k ps g i == 0) = true) :
    i + 2 ^ c5b_k ps g i ≤ g.size ∧ c5b_Good (ps.getD (g.getD i (0, 0, 0)).2.2 default) ∧
      ct_pairSum pt (ps.getD (g.getD i (0, 0, 0)).2.2 default) =
        ((List.range (2 ^ c5b_k ps g i)).map fun m ↦ ct_pairSum pt (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default)).sum := by
  rw [beq_iff_eq] at hk
  rw [hk]
  obtain ⟨t, hpt, htm, -⟩ := hg _ (c5b_getD_mem g (0, 0, 0) i hlt)
  refine ⟨by simpa using hlt, by rw [hpt]; exact hwf _ htm, by simp⟩

theorem c5b_step1 (pt : List FE) (ps : Array (CTerm × Option ℕ)) (hwf : ∀ p ∈ ps, c5b_Good p)
    (K : ℕ × FE × ℕ × List ℕ × Option ℕ) (g : Array (ℕ × ℕ × ℕ)) (hg : ∀ e ∈ g, c5b_Ent ps K e) (i : ℕ)
    (hlt : i < g.size) (hk : ¬ (c5b_k ps g i == 0) = true) :
    i + 2 ^ c5b_k ps g i ≤ g.size ∧ c5b_Good (c5b_merged ps g i, (ps.getD (g.getD i (0, 0, 0)).2.2 default).2) ∧
      ct_pairSum pt (c5b_merged ps g i, (ps.getD (g.getD i (0, 0, 0)).2.2 default).2) =
        ((List.range (2 ^ c5b_k ps g i)).map fun m ↦ ct_pairSum pt (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default)).sum := by
  have hk' : c5b_k ps g i ≠ 0 := by simpa using hk
  obtain ⟨hx, hsz, hxl, hrun⟩ := c5b_ok_spec hk'
  obtain ⟨t, hpt, htm, hcls, htx, hto, htw, htl, hwv, hcl⟩ := hg _ (c5b_getD_mem g (0, 0, 0) i hlt)
  have hmerged : c5b_merged ps g i = { t with
      l := t.l + c5b_k ps g i
      cls := .aff ⟨(g.getD i (0, 0, 0)).2.1, K.2.2.2.1 ++ (List.range (c5b_k ps g i)).map (c5b_d g i * 2 ^ ·)⟩ } := by
    unfold c5b_merged c5b_a
    rw [hpt]
    simp only [hcls]
  rw [hpt] at hx hxl hrun ⊢
  rw [hmerged]
  simp only at hx hxl hrun ⊢
  generalize c5b_k ps g i = k at hsz hx hxl hrun ⊢
  have hc : K.2.2.2.1.length = t.l := by rw [hcl, htl]
  have hG : ∀ m < 2 ^ k, (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default).1.wv = [] ∧
      (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default).1.l = t.l ∧
      (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default).1.o = t.o ∧
      (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default).1.w = t.w ∧
      (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default).1.x0 = t.x0 + m * 2 ^ t.l ∧
      (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default).1.cls =
        .aff ⟨(g.getD i (0, 0, 0)).2.1 + m * c5b_d g i, K.2.2.2.1⟩ ∧
      (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default).2 = K.2.2.2.2 ∧
      c5b_Good (ps.getD (g.getD (i + m) (0, 0, 0)).2.2 default) := by
    intro m hm
    obtain ⟨tm, hptm, htmm, hclsm, htxm, htom, htwm, htlm, hwvm, -⟩ :=
      hg _ (c5b_getD_mem g (0, 0, 0) (i + m) (by have := hsz; have : m < 2 ^ k := hm; omega))
    obtain ⟨hrx, hry⟩ := hrun m hm
    rw [hptm]
    refine ⟨hwvm, by rw [htlm, htl], by rw [htom, hto], by rw [htwm, htw], ?_, ?_, rfl, hwf _ htmm⟩
    · rw [htxm, hrx, htx]
    · rw [hclsm, hry]
  have hgood := hwf _ htm
  refine ⟨hsz, ?_, ?_⟩
  · exact c5b_merge_ok t K.2.2.2.2 k (c5b_d g i) _ K.2.2.2.1 hwv hc _
      (fun m hm ↦ ⟨(hG m hm).1, (hG m hm).2.1, (hG m hm).2.2.1, (hG m hm).2.2.2.1, (hG m hm).2.2.2.2.1,
        (hG m hm).2.2.2.2.2.1⟩)
      (fun m hm ↦ by have := (hG m hm).2.2.2.2.2.2.2.2; rw [(hG m hm).2.2.2.2.2.2.1] at this; exact this)
      hgood.1.1 (by rw [htx]; exact hx) (by rw [htx]; exact hxl)
  · rw [c5b_pairSum_merge pt t K.2.2.2.2 k (c5b_d g i) _ K.2.2.2.1 hwv hc _
      (fun m hm ↦ ⟨(hG m hm).1, (hG m hm).2.1, (hG m hm).2.2.1, (hG m hm).2.2.2.1, (hG m hm).2.2.2.2.1,
        (hG m hm).2.2.2.2.2.1⟩)]
    congr 1
    apply List.map_congr_left
    intro m hm
    rw [List.mem_range] at hm
    rw [← (hG m hm).2.2.2.2.2.2.1]

theorem c5b_inner_spec (pt : List FE) (ps : Array (CTerm × Option ℕ)) (hwf : ∀ p ∈ ps, c5b_Good p)
    (K : ℕ × FE × ℕ × List ℕ × Option ℕ) (g : Array (ℕ × ℕ × ℕ)) (hg : ∀ e ∈ g, c5b_Ent ps K e)
    (out0 : Array (CTerm × Option ℕ)) (hout : ∀ p ∈ out0, c5b_Good p) :
    (∀ p ∈ c5b_inner ps g out0, c5b_Good p) ∧
      ((c5b_inner ps g out0).toList.map (ct_pairSum pt)).sum =
        (out0.toList.map (ct_pairSum pt)).sum + (g.toList.map fun e ↦ ct_pairSum pt (ps.getD e.2.2 default)).sum := by
  unfold c5b_inner
  refine c5b_while _ (fun r : Array (CTerm × Option ℕ) × ℕ ↦ g.size - r.2)
    (fun r : Array (CTerm × Option ℕ) × ℕ ↦ r.2 ≤ g.size ∧ (∀ p ∈ r.1, c5b_Good p) ∧
      (r.1.toList.map (ct_pairSum pt)).sum = (out0.toList.map (ct_pairSum pt)).sum +
        ((List.range r.2).map fun j ↦ ct_pairSum pt (ps.getD (g.getD j (0, 0, 0)).2.2 default)).sum)
    (fun r : Array (CTerm × Option ℕ) × ℕ ↦ (∀ p ∈ r.1, c5b_Good p) ∧
      (r.1.toList.map (ct_pairSum pt)).sum = (out0.toList.map (ct_pairSum pt)).sum +
        (g.toList.map fun e ↦ ct_pairSum pt (ps.getD e.2.2 default)).sum) ?_ _ ⟨Nat.zero_le _, hout, by simp⟩
  rintro ⟨out, i⟩ ⟨hi, hok, hsum⟩
  simp only at hi hok hsum ⊢
  by_cases hlt : i < g.size
  · simp only [hlt, ↓reduceIte]
    by_cases hk0 : (c5b_k ps g i == 0) = true
    · obtain ⟨hsz, hgd, hS⟩ := c5b_step0 pt ps hwf K g hg i hlt hk0
      simp only [hk0, ↓reduceIte, Id.run_pure]
      refine ⟨⟨hsz, ?_, ?_⟩, ?_⟩
      · intro p hp
        rw [Array.mem_push] at hp
        rcases hp with hp | rfl
        · exact hok p hp
        · exact hgd
      · rw [Array.toList_push, List.map_append, List.sum_append, hsum, List.range_add, List.map_append,
          List.sum_append, List.map_map]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hS, Function.comp_def]
        ring
      · have : 0 < 2 ^ c5b_k ps g i := by positivity
        omega
    · obtain ⟨hsz, hgd, hS⟩ := c5b_step1 pt ps hwf K g hg i hlt hk0
      simp only [hk0, Bool.false_eq_true, ↓reduceIte, Id.run_pure]
      refine ⟨⟨hsz, ?_, ?_⟩, ?_⟩
      · intro p hp
        rw [Array.mem_push] at hp
        rcases hp with hp | rfl
        · exact hok p hp
        · exact hgd
      · rw [Array.toList_push, List.map_append, List.sum_append, hsum, List.range_add, List.map_append,
          List.sum_append, List.map_map]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hS, Function.comp_def]
        ring
      · have : 0 < 2 ^ c5b_k ps g i := by positivity
        omega
  · simp only [hlt, ite_false, Id.run_pure]
    refine ⟨hok, ?_⟩
    rw [hsum, c5b_sum_getD g (0, 0, 0), show i = g.size by omega]

theorem c5b_ph2_spec (pt : List FE) (ps : Array (CTerm × Option ℕ)) (hwf : ∀ p ∈ ps, c5b_Good p)
    (grp : Std.HashMap (ℕ × FE × ℕ × List ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ)))
    (hgrp : ∀ K g, grp[K]? = some g → ∀ e ∈ g, c5b_Ent ps K e)
    (out0 : Array (CTerm × Option ℕ)) (hout : ∀ p ∈ out0, c5b_Good p) :
    (∀ p ∈ c5b_ph2 ps grp out0, c5b_Good p) ∧
      ((c5b_ph2 ps grp out0).toList.map (ct_pairSum pt)).sum =
        (out0.toList.map (ct_pairSum pt)).sum + c5b_G (fun e ↦ ct_pairSum pt (ps.getD e.2.2 default)) grp := by
  have h := c5b_forIn_list grp.toList
    (fun x r ↦ pure (ForInStep.yield (c5b_inner ps (x.2.qsort fun a b ↦ a.1 < b.1) r)))
    (fun j r ↦ (∀ p ∈ r, c5b_Good p) ∧ (r.toList.map (ct_pairSum pt)).sum = (out0.toList.map (ct_pairSum pt)).sum +
      ((grp.toList.take j).map fun kg ↦ (kg.2.toList.map fun e ↦ ct_pairSum pt (ps.getD e.2.2 default)).sum).sum)
    ?_ out0 ⟨hout, by simp⟩
  · rw [List.take_length] at h
    exact h
  · rintro j hj r ⟨hr, hs⟩
    refine ⟨_, rfl, ?_⟩
    have hmem : grp[grp.toList[j].1]? = some grp.toList[j].2 :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.1 (List.getElem_mem hj)
    have hperm := qs_qsort_perm grp.toList[j].2 (fun a b ↦ decide (a.1 < b.1))
    obtain ⟨h1, h2⟩ := c5b_inner_spec pt ps hwf grp.toList[j].1 _ (fun e he ↦ hgrp _ _ hmem e
      (by rw [← Array.mem_toList_iff, ← hperm.mem_iff, Array.mem_toList_iff]; exact he)) r hr
    refine ⟨h1, ?_⟩
    rw [h2, hs, List.take_add_one, List.getElem?_eq_getElem hj, (hperm.map _).sum_eq]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    ring

theorem c5b_ph1_spec (pt : List FE) (ps : Array (CTerm × Option ℕ)) (hwf : ∀ p ∈ ps, c5b_Good p) :
    (∀ p ∈ (c5b_ph1 ps).2, c5b_Good p) ∧ (∀ K g, (c5b_ph1 ps).1[K]? = some g → ∀ e ∈ g, c5b_Ent ps K e) ∧
      (ps.toList.map (ct_pairSum pt)).sum = ((c5b_ph1 ps).2.toList.map (ct_pairSum pt)).sum +
        c5b_G (fun e ↦ ct_pairSum pt (ps.getD e.2.2 default)) (c5b_ph1 ps).1 := by
  rw [c5b_sum_getD ps default]
  unfold c5b_ph1
  refine c5b_forIn_range ps.size _ (fun j (r : Std.HashMap (ℕ × FE × ℕ × List ℕ × Option ℕ) (Array (ℕ × ℕ × ℕ)) ×
      Array (CTerm × Option ℕ)) ↦ (∀ p ∈ r.2, c5b_Good p) ∧
      (∀ K g, r.1[K]? = some g → ∀ e ∈ g, c5b_Ent ps K e) ∧
      ((List.range j).map fun i ↦ ct_pairSum pt (ps.getD i default)).sum = (r.2.toList.map (ct_pairSum pt)).sum +
        c5b_G (fun e ↦ ct_pairSum pt (ps.getD e.2.2 default)) r.1) ?_ _ ⟨by simp, by simp, by simp [c5b_G]⟩
  rintro j hj ⟨grp, out⟩ ⟨hgood, hgrp, hsum⟩
  have hpj : ps.getD j default ∈ ps := c5b_getD_mem ps default j hj
  rcases hp : ps.getD j default with ⟨t, lim⟩
  rw [hp] at hpj
  have hsucc : ((List.range (j + 1)).map fun i ↦ ct_pairSum pt (ps.getD i default)).sum =
      ((List.range j).map fun i ↦ ct_pairSum pt (ps.getD i default)).sum + ct_pairSum pt (t, lim) := by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hp]
  have hpush : ((grp, out.push (t, lim)).2.toList.map (ct_pairSum pt)).sum +
      c5b_G (fun e ↦ ct_pairSum pt (ps.getD e.2.2 default)) (grp, out.push (t, lim)).1 =
      ((List.range (j + 1)).map fun i ↦ ct_pairSum pt (ps.getD i default)).sum := by
    rw [hsucc, hsum]
    simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    ring
  have hgood' : ∀ p ∈ (grp, out.push (t, lim)).2, c5b_Good p := by
    intro p hp'
    rcases Array.mem_push.1 hp' with hp' | rfl
    · exact hgood p hp'
    · exact hwf _ hpj
  rcases hc : t.cls with a | _ | _ | _
  · by_cases hcond : (t.wv.isEmpty && termWFB t && a.coef.length == t.l) = true
    · refine ⟨(grp.insert (t.o, t.w, t.l, a.coef, lim)
        ((grp.getD (t.o, t.w, t.l, a.coef, lim) #[]).push (t.x0, a.y0, j)), out), ?_, hgood, ?_, ?_⟩
      · simp only [hc, hcond, ↓reduceIte]
      · have hnew : c5b_Ent ps (t.o, t.w, t.l, a.coef, lim) (t.x0, a.y0, j) := by
          simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hcond
          exact ⟨t, hp, hpj, hc, rfl, rfl, rfl, rfl, hcond.1.1, hcond.2⟩
        intro K g hK e he
        simp only at hK
        rw [Std.HashMap.getElem?_insert] at hK
        split at hK
        · rename_i hKK
          rw [beq_iff_eq] at hKK
          subst hKK
          simp only [Option.some.injEq] at hK
          subst hK
          rcases Array.mem_push.1 he with he | rfl
          · rw [Std.HashMap.getD_eq_getD_getElem?] at he
            rcases hg0 : grp[(t.o, t.w, t.l, a.coef, lim)]? with _ | g0
            · rw [hg0] at he; simp at he
            · rw [hg0] at he; exact hgrp _ g0 hg0 e he
          · exact hnew
        · exact hgrp K g hK e he
      · simp only
        rw [c5b_G_insert, hsucc, hsum]
        simp only [hp]
        ring
    · refine ⟨(grp, out.push (t, lim)), ?_, hgood', hgrp, hpush.symm⟩
      simp only [hc, hcond, Bool.false_eq_true, ↓reduceIte]
  all_goals exact ⟨(grp, out.push (t, lim)), by simp only [hc], hgood', hgrp, hpush.symm⟩

/-- **The slot-run merge** (C5). -/
theorem ct_runMerge (pt : List FE) (ps : Array (CTerm × Option ℕ)) (hwf : ∀ p ∈ ps, TermWF p.1 ∧ ct_LimOk p.1 p.2) :
    (∀ p ∈ runMerge ps, TermWF p.1 ∧ ct_LimOk p.1 p.2) ∧
      (ps.toList.map (ct_pairSum pt)).sum = ((runMerge ps).toList.map (ct_pairSum pt)).sum := by
  obtain ⟨h1, h2, h3⟩ := c5b_ph1_spec pt ps hwf
  obtain ⟨h4, h5⟩ := c5b_ph2_spec pt ps hwf _ h2 _ h1
  rw [c5b_runMerge_eq]
  exact ⟨h4, by rw [h3, h5]⟩

/-! ## Black boxes requested from the lead (NEED) -/

/-! ## Bits -/

theorem c3_tb_add_mul (Y m e k : ℕ) (hY : (Y >>> e) % 2 ^ k = 0) (hm : m < 2 ^ k) (i : ℕ) :
    (Y + m * 2 ^ e).testBit i = if e ≤ i ∧ i < e + k then m.testBit (i - e) else Y.testBit i := by
  have hq : Y >>> e = 2 ^ k * (Y >>> e / 2 ^ k) := by
    have := Nat.div_add_mod (Y >>> e) (2 ^ k); omega
  have hYd : Y = 2 ^ e * (2 ^ k * (Y >>> e / 2 ^ k) + 0) + Y % 2 ^ e := by
    rw [add_zero, ← hq, Nat.shiftRight_eq_div_pow]; exact (Nat.div_add_mod Y (2 ^ e)).symm
  have hYm : Y + m * 2 ^ e = 2 ^ e * (2 ^ k * (Y >>> e / 2 ^ k) + m) + Y % 2 ^ e := by
    conv_lhs => rw [hYd]
    ring
  have hlt : Y % 2 ^ e < 2 ^ e := Nat.mod_lt _ (Nat.two_pow_pos e)
  rw [hYm]
  conv_rhs => rw [hYd]
  rw [Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow_mul_add _ hlt,
    Nat.testBit_two_pow_mul_add _ hm, Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos k)]
  by_cases h1 : i < e
  · simp [h1, show ¬ e ≤ i by omega]
  · by_cases h2 : i - e < k
    · simp [h1, h2, show e ≤ i ∧ i < e + k by omega]
    · simp [h1, h2, show ¬ (e ≤ i ∧ i < e + k) by omega]

theorem c3_tb_add_pow (x b : ℕ) (hx : x.testBit b = false) (c : Bool) (i : ℕ) :
    (x + if c then 2 ^ b else 0).testBit i = if i = b then c else x.testBit i := by
  have hY : (x >>> b) % 2 ^ 1 = 0 := by
    have : (x >>> b).testBit 0 = false := by rw [Nat.testBit_shiftRight]; simpa using hx
    simp only [Nat.testBit_zero, decide_eq_false_iff_not] at this
    omega
  have := c3_tb_add_mul x (if c then 1 else 0) b 1 hY (by split <;> simp) i
  rw [show (if c then 2 ^ b else 0) = (if c then 1 else 0) * 2 ^ b by split <;> simp, this]
  by_cases h : i = b
  · subst h
    have h1 : i ≤ i ∧ i < i + 1 := by omega
    simp only [h1, ↓reduceIte, Nat.sub_self]
    cases c <;> simp
  · have h1 : ¬ (b ≤ i ∧ i < b + 1) := by omega
    simp only [h1, h, ↓reduceIte]

/-! ## `eqOn` -/

theorem c3_eqOn_split (r : Array FE) (L : List ℕ) (p : ℕ → Bool) (v : ℕ) :
    ct_eqOn r L v = ct_eqOn r (L.filter p) v * ct_eqOn r (L.filter fun b ↦ !p b) v := by
  rw [← ct_eqOn_append, ct_eqOn_perm r (List.filter_append_perm p L)]

theorem c3_eqOn_nil (r : Array FE) (v : ℕ) : ct_eqOn r [] v = 1 := by simp [ct_eqOn]

theorem c3_eqOn_cons (r : Array FE) (b : ℕ) (L : List ℕ) (v : ℕ) :
    ct_eqOn r (b :: L) v = eq1 (r.getD b 0) (v.testBit b) * ct_eqOn r L v := by simp [ct_eqOn]

theorem c3_eqOn_list (r : Array FE) (l : List ℕ) (X : ℕ) :
    ∀ j, (∀ k < l.length, X.testBit (l.getD k 0) = j.testBit k) →
      ct_eqOn r l X = eqW (l.map fun b ↦ r.getD b 0) j := by
  induction l with
  | nil => intro j _; simp [ct_eqOn, eqW]
  | cons b l ih =>
    intro j h
    rw [c3_eqOn_cons, List.map_cons, eqW, ih (j / 2) (fun k hk ↦ by
      rw [Nat.testBit_div_two]; simpa using h (k + 1) (by simp; omega))]
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, Nat.testBit_zero] at h0
    rw [h0]
    by_cases hj : j % 2 = 1 <;> simp [eq1, hj]

theorem c3_eqOn_perm_ext (r : Array FE) (A B : List ℕ) (hA : A.Nodup) (hB : B.Nodup)
    (h : ∀ b, b ∈ A ↔ b ∈ B) (v : ℕ) : ct_eqOn r A v = ct_eqOn r B v :=
  ct_eqOn_perm r ((List.perm_ext_iff_of_nodup hA hB).mpr h) v

/-! ## `pext` -/

theorem c3_pextGo (v : ℕ) (l : List ℕ) : ∀ k, pextGo v k l = 2 ^ k * pextGo v 0 l := by
  induction l with
  | nil => intro k; simp [pextGo]
  | cons b l ih =>
    intro k
    simp only [pextGo]
    rw [ih (k + 1), ih 1]
    split <;> simp [Nat.shiftLeft_eq, pow_succ] <;> ring

theorem c3_pext_cons (v b : ℕ) (l : List ℕ) :
    pext v (b :: l) = 2 ^ 1 * pext v l + (if v.testBit b then 1 else 0) := by
  simp only [pext, pextGo]
  rw [c3_pextGo v l 1]
  split <;> (simp [Nat.shiftLeft_eq]; try ring)

theorem c3_pext_lt (v : ℕ) (l : List ℕ) : pext v l < 2 ^ l.length := by
  induction l with
  | nil => simp [pext, pextGo]
  | cons b l ih =>
    rw [c3_pext_cons]; simp only [List.length_cons, pow_succ]
    split <;> omega

theorem c3_pext_testBit (v : ℕ) (l : List ℕ) : ∀ k < l.length, (pext v l).testBit k = v.testBit (l.getD k 0) := by
  induction l with
  | nil => intro k hk; simp at hk
  | cons b l ih =>
    intro k hk
    rw [c3_pext_cons, Nat.testBit_two_pow_mul_add _ (by split <;> simp)]
    rcases k with _ | k
    · by_cases hb : v.testBit b <;> simp [hb]
    · simp only [show ¬ k + 1 < 1 by omega, ite_false, Nat.add_sub_cancel, List.getD_cons_succ]
      exact ih k (by simp at hk; omega)

/-! ## The `x` value of a member's step -/

/-- The `x` value of step `j` (as in `mkPass` and `ct_memSem`). -/
def c3_xx (xs : List ℕ) (x j : ℕ) : ℕ :=
  x + ((List.range xs.length).map fun k ↦ if j.testBit k then 2 ^ xs.getD k 0 else 0).sum

theorem c3_xx_cons (b : ℕ) (xs : List ℕ) (x j : ℕ) :
    c3_xx (b :: xs) x j = c3_xx xs (x + if j.testBit 0 then 2 ^ b else 0) (j / 2) := by
  simp only [c3_xx, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
    List.getD_cons_zero]
  rw [add_assoc]
  congr 3
  apply List.map_congr_left
  intro k _
  simp [Nat.testBit_div_two]

theorem c3_xx_bits (xs : List ℕ) (hnd : xs.Nodup) :
    ∀ x j, (∀ b ∈ xs, x.testBit b = false) →
      (∀ b, b ∉ xs → (c3_xx xs x j).testBit b = x.testBit b) ∧
      (∀ k < xs.length, (c3_xx xs x j).testBit (xs.getD k 0) = j.testBit k) := by
  induction xs with
  | nil => intro x j _; simp [c3_xx]
  | cons b xs ih =>
    intro x j hx
    rw [List.nodup_cons] at hnd
    have hxb : x.testBit b = false := hx b (by simp)
    have hx' : ∀ b' ∈ xs, (x + if j.testBit 0 then 2 ^ b else 0).testBit b' = false := by
      intro b' hb'
      rw [c3_tb_add_pow x b hxb]
      have : b' ≠ b := fun h ↦ hnd.1 (h ▸ hb')
      simp only [this, ↓reduceIte]
      exact hx b' (by simp [hb'])
    obtain ⟨ih1, ih2⟩ := ih hnd.2 _ (j / 2) hx'
    rw [c3_xx_cons]
    refine ⟨fun b' hb' ↦ ?_, fun k hk ↦ ?_⟩
    · simp only [List.mem_cons, not_or] at hb'
      rw [ih1 b' hb'.2, c3_tb_add_pow x b hxb]
      simp [hb'.1]
    · rcases k with _ | k
      · simp only [List.getD_cons_zero]
        rw [ih1 b hnd.1, c3_tb_add_pow x b hxb]
        simp
      · simp only [List.getD_cons_succ]
        rw [ih2 k (by simp at hk; omega), Nat.testBit_div_two]

theorem c3_xx_lt (xs : List ℕ) (hnd : xs.Nodup) (hlt : ∀ b ∈ xs, b < xVars) (x j : ℕ)
    (hx : ∀ b ∈ xs, x.testBit b = false) (hxv : x < 2 ^ xVars) : c3_xx xs x j < 2 ^ xVars := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [(c3_xx_bits xs hnd x j hx).1 i (fun h ↦ by have := hlt i h; omega)]
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hxv (Nat.pow_le_pow_right (by omega) hi))

theorem c3_xpart (r : Array FE) (xs : List ℕ) (hsort : xs.Pairwise (· < ·)) (hlt : ∀ b ∈ xs, b < xVars)
    (x j : ℕ) (hx : ∀ b ∈ xs, x.testBit b = false) :
    ct_eqOn r (List.range xVars) (c3_xx xs x j) =
      ct_eqOn r ((List.range xVars).filter fun b ↦ !xs.contains b) x * eqW (xs.map fun b ↦ r.getD b 0) j := by
  have hnd : xs.Nodup := hsort.imp (fun h ↦ Nat.ne_of_lt h)
  obtain ⟨h1, h2⟩ := c3_xx_bits xs hnd x j hx
  rw [c3_eqOn_split r _ (fun b ↦ xs.contains b), mul_comm]
  congr 1
  · apply ct_eqOn_congr
    intro b hb
    simp only [List.mem_filter, Bool.not_eq_true'] at hb
    exact h1 b (fun h ↦ by simp [h] at hb)
  · rw [c3_eqOn_perm_ext r _ xs ((List.nodup_range).filter _) hnd (fun b ↦ by
      simp only [List.mem_filter, List.mem_range, List.contains_iff_mem]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hlt b h, h⟩⟩)]
    exact c3_eqOn_list r xs _ j h2

/-! ## The `y` side -/

theorem c3_limb_split (r : Array FE) (y e m : ℕ) (he : e + 1 < yVars) (hy : (y >>> e) % 4 = 0) (hm : m < 4) :
    ct_eqOn r (List.range yVars) (y + m * 2 ^ e) =
      ct_eqOn r (ct_yFree [e, e + 1]) y * (eq1 (r.getD e 0) (m.testBit 0) * eq1 (r.getD (e + 1) 0) (m.testBit 1)) := by
  have hb := c3_tb_add_mul y m e 2 (by simpa using hy) (by simpa using hm)
  rw [c3_eqOn_split r _ (fun b ↦ [e, e + 1].contains b), mul_comm]
  congr 1
  · apply ct_eqOn_congr
    intro b hb'
    simp only [List.mem_filter, List.mem_range, Bool.not_eq_true'] at hb'
    rw [hb b]
    have : ¬ (e ≤ b ∧ b < e + 2) := by
      intro h
      have : b = e ∨ b = e + 1 := by omega
      rcases this with rfl | rfl <;> simp at hb'
    simp [this]
  · rw [c3_eqOn_perm_ext r _ [e, e + 1] ((List.nodup_range).filter _) (by simp) (fun b ↦ by
      simp only [List.mem_filter, List.mem_range, List.contains_iff_mem, List.mem_cons, List.not_mem_nil,
        or_false]
      omega)]
    simp only [c3_eqOn_cons, c3_eqOn_nil, mul_one, hb]
    simp

theorem c3_kerVal_lim (P : Pt) (lim : Option ℕ) :
    kerVal P (ct_limFs [] lim) = match lim with
      | none => 1
      | some e => limbVal (P.ry.getD e 0) (P.ry.getD (e + 1) 0) := by
  cases lim <;> simp [ct_limFs, kerVal, kfVal]

/-- The limb bits of a word are free. -/
def c3_limOk (lim : Option ℕ) (y : ℕ) : Prop :=
  match lim with
  | none => True
  | some e => e + 1 < yVars ∧ (y >>> e) % 4 = 0

/-- The atom of one entry, as `ct_addAtom` gives it for a point. -/
theorem c3_EL (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (o x y : ℕ) (lim : Option ℕ) (ho : o < 4)
    (hx : x < 2 ^ xVars) (hl : c3_limOk lim y) :
    ct_EL pt lim o x y = eqW (sub (Pt.ofList pt).kap 0 2) o * ct_eqOn (Pt.ofList pt).rx (List.range xVars) x *
      ct_eqOn (Pt.ofList pt).ry (ct_yFree (ct_limYm [] lim)) y * kerVal (Pt.ofList pt) (ct_limFs [] lim) := by
  rw [c3_kerVal_lim]
  cases lim with
  | none =>
    simp only [ct_EL, ct_E_split pt hpt o x y ho hx, ct_limYm, ct_yFree, List.contains_nil, Bool.not_false,
      List.filter_true, mul_one]
  | some e =>
    obtain ⟨he, hy⟩ := hl
    simp only [ct_EL, ct_E_split pt hpt o x _ ho hx, ct_limYm, List.nil_append]
    have h0 := c3_limb_split (Pt.ofList pt).ry y e 0 he hy (by omega)
    have h1 := c3_limb_split (Pt.ofList pt).ry y e 1 he hy (by omega)
    have h2 := c3_limb_split (Pt.ofList pt).ry y e 2 he hy (by omega)
    simp only [zero_mul, add_zero, one_mul] at h0 h1
    rw [h0, h1, h2]
    have t00 : Nat.testBit 0 0 = false := by decide
    have t01 : Nat.testBit 0 1 = false := by decide
    have t10 : Nat.testBit 1 0 = true := by decide
    have t11 : Nat.testBit 1 1 = false := by decide
    have t20 : Nat.testBit 2 0 = false := by decide
    have t21 : Nat.testBit 2 1 = true := by decide
    simp only [eq1, limbVal, t00, t01, t10, t11, t20, t21, Bool.false_eq_true, ↓reduceIte]
    ring

/-- The `y` bits a pass masks: the automaton's and the limb bits. -/
def c3_masked (n : ℕ) (lim : Option ℕ) (b : ℕ) : Bool :=
  b < n || (match lim with | some e => b == e || b == e + 1 | none => false)

/-- The finish bits. -/
def c3_free (n : ℕ) (lim : Option ℕ) : List ℕ := (List.range yVars).filter (!c3_masked n lim ·)

/-- The limb bits lie past the automaton's. -/
def c3_limLe (lim : Option ℕ) (n : ℕ) : Prop :=
  match lim with
  | none => True
  | some e => n ≤ e

theorem c3_ypart (r : Array FE) (n : ℕ) (lim : Option ℕ) (hn : n ≤ yVars) (hne : c3_limLe lim n) (Y : ℕ) :
    ct_eqOn r (ct_yFree (ct_limYm [] lim)) Y = eqW (sub r 0 n) (Y % 2 ^ n) * ct_eqOn r (c3_free n lim) Y := by
  unfold ct_yFree
  rw [c3_eqOn_split r _ (fun b ↦ decide (b < n))]
  congr 1
  · rw [ct_eqW_sub, c3_eqOn_perm_ext r _ (List.range n) (((List.nodup_range).filter _).filter _) List.nodup_range
      (fun b ↦ by
        cases lim <;> simp [ct_limYm, c3_limLe] at hne ⊢ <;> omega)]
    apply ct_eqOn_congr
    intro b hb
    simp only [List.mem_range] at hb
    simp [Nat.testBit_mod_two_pow, hb]
  · apply c3_eqOn_perm_ext r _ _ (((List.nodup_range).filter _).filter _) ((List.nodup_range).filter _)
    intro b
    cases lim <;> simp [ct_limYm, c3_masked, c3_limLe] at hne ⊢

/-! ## Folds -/

theorem c3_foldl_inv {α β : Type} (f : β → α → β) (P : β → Prop) (h : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro b hb; exact hb
  | cons a l ih => intro b hb; exact ih _ (h b a hb)

theorem c3_tab_pm (s : CS) (k : TKey) : (s.tab k).1.pm = s.pm := by
  unfold CS.tab; split <;> rfl

theorem c3_rangeKeys_pm (s : CS) (isX : Bool) (N cut : ℕ) (mask : ℕ → Bool) (v : ℕ) :
    (s.rangeKeys isX N cut mask v).1.pm = s.pm := by
  unfold CS.rangeKeys
  apply c3_foldl_inv _ (fun acc : CS × List (ℕ × ℕ) ↦ acc.1.pm = s.pm)
  · intro b a hb
    simp only
    rw [c3_tab_pm, hb]
  · rfl

theorem c3_addAtom_pm (s : CS) (fs : List KF) (o xm x : ℕ) (ym : List ℕ) (y : ℕ) (w : FE) (lim : Option ℕ) :
    (s.addAtom fs o xm x ym y w lim).pm = s.pm := by
  have hk : ∀ fs : List KF, (s.ker fs).1.pm = s.pm := fun fs ↦ by unfold CS.ker; split <;> rfl
  unfold CS.addAtom
  cases lim <;> simp only <;> rw [c3_rangeKeys_pm, c3_rangeKeys_pm] <;> split <;> simp [hk]

/-! ## The points branch -/

/-- `mkPass`'s points. -/
def c3_pts (s : CS) (xs : List ℕ) (R : ℕ) (lim : Option ℕ) (raw : Array (ℕ × ℕ × ℕ × FE)) : CS :=
  raw.foldl (fun s m ↦ (List.range (2 ^ xs.length)).foldl (fun s j ↦
    s.addAtom [] m.2.1 0 (c3_xx xs m.2.2.1 j) [] (m.1 + R * j) m.2.2.2 lim) s) s

theorem c3_pts_pm (s : CS) (xs : List ℕ) (R : ℕ) (lim : Option ℕ) (raw : Array (ℕ × ℕ × ℕ × FE)) :
    (c3_pts s xs R lim raw).pm = s.pm := by
  unfold c3_pts
  rw [← Array.foldl_toList]
  apply c3_foldl_inv _ (fun s' : CS ↦ s'.pm = s.pm) _ _ _ rfl
  intro b a hb
  apply c3_foldl_inv _ (fun s' : CS ↦ s'.pm = s.pm) _ _ _ hb
  intro b' j hb'
  rw [c3_addAtom_pm, hb']

theorem c3_pts_adds (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s)
    (xs : List ℕ) (R : ℕ) (lim : Option ℕ) (raw : Array (ℕ × ℕ × ℕ × FE))
    (hraw : ∀ m ∈ raw, ct_MemOk (xs, R, lim) m) :
    ct_Adds pt s (c3_pts s xs R lim raw) (raw.toList.map (ct_memSem pt (xs, R, lim))).sum := by
  unfold c3_pts
  rw [← Array.foldl_toList]
  refine ct_Adds_foldl pt _ (ct_memSem pt (xs, R, lim)) (ct_MemOk (xs, R, lim)) ?_ raw.toList s hs
    (fun m hm ↦ hraw m (Array.mem_toList_iff.mp hm))
  rintro s' ⟨st, o, x, w⟩ hs' ⟨ho, hsort, hlt, hxb, hxv, hlim⟩
  have hnd : xs.Nodup := hsort.imp (fun h ↦ Nat.ne_of_lt h)
  refine ct_Adds_foldl pt _ (fun j ↦ w * ct_EL pt lim o (c3_xx xs x j) (st + R * j)) (fun j ↦ j < 2 ^ xs.length)
    ?_ (List.range (2 ^ xs.length)) s' hs' (fun j hj ↦ List.mem_range.mp hj)
  intro s'' j hs'' hj
  refine ct_Adds_congr (ct_addAtom pt s'' hs'' [] o 0 (c3_xx xs x j) [] (st + R * j) w lim ho) ?_
  have hl : c3_limOk lim (st + R * j) := by
    cases lim with
    | none => trivial
    | some e => exact ⟨hlim.2.1, hlim.2.2 j hj⟩
  rw [c3_EL pt hpt o _ _ lim ho (c3_xx_lt xs hnd hlt x j hxb hxv) hl]
  have hxf : ct_xFree 0 = List.range xVars := by simp [ct_xFree]
  rw [hxf]
  ring

/-! ## The finish sum -/

theorem c3_finLoop (TL TH : Array FE) (bl bh : List ℕ)
    (body : ForInStep (FE × FE × ℕ) → ℕ × FE → Id (ForInStep (FE × FE × ℕ)))
    (hbody : ∀ b a, body (.yield b) a = pure (.yield (if pext a.1 bh = b.2.2 then
      (b.1, b.2.1 + a.2 * TL[pext a.1 bl]?.getD 0, b.2.2) else
      (b.1 + TH[b.2.2]?.getD 0 * b.2.1, a.2 * TL[pext a.1 bl]?.getD 0, pext a.1 bh))))
    (fs : Array (ℕ × FE)) (h0 : ℕ) :
    (ForInStep.value <$> Array.foldlM body (ForInStep.yield ((0 : FE), (0 : FE), h0)) fs).run.1 +
      TH[(ForInStep.value <$> Array.foldlM body (ForInStep.yield ((0 : FE), (0 : FE), h0)) fs).run.2.2]?.getD 0 *
        (ForInStep.value <$> Array.foldlM body (ForInStep.yield ((0 : FE), (0 : FE), h0)) fs).run.2.1 =
    (fs.toList.map fun cv ↦ cv.2 * (TL[pext cv.1 bl]?.getD 0 * TH[pext cv.1 bh]?.getD 0)).sum := by
  rw [← Array.foldlM_toList]
  generalize fs.toList = l
  suffices H : ∃ b, List.foldlM body (ForInStep.yield ((0 : FE), (0 : FE), h0)) l = pure (.yield b) ∧
      b.1 + TH[b.2.2]?.getD 0 * b.2.1 =
        (l.map fun cv ↦ cv.2 * (TL[pext cv.1 bl]?.getD 0 * TH[pext cv.1 bh]?.getD 0)).sum by
    obtain ⟨b, hb, he⟩ := H
    rw [hb]
    exact he
  induction l using List.reverseRecOn with
  | nil => exact ⟨_, rfl, by simp⟩
  | append_singleton l a ih =>
    obtain ⟨b, hb, he⟩ := ih
    refine ⟨_, by rw [List.foldlM_append, hb, pure_bind, List.foldlM_cons, hbody, pure_bind, List.foldlM_nil], ?_⟩
    rw [List.map_append, List.sum_append, ← he]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    split_ifs with hk
    · rw [hk]; ring
    · ring

theorem c3_foldl_sum (g : ℕ → FE) (l : List (ℕ × FE)) (c : FE) :
    l.foldl (fun acc (cv : ℕ × FE) ↦ acc + cv.2 * g cv.1) c = c + (l.map fun cv ↦ cv.2 * g cv.1).sum := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [ih]; ring

theorem la2_pextGo_run (v : ℕ) : ∀ (n b k : ℕ),
    pextGo v k ((List.range n).map (b + ·)) = 2 ^ k * ((v >>> b) % 2 ^ n) := by
  intro n
  induction n with
  | zero => intro b k; simp [pextGo, Nat.mod_one]
  | succ n ih =>
    intro b k
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have e : ((b + ·) ∘ Nat.succ) = ((b + 1) + ·) := by funext i; simp [Function.comp]; omega
    rw [e, pextGo, ih (b + 1) (k + 1), Nat.add_zero]
    have h1 : (v >>> b) % 2 ^ (n + 1) = (v >>> b) % 2 + 2 * ((v >>> (b + 1)) % 2 ^ n) := by
      rw [show v >>> (b + 1) = (v >>> b) / 2 by rw [Nat.shiftRight_succ]]
      rw [Nat.pow_succ', Nat.mod_mul, Nat.mul_comm 2]
    rw [h1, Nat.testBit, Nat.shiftLeft_eq, one_mul]
    rcases Nat.mod_two_eq_zero_or_one (v >>> b) with h | h <;> simp [h, Nat.one_and_eq_mod_two, pow_succ] <;> ring

theorem la2_pextR (bs : List ℕ) (v : ℕ) : pextR (runOf bs) (2 ^ bs.length - 1) v bs = pext v bs := by
  cases bs with
  | nil => simp [pextR, runOf, pext, pextGo]
  | cons b rest =>
    simp only [runOf]
    split_ifs with h
    · simp only [pextR]
      have h' := beq_iff_eq.1 h
      rw [Nat.and_two_pow_sub_one_eq_mod, pext, h', la2_pextGo_run]
      simp
    · rfl

theorem c3_finSum (T : Array (Array FE)) (p : Pass) (fs : Array (ℕ × FE)) :
    finSum T p fs = (fs.toList.map fun cv ↦ cv.2 * finVal T p cv.1).sum := by
  by_cases h2 : p.fin.size = 2
  · obtain ⟨xs, R, atoms, depth, ⟨fl⟩, limbE, code, fcode⟩ := p
    simp only [List.size_toArray] at h2
    match fl, h2 with
    | [(tl, bl), (th, bh)], _ =>
      simp only [finSum, finVal, la2_pextR, mulI_eq]
      simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, Array.getD_eq_getD_getElem?, Order.lt_two_iff, Std.le_refl, ↓reduceDIte,
        Array.getInternal_eq_getElem, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, bne_iff_ne,
        ne_eq, zero_le, ite_not, bind_pure_comp, Id.run_map, List.foldl_toArray', List.foldl_cons, one_mul,
        List.foldl_nil]
      rw [Array.forIn_eq_foldlM]
      refine c3_finLoop _ _ bl bh _ ?_ fs _
      intro b a
      simp only
      split_ifs <;> rfl
  · have h2' : (p.fin.size != 2) = true := by simpa using h2
    simp only [finSum, h2', ↓reduceIte, Id.run]
    show fs.foldl (fun acc (cv : ℕ × FE) ↦ acc + cv.2 * finVal T p cv.1) 0 = _
    rw [← Array.foldl_toList, c3_foldl_sum, zero_add]

/-! ## Merging keeps the state-weighted sums -/

theorem c3_drop1 (a : Atom) (h1 : (a.keys.getD 1 (0, 0)).1 = 1)
    (h2 : ∀ i, 2 ≤ i → (a.keys.getD i (0, 0)).1 = 0 → (a.keys.getD i (0, 0)).2 = 0) :
    ∀ k ∈ a.keys.toList.drop 1, k.1 = 0 → k.2 = 0 := by
  intro k hk hk0
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  rw [List.getElem_drop] at hk0 ⊢
  have hlt : 1 + i < a.keys.toList.length := by simp at hi ⊢; omega
  rw [← runs_getD_toList a _ hlt] at hk0 ⊢
  rcases i with _ | i
  · rw [h1] at hk0; exact absurd hk0 (by decide)
  · exact h2 _ (by omega) hk0

/-- The tables with table `0` replaced by `h` on `[0, N)`. -/
def c3_Th (T : Array (Array FE)) (h : ℕ → FE) (N : ℕ) : Array (Array FE) := T.set! 0 ((Array.range N).map h)

theorem c3_Th_ne (T : Array (Array FE)) (h : ℕ → FE) (N : ℕ) (k : ℕ × ℕ) (hk : k.1 ≠ 0) :
    keyVal (c3_Th T h N) k = keyVal T k := by
  simp [c3_Th, keyVal, Array.getElem?_setIfInBounds_ne (Ne.symm hk)]

theorem c3_Th_zero (T : Array (Array FE)) (h : ℕ → FE) (N : ℕ) (hT : 0 < T.size) (v : ℕ) (hv : v < N) :
    keyVal (c3_Th T h N) (0, v) = h v := by
  simp [c3_Th, keyVal, hT, hv]

theorem c3_atomVal_eq (T : Array (Array FE)) (a : Atom) : atomVal T a = runs_valFrom T 0 a := by
  unfold atomVal runs_valFrom
  rw [List.drop_zero, Array.foldl_toList]

theorem c3_foldl_prod (T : Array (Array FE)) (l : List (ℕ × ℕ)) (c : FE) :
    l.foldl (fun acc k ↦ acc * keyVal T k) c = c * (l.map (keyVal T)).prod := by
  induction l generalizing c with
  | nil => simp
  | cons k l ih => simp only [List.foldl_cons, List.map_cons, List.prod_cons]; rw [ih]; ring

theorem c3_foldl_congr (T T' : Array (Array FE)) (l : List (ℕ × ℕ)) (h : ∀ k ∈ l, keyVal T k = keyVal T' k)
    (c : FE) : l.foldl (fun acc k ↦ acc * keyVal T k) c = l.foldl (fun acc k ↦ acc * keyVal T' k) c := by
  rw [c3_foldl_prod, c3_foldl_prod, List.map_congr_left h]

theorem c3_atomVal_Th (T : Array (Array FE)) (hT : keyVal T (0, 0) = 1) (hTs : 0 < T.size) (h : ℕ → FE)
    (hh : h 0 = 1) (N : ℕ) (hN : 0 < N) (a : Atom) (hs : 0 < a.keys.size) (ha0 : (a.keys.getD 0 (0, 0)).1 = 0)
    (haN : (a.keys.getD 0 (0, 0)).2 < N) (hd : ∀ k ∈ a.keys.toList.drop 1, k.1 = 0 → k.2 = 0) :
    atomVal (c3_Th T h N) a = h (a.keys.getD 0 (0, 0)).2 * runs_valFrom T 1 a := by
  have hk0 : keyVal (c3_Th T h N) (a.keys.getD 0 (0, 0)) = h (a.keys.getD 0 (0, 0)).2 := by
    have : a.keys.getD 0 (0, 0) = (0, (a.keys.getD 0 (0, 0)).2) := Prod.ext ha0 rfl
    rw [this, c3_Th_zero T h N hTs _ haN]
  have hr : runs_valFrom (c3_Th T h N) 1 a = runs_valFrom T 1 a := by
    unfold runs_valFrom
    apply c3_foldl_congr
    intro k hk
    by_cases hk0 : k.1 = 0
    · have : k = (0, 0) := Prod.ext hk0 (hd k hk hk0)
      rw [this, c3_Th_zero T h N hTs 0 hN, hh, hT]
    · exact c3_Th_ne T h N k hk0
  rw [c3_atomVal_eq, runs_valFrom_succ _ _ _ hs, hk0, hr]

theorem c3_lin (l : List Atom) (V : Atom → FE) (f : Atom → ℕ) (g : ℕ → FE) :
    (l.map fun a ↦ V a * g (f a)).sum = (l.map fun a ↦ V a * (1 + g (f a) - g 0)).sum -
      (l.map fun a ↦ V a * 1).sum + g 0 * (l.map fun a ↦ V a * 1).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring

/-- The merged atoms' properties used by the pass. -/
theorem c3_merged (P : Pt) (T : Array (Array FE)) (hT : keyVal T (0, 0) = 1)
    (hk : ∀ m < 16, keyVal T (1, m) = ct_kapV P m) (as : Array Atom) (D : ℕ)
    (hD : ∀ a ∈ as, a.keys.size ≤ D)
    (hsel : ∀ a ∈ as, 2 ≤ a.keys.size ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧ (a.keys.getD 1 (0, 0)).2 < 16)
    (h0 : ∀ a ∈ as, (a.keys.getD 0 (0, 0)).1 = 0)
    (h2 : ∀ a ∈ as, ∀ i, 2 ≤ i → (a.keys.getD i (0, 0)).1 = 0 → (a.keys.getD i (0, 0)).2 = 0) :
    ∀ a ∈ mergeAtoms 1 (padTo D as), a.keys.size = D ∧ 0 < a.keys.size ∧
      (∃ b ∈ as, a.keys.getD 0 (0, 0) = b.keys.getD 0 (0, 0)) ∧ (a.keys.getD 0 (0, 0)).1 = 0 ∧
      ∀ k ∈ a.keys.toList.drop 1, k.1 = 0 → k.2 = 0 := by
  obtain ⟨hM1, -, -⟩ := ct_mergeAtoms P T hT hk as D hD hsel
  intro a ha
  obtain ⟨hsz, hl1, -, b, hb, hkeys⟩ := hM1 a ha
  refine ⟨hsz, ?_, ⟨b, hb, hkeys 0 (by decide)⟩, by rw [hkeys 0 (by decide)]; exact h0 b hb, ?_⟩
  · have := (hsel b hb).1; have := hD b hb; omega
  · apply c3_drop1 a hl1
    intro i hi
    rw [hkeys i (by omega)]
    exact h2 b hb i hi

theorem c3_merge_g (P : Pt) (T : Array (Array FE)) (hT : keyVal T (0, 0) = 1)
    (hk : ∀ m < 16, keyVal T (1, m) = ct_kapV P m) (as : Array Atom) (D : ℕ)
    (hD : ∀ a ∈ as, a.keys.size ≤ D)
    (hsel : ∀ a ∈ as, 2 ≤ a.keys.size ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧ (a.keys.getD 1 (0, 0)).2 < 16)
    (h0 : ∀ a ∈ as, (a.keys.getD 0 (0, 0)).1 = 0)
    (h2 : ∀ a ∈ as, ∀ i, 2 ≤ i → (a.keys.getD i (0, 0)).1 = 0 → (a.keys.getD i (0, 0)).2 = 0) (g : ℕ → FE) :
    ((mergeAtoms 1 (padTo D as)).toList.map fun a ↦ runs_valFrom T 1 a * g (a.keys.getD 0 (0, 0)).2).sum =
      (as.toList.map fun a ↦ runs_valFrom T 1 a * g (a.keys.getD 0 (0, 0)).2).sum := by
  have hM := c3_merged P T hT hk as D hD hsel h0 h2
  have hTs : 0 < T.size := by
    by_contra hc
    have : T.size = 0 := by omega
    simp [keyVal, Array.getElem?_eq_none (by omega : T.size ≤ 0)] at hT
  set N := (as.toList.map fun a ↦ (a.keys.getD 0 (0, 0)).2).sum + 1 with hN
  have hasN : ∀ b ∈ as, (b.keys.getD 0 (0, 0)).2 < N := by
    intro b hb
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun a : Atom ↦ (a.keys.getD 0 (0, 0)).2)
      (Array.mem_toList_iff.mpr hb))
    omega
  have key : ∀ h : ℕ → FE, h 0 = 1 →
      ((mergeAtoms 1 (padTo D as)).toList.map fun a ↦ runs_valFrom T 1 a * h (a.keys.getD 0 (0, 0)).2).sum =
        (as.toList.map fun a ↦ runs_valFrom T 1 a * h (a.keys.getD 0 (0, 0)).2).sum := by
    intro h hh
    have hT' : keyVal (c3_Th T h N) (0, 0) = 1 := by rw [c3_Th_zero T h N hTs 0 (by omega), hh]
    have hk' : ∀ m < 16, keyVal (c3_Th T h N) (1, m) = ct_kapV P m := fun m hm ↦ by
      rw [c3_Th_ne T h N _ (by simp)]; exact hk m hm
    obtain ⟨-, e, -⟩ := ct_mergeAtoms P (c3_Th T h N) hT' hk' as D hD hsel
    have eM : (mergeAtoms 1 (padTo D as)).toList.map (atomVal (c3_Th T h N)) =
        (mergeAtoms 1 (padTo D as)).toList.map fun a ↦ h (a.keys.getD 0 (0, 0)).2 * runs_valFrom T 1 a :=
      List.map_congr_left (fun a ha ↦ by
        obtain ⟨-, hs, ⟨b, hb, hab⟩, h0a, hd⟩ := hM a (Array.mem_toList_iff.mp ha)
        exact c3_atomVal_Th T hT hTs h hh N (by omega) a hs h0a (hab ▸ hasN b hb) hd)
    have eA : as.toList.map (atomVal (c3_Th T h N)) =
        as.toList.map fun a ↦ h (a.keys.getD 0 (0, 0)).2 * runs_valFrom T 1 a :=
      List.map_congr_left (fun a ha ↦ by
        have ha' := Array.mem_toList_iff.mp ha
        exact c3_atomVal_Th T hT hTs h hh N (by omega) a (by have := (hsel a ha').1; omega) (h0 a ha')
          (hasN a ha') (c3_drop1 a (hsel a ha').2.1 (h2 a ha')))
    rw [eM, eA] at e
    simpa only [mul_comm] using e
  rw [c3_lin _ _ (fun a ↦ (a.keys.getD 0 (0, 0)).2) g, c3_lin as.toList _ (fun a ↦ (a.keys.getD 0 (0, 0)).2) g,
    key (fun v ↦ 1 + g v - g 0) (by ring), key (fun _ ↦ 1) rfl]

/-! ## The pass branch: `mkPass`'s pieces -/

/-- The finish groups. -/
def c3_groups (n : ℕ) (lim : Option ℕ) : List (List ℕ) :=
  [(c3_free n lim).filter (· < yCut), (c3_free n lim).filter (· ≥ yCut)].filter (!·.isEmpty)

/-- A step of the finish tables' fold. -/
def c3_finStep (n : ℕ) (acc : CS × Array (ℕ × List ℕ)) (bs : List ℕ) : CS × Array (ℕ × List ℕ) :=
  let (s', t) := acc.1.tab (.eqy bs)
  (s', acc.2.push (t, bs.map (· - n)))

/-- The finish tables. -/
def c3_fin (s : CS) (n : ℕ) (G : List (List ℕ)) : CS × Array (ℕ × List ℕ) := G.foldl (c3_finStep n) (s, #[])

/-- A step of the members' fold. -/
def c3_memStep (xs : List ℕ) (acc : CS × Array Atom) (m : ℕ × ℕ × ℕ × FE) : CS × Array Atom :=
  match m with
  | (st, o, x, w) =>
    let (s', xk) := acc.1.rangeKeys true xVars xCut (fun b ↦ xs.contains b) x
    (s', acc.2.push ⟨(#[(0, st), (1, 1 <<< o)] ++ xk.reverse.toArray), w⟩)

/-- The members' atoms. -/
def c3_mem (s : CS) (xs : List ℕ) (raw : Array (ℕ × ℕ × ℕ × FE)) : CS × Array Atom :=
  raw.foldl (c3_memStep xs) (s, #[])

/-- The members' depth. -/
def c3_D (mem : Array Atom) : ℕ := mem.foldl (fun d a ↦ max d a.keys.size) 0

/-- The pass. -/
def c3_pass (xs : List ℕ) (R : ℕ) (lim : Option ℕ) (fin : Array (ℕ × List ℕ)) (mem : Array Atom) : Pass :=
  ⟨xs.toArray, R, mergeAtoms 1 (padTo (c3_D mem) mem), c3_D mem, fin, lim,
    initCodeG (mergeAtoms 1 (padTo (c3_D mem) mem)) (c3_D mem), none⟩

theorem c3_cases (s : CS) (xs : List ℕ) (R : ℕ) (lim : Option ℕ) (raw : Array (ℕ × ℕ × ℕ × FE)) :
    s.mkPass xs R lim raw = (c3_pts s xs R lim raw, none) ∨
    s.mkPass xs R lim raw =
      ((c3_mem (c3_fin s xs.length (c3_groups xs.length lim)).1 xs raw).1,
        some (c3_pass xs R lim (c3_fin s xs.length (c3_groups xs.length lim)).2
          (c3_mem (c3_fin s xs.length (c3_groups xs.length lim)).1 xs raw).2)) := by
  unfold CS.mkPass
  simp only
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem c3_fin_spec (n : ℕ) : ∀ (G : List (List ℕ)) (s0 : CS) (acc : Array (ℕ × List ℕ)), ct_WF s0 →
    (∀ bs ∈ G, ct_GrpOk yVars yCut bs) →
    ct_WF (G.foldl (c3_finStep n) (s0, acc)).1 ∧ ct_Le s0 (G.foldl (c3_finStep n) (s0, acc)).1 ∧
      (G.foldl (c3_finStep n) (s0, acc)).1.atoms = s0.atoms ∧ (G.foldl (c3_finStep n) (s0, acc)).1.pm = s0.pm ∧
      ∃ L : List (ℕ × List ℕ), L.map (·.2) = G ∧
        (G.foldl (c3_finStep n) (s0, acc)).2.toList = acc.toList ++ L.map (fun tb ↦ (tb.1, tb.2.map (· - n))) ∧
        ∀ tb ∈ L, (G.foldl (c3_finStep n) (s0, acc)).1.tabs[tb.1]? = some (.eqy tb.2) := by
  intro G
  induction G with
  | nil =>
    intro s0 acc hs _
    exact ⟨hs, ct_Le_refl s0, rfl, rfl, [], rfl, by simp, by simp⟩
  | cons bs G ih =>
    intro s0 acc hs hG
    obtain ⟨hw1, hle1, hat1, hpm1, -, -, htab1⟩ := ct_tab s0 hs (.eqy bs) (hG bs (by simp))
    rcases ht : s0.tab (.eqy bs) with ⟨s1, t⟩
    rw [ht] at hw1 hle1 hat1 hpm1 htab1
    have hstep : c3_finStep n (s0, acc) bs = (s1, acc.push (t, bs.map (· - n))) := by
      simp only [c3_finStep, ht]
    simp only [List.foldl_cons, hstep]
    obtain ⟨hw, hle, hat, hpm, L, hL, hfin, htabs⟩ :=
      ih s1 (acc.push (t, bs.map (· - n))) hw1 (fun b hb ↦ hG b (by simp [hb]))
    refine ⟨hw, ct_Le_trans hle1 hle, hat.trans hat1, hpm.trans hpm1, (t, bs) :: L, by simp [hL], ?_, ?_⟩
    · rw [hfin]; simp
    · intro tb htb
      simp only [List.mem_cons] at htb
      rcases htb with rfl | htb
      · exact hle.1 _ _ htab1
      · exact htabs tb htb

/-- A member and its atom. -/
def c3_MemRel (P : Pt) (xs : List ℕ) (s : CS) (m : ℕ × ℕ × ℕ × FE) (a : Atom) : Prop :=
  ∃ xk : List (ℕ × ℕ), a = ⟨#[(0, m.1), (1, 1 <<< m.2.1)] ++ xk.reverse.toArray, m.2.2.2⟩ ∧ (∀ k ∈ xk, 5 ≤ k.1) ∧
    ∀ T, ct_Cons P s T →
      (xk.map (keyVal T)).prod = ct_eqOn P.rx ((List.range xVars).filter fun b ↦ !xs.contains b) m.2.2.1

theorem c3_MemRel_mono (P : Pt) (xs : List ℕ) {s s' : CS} (h : ct_Le s s') (m : ℕ × ℕ × ℕ × FE) (a : Atom)
    (hr : c3_MemRel P xs s m a) : c3_MemRel P xs s' m a := by
  obtain ⟨xk, ha, h5, hv⟩ := hr
  exact ⟨xk, ha, h5, fun T hT ↦ hv T (ct_Cons_mono h hT)⟩

theorem c3_mem_spec (P : Pt) (xs : List ℕ) : ∀ (L : List (ℕ × ℕ × ℕ × FE)) (s0 : CS) (acc : Array Atom),
    ct_WF s0 →
    ct_WF (L.foldl (c3_memStep xs) (s0, acc)).1 ∧ ct_Le s0 (L.foldl (c3_memStep xs) (s0, acc)).1 ∧
      (L.foldl (c3_memStep xs) (s0, acc)).1.atoms = s0.atoms ∧ (L.foldl (c3_memStep xs) (s0, acc)).1.pm = s0.pm ∧
      ∃ l : List Atom, (L.foldl (c3_memStep xs) (s0, acc)).2.toList = acc.toList ++ l ∧
        List.Forall₂ (c3_MemRel P xs (L.foldl (c3_memStep xs) (s0, acc)).1) L l := by
  intro L
  induction L with
  | nil =>
    intro s0 acc hs
    exact ⟨hs, ct_Le_refl s0, rfl, rfl, [], by simp, List.Forall₂.nil⟩
  | cons m L ih =>
    intro s0 acc hs
    obtain ⟨st, o, x, w⟩ := m
    obtain ⟨hw1, hle1, hat1, hpm1, h51, hv1⟩ := ct_rangeKeysX P s0 hs (fun b ↦ xs.contains b) x
    rcases hr : s0.rangeKeys true xVars xCut (fun b ↦ xs.contains b) x with ⟨s1, xk⟩
    rw [hr] at hw1 hle1 hat1 hpm1 h51 hv1
    have hstep : c3_memStep xs (s0, acc) (st, o, x, w) =
        (s1, acc.push ⟨(#[(0, st), (1, 1 <<< o)] ++ xk.reverse.toArray), w⟩) := by
      simp only [c3_memStep, hr]
    simp only [List.foldl_cons, hstep]
    obtain ⟨hw, hle, hat, hpm, l, hl, hF⟩ := ih s1 (acc.push ⟨(#[(0, st), (1, 1 <<< o)] ++ xk.reverse.toArray), w⟩) hw1
    refine ⟨hw, ct_Le_trans hle1 hle, hat.trans hat1, hpm.trans hpm1,
      ⟨(#[(0, st), (1, 1 <<< o)] ++ xk.reverse.toArray), w⟩ :: l, by rw [hl]; simp, ?_⟩
    refine List.Forall₂.cons ?_ hF
    exact c3_MemRel_mono P xs hle _ _ ⟨xk, rfl, h51, hv1⟩

theorem c3_forall2_mem {α β : Type} (R : α → β → Prop) :
    ∀ (L : List α) (l : List β), List.Forall₂ R L l → ∀ b ∈ l, ∃ a ∈ L, R a b := by
  intro L l h
  induction h with
  | nil => intro b hb; simp at hb
  | cons hab _ ih =>
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨a, ha, h⟩ := ih b hb
      exact ⟨a, by simp [ha], h⟩

theorem c3_shl_lt (o : ℕ) (ho : o < 4) : 1 <<< o < 16 := by
  rw [Nat.shiftLeft_eq, one_mul]
  calc 2 ^ o < 2 ^ 4 := Nat.pow_lt_pow_right (by omega) ho
    _ = 16 := by norm_num

theorem c3_memAtom_keys (st q : ℕ) (xk : List (ℕ × ℕ)) :
    (#[(0, st), (1, q)] ++ xk.reverse.toArray) = ((0, st) :: (1, q) :: xk.reverse).toArray := by simp

theorem c3_memAtom_props (P : Pt) (xs : List ℕ) (s : CS) (m : ℕ × ℕ × ℕ × FE) (a : Atom)
    (hr : c3_MemRel P xs s m a) (ho : m.2.1 < 4) :
    2 ≤ a.keys.size ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧ (a.keys.getD 1 (0, 0)).2 < 16 ∧
      (a.keys.getD 0 (0, 0)).1 = 0 ∧ (a.keys.getD 0 (0, 0)).2 = m.1 ∧
      ∀ i, 2 ≤ i → (a.keys.getD i (0, 0)).1 = 0 → (a.keys.getD i (0, 0)).2 = 0 := by
  obtain ⟨xk, rfl, h5, -⟩ := hr
  simp only [c3_memAtom_keys, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.size_toArray,
    List.length_cons]
  refine ⟨by omega, by simp, by simpa using c3_shl_lt _ ho, by simp, by simp, ?_⟩
  intro i hi hi0
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  simp only [List.getElem?_cons_succ] at hi0 ⊢
  rcases hk : xk.reverse[i]? with _ | k
  · simp
  · rw [hk] at hi0
    have : k ∈ xk := List.mem_reverse.mp (List.mem_of_getElem? hk)
    have := h5 k this
    simp at hi0
    omega

theorem c3_forall2_sum (P : Pt) (xs : List ℕ) (s : CS) (T : Array (Array FE)) (hC : ct_Cons P s T)
    (G : ℕ → FE) : ∀ (L : List (ℕ × ℕ × ℕ × FE)) (l : List Atom), List.Forall₂ (c3_MemRel P xs s) L l →
      (∀ m ∈ L, m.2.1 < 4) →
      (l.map fun a ↦ runs_valFrom T 1 a * G (a.keys.getD 0 (0, 0)).2).sum =
        (L.map fun m ↦ m.2.2.2 * eqW (sub P.kap 0 2) m.2.1 *
          ct_eqOn P.rx ((List.range xVars).filter fun b ↦ !xs.contains b) m.2.2.1 * G m.1).sum := by
  intro L l h
  induction h with
  | nil => intro _; simp
  | @cons m a L l hr _ ih =>
    intro ho
    have ho' := ho m (by simp)
    have hhead : runs_valFrom T 1 a * G (a.keys.getD 0 (0, 0)).2 = m.2.2.2 * eqW (sub P.kap 0 2) m.2.1 *
        ct_eqOn P.rx ((List.range xVars).filter fun b ↦ !xs.contains b) m.2.2.1 * G m.1 := by
      obtain ⟨-, -, -, -, hst, -⟩ := c3_memAtom_props P xs s m a hr ho'
      rw [hst]
      obtain ⟨xk, rfl, -, hv⟩ := hr
      unfold runs_valFrom
      rw [c3_memAtom_keys]
      simp only [List.drop_succ_cons, List.drop_zero, List.foldl_cons]
      rw [c3_foldl_prod, List.map_reverse, List.prod_reverse, hv T hC, hC.2.1 _ (c3_shl_lt _ ho'),
        ct_kapV_single P _ ho']
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun m' hm' ↦ ho m' (by simp [hm'])), hhead]

/-! ## The finish value -/

theorem c3_prod_filter_ne (r : Array FE) (Y : ℕ) (l : List (List ℕ)) :
    ((l.filter (!·.isEmpty)).map fun bs ↦ ct_eqOn r bs Y).prod = (l.map fun bs ↦ ct_eqOn r bs Y).prod := by
  induction l with
  | nil => rfl
  | cons bs l ih =>
    rcases bs with _ | ⟨b, bs⟩
    · simp [ih, c3_eqOn_nil]
    · simp [ih]

theorem c3_groups_prod (r : Array FE) (n : ℕ) (lim : Option ℕ) (Y : ℕ) :
    ((c3_groups n lim).map fun bs ↦ ct_eqOn r bs Y).prod = ct_eqOn r (c3_free n lim) Y := by
  unfold c3_groups
  rw [c3_prod_filter_ne, c3_eqOn_split r (c3_free n lim) (fun b ↦ decide (b < yCut)) Y]
  have : (c3_free n lim).filter (fun b ↦ decide (b ≥ yCut)) = (c3_free n lim).filter fun b ↦ !decide (b < yCut) :=
    List.filter_congr (fun b _ ↦ by by_cases h : b < yCut <;> (simp [h]; try omega))
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, this]

theorem c3_groups_ge (n : ℕ) (lim : Option ℕ) : ∀ bs ∈ c3_groups n lim, ∀ b ∈ bs, n ≤ b ∧ b ∈ c3_free n lim := by
  intro bs hbs b hb
  unfold c3_groups at hbs
  simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hbs
  have hbf : b ∈ c3_free n lim := by
    rcases hbs.1 with rfl | rfl <;> exact (List.mem_filter.mp hb).1
  refine ⟨?_, hbf⟩
  unfold c3_free c3_masked at hbf
  simp only [List.mem_filter, Bool.not_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hbf
  omega

theorem c3_groups_grp (n : ℕ) (lim : Option ℕ) : ∀ bs ∈ c3_groups n lim, ct_GrpOk yVars yCut bs := by
  intro bs hbs
  unfold c3_groups at hbs
  simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hbs
  have hs : (c3_free n lim).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hlt : ∀ b ∈ c3_free n lim, b < yVars := fun b hb ↦ List.mem_range.mp (List.mem_filter.mp hb).1
  rcases hbs.1 with rfl | rfl
  · exact ⟨hs.filter _, Or.inl fun b hb ↦ by simpa using (List.mem_filter.mp hb).2⟩
  · exact ⟨hs.filter _, Or.inr fun b hb ↦ ⟨by simpa using (List.mem_filter.mp hb).2,
      hlt b (List.mem_filter.mp hb).1⟩⟩

theorem c3_finVal (P : Pt) (T : Array (Array FE)) (p : Pass) (n : ℕ) (lim : Option ℕ) (s : CS)
    (hC : ct_Cons P s T) (L : List (ℕ × List ℕ)) (hL : L.map (·.2) = c3_groups n lim)
    (hfin : p.fin.toList = L.map (fun tb ↦ (tb.1, tb.2.map (· - n))))
    (htabs : ∀ tb ∈ L, s.tabs[tb.1]? = some (.eqy tb.2)) (Y : ℕ) :
    finVal T p (Y / 2 ^ n) = ct_eqOn P.ry (c3_free n lim) Y := by
  have hfac : ∀ tb ∈ L, (T.getD tb.1 #[]).getD (pext (Y / 2 ^ n) (tb.2.map (· - n))) 0 = ct_eqOn P.ry tb.2 Y := by
    intro tb htb
    have hge : ∀ b ∈ tb.2, n ≤ b := fun b hb ↦
      (c3_groups_ge n lim tb.2 (hL ▸ List.mem_map_of_mem htb) b hb).1
    have hv := c3_pext_lt (Y / 2 ^ n) (tb.2.map (· - n))
    rw [List.length_map] at hv
    rw [show (T.getD tb.1 #[]).getD (pext (Y / 2 ^ n) (tb.2.map (· - n))) 0 =
      keyVal T (tb.1, pext (Y / 2 ^ n) (tb.2.map (· - n))) from rfl, hC.2.2.2.2 tb.1 tb.2 (htabs tb htb) _ hv]
    symm
    apply c3_eqOn_list
    intro k hk
    rw [c3_pext_testBit _ _ k (by simpa using hk), List.getD_eq_getElem _ _ hk,
      List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, Nat.testBit_div_two_pow,
      Nat.sub_add_cancel (hge _ (List.getElem_mem hk))]
  have hgen : ∀ L' : List (ℕ × List ℕ), (∀ tb ∈ L', tb ∈ L) → ∀ c : FE,
      (L'.map (fun tb ↦ (tb.1, tb.2.map (· - n)))).foldl
        (fun acc (tb : ℕ × List ℕ) ↦ acc * (T.getD tb.1 #[]).getD (pext (Y / 2 ^ n) tb.2) 0) c =
      c * (L'.map fun tb ↦ ct_eqOn P.ry tb.2 Y).prod := by
    intro L'
    induction L' with
    | nil => intro _ c; simp
    | cons tb L' ih =>
      intro hsub c
      simp only [List.map_cons, List.foldl_cons, List.prod_cons]
      rw [hfac tb (hsub tb (by simp)), ih (fun tb' h ↦ hsub tb' (by simp [h]))]
      ring
  unfold finVal
  rw [← Array.foldl_toList, hfin]
  rw [hgen L (fun _ h ↦ h) 1, one_mul, ← c3_groups_prod P.ry n lim Y, ← hL, List.map_map]
  rfl

/-! ## A member's value -/

/-- The automaton's sum from initial state `s` with finish `F` (`runAuto_eq`'s right side). -/
def c3_G (P : Pt) (xs : List ℕ) (R : ℕ) (F : ℕ → FE) (s : ℕ) : FE :=
  ((List.range (2 ^ xs.length)).map fun j ↦ eqW (xs.map fun i ↦ P.rx.getD i 0) j *
    eqW (sub P.ry 0 xs.length) ((s + R * j) % 2 ^ xs.length) * F ((s + R * j) / 2 ^ xs.length)).sum

theorem c3_len_le (xs : List ℕ) (hsort : xs.Pairwise (· < ·)) (hlt : ∀ b ∈ xs, b < xVars) : xs.length ≤ xVars := by
  have hnd : xs.Nodup := hsort.imp (fun h ↦ Nat.ne_of_lt h)
  have := (hnd.subperm (l₂ := List.range xVars) (fun b hb ↦ List.mem_range.mpr (hlt b hb))).length_le
  simpa using this

theorem c3_member (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (xs : List ℕ) (R : ℕ) (lim : Option ℕ)
    (F : ℕ → FE) (hF : ∀ Y, F (Y / 2 ^ xs.length) = ct_eqOn (Pt.ofList pt).ry (c3_free xs.length lim) Y)
    (m : ℕ × ℕ × ℕ × FE) (hm : ct_MemOk (xs, R, lim) m) :
    m.2.2.2 * eqW (sub (Pt.ofList pt).kap 0 2) m.2.1 *
        ct_eqOn (Pt.ofList pt).rx ((List.range xVars).filter fun b ↦ !xs.contains b) m.2.2.1 *
        c3_G (Pt.ofList pt) xs R F m.1 * kerVal (Pt.ofList pt) (ct_limFs [] lim) =
      ct_memSem pt (xs, R, lim) m := by
  obtain ⟨st, o, x, w⟩ := m
  obtain ⟨ho, hsort, hlt, hxb, hxv, hlim⟩ := hm
  simp only at ho hsort hlt hxb hxv hlim ⊢
  have hnd : xs.Nodup := hsort.imp (fun h ↦ Nat.ne_of_lt h)
  have hn : xs.length ≤ yVars := le_trans (c3_len_le xs hsort hlt) (by decide)
  have hne : c3_limLe lim xs.length := by
    cases lim with
    | none => trivial
    | some e => exact hlim.1
  set P := Pt.ofList pt with hP
  have hj : ∀ j ∈ List.range (2 ^ xs.length), w * ct_EL pt lim o (c3_xx xs x j) (st + R * j) =
      (w * eqW (sub P.kap 0 2) o * ct_eqOn P.rx ((List.range xVars).filter fun b ↦ !xs.contains b) x *
        kerVal P (ct_limFs [] lim)) *
      (eqW (xs.map fun i ↦ P.rx.getD i 0) j * eqW (sub P.ry 0 xs.length) ((st + R * j) % 2 ^ xs.length) *
        F ((st + R * j) / 2 ^ xs.length)) := by
    intro j hj
    have hl : c3_limOk lim (st + R * j) := by
      cases lim with
      | none => trivial
      | some e => exact ⟨hlim.2.1, hlim.2.2 j (List.mem_range.mp hj)⟩
    rw [c3_EL pt hpt o _ _ lim ho (c3_xx_lt xs hnd hlt x j hxb hxv) hl, c3_xpart P.rx xs hsort hlt x j hxb,
      c3_ypart P.ry xs.length lim hn hne, hF]
    ring
  rw [show ct_memSem pt (xs, R, lim) (st, o, x, w) =
    ((List.range (2 ^ xs.length)).map fun j ↦ w * ct_EL pt lim o (c3_xx xs x j) (st + R * j)).sum from rfl]
  unfold c3_G
  rw [List.map_congr_left hj, List.sum_map_mul_left]
  ring

/-! ## The pass branch -/

theorem c3_fin_spec' (s : CS) (hs : ct_WF s) (n : ℕ) (lim : Option ℕ) :
    ct_WF (c3_fin s n (c3_groups n lim)).1 ∧ ct_Le s (c3_fin s n (c3_groups n lim)).1 ∧
      (c3_fin s n (c3_groups n lim)).1.atoms = s.atoms ∧ (c3_fin s n (c3_groups n lim)).1.pm = s.pm ∧
      ∃ L : List (ℕ × List ℕ), L.map (·.2) = c3_groups n lim ∧
        (c3_fin s n (c3_groups n lim)).2.toList = L.map (fun tb ↦ (tb.1, tb.2.map (· - n))) ∧
        ∀ tb ∈ L, (c3_fin s n (c3_groups n lim)).1.tabs[tb.1]? = some (.eqy tb.2) := by
  obtain ⟨h1, h2, h3, h4, L, h5, h6, h7⟩ := c3_fin_spec n (c3_groups n lim) s #[] hs (c3_groups_grp n lim)
  have h6' : (c3_fin s n (c3_groups n lim)).2.toList =
      (#[] : Array (ℕ × List ℕ)).toList ++ L.map (fun tb ↦ (tb.1, tb.2.map (· - n))) := h6
  exact ⟨h1, h2, h3, h4, L, h5, by simpa using h6', h7⟩

theorem c3_mem_spec' (P : Pt) (xs : List ℕ) (s : CS) (hs : ct_WF s) (raw : Array (ℕ × ℕ × ℕ × FE)) :
    ct_WF (c3_mem s xs raw).1 ∧ ct_Le s (c3_mem s xs raw).1 ∧ (c3_mem s xs raw).1.atoms = s.atoms ∧
      (c3_mem s xs raw).1.pm = s.pm ∧
      List.Forall₂ (c3_MemRel P xs (c3_mem s xs raw).1) raw.toList (c3_mem s xs raw).2.toList := by
  unfold c3_mem
  rw [← Array.foldl_toList]
  obtain ⟨h1, h2, h3, h4, l, h5, h6⟩ := c3_mem_spec P xs raw.toList s #[] hs
  rw [h5]
  exact ⟨h1, h2, h3, h4, by simpa using h6⟩

theorem c3_lim_match (P : Pt) (lim : Option ℕ) (v : FE) :
    (match lim with
      | some e => v * limbVal (P.ry.getD e 0) (P.ry.getD (e + 1) 0)
      | none => v) = v * kerVal P (ct_limFs [] lim) := by
  rw [c3_kerVal_lim]; cases lim <;> simp

theorem c3_pass_value (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (xs : List ℕ) (R : ℕ)
    (lim : Option ℕ) (raw : Array (ℕ × ℕ × ℕ × FE)) (hraw : ∀ m ∈ raw, ct_MemOk (xs, R, lim) m)
    (fin : Array (ℕ × List ℕ)) (mem : Array Atom) (s1 s2 : CS) (hle : ct_Le s1 s2)
    (T : Array (Array FE)) (hT : ct_Cons (Pt.ofList pt) s2 T)
    (L : List (ℕ × List ℕ)) (hL : L.map (·.2) = c3_groups xs.length lim)
    (hfin : fin.toList = L.map (fun tb ↦ (tb.1, tb.2.map (· - xs.length))))
    (htabs : ∀ tb ∈ L, s1.tabs[tb.1]? = some (.eqy tb.2))
    (hF2 : List.Forall₂ (c3_MemRel (Pt.ofList pt) xs s2) raw.toList mem.toList) :
    runPass (Pt.ofList pt) T (c3_pass xs R lim fin mem) = (raw.toList.map (ct_memSem pt (xs, R, lim))).sum := by
  set P := Pt.ofList pt with hP
  set p := c3_pass xs R lim fin mem with hp
  set D := c3_D mem with hDdef
  have ho : ∀ m ∈ raw.toList, m.2.1 < 4 := fun m hm ↦ (hraw m (Array.mem_toList_iff.mp hm)).1
  have hmem : ∀ a ∈ mem, ∃ m ∈ raw.toList, c3_MemRel P xs s2 m a := fun a ha ↦
    c3_forall2_mem _ _ _ hF2 a (Array.mem_toList_iff.mpr ha)
  have hprops : ∀ a ∈ mem, 2 ≤ a.keys.size ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧ (a.keys.getD 1 (0, 0)).2 < 16 ∧
      (a.keys.getD 0 (0, 0)).1 = 0 ∧
      ∀ i, 2 ≤ i → (a.keys.getD i (0, 0)).1 = 0 → (a.keys.getD i (0, 0)).2 = 0 := by
    intro a ha
    obtain ⟨m, hm, hr⟩ := hmem a ha
    obtain ⟨h1, h2, h3, h4, -, h6⟩ := c3_memAtom_props P xs s2 m a hr (ho m hm)
    exact ⟨h1, h2, h3, h4, h6⟩
  have hsel : ∀ a ∈ mem, 2 ≤ a.keys.size ∧ (a.keys.getD 1 (0, 0)).1 = 1 ∧ (a.keys.getD 1 (0, 0)).2 < 16 :=
    fun a ha ↦ ⟨(hprops a ha).1, (hprops a ha).2.1, (hprops a ha).2.2.1⟩
  have h0m : ∀ a ∈ mem, (a.keys.getD 0 (0, 0)).1 = 0 := fun a ha ↦ (hprops a ha).2.2.2.1
  have h2m : ∀ a ∈ mem, ∀ i, 2 ≤ i → (a.keys.getD i (0, 0)).1 = 0 → (a.keys.getD i (0, 0)).2 = 0 :=
    fun a ha ↦ (hprops a ha).2.2.2.2
  have hDle : ∀ a ∈ mem, a.keys.size ≤ D := ct_le_foldl_max mem
  have hM := c3_merged P T hT.1 hT.2.1 mem D hDle hsel h0m h2m
  have hD' : ∀ a ∈ p.atoms, a.keys.size = p.depth := fun a ha ↦ (hM a ha).1
  have h0' : ∀ a ∈ p.atoms, ∀ k ∈ a.keys.toList.drop 1, k.1 = 0 → k.2 = 0 := fun a ha ↦ (hM a ha).2.2.2.2
  have hG : ∀ g : ℕ → FE, ((runCode T p.code).2.toList.Pairwise fun a b ↦ a.1 < b.1) ∧
      ((runCode T p.code).2.toList.map fun sv ↦ sv.2 * g sv.1).sum =
        (p.atoms.toList.map fun a ↦ runs_valFrom T 1 a * g (a.keys.getD 0 (0, 0)).2).sum :=
    greedy_initCodeG T p.atoms p.depth hD' hT.1 h0' (fun a ha ↦ (hM a ha).2.2.2.1)
  have hsrt : (runCode T p.code).2.toList.Pairwise fun a b ↦ a.1 < b.1 := (hG (fun _ ↦ 0)).1
  have hfv : ∀ Y, finVal T p (Y / 2 ^ xs.length) = ct_eqOn P.ry (c3_free xs.length lim) Y :=
    c3_finVal P T p xs.length lim s1 (ct_Cons_mono hle hT) L hL hfin htabs
  have hra : ((runAuto P xs.toArray R (runCode T p.code).2).toList.map fun cv ↦ cv.2 * finVal T p cv.1).sum =
      ((runCode T p.code).2.toList.map fun sv ↦ sv.2 * c3_G P xs R (finVal T p) sv.1).sum := by
    rw [runAuto_eq P xs.toArray R (runCode T p.code).2 hsrt (finVal T p)]
    simp only [List.size_toArray, c3_G]
  have hsum := (hG (c3_G P xs R (finVal T p))).2
  have hmg := c3_merge_g P T hT.1 hT.2.1 mem D hDle hsel h0m h2m (c3_G P xs R (finVal T p))
  have hfa := c3_forall2_sum P xs s2 T hT (c3_G P xs R (finVal T p)) raw.toList mem.toList hF2 ho
  have hfinal : finSum T p (runAuto P p.xs p.R (runCode T p.code).2) * kerVal P (ct_limFs [] lim) =
      (raw.toList.map (ct_memSem pt (xs, R, lim))).sum := by
    rw [c3_finSum]
    change ((runAuto P xs.toArray R (runCode T p.code).2).toList.map fun cv ↦ cv.2 * finVal T p cv.1).sum * _ = _
    rw [hra, hsum]
    change ((mergeAtoms 1 (padTo D mem)).toList.map fun a ↦
      runs_valFrom T 1 a * c3_G P xs R (finVal T p) (a.keys.getD 0 (0, 0)).2).sum * _ = _
    rw [hmg, hfa, ← List.sum_map_mul_right]
    apply congrArg List.sum
    apply List.map_congr_left
    intro m hm
    exact c3_member pt hpt xs R lim (finVal T p) hfv m (hraw m (Array.mem_toList_iff.mp hm))
  unfold runPass
  simp only
  rw [show p.limbE = lim from rfl]
  split
  · rw [← hfinal, c3_kerVal_lim]
  · rw [← hfinal, c3_kerVal_lim, mul_one]

/-! ## The target -/

/-- **A pass** (C3): the members become atoms (points) or one pass whose value is their sum. -/
theorem ct_mkPass (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s)
    (xs : List ℕ) (R : ℕ) (lim : Option ℕ) (raw : Array (ℕ × ℕ × ℕ × FE))
    (hraw : ∀ m ∈ raw, ct_MemOk (xs, R, lim) m) :
    ct_WF (s.mkPass xs R lim raw).1 ∧ ct_Le s (s.mkPass xs R lim raw).1 ∧
      (s.mkPass xs R lim raw).1.pm = s.pm ∧
      ∀ T, ct_Cons (Pt.ofList pt) (s.mkPass xs R lim raw).1 T →
        ct_aSum T (s.mkPass xs R lim raw).1 +
          (match (s.mkPass xs R lim raw).2 with
           | some p => runPass (Pt.ofList pt) T p
           | none => 0) =
        ct_aSum T s + (raw.toList.map (ct_memSem pt (xs, R, lim))).sum := by
  rcases c3_cases s xs R lim raw with h | h <;> rw [h]
  · obtain ⟨hw, hle, hv⟩ := c3_pts_adds pt hpt s hs xs R lim raw hraw
    have hpm := c3_pts_pm s xs R lim raw
    refine ⟨hw, hle, hpm, fun T hT ↦ ?_⟩
    have e := hv T hT
    have hps : ct_pmSum pt (c3_pts s xs R lim raw) = ct_pmSum pt s := by unfold ct_pmSum; rw [hpm]
    simp only [add_zero]
    rw [hps] at e
    exact add_right_cancel (e.trans (add_right_comm _ _ _))
  · obtain ⟨hw1, hle1, hat1, hpm1, L, hL, hfin, htabs⟩ := c3_fin_spec' s hs xs.length lim
    generalize c3_fin s xs.length (c3_groups xs.length lim) = fr at *
    obtain ⟨s1, fin⟩ := fr
    simp only at hw1 hle1 hat1 hpm1 hfin htabs ⊢
    obtain ⟨hw2, hle2, hat2, hpm2, hF2⟩ := c3_mem_spec' (Pt.ofList pt) xs s1 hw1 raw
    generalize c3_mem s1 xs raw = mr at *
    obtain ⟨s2, mem⟩ := mr
    simp only at hw2 hle2 hat2 hpm2 hF2 ⊢
    refine ⟨hw2, ct_Le_trans hle1 hle2, hpm2.trans hpm1, fun T hT ↦ ?_⟩
    have haS : ct_aSum T s2 = ct_aSum T s := by unfold ct_aSum; rw [hat2, hat1]
    rw [haS, c3_pass_value pt hpt xs R lim raw hraw fin mem s1 s2 hle2 T hT L hL hfin htabs hF2]

theorem c0a_final_get (s : CS) (hs : 5 ≤ s.tabs.size) (i : ℕ) :
    (((s.tabs.set! 2 (.ker s.kers)).set! 3 (.prod s.xm)).set! 4 (.prod s.ym))[i]? =
      if i = 4 then some (.prod s.ym) else if i = 3 then some (.prod s.xm) else if i = 2 then some (.ker s.kers)
      else s.tabs[i]? := by
  simp only [Array.set!, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  by_cases h4 : i = 4
  · subst h4; simp; omega
  by_cases h3 : i = 3
  · subst h3; simp; omega
  by_cases h2 : i = 2
  · subst h2; simp; omega
  simp [Ne.symm h4, Ne.symm h3, Ne.symm h2, h4, h3, h2]

/-- **The final tables are consistent** (C7, with the tables lemmas). -/
theorem ct_final_Cons (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) (s : CS) (hs : ct_WF s) :
    ct_Cons (Pt.ofList pt) s
      (tabsAt (Pt.ofList pt) (((s.tabs.set! 2 (.ker s.kers)).set! 3 (.prod s.xm)).set! 4 (.prod s.ym))) := by
  set rs := ((s.tabs.set! 2 (.ker s.kers)).set! 3 (.prod s.xm)).set! 4 (.prod s.ym) with hrs
  have hg := c0a_final_get s hs.size
  rw [← hrs] at hg
  have hof : ∀ (i : ℕ) (r : TRec), rs[i]? = some r → ∃ hi : i < rs.size, rs[i] = r :=
    fun i r h ↦ Array.getElem?_eq_some_iff.1 h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hi, h⟩ := hof 0 .one (by rw [hg]; simpa using hs.t0)
    simp [keyVal, tab_tabsAt_one _ rs 0 hi h]
  · intro m hm
    obtain ⟨hi, h⟩ := hof 1 .kap (by rw [hg]; simpa using hs.t1)
    simp only [keyVal, tab_tabsAt_kap _ rs 1 hi h]
    exact tab_kapTab_get _ m hm
  · intro i fs hfs
    obtain ⟨hi, h⟩ := hof 2 (.ker s.kers) (by rw [hg]; simp)
    simp [keyVal, tab_tabsAt_ker _ rs 2 hi _ h, Array.getD_eq_getD_getElem?, hfs]
  · intro t bits ht v hv
    obtain ⟨h5, hgrp⟩ := hs.eqx t bits ht
    obtain ⟨hi, h⟩ := hof t (.eqx bits) (by
      rw [hg]; simp only [show ¬ t = 4 by omega, show ¬ t = 3 by omega, show ¬ t = 2 by omega, ↓reduceIte]
      exact ht)
    unfold keyVal
    exact tab_tabsAt_eqx _ rs t hi bits h hgrp.1 hgrp.2 v hv
  · intro t bits ht v hv
    obtain ⟨h5, hgrp⟩ := hs.eqy t bits ht
    obtain ⟨hi, h⟩ := hof t (.eqy bits) (by
      rw [hg]; simp only [show ¬ t = 4 by omega, show ¬ t = 3 by omega, show ¬ t = 2 by omega, ↓reduceIte]
      exact ht)
    unfold keyVal
    exact tab_tabsAt_eqy _ rs t hi bits h hgrp.1 hgrp.2 v hv

/-- The pass fold's step (as `compileT` has it after `simp only [compileT]`). -/
def ct_pf (acc : CS × Array Pass) (x : (List ℕ × ℕ × Option ℕ) × Array (ℕ × ℕ × ℕ × FE)) : CS × Array Pass :=
  ((acc.1.mkPass x.1.1 x.1.2.1 x.1.2.2 x.2).1,
    match (acc.1.mkPass x.1.1 x.1.2.1 x.1.2.2 x.2).2 with
    | some p => acc.2.push p
    | none => acc.2)

/-- The pass fold (C7): every member is accounted for, by a pass or by atoms. -/
theorem ct_passFold (pt : List FE) (hpt : pt.length = 2 + xVars + yVars) :
    ∀ (L : List ((List ℕ × ℕ × Option ℕ) × Array (ℕ × ℕ × ℕ × FE))) (s : CS) (ps : Array Pass),
      ct_WF s → (∀ km ∈ L, ∀ m ∈ km.2, ct_MemOk km.1 m) →
      ct_WF (L.foldl ct_pf (s, ps)).1 ∧ ct_Le s (L.foldl ct_pf (s, ps)).1 ∧
        ∀ T, ct_Cons (Pt.ofList pt) (L.foldl ct_pf (s, ps)).1 T →
        ct_aSum T (L.foldl ct_pf (s, ps)).1 + ((L.foldl ct_pf (s, ps)).2.toList.map (runPass (Pt.ofList pt) T)).sum =
          ct_aSum T s + (ps.toList.map (runPass (Pt.ofList pt) T)).sum +
            (L.map fun km ↦ (km.2.toList.map (ct_memSem pt km.1)).sum).sum := by
  intro L
  induction L with
  | nil => intro s ps hs _; exact ⟨hs, ct_Le_refl s, fun T _ ↦ by simp⟩
  | cons km L ih =>
    intro s ps hs hL
    obtain ⟨⟨xs, R, lim⟩, raw⟩ := km
    obtain ⟨m1, m2, -, m4⟩ := ct_mkPass pt hpt s hs xs R lim raw (hL _ List.mem_cons_self)
    have hL' : ∀ km ∈ L, ∀ m ∈ km.2, ct_MemOk km.1 m := fun km hkm ↦ hL km (List.mem_cons_of_mem _ hkm)
    have hstep : ct_pf (s, ps) ((xs, R, lim), raw) = ((s.mkPass xs R lim raw).1,
        match (s.mkPass xs R lim raw).2 with | some p => ps.push p | none => ps) := rfl
    simp only [List.foldl_cons, hstep, List.map_cons, List.sum_cons]
    generalize s.mkPass xs R lim raw = q at m1 m2 m4 ⊢
    obtain ⟨q1, q2⟩ := q
    cases q2 with
    | none =>
      obtain ⟨i1, i2, i3⟩ := ih q1 ps m1 hL'
      refine ⟨i1, ct_Le_trans m2 i2, fun T hT ↦ ?_⟩
      have e1 := i3 T hT
      have e2 := m4 T (ct_Cons_mono i2 hT)
      simp only at e1 e2 ⊢
      linear_combination e1 + e2
    | some p =>
      obtain ⟨i1, i2, i3⟩ := ih q1 (ps.push p) m1 hL'
      refine ⟨i1, ct_Le_trans m2 i2, fun T hT ↦ ?_⟩
      have e1 := i3 T hT
      have e2 := m4 T (ct_Cons_mono i2 hT)
      simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero] at e1 e2 ⊢
      linear_combination e1 + e2

/-! ## The assembly -/

/-- `compileT`'s last step (LA2): the comp of the state and passes after the pass fold. -/
def la2_tail (r : CS × Array Pass) : Comp :=
  { tabs := ((r.1.tabs.set! 2 (.ker r.1.kers)).set! 3 (.prod r.1.xm)).set! 4 (.prod r.1.ym),
    atoms := mergeAtoms 1 (padTo (r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0) r.1.atoms),
    depth := r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0,
    passes := r.2.map (fun p ↦ { p with fcode := fuse (((r.1.tabs.set! 2 (.ker r.1.kers)).set! 3
      (.prod r.1.xm)).set! 4 (.prod r.1.ym)) p.code }),
    code := atomCodeG (mergeAtoms 1 (padTo (r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0) r.1.atoms))
      (r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0),
    fcode := fuse (((r.1.tabs.set! 2 (.ker r.1.kers)).set! 3 (.prod r.1.xm)).set! 4 (.prod r.1.ym))
      (atomCodeG (mergeAtoms 1 (padTo (r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0) r.1.atoms))
        (r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0)) }

/-- A pass with its fused initial code runs as the pass. -/
theorem la2_runPassF (P : Pt) (rs : Array TRec) (T : Array (Array FE)) (p : Pass) :
    runPassF P T (flatTabs rs T) { p with fcode := fuse rs p.code } = runPass P T p := by
  unfold runPassF runPass
  cases h : fuse rs p.code with
  | none => rfl
  | some fc => simp only [runF_fuse rs T p.code fc h]; rfl

/-- The tail's value: the atoms' code plus the passes, fused or not. -/
theorem la2_evalC_tail (pt : List FE) (r : CS × Array Pass) :
    evalC (la2_tail r) pt =
      (runCode (tabsAt (Pt.ofList pt) (((r.1.tabs.set! 2 (.ker r.1.kers)).set! 3 (.prod r.1.xm)).set! 4
        (.prod r.1.ym))) (atomCodeG (mergeAtoms 1 (padTo (r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0)
          r.1.atoms)) (r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0))).1 +
      (r.2.toList.map (runPass (Pt.ofList pt) (tabsAt (Pt.ofList pt) (((r.1.tabs.set! 2 (.ker r.1.kers)).set! 3
        (.prod r.1.xm)).set! 4 (.prod r.1.ym))))).sum := by
  unfold evalC la2_tail
  simp only
  generalize ((r.1.tabs.set! 2 (.ker r.1.kers)).set! 3 (.prod r.1.xm)).set! 4 (.prod r.1.ym) = rs
  generalize atomCodeG (mergeAtoms 1 (padTo (r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0) r.1.atoms))
    (r.1.atoms.foldl (fun d a ↦ max d a.keys.size) 0) = code
  suffices H : ∀ a0 : FE, Array.foldl (fun acc p ↦ acc + runPassF (Pt.ofList pt) (tabsAt (Pt.ofList pt) rs)
      (flatTabs rs (tabsAt (Pt.ofList pt) rs)) p) a0 (r.2.map fun p ↦ { p with fcode := fuse rs p.code }) =
      a0 + (r.2.toList.map (runPass (Pt.ofList pt) (tabsAt (Pt.ofList pt) rs))).sum by
    rcases h : fuse rs code with _ | fc
    · exact H _
    · simp only [runF_fuse rs _ code fc h]; exact H _
  intro a0
  rw [← Array.foldl_toList, Array.toList_map, List.foldl_map]
  simp only [la2_runPassF]
  induction r.2.toList generalizing a0 with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]; ring

/-- **The compiler is exact** (statement): on well-formed terms, the compiled evaluator is the terms' sum at
every point of `phiVars` coordinates. Owner L-A. -/
theorem compileT_eq (ts : Array CTerm) (hwf : ∀ t ∈ ts, TermWF t) (pt : List FE)
    (hpt : pt.length = 2 + xVars + yVars) :
    evalC (compileT ts) pt = (ts.toList.map fun t ↦ termSum t pt).sum := by
  obtain ⟨h1wf, h1geo, h1sum⟩ := ct_mergeGeo pt ts hwf
  rcases hg : mergeGeo ts with ⟨rest, geos⟩
  rw [hg] at h1wf h1geo h1sum
  obtain ⟨h3wf, h3sum⟩ := ct_mergeLimbs pt rest h1wf
  obtain ⟨h4wf, h4sum⟩ := ct_runMerge pt (mergeLimbs rest) h3wf
  have A2 := ct_Adds_foldl pt CS.addGeo (ct_geoSum pt) ct_GeoOk
    (fun s r hs hr ↦ ct_addGeo pt hpt s hs r hr) geos.toList {} ct_WF_empty
    (fun r hr ↦ h1geo r (Array.mem_toList_iff.mp hr))
  rw [Array.foldl_toList] at A2
  have A3 := ct_Adds_foldl pt (fun s (p : CTerm × Option ℕ) ↦ s.addTerm p.1 p.2) (ct_pairSum pt)
    (fun p ↦ TermWF p.1 ∧ ct_LimOk p.1 p.2) (fun s p hs hp ↦ ct_addTerm pt hpt s hs p.1 p.2 hp.1 hp.2)
    (runMerge (mergeLimbs rest)).toList _ A2.1
    (fun p hp ↦ h4wf p (Array.mem_toList_iff.mp hp))
  rw [Array.foldl_toList] at A3
  simp only [compileT, hg]
  generalize hs2 : geos.foldl CS.addGeo ({} : CS) = s2 at A2 A3
  generalize hs3 : (runMerge (mergeLimbs rest)).foldl (fun s (p : CTerm × Option ℕ) ↦ s.addTerm p.1 p.2) s2 = s3
    at A3 ⊢
  have hmem : ∀ km ∈ s3.pm.toList, ∀ m ∈ km.2, ct_MemOk km.1 m := by
    intro km hkm m hm
    exact A3.1.pm km.1 km.2 (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hkm) m hm
  have A4 := ct_passFold pt hpt s3.pm.toList s3 #[] A3.1 hmem
  change evalC (la2_tail (s3.pm.toList.foldl ct_pf (s3, #[]))) pt = _
  generalize hr : s3.pm.toList.foldl ct_pf (s3, #[]) = r at A4 ⊢
  obtain ⟨s4, ps⟩ := r
  simp only at A4 ⊢
  obtain ⟨hwf4, hle4, hv4⟩ := A4
  set D := s4.atoms.foldl (fun d a ↦ max d a.keys.size) 0 with hD
  set T := tabsAt (Pt.ofList pt) (((s4.tabs.set! 2 (.ker s4.kers)).set! 3 (.prod s4.xm)).set! 4 (.prod s4.ym)) with hT
  have hC4 : ct_Cons (Pt.ofList pt) s4 T := ct_final_Cons pt hpt s4 hwf4
  have hC3 : ct_Cons (Pt.ofList pt) s3 T := ct_Cons_mono hle4 hC4
  have hC2 : ct_Cons (Pt.ofList pt) s2 T := ct_Cons_mono A3.2.1 hC3
  obtain ⟨hma1, hma2, -⟩ := ct_mergeAtoms (Pt.ofList pt) T hC4.1 hC4.2.1 s4.atoms D (ct_le_foldl_max s4.atoms)
    (fun a ha ↦ ⟨(hwf4.atoms a ha).1, (hwf4.atoms a ha).2.1, (hwf4.atoms a ha).2.2.1⟩)
  have h0 := ct_mergeAtoms_h0 s4.atoms D hwf4.atoms hma1
  have hcode : (runCode T (atomCodeG (mergeAtoms 1 (padTo D s4.atoms)) D)).1 = ct_aSum T s4 := by
    rw [runCode_atomCodeG T _ D (fun a ha ↦ (hma1 a ha).1) hC4.1 h0, hma2]
    rfl
  have hev : evalC (la2_tail (s4, ps)) pt = ct_aSum T s4 + (ps.toList.map (runPass (Pt.ofList pt) T)).sum := by
    rw [la2_evalC_tail, ← hT, ← hD, hcode]
  rw [hev, hv4 T hC4]
  have e3 := A3.2.2 T hC3
  have e2 := A2.2.2 T hC2
  simp only [ct_aSum_empty, ct_pmSum_empty, zero_add] at e2
  have hpm : ct_pmSum pt s3 = (s3.pm.toList.map fun km ↦ (km.2.toList.map (ct_memSem pt km.1)).sum).sum := rfl
  rw [h1sum, h3sum, h4sum]
  simp only [List.map_nil, List.sum_nil, add_zero]
  rw [← hpm, e3, e2]
  ring

end Lvm.Typed.K
