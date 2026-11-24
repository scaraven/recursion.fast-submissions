-- New for lvm2 S2GT (GT-V): `Φ_Q` at an `E2` point on the coordinate-split cache, natively (the fast twin of
-- `LvmE2TWiring`'s `PhiQFT`; executable now, its equality is a later statement).
import LvmE2TWiring

/-!
# `Φ_Q` at `E2` on the compiled cache

T's form (`PhiQCT`): `Φ_Q(pt) = Σ_{s<2} X^s · Σ_{j<3} sel_j(p₂, p₃) · ev_{s,j}(p')`, where `ev_{s,j}` is coordinate
`s`'s `Φ` with the `j`-th `K` coordinates of the `E3` coefficients (`PhiPieceFT`) and `p'` the point without bits
2–3. The cache `c_s` (`PhiCacheX`) computes `Σ_e c_e · eq(p', e)` with `c_e ∈ E3 = K[y]/(y³ + y + 1)`.

**The `E2`-linear map.** Let `λ(c) = Σ_j c_j·sel_j` (`K`-linear, `E3 → E2`). Then
`Σ_j sel_j·ev_{s,j}(p') = Σ_e λ(c_e)·eq(p', e)`. The compiled evaluator multiplies the coefficients' `E3`
content (a weight `c·y^m`, a merged cell's limb factor `Σ_m eq_m·y^m`) only by point values, never by each other
(`linOk`, checked on the cache), so `λ` goes to the leaves: every value is an `E2` element. With
`sel₀ ≠ 0` the common factor `sel₀` comes out: a weight `c ∈ K` is one mixed product (`ρ₀ = 1`), `c·y^m` is
`c·ρ_m` with `ρ_m = sel_m / sel₀`, a limb factor is `Σ_m eq_m·ρ_m`.

**Cost.** An `E2` product is Karatsuba's three `K` products with the reductions folded (`m2`: two reductions); `E3`
products (`K.mulI`) are six.

`PhiQGC` falls back to the terms' sums at `E2` (`termsSum2`, slow) when `sel₀ = 0` (`p₂ = 1` or `p₃ = 1`) or a code
is not fused. Its correctness needs the cache linear (`linOkX`, a static guard fact: ≈ 30 ms natively, too slow per
call).
-/

set_option autoImplicit false

namespace Lvm.Typed.KT

open Lvm.Loop Lvm.Typed.K

/-! ## `E2` arithmetic on words -/

/-- `x·v` in `K` (`x⁶⁴ = x⁴ + x³ + x + 1`). -/
@[inline] def mulXw (v : UInt64) : UInt64 := (v <<< 1) ^^^ ((v >>> 63) * 0x1B)

/-- **The `E2` product**, three unreduced `K` products and two reductions: `re = p₀ + p₁`,
`im = m + p₀ + p₁ + x·p₁` (`x·p₁` unreduced: `p₁` has degree `≤ 126`). -/
@[inline] def m2 (a b : FE2) : FE2 :=
  let p0 := FK.clmul64 a.re.val b.re.val
  let p1 := FK.clmul64 a.im.val b.im.val
  let m := FK.clmul64 (a.re.val ^^^ a.im.val) (b.re.val ^^^ b.im.val)
  let rl := p0.lo ^^^ p1.lo
  let rh := p0.hi ^^^ p1.hi
  ⟨⟨FK.reduce rl rh⟩,
    ⟨FK.reduce (m.lo ^^^ rl ^^^ (p1.lo <<< 1)) (m.hi ^^^ rh ^^^ ((p1.hi <<< 1) ||| (p1.lo >>> 63)))⟩⟩

/-- The mixed product by `c ∈ K`: two products. -/
@[inline] def mK (a : FE2) (c : FK) : FE2 := ⟨fkMulI a.re c, fkMulI a.im c⟩

/-- `X·a` (`X² = 1 + xX`): `a₁ + (a₀ + x·a₁)X`, no product. -/
@[inline] def mX (a : FE2) : FE2 := ⟨a.im, ⟨a.re.val ^^^ mulXw a.im.val⟩⟩

@[inline] def a2 (a b : FE2) : FE2 := ⟨⟨a.re.val ^^^ b.re.val⟩, ⟨a.im.val ^^^ b.im.val⟩⟩

/-! ## The point and the leaf map -/

/-- The point `κ ++ r_x ++ r_y` (43 coordinates). -/
structure Pt2 where
  kap : Array FE2
  rx : Array FE2
  ry : Array FE2
  deriving Inhabited

def Pt2.ofList (pt : List FE2) : Pt2 :=
  ⟨(pt.take 2).toArray, ((pt.drop 2).take xVars).toArray, ((pt.drop (2 + xVars)).take yVars).toArray⟩

/-- The leaf map's ratios `ρ₁ = sel₁/sel₀`, `ρ₂ = sel₂/sel₀`. -/
structure Lam where
  r1 : FE2
  r2 : FE2
  deriving Inhabited

/-- `λ(w)/sel₀` of a weight. -/
@[inline] def lamW (L : Lam) (w : FE) : FE2 := a2 (a2 (FE2.ofK w.c₀) (mK L.r1 w.c₁)) (mK L.r2 w.c₂)

/-- `v·λ(w)/sel₀` by the weight's kind (`K.wKind`). -/
@[inline] def wmul2 (L : Lam) (m : ℕ) (v : FE2) (w : FE) : FE2 :=
  if m == 0 then mK v w.c₀ else if m == 1 then m2 (mK v w.c₁) L.r1
  else if m == 2 then m2 (mK v w.c₂) L.r2 else m2 v (lamW L w)

/-! ## Tables -/

def eqTabB2 (r : Array FE2) (bits : List ℕ) : Array FE2 := Id.run do
  let ba := bits.toArray
  let n := ba.size
  let mut t : Array FE2 := #[1]
  for i in [0:n] do
    let a := r.getD (ba.getD (n - 1 - i) 0) 0
    let mut nt : Array FE2 := Array.mkEmpty (2 * t.size)
    for v in t do
      let hi := m2 v a
      nt := nt.push (a2 v hi)
      nt := nt.push hi
    t := nt
  return t

def eqLevels2 (r : Array FE2) (lo n : ℕ) : Array (Array FE2) := Id.run do
  let mut t : Array FE2 := #[1]
  let mut lv : Array (Array FE2) := #[t]
  for i in [0:n] do
    let a := r.getD (lo + n - 1 - i) 0
    let mut nt : Array FE2 := Array.mkEmpty (2 * t.size)
    for v in t do
      let hi := m2 v a
      nt := nt.push (a2 v hi)
      nt := nt.push hi
    t := nt
    lv := lv.push t
  return lv.reverse

def margTab2 (lv : Array (Array FE2)) (lo n : ℕ) (bits : List ℕ) : Array FE2 := Id.run do
  match bits.head? with
  | none => return #[1]
  | some b0 =>
    let k := b0 - lo
    let t := lv.getD k #[]
    let kept := bits.foldl (fun acc b ↦ acc ||| 2 ^ (b - lo - k)) 0
    let miss := (2 ^ (n - k) - 1) ^^^ kept
    let nIn := 2 ^ (n - k - bits.length)
    let mut out : Array FE2 := Array.mkEmpty (2 ^ bits.length)
    let mut x := 0
    for _ in [0:2 ^ bits.length] do
      let mut acc : FE2 := 0
      let mut m := 0
      for _ in [0:nIn] do
        acc := a2 acc (t.getD (x ||| m) 0)
        m := ((m ||| kept) + 1) &&& miss
      out := out.push acc
      x := ((x ||| miss) + 1) &&& kept
    return out

def subTab2 (r : Array FE2) (lv : Array (Array FE2)) (lo n : ℕ) (bits : List ℕ) : Array FE2 :=
  match bits.head? with
  | none => #[1]
  | some b0 =>
    let k := b0 - lo
    if bits == (List.range (n - k)).map (b0 + ·) then lv.getD k #[]
    else if 20 * 2 ^ bits.length ≤ 2 ^ (n - k) then eqTabB2 r bits
    else margTab2 lv lo n bits

def succVal2 (xs ys : List FE2) : FE2 := Id.run do
  let n := xs.length
  let xa := xs.toArray
  let ya := ys.toArray
  let mut e : FE2 := 1
  let mut s : FE2 := 0
  for i in [0:n] do
    let k := n - 1 - i
    let a := xa.getD k 0
    let b := ya.getD k 0
    let ab := m2 a b
    s := a2 (m2 (a2 a ab) e) (m2 (a2 b ab) s)
    e := m2 (a2 (a2 (a2 1 a) b) (a2 ab ab)) e
  return s

/-- The limb factor under the leaf map: `Σ_m eq((a, b), m)·ρ_m` (`ρ₀ = 1`). -/
def limbVal2 (L : Lam) (a b : FE2) : FE2 :=
  let ab := m2 a b
  a2 (a2 (a2 (a2 (a2 1 a) b) ab) (m2 (a2 a ab) L.r1)) (m2 (a2 b ab) L.r2)

def kfVal2 (L : Lam) (P : Pt2) : KF → FE2
  | .pair i j => a2 (a2 1 (P.rx.getD i 0)) (P.ry.getD j 0)
  | .fixX i b => let r := P.rx.getD i 0; if b then r else a2 1 r
  | .succ xs ys => succVal2 (xs.map fun i ↦ P.rx.getD i 0) (ys.map fun j ↦ P.ry.getD j 0)
  | .limb e => limbVal2 L (P.ry.getD e 0) (P.ry.getD (e + 1) 0)
  | .ypow j c => let r := P.ry.getD j 0; a2 (a2 1 r) (mK r c)

def kerVal2 (L : Lam) (P : Pt2) (fs : List KF) : FE2 := fs.foldl (fun acc f ↦ m2 acc (kfVal2 L P f)) 1

def kapTab2 (κ : Array FE2) : Array FE2 :=
  let e := eqTabB2 κ [0, 1]
  (Array.range 16).map fun m ↦ (List.range 4).foldl (fun acc o ↦ if m.testBit o then a2 acc (e.getD o 0) else acc) 0

def TRec.eval2 (L : Lam) (P : Pt2) : TRec → Array FE2
  | .one => #[1]
  | .eqx bits => eqTabB2 P.rx bits
  | .eqy bits => eqTabB2 P.ry bits
  | .kap => kapTab2 P.kap
  | .ker ks => ks.map (kerVal2 L P)
  | .prod _ => #[]

@[inline] def keyVal2 (T : Array (Array FE2)) (k : ℕ × ℕ) : FE2 := (T.getD k.1 #[]).getD k.2 0

def prodKeys2 (T : Array (Array FE2)) : List (ℕ × ℕ) → FE2
  | [] => 1
  | k :: ks => ks.foldl (fun acc k' ↦ m2 acc (keyVal2 T k')) (keyVal2 T k)

def tabsAt2 (L : Lam) (P : Pt2) (rs : Array TRec) : Array (Array FE2) :=
  let lx0 := eqLevels2 P.rx 0 10
  let lx1 := eqLevels2 P.rx 10 (xVars - 10)
  let ly0 := eqLevels2 P.ry 0 11
  let ly1 := eqLevels2 P.ry 11 (yVars - 11)
  let T0 := rs.map fun r ↦ match r with
    | .eqx bits =>
      let (lo, n) := groupOf xVars 10 bits
      subTab2 P.rx (if lo == 0 then lx0 else lx1) lo n bits
    | .eqy bits =>
      let (lo, n) := groupOf yVars 11 bits
      subTab2 P.ry (if lo == 0 then ly0 else ly1) lo n bits
    | r => TRec.eval2 L P r
  rs.mapIdx fun i r ↦ match r with
    | .prod rows => rows.map (prodKeys2 T0)
    | _ => T0.getD i #[]

def flatTabs2 (rs : Array TRec) (T : Array (Array FE2)) : Array FE2 := Id.run do
  let mut F : Array FE2 := Array.mkEmpty ((tabOffs rs).getD rs.size 0)
  for t in [0:rs.size] do
    let tt := T.getD t #[]
    for i in [0:(rs.getD t .one).size] do
      F := F.push (tt.getD i 0)
  return F

/-! ## Fused code, the automaton, the finish -/

/-- **`runF2`'s loop** from instruction `k` with `fuel` instructions left: the accumulator `top` as its two words
(`tr`, `ti`), so that an instruction allocates no state (ACW-PHI; `runF2_fold` gives its value). -/
def runF2Go (L : Lam) (F : Array FE2) (ins : Array ℕ) (W : Array FE) :
    ℕ → ℕ → UInt64 → UInt64 → Array FE2 → Array (ℕ × FE2) → FE2 × Array (ℕ × FE2)
  | 0, _, tr, ti, _, em => (⟨⟨tr⟩, ⟨ti⟩⟩, em)
  | fuel + 1, k, tr, ti, st, em =>
    let top : FE2 := ⟨⟨tr⟩, ⟨ti⟩⟩
    let n := ins.getD k 0
    let a := F.getD ((n >>> 6) &&& 0xFFFFF) 0
    if n &&& 15 == 7 then
      let v := a2 top (m2 a (F.getD ((n >>> 26) &&& 0xFFFFF) 0))
      runF2Go L F ins W fuel (k + 1) v.re.val v.im.val st em
    else if n &&& 15 == 5 then
      runF2Go L F ins W fuel (k + 1) (tr ^^^ a.re.val) (ti ^^^ a.im.val) st em
    else if n &&& 15 == 6 then
      let v := a2 top (wmul2 L ((n >>> 4) &&& 3) a (W.getD (n >>> 46) 1))
      runF2Go L F ins W fuel (k + 1) v.re.val v.im.val st em
    else if n &&& 15 == 3 then
      let v := a2 (st.getD (st.size - 1) 0) (m2 a top)
      runF2Go L F ins W fuel (k + 1) v.re.val v.im.val st.pop em
    else if n &&& 15 == 1 then
      runF2Go L F ins W fuel (k + 1) a.re.val a.im.val (st.push top) em
    else if n &&& 15 == 0 then
      runF2Go L F ins W fuel (k + 1) 0 0 (st.push top) em
    else if n &&& 15 == 8 then
      let v := a2 top (m2 a (wmul2 L ((n >>> 4) &&& 3) (F.getD ((n >>> 26) &&& 0xFFFFF) 0) (W.getD (n >>> 46) 1)))
      runF2Go L F ins W fuel (k + 1) v.re.val v.im.val st em
    else if n &&& 15 == 4 then
      let v := st.getD (st.size - 1) 0
      runF2Go L F ins W fuel (k + 1) v.re.val v.im.val st.pop (em.push (n >>> 26, top))
    else if n &&& 15 == 2 then
      let v := wmul2 L ((n >>> 4) &&& 3) a (W.getD (n >>> 46) 1)
      runF2Go L F ins W fuel (k + 1) v.re.val v.im.val (st.push top) em
    else
      let v := a2 (st.getD (st.size - 1) 0) top
      runF2Go L F ins W fuel (k + 1) v.re.val v.im.val st.pop em

/-- **Run fused code at `E2`** (`K.runF`'s instructions; weights through `wmul2`): `runF2Go` over every
instruction. -/
def runF2 (L : Lam) (F : Array FE2) (c : FCode) : FE2 × Array (ℕ × FE2) :=
  runF2Go L F c.ins c.ws c.ins.size 0 0 0 (Array.mkEmpty 8) #[]

def autoStepP2 (R : ℕ) (rxk ryk : FE2) (cs : Array ℕ) (vs : Array FE2) : Array ℕ × Array FE2 := Id.run do
  let p := m2 rxk ryk
  let e00 := a2 (a2 (a2 1 rxk) ryk) p
  let e01 := a2 ryk p
  let e10 := a2 rxk p
  let e11 := p
  let n := cs.size
  let half (sh : ℕ) : Array ℕ × Array FE2 × Array ℕ := Id.run do
    let mut ts : Array ℕ := Array.mkEmpty n
    let mut xs : Array FE2 := Array.mkEmpty n
    let mut ks : Array ℕ := Array.mkEmpty n
    let mut i := 0
    while i < n do
      let c := cs.getD i 0
      let v := vs.getD i 0
      let d := c + sh
      if d % 2 == 0 then
        if i + 1 < n && cs.getD (i + 1) 0 == c + 1 then
          let v' := vs.getD (i + 1) 0
          ts := ts.push (d / 2); xs := xs.push (a2 v (m2 ryk (a2 v v'))); ks := ks.push 2
          i := i + 2
        else
          ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 0
          i := i + 1
      else
        ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 1
        i := i + 1
    return (ts, xs, ks)
  let (ta, va, ka) := half 0
  let (tb, vb, kb) := half R
  let wy (val : FE2) (k : ℕ) : FE2 := if k == 2 then val else if k == 0 then a2 val (m2 ryk val) else m2 ryk val
  let mut oc : Array ℕ := Array.mkEmpty (ta.size + tb.size)
  let mut ov : Array FE2 := Array.mkEmpty (ta.size + tb.size)
  let mut i := 0
  let mut j := 0
  while i < ta.size || j < tb.size do
    let a := ta.getD i 0
    let b := tb.getD j 0
    if j ≥ tb.size || (i < ta.size && a < b) then
      let x := va.getD i 0
      let k := ka.getD i 0
      oc := oc.push a; ov := ov.push (if k == 2 then a2 x (m2 rxk x) else m2 x (if k == 0 then e00 else e01))
      i := i + 1
    else if i ≥ ta.size || b < a then
      let x := vb.getD j 0
      let k := kb.getD j 0
      oc := oc.push b; ov := ov.push (if k == 2 then m2 rxk x else m2 x (if k == 0 then e10 else e11))
      j := j + 1
    else
      let x := va.getD i 0
      let y := vb.getD j 0
      let k := ka.getD i 0
      let k' := kb.getD j 0
      oc := oc.push a
      if k != 2 && k' != 2 then
        ov := ov.push (a2 (m2 x (if k == 0 then e00 else e01)) (m2 y (if k' == 0 then e10 else e11)))
      else
        let A := wy x k
        let B := wy y k'
        ov := ov.push (a2 A (m2 rxk (a2 A B)))
      i := i + 1
      j := j + 1
  return (oc, ov)

def runAuto2 (P : Pt2) (xs : Array ℕ) (R : ℕ) (st : Array (ℕ × FE2)) : Array (ℕ × FE2) := Id.run do
  let mut cs := st.map (·.1)
  let mut vs := st.map (·.2)
  for k in [0:xs.size] do
    let r := autoStepP2 R (P.rx.getD (xs.getD k 0) 0) (P.ry.getD k 0) cs vs
    cs := r.1
    vs := r.2
  return (Array.range cs.size).map fun i ↦ (cs.getD i 0, vs.getD i 0)

def finVal2 (T : Array (Array FE2)) (p : Pass) (c : ℕ) : FE2 :=
  p.fin.foldl (fun acc (t, bs) ↦ m2 acc ((T.getD t #[]).getD (pext c bs) 0)) 1

def finSum2 (T : Array (Array FE2)) (p : Pass) (fs : Array (ℕ × FE2)) : FE2 := Id.run do
  if p.fin.size != 2 then return fs.foldl (fun acc (c, v) ↦ a2 acc (m2 v (finVal2 T p c))) 0
  let (tl, bl) := p.fin.getD 0 (0, [])
  let (th, bh) := p.fin.getD 1 (0, [])
  let rl := runOf bl
  let rh := runOf bh
  let ml := 2 ^ bl.length - 1
  let mh := 2 ^ bh.length - 1
  let Tl := T.getD tl #[]
  let Th := T.getD th #[]
  let mut tot : FE2 := 0
  let mut inner : FE2 := 0
  let mut h := pextR rh mh (fs.getD 0 (0, 0)).1 bh
  for (c, v) in fs do
    let h' := pextR rh mh c bh
    if h' != h then
      tot := a2 tot (m2 (Th.getD h 0) inner)
      inner := 0
      h := h'
    inner := a2 inner (m2 v (Tl.getD (pextR rl ml c bl) 0))
  return a2 tot (m2 (Th.getD h 0) inner)

def runPassF2 (L : Lam) (P : Pt2) (T : Array (Array FE2)) (F : Array FE2) (p : Pass) (fc : FCode) : FE2 :=
  let s := finSum2 T p (runAuto2 P p.xs p.R (runF2 L F fc).2)
  match p.limbE with
  | some e => m2 s (limbVal2 L (P.ry.getD e 0) (P.ry.getD (e + 1) 0))
  | none => s

/-- **The compiled evaluator under the leaf map** (`λ/sel₀` at the leaves), `none` if a code is not fused. -/
def evalC2 (L : Lam) (c : Comp) (pt : List FE2) : Option FE2 := do
  let fc ← c.fcode
  let P := Pt2.ofList pt
  let T := tabsAt2 L P c.tabs
  let F := flatTabs2 c.tabs T
  let a := (runF2 L F fc).1
  c.passes.foldlM (fun acc p ↦ do let pf ← p.fcode; pure (a2 acc (runPassF2 L P T F p pf))) a

/-! ## The linearity check (`λ` goes to the leaves) -/

/-- The ker tables with a limb factor (`none` if a ker entry has two, or a prod table reads one). -/
def limbTabs (rs : Array TRec) : Option (Array ℕ) := Id.run do
  let mut out : Array ℕ := #[]
  for t in [0:rs.size] do
    match rs.getD t .one with
    | .ker ks =>
      let cnt := ks.map fun fs ↦ (fs.filter fun f ↦ match f with | .limb _ => true | _ => false).length
      if cnt.any (· > 1) then return none
      if cnt.any (· > 0) then out := out.push t
    | _ => pure ()
  for t in [0:rs.size] do
    match rs.getD t .one with
    | .prod rows => if rows.any fun r ↦ r.any fun k ↦ out.contains k.1 then return none
    | _ => pure ()
  return some out

/-- A code's `E3` content: whether no product meets two `E3`-carrying factors (a weight `c·y^m`, `m ≥ 1`, or a
limb entry), and whether the result (and every emitted state) is `E3`-free. -/
def linCode (lim : ℕ → Bool) (c : FCode) : Bool × Bool := Id.run do
  let mut top := false
  let mut st : Array Bool := #[]
  let mut ok := true
  let mut emc := false
  for n in c.ins do
    let op := n &&& 15
    let la := lim ((n >>> 6) &&& 0xFFFFF)
    let lb := lim ((n >>> 26) &&& 0xFFFFF)
    let wm := (n >>> 4) &&& 3 != 0
    if op == 7 then
      if la && lb then ok := false
      top := top || la || lb
    else if op == 5 then top := top || la
    else if op == 6 then
      if la && wm then ok := false
      top := top || la || wm
    else if op == 3 then
      if la && top then ok := false
      top := st.getD (st.size - 1) false || la || top
      st := st.pop
    else if op == 1 then st := st.push top; top := la
    else if op == 0 then st := st.push top; top := false
    else if op == 8 then
      if (la && lb) || (la && wm) || (lb && wm) then ok := false
      top := top || la || lb || wm
    else if op == 4 then
      emc := emc || top
      top := st.getD (st.size - 1) false
      st := st.pop
    else if op == 2 then
      if la && wm then ok := false
      st := st.push top; top := la || wm
    else
      top := st.getD (st.size - 1) false || top
      st := st.pop
  return (ok, !(top || emc))

/-- **The linearity check** of a compiled evaluator: ker entries with at most one limb factor, no prod table
over them, every code linear, a pass with a limb factor `E3`-free before it, the finish tables `E3`-free. -/
def linOk (c : Comp) : Bool :=
  match limbTabs c.tabs with
  | none => false
  | some lt =>
    let offs := tabOffs c.tabs
    let lim (fi : ℕ) : Bool := lt.any fun t ↦ offs.getD t 0 ≤ fi && fi < offs.getD (t + 1) 0
    (match c.fcode with | some fc => (linCode lim fc).1 | none => false) &&
      c.passes.all fun p ↦
        (match p.fcode with
          | some fc => let r := linCode lim fc; r.1 && (p.limbE.isNone || r.2)
          | none => false) &&
        p.fin.all fun (t, _) ↦ !lt.contains t

/-! ## `Φ_Q` at `E2` -/

/-- `λ(c) = Σ_j c_j·sel_j` (`sel` unnormalised). -/
@[inline] def lamS (s0 s1 s2 : FE2) (c : FE) : FE2 := a2 (a2 (mK s0 c.c₀) (mK s1 c.c₁)) (mK s2 c.c₂)

/-- **The slow path**: the terms' sums at `E2` under `λ`, `Σ_t Σ_{jf < 2^l} λ(w_t(jf))·eq(p', e_t(jf))` (the cache's
terms are the entries, `PhiCache.okBX`). -/
def termsSum2 (s0 s1 s2 : FE2) (ts : List CTerm) (p' : List FE2) : FE2 :=
  ts.foldl (fun acc t ↦ (List.range (2 ^ t.l)).foldl (fun acc jf ↦
    let e := t.at jf
    a2 acc (m2 (lamS s0 s1 s2 e.c) (eqWT p' e.idx))) acc) 0

/-- **`Φ_Q` at an `E2` point on the coordinate-split cache** (S2GT's `PhiQGC`; correct on a linear cache, `linOkX`,
a static fact of the guard): with `sel₀ ≠ 0`, `sel₀·(Φ̃₀(p') + X·Φ̃₁(p'))` by the compiled codes under the leaf map
`λ/sel₀`; else (`p₂ = 1` or `p₃ = 1`, or a code not fused) the terms' sums (`termsSum2`, slow). -/
def PhiQGCK (c : PhiCacheX) (pt : List FE2) : FE2 :=
  let p2 := pt.getD 2 0
  let p3 := pt.getD 3 0
  let s0 := m2 (a2 1 p2) (a2 1 p3)
  let s1 := m2 p2 (a2 1 p3)
  let s2 := m2 (a2 1 p2) p3
  let p' := pt.take 2 ++ pt.drop 4
  let slow (_ : Unit) : FE2 :=
    a2 (termsSum2 s0 s1 s2 c.c0.terms p') (mX (termsSum2 s0 s1 s2 c.c1.terms p'))
  if s0 == 0 then slow () else
    let i := s0⁻¹
    let L : Lam := ⟨m2 s1 i, m2 s2 i⟩
    match evalC2 L c.c0.comp p', evalC2 L c.c1.comp p' with
    | some v0, some v1 => m2 s0 (a2 v0 (mX v1))
    | _, _ => slow ()

/-- The fast path alone (`linOk` assumed; `none` when `sel₀ = 0` or a code is not fused): the benchmark's. -/
def PhiQTC (c : PhiCacheX) (pt : List FE2) : Option FE2 :=
  let p2 := pt.getD 2 0
  let p3 := pt.getD 3 0
  let s0 := m2 (a2 1 p2) (a2 1 p3)
  if s0 == 0 then none else
    let i := s0⁻¹
    let L : Lam := ⟨m2 (m2 p2 (a2 1 p3)) i, m2 (m2 (a2 1 p2) p3) i⟩
    let p' := pt.take 2 ++ pt.drop 4
    match evalC2 L c.c0.comp p', evalC2 L c.c1.comp p' with
    | some v0, some v1 => some (m2 s0 (a2 v0 (mX v1)))
    | _, _ => none

/-- The cache's linearity check. -/
def linOkX (c : PhiCacheX) : Bool := linOk c.c0.comp && linOk c.c1.comp

end Lvm.Typed.KT

namespace Lvm.E2T

/-- **The fast `Φ_Q` at an `E2` point** over the coordinate-split cache (GT-L's placeholder `PhiQGC`). -/
def PhiQGC (c : Lvm.Typed.PhiCacheX) (pt : List FE2) : FE2 := Lvm.Typed.KT.PhiQGCK c pt

end Lvm.E2T
