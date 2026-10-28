-- Dev-only kill test of stage S-E4 (track L-circ), outside the entry: a compiled `main`, no
-- elaboration-time code. Times the flat-table evaluation classes of BLUEPRINT §10 changes 17 on
-- the node sizes of `logs/S-E3/nodedump/` (slot 0), with the entry's `F` (`FRField128`) and the
-- entry's walk (`FRBlake2sWalk.walkAB`). Prints, per class, the F products it performs, the time,
-- and ns per F product. `e4kill REPS`.
import FRBlake2sWalk
import FRField128

open FR RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def randF (s : UInt64) : F := let a := lcg (s ^^^ 0x5555); ⟨⟨a⟩, ⟨lcg a⟩⟩
def randAF (seed : UInt64) (n : Nat) : Array F := (Array.range n).map fun i => randF (seed * 7919 + i.toUInt64)

/-- `eq(r, ·)` over `2^|r|` points, bit `l` of the index ↔ `r[l]`; `2^v − 1` products. -/
def eqTab (r : Array F) : Array F := Id.run do
  let v := r.size
  let mut t : Array F := Array.replicate (1 <<< v) 0
  t := t.set! 0 1
  for l in [0:v] do
    let h := 1 <<< l
    let x := r[l]!
    for i in [0:h] do
      let a := t[i]!
      let b := a * x
      t := t.set! (i + h) b
      t := t.set! i (a + b)
  return t

/-- `Π_{l ∈ [lo, hi)} eq(r_l, bit l of c)`. -/
def eqBits (r : Array F) (lo hi c : Nat) : F := Id.run do
  let mut p : F := 1
  for l in [lo:hi] do
    let x := r[l]!
    p := p * (if c.testBit l then x else x + 1)
  return p

/-- `Σ_{t<n} eq(x[xo..xo+L), t) · eq(y[yo..yo+L), t)` by the dyadic decomposition of `[0, n)`:
`low[b] = Π_{l<b} (1 + x_l + y_l)`, then the set bits of `n` from the top. -/
def rangeEq (x : Array F) (xo : Nat) (y : Array F) (yo L n : Nat) : F := Id.run do
  let mut low : Array F := Array.mkEmpty (L + 1)
  let mut p : F := 1
  for l in [0:L] do
    low := low.push p
    p := p * (1 + x[xo + l]! + y[yo + l]!)
  let mut hp : F := 1
  let mut acc : F := 0
  for k in [0:L] do
    let b := L - 1 - k
    let xb := x[xo + b]!; let yb := y[yo + b]!
    if n.testBit b then
      acc := acc + hp * ((1 + xb) * (1 + yb)) * low[b]!
      hp := hp * (xb * yb)
    else
      hp := hp * ((1 + xb) * (1 + yb))
  if n == 1 <<< L then acc := p
  return acc

def popc (n : Nat) (L : Nat) : Nat := (List.range L).foldl (fun a b => if n.testBit b then a + 1 else a) 0

/-- One regular (key, import) pair: `U · eq(τ above, R0) · eq(σ above, C0) · rangeEq`. -/
structure Pair where
  a : Nat     -- row bits of the key (local rows)
  s : Nat     -- cell stride bits
  n : Nat     -- instances
  r0 : Nat    -- the key's aligned row base
  c0 : Nat    -- the import's cell base
  deriving Inhabited

def clog (n : Nat) : Nat := Id.run do
  let mut L := 0
  while (1 <<< L) < n do L := L + 1
  return L

def pairVal (τ σ : Array F) (u : F) (p : Pair) : F :=
  let L := clog p.n
  let rt := eqBits τ (p.a + L) 21 (p.r0 >>> 0)
  let ct := eqBits σ (p.s + L) 23 p.c0
  let cl := eqBits σ 0 p.s p.c0
  u * rt * ct * cl * rangeEq τ p.a σ p.s L p.n

def pairProducts (p : Pair) : Nat :=
  let L := clog p.n
  (21 - (p.a + L)) + (23 - (p.s + L)) + p.s + 4 + L + 2 * L + 2 * popc p.n L

/-- The keys of the dump's `groups-0.txt` plus the 3.12 templates: (a, s, n, imports per key). -/
def keys : List (Nat × Nat × Nat × Nat) :=
  [(7, 7, 290, 64), (5, 5, 581, 16), (8, 8, 512, 8), (3, 5, 7552, 4), (9, 9, 126, 6), (6, 6, 4, 8),
   (5, 5, 871, 20), (8, 8, 882, 4)]

def mkPairs (target : Nat) : Array Pair := Id.run do
  let mut out := #[]
  let mut i := 0
  while out.size < target do
    let (a, s, n, k) := keys[i % keys.length]!
    for j in [0:k] do
      if out.size < target then
        let L := clog n
        out := out.push { a, s, n, r0 := (i * 977) % (1 <<< (21 - a - L)) <<< (a + L) >>> 0,
                          c0 := (((i * 131 + j) % (1 <<< (23 - s - L))) <<< (s + L)) + (j % (1 <<< s)) }
    i := i + 1
  return out

/-- Run-structured imports: prefix array of `pack(c) · lo[c]` over `σ_lo` (12 bits), then per run
`(P[e] − P[s]) · hi[c ≫ 12] · w_step`; per step the row factor `w = U · eqτ(row)`. -/
def prefixArr (lo : Array F) (pack : Array F) : Array F := Id.run do
  let mut P : Array F := Array.mkEmpty (lo.size + 1)
  let mut acc : F := 0
  P := P.push acc
  for i in [0:lo.size] do
    acc := acc + pack[i % pack.size]! * lo[i]!
    P := P.push acc
  return P

structure Run where
  c : Nat
  len : Nat
  deriving Inhabited

def mkRuns (steps : Nat) (perStep : Nat) : Array Run := Id.run do
  let mut out := #[]
  for t in [0:steps] do
    for j in [0:perStep] do
      let c := 6291457 + ((t * 2654435761 + j * 40503) % (1 <<< 21))
      let len := [16, 8, 1, 8][j % 4]!
      -- keep the run inside one 2^12 block (the evaluator splits a crossing run in two)
      let c := if (c &&& 4095) + len > 4096 then c - len else c
      out := out.push { c, len }
  return out

def runsVal (P hi tlo thi : Array F) (u : F) (runs : Array Run) (perStep : Nat) : F := Id.run do
  let mut acc : F := 0
  let steps := runs.size / perStep
  for t in [0:steps] do
    let row := (t * 8) % (1 <<< 21)
    let w := u * (tlo[row &&& 2047]! * thi[row >>> 11]!)
    let mut sacc : F := 0
    for j in [0:perStep] do
      let r := runs[t * perStep + j]!
      let lo := r.c &&& 4095
      sacc := sacc + (P[lo + r.len]! + P[lo]!) * hi[r.c >>> 12]!
    acc := acc + w * sacc
  return acc

/-- A template's local part (`hornerPos`-like): rows of A/B/C entries `(cell, coef?)`; per row
three accumulators `S_A, S_B, S_C` (an entry with coefficient 1 is an addition, any other one a
product), then `Σ_j eqτ[j] · S_m`. -/
structure TplFlat where
  rowStart : Array Nat     -- per row, index of its first entry (size rows+1)
  cell : Array UInt32      -- entry's local cell
  mat : Array UInt8        -- 0/1/2 = A/B/C
  coef : Array F           -- entry's coefficient
  one : Array Bool         -- coefficient is 1

def mkTpl (mulKs : Nat) : TplFlat := Id.run do
  let mut rs := #[0]; let mut cell := #[]; let mut mat := #[]; let mut coef := #[]; let mut one := #[]
  let α := randF 77
  for i in [0:mulKs] do
    for r in [0:3] do
      -- A: 3 entries (acc's linear form) + 1 import; B: 2; C: 1  (≈ 20 entries per mulK)
      let ents : List (Nat × Nat × Bool) :=
        [(0, 6*i + r, true), (0, 6*i + r + 1, r != 2), (0, 6*i + 2, true), (0, 900 + i, true),
         (1, 1000 + r, true), (1, 1001, r == 2), (2, 6*(i+1) + r, true)]
      for (m, c, o) in ents do
        cell := cell.push (c % 1024).toUInt32; mat := mat.push m.toUInt8
        coef := coef.push (if o then 1 else α); one := one.push o
      rs := rs.push cell.size
  return { rowStart := rs, cell, mat, coef, one }

def tplProducts (t : TplFlat) : Nat :=
  (t.one.foldl (fun a o => if o then a else a + 1) 0) + 3 * (t.rowStart.size - 1)

def locVal (t : TplFlat) (tlo slo : Array F) : F × F × F := Id.run do
  let mut A : F := 0; let mut B : F := 0; let mut C : F := 0
  for j in [0:t.rowStart.size - 1] do
    let mut sa : F := 0; let mut sb : F := 0; let mut sc : F := 0
    for e in [t.rowStart[j]!:t.rowStart[j+1]!] do
      let v := slo[t.cell[e]!.toNat]!
      let v := if t.one[e]! then v else t.coef[e]! * v
      match t.mat[e]! with
      | 0 => sa := sa + v
      | 1 => sb := sb + v
      | _ => sc := sc + v
    let w := tlo[j]!
    A := A + w * sa; B := B + w * sb; C := C + w * sc
  return (A, B, C)

/-- Run `f` `reps` times on inputs depending on the repetition; best and median ns. -/
def bench (name : String) (reps : Nat) (prods : Nat) (f : Nat → F) : IO Float := do
  let mut ts : Array Nat := #[]
  let mut chk : F := 0
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    let v ← IO.lazyPure fun _ => f i
    let t1 ← IO.monoNanosNow
    chk := chk + v
    ts := ts.push (t1 - t0)
  let s := ts.qsort (· < ·)
  let best := s[0]!; let med := s[s.size / 2]!
  let nsP := med.toFloat / prods.toFloat
  IO.println s!"{name}: products {prods}, best {best.toFloat / 1e6} ms, median {med.toFloat / 1e6} ms, {nsP} ns/F product (median)  [chk {chk.c₀.val}]"
  (← IO.getStdout).flush
  return med.toFloat / 1e6

/-- Walk positions as arrays (the entry's `onPos`). -/
def onPosA (a : Array F) (k : Pos Blake2sCircuit.m) : F := a.getD k.val 0

/-- Gate count of the compression program (`S = ℕ`, `α = Unit`). -/
def gateCount : Nat :=
  let o : GOps Blake2sCircuit.m Unit Nat :=
    { zero := (), xor := fun _ _ => (), var := fun _ => (), res := fun _ _ _ => (), upd := fun s _ _ _ => s + 1 }
  (o.compressW.run ⟨gateBase, 0⟩).2.acc

def main (args : List String) : IO UInt32 := do
  let reps := (args.head? >>= String.toNat?).getD 9
  -- the evaluation point (rows 21 bits, cells 23 bits), per repetition
  let τs := fun i : Nat => randAF (1000 + i.toUInt64) 21
  let σs := fun i : Nat => randAF (2000 + i.toUInt64) 23
  -- 0. one F product, chained
  let mulChain := fun (i : Nat) => Id.run do
    let mut x := randF i.toUInt64; let y := randF (i.toUInt64 + 1)
    for _ in [0:100000] do x := x * y
    return x
  let _ ← bench "F.mul chain (1e5)" reps 100000 mulChain
  -- 1. tables: τ 11 + 10, σ 12 + 11, the walks' 2 × 14
  let tabs := fun (i : Nat) =>
    let τ := τs i; let σ := σs i
    let a := eqTab (τ.extract 0 11); let b := eqTab (τ.extract 11 21)
    let c := eqTab (σ.extract 0 12); let d := eqTab (σ.extract 12 23)
    let e := eqTab (τ.extract 0 14); let f := eqTab (σ.extract 0 14)
    a[5]! + b[7]! + c[9]! + d[11]! + e[13]! + f[17]!
  let tTab ← bench "tables (2^11+2^10+2^12+2^11+2·2^14)" reps (2^11+2^10+2^12+2^11+2*2^14 - 6) tabs
  -- 2. regular imports, 1,500 pairs
  let pairs := mkPairs 1500
  let pp := pairs.foldl (fun a p => a + pairProducts p) 0
  let reg := fun (i : Nat) => Id.run do
    let τ := τs i; let σ := σs i; let u := randF 3
    let mut acc : F := 0
    for p in pairs do acc := acc + pairVal τ σ u p
    return acc
  let tReg ← bench "regular imports (1,500 pairs)" reps pp reg
  -- 3. run-structured imports: 7,552 Merkle steps × 4 runs, prefix array over σ_lo
  let runs := mkRuns 7552 4
  let packs := randAF 55 64
  let tlo0 := eqTab ((τs 0).extract 0 11); let thi0 := eqTab ((τs 0).extract 11 21)
  let slo0 := eqTab ((σs 0).extract 0 12); let shi0 := eqTab ((σs 0).extract 12 23)
  let pre := fun (i : Nat) => (prefixArr (if i % 2 == 0 then slo0 else shi0.extract 0 4096 ++ slo0.extract 0 2048) packs)[4000]!
  let tPre ← bench "prefix array (2^12)" reps 4096 pre
  let P0 := prefixArr slo0 packs
  let runF := fun (i : Nat) => runsVal P0 shi0 tlo0 thi0 (randF i.toUInt64) runs 4
  let tRun ← bench "Merkle-step runs (7,552 × 4 runs)" reps (7552 * (2 + 4)) runF
  -- 4. template local part: hornerPos (127 mulK)
  let tpl := mkTpl 127
  let tlo9 := eqTab ((τs 0).extract 0 9); let slo10 := eqTab ((σs 0).extract 0 10)
  let tp := tplProducts tpl
  let locF := fun (i : Nat) => let (a, b, c) := locVal tpl (if i % 2 == 0 then tlo9 else tlo9.reverse) slo10; a + b + c
  let tLoc ← bench s!"hornerPos LOC ({tpl.cell.size} entries, {tpl.rowStart.size - 1} rows)" reps tp locF
  -- 5. the walk as implemented: walkAB over onPos arrays (computes A₀ and B₀ in one run)
  IO.println s!"compression gates: {gateCount}"
  let e0 := tlo0 ++ tlo0 ++ tlo0 ++ tlo0 ++ tlo0 ++ tlo0 ++ tlo0 ++ tlo0
  let w0 := slo0 ++ slo0 ++ slo0 ++ slo0
  let walkF := fun (i : Nat) => let (a, b) := walkAB (onPosA (if i % 2 == 0 then e0 else e0.reverse)) (onPosA w0); a + b
  let tWalk ← bench "walkAB (one run, A and B)" reps (2 * gateCount) walkF
  -- projection. Measured per class, scaled to the plan's per-node counts (sizes.py, changes 17):
  -- tables once; one walkAB run gives A₀ and B₀; LOC 36 k entries (shared by the slots); regular
  -- imports 1,500 pairs per slot and run imports 30,790 runs per slot, both slots; one prefix array.
  let locMs := tLoc * 36000 / tpl.cell.size.toFloat
  let runMs := tRun * 30790 / (7552 * 4).toFloat
  let evalM := tTab + tWalk + locMs + 2 * tReg + 2 * runMs + tPre
  IO.println s!"projection (measured implementation): tables {tTab} + walkAB {tWalk} + LOC {locMs} + regular 2×{tReg} + runs 2×{runMs} + prefix {tPre} = evalM {evalM} ms"
  IO.println s!"V (N30) ≈ 166.3 + 8 (finPf) + 3 (evalL) + evalM = {166.3 + 8 + 3 + evalM} ms VM (plan ≤ 230; kill > 253)"
  IO.println s!"  with V's own walkA + walkB fused into one walkAB op (−1 walk): {166.3 + 8 + 3 + evalM - tWalk} ms VM"
  let regPlan := 2 * 45000 * (tReg * 1e6 / pp.toFloat) / 1e6
  IO.println s!"  with the regular pairs at the plan's 30 F per pair: evalM {evalM - 2 * tReg + regPlan} ms, V {166.3 + 8 + 3 + evalM - 2 * tReg + regPlan - tWalk} ms VM (walkAB op too)"
  return 0
