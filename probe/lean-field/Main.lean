/-
  The benchmark and the known-answer dump.

    gfbench check SEED      -- prints `variant a b r` lines (hex) for checkgf.py
    gfbench bench SEED REPS -- prints `variant kind ns_per_op (median) min max`

  Inputs come from a splitmix64 stream seeded at run time; each loop's result is printed (as a
  checksum), so nothing is evaluated at compile time or dropped.
-/
import GF
import GFU
import Blake2sProbe

open GF

set_option maxRecDepth 100000
set_option compiler.maxRecInline 1024

@[inline] def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s, z ^^^ (z >>> 31))

/-- Latency: `x := x * y`, `n` times. -/
@[specialize] def lat (mul : UInt64 → UInt64 → UInt64 → UInt64 → U128) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, xl, xh, _, _ => xl ^^^ xh
  | n + 1, xl, xh, yl, yh => let r := mul xl xh yl yh; lat mul n r.lo r.hi yl yh

/-- Throughput: four independent chains. -/
@[specialize] def thr (mul : UInt64 → UInt64 → UInt64 → UInt64 → U128) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul a0 a1 yl yh
    let rb := mul b0 b1 yl yh
    let rc := mul c0 c1 yl yh
    let rd := mul d0 d1 yl yh
    thr mul n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

@[specialize] def lat64 (mul : UInt64 → UInt64 → UInt64) : Nat → UInt64 → UInt64 → UInt64
  | 0, x, _ => x
  | n + 1, x, y => lat64 mul n (mul x y) y

@[specialize] def thr64 (mul : UInt64 → UInt64 → UInt64) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a, b, c, d, _ => a ^^^ b ^^^ c ^^^ d
  | n + 1, a, b, c, d, y => thr64 mul n (mul a y) (mul b y) (mul c y) (mul d y) y

def thr_mul128Naive : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul128Naive a0 a1 yl yh
    let rb := mul128Naive b0 b1 yl yh
    let rc := mul128Naive c0 c1 yl yh
    let rd := mul128Naive d0 d1 yl yh
    thr_mul128Naive n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

def thr_mul128NaiveU : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul128NaiveU a0 a1 yl yh
    let rb := mul128NaiveU b0 b1 yl yh
    let rc := mul128NaiveU c0 c1 yl yh
    let rd := mul128NaiveU d0 d1 yl yh
    thr_mul128NaiveU n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

def thr_mul128Comb : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul128Comb a0 a1 yl yh
    let rb := mul128Comb b0 b1 yl yh
    let rc := mul128Comb c0 c1 yl yh
    let rd := mul128Comb d0 d1 yl yh
    thr_mul128Comb n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

def thr_mul128CombU : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul128CombU a0 a1 yl yh
    let rb := mul128CombU b0 b1 yl yh
    let rc := mul128CombU c0 c1 yl yh
    let rd := mul128CombU d0 d1 yl yh
    thr_mul128CombU n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

def thr_mul128WinA : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul128WinA a0 a1 yl yh
    let rb := mul128WinA b0 b1 yl yh
    let rc := mul128WinA c0 c1 yl yh
    let rd := mul128WinA d0 d1 yl yh
    thr_mul128WinA n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

def thr_mul128WinM : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul128WinM a0 a1 yl yh
    let rb := mul128WinM b0 b1 yl yh
    let rc := mul128WinM c0 c1 yl yh
    let rd := mul128WinM d0 d1 yl yh
    thr_mul128WinM n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

def thr_mul128WinMU : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul128WinMU a0 a1 yl yh
    let rb := mul128WinMU b0 b1 yl yh
    let rc := mul128WinMU c0 c1 yl yh
    let rd := mul128WinMU d0 d1 yl yh
    thr_mul128WinMU n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

def thr_mul128H32 : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul128H32 a0 a1 yl yh
    let rb := mul128H32 b0 b1 yl yh
    let rc := mul128H32 c0 c1 yl yh
    let rd := mul128H32 d0 d1 yl yh
    thr_mul128H32 n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

def thr_mul128H64 : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a0, a1, b0, b1, c0, c1, d0, d1, _, _ => a0 ^^^ a1 ^^^ b0 ^^^ b1 ^^^ c0 ^^^ c1 ^^^ d0 ^^^ d1
  | n + 1, a0, a1, b0, b1, c0, c1, d0, d1, yl, yh =>
    let ra := mul128H64 a0 a1 yl yh
    let rb := mul128H64 b0 b1 yl yh
    let rc := mul128H64 c0 c1 yl yh
    let rd := mul128H64 d0 d1 yl yh
    thr_mul128H64 n ra.lo ra.hi rb.lo rb.hi rc.lo rc.hi rd.lo rd.hi yl yh

def thr_mul64Comb : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a, b, c, d, _ => a ^^^ b ^^^ c ^^^ d
  | n + 1, a, b, c, d, y => thr_mul64Comb n (mul64Comb a y) (mul64Comb b y) (mul64Comb c y) (mul64Comb d y) y

def thr_mul64CombU : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a, b, c, d, _ => a ^^^ b ^^^ c ^^^ d
  | n + 1, a, b, c, d, y => thr_mul64CombU n (mul64CombU a y) (mul64CombU b y) (mul64CombU c y) (mul64CombU d y) y

def thr_mul64H32 : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a, b, c, d, _ => a ^^^ b ^^^ c ^^^ d
  | n + 1, a, b, c, d, y => thr_mul64H32 n (mul64H32 a y) (mul64H32 b y) (mul64H32 c y) (mul64H32 d y) y

def thr_mul64H64 : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, a, b, c, d, _ => a ^^^ b ^^^ c ^^^ d
  | n + 1, a, b, c, d, y => thr_mul64H64 n (mul64H64 a y) (mul64H64 b y) (mul64H64 c y) (mul64H64 d y) y

def latBoxed : Nat → G128 → G128 → G128
  | 0, x, _ => x
  | n + 1, x, y => latBoxed n (G128.mul x y) y

def latBoxedH32 : Nat → G128 → G128 → G128
  | 0, x, _ => x
  | n + 1, x, y => latBoxedH32 n (G128.mulH32 x y) y

def latFixed (f : Fixed) : Nat → UInt64 → UInt64 → UInt64
  | 0, xl, xh => xl ^^^ xh
  | n + 1, xl, xh => let r := mulFixed f xl xh; latFixed f n r.lo r.hi

def latSq : Nat → UInt64 → UInt64 → UInt64
  | 0, xl, xh => xl ^^^ xh
  | n + 1, xl, xh => let r := sq128 xl xh; latSq n r.lo r.hi

/-- An inner product of two arrays of boxed elements, with the boxed multiplication. -/
def dot (a b : Array G128) : Nat → Nat → G128 → G128
  | 0, _, acc => acc
  | n + 1, i, acc =>
    let p := G128.mul a[i]! b[i]!
    dot a b n (i + 1) ⟨acc.lo ^^^ p.lo, acc.hi ^^^ p.hi⟩

/-- The same inner product with the multiplication inlined (no result allocated). -/
def dotI (a b : Array G128) : Nat → Nat → UInt64 → UInt64 → UInt64
  | 0, _, l, h => l ^^^ h
  | n + 1, i, l, h =>
    let x := a[i]!
    let y := b[i]!
    let p := mul128H64 x.lo x.hi y.lo y.hi
    dotI a b n (i + 1) (l ^^^ p.lo) (h ^^^ p.hi)


/-- BLAKE2s compressions chained: `h := compressF h m 64 0 0`. -/
def blakeLat (m : Vector UInt32 16) : Nat → Vector UInt32 8 → UInt64
  | 0, h => h[0].toUInt64
  | n + 1, h => blakeLat m n (Blake2sProbe.compressF h m 64 0 0)

/-- BLAKE2s-256 of a message of at most 64 bytes (one compression), as hex. -/
def blake2s1 (msg : List UInt8) : String :=
  let b := msg.toArray ++ Array.replicate (64 - msg.length) (0 : UInt8)
  let m : Vector UInt32 16 := Vector.ofFn fun i =>
    b[4*i.val]!.toUInt32 ||| (b[4*i.val+1]!.toUInt32 <<< 8) ||| (b[4*i.val+2]!.toUInt32 <<< 16) |||
      (b[4*i.val+3]!.toUInt32 <<< 24)
  let h := Blake2sProbe.iv.set 0 (Blake2sProbe.iv[0] ^^^ 0x01010020)
  let o := Blake2sProbe.compressF h m msg.length.toUInt64 0xFFFFFFFF 0
  String.join ((List.range 32).map fun k =>
    let byte := ((o[k / 4]! >>> (8 * (k % 4)).toUInt32) &&& 0xFF).toNat
    let s := String.ofList (Nat.toDigits 16 byte)
    if s.length == 1 then "0" ++ s else s)

def hex (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (16 - s.length) ++ s

def rand (s : UInt64) (k : Nat) : Array UInt64 := Id.run do
  let mut s := s
  let mut out := #[]
  for _ in [0:k] do
    let (s', z) := splitmix s
    s := s'
    out := out.push z
  return out

def check (seed : UInt64) : IO Unit := do
  IO.println s!"blake2s256 616263 {blake2s1 [0x61, 0x62, 0x63]}"
  let r := rand seed 512
  -- structured inputs first: x^127 * x, x^64 * x^64, all-ones squared, 1 * a
  let extra : List (UInt64 × UInt64 × UInt64 × UInt64) :=
    [(0, 0x8000000000000000, 2, 0), (0, 1, 0, 1), (UInt64.ofNat (2^64-1), UInt64.ofNat (2^64-1),
      UInt64.ofNat (2^64-1), UInt64.ofNat (2^64-1)), (1, 0, r[0]!, r[1]!)]
  let pairs := extra ++ (List.range 120).map fun i => (r[4*i]!, r[4*i+1]!, r[4*i+2]!, r[4*i+3]!)
  for (al, ah, bl, bh) in pairs do
    let p := clmulComb al bl
    IO.println s!"c64comb {hex al} {hex bl} {hex p.hi}{hex p.lo}"
    let p := clmulCombU al bl
    IO.println s!"c64combU {hex al} {hex bl} {hex p.hi}{hex p.lo}"
    let p := clmulWinA al bl
    IO.println s!"c64win4a {hex al} {hex bl} {hex p.hi}{hex p.lo}"
    let p := clmulWinM al bl
    IO.println s!"c64win4m {hex al} {hex bl} {hex p.hi}{hex p.lo}"
    let p := clmulWinMU al bl
    IO.println s!"c64win4mU {hex al} {hex bl} {hex p.hi}{hex p.lo}"
    let p := clmulH32 al bl
    IO.println s!"c64h32 {hex al} {hex bl} {hex p.hi}{hex p.lo}"
    let p := clmulH64 al bl
    IO.println s!"c64h64 {hex al} {hex bl} {hex p.hi}{hex p.lo}"
    let p := mul128Naive al ah bl bh
    IO.println s!"g128naive {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := mul128NaiveU al ah bl bh
    IO.println s!"g128naiveU {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := mul128Comb al ah bl bh
    IO.println s!"g128comb {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := mul128CombU al ah bl bh
    IO.println s!"g128combU {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := mul128WinA al ah bl bh
    IO.println s!"g128win4a {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := mul128WinM al ah bl bh
    IO.println s!"g128win4m {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := mul128WinMU al ah bl bh
    IO.println s!"g128win4mU {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := mul128H32 al ah bl bh
    IO.println s!"g128h32 {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := mul128H64 al ah bl bh
    IO.println s!"g128h64 {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := mulFixed (Fixed.mk' bl bh) al ah
    IO.println s!"g128fixed {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := G128.mul ⟨al, ah⟩ ⟨bl, bh⟩
    IO.println s!"g128boxed {hex ah}{hex al} {hex bh}{hex bl} {hex p.hi}{hex p.lo}"
    let p := sq128 al ah
    IO.println s!"g128sq {hex ah}{hex al} {hex ah}{hex al} {hex p.hi}{hex p.lo}"
    IO.println s!"g64comb {hex al} {hex bl} {hex (mul64Comb al bl)}"
    IO.println s!"g64combU {hex al} {hex bl} {hex (mul64CombU al bl)}"
    IO.println s!"g64h32 {hex al} {hex bl} {hex (mul64H32 al bl)}"
    IO.println s!"g64h64 {hex al} {hex bl} {hex (mul64H64 al bl)}"

def median (xs : Array Nat) : Nat := (xs.qsort (· < ·))[xs.size / 2]!

/-- Time `k` repetitions of `f n`, print ns per operation (`ops` operations per call). -/
def timeIt (name : String) (reps n ops : Nat) (f : Nat → UInt64) : IO Unit := do
  let mut ts := #[]
  let mut chk : UInt64 := 0
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => f n
    chk := chk ^^^ r
    let t1 ← IO.monoNanosNow
    ts := ts.push (t1 - t0)
  let per (t : Nat) : Float := t.toFloat / (n * ops).toFloat
  let s := ts.qsort (· < ·)
  IO.println s!"{name} {per (median ts)} {per s[0]!} {per s[s.size - 1]!} chk={hex chk}"

def bench (seed : UInt64) (reps : Nat) : IO Unit := do
  let r := rand seed 64
  let (xl, xh, yl, yh) := (r[0]!, r[1]!, r[2]!, r[3]!)
  timeIt "g128 naive lat" reps 200000 1 fun n => lat mul128Naive n xl xh yl yh
  timeIt "g128 naive thr" reps 50000 4 fun n => thr_mul128Naive n xl xh r[4]! r[5]! r[6]! r[7]! r[8]! r[9]! yl yh
  timeIt "g128 naiveU lat" reps 200000 1 fun n => lat mul128NaiveU n xl xh yl yh
  timeIt "g128 naiveU thr" reps 50000 4 fun n => thr_mul128NaiveU n xl xh r[4]! r[5]! r[6]! r[7]! r[8]! r[9]! yl yh
  timeIt "g128 comb lat" reps 200000 1 fun n => lat mul128Comb n xl xh yl yh
  timeIt "g128 comb thr" reps 50000 4 fun n => thr_mul128Comb n xl xh r[4]! r[5]! r[6]! r[7]! r[8]! r[9]! yl yh
  timeIt "g128 combU lat" reps 400000 1 fun n => lat mul128CombU n xl xh yl yh
  timeIt "g128 combU thr" reps 100000 4 fun n => thr_mul128CombU n xl xh r[4]! r[5]! r[6]! r[7]! r[8]! r[9]! yl yh
  timeIt "g128 win4a lat" reps 200000 1 fun n => lat mul128WinA n xl xh yl yh
  timeIt "g128 win4a thr" reps 50000 4 fun n => thr_mul128WinA n xl xh r[4]! r[5]! r[6]! r[7]! r[8]! r[9]! yl yh
  timeIt "g128 win4m lat" reps 1000000 1 fun n => lat mul128WinM n xl xh yl yh
  timeIt "g128 win4m thr" reps 250000 4 fun n => thr_mul128WinM n xl xh r[4]! r[5]! r[6]! r[7]! r[8]! r[9]! yl yh
  timeIt "g128 win4mU lat" reps 1000000 1 fun n => lat mul128WinMU n xl xh yl yh
  timeIt "g128 win4mU thr" reps 250000 4 fun n => thr_mul128WinMU n xl xh r[4]! r[5]! r[6]! r[7]! r[8]! r[9]! yl yh
  timeIt "g128 h32 lat" reps 2000000 1 fun n => lat mul128H32 n xl xh yl yh
  timeIt "g128 h32 thr" reps 500000 4 fun n => thr_mul128H32 n xl xh r[4]! r[5]! r[6]! r[7]! r[8]! r[9]! yl yh
  timeIt "g128 h64 lat" reps 2000000 1 fun n => lat mul128H64 n xl xh yl yh
  timeIt "g128 h64 thr" reps 500000 4 fun n => thr_mul128H64 n xl xh r[4]! r[5]! r[6]! r[7]! r[8]! r[9]! yl yh
  timeIt "g128 sq lat" reps 4000000 1 fun n => latSq n xl xh
  let fx := Fixed.mk' yl yh
  timeIt "g128 fixed-win4 lat" reps 1000000 1 fun n => latFixed fx n xl xh
  timeIt "g128 boxed-h64 lat" reps 2000000 1 fun n => (latBoxed n ⟨xl, xh⟩ ⟨yl, yh⟩).lo
  timeIt "g128 boxed-h32 lat" reps 2000000 1 fun n => (latBoxedH32 n ⟨xl, xh⟩ ⟨yl, yh⟩).lo
  let big := rand (seed + 1) 4096
  let a : Array G128 := (Array.range 1024).map fun i => ⟨big[2*i]!, big[2*i+1]!⟩
  let b : Array G128 := (Array.range 1024).map fun i => ⟨big[2048+2*i]!, big[2048+2*i+1]!⟩
  timeIt "g128 dot1024-boxed per-mul" reps 2000 1024 fun n =>
    (List.range n).foldl (fun c _ => (dot a b 1024 0 ⟨c, 0⟩).lo) 0
  timeIt "g128 dot1024-inline per-mul" reps 2000 1024 fun n =>
    (List.range n).foldl (fun c _ => dotI a b 1024 0 c 0) 0
  timeIt "g64 comb lat" reps 400000 1 fun n => lat64 mul64Comb n xl yl
  timeIt "g64 comb thr" reps 100000 4 fun n => thr_mul64Comb n xl r[4]! r[6]! r[8]! yl
  timeIt "g64 combU lat" reps 1000000 1 fun n => lat64 mul64CombU n xl yl
  timeIt "g64 combU thr" reps 250000 4 fun n => thr_mul64CombU n xl r[4]! r[6]! r[8]! yl
  timeIt "g64 h32 lat" reps 4000000 1 fun n => lat64 mul64H32 n xl yl
  timeIt "g64 h32 thr" reps 1000000 4 fun n => thr_mul64H32 n xl r[4]! r[6]! r[8]! yl
  timeIt "g64 h64 lat" reps 4000000 1 fun n => lat64 mul64H64 n xl yl
  timeIt "g64 h64 thr" reps 1000000 4 fun n => thr_mul64H64 n xl r[4]! r[6]! r[8]! yl
  let m : Vector UInt32 16 := Vector.ofFn fun i => (r[10 + i.val]!).toUInt32
  let h0 : Vector UInt32 8 := Vector.ofFn fun i => (r[30 + i.val]!).toUInt32
  timeIt "blake2s compressF lat" reps 2000000 1 fun n => blakeLat m n h0

def main (args : List String) : IO Unit := do
  match args with
  | ["check", s] => check s.toNat!.toUInt64
  | ["bench", s, k] => bench s.toNat!.toUInt64 k.toNat!
  | _ => IO.eprintln "usage: gfbench check SEED | bench SEED REPS"
