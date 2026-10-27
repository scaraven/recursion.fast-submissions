/-
  Phase 0 M, item 3: compiled-Lean binary-field multiplication, no imports beyond core.

  GF(2^128) = GF(2)[x] / (x^128 + x^7 + x^2 + x + 1), an element as two UInt64 limbs (lo, hi),
  bit i of lo the coefficient of x^i, bit i of hi that of x^(64+i).
  GF(2^64)  = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1) (CompPoly's BF64 modulus), one UInt64.

  Variants of the 64x64 -> 128 carry-less product (each then Karatsuba for GF(2^128) and reduced):
    naive  : GF(2^128) shift-and-xor directly, 128 branch-free steps (4 per round)
    comb   : 64-step branch-free comb per clmul64
    win4a  : 4-bit windows, the 16-entry table built per product in an `Array UInt64` (boxed)
    win4m  : 4-bit windows, table entries in locals, the lookup a `match` on the nibble
    h32    : integer multiplication with holes on 32-bit halves (16 imuls give the exact 64-bit
             carry-less product of two 32-bit words; spartan-srom's `clmul32`), Karatsuba twice
    h64    : integer multiplication with holes on 64-bit words (BearSSL ghash_ctmul64): low half
             from 16 imuls, high half from the bit-reversed operands
-/

namespace GF

/-- A 128-bit value as two words. -/
structure U128 where
  lo : UInt64
  hi : UInt64

/-! ## Reduction -/

/-- Reduce the 256-bit carry-less product p0 + p1 x^64 + p2 x^128 + p3 x^192 modulo
x^128 + x^7 + x^2 + x + 1. -/
@[inline] def red128 (p0 p1 p2 p3 : UInt64) : U128 :=
  let t3 := p3 ^^^ (p3 <<< 1) ^^^ (p3 <<< 2) ^^^ (p3 <<< 7)
  let c3 := (p3 >>> 63) ^^^ (p3 >>> 62) ^^^ (p3 >>> 57)
  let p1 := p1 ^^^ t3
  let p2 := p2 ^^^ c3
  let t2 := p2 ^^^ (p2 <<< 1) ^^^ (p2 <<< 2) ^^^ (p2 <<< 7)
  let c2 := (p2 >>> 63) ^^^ (p2 >>> 62) ^^^ (p2 >>> 57)
  ⟨p0 ^^^ t2, p1 ^^^ c2⟩

/-- Reduce lo + hi x^64 modulo x^64 + x^4 + x^3 + x + 1 (spartan-srom's `reduce`). -/
@[inline] def red64 (lo hi : UInt64) : UInt64 :=
  let d := hi ^^^ (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  lo ^^^ d ^^^ (d <<< 1) ^^^ (d <<< 3) ^^^ (d <<< 4)

/-- Karatsuba for GF(2^128) on a 64x64 carry-less product `m`. -/
@[inline] def kara (m : UInt64 → UInt64 → U128) (alo ahi blo bhi : UInt64) : U128 :=
  let z0 := m alo blo
  let z2 := m ahi bhi
  let z1 := m (alo ^^^ ahi) (blo ^^^ bhi)
  let mlo := z1.lo ^^^ z0.lo ^^^ z2.lo
  let mhi := z1.hi ^^^ z0.hi ^^^ z2.hi
  red128 z0.lo (z0.hi ^^^ mlo) (z2.lo ^^^ mhi) z2.hi

/-! ## (a) naive shift-and-xor over GF(2^128) -/

/-- Four steps: add `a` where the bit of `b` is set, then `a := a * x` (mod p), `b >>= 1`. -/
@[inline] def nstep (alo ahi b rlo rhi : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let m := (0 : UInt64) - (b &&& 1)
  let rlo := rlo ^^^ (alo &&& m)
  let rhi := rhi ^^^ (ahi &&& m)
  let c := (0 : UInt64) - (ahi >>> 63)
  let ahi := (ahi <<< 1) ||| (alo >>> 63)
  let alo := (alo <<< 1) ^^^ (c &&& 0x87)
  (alo, ahi, b >>> 1, rlo, rhi)

def naiveLoop : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → U128
  | 0, _, _, _, rlo, rhi => ⟨rlo, rhi⟩
  | n + 1, alo, ahi, b, rlo, rhi =>
    let (alo, ahi, b, rlo, rhi) := nstep alo ahi b rlo rhi
    let (alo, ahi, b, rlo, rhi) := nstep alo ahi b rlo rhi
    let (alo, ahi, b, rlo, rhi) := nstep alo ahi b rlo rhi
    let (alo, ahi, b, rlo, rhi) := nstep alo ahi b rlo rhi
    naiveLoop n alo ahi b rlo rhi

/-- The same 16 rounds, but carrying `a` on: returns (a * x^64, partial product). -/
def naiveLoopA : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → U128 × U128
  | 0, alo, ahi, _, rlo, rhi => (⟨alo, ahi⟩, ⟨rlo, rhi⟩)
  | n + 1, alo, ahi, b, rlo, rhi =>
    let (alo, ahi, b, rlo, rhi) := nstep alo ahi b rlo rhi
    let (alo, ahi, b, rlo, rhi) := nstep alo ahi b rlo rhi
    let (alo, ahi, b, rlo, rhi) := nstep alo ahi b rlo rhi
    let (alo, ahi, b, rlo, rhi) := nstep alo ahi b rlo rhi
    naiveLoopA n alo ahi b rlo rhi

@[inline] def mulNaive (alo ahi blo bhi : UInt64) : U128 :=
  let (a, r) := naiveLoopA 16 alo ahi blo 0 0
  naiveLoop 16 a.lo a.hi bhi r.lo r.hi

/-! ## (b0) comb: 64 branch-free steps per 64x64 product -/

def combLoop : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → U128
  | 0, _, _, _, lo, hi => ⟨lo, hi⟩
  | n + 1, a, b, i, lo, hi =>
    -- bit i of b: add a << i (and a >> (64 - i) to the high word; i = 0 adds nothing there)
    let m := (0 : UInt64) - ((b >>> i) &&& 1)
    let hiPart := ((a >>> 1) >>> (63 - i))
    let lo := lo ^^^ ((a <<< i) &&& m)
    let hi := hi ^^^ (hiPart &&& m)
    let i := i + 1
    let m := (0 : UInt64) - ((b >>> i) &&& 1)
    let hiPart := ((a >>> 1) >>> (63 - i))
    let lo := lo ^^^ ((a <<< i) &&& m)
    let hi := hi ^^^ (hiPart &&& m)
    combLoop n a b (i + 1) lo hi

@[inline] def clmulComb (a b : UInt64) : U128 := combLoop 32 a b 0 0 0

/-! ## (b) 4-bit windows (gf2x `mul1` with the repair of the top three bits of `a`) -/

/-- The repair: the bits of `a * k` above 63, lost in the 64-bit table, for `a`'s top three bits. -/
@[inline] def winRepair (a b h : UInt64) : UInt64 :=
  let h := h ^^^ (((b &&& 0xEEEEEEEEEEEEEEEE) >>> 1) &&& ((0 : UInt64) - (a >>> 63)))
  let h := h ^^^ (((b &&& 0xCCCCCCCCCCCCCCCC) >>> 2) &&& ((0 : UInt64) - ((a >>> 62) &&& 1)))
  h ^^^ (((b &&& 0x8888888888888888) >>> 3) &&& ((0 : UInt64) - ((a >>> 61) &&& 1)))

/-- The 16 multiples `a * k` (low 64 bits), as an array. -/
@[inline] def winTable (a : UInt64) : Array UInt64 :=
  let u2 := a <<< 1
  let u4 := a <<< 2
  let u8 := a <<< 3
  #[0, a, u2, u2 ^^^ a, u4, u4 ^^^ a, u4 ^^^ u2, u4 ^^^ u2 ^^^ a, u8, u8 ^^^ a, u8 ^^^ u2,
    u8 ^^^ u2 ^^^ a, u8 ^^^ u4, u8 ^^^ u4 ^^^ a, u8 ^^^ u4 ^^^ u2, u8 ^^^ u4 ^^^ u2 ^^^ a]

def winLoopA (t : Array UInt64) (b : UInt64) : Nat → UInt64 → UInt64 → UInt64 → U128
  | 0, _, lo, hi => ⟨lo, hi⟩
  | n + 1, i, lo, hi =>
    let g := t[((b >>> i) &&& 15).toNat]!
    winLoopA t b n (i + 4) (lo ^^^ (g <<< i)) (hi ^^^ (g >>> (64 - i)))

/-- 4-bit windows with a table given (built per product, or once for a fixed `a`). -/
@[inline] def clmulWinT (t : Array UInt64) (a b : UInt64) : U128 :=
  let g := t[(b &&& 15).toNat]!
  let r := winLoopA t b 15 4 g 0
  ⟨r.lo, winRepair a b r.hi⟩

@[inline] def clmulWinA (a b : UInt64) : U128 := clmulWinT (winTable a) a b

/-- The 16 multiples in locals. -/
structure T16 where
  (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : UInt64)

@[inline] def T16.sel (t : T16) (n : UInt64) : UInt64 :=
  match n.toUInt8 with
  | 0 => t.t0 | 1 => t.t1 | 2 => t.t2 | 3 => t.t3 | 4 => t.t4 | 5 => t.t5 | 6 => t.t6
  | 7 => t.t7 | 8 => t.t8 | 9 => t.t9 | 10 => t.t10 | 11 => t.t11 | 12 => t.t12 | 13 => t.t13
  | 14 => t.t14 | _ => t.t15

def winLoopM (t : T16) (b : UInt64) : Nat → UInt64 → UInt64 → UInt64 → U128
  | 0, _, lo, hi => ⟨lo, hi⟩
  | n + 1, i, lo, hi =>
    let g := t.sel ((b >>> i) &&& 15)
    winLoopM t b n (i + 4) (lo ^^^ (g <<< i)) (hi ^^^ (g >>> (64 - i)))

@[inline] def clmulWinM (a b : UInt64) : U128 :=
  let u2 := a <<< 1
  let u4 := a <<< 2
  let u8 := a <<< 3
  let t : T16 := ⟨0, a, u2, u2 ^^^ a, u4, u4 ^^^ a, u4 ^^^ u2, u4 ^^^ u2 ^^^ a, u8, u8 ^^^ a,
    u8 ^^^ u2, u8 ^^^ u2 ^^^ a, u8 ^^^ u4, u8 ^^^ u4 ^^^ a, u8 ^^^ u4 ^^^ u2, u8 ^^^ u4 ^^^ u2 ^^^ a⟩
  let r := winLoopM t b 15 4 (t.sel (b &&& 15)) 0
  ⟨r.lo, winRepair a b r.hi⟩

/-! ## (c) integer multiplication with holes -/

/-- The exact carry-less product of two words below 2^32 (spartan-srom's `clmul32`). -/
@[inline] def clmul32 (x y : UInt64) : UInt64 :=
  let x0 := x &&& 0x11111111
  let x1 := x &&& 0x22222222
  let x2 := x &&& 0x44444444
  let x3 := x &&& 0x88888888
  let y0 := y &&& 0x11111111
  let y1 := y &&& 0x22222222
  let y2 := y &&& 0x44444444
  let y3 := y &&& 0x88888888
  (((x0 * y0) ^^^ (x1 * y3) ^^^ (x2 * y2) ^^^ (x3 * y1)) &&& 0x1111111111111111) |||
    (((x0 * y1) ^^^ (x1 * y0) ^^^ (x2 * y3) ^^^ (x3 * y2)) &&& 0x2222222222222222) |||
    (((x0 * y2) ^^^ (x1 * y1) ^^^ (x2 * y0) ^^^ (x3 * y3)) &&& 0x4444444444444444) |||
    (((x0 * y3) ^^^ (x1 * y2) ^^^ (x2 * y1) ^^^ (x3 * y0)) &&& 0x8888888888888888)

/-- 64x64 -> 128 by Karatsuba over 32-bit halves (three `clmul32`). -/
@[inline] def clmulH32 (a b : UInt64) : U128 :=
  let a0 := a &&& 0xFFFFFFFF
  let a1 := a >>> 32
  let b0 := b &&& 0xFFFFFFFF
  let b1 := b >>> 32
  let p0 := clmul32 a0 b0
  let p2 := clmul32 a1 b1
  let pm := clmul32 (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p2
  ⟨p0 ^^^ (pm <<< 32), p2 ^^^ (pm >>> 32)⟩

/-- The low 64 bits of the carry-less product of two words (BearSSL `bmul64`): column sums below
the top reach at most 16 only at positions 60..63, whose carry leaves the word. -/
@[inline] def bmul64 (x y : UInt64) : UInt64 :=
  let x0 := x &&& 0x1111111111111111
  let x1 := x &&& 0x2222222222222222
  let x2 := x &&& 0x4444444444444444
  let x3 := x &&& 0x8888888888888888
  let y0 := y &&& 0x1111111111111111
  let y1 := y &&& 0x2222222222222222
  let y2 := y &&& 0x4444444444444444
  let y3 := y &&& 0x8888888888888888
  (((x0 * y0) ^^^ (x1 * y3) ^^^ (x2 * y2) ^^^ (x3 * y1)) &&& 0x1111111111111111) |||
    (((x0 * y1) ^^^ (x1 * y0) ^^^ (x2 * y3) ^^^ (x3 * y2)) &&& 0x2222222222222222) |||
    (((x0 * y2) ^^^ (x1 * y1) ^^^ (x2 * y0) ^^^ (x3 * y3)) &&& 0x4444444444444444) |||
    (((x0 * y3) ^^^ (x1 * y2) ^^^ (x2 * y1) ^^^ (x3 * y0)) &&& 0x8888888888888888)

/-- Bit reversal of a word. -/
@[inline] def rev64 (x : UInt64) : UInt64 :=
  let x : UInt64 := ((x >>> 1) &&& (0x5555555555555555 : UInt64)) ||| ((x &&& (0x5555555555555555 : UInt64)) <<< 1)
  let x : UInt64 := ((x >>> 2) &&& (0x3333333333333333 : UInt64)) ||| ((x &&& (0x3333333333333333 : UInt64)) <<< 2)
  let x : UInt64 := ((x >>> 4) &&& (0x0F0F0F0F0F0F0F0F : UInt64)) ||| ((x &&& (0x0F0F0F0F0F0F0F0F : UInt64)) <<< 4)
  let x : UInt64 := ((x >>> 8) &&& (0x00FF00FF00FF00FF : UInt64)) ||| ((x &&& (0x00FF00FF00FF00FF : UInt64)) <<< 8)
  let x : UInt64 := ((x >>> 16) &&& (0x0000FFFF0000FFFF : UInt64)) ||| ((x &&& (0x0000FFFF0000FFFF : UInt64)) <<< 16)
  (x >>> 32) ||| (x <<< 32)

/-- 64x64 -> 128: the low word by `bmul64`, the high word from the reversed operands. -/
@[inline] def clmulH64 (a b : UInt64) : U128 :=
  ⟨bmul64 a b, rev64 (bmul64 (rev64 a) (rev64 b)) >>> 1⟩

/-- GF(2^128) by Karatsuba with `bmul64` (BearSSL `ghash_ctmul64`: six `bmul64`, the reversals of
the operands shared by the middle product). -/
@[inline] def mulH64 (alo ahi blo bhi : UInt64) : U128 :=
  let a2 := alo ^^^ ahi
  let b2 := blo ^^^ bhi
  let alr := rev64 alo
  let ahr := rev64 ahi
  let blr := rev64 blo
  let bhr := rev64 bhi
  let a2r := alr ^^^ ahr
  let b2r := blr ^^^ bhr
  let z0 := bmul64 alo blo
  let z1 := bmul64 ahi bhi
  let z2 := bmul64 a2 b2
  let z0h := bmul64 alr blr
  let z1h := bmul64 ahr bhr
  let z2h := bmul64 a2r b2r
  let z2 := z2 ^^^ z0 ^^^ z1
  let z2h := z2h ^^^ z0h ^^^ z1h
  let z0h := rev64 z0h >>> 1
  let z1h := rev64 z1h >>> 1
  let z2h := rev64 z2h >>> 1
  red128 z0 (z0h ^^^ z2) (z1 ^^^ z2h) z1h

/-! ## The multiplications compared -/

@[inline] def mul128Naive (alo ahi blo bhi : UInt64) : U128 := mulNaive alo ahi blo bhi
@[inline] def mul128Comb (alo ahi blo bhi : UInt64) : U128 := kara clmulComb alo ahi blo bhi
@[inline] def mul128WinA (alo ahi blo bhi : UInt64) : U128 := kara clmulWinA alo ahi blo bhi
@[inline] def mul128WinM (alo ahi blo bhi : UInt64) : U128 := kara clmulWinM alo ahi blo bhi
@[inline] def mul128H32 (alo ahi blo bhi : UInt64) : U128 := kara clmulH32 alo ahi blo bhi
@[inline] def mul128H64 (alo ahi blo bhi : UInt64) : U128 := mulH64 alo ahi blo bhi

/-- Squaring: spread each half (bit i to bit 2i) and reduce. -/
@[inline] def spread (x : UInt64) : UInt64 :=
  let x := x &&& 0x00000000FFFFFFFF
  let x : UInt64 := (x ||| (x <<< 16)) &&& 0x0000FFFF0000FFFF
  let x : UInt64 := (x ||| (x <<< 8)) &&& 0x00FF00FF00FF00FF
  let x : UInt64 := (x ||| (x <<< 4)) &&& 0x0F0F0F0F0F0F0F0F
  let x : UInt64 := (x ||| (x <<< 2)) &&& 0x3333333333333333
  (x ||| (x <<< 1)) &&& 0x5555555555555555

@[inline] def sq128 (alo ahi : UInt64) : U128 :=
  red128 (spread alo) (spread (alo >>> 32)) (spread ahi) (spread (ahi >>> 32))

/-- GF(2^128) with a fixed multiplicand `b`: its three Karatsuba operands' window tables, once. -/
structure Fixed where
  b0 : UInt64
  b1 : UInt64
  b2 : UInt64
  t0 : Array UInt64
  t1 : Array UInt64
  t2 : Array UInt64

def Fixed.mk' (blo bhi : UInt64) : Fixed :=
  ⟨blo, bhi, blo ^^^ bhi, winTable blo, winTable bhi, winTable (blo ^^^ bhi)⟩

@[inline] def mulFixed (f : Fixed) (alo ahi : UInt64) : U128 :=
  let z0 := clmulWinT f.t0 f.b0 alo
  let z2 := clmulWinT f.t1 f.b1 ahi
  let z1 := clmulWinT f.t2 f.b2 (alo ^^^ ahi)
  let mlo := z1.lo ^^^ z0.lo ^^^ z2.lo
  let mhi := z1.hi ^^^ z0.hi ^^^ z2.hi
  red128 z0.lo (z0.hi ^^^ mlo) (z2.lo ^^^ mhi) z2.hi

/-! ## GF(2^64) -/

@[inline] def mul64H32 (a b : UInt64) : UInt64 := let p := clmulH32 a b; red64 p.lo p.hi
@[inline] def mul64H64 (a b : UInt64) : UInt64 := let p := clmulH64 a b; red64 p.lo p.hi
@[inline] def mul64Comb (a b : UInt64) : UInt64 := let p := clmulComb a b; red64 p.lo p.hi

/-- A boxed GF(2^128) element and a multiplication that is a real call returning a fresh
structure (what code keeping elements in structures and arrays pays). -/
structure G128 where
  lo : UInt64
  hi : UInt64
  deriving Inhabited

@[noinline] def G128.mul (a b : G128) : G128 :=
  let r := mul128H64 a.lo a.hi b.lo b.hi
  ⟨r.lo, r.hi⟩

@[noinline] def G128.mulH32 (a b : G128) : G128 :=
  let r := mul128H32 a.lo a.hi b.lo b.hi
  ⟨r.lo, r.hi⟩

end GF
