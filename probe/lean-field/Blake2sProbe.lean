/-
  COPY (definitions only, no proofs) of recursion.fast core `RecursionFast/Library/Blake2sFast.lean`
  at 15dac52: `W16`, `G`, `mix0`..`mix7`, `roundF`, `compressF`, and the contract's `iv`
  (`RecursionFast/Contract/Hash/Blake2s.lean`). The original imports Mathlib only for its proofs
  (`compressF_eq`); the compiled code is the same.
-/
namespace Blake2sProbe

/-- The BLAKE2s initialization vector (RFC 7693 §2.6). -/
def iv : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The sixteen words of `F`'s working vector, as separate fields. -/
structure W16 where
  (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32)

/-- The working vector as the contract's vector. -/
def W16.toVec (w : W16) : Vector UInt32 16 :=
  #v[w.v0, w.v1, w.v2, w.v3, w.v4, w.v5, w.v6, w.v7, w.v8, w.v9, w.v10, w.v11, w.v12, w.v13,
    w.v14, w.v15]

/-- The mixing function `G` on four words, rotations by constants. -/
@[inline] def G (a b c d x y : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let va := a + b + x
  let t := d ^^^ va
  let vd := t >>> 16 ||| t <<< 16
  let vc := c + vd
  let t := b ^^^ vc
  let vb := t >>> 12 ||| t <<< 20
  let va := va + vb + y
  let t := vd ^^^ va
  let vd := t >>> 8 ||| t <<< 24
  let vc := vc + vd
  let t := vb ^^^ vc
  let vb := t >>> 7 ||| t <<< 25
  (va, vb, vc, vd)

/-- `mix` at positions `0 4 8 12` (a column), on separate words. -/
@[inline] def mix0 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v0 w.v4 w.v8 w.v12 x y; { w with v0 := a, v4 := b, v8 := c, v12 := d }
/-- `mix` at positions `1 5 9 13` (a column), on separate words. -/
@[inline] def mix1 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v1 w.v5 w.v9 w.v13 x y; { w with v1 := a, v5 := b, v9 := c, v13 := d }
/-- `mix` at positions `2 6 10 14` (a column), on separate words. -/
@[inline] def mix2 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v2 w.v6 w.v10 w.v14 x y; { w with v2 := a, v6 := b, v10 := c, v14 := d }
/-- `mix` at positions `3 7 11 15` (a column), on separate words. -/
@[inline] def mix3 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v3 w.v7 w.v11 w.v15 x y; { w with v3 := a, v7 := b, v11 := c, v15 := d }
/-- `mix` at positions `0 5 10 15` (a diagonal), on separate words. -/
@[inline] def mix4 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v0 w.v5 w.v10 w.v15 x y; { w with v0 := a, v5 := b, v10 := c, v15 := d }
/-- `mix` at positions `1 6 11 12` (a diagonal), on separate words. -/
@[inline] def mix5 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v1 w.v6 w.v11 w.v12 x y; { w with v1 := a, v6 := b, v11 := c, v12 := d }
/-- `mix` at positions `2 7 8 13` (a diagonal), on separate words. -/
@[inline] def mix6 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v2 w.v7 w.v8 w.v13 x y; { w with v2 := a, v7 := b, v8 := c, v13 := d }
/-- `mix` at positions `3 4 9 14` (a diagonal), on separate words. -/
@[inline] def mix7 (w : W16) (x y : UInt32) : W16 :=
  let (a, b, c, d) := G w.v3 w.v4 w.v9 w.v14 x y; { w with v3 := a, v4 := b, v9 := c, v14 := d }

/-- One round on separate words, the message words given in the round's order. -/
@[inline] def roundF (w : W16) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    W16 :=
  mix7 (mix6 (mix5 (mix4 (mix3 (mix2 (mix1 (mix0 w x0 x1) x2 x3) x4 x5) x6 x7) x8 x9) x10 x11)
    x12 x13) x14 x15

/-- `compress` on separate words, the schedule `sigma` written out. -/
def compressF (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let m0 := m[0]; let m1 := m[1]; let m2 := m[2]; let m3 := m[3]; let m4 := m[4]
  let m5 := m[5]; let m6 := m[6]; let m7 := m[7]; let m8 := m[8]; let m9 := m[9]
  let m10 := m[10]; let m11 := m[11]; let m12 := m[12]; let m13 := m[13]; let m14 := m[14]
  let m15 := m[15]
  let v : W16 := ⟨h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], iv[0], iv[1], iv[2], iv[3],
    iv[4] ^^^ t.toUInt32, iv[5] ^^^ (t >>> 32).toUInt32, iv[6] ^^^ f0, iv[7] ^^^ f1⟩
  let v := roundF v m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
  let v := roundF v m14 m10 m4 m8 m9 m15 m13 m6 m1 m12 m0 m2 m11 m7 m5 m3
  let v := roundF v m11 m8 m12 m0 m5 m2 m15 m13 m10 m14 m3 m6 m7 m1 m9 m4
  let v := roundF v m7 m9 m3 m1 m13 m12 m11 m14 m2 m6 m5 m10 m4 m0 m15 m8
  let v := roundF v m9 m0 m5 m7 m2 m4 m10 m15 m14 m1 m11 m12 m6 m8 m3 m13
  let v := roundF v m2 m12 m6 m10 m0 m11 m8 m3 m4 m13 m7 m5 m15 m14 m1 m9
  let v := roundF v m12 m5 m1 m15 m14 m13 m4 m10 m0 m7 m6 m3 m9 m2 m8 m11
  let v := roundF v m13 m11 m7 m14 m12 m1 m3 m9 m5 m0 m15 m4 m8 m6 m2 m10
  let v := roundF v m6 m15 m14 m9 m11 m3 m0 m8 m12 m2 m13 m7 m1 m4 m10 m5
  let v := roundF v m10 m2 m8 m4 m7 m6 m1 m5 m15 m11 m9 m14 m3 m12 m13 m0
  #v[h[0] ^^^ v.v0 ^^^ v.v8, h[1] ^^^ v.v1 ^^^ v.v9, h[2] ^^^ v.v2 ^^^ v.v10,
     h[3] ^^^ v.v3 ^^^ v.v11, h[4] ^^^ v.v4 ^^^ v.v12, h[5] ^^^ v.v5 ^^^ v.v13,
     h[6] ^^^ v.v6 ^^^ v.v14, h[7] ^^^ v.v7 ^^^ v.v15]


end Blake2sProbe
