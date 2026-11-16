-- New for lvm2 S1 (E2-F, E2F-V): `E2 = K[X]/(X² + xX + 1)` on two machine words, the fast twin of
-- `LvmFieldE2`'s `E2` for V_S (the prover's `gf2_64x2.rs` `F128`). Its agreement is `LvmFieldE2Correct`.
import LvmFieldK

/-!
# `E2` on machine words

`FE2` is `re + im·X` with `re, im : FK` and `X² = 1 + xX` (`x = FK.x`), the coordinates `c0`, `c1` of
the prover's `F128` (16 bytes, `re` first).

* Addition is coordinatewise `xor`.
* Multiplication is Karatsuba with three `FK` products `p0 = a0 b0`, `p1 = a1 b1`,
  `m = (a0 + a1)(b0 + b1)`: `re = p0 + p1`, `im = m + p0 + p1 + x·p1` (`gf2_64x2.rs` `mul_unreduced`
  then `reduce`, here with reduced products).
* `mulK`: the mixed product by `k ∈ K`, two products.
* Squaring: `(a0² + a1²) + x·a1²·X`. Inversion through the norm `a0² + x a0 a1 + a1²`, `0⁻¹ = 0`.
* Powers by square-and-multiply (`powGo`).
-/

namespace Lvm

/-- An element of `E2`: `re + im·X`. -/
structure FE2 where
  /-- The constant coordinate (`c0`). -/
  re : FK
  /-- The `X` coordinate (`c1`). -/
  im : FK
  deriving DecidableEq, Inhabited

namespace FE2

instance : Zero FE2 := ⟨⟨0, 0⟩⟩
instance : One FE2 := ⟨⟨1, 0⟩⟩

/-- Coordinatewise `xor`. -/
@[inline] def add (a b : FE2) : FE2 := ⟨a.re + b.re, a.im + b.im⟩

instance : Add FE2 := ⟨add⟩
instance : Sub FE2 := ⟨add⟩
instance : Neg FE2 := ⟨fun a => a⟩

/-- **Karatsuba**: three products. -/
@[inline] def mul (a b : FE2) : FE2 :=
  let p0 := a.re * b.re
  let p1 := a.im * b.im
  let m := (a.re + a.im) * (b.re + b.im)
  ⟨p0 + p1, m + p0 + p1 + FK.x * p1⟩

instance : Mul FE2 := ⟨mul⟩

/-- The mixed product by `k ∈ K`. -/
@[inline] def mulK (a : FE2) (k : FK) : FE2 := ⟨a.re * k, a.im * k⟩

/-- `K ↪ E2`. -/
@[inline] def ofK (k : FK) : FE2 := ⟨k, 0⟩

/-- Squaring: `(a0² + a1²) + x·a1²·X`. -/
@[inline] def sq (a : FE2) : FE2 :=
  let s0 := FK.sq a.re
  let s1 := FK.sq a.im
  ⟨s0 + s1, FK.x * s1⟩

/-- The inverse through the norm `N = a0² + x a0 a1 + a1²`: `(a0 + x a1)/N + (a1/N)·X`; `0⁻¹ = 0`. -/
def inv (a : FE2) : FE2 :=
  let n := (a.re * a.re + FK.x * a.re * a.im + a.im * a.im)⁻¹
  ⟨(a.re + FK.x * a.im) * n, a.im * n⟩

instance : Inv FE2 := ⟨inv⟩

/-- Square-and-multiply: `powGo k b e acc = acc * b ^ e` whenever `e ≤ k`, the fuel `k` making the
recursion structural (as `FK.powGo`). -/
def powGo : Nat → FE2 → Nat → FE2 → FE2
  | 0, _, _, acc => acc
  | k + 1, b, e, acc =>
    if e = 0 then acc else powGo k (sq b) (e / 2) (if e % 2 = 1 then acc * b else acc)

/-- Powers by repeated squaring. -/
instance : Pow FE2 Nat := ⟨fun a n => powGo n a n 1⟩

/-- The sixteen bytes, `re` first (little-endian words). -/
def toBytes (a : FE2) : List UInt8 := (FK.toBytes a.re).toList ++ (FK.toBytes a.im).toList

end FE2

end Lvm
