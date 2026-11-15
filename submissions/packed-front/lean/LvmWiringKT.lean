-- New for lvm2 (roll 8 = B1, B1-K): the data types of the wiring's matrix entries and of their operand classes
-- (B1-P1P2 §2), moved out of `LvmWiring` (B1-S0) unchanged so that the kernels and the compiled evaluator
-- (`LvmWiringK`) and the class derivation (`LvmWiringKD`) can be imported by `LvmWiring`.
import LvmTypedLayout

/-!
# Entries and operand classes

* `Ent`: a matrix entry `(o, x, y, c)`, its index `Ent.idx` on `Φ_Q`'s cube (`o` the low 2 bits, then `x`, then `y`);
* `Aff`: an affine word map of the iteration bits; `Aff.isK1` (a bit injection);
* `OpClass`: the operand classes K1/K3 (`aff`), K2 (`shift`), sub-cube splits (`split`), points;
* `TSrc`, `CTerm`: one term of the matrices (one entry position of one row, at every iteration).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-- A matrix entry: matrix `o` (0 `A`, 1 `B`, 2 `D`, 3 `W`), slot `x`, word `y`, coefficient `c`. -/
structure Ent where
  /-- The matrix. -/
  o : ℕ
  /-- The slot. -/
  x : ℕ
  /-- The word. -/
  y : ℕ
  /-- The coefficient. -/
  c : FE
  deriving DecidableEq, Inhabited

/-- Entries of matrix `o` at slot `x`. -/
def tagE (o x : ℕ) (l : List (ℕ × FE)) : List Ent := l.map fun p ↦ ⟨o, x, p.1, p.2⟩

/-- An entry's index on `Φ_Q`'s cube: `o` the low 2 bits, then `x`, then `y`. -/
def Ent.idx (e : Ent) : ℕ := e.o + 4 * (e.x + 2 ^ xVars * e.y)

/-! ## Operand classes (B1-P1P2 §2) -/

/-- An affine word map of the iteration: `y0 + Σ_i bit_i(jf)·coef_i`. -/
structure Aff where
  /-- The word at iteration `0`. -/
  y0 : ℕ
  /-- Per iteration bit, its coefficient. -/
  coef : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The word at iteration `jf`. -/
def Aff.at (a : Aff) (jf : ℕ) : ℕ :=
  a.y0 + ((List.range a.coef.length).map fun i ↦ if jf.testBit i then a.coef.getD i 0 else 0).sum

/-- **K1**: the coefficients are distinct powers of two (or `0`, a broadcast bit) and do not carry into `y0`:
a bit injection, whose extension is a product of one-bit factors. Otherwise **K3**, a record read
`b + R·j_out + o` (the carry automaton, B-DES §1.4). -/
def Aff.isK1 (a : Aff) : Bool :=
  (a.coef.foldl (fun (acc : Option ℕ) c ↦ acc.bind fun u ↦
    if c = 0 then some u else if c &&& (c - 1) = 0 ∧ u &&& c = 0 then some (u ||| c) else none) (some a.y0)).isSome

/-- **An operand's class**: its word at iteration `jf` (limb by limb: one term per word of the row's entries). -/
inductive OpClass where
  /-- K1 or K3 (`Aff.isK1`). -/
  | aff (a : Aff)
  /-- **K2**, the shift on the iteration field `[p, p + n)` (the flat `prev`, or the last loop dimension: a
  sumcheck's previous round): at field value `v ≥ 1` the map `sh` at the iteration with the field `v − 1`; at
  `v = 0` the map `ini` (the init cell, or the previous loop's last row). -/
  | shift (p n : ℕ) (sh ini : Aff)
  /-- **A sub-cube split** of a piecewise-affine target (QLT's static `readd`, a Keccak lane rotation): each part
  fixes some iteration bits `(bit, value)`; the first matching part's map. -/
  | split (parts : List (List (ℕ × Bool) × Aff))
  /-- **Points**: the words per iteration, enumerated (glue rows, loops of ≤ 16 iterations). -/
  | point (ys : List ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- The word of a class at iteration `jf`. -/
def OpClass.at : OpClass → ℕ → ℕ
  | .aff a, jf => a.at jf
  | .shift p n sh ini, jf =>
    if (jf / 2 ^ p) % 2 ^ n = 0 then ini.at jf else sh.at (jf - 2 ^ p)
  | .split parts, jf =>
    match parts.find? (fun q ↦ q.1.all fun bv ↦ jf.testBit bv.1 == bv.2) with
    | some q => q.2.at jf
    | none => 0
  | .point ys, jf => ys.getD jf 0

/-- Where a term lives: template row `t` of block `b`, or row `r` of auxiliary block `k`. -/
inductive TSrc where
  /-- A template row. -/
  | row (b t : ℕ)
  /-- An auxiliary row. -/
  | aux (k r : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- **A term of the matrices**: entry `idx` of its row's entries at every iteration `jf < 2^l`: matrix `o`,
weight `w` (or `wv[jf]`), slot `x0 + jf`, word `cls.at jf`. -/
structure CTerm where
  /-- Its row. -/
  src : TSrc
  /-- Its position in the row's entries. -/
  idx : ℕ
  /-- `log₂` of the row's iterations. -/
  l : ℕ
  /-- The matrix. -/
  o : ℕ
  /-- The weight. -/
  w : FE
  /-- The slot at iteration `0`. -/
  x0 : ℕ
  /-- The word's class. -/
  cls : OpClass
  /-- Per-iteration weights, when they vary (a constant cell's value: QLT in `Φ_Q`); `[]`: the weight `w`. -/
  wv : List FE := []
  deriving DecidableEq, Inhabited

/-- A term's weight at iteration `jf`. -/
def CTerm.wAt (c : CTerm) (jf : ℕ) : FE := if c.wv.isEmpty then c.w else c.wv.getD jf 0

/-- A term's entry at iteration `jf`. -/
def CTerm.at (c : CTerm) (jf : ℕ) : Ent := ⟨c.o, c.x0 + jf, c.cls.at jf, c.wAt jf⟩

end Lvm.Typed
