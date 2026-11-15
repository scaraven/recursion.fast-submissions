-- New for lvm2 E2F (slice S1, E2F-QH2): the row switch's weight in the circuit (design/E2-S-switch.md §2.4 and §3
-- "V cost", the CRT route): `Ŵ(r) = Σ_j ρ_j c_j(P(r))`, `P(r) = Π_l (1 + z_l ⊗ 1 + 1 ⊗ r_l) ∈ E2 ⊗_{F₂} E3`
-- (V's `tensorWD`), evaluated through `K ⊗_{F₂} E3 ≅ E3^64`, `a ⊗ e ↦ (a^(2^k) e)_k`, with no bit matrices.
import LvmQRingRow

/-!
# The row weight by the CRT (`rowNuG`, `rowLeafG`)

Write `E2 ⊗_{F₂} E3 = (K ⊗ E3)[X]/(X² + xX + 1)` and `P = P₀ + P₁X`, `P_h ∈ K ⊗ E3`. The CRT sends `P_h` to its
components `P_{h,k} = (σ^k ⊗ 1)(P_h)` (`σ` the Frobenius of `K`); component `k` of `E2 ⊗ E3` is the quadratic
algebra `E3[X]/(X² + x^(2^k) X + 1)`, and a factor `1 + z ⊗ 1 + 1 ⊗ r` (`z = a + bX`) has component
`(1 + a^(2^k) + r) + b^(2^k) X`.

The coordinate `c_{(i,h)}(P)` on `x^i X^h ⊗ 1` is `Tr(δ_i P_h)` (`δ` the trace-dual basis of `(x^i)`), so with
`ρ_{(i,h)} = e_i·(1 + r₆ or r₆)` (`e = eq(r''₀…₅, ·)`):

  `Ŵ = Σ_k ν_k·((1 + r₆)·P_{0,k} + r₆·P_{1,k})`,  `ν_k = Σ_i δ_i^(2^k)·e_i`.

* **`dualK i`**: `δ_i = β_i / f'(x)`, `f(y)/(y − x) = Σ β_i y^i`, `f'(x) = x² + 1` (`f = y⁶⁴ + y⁴ + y³ + y + 1`);
  `dualTab k i = δ_i^(2^k)` (computed once).
* **`rowNuG rw`** (once per switch, from `RowOut`): `e_i = ρ_i + ρ_{i+64}`, `ν` (4,096 `lin` rows), `ν·(1 + r₆)`,
  `ν·r₆`.
* **`rowLeafG nu z κ xb`**: the Frobenius powers of every coordinate of `z` (and of `κ`, an extra factor
  `κ ⊗ 1`; `none` for none), the 64 component products, `Σ_k ν0_k A_k + ν1_k B_k`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## The trace-dual basis -/

/-- `x^i` in `K`. -/
def xPowK (i : Nat) : FK := ⟨UInt64.ofNat (2 ^ i)⟩

/-- The coefficients of `f(y) = y⁶⁴ + y⁴ + y³ + y + 1` below `y⁶⁴`. -/
def fCoef (i : Nat) : FK := if i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4 then 1 else 0

/-- `β_i`: `f(y)/(y − x) = Σ_{i<64} β_i y^i` (`β₆₃ = 1`, `β_{i−1} = f_i + x·β_i`), from the top. -/
def quotCoefs : Array FK :=
  ((List.range 63).foldl (fun (acc : List FK) i =>
    let b := acc.headD 1
    (fCoef (63 - i) + FK.x * b) :: acc) [1]).toArray

/-- `δ_i = β_i / (x² + 1)`. -/
def dualK (i : Nat) : FK := quotCoefs.getD i 0 * (FK.x * FK.x + 1)⁻¹

/-- `δ_i^(2^k)`, `k, i < 64` (row `k`). -/
def dualTab : Array (Array FK) :=
  (List.range 64).toArray.map fun k => (List.range 64).toArray.map fun i => FK.frob k (dualK i)

/-- `δ_i^(2^k)`. -/
def dualAt (k i : Nat) : FK := (dualTab.getD k #[]).getD i 0

/-- `x^(2^k)`, the twist of component `k`. -/
def twist (k : Nat) : FK := FK.frob k FK.x

/-! ## Per switch -/

/-- What a switch hands to its weight leaves: `ν_k·(1 + r₆)` and `ν_k·r₆` (`E` cells, `k < 64`). -/
structure RowNu where
  nu0 : List Cell
  nu1 : List Cell

/-- `acc + Σ_i k_i·a_i` on `E` rows (`lin` with a constant). -/
def linSumE : Cell → List (FK × Cell) → BM Cell
  | acc, [] => pure acc
  | acc, (k, a) :: r => lin .E k 0 acc a >>= fun acc' => linSumE acc' r

/-- **`ν` of a switch** from its `RowOut` (`z`, `o`: `E` zero and one cells). -/
def rowNuG (rw : RowOut) (z o : Nat) : BM RowNu :=
  mapB (fun i => add (rw.eqR.getD i default) (rw.eqR.getD (i + 64) default)) (List.range 64) >>= fun e =>
  mapB (fun k => linSumE (ec z) ((List.range 64).map fun i => (dualAt k i, e.getD i default))) (List.range 64) >>=
    fun nu =>
  let r6 := rw.rr.getD 6 default
  add r6 (ec o) >>= fun r6' =>
  mapB (fun k => mulAdd .E (nu.getD k default) r6' (ec z)) (List.range 64) >>= fun nu0 =>
  mapB (fun k => mulAdd .E (nu.getD k default) r6 (ec z)) (List.range 64) >>= fun nu1 =>
  pure ⟨nu0, nu1⟩

/-! ## The leaf -/

/-- `a, a², a⁴, …, a^(2^63)` (`K` rows; `zk` a `K` zero cell). -/
def frobsK (zk : Cell) (a : Cell) : BM (List Cell) :=
  (List.range 63).foldl (fun (m : BM (List Cell)) _ => m >>= fun l =>
    mulAdd .K (l.getD 0 default) (l.getD 0 default) zk >>= fun s => pure (s :: l)) (pure [a]) >>= fun l =>
  pure l.reverse

/-- The Frobenius powers of an `E2` value's two coordinates. -/
structure Frob2 where
  re : List Cell
  im : List Cell

/-- `(A, B)·(α, β)` in `E3[X]/(X² + tX + 1)`: `(Aα + Bβ, Aβ + Bα + t·Bβ)` (`β` a `K` cell). -/
def qmul (t : FK) (z : Cell) (A B α β : Cell) : BM (Cell × Cell) :=
  mulAdd .E B β z >>= fun q => mulAdd .E A α q >>= fun re =>
  lin .E (t + 1) 0 q q >>= fun tq => mulAdd .E B α tq >>= fun i1 => mulAdd .E A β i1 >>= fun im =>
  pure (re, im)

/-- A factor's component: `(1 + a^(2^k) + r, b^(2^k))`, `r` an `E` cell or (for `κ ⊗ 1`) `a^(2^k)` alone. -/
def factorK (k : Nat) (f : Frob2) (r : Option Cell) : BM (Cell × Cell) :=
  match r with
  | some x => lin .E 1 1 x (f.re.getD k default) >>= fun α => pure (α, f.im.getD k default)
  | none => pure (f.re.getD k default, f.im.getD k default)

/-- Component `k` of `Π` of the factors (the first one is the start). -/
def compK (z : Cell) (k : Nat) : List (Frob2 × Option Cell) → BM (Cell × Cell)
  | [] => pure (z, z)
  | (f, r) :: fs => factorK k f r >>= fun a0 =>
    fs.foldl (fun (m : BM (Cell × Cell)) (fr : Frob2 × Option Cell) => m >>= fun acc =>
      factorK k fr.1 fr.2 >>= fun ab => qmul (twist k) z acc.1 acc.2 ab.1 ab.2) (pure a0)

/-- **The row weight at the basis point** (`E` cells `xb + l`, `l < |zs|`): `Σ_j ρ_j c_j((κ ⊗ 1)·Π_l (1 + z_l ⊗ 1 +
1 ⊗ x_l))`; `z`/`zk` `E`/`K` zero cells. -/
def rowLeafG (nu : RowNu) (zs : List C2) (κ : Option C2) (xb : Nat) (z zk : Cell) : BM Cell :=
  mapB (fun c => frobsK zk c.re >>= fun fr => frobsK zk c.im >>= fun fi => pure (⟨fr, fi⟩ : Frob2)) zs >>= fun fz =>
  (match κ with
    | some c => frobsK zk c.re >>= fun fr => frobsK zk c.im >>= fun fi => pure [((⟨fr, fi⟩ : Frob2), (none : Option Cell))]
    | none => pure []) >>= fun fk =>
  let fs := (List.range zs.length).map (fun l => (fz.getD l ⟨[], []⟩, some (ec (xb + l)))) ++ fk
  mapB (fun k => compK z k fs) (List.range 64) >>= fun P =>
  linSumE z [] >>= fun z0 =>
  (List.range 64).foldl (fun (m : BM Cell) k => m >>= fun acc =>
    mulAdd .E (nu.nu0.getD k default) (P.getD k (z, z)).1 acc >>= fun a1 =>
    mulAdd .E (nu.nu1.getD k default) (P.getD k (z, z)).2 a1) (pure z0)

end Lvm.Q2
