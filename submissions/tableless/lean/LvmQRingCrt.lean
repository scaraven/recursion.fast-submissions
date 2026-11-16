-- New for lvm2 E2F (slice S1, E2F-QH2): the row switch's weight in the circuit (design/E2-S-switch.md §2.4 and §3
-- "V cost", the CRT route): `Ŵ(r) = Σ_j ρ_j c_j(P(r))`, `P(r) = Π_l (1 + z_l ⊗ 1 + 1 ⊗ r_l) ∈ E2 ⊗_{F₂} E3`
-- (V's `tensorWD`), evaluated through `K ⊗_{F₂} E3 ≅ E3^64`, `a ⊗ e ↦ (a^(2^k) e)_k`, with no bit matrices.
import LvmQRingRow
import LvmQSumcheckCore

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

/-! ## Blob v4 (lever L1): the same weights in loops over the 64 components

Iteration `j < 64` of every loop below is component `c(j) = (j + 1) mod 64` (`a^(2^64) = a` in `K`): a squaring loop
whose prologue holds `a` gives `a^(2^(j+1)) = a^(2^c(j))` at iteration `j`, so the components' Frobenius powers, the
twists `x^(2^c)` and the duals `δ_i^(2^c)` are all one loop's outputs, read at stride one word (`K1`). `RowNu`'s lists
stay in component order (`nu0[c]` is iteration `(c + 63) mod 64`'s cell).
-/

/-- The squaring template: row `t` writes `prev(t)²` (`K`; `zk` a `K` zero cell). -/
def frobTpl (zk : Cell) (n : Nat) : List LRow :=
  (List.range n).map fun t => ⟨.muladd, .K, [.prev t, .prev t, zk.opd]⟩

/-- **The squaring loop** of the cells `as`: row `t`'s output at iteration `j` is `as[t]^(2^(j+1))`. -/
def frobLoop (zk : Cell) (as : List Cell) : BM LoopOut :=
  loopP [6] (frobTpl zk as.length) (fun t => as.getD t default)

/-- The `ν` template (per component): `acc_i = δ_i^(2^c)·e_i + acc_{i−1}` (`i < 64`, `D` the duals' squaring loop),
then `ν·(1 + r₆)` and `ν·r₆`. -/
def nuTpl (D : LoopOut) (e : List Cell) (r6' r6 : Cell) (z : Nat) : List LRow :=
  (List.range 64).map (fun i =>
    ⟨.muladd, .E, [.abs (D.addr i), (e.getD i default).opd, if i = 0 then (ec z).opd else .cur (i - 1)]⟩) ++
  [⟨.muladd, .E, [.cur 63, r6'.opd, (ec z).opd]⟩, ⟨.muladd, .E, [.cur 63, r6.opd, (ec z).opd]⟩]

/-- **`ν` of a switch in loops** (`rowNuG`'s values): the duals `δ_i` as constants, their squaring loop, the `ν` loop.
`nu0[c]`, `nu1[c]` are the `ν` loop's rows 64 and 65 at iteration `(c + 63) mod 64`. -/
def rowNuGL (rw : RowOut) (z o : Nat) : BM RowNu :=
  mapB (fun i => add (rw.eqR.getD i default) (rw.eqR.getD (i + 64) default)) (List.range 64) >>= fun e =>
  const .K 0 (kc 0) >>= fun zk =>
  mapB (fun i => const .K (dualK i) (kc 0)) (List.range 64) >>= fun ds =>
  frobLoop zk ds >>= fun D =>
  let r6 := rw.rr.getD 6 default
  add r6 (ec o) >>= fun r6' =>
  loop [6] (nuTpl D e r6' r6 z) >>= fun N =>
  pure ⟨(List.range 64).map (fun c => N.cell 64 ((c + 63) % 64)), (List.range 64).map (fun c => N.cell 65 ((c + 63) % 64))⟩

open Lvm.Q1 (Ins Src tplOf)

/-- The address of a `RowNu` list's loop row: iteration `j`'s cell is `l[j + 1]` (component order, `rowNuGL`). -/
def nuAddr (l : List Cell) : Addr :=
  ⟨.E, (l.getD 1 default).n, [(l.getD 2 default).n - (l.getD 1 default).n]⟩

/-- `qmul`'s five instructions from row `t0` (`(A, B)·(α, β)` in `E3[X]/(X² + t X + 1)`, `t` read at `tw`): `q = B·β`,
`re = A·α + q`, `t·q`, `i1 = B·α + t·q`, `im = A·β + i1`; `re` at `t0 + 1`, `im` at `t0 + 4`. -/
def qmIns (z : Cell) (tw : Src) (t0 : Nat) (A B α β : Src) : List Ins :=
  [⟨.muladd, .E, [B, β, .ext z.addr]⟩, ⟨.muladd, .E, [A, α, .loc t0]⟩, ⟨.muladd, .E, [.loc t0, tw, .ext z.addr]⟩,
    ⟨.muladd, .E, [B, α, .loc (t0 + 2)]⟩, ⟨.muladd, .E, [A, β, .loc (t0 + 3)]⟩]

/-- The component instructions (iteration `j`, component `c(j)`): with `F` the squaring loop of
`[re₀, im₀, …, re_{n−1}, im_{n−1}] (++ [κ_re, κ_im]) ++ [x]`, the factors `(1 + a_l^(2^c) + x_l, b_l^(2^c))` (and
`(κ_re^(2^c), κ_im^(2^c))`) multiplied left to right (`qmIns`, `t = x^(2^c)`), then `s = ν0·A + ν1·B` (the last
row). -/
def compIns (F : LoopOut) (n : Nat) (κ : Bool) (xb : Nat) (z : Cell) (nu0 nu1 : Addr) : List Ins :=
  let tw : Src := .ext (F.addr (2 * n + if κ then 2 else 0))
  let fre (l : Nat) : Src := .ext (F.addr (2 * l))
  let fim (l : Nat) : Src := .ext (F.addr (2 * l + 1))
  let step (acc : List Ins × Src × Src) (l : Nat) : List Ins × Src × Src :=
    let ta := acc.1.length
    (acc.1 ++ ⟨.lin 1 1, .E, [.ext (ec (xb + l)).addr, fre l]⟩ :: qmIns z tw (ta + 1) acc.2.1 acc.2.2 (.loc ta) (fim l),
      .loc (ta + 2), .loc (ta + 5))
  let r := (List.range (n - 1)).foldl (fun acc l => step acc (l + 1))
    ([⟨.lin 1 1, .E, [.ext (ec xb).addr, fre 0]⟩], .loc 0, fim 0)
  let r := if κ then
      let t0 := r.1.length
      (r.1 ++ qmIns z tw t0 r.2.1 r.2.2 (.ext (F.addr (2 * n))) (.ext (F.addr (2 * n + 1))), .loc (t0 + 1),
        .loc (t0 + 4))
    else r
  let ts := r.1.length
  r.1 ++ [⟨.muladd, .E, [.ext nu0, r.2.1, .ext z.addr]⟩, ⟨.muladd, .E, [.ext nu1, r.2.2, .loc ts]⟩]

/-- **The row weight at the basis point, in loops** (`rowLeafG`'s value): the squaring loop, the component loop, the
sum of the 64 components' `s` (a two-row accumulation loop). -/
def rowLeafGL (nu : RowNu) (zs : List C2) (κ : Option C2) (xb : Nat) (z zk : Cell) : BM Cell :=
  const .K FK.x zk >>= fun x =>
  let srcs := zs.flatMap (fun c => [c.re, c.im]) ++ (match κ with | some c => [c.re, c.im] | none => []) ++ [x]
  frobLoop zk srcs >>= fun F =>
  let ins := compIns F zs.length κ.isSome xb z (nuAddr nu.nu0) (nuAddr nu.nu1)
  loop [6] (tplOf ins) >>= fun P =>
  loopP [6] (tplOf [⟨.lin 1 0, .E, [.prev 0, .ext (P.addr (ins.length - 1))]⟩]) (fun _ => z) >>= fun S =>
  pure (S.cell 0 63)

end Lvm.Q2
