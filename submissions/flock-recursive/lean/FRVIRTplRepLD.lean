-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b).
import FRVIRTplRepLW

/-!
# The replay template of a node's `evalL` (`NI4F.evalL4I ν`): definitions

One node kind's sub-template for the previous node's `evalL` (inputs `rL : AF a`, then `r4 : AF b`),
gate for gate `evalL4I ν rL r4`. This module holds the definitions only (no import of
`FRVerifierImplNode4F`, so the fold into `nodeIRows4` can import it); `FRVIRTplRepL` proves them.

* four `eq` tables (`tabsG`): `rL`'s low 9 and high `logL − 9` coordinates (`bt`), `r4`'s low 14
  (`tY`) and high `m − 21` (the slots' and `one`'s high factors);
* `E` (`vslots · nJ` products): `e_i = A[i mod 512] · B[⌊i/512⌋] = eq(rL, i)`;
* `F` (`vslots · nJ` products): `e_i · tY[299 + i mod nJ]`;
* `Q` (`vslots` products): `eq(r4_hi, hb + σ) · Σ_j F_{σ nJ + j}`;
* `O` (one product): `eq(r4, oneCell)` from `tY` and the high table;
* one `mulAdd`: `(Σ_i e_i) · O − Σ_σ Q_σ`.

The outputs are `Σ_σ Q_σ`, that local, and `0`.
-/

namespace FR
namespace Tpl
open Circ

section EvL
variable (ν : Rev4.NodeKind) (a b : ℕ)

/-- Declared bits per slot (`NI4F.nJ`, the same numeral). -/
def nJL : ℕ := 266 + 399 + 7552 + 3

/-- The four tables' coordinate forms (`rL` on inputs `0 … a−1`, `r4` on `a … a+b−1`). -/
def evCs : List (List LinT) :=
  [(List.range 9).map (cT a), (List.range (ν.dims.logL - 9)).map fun l => cT a (9 + l),
   (List.range 14).map (cR a b), (List.range (ν.m - 7 - 14)).map fun l => cR a b (14 + l)]

/-- The tables' gates and entries. -/
def evT : List Gate × List (List LinT) := tabsG (evCs ν a b) 0

/-- Entry `i` of table `j`. -/
def evE (j i : ℕ) : LinT := ((evT ν a b).2.getD j []).getD i []

/-- The L rows: `vslots · nJ`. -/
def evN : ℕ := ν.vslots * nJL

/-- The high cell block of slot `0`'s bits (`lBase·128 / 2^14`). -/
def evHb : ℕ := ν.lBase * 128 / 2 ^ 14

/-- **The template's context**, built once per instance: the tables' entries (arrays) and the
tables' locals (a piece that recomputed the tables at every reference made the template quadratic
to build). -/
structure EvCx where
  E : ℕ → ℕ → LinT
  k1 : ℕ

def mkEvCx (ν : Rev4.NodeKind) (a b : ℕ) : EvCx :=
  let T := evT ν a b
  let A := T.2.toArray.map List.toArray
  ⟨fun j i => (A.getD j #[]).getD i [], nlocs T.1⟩

end EvL

section EvLC
variable (ν : Rev4.NodeKind) (cx : EvCx)

/-- The stages' first locals. -/
def evK2 : ℕ := cx.k1 + evN ν
def evK3 : ℕ := evK2 ν cx + evN ν
def evK4 : ℕ := evK3 ν cx + ν.vslots

/-- `Σ_σ Q_σ` (the first output). -/
def evS2 : LinT := sumG ν.vslots fun σ => L (evK3 ν cx + σ)

/-- **The node kind `ν`'s `evalL` template** (inputs `rL : AF a`, then `r4 : AF b`). -/
def tplEvLx (a b : ℕ) : Tpl :=
  ⟨(evT ν a b).1 ++
    (mulsG (evN ν) (fun i => cx.E 0 (i % 512)) (fun i => cx.E 1 (i / 512)) ++
    (mulsG (evN ν) (fun i => L (cx.k1 + i)) (fun i => cx.E 2 (299 + i % nJL)) ++
    (mulsG ν.vslots (fun σ => cx.E 3 (evHb ν + σ))
      (fun σ => sumG nJL fun j => L (evK2 ν cx + (σ * nJL + j))) ++
    (mulsG 1 (fun _ => cx.E 2 (ν.oneCell % 2 ^ 14)) (fun _ => cx.E 3 (ν.oneCell / 2 ^ 14)) ++
    [.mulAdd (sumG (evN ν) fun i => L (cx.k1 + i)) (L (evK4 ν cx)) (sc (-1) (evS2 ν cx))])))),
   [evS2 ν cx, L (evK4 ν cx + 1), []]⟩

end EvLC

/-- **The node kind `ν`'s `evalL` template** (inputs `rL : AF a`, then `r4 : AF b`), its context
built once. -/
def tplEvL (ν : Rev4.NodeKind) (a b : ℕ) : Tpl := let cx := mkEvCx ν a b; tplEvLx ν cx a b

theorem tplEvL_outs (ν : Rev4.NodeKind) (a b : ℕ) : (tplEvL ν a b).outs.length = 3 := rfl

theorem mkEvCx_k1 (ν : Rev4.NodeKind) (a b : ℕ) : (mkEvCx ν a b).k1 = nlocs (evT ν a b).1 := rfl

theorem mkEvCx_E (ν : Rev4.NodeKind) (a b j i : ℕ) : (mkEvCx ν a b).E j i = evE ν a b j i := by
  simp only [mkEvCx, evE, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  cases ((evT ν a b).2)[j]? <;> simp

end Tpl
end FR
