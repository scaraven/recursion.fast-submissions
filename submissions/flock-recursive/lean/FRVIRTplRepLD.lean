-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b; CF2: the carry automaton).
import FRVIRTplRepLW
import FRVIRTplRepLG

/-!
# The replay template of a node's `evalL` (`NI4F.evalL4I ν`): definitions

One node kind's sub-template for the previous node's `evalL` (inputs `rL : AF a`, then `r4 : AF b`).
This module holds the definitions only (no import of `FRVerifierImplNode4F`, so the fold into
`nodeIRows4` can import it); `FRVIRTplRepL` proves them.

CF2: every sum is a carry automaton (`autoG`, `FRVIRTplRepLG`; about 20 gates per bit and state)
instead of C1b's `eq` tables and `2 · vslots · nJ` products (319.5 k rows over the three kinds):

* `S_σ = Σ_{j<nJ} eq(rL, σ nJ + j) · eq(r4_lo, 299 + j)` and `E_σ = Σ_{j<nJ} eq(rL, σ nJ + j)`;
* `eq(r4_hi, hb + σ)` and `eq(r4, oneCell)` (`n = 1` automata);
* `Q_σ = eq(r4_hi, hb + σ) · S_σ`, `O = eq(r4, oneCell)`, and one product `(Σ_σ E_σ) · O`.

The outputs are `Σ_σ Q_σ`, `(Σ_σ E_σ) · O − Σ_σ Q_σ` and `0`.
-/

namespace FR
namespace Tpl
open Circ

/-- Declared bits per slot (`NI4F.nJ`, the same numeral). -/
def nJL : ℕ := 266 + 399 + 7552 + 3

/-- The bit factors of an `n`-coordinate block `c` (bit `l`: `c l` or `1 − c l`; past `n`: `0` for a
set bit, `1` otherwise). -/
def qE (c : ℕ → LinT) (n l : ℕ) (bit : Bool) : LinT :=
  if l < n then (if bit then c l else C 1 ++ sc (-1) (c l)) else (if bit then [] else C 1)

/-- The trivial factors. -/
def qO (_ : ℕ) (_ : Bool) : LinT := C 1

section EvL
variable (ν : Rev4.NodeKind) (a b : ℕ)

/-- The high cell block of slot `0`'s bits (`lBase·128 / 2^14`). -/
def evHb : ℕ := ν.lBase * 128 / 2 ^ 14

/-- **The gates and outputs** (inputs `rL : AF a`, then `r4 : AF b`). -/
def evGM : GM (List LinT) :=
  (autoG (qE (cT a) ν.dims.logL) (qE (cR a b) 14) ν.dims.logL
    ((List.range ν.vslots).map fun σ => (nJL, σ * nJL, 299))).bind fun S =>
  (autoG (qE (cT a) ν.dims.logL) qO ν.dims.logL ((List.range ν.vslots).map fun σ => (nJL, σ * nJL, 0))).bind fun E =>
  (autoG (qE (cR a b) 14) qO 14 [(1, ν.oneCell % 2 ^ 14, 0)]).bind fun O1 =>
  (autoG (qE (fun l => cR a b (14 + l)) (ν.m - 7 - 14)) qO (ν.m - 7 - 14)
    (((List.range ν.vslots).map fun σ => (1, evHb ν + σ, 0)) ++ [(1, ν.oneCell / 2 ^ 14, 0)])).bind fun H =>
  (GM.mapL (fun σ => mulF (H.getD σ []) (S.getD σ [])) (List.range ν.vslots)).bind fun Q =>
  (mulF (O1.getD 0 []) (H.getD ν.vslots [])).bind fun O =>
  (mulF E.flatten O).map fun EO => [Q.flatten, EO ++ sc (-1) Q.flatten, []]

end EvL

/-- **The node kind `ν`'s `evalL` template** (inputs `rL : AF a`, then `r4 : AF b`). -/
def tplEvL (ν : Rev4.NodeKind) (a b : ℕ) : Tpl := let g := evGM ν a b 0; ⟨g.1, g.2⟩

theorem tplEvL_outs (ν : Rev4.NodeKind) (a b : ℕ) : (tplEvL ν a b).outs.length = 3 := rfl

end Tpl
end FR
