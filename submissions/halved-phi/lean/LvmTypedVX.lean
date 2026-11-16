-- New for lvm2 E2F (slice S1, E2F-Q): V_S's typed phases at S2GF, natively (the DM twin of
-- `LvmTypedSpecX.typedProgX`, read for read).
import LvmTypedV

/-!
# V_S's typed phases with the coordinate split (`dTypedX`)

Read for read as `LvmTypedSpecX.typedProgX` (s2gf AMENDMENT 1):

* `dZeroX`: `τ` (20), `ω`, 20 equality-mode rounds, six values `A₀, A₁, B₀, B₁, C₀, C₁`, the final claim against
  `A₀B₀ + A₁B₁ + C₀ + ω·(A₀B₁ + A₁B₀ + x·A₁B₁ + C₁)` (`x = FK.x`);
* `dWiringX`: `γ`, 21 rounds from `Σ_k γ^k v_k`, eight matrix values, four region values, the final claim against
  `(v₀ + γv₄ + γ²v₁ + γ³v₅ + γ⁴(v₂ + v₃) + γ⁵(v₆ + v₇))·(Σ regions + virtE)`;
* `dAccX`: A23 at `Φ_Q` in 44 variables, `κ` (3), `h` (45);
* `dRelayT`, `dMiniT`, `typedClaimsN`: roll 11's.

The record is roll 11's `TNat` with `phi` the 44-variable evaluator (`LvmWiringX.PhiQCX (cacheWX Q lay)`).
-/

namespace Lvm.TypedV

open Lvm DM
open Lvm.Typed (xVars yVars)

/-- `Φ_Q`'s variables with the coordinate bit (`LvmWiringX.phiVarsX`). -/
abbrev phiVarsNX : Nat := 3 + xVars + yVars

/-- **Zerocheck, coordinate-split** (`zeroProgX`). -/
def dZeroX : DM (List FE × List FE) := do
  let tau ← samples xVars
  let om ← sampleE
  let rf ← sumcheck 0 3 (tau.map some)
  let v ← readEs 6
  let a0 := v.getD 0 0
  let a1 := v.getD 1 0
  let b0 := v.getD 2 0
  let b1 := v.getD 3 0
  let c0 := v.getD 4 0
  let c1 := v.getD 5 0
  require (rf.2 == a0 * b0 + a1 * b1 + c0 + om * (a0 * b1 + a1 * b0 + FE.ofK FK.x * (a1 * b1) + c1))
  pure (rf.1, v)

/-- The wiring's batch of the eight matrix values (`wGX`). -/
def wGXF (g : FE) (vs : List FE) : FE :=
  vs.getD 0 0 + g * vs.getD 4 0 + g ^ 2 * vs.getD 1 0 + g ^ 3 * vs.getD 5 0 + g ^ 4 * (vs.getD 2 0 + vs.getD 3 0) +
    g ^ 5 * (vs.getD 6 0 + vs.getD 7 0)

/-- **Wiring, coordinate-split** (`wireProgX`). -/
def dWiringX (N : TNat) (pub : Pub) (v : List FE) : DM (List FE × List FE × List FE) := do
  let g ← sampleE
  let rf ← sumcheck (((List.range 6).map fun k => g ^ k * v.getD k 0).sum) 3 (List.replicate yVars none)
  let vs ← readEs 8
  let rv ← readEs 4
  require (rf.2 == wGXF g vs * (sumE rv + virtEF N pub rf.1))
  pure (rf.1, vs, rv)

/-- **A23 at `Φ_Q` in 44 variables** (`accProgQX`): `κ` (3), `h` (45), `t`, the zero scalar. -/
def dAccX (pub : Pub) (rxy vs : List FE) : DM Acc := do
  let kappa ← samples 3
  let h ← readEs (phiVarsNX + 1)
  let t ← sampleE
  let z ← readE
  require (h.headD 0 == pub.accIn.y)
  require (sumE h == dot (eqKernel kappa) vs)
  require (z == 0)
  pure ⟨accLine pub.accIn.pt (kappa ++ rxy) t, polyEval h t⟩

/-- **The typed phases at S2GF** (`typedProgX`): zerocheck, wiring, relayout, A23, the mini-bus; the folded
accumulator and the claims. -/
def dTypedX (p : Params) (N : TNat) (m : M3) (pub : Pub) :
    DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) := do
  let z ← dZeroX
  let w ← dWiringX N pub z.2
  let r ← dRelayT N w.1 (w.2.2.getD 1 0)
  let acc ← dAccX pub (z.1 ++ w.1) w.2.1
  let evals ← dMiniT p m N.mbT pub
  pure (acc, typedClaimsN N p w.1 w.2.2 r.1 r.2, evals)

end Lvm.TypedV
