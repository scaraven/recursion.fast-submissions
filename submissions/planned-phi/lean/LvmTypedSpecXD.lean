-- New for lvm2 E2F (slice S1, E2F-Q; E2AC-DES §1.2, §6 statement 12; transcript s2gf AMENDMENT 1, E2F-LEAD
-- 2026-11-13): the typed phases with the coordinate-split zerocheck and the definitions statement 12 (`typedSpecX`,
-- LvmTypedSpecX) is stated with; its proof is LvmTypedSpecXP.
import LvmTypedSpec
import LvmWiringX

/-!
# The typed phases with `E2` rows (`typedSpecX`)

The coordinate-split relation (`LvmWiringX.WiringRelX`) is checked by roll 8's phases with three changes
(s2gf AMENDMENT 1, (a)–(e)):

* **Zerocheck** (`zeroProgX`): `τ ∈ E^20`, then **`ω`** (one sample; with `τ` one group of 21, `leadTX`); 20 rounds of degree 3 from
  `0` in equality mode on `eq(τ, x)·(relX0(x) + ω·relX1(x))`; **six values** `A₀, A₁, B₀, B₁, C₀, C₁` at `r_x`
  (`C_s = D_s + W_s`); the final claim against `A₀B₀ + A₁B₁ + C₀ + ω·(A₀B₁ + A₁B₀ + x·A₁B₁ + C₁)`.
* **Wiring** (`wireProgX`): `γ`; 21 rounds of 3 values each (degree ≤ 2) from `Σ_k γ^k·v_k` (`k = 0..5` in the order above);
  **eight** matrix values `v_o` (`o = m + 4s`) and the four region values; the final claim against
  `(v₀ + γv₄ + γ²v₁ + γ³v₅ + γ⁴(v₂ + v₃) + γ⁵(v₆ + v₇))·z̃(r_y)` (`wGX`).
* **A23** (`accProgQX`) at `Φ_Q` in `phiVarsX = 44` variables: `κ ∈ E^3`, `h` with 45 coefficients.
* The relayout, the mini-bus and the returned claims are roll 11's (`relayProg`, `miniBusProg`, `typedClaims`).

**`typedSpecX`** (statement 12) is `typedSpecR`'s statement with `TGoodX` (the coordinate-split relation),
`AccOkTX` (`Φ_Q` in 44 variables) and `TErrsX` (`ω`'s group, `κ`'s three samples, A23 at 44 variables).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open Lvm.M3 (Tab inst stackOf comCell NoCG KeysOk AllSc LayOk FixOk)
open Lvm.ASM (OpenClaims)
open scoped ENNReal NNReal

/-! ## The phases -/

/-- **Zerocheck, coordinate-split** (step 1): `τ ∈ E^20`, `ω`; 20 rounds of degree 3 from `0` in equality mode;
the six values `A₀, A₁, B₀, B₁, C₀, C₁`; the final claim against the batched coordinates. Returns `(r_x, values)`. -/
def zeroProgX : VerifierProgram (List E × List E) :=
  (VerifierProgram.sampleChallenges xVars).bind fun τ ↦
    VerifierProgram.sampleChallenge.bind fun ω ↦
      (LeanVM.Protocol.Verifier.sumcheck 0 3 (τ.map some)).bind fun rf ↦
        (VerifierProgram.readScalars 6).bind fun v ↦
          (VerifierProgram.require (rf.2 =
            v.getD 0 0 * v.getD 2 0 + v.getD 1 0 * v.getD 3 0 + v.getD 4 0 +
              ω * (v.getD 0 0 * v.getD 3 0 + v.getD 1 0 * v.getD 2 0 + ofK g * (v.getD 1 0 * v.getD 3 0) +
                v.getD 5 0))).bind fun _ ↦
            VerifierProgram.ret (rf.1, v)

/-- The wiring's batch of the eight matrix values: `v₀ + γv₄ + γ²v₁ + γ³v₅ + γ⁴(v₂ + v₃) + γ⁵(v₆ + v₇)`
(`A₀, A₁, B₀, B₁, C₀, C₁` at `γ^0 … γ^5`). -/
def wGX (γ : E) (vs : List E) : E :=
  vs.getD 0 0 + γ * vs.getD 4 0 + γ ^ 2 * vs.getD 1 0 + γ ^ 3 * vs.getD 5 0 + γ ^ 4 * (vs.getD 2 0 + vs.getD 3 0) +
    γ ^ 5 * (vs.getD 6 0 + vs.getD 7 0)

/-- **Wiring, coordinate-split** (step 2): `γ`; 21 rounds of 3 values each (degree ≤ 2) from `Σ_k γ^k·v_k`; the eight matrix values
and the four region values; the final claim. Returns `(r_y, matrix values, region values)`. -/
def wireProgX (Ti : TInst) (pub : Lvm.Pub) (v : List E) : VerifierProgram (List E × List E × List E) :=
  VerifierProgram.sampleChallenge.bind fun γ ↦
    (LeanVM.Protocol.Verifier.sumcheck (((List.range 6).map fun k ↦ γ ^ k * v.getD k 0).sum) 3
        (List.replicate yVars none)).bind fun rf ↦
      (VerifierProgram.readScalars 8).bind fun vs ↦ (VerifierProgram.readScalars 4).bind fun rv ↦
        (VerifierProgram.require (rf.2 = wGX γ vs * (rv.sum + virtE Ti pub rf.1))).bind fun _ ↦
          VerifierProgram.ret (rf.1, vs, rv)

/-- **A23 at `Φ_Q` in 44 variables**: `κ` (3 samples), `h` (`phiVarsX + 1 = 45` coefficients), `t`, the zero
scalar. -/
def accProgQX (Q : Program) (lay : Lay) (ok : Bool) (yIn : E) (a rxy vs : List E) : VerifierProgram Unit :=
  Lvm.Acc.accProg 3 phiVarsX ok yIn a (yOwnQ vs) (bOfQ rxy) (PhiQX Q lay)

/-- **The typed phases, coordinate-split**: zerocheck, wiring, relayout, A23 at `Φ_Q` (44 variables), the
mini-bus; roll 11's claims. -/
@[irreducible] def typedProgX (Ti : TInst) (pub : Lvm.Pub) : VerifierProgram OpenClaims :=
  zeroProgX.bind fun z ↦ (wireProgX Ti pub z.2).bind fun w ↦ (relayProg Ti w.1 (w.2.2.getD 1 0)).bind fun r ↦
    (accProgQX Ti.Q Ti.lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (z.1 ++ w.1) w.2.1).bind
      fun _ ↦ (miniBusProg Ti).bind fun cl ↦ VerifierProgram.ret (typedClaims Ti w.1 w.2.2 r.1 r.2 cl)

/-! ## The specification -/

/-- **The typed half of a good pair, coordinate-split**: the relation `WiringRelX` on the candidate, and the
mini-bus balances. -/
def TGoodX (Ti : TInst) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pub : Lvm.Pub)
    (p : Column L.nuMain × Column L.nuRec) : Prop :=
  WiringRelX Ti.Q Ti.lay (Ti.zOf L pub p.1 p.2) ∧ M3Holds (inst L Ti.mbT hτ) () (stackOf L p.1 p.2)

/-- **The incoming accumulator holds at `Φ_Q` in 44 variables.** -/
def AccOkTX (Ti : TInst) (pub : Lvm.Pub) : Prop :=
  PhiQX Ti.Q Ti.lay (pub.accIn.pt.map FE.toExt3) = FE.toExt3 pub.accIn.y

/-- The coordinate-split zerocheck's lead: `τ`'s 20 samples and `ω`, one group (no prover move between them),
`21·L₀/|E|`. -/
noncomputable abbrev leadTX (L₀ : ℕ) : ℝ≥0∞ := (((xVars + 1 : ℕ) : ℝ≥0∞)) * ((L₀ : ℝ≥0∞) * errE 1) + 0

/-- The largest lead any typed phase hands its follower, coordinate-split: `τ`'s, the mini-bus's `(α, β)`, A23's
`κ` (three samples), the follower's `T`. -/
noncomputable abbrev leadMaxTX (L₀ : ℕ) (I : M3Instance) (T : ℝ≥0∞) : ℝ≥0∞ :=
  max (leadTX L₀) (max (abError I L₀ + 0) (max (3 * errE 1) T))

/-- **The typed phases' error side conditions, coordinate-split** (`TErrs` with `τ` and `ω` as one group of 21
samples — `zeroProgX` has no prover move between them, so `ω` cannot be its own group (E2F-Q-S12) — `κ`'s three
samples and A23 at `phiVarsX`). -/
structure TErrsX (L₀ : ℕ) (I : M3Instance) (εmax T : ℝ≥0∞) : Prop where
  lead : leadTX L₀ ≤ εmax
  rounds : ∀ d ≤ 4, roundError L₀ d + leadMaxTX L₀ I T ≤ εmax
  acc : errE phiVarsX + leadMaxTX L₀ I T ≤ εmax
  ab : abError I L₀ < 1 ∧ abError I L₀ + leadMaxTX L₀ I T ≤ εmax
  lam : interpLead L₀ 2 (lambdaError L₀) + leadMaxTX L₀ I T ≤ εmax ∧ lambdaError L₀ + leadMaxTX L₀ I T ≤ εmax
  xi : xiError I L₀ + leadMaxTX L₀ I T ≤ εmax
  follow : leadMaxTX L₀ I T ≤ εmax

end Lvm.Typed
