-- New for lvm6 Y1 (2026-11-22): the typed phases at `E = GF(2^128)` (zerocheck, wiring, relayout, A23, the mini-bus),
-- re-parameterised from season 1's S2GT/S2GL (`LvmE2TProg`, `LvmS2GLMid`): one `E` relation per slot (two `K`
-- coordinates, no `ω`), `Φ_Q` in 43 variables, claims at `E` (no re/im split), the mini-bus at `E`; and the frozen
-- statement `TypedSpecEStmt` (docs/lvm6/stages/Y1-typed.md §2.1). Definitions only; proofs in `Lvm6Ty*`.
import Lvm6MbProg
import LvmE2TWiring
import LvmTypedSpecP

/-!
# The typed phases at `E2` (definitions and the frozen statement)

Season 1's typed phases were already at `E2` with a nonce per challenge (S2GT, `typedSpecT`). Three `E3` residues
are removed here (A1 Q1):
* **The relation** (`relE`, `WiringRelE`): `Q`'s `E` cells are two-limb `E2` twin rows, so the relation at a slot
  is one `E2` equation `A·B + C = 0` on the coordinate-`0` matrices of `entsT` (`matZT Q lay m`, `m < 4`); S1's
  `E3 ⊗_K E2` product `mulY3` and the batching challenge `ω` are gone. A program without `E3` rows
  (`NoE3`) has no other entries, so `WiringRelE` is then S1's relation (`Lvm6TyZero.wiringRelE_iff`).
* **`Φ_Q`** (`PhiQE`) is the sparse extension of the four matrices in `phiVarsE = 2 + 20 + 21 = 43` variables
  (matrix in 2 bits, then `x`, then `y`); A23 draws `κ ∈ E2^2`.
* **The claims** are `E2` claims (`Lvm6.Mb.ClaimE`), one per region and one point claim (no split into `K`-linear
  halves); the mini-bus's three claims follow on `C_main`.

The order on the wire (FORMAT6-T-typed.md §1): `τ` (20 groups `G(1)`), 20 equality-mode rounds (`E(2)`, `G(2)`),
`A, B, C`; `γ` (`G(2)`), 21 rounds (`E(2)`, `G(2)`), four matrix and four region values; `relayRounds`
relayout rounds (18 at `P17`),
`v_R`; `κ` (2 groups `G(1)`), `h` (44 scalars), `t` (`G(6)`); the mini-bus (`Lvm6.Mb.miniBusLProg6`).
-/

set_option autoImplicit false

namespace Lvm6.Ty

open Lvm.Loop Lvm.Typed Lvm.E2V LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd.Front
open Lvm.M3 (Tab inst KeysOk AllSc LayOk FixOk)
open Lvm6.Mb (ClaimE BClaimG miniBusLProg6 mbLinB6 miniDepth stackOf gAB gLam gRd gY gYl kG)
open scoped ENNReal

/-! ## Proof-of-work bits (`g = ⌈log₂(8c/7)⌉`, PARAM §1) -/

/-- `τ_i`: numerator 1. -/
abbrev gTau : ℕ := 1
/-- Zerocheck rounds: numerator 3 (as S1; the proof needs 2, the equality factor peeled). -/
abbrev gZero : ℕ := 2
/-- `γ`: numerator 2 (three values). -/
abbrev gGamma : ℕ := 2
/-- Wiring and relayout rounds: numerator 2. -/
abbrev gWire : ℕ := 2
/-- `κ_j`: numerator 1. -/
abbrev gKappa : ℕ := 1
/-- A23's `t`: numerator `phiVarsE = 43`. -/
abbrev gT : ℕ := 6

/-! ## The typed instance -/

/-- **A typed instance at `E2`** (season 1's `TInst` without the statement's public values, which the phases take
as an argument): the program, its layout, the mini-bus's tables and where the regions live. -/
structure TInst6 where
  /-- The program. -/
  Q : Program
  /-- Its typed layout. -/
  lay : Lay
  /-- The mini-bus's tables. -/
  mbT : List Tab
  /-- The `C_main` word of a committed word. -/
  comW : ℕ → ℕ
  /-- The `C_main` word of a `KS` alias word. -/
  ksW : ℕ → ℕ
  /-- The `C_rec` word of an `S_flat` word. -/
  sflatW : ℕ → ℕ
  /-- The `C_rec` word of a `σ′` word. -/
  sigmaW : ℕ → ℕ
  /-- The `QLT` words (public). -/
  qltV : ℕ → Lvm.FK

namespace TInst6

variable (Ti : TInst6)

/-- The source of word `y`. -/
def src? (y : ℕ) : Option YSrc :=
  (Ti.lay.yregs.find? fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)).map (·.src)

/-- Cell `n` of commitment `rec` (`C_rec` if `rec`, else `C_main`; `0` past it). -/
def comCell (L : Lvm.M3.Lay) (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) (n : ℕ) : K :=
  if rec then (if h : n < 2 ^ L.nuRec then qr.values[n] else 0)
  else (if h : n < 2 ^ L.nuMain then qm.values[n] else 0)

/-- **A candidate pair's words**: committed and `KS` words from `C_main`, `S_flat` and `σ′` from `C_rec`, `PUB`
from the public words `pw`, `QLT`, the constant `1`. -/
def zOf (L : Lvm.M3.Lay) (pw : ℕ → Lvm.FK) (qm : Column L.nuMain) (qr : Column L.nuRec) (y : ℕ) : Lvm.FK :=
  match Ti.src? y with
  | some .com => Lvm.FK.ofBF64 (comCell L qm qr false (Ti.comW y))
  | some .ks => Lvm.FK.ofBF64 (comCell L qm qr false (Ti.ksW y))
  | some .sflat => Lvm.FK.ofBF64 (comCell L qm qr true (Ti.sflatW y))
  | some .sigma => Lvm.FK.ofBF64 (comCell L qm qr true (Ti.sigmaW y))
  | some .pub => pw y
  | some .qlt => Ti.qltV y
  | some .one => 1
  | none => 0

/-- **The instance check**: the layout is one of `Q`, and its word `1` lies in a `one` region. -/
def Ok : Prop := Ti.lay.Ok Ti.Q ∧ Ti.src? Ti.lay.one = some .one

/-- **The region maps land in the commitments.** -/
def MapsFit (L : Lvm.M3.Lay) : Prop :=
  ∀ y, match Ti.src? y with
    | some .com => Ti.comW y < 2 ^ L.nuMain
    | some .ks => Ti.ksW y < 2 ^ L.nuMain
    | some .sflat => Ti.sflatW y < 2 ^ L.nuRec
    | some .sigma => Ti.sigmaW y < 2 ^ L.nuRec
    | _ => True

end TInst6

/-- The relayout's rounds: `C_rec`'s variables, 18 at `P17` (FORMAT6 v2.6 §6.4a: `C_rec = ⟨18, 33·2^18⟩`, one slot
of `2^18` words; 19 at `P18`). -/
abbrev relayRounds : ℕ := 18

/-! ## The relation at `E2` and `Φ_Q` -/

/-- **The relation at slot `x`**: `A·B + C` in `E2`, `A = M_0 z`, `B = M_1 z`, `C = M_2 z + M_3 z` (the
coordinate-`0` matrices of `entsT`). -/
def relE (Q : Program) (lay : Lay) (z : ℕ → Lvm.FK) (x : ℕ) : Lvm.FE2 :=
  matZT Q lay 0 z x * matZT Q lay 1 z x + (matZT Q lay 2 z x + matZT Q lay 3 z x)

/-- **The wiring relation at `E2`**: the relation vanishes at every slot. -/
def WiringRelE (Q : Program) (lay : Lay) (z : ℕ → Lvm.FK) : Prop := ∀ x, relE Q lay z x = 0

/-- `Q` has no `E3` row: every entry's coefficient is in `K` (the static condition under which `WiringRelE` is
season 1's relation). -/
def NoE3 (Q : Program) (lay : Lay) : Prop := ∀ e ∈ entsX Q lay, e.c.c₁ = 0 ∧ e.c.c₂ = 0

/-- The selector bits of `Φ_Q` at `E2`: four matrices. -/
abbrev selBitsE : ℕ := 2

/-- **`Φ_Q`'s variables at `E2`**: `2 + 20 + 21 = 43`. -/
abbrev phiVarsE : ℕ := selBitsE + xVars + yVars

/-- The four matrices' entries at `E2` (the coordinate-`0` entries of `entsT`). -/
def entsE (Q : Program) (lay : Lay) : List EntT := (entsT Q lay).filter fun e ↦ decide (e.o < 4)

/-- An entry's index on `Φ_Q`'s cube at `E2`: matrix (2 bits), slot, word. -/
def EntT.idxE (e : EntT) : ℕ := e.o + 4 * (e.x + 2 ^ xVars * e.y)

/-- **`Φ_Q` executably at `E2`**, at a point of `phiVarsE` coordinates. -/
def PhiQFE (Q : Program) (lay : Lay) (pt : List Lvm.FE2) : Lvm.FE2 :=
  (entsE Q lay).foldr (fun e acc ↦ e.c * eqWT pt (EntT.idxE e) + acc) 0

/-- **`Φ_Q` over `E2`** (A23's `Φ` at v6, 43 variables). -/
def PhiQE (Q : Program) (lay : Lay) (pt : List E2) : E2 := Lvm.FE2.toE2 (PhiQFE Q lay (pt.map ofE2))

/-! ## Region sums and the executable part of `z̃` -/

/-- `Σ_{regions of a source in S} Σ_{y in the region} f(y)`. -/
def regSumW {α : Type} [Add α] [Zero α] (Ti : TInst6) (S : YSrc → Bool) (f : ℕ → α) : α :=
  (Ti.lay.yregs.map fun reg ↦ if S reg.src then
    ((List.range (2 ^ reg.log)).map fun i ↦ f (reg.base + i)).sum else 0).sum

/-- `Σ eq(r, y)·f(y)` over the regions of a source in `S`, at `E2`. -/
def regSumT (Ti : TInst6) (S : YSrc → Bool) (f : ℕ → E2) (r : List E2) : E2 :=
  regSumW Ti S fun y ↦ eqAtF r y * f y

/-- **The executable part of `z̃(r_y)`**: `PUB`, `QLT`, `1`. -/
def virtE (Ti : TInst6) (pw : ℕ → Lvm.FK) (ry : List E2) : E2 :=
  regSumT Ti (fun s ↦ s == .pub) (fun y ↦ kG (pw y)) ry +
    regSumT Ti (fun s ↦ s == .qlt) (fun y ↦ kG (Ti.qltV y)) ry +
    regSumT Ti (fun s ↦ s == .one) (fun _ ↦ 1) ry

/-! ## The phases -/

/-- **Zerocheck at `E2`**: `τ` (20 ground coordinates), 20 equality-mode rounds from `0` (degree 2 after the peeled
factor), `A, B, C` at `r_x`, the final claim `A·B + C`. Returns `(r_x, [A, B, C])`. -/
def zeroProgE : VerifierProgram (List E2 × List E2) :=
  e2Samples gTau xVars >>= fun τ ↦ sumcheckE2 gZero 0 3 (τ.map some) >>= fun rf ↦ e2Reads 3 >>= fun v ↦
    VerifierProgram.require (rf.2 = v.getD 0 0 * v.getD 1 0 + v.getD 2 0) >>= fun _ ↦ pure (rf.1, v)

/-- The wiring's start: `A + γ·B + γ²·C`. -/
def wBatchE (γ : E2) (v : List E2) : E2 := v.getD 0 0 + γ * v.getD 1 0 + γ ^ 2 * v.getD 2 0

/-- The wiring's batch of the four matrix values: `v_A + γ·v_B + γ²·(v_D + v_W)`. -/
def wGE (γ : E2) (vs : List E2) : E2 := vs.getD 0 0 + γ * vs.getD 1 0 + γ ^ 2 * (vs.getD 2 0 + vs.getD 3 0)

/-- **Wiring at `E2`**: `γ`; 21 rounds of degree 2; four matrix values, four region values (committed, `S_flat`,
`σ′`, `KS`); the final claim against `wGE γ vs · z̃(r_y)`. Returns `(r_y, matrix values, region values)`. -/
def wireProgE (Ti : TInst6) (pw : ℕ → Lvm.FK) (v : List E2) : VerifierProgram (List E2 × List E2 × List E2) :=
  e2Sample gGamma >>= fun γ ↦ sumcheckE2 gWire (wBatchE γ v) 3 (List.replicate yVars none) >>= fun rf ↦
    e2Reads 4 >>= fun vs ↦ e2Reads 4 >>= fun rv ↦
      VerifierProgram.require (rf.2 = wGE γ vs * (sumF rv + virtE Ti pw rf.1)) >>= fun _ ↦ pure (rf.1, vs, rv)

/-- The relayout's kernel at `E2`. -/
def relayKernE (Ti : TInst6) (ry r : List E2) : E2 := regSumT Ti (fun s ↦ s == .sflat) (fun y ↦ eqAtF r (Ti.sflatW y)) ry

/-- **The `S_flat` relayout at `E2`**: `relayRounds` rounds of degree 2; `v_R`. Returns `(r, v_R)`. -/
def relayProgE (Ti : TInst6) (ry : List E2) (vS : E2) : VerifierProgram (List E2 × E2) :=
  sumcheckE2 gWire vS 3 (List.replicate relayRounds none) >>= fun rf ↦ e2Read >>= fun vR ↦
    VerifierProgram.require (rf.2 = relayKernE Ti ry rf.1 * vR) >>= fun _ ↦ pure (rf.1, vR)

/-- A23's line from `a` to `b`. -/
def lineE (a b : List E2) (t : E2) : List E2 := List.zipWith (fun x y ↦ x + t * (x + y)) a b

/-- The line polynomial's value. -/
def hEvalE (hs : List E2) (t : E2) : E2 := hs.foldr (fun c acc ↦ c + t * acc) 0

/-- `y_own(κ) = Σ_o eq(κ, o)·v_o` over the four matrix values. -/
def yOwnE (vs κ : List E2) : E2 := dotF (eqKernelF κ) vs

/-- **A23 at `Φ_Q` in 43 variables**: `κ` (2 ground coordinates), `h` (44 scalars), `t`; the checks. -/
def accProgE (Q : Program) (lay : Lay) (yIn : E2) (a rxy vs : List E2) : VerifierProgram Unit :=
  e2Samples gKappa selBitsE >>= fun κ ↦ e2Reads (phiVarsE + 1) >>= fun hs ↦ e2Sample gT >>= fun t ↦
    VerifierProgram.require (hEvalE hs 0 = yIn ∧ hEvalE hs 1 = yOwnE vs κ ∧
      PhiQE Q lay (lineE a (κ ++ rxy) t) = hEvalE hs t)

/-! ## The claims -/

/-- **A region claim at `E2`**: `Σ_{y, src y = s} eq(r, y)·q[w(y)] = v`, the weight on the commitment's cube. -/
def regClaimE (Ti : TInst6) (s : YSrc) (w : ℕ → ℕ) (r : List E2) (v : E2) : ClaimE :=
  (fun X ↦ regSumT Ti (fun s' ↦ s' == s) (fun y ↦ eqAtF X (w y)) r, v)

/-- The claims the typed phases hand the opening: on `C_rec`, on `C_main`. -/
abbrev OpenClaimsE : Type := List ClaimE × List ClaimE

/-- **The typed claims at `E2`**: on `C_rec` the relayout's point claim (`C_rec`'s whole `⟨relayRounds, 0⟩`) and
`σ′`'s; on
`C_main` the committed block's, the `KS` aliases' and the mini-bus's three. -/
def typedClaimsE (Ti : TInst6) (ry rv rr : List E2) (vR : E2) (cl : List ClaimE) : OpenClaimsE :=
  ([(BClaimG.point ⟨relayRounds, 0⟩ rr vR).onStack, regClaimE Ti .sigma Ti.sigmaW ry (rv.getD 2 0)],
    [regClaimE Ti .com Ti.comW ry (rv.getD 0 0), regClaimE Ti .ks Ti.ksW ry (rv.getD 3 0)] ++ cl)

/-- **The typed phases at `E2`**: zerocheck, wiring, relayout, A23 at `Φ_Q` (the incoming accumulator `acc`), the
mini-bus at `E2`; the claims. -/
@[irreducible] noncomputable def typedProgE (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → Lvm.FK)
    (acc : List E2 × E2) : VerifierProgram OpenClaimsE :=
  zeroProgE >>= fun z ↦ wireProgE Ti pw z.2 >>= fun w ↦ relayProgE Ti w.1 (w.2.2.getD 1 0) >>= fun r ↦
    accProgE Ti.Q Ti.lay acc.2 acc.1 (z.1 ++ w.1) w.2.1 >>= fun _ ↦
      miniBusLProg6 L Ti.mbT miniDepth >>= fun cl ↦ pure (typedClaimsE Ti w.1 w.2.2 r.1 r.2 cl)

/-! ## The relation, the accumulator, the errors -/

/-- **The typed half of a good pair at `E2`**: the relation at `E2` on the candidate's words, and the mini-bus
balances. -/
def TGoodE (Ti : TInst6) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → Lvm.FK)
    (p : Column L.nuMain × Column L.nuRec) : Prop :=
  WiringRelE Ti.Q Ti.lay (Ti.zOf L pw p.1 p.2) ∧ M3Holds (inst L Ti.mbT hτ) () (stackOf L p.1 p.2)

/-- **The incoming accumulator holds at `Φ_Q`** (43 variables). -/
def AccOkE (Ti : TInst6) (acc : List E2 × E2) : Prop := PhiQE Ti.Q Ti.lay acc.1 = acc.2

/-- The returned claims hold on a pair. -/
def TClaimsHoldE (L : Lvm.M3.Lay) (out : OpenClaimsE) (p : Column L.nuMain × Column L.nuRec) : Prop :=
  (∀ c ∈ out.1, ClaimE.Holds L.nuRec c p.2) ∧ (∀ c ∈ out.2, ClaimE.Holds L.nuMain c p.1)

/-- **The typed phases' error side conditions at `E2`**: every group's escape (`L₀·errG g c`; A23's `κ` and `t`
without `L₀`, their escapes do not depend on the candidates), the mini-bus's groups with the follower's lead `T`. -/
structure TErrsE (L₀ : ℕ) (εmax T : ℝ≥0∞) : Prop where
  tau : (L₀ : ℝ≥0∞) * errG gTau 1 ≤ εmax
  zero : (L₀ : ℝ≥0∞) * errG gZero 3 ≤ εmax
  gamma : (L₀ : ℝ≥0∞) * errG gGamma 2 ≤ εmax
  wire : (L₀ : ℝ≥0∞) * errG gWire 2 ≤ εmax
  kappa : errG gKappa 1 ≤ εmax
  t : errG gT phiVarsE ≤ εmax
  ab : (L₀ : ℝ≥0∞) * errG gAB (4 * 2 ^ miniDepth) + T ≤ εmax
  lam : (L₀ : ℝ≥0∞) * errG gLam 2 + T ≤ εmax
  rd : (L₀ : ℝ≥0∞) * errG gRd 5 + T ≤ εmax
  y : (L₀ : ℝ≥0∞) * errG gY 2 + T ≤ εmax
  yl : (L₀ : ℝ≥0∞) * errG gYl 4 + T ≤ εmax

/-- `εI = 7·2^-131`, every group's cap (PARAM §1). -/
noncomputable def εI : ℝ≥0∞ := 7 * (2 : ℝ≥0∞)⁻¹ ^ 131

/-! ## The frozen statement -/

/-- **`typedSpecE`'s statement** (frozen; Y1-typed.md §2.1; BLUEPRINT §5 T4): from `G ∧ firstWord ∧ Doomed C (TGoodE
∧ R ∧ AccOkE)` to the doom of the returned `E2` claims with `R`, generic in the candidate sets `C` and the carried
`R`; lead `0` (the first event is a nonce); the errors `TErrsE`. -/
def TypedSpecEStmt : Prop :=
  ∀ (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → Lvm.FK) (acc : List E2 × E2) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
    (C : List Ev → Set (Column L.nuMain × Column L.nuRec)) (R : Column L.nuMain × Column L.nuRec → Prop)
    {L₀ : ℕ} {εmax T : ℝ≥0∞} (G : List Ev → Prop),
    Ti.Ok → Ti.MapsFit L → L.nuRec = relayRounds → acc.1.length = phiVarsE →
    AllSc Ti.mbT → LayOk L Ti.mbT → KeysOk Ti.mbT → FixOk Ti.mbT → mbLinB6 Ti.mbT = true →
    (inst L Ti.mbT hτL).μBus = miniDepth →
    (∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀) → (∀ h, (C h).Finite) → (∀ h, (C h).ncard ≤ L₀) →
    εmax < 1 → TErrsE L₀ εmax T →
    Nonempty (Spec (typedProgE Ti L pw acc)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ TGoodE Ti L hτL pw p ∧ R p ∧ AccOkE Ti acc) h)
      (fun out h ↦ Doomed C (fun p ↦ TClaimsHoldE L out p ∧ R p) h) εmax 0 T)

end Lvm6.Ty
