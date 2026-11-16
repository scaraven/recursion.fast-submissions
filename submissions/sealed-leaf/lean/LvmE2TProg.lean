-- New for lvm2 E2-FT (stage S2GT, E2F-T; transcript ref/s2gt.py with AMENDMENTS 1-2): the typed phases' programs
-- at `E2` (zerocheck with the swapped coordinate split, wiring, relayout, A23 at `Φ_Q` in 45 variables; the mini-bus
-- stays `E3`), their claims split into `K`-linear halves, the good relation and the error side conditions.
-- Frozen on day 0 (E2F-T).
import LvmE2TWiring
import LvmTypedSpecX
import LvmE2VMidSpec
import LvmE2VGkrSpec
import LvmCertSMid3

/-!
# The typed phases at `E2` (S2GT)

Every scalar of the zerocheck, the wiring, the relayout and A23 is an `E2` scalar (`e2Read`, 16 B); every `E2`
challenge has its own nonce and proof of work (`e2Sample g`, S2GT AMENDMENT 2), `g` the least with
`c·2^-g ≤ 7/8` for the challenge's numerator `c`:

* **Zerocheck** (`zeroProgT`): the separator; `τ ∈ E2^20` (`c = 1`, `g = 1` each); `ω` (`c = 2`, `g = 2`); 20
  equality-mode rounds (`c = 3`, `g = 2`); the nine values `A_j, B_j, C_j` (`j < 3`) at `r_x`; the final claim
  against `Σ_k ω^k·((A ⊗ B)_k + C_k)` (`zeroFinalT`: `E3 ⊗_K E2`'s product, `LvmE2TWiring.mulY3`).
* **Wiring** (`wireProgT`): `γ` (`c = 8`, `g = 4`); 21 rounds of degree 2 (`c = 2`, `g = 2`) from `Σ_{k<9} γ^k·v_k`;
  twelve matrix values `v_{m+4j}`, four region values; the final claim against `wGT γ vs · z̃(r_y)`.
* **Relayout** (`relayProgT`): 19 rounds of degree 2; `v_R`.
* **A23** (`accProgT`) at `Φ_Q` in `phiVarsT = 45` variables: `κ ∈ E2^4` (`c = 1`, `g = 1` each), `h` (46),
  `t` (`c = 45`, `g = 6`), the zero scalar.
* **The mini-bus** is roll 11's `miniBusProg` at `E3` (S2GT AMENDMENT 1).
* **The claims** (`typedClaimsT`): every `E2` claim on a committed column becomes two `K`-linear claims, re then
  im, in place (the tensor switch): the relayout's point claim (`splitE2`), the region claims of the committed
  block, `σ′` and the `KS` aliases (`regClaimT`); the mini-bus's claims stay `E3`.

The relation and errors used by `typedSpecT` (stated in `LvmE2TSpec`) are here: `TGoodT` (`WiringRelT ∧ M3Holds`),
`AccOkTT` (`Φ_Q` at `E2` on the header's `acc_in`), `TErrsT` (each `E2` challenge's escape `L₀·errG g c`, A23's
without `L₀`; the mini-bus's errors as roll 11's), and `errsT_at` (all of them at `L₀ = 1` against `εS`). The
zerocheck rounds are priced at numerator 3 as in the transcript; the proof needs 2 (the equality factor is peeled),
so `TErrsT.zero` is conservative.
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm.Loop Lvm.Typed Lvm.E2V LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open Lvm.M3 (Tab inst stackOf KeysOk AllSc LayOk FixOk lay26)
open Lvm.ASM (OpenClaims Pair GoodRel MidSpecP GkS BndS εS)
open Lvm.VEq (VStackClaim hdX pubX)
open LeanVM.Protocol.KeccakGkr (errE)
open Lvm.ASM (coe_overE coe_div_card errE_le_εS errE_add errE_smul εS_lt_one)
open scoped ENNReal NNReal

/-! ## Proof-of-work bits (S2GT, AMENDMENT 2) -/

/-- `τ_i`: numerator 1. -/
abbrev gTau : ℕ := 1
/-- `ω`: numerator 2 (degree 2 in `ω`). -/
abbrev gOmega : ℕ := 2
/-- Zerocheck rounds: numerator 3. -/
abbrev gZero : ℕ := 2
/-- `γ`: numerator 8 (nine values). -/
abbrev gGamma : ℕ := 4
/-- Wiring and relayout rounds: numerator 2. -/
abbrev gWire : ℕ := 2
/-- `κ_j`: numerator 1. -/
abbrev gKappa : ℕ := 1
/-- A23's `t`: numerator `phiVarsT = 45`. -/
abbrev gT : ℕ := 6

/-! ## Field helpers -/

/-- `K` in `E2`. -/
def kE2 (a : FK) : E2 := FE2.toE2 (FE2.ofK a)

/-- A header scalar at `E2`: lanes 0–1 of its `E3` decoding (16-B scalars, as `e2OfE`). -/
def e2OfFE (a : FE) : E2 := e2OfE (FE.toExt3 a)

/-- **`acc_in` at `E2`**: the header's point (45 coordinates) and value. -/
def accPtT (pub : Lvm.Pub) : List E2 := pub.accIn.pt.map e2OfFE

/-- The header's `acc_in` value at `E2`. -/
def accYT (pub : Lvm.Pub) : E2 := e2OfFE pub.accIn.y

/-- `Σ_{regions of a source in S} Σ_{y in the region} f(y)`. -/
def regSumW {α : Type} [Add α] [Zero α] (Ti : TInst) (S : YSrc → Bool) (f : ℕ → α) : α :=
  (Ti.lay.yregs.map fun reg ↦ if S reg.src then
    ((List.range (2 ^ reg.log)).map fun i ↦ f (reg.base + i)).sum else 0).sum

/-- `regSum` at `E2`: `Σ eq(r, y)·f(y)` over the regions of a source in `S`. -/
def regSumT (Ti : TInst) (S : YSrc → Bool) (f : ℕ → E2) (r : List E2) : E2 :=
  regSumW Ti S fun y ↦ E2V.eqAtF r y * f y

/-- **The natively computed part of `z̃(r_y)` at `E2`**: `PUB`, `QLT`, `1`. -/
def virtT (Ti : TInst) (pub : Lvm.Pub) (ry : List E2) : E2 :=
  regSumT Ti (fun s ↦ s == .pub) (fun y ↦ kE2 (Ti.pubV pub y)) ry +
    regSumT Ti (fun s ↦ s == .qlt) (fun y ↦ kE2 (Ti.qltV y)) ry +
    regSumT Ti (fun s ↦ s == .one) (fun _ ↦ 1) ry

/-! ## The phases -/

/-- **The zerocheck's final value**: `Σ_{k<3} ω^k·((A ⊗ B)_k + C_k)` on the nine values
`A₀, A₁, A₂, B₀, B₁, B₂, C₀, C₁, C₂`. -/
def zeroFinalT (ω : E2) (v : List E2) : E2 :=
  ((List.range 3).map fun k ↦
    ω ^ k * (mulY3 (fun j ↦ v.getD j 0) (fun j ↦ v.getD (3 + j) 0) k + v.getD (6 + k) 0)).sum

/-- **Zerocheck at `E2`, swapped split**: the separator, `τ`, `ω`, 20 equality-mode rounds from `0`, nine values,
the final claim. Returns `(r_x, values)`. -/
def zeroProgT : VerifierProgram (List E2 × List E2) :=
  e2Sep >>= fun _ ↦ e2Samples gTau xVars >>= fun τ ↦ e2Sample gOmega >>= fun ω ↦
    sumcheckE2 gZero 0 3 (τ.map some) >>= fun rf ↦ e2Reads 9 >>= fun v ↦
      VerifierProgram.require (rf.2 = zeroFinalT ω v) >>= fun _ ↦ pure (rf.1, v)

/-- The wiring's start: `Σ_{k<9} γ^k·v_k`. -/
def wBatchT (γ : E2) (v : List E2) : E2 := ((List.range 9).map fun k ↦ γ ^ k * v.getD k 0).sum

/-- The wiring's batch of the twelve matrix values (`v_{m+4j}`; `A_j` at `γ^j`, `B_j` at `γ^{3+j}`, `C_j` at
`γ^{6+j}`). -/
def wGT (γ : E2) (vs : List E2) : E2 :=
  ((List.range 3).map fun j ↦ γ ^ j * vs.getD (4 * j) 0 + γ ^ (3 + j) * vs.getD (1 + 4 * j) 0 +
    γ ^ (6 + j) * (vs.getD (2 + 4 * j) 0 + vs.getD (3 + 4 * j) 0)).sum

/-- **Wiring at `E2`**: `γ`; 21 rounds of degree 2; twelve matrix values, four region values; the final claim.
Returns `(r_y, matrix values, region values)`. -/
def wireProgT (Ti : TInst) (pub : Lvm.Pub) (v : List E2) : VerifierProgram (List E2 × List E2 × List E2) :=
  e2Sample gGamma >>= fun γ ↦ sumcheckE2 gWire (wBatchT γ v) 3 (List.replicate yVars none) >>= fun rf ↦
    e2Reads 12 >>= fun vs ↦ e2Reads 4 >>= fun rv ↦
      VerifierProgram.require (rf.2 = wGT γ vs * (sumF rv + virtT Ti pub rf.1)) >>= fun _ ↦
        pure (rf.1, vs, rv)

/-- The relayout's kernel at `E2`. -/
def relayKernT (Ti : TInst) (ry r : List E2) : E2 := regSumT Ti (fun s ↦ s == .sflat) (fun y ↦ E2V.eqAtF r (Ti.sflatW y)) ry

/-- **The `S_flat` relayout at `E2`**: 19 rounds of degree 2; `v_R`. Returns `(r, v_R)`. -/
def relayProgT (Ti : TInst) (ry : List E2) (vS : E2) : VerifierProgram (List E2 × E2) :=
  sumcheckE2 gWire vS 3 (List.replicate relayRounds none) >>= fun rf ↦ e2Read >>= fun vR ↦
    VerifierProgram.require (rf.2 = relayKernT Ti ry rf.1 * vR) >>= fun _ ↦ pure (rf.1, vR)

/-- A23's line from `a` to `b` at `E2`. -/
def lineT (a b : List E2) (t : E2) : List E2 := List.zipWith (fun x y ↦ x + t * (x + y)) a b

/-- The line polynomial's value. -/
def hEvalT (hs : List E2) (t : E2) : E2 := hs.foldr (fun c acc ↦ c + t * acc) 0

/-- `y_own(κ) = Σ_{o'} eq(κ, o')·v_{o'}`. -/
def yOwnT (vs κ : List E2) : E2 := dotF (eqKernelF κ) vs

/-- **A23 at `Φ_Q` in 45 variables, at `E2`**: `κ` (4), `h` (46), `t`, the zero scalar; the checks. -/
def accProgT (Q : Program) (lay : Lay) (ok : Bool) (yIn : E2) (a rxy vs : List E2) : VerifierProgram Unit :=
  e2Samples gKappa selBitsT >>= fun κ ↦ e2Reads (phiVarsT + 1) >>= fun hs ↦ e2Sample gT >>= fun t ↦
    e2Read >>= fun z ↦
      VerifierProgram.require (ok = true ∧ hEvalT hs 0 = yIn ∧ hEvalT hs 1 = yOwnT vs κ ∧ z = 0 ∧
        PhiQT Q lay (lineT a (κ ++ rxy) t) = hEvalT hs t)

/-! ## The claims -/

/-- Coordinate `h` of an `E2` value as an `E3` value (`false`: re, `true`: im). -/
def coordE (h : Bool) (v : E2) : E := ofK (if h then v.im else v.re)

/-- **A region claim at `E2`, split** (the tensor switch for a word claim): `Σ_y eq(r, y)·q[w(y)] = v` over the
regions of source `s` becomes the two `K`-linear claims `Σ_y eq(r, y)_h·q[w(y)] = v_h`, re then im. -/
def regClaimT (Ti : TInst) (s : YSrc) (w : ℕ → ℕ) (r : List E2) (v : E2) : List VStackClaim :=
  [false, true].map fun h ↦
    (fun X ↦ regSumW Ti (fun s' ↦ s' == s) (fun y ↦ coordE h (E2V.eqAtF r y) * KeccakGkr.eqAt X (w y)), coordE h v)

/-- **The typed claims at S2GT**: on `C_rec` the relayout's point claim (split), `σ′`'s (split) and the
mini-bus's (`E3`); on `C_main` the committed block's and the `KS` aliases' (split) and the mini-bus's (`E3`). -/
def typedClaimsT (Ti : TInst) (ry rv rr : List E2) (vR : E2)
    (cl : List LeanVM.Protocol.Verifier.ColumnClaim) : OpenClaims :=
  ((splitE2 relayRounds (pointE2 ⟨relayRounds, 0⟩ rr vR)).map (·.onStack) ++
      regClaimT Ti .sigma Ti.sigmaW ry (rv.getD 2 0) ++ miniClaims Ti .crec cl,
    regClaimT Ti .com Ti.comW ry (rv.getD 0 0) ++ regClaimT Ti .ks Ti.ksW ry (rv.getD 3 0) ++
      miniClaims Ti .main cl)

/-- **The typed phases at S2GT**: zerocheck, wiring, relayout, A23 at `E2`; the mini-bus at `E3`; the claims. -/
@[irreducible] def typedProgT (Ti : TInst) (pub : Lvm.Pub) : VerifierProgram OpenClaims :=
  zeroProgT >>= fun z ↦ wireProgT Ti pub z.2 >>= fun w ↦ relayProgT Ti w.1 (w.2.2.getD 1 0) >>= fun r ↦
    accProgT Ti.Q Ti.lay true (accYT pub) (accPtT pub) (z.1 ++ w.1) w.2.1 >>= fun _ ↦
      miniBusProg Ti >>= fun cl ↦ pure (typedClaimsT Ti w.1 w.2.2 r.1 r.2 cl)

/-! ## The split claims mean the `E2` claims -/

/-- **The tensor switch for a region claim**: both split claims hold on a column iff the `E2` claim holds (the
words are in `K`). -/
theorem regClaimT_holds_iff (Ti : TInst) (nu : ℕ) (s : YSrc) (w : ℕ → ℕ) (r : List E2) (v : E2) (q : Column nu)
    (hw : ∀ reg ∈ Ti.lay.yregs, reg.src = s → ∀ i < 2 ^ reg.log, w (reg.base + i) < 2 ^ nu) :
    (∀ c ∈ regClaimT Ti s w r v, StackClaim.Holds nu c q) ↔
      regSumT Ti (fun s' ↦ s' == s) (fun y ↦ (algebraMap K E2) (q.values.getD (w y) 0)) r = v := by
  have cAdd : ∀ (h : Bool) (a b : E2), coordE h (a + b) = coordE h a + coordE h b := by
    intro h a b; cases h <;> exact map_add (algebraMap K E) _ _
  have cZero : ∀ h : Bool, coordE h 0 = 0 := by intro h; cases h <;> exact map_zero (algebraMap K E)
  have cSum : ∀ (h : Bool) {α : Type} (l : List α) (f : α → E2),
      coordE h (l.map f).sum = (l.map fun a ↦ coordE h (f a)).sum := by
    intro h α l f
    induction l with
    | nil => exact cZero h
    | cons a l ih => simp only [List.map_cons, List.sum_cons, cAdd, ih]
  have cMul : ∀ (h : Bool) (a : E2) (k : K), coordE h (a * algebraMap K E2 k) = coordE h a * ofK k := by
    intro h a k
    rw [← Quad.C_eq_algebraMap]
    cases h <;> simp only [coordE, Bool.false_eq_true, ite_false, ite_true, Quad.re_mul_C, Quad.im_mul_C] <;>
      exact map_mul (algebraMap K E) _ _
  have hc : ∀ h : Bool, StackClaim.Holds nu (fun X ↦ regSumW Ti (fun s' ↦ s' == s)
        (fun y ↦ coordE h (E2V.eqAtF r y) * KeccakGkr.eqAt X (w y)), coordE h v) q ↔
      coordE h (regSumT Ti (fun s' ↦ s' == s) (fun y ↦ (algebraMap K E2) (q.values.getD (w y) 0)) r) =
        coordE h v := by
    intro h
    unfold StackClaim.Holds
    refine Eq.congr_left ?_
    simp only [regSumT, regSumW, ← List.sum_map_mul_right, cSum]
    rw [sum_list_swap]
    refine congrArg List.sum (List.map_congr_left fun reg hreg ↦ ?_)
    split_ifs with hS
    · simp only [← List.sum_map_mul_right, cSum]
      rw [sum_list_swap]
      refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
      rw [cMul, ← sum_fin_eqAt nu (w (reg.base + i)) (hw reg hreg (by simpa using hS) i (List.mem_range.mp hi))
        (fun x ↦ ofK (q.values.getD x 0)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ ↦ by ring
    · simp [cZero]
  have hinj : ∀ (h : Bool) (a b : E2), coordE h a = coordE h b ↔ (if h then a.im else a.re) = (if h then b.im else b.re) :=
    fun h a b ↦ (algebraMap K E).injective.eq_iff
  simp only [regClaimT, List.forall_mem_map, List.forall_mem_cons, hc, hinj]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  constructor
  · rintro ⟨h0, h1, -⟩
    exact QuadraticAlgebra.ext h0 h1
  · rintro rfl
    exact ⟨rfl, rfl, fun x hx ↦ absurd hx List.not_mem_nil⟩

/-! ## The specification -/

/-- **The typed half of a good pair at S2GT**: the relation at `E2` on the candidate, and the mini-bus balances. -/
def TGoodT (Ti : TInst) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pub : Lvm.Pub)
    (p : Column L.nuMain × Column L.nuRec) : Prop :=
  WiringRelT Ti.Q Ti.lay (Ti.zOf L pub p.1 p.2) ∧ M3Holds (inst L Ti.mbT hτ) () (stackOf L p.1 p.2)

/-- **The incoming accumulator holds at `Φ_Q` at `E2`** (45 variables). -/
def AccOkTT (Ti : TInst) (pub : Lvm.Pub) : Prop := PhiQT Ti.Q Ti.lay (accPtT pub) = accYT pub

/-- The mini-bus's lead and follower (`E3`, roll 11's): `(α, β)`'s and the follower's `T`. -/
noncomputable abbrev leadMiniT (L₀ : ℕ) (I : M3Instance) (T : ℝ≥0∞) : ℝ≥0∞ := max (abError I L₀ + 0) T

/-- **The typed phases' error side conditions at S2GT**: every `E2` challenge's escape `L₀·errG g c` (its follower
is a read: lead `0`; A23's `κ` and `t` without `L₀`: their escapes do not depend on the candidates, as roll 11's
`TErrs.acc`), and the `E3` mini-bus's (`TErrs`'s fields with `leadMiniT`). -/
structure TErrsT (L₀ : ℕ) (I : M3Instance) (εmax T : ℝ≥0∞) : Prop where
  tau : (L₀ : ℝ≥0∞) * errG gTau 1 ≤ εmax
  omega : (L₀ : ℝ≥0∞) * errG gOmega 2 ≤ εmax
  zero : (L₀ : ℝ≥0∞) * errG gZero 3 ≤ εmax
  gamma : (L₀ : ℝ≥0∞) * errG gGamma 8 ≤ εmax
  wire : (L₀ : ℝ≥0∞) * errG gWire 2 ≤ εmax
  kappa : errG gKappa 1 ≤ εmax
  t : errG gT phiVarsT ≤ εmax
  rounds : ∀ d ≤ 4, roundError L₀ d + leadMiniT L₀ I T ≤ εmax
  ab : abError I L₀ < 1 ∧ abError I L₀ + leadMiniT L₀ I T ≤ εmax
  lam : interpLead L₀ 2 (lambdaError L₀) + leadMiniT L₀ I T ≤ εmax ∧ lambdaError L₀ + leadMiniT L₀ I T ≤ εmax
  xi : xiError I L₀ + leadMiniT L₀ I T ≤ εmax
  follow : leadMiniT L₀ I T ≤ εmax

/-! ## The error side conditions at `L₀ = 1` -/


/-- **S2GT's typed errors at `L₀ = 1`** (after the pin): every `E2` challenge `≤ 6·2^-131 < εS` (`t`: `45/64`,
zerocheck rounds `3/4`), the `E3` mini-bus's far below; follower lead `0`. -/
theorem errsT_at (I : M3Instance) (hμ : I.μBus = miniDepth) (hB : I.B = 0) : TErrsT 1 I εS 0 := by
  have hg : ∀ {c g : ℕ}, grpEps 1 c g ≤ epsS → ((1 : ℕ) : ℝ≥0∞) * errG g c ≤ εS := fun h ↦
    (le_of_eq (add_zero _).symm).trans (errG_le_εS h)
  have hab : abError I 1 = errE (1 * (4 * 2 ^ 12)) := by rw [abError, coe_overE, errE_smul, hμ]
  have hr : ∀ d, roundError 1 d = errE (1 * d) := fun d ↦ by rw [roundError, coe_div_card, errE_smul]
  have hl : lambdaError 1 = errE (1 * 2) := by rw [lambdaError, coe_div_card, errE_smul]
  have hu : unitError 1 = errE (1 * 1) := by rw [← errE_smul]; simp [unitError, errE]
  have hx : xiError I 1 = errE (1 * (I.B + 3 - 1)) := by rw [xiError, coe_div_card, errE_smul]
  have hM : leadMiniT 1 I 0 = errE (1 * (4 * 2 ^ 12)) := by
    rw [leadMiniT, hab, add_zero]; exact max_eq_left zero_le
  have fin : ∀ a : ℕ, a ≤ 2 ^ 62 → errE a + leadMiniT 1 I 0 ≤ εS := fun a ha ↦ by
    rw [hM, errE_add]; exact errE_le_εS (Nat.le_trans (Nat.add_le_add_right ha _) (by norm_num))
  refine ⟨hg (by unfold grpEps epsS; norm_num), hg (by unfold grpEps epsS; norm_num),
    hg (by unfold grpEps epsS; norm_num), hg (by unfold grpEps epsS; norm_num),
    hg (by unfold grpEps epsS; norm_num), by simpa using hg (c := 1) (g := gKappa) (by unfold grpEps epsS; norm_num),
    by simpa using hg (c := phiVarsT) (g := gT) (by unfold grpEps epsS phiVarsT selBitsT xVars yVars; norm_num),
    fun d hd ↦ ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hr]; exact fin _ (by omega)
  · rw [hab]; exact lt_of_le_of_lt (errE_le_εS (by norm_num)) εS_lt_one
  · rw [hab]; exact fin _ (by norm_num)
  · rw [interpLead_eq, hu, hl, errE_smul, errE_add]; exact fin _ (by norm_num)
  · rw [hl]; exact fin _ (by norm_num)
  · rw [hx, hB]; exact fin _ (by norm_num)
  · rw [hM]; exact errE_le_εS (by norm_num)


end Lvm.E2T
