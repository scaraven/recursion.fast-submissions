-- New for lvm2 (roll 8 = B1, B1-S0 skeleton; B-DES §1.2, §2): the typed backend's phases on the wire (zerocheck,
-- wiring, the `S_flat` relayout, A23 at `Φ_Q`, the mini-bus) and `typedSpecR`, in `midBusTableAccSpecB`'s shape
-- (`LvmAccSpecMid`); the new bus half `GbT`, `Good₂` of `GoodT`, `midSpecOfRel` and `kcertSJ` applied unchanged
-- (`LvmShape`, `LvmCertSMid3`, `LvmCertSKJ`). Not wired into `certified` (wave X/INT).
import LvmTyped
import LvmTypedAcc
import LvmTypedSpecP
import LvmShape
import LvmCertSKJ

-- (GOLF2: 22 declarations that `certified` does not use moved verbatim to `LvmMPMidTOff`, outside its import closure.)

/-!
# The typed backend's phases and their specification

* **`TInst`**: the program `Q`, its layout, the mini-bus's tables (`capTpl`'s reads, `2^13` leaves) and where the
  word space's regions live (`C_main` words of the committed and `KS` regions, `C_rec` words of `S_flat` and `σ′`,
  `PUB` from the statement, `QLT`); **`zOf`**: a candidate pair's words; **`TGood`**: the wiring relation on them
  and the mini-bus's `M3Holds`; **`AccOkT`**: the incoming accumulator at `Φ_Q`.
* **The phases** (B-DES §1.2; stub programs, B1-V owns their final form, V_S refines them): `zeroProg` (`τ`, 20
  rounds of degree 3, equality mode), `wireProg` (`γ`, 21 rounds of degree 2, `v_o`, the region values),
  `relayProg` (19 rounds of degree 2), `accProgQ`, `miniBusProg` (the bus at depth 13 and the fixed-column check);
  **`typedProg`** returns the claims on `C_rec` and `C_main`.
* **`typedSpecR`** (L-B): from `G ∧ firstWord ∧ Doomed C (TGood ∧ R ∧ AccOkT)` to `Doomed C (claims hold ∧ R)`,
  generic in the candidate set `C` and the carried `R` (`midBusTableAccSpecB`'s shape); the region maps land in the
  commitments (`MapsFit`), `C_rec` has `relayRounds` variables, `acc_in` has 43 coordinates, the mini-bus's
  `FixOk`.
* At P20 (`lay26`, `candPairs`): **`GbT`** (`TGood ∧ BndS`, `AccOkT`), **`GoodT = GbT ∧ GkS`** (the shape of
  `GoodA`), `Good₂ (GoodT Ti)`, `nodeSoundT₂`; **`midT₂`**, `specBusT₂` (`typedSpecR` at `imgC x`, as `specBusA₂`),
  **`midSpecR_T₂`** (`midSpecOfRel`, with `LvmShape.specKgS₂` unchanged), **`midShape_T₂`**, **`kcertT`**
  (`kcertSJ` unchanged).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal

/-! ## The typed instance -/

/-- **A typed instance**: the program, its layout, the mini-bus's tables, and where the word space's regions
live (B1-V and INT fill it at P20; every map takes the absolute word `y`). -/
structure TInst where
  /-- The program (B's node program). -/
  Q : Program
  /-- Its typed layout. -/
  lay : Lay
  /-- The mini-bus's tables (`capTpl`'s reads against the cap regions, B-DES §1.5). -/
  mbT : List Tab
  /-- The `C_main` word of a committed word. -/
  comW : ℕ → ℕ
  /-- The `C_main` word of a `KS` alias word (`C_main`'s `KS` block). -/
  ksW : ℕ → ℕ
  /-- The `C_rec` word of an `S_flat` word (position `p` of the child's trace: lane `p mod 17`, row `p div 17`). -/
  sflatW : ℕ → ℕ
  /-- The `C_rec` word of a `σ′` word (`C_rec`'s column 17). -/
  sigmaW : ℕ → ℕ
  /-- The `PUB` words of a statement's public values. -/
  pubV : Lvm.Pub → ℕ → FK
  /-- The `QLT` words (public). -/
  qltV : ℕ → FK

namespace TInst

variable (Ti : TInst)

/-- The source of word `y` (`none` outside every region). -/
def src? (y : ℕ) : Option YSrc :=
  (Ti.lay.yregs.find? fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)).map (·.src)

/-- **A candidate pair's words** (statement `pub`): committed and `KS` words from `C_main`, `S_flat` and `σ′`
from `C_rec`, `PUB` from the statement, `QLT`, the constant `1`. -/
def zOf (L : Lvm.M3.Lay) (pub : Lvm.Pub) (qm : Column L.nuMain) (qr : Column L.nuRec) (y : ℕ) : FK :=
  match Ti.src? y with
  | some .com => Lvm.FK.ofBF64 (comCell L qm qr false (Ti.comW y))
  | some .ks => Lvm.FK.ofBF64 (comCell L qm qr false (Ti.ksW y))
  | some .sflat => Lvm.FK.ofBF64 (comCell L qm qr true (Ti.sflatW y))
  | some .sigma => Lvm.FK.ofBF64 (comCell L qm qr true (Ti.sigmaW y))
  | some .pub => Ti.pubV pub y
  | some .qlt => Ti.qltV y
  | some .one => 1
  | none => 0

/-- **The instance check**: the layout is one of `Q`, and its word `1` lies in a `one` region. -/
def Ok : Prop := Ti.lay.Ok Ti.Q ∧ Ti.src? Ti.lay.one = some .one

/-- **The region maps land in the commitments** (`2^nuMain` words of `C_main`, `2^nuRec` of `C_rec`): a claim's
weight reads its word modulo the cube, `zOf` reads it exactly. -/
def MapsFit (L : Lvm.M3.Lay) : Prop :=
  ∀ y, match Ti.src? y with
    | some .com => Ti.comW y < 2 ^ L.nuMain
    | some .ks => Ti.ksW y < 2 ^ L.nuMain
    | some .sflat => Ti.sflatW y < 2 ^ L.nuRec
    | some .sigma => Ti.sigmaW y < 2 ^ L.nuRec
    | _ => True

end TInst

/-- **The typed half of a good pair** (B-DES §2: "the wiring relation holds on the candidate, and the mini-bus
balances"). -/
def TGood (Ti : TInst) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pub : Lvm.Pub)
    (p : Column L.nuMain × Column L.nuRec) : Prop :=
  WiringRel Ti.Q Ti.lay (Ti.zOf L pub p.1 p.2) ∧ M3Holds (inst L Ti.mbT hτ) () (stackOf L p.1 p.2)

/-- **The incoming accumulator holds at `Φ_Q`** (`AccOk acc_in`, B-DES §1.2 step 3). -/
def AccOkT (Ti : TInst) (pub : Lvm.Pub) : Prop :=
  PhiQ Ti.Q Ti.lay (pub.accIn.pt.map FE.toExt3) = FE.toExt3 pub.accIn.y

/-! ## The phases on the wire (stub programs; B1-V) -/

/-- The mini-bus's depth: `2^12` leaves (lvm2 roll 11, M′ `S2GM`: `C_rec`'s cap reads left `capTpl`; B1: `2^13`,
B-DES §1.5). -/
abbrev miniDepth : ℕ := 12

/-- The relayout's rounds: `C_rec`'s 19 variables (B-DES §1.2 says 18, but `S_flat` has `17·2^14 > 2^18` words; the
stride-17 map lands on `C_rec`'s lane and row bits, 5 + 14). -/
abbrev relayRounds : ℕ := 19

/-- `Σ_{regions of a source in S} Σ_{y in the region} eq(r, y)·f(y)`: a region family's part of `z̃(r)`, region by
region (V computes the virtual ones natively; B1-V's closed forms). Equal to the sum over the words of those
sources when the regions are disjoint (`yregsSorted`). -/
def regSum (Ti : TInst) (S : YSrc → Bool) (f : ℕ → E) (r : List E) : E :=
  (Ti.lay.yregs.map fun reg ↦ if S reg.src then
    ((List.range (2 ^ reg.log)).map fun i ↦ eqAt r (reg.base + i) * f (reg.base + i)).sum else 0).sum

/-- The natively computed part of `z̃(r_y)`: `PUB`, `QLT`, `1`. -/
def virtE (Ti : TInst) (pub : Lvm.Pub) (ry : List E) : E :=
  regSum Ti (fun s ↦ s == .pub) (fun y ↦ FE.toExt3 (FE.ofK (Ti.pubV pub y))) ry +
    regSum Ti (fun s ↦ s == .qlt) (fun y ↦ FE.toExt3 (FE.ofK (Ti.qltV y))) ry +
    regSum Ti (fun s ↦ s == .one) (fun _ ↦ 1) ry

/-- A claim on a commitment: `Σ_{y, src y = s} eq(r, y)·q[w(y)] = v` (the weight on the commitment's cube). -/
def regClaim (Ti : TInst) (s : YSrc) (w : ℕ → ℕ) (r : List E) (v : E) : VStackClaim :=
  (fun X ↦ regSum Ti (fun s' ↦ s' == s) (fun y ↦ eqAt X (w y)) r, v)

/-- **Zerocheck** (step 1): `τ ∈ E^20`; 20 rounds of degree 3 from `0`, in equality mode (as `gkrStep`: the sent
polynomial has degree 2, the factor `eq(τ_i, ·)` is peeled, so the final claim is checked without `eq(τ, r_x)`);
`a*, b*, c*`; the final claim against `a*·b* + c*`. Returns `(r_x, (a*, b*, c*))`. -/
def zeroProg : VerifierProgram (List E × E × E × E) :=
  (VerifierProgram.sampleChallenges xVars).bind fun τ ↦
    (LeanVM.Protocol.Verifier.sumcheck 0 3 (τ.map some)).bind fun rf ↦
      (VerifierProgram.readScalars 3).bind fun abc ↦
        (VerifierProgram.require (rf.2 = abc.getD 0 0 * abc.getD 1 0 + abc.getD 2 0)).bind fun _ ↦
          VerifierProgram.ret (rf.1, abc.getD 0 0, abc.getD 1 0, abc.getD 2 0)

/-- **Wiring** (step 2): `γ`; 21 rounds of degree 2 from `a* + γ b* + γ² c*`; the four matrix values `v_o` and the
region values `v_C, v_S, v_σ, v_K` (committed, `S_flat`, `σ′`, `KS`); the final claim against
`(v_A + γ v_B + γ² (v_D + v_W))·z̃(r_y)`, `z̃(r_y) = v_C + v_S + v_σ + v_K + virtE`. Returns `(r_y, v, regions)`. -/
def wireProg (Ti : TInst) (pub : Lvm.Pub) (abc : E × E × E) : VerifierProgram (List E × List E × List E) :=
  VerifierProgram.sampleChallenge.bind fun γ ↦
    (LeanVM.Protocol.Verifier.sumcheck (abc.1 + γ * abc.2.1 + γ * γ * abc.2.2) 3
        (List.replicate yVars none)).bind fun rf ↦
      (VerifierProgram.readScalars 4).bind fun vs ↦ (VerifierProgram.readScalars 4).bind fun rv ↦
        (VerifierProgram.require (rf.2 = (vs.getD 0 0 + γ * vs.getD 1 0 + γ * γ * (vs.getD 2 0 + vs.getD 3 0)) *
          (rv.sum + virtE Ti pub rf.1))).bind fun _ ↦ VerifierProgram.ret (rf.1, vs, rv)

/-- The relayout's kernel at `(r_y, r)`: `Σ_{y ∈ S_flat} eq(r_y, y)·eq(r, sflatW y)` (B-DES §1.2: the stride-17
map, evaluated directly). -/
def relayKern (Ti : TInst) (ry r : List E) : E := regSum Ti (fun s ↦ s == .sflat) (fun y ↦ eqAt r (Ti.sflatW y)) ry

/-- **The `S_flat` relayout** (step 2): `v_S` reduced to one claim on `C_rec` by `relayRounds` rounds of degree 2;
the final claim against `kern(r_y, r)·v_R`. Returns `(r, v_R)`. -/
def relayProg (Ti : TInst) (ry : List E) (vS : E) : VerifierProgram (List E × E) :=
  (LeanVM.Protocol.Verifier.sumcheck vS 3 (List.replicate relayRounds none)).bind fun rf ↦
    VerifierProgram.readScalar.bind fun vR ↦
      (VerifierProgram.require (rf.2 = relayKern Ti ry rf.1 * vR)).bind fun _ ↦ VerifierProgram.ret (rf.1, vR)

/-- **The mini-bus** (step 4, B-DES §1.5): today's bus and table phase on the mini-bus's tables at depth 13, then
the native fixed-column check (WP-9b's `lbusTableCheckProg`, the pre-A23 path: its fixed columns are not in `Φ_Q`). -/
def miniBusProg (Ti : TInst) : VerifierProgram (List LeanVM.Protocol.Verifier.ColumnClaim) :=
  lbusTableCheckProg Ti.mbT miniDepth

/-- The mini-bus's claims on one commitment. -/
def miniClaims (Ti : TInst) (com : Lvm.Com) (cl : List LeanVM.Protocol.Verifier.ColumnClaim) :
    List VStackClaim :=
  ((tableClaimsE Ti.mbT cl).filter (·.1 == com)).map (·.2.onStack)

/-- **The claims of the typed phases**: on `C_rec` the relayout's point claim, `σ′`'s and the mini-bus's; on
`C_main` the committed block's, the `KS` aliases' and the mini-bus's. The relayout's point claim is the block
claim on `C_rec`'s whole `⟨relayRounds, 0⟩` (as V_S's `BlockClaim.point`; L-C, wave L: the bare `eqEval rr` differs
from it off `C_rec`'s `19`-coordinate cube, so it would not refine; on the cube, where `Holds` reads it, they
agree). -/
def typedClaims (Ti : TInst) (ry rv : List E) (rr : List E) (vR : E)
    (cl : List LeanVM.Protocol.Verifier.ColumnClaim) : OpenClaims :=
  ((BClaim.point ⟨relayRounds, 0⟩ rr vR).onStack ::
      regClaim Ti .sigma Ti.sigmaW ry (rv.getD 2 0) :: miniClaims Ti .crec cl,
    regClaim Ti .com Ti.comW ry (rv.getD 0 0) :: regClaim Ti .ks Ti.ksW ry (rv.getD 3 0) :: miniClaims Ti .main cl)

/-- **The typed backend's phases** (B-DES §1.2, after the commitment; they replace the bus, the table sumcheck
and A23's `fixCols`): zerocheck, wiring, relayout, A23 at `Φ_Q`, the mini-bus; the claims. Irreducible (an
attribute, as `LvmXChainL.msgL`): elaboration would otherwise unfold the program in every `NoCommit` check. -/
@[irreducible] def typedProg (Ti : TInst) (pub : Lvm.Pub) : VerifierProgram OpenClaims :=
  zeroProg.bind fun z ↦ (wireProg Ti pub z.2).bind fun w ↦ (relayProg Ti w.1 (w.2.2.getD 1 0)).bind fun r ↦
    (accProgQ Ti.Q Ti.lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (z.1 ++ w.1) w.2.1).bind
      fun _ ↦ (miniBusProg Ti).bind fun cl ↦ VerifierProgram.ret (typedClaims Ti w.1 w.2.2 r.1 r.2 cl)

/-! ## The specification -/

/-- The returned claims hold on a pair. -/
def TClaimsHold (L : Lvm.M3.Lay) (out : OpenClaims) (p : Column L.nuMain × Column L.nuRec) : Prop :=
  (∀ c ∈ out.1, LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuRec c p.2) ∧
    (∀ c ∈ out.2, LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuMain c p.1)

/-- The typed phases' lead: `τ`'s `20` samples as one group over `L₀` candidates. -/
noncomputable abbrev leadT (L₀ : ℕ) : ℝ≥0∞ := ((xVars : ℕ) : ℝ≥0∞) * ((L₀ : ℝ≥0∞) * errE 1) + 0

/-- The largest lead any of the typed phases hands its follower: `τ`'s, the mini-bus's `(α, β)`, A23's `κ`, and
the follower's `T`. -/
noncomputable abbrev leadMaxT (L₀ : ℕ) (I : M3Instance) (T : ℝ≥0∞) : ℝ≥0∞ :=
  max (leadT L₀) (max (abError I L₀ + 0) (max (2 * errE 1) T))

/-- **The typed phases' error side conditions** (B-DES §1.7, stated generously: every group's escape plus the
largest lead within `εmax`; at P20 every term is `≤ 2^-160` against `εS = 2^-128.2`): `τ` (the lead), the rounds
(degree 1–4: zerocheck 3, wiring and relayout 2, the mini-bus's GKR), `γ` (degree 2), A23 (`κ`, `t` at
`phiVars`), the mini-bus's `(α, β)`, `λ`, `ξ`; the follower `T`. -/
structure TErrs (L₀ : ℕ) (I : M3Instance) (εmax T : ℝ≥0∞) : Prop where
  lead : leadT L₀ ≤ εmax
  rounds : ∀ d ≤ 4, roundError L₀ d + leadMaxT L₀ I T ≤ εmax
  acc : errE phiVars + leadMaxT L₀ I T ≤ εmax
  ab : abError I L₀ < 1 ∧ abError I L₀ + leadMaxT L₀ I T ≤ εmax
  lam : interpLead L₀ 2 (lambdaError L₀) + leadMaxT L₀ I T ≤ εmax ∧ lambdaError L₀ + leadMaxT L₀ I T ≤ εmax
  xi : xiError I L₀ + leadMaxT L₀ I T ≤ εmax
  follow : leadMaxT L₀ I T ≤ εmax

/-! ## The proof of `typedSpecR`: the instance's facts -/

section Facts

variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub)

theorem regSum_eq (S : YSrc → Bool) (f : ℕ → E) (r : List E) : regSum Ti S f r = regSumL Ti.lay.yregs S f r :=
  rfl

theorem src?_eq (y : ℕ) : Ti.src? y = ysrcL Ti.lay.yregs y := rfl

/-- **The regions of a checked instance are sorted, disjoint and inside the word space.** -/
theorem yregs_pairwise (hTi : Ti.Ok) :
    Ti.lay.yregs.Pairwise (fun r r' ↦ r.base + 2 ^ r.log ≤ r'.base) ∧
      ∀ r ∈ Ti.lay.yregs, r.base + 2 ^ r.log ≤ 2 ^ yVars := by
  have h := hTi.1
  unfold Lay.Ok Lay.okB at h
  simp only [Bool.and_eq_true] at h
  exact yregsSorted_pairwise _ h.1.1.1.1.2

/-- A region's words have its source. -/
theorem src?_mem (hTi : Ti.Ok) {reg : YReg} (hreg : reg ∈ Ti.lay.yregs) {i : ℕ} (hi : i < 2 ^ reg.log) :
    Ti.src? (reg.base + i) = some reg.src :=
  ysrcL_of_mem (yregs_pairwise Ti hTi).1 hreg hi

/-- **`z̃(r_y)` is the regions' sums** (the committed, `S_flat`, `σ′`, `KS` parts and the native `virtE`). -/
theorem mleZ_zOf (hTi : Ti.Ok) (qm : Column L.nuMain) (qr : Column L.nuRec) (ry : List E) :
    mleZ yVars (zwE (Ti.zOf L pub qm qr)) ry =
      regSum Ti (· == .com) (zwE (Ti.zOf L pub qm qr)) ry + regSum Ti (· == .sflat) (zwE (Ti.zOf L pub qm qr)) ry +
        regSum Ti (· == .sigma) (zwE (Ti.zOf L pub qm qr)) ry + regSum Ti (· == .ks) (zwE (Ti.zOf L pub qm qr)) ry +
          virtE Ti pub ry := by
  obtain ⟨hP, hfit⟩ := yregs_pairwise Ti hTi
  unfold mleZ
  rw [sum_regions (2 ^ yVars) _ hP hfit (fun y ↦ eqAt ry y * zwE (Ti.zOf L pub qm qr) y) (fun y hy ↦ by
    simp only [zwE, TInst.zOf, src?_eq, ysrcL_none hy, FE.toExt3_ofK]
    simp)]
  rw [← regSumL_sources]
  have hc : ∀ (s : YSrc) (f : ℕ → E), (∀ y, Ti.src? y = some s → f y = zwE (Ti.zOf L pub qm qr) y) →
      regSum Ti (· == s) f ry = regSumL Ti.lay.yregs (· == s) (zwE (Ti.zOf L pub qm qr)) ry := fun s f hf ↦
    regSumL_congr Ti.lay.yregs (· == s) ry fun reg hreg hS i hi ↦ hf _ (by
      rw [src?_mem Ti hTi hreg hi]; simpa using hS)
  have hv : virtE Ti pub ry = regSumL Ti.lay.yregs (· == .pub) (zwE (Ti.zOf L pub qm qr)) ry +
      regSumL Ti.lay.yregs (· == .qlt) (zwE (Ti.zOf L pub qm qr)) ry +
        regSumL Ti.lay.yregs (· == .one) (zwE (Ti.zOf L pub qm qr)) ry := by
    unfold virtE
    rw [hc .pub _ fun y hy ↦ by simp only [zwE, TInst.zOf, hy],
      hc .qlt _ fun y hy ↦ by simp only [zwE, TInst.zOf, hy],
      hc .one _ fun y hy ↦ by simp only [zwE, TInst.zOf, hy]; exact (FE.toExt3_one).symm]
  rw [hv]
  rfl

/-- **A region claim holds iff its value is the region's true value**, when the candidate's words on the
source's regions are the commitment's words through the map, inside the commitment. -/
theorem holds_regTrue (hTi : Ti.Ok) {μ : ℕ} (s : YSrc) (w : ℕ → ℕ) (q : Column μ) (z : ℕ → FK) (ry : List E)
    (v : E) (hz : ∀ y, Ti.src? y = some s → w y < 2 ^ μ ∧ zwE z y = ofK (q.values.getD (w y) 0)) :
    LeanVM.Protocol.EndToEnd.StackClaim.Holds μ (regClaim Ti s w ry v) q ↔ regSum Ti (· == s) (zwE z) ry = v := by
  have hm : ∀ reg ∈ Ti.lay.yregs, (reg.src == s) = true → ∀ i < 2 ^ reg.log,
      Ti.src? (reg.base + i) = some s := fun reg hreg hS i hi ↦ by
    rw [src?_mem Ti hTi hreg hi]; simpa using hS
  unfold regClaim
  rw [show (fun X ↦ regSum Ti (fun s' ↦ s' == s) (fun y ↦ eqAt X (w y)) ry) =
      fun X ↦ regSumL Ti.lay.yregs (· == s) (fun y ↦ eqAt X (w y)) ry from rfl,
    holds_regClaim μ Ti.lay.yregs (· == s) w ry v q fun reg hreg hS i hi ↦ (hz _ (hm reg hreg hS i hi)).1,
    regSum_eq]
  rw [regSumL_congr _ _ _ fun reg hreg hS i hi ↦ (hz _ (hm reg hreg hS i hi)).2.symm]

/-- A commitment's cell inside it is its word's entry. -/
theorem comCell_of_lt (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) {n : ℕ}
    (hn : n < 2 ^ (if rec then L.nuRec else L.nuMain)) :
    Lvm.M3.comCell L qm qr rec n = if rec then qr.values.getD n 0 else qm.values.getD n 0 := by
  cases rec
  · simp only [Bool.false_eq_true, ite_false] at hn ⊢
    simp [Lvm.M3.comCell, hn, Vector.getD, Array.getD]
  · simp only [ite_true] at hn ⊢
    simp [Lvm.M3.comCell, hn, Vector.getD, Array.getD]

/-- The committed block's claim. -/
theorem holds_com (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec) (ry : List E)
    (v : E) :
    LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuMain (regClaim Ti .com Ti.comW ry v) qm ↔
      regSum Ti (· == .com) (zwE (Ti.zOf L pub qm qr)) ry = v :=
  holds_regTrue Ti hTi .com Ti.comW qm _ ry v fun y hy ↦ by
    have hb : Ti.comW y < 2 ^ L.nuMain := by have := hmaps y; simp only [hy] at this; exact this
    refine ⟨hb, ?_⟩
    simp only [zwE, TInst.zOf, hy, zE_ofBF64, comCell_of_lt L qm qr false (by simpa using hb)]
    rfl

/-- The `KS` aliases' claim. -/
theorem holds_ks (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec) (ry : List E)
    (v : E) :
    LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuMain (regClaim Ti .ks Ti.ksW ry v) qm ↔
      regSum Ti (· == .ks) (zwE (Ti.zOf L pub qm qr)) ry = v :=
  holds_regTrue Ti hTi .ks Ti.ksW qm _ ry v fun y hy ↦ by
    have hb : Ti.ksW y < 2 ^ L.nuMain := by have := hmaps y; simp only [hy] at this; exact this
    refine ⟨hb, ?_⟩
    simp only [zwE, TInst.zOf, hy, zE_ofBF64, comCell_of_lt L qm qr false (by simpa using hb)]
    rfl

/-- `σ′`'s claim. -/
theorem holds_sigma (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (ry : List E) (v : E) :
    LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuRec (regClaim Ti .sigma Ti.sigmaW ry v) qr ↔
      regSum Ti (· == .sigma) (zwE (Ti.zOf L pub qm qr)) ry = v :=
  holds_regTrue Ti hTi .sigma Ti.sigmaW qr _ ry v fun y hy ↦ by
    have hb : Ti.sigmaW y < 2 ^ L.nuRec := by have := hmaps y; simp only [hy] at this; exact this
    refine ⟨hb, ?_⟩
    simp only [zwE, TInst.zOf, hy, zE_ofBF64, comCell_of_lt L qm qr true (by simpa using hb)]
    rfl

/-- **The relayout's claim is `S_flat`'s true value** (the map inside `C_rec`). -/
theorem relay_true (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (ry : List E) :
    tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW ry L.nuRec fun w ↦ ofK (qr.values.getD w 0)) [] =
      regSum Ti (· == .sflat) (zwE (Ti.zOf L pub qm qr)) ry := by
  have hb : ∀ y, Ti.src? y = some .sflat → Ti.sflatW y < 2 ^ L.nuRec := fun y hy ↦ by
    have := hmaps y; simp only [hy] at this; exact this
  rw [relay_nil _ _ _ _ _ fun reg hreg hs i hi ↦ hb _ (by rw [src?_mem Ti hTi hreg hi, hs]), regSum_eq]
  refine regSumL_congr _ _ _ fun reg hreg hS i hi ↦ ?_
  have hy : Ti.src? (reg.base + i) = some .sflat := by rw [src?_mem Ti hTi hreg hi]; simpa using hS
  simp only [zwE, TInst.zOf, hy, zE_ofBF64, comCell_of_lt L qm qr true (by simpa using hb _ hy)]
  rfl

open CompPoly CMlPolynomialEval in
/-- A block's extension at a point of its height is the `eqAt`-weighted sum of its cells (any `L`; at `lay26`:
`LvmCertSMid3Tab.eval_comBlock_sum`). -/
theorem eval_comBlock_sumL (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) (τ off : ℕ) (z : List E)
    (hz : z.length = τ) :
    eval₂Mle (Lvm.M3.comBlock L qm qr rec τ off).values (algebraMap K E) (vecOf τ z) =
      ∑ n ∈ Finset.range (2 ^ τ), eqAt z n * ofK (Lvm.M3.comCell L qm qr rec (off + n)) := by
  subst hz
  rw [← sum_eqEval_mul, toList_vecOf z rfl]
  rw [Fin.sum_univ_eq_sum_range (fun x => LeanVM.Protocol.Verifier.eqEval z (boolPoint z.length x) *
    ofK ((Lvm.M3.comBlock L qm qr rec z.length off).values.getD x 0))]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [eqEval_boolPoint_eqAt]
  have hn' := Finset.mem_range.mp hn
  simp [Lvm.M3.comBlock, Vector.getD, hn']

/-- **The mini-bus's claims holding on the commitments give `BlockHolds`** (any `L`, under `LayOk`; at
`lay26`: `LvmCertSMid3Tab.blockHolds_of_tableClaims`). -/
theorem blockHolds_mini {T : List Tab} (hlay : LayOk L T) {cl : List ColumnClaim} (hret : Lvm.ASM.TabRet T cl)
    {qm : Column L.nuMain} {qr : Column L.nuRec}
    (h1 : ∀ c ∈ ((tableClaimsE T cl).filter (·.1 == .crec)).map (·.2.onStack),
      LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuRec c qr)
    (h2 : ∀ c ∈ ((tableClaimsE T cl).filter (·.1 == .main)).map (·.2.onStack),
      LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuMain c qm) :
    ∀ c ∈ cl, Lvm.M3.BlockHolds L T qm qr c := by
  intro c hc j i hj rec off hloc hcol
  have hi : i < (T.get ⟨j, hj⟩).w := (List.getElem?_eq_some_iff.mp hcol).1
  have hal := hlay (T.get ⟨j, hj⟩) (List.get_mem _ _) i hi
  unfold Lvm.M3.Aligned at hal
  rw [hcol] at hal
  obtain ⟨hdvd, hfit, -⟩ := hal
  have hτ : (T[j]?.map (·.τ)).getD 0 = (T.get ⟨j, hj⟩).τ := by simp [List.getElem?_eq_getElem hj]
  have hz : c.point.length = (T.get ⟨j, hj⟩).τ := (hret.1 c hc j i hloc).trans hτ
  have hmem : (if rec then Lvm.Com.crec else Lvm.Com.main,
      BClaim.point ⟨(T.get ⟨j, hj⟩).τ, off⟩ c.point c.value) ∈ tableClaimsE T cl := by
    unfold tableClaimsE
    refine List.mem_filterMap.mpr ⟨c, hc, ?_⟩
    rw [hloc]
    have hcol' : T[j].cols[i]? = some (.com rec off) := hcol
    simp only [Option.bind_some, List.getElem?_eq_getElem hj, hcol']
    rfl
  rw [eval_comBlock_sumL L qm qr rec _ off c.point hz]
  cases rec
  · simp only [Bool.false_eq_true, ite_false] at hfit hmem
    have hh := h2 _ (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩)
    rw [Lvm.ASM.holds_point hdvd hfit c.point hz c.value qm] at hh
    rw [← hh]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [comCell_of_lt L qm qr false (by simp; have := Finset.mem_range.mp hn; (clear * - hj hfit this; omega))]
    rfl
  · simp only [ite_true] at hfit hmem
    have hh := h1 _ (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩)
    rw [Lvm.ASM.holds_point hdvd hfit c.point hz c.value qr] at hh
    rw [← hh]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [comCell_of_lt L qm qr true (by simp; have := Finset.mem_range.mp hn; (clear * - hj hfit this; omega))]
    rfl

/-- **The relayout's point claim** (the block claim on `C_rec`'s whole `⟨relayRounds, 0⟩`) holds iff its value is
`C_rec`'s extension at the point. -/
theorem holds_relayPoint (hrec : L.nuRec = relayRounds) (rr : List E) (hrr : rr.length = relayRounds) (v : E)
    (qr : Column L.nuRec) :
    LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuRec (BClaim.point ⟨relayRounds, 0⟩ rr v).onStack qr ↔
      mleZ L.nuRec (fun w ↦ ofK (qr.values.getD w 0)) rr = v := by
  have hr : Finset.range (2 ^ L.nuRec) = Finset.range (2 ^ relayRounds) := by rw [hrec]
  rw [Lvm.ASM.holds_point (dvd_zero _) (by rw [hrec, zero_add]) rr hrr v qr, mleZ, hr]
  simp only [zero_add]

end Facts

/-! ## The proof of `typedSpecR`: the phases -/

/-- A list of four values sums to its entries. -/
theorem sum_four (l : List E) (h : l.length = 4) :
    l.sum = l.getD 0 0 + l.getD 1 0 + l.getD 2 0 + l.getD 3 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp at h ⊢
  ring

/-- **The typed phases' error side conditions, unpacked** (every follower's lead is at most `leadMaxT`). -/
theorem TErrs.facts {L₀ : ℕ} {I : M3Instance} {εmax T : ℝ≥0∞} (h : TErrs L₀ I εmax T) :
    (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax ∧ max (2 * errE 1) (abError I L₀ + 0) ≤ εmax ∧ errE phiVars ≤ εmax ∧
      abError I L₀ + 0 ≤ εmax ∧ abError I L₀ < 1 ∧ roundError L₀ 4 ≤ εmax ∧
      interpLead L₀ 2 (lambdaError L₀) ≤ εmax ∧ lambdaError L₀ + 0 ≤ εmax ∧ roundError L₀ 3 + T ≤ εmax ∧
      T ≤ εmax ∧ ∀ n, xiError I L₀ + sumcheckLead (List.replicate n none) T ≤ εmax := by
  have hM1 : abError I L₀ + 0 ≤ leadMaxT L₀ I T := le_max_of_le_right (le_max_left _ _)
  have hM2 : 2 * errE 1 ≤ leadMaxT L₀ I T := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hM3 : T ≤ leadMaxT L₀ I T := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hle : ∀ a : ℝ≥0∞, a ≤ a + leadMaxT L₀ I T := fun a ↦ le_self_add
  refine ⟨?_, (max_le hM2 hM1).trans h.follow, (hle _).trans h.acc, hM1.trans h.follow, h.ab.1,
    (hle _).trans (h.rounds 4 le_rfl), (hle _).trans h.lam.1, ?_, ?_, hM3.trans h.follow, fun n ↦ ?_⟩
  · rw [← roundError_eq, add_zero]; exact (hle _).trans (h.rounds 2 (by norm_num))
  · rw [add_zero]; exact (hle _).trans h.lam.2
  · exact (add_le_add le_rfl hM3).trans (h.rounds 3 (by norm_num))
  · exact (add_le_add le_rfl ((sumcheckLead_le _ _).trans hM3)).trans h.xi

section Phases

variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
  (R : Column L.nuMain × Column L.nuRec → Prop)

/-- The carried predicate: the mini-bus relation, `R`, `AccOk acc_in`. -/
def aR0 (q : Column L.nuMain × Column L.nuRec) : Prop :=
  M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧ R q ∧ AccOkT Ti pub

/-- **After the zerocheck**: the three values are the slot extensions of `A z`, `B z`, `(D + W) z` at `r_x`. -/
def aABC (z : List E × E × E × E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  (z.2.1 = mleZ xVars (matE Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) 0) z.1 ∧
    z.2.2.1 = mleZ xVars (matE Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) 1) z.1 ∧
    z.2.2.2 = mleZ xVars (fun x ↦ matE Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) 2 x +
      matE Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) 3 x) z.1) ∧ aR0 Ti L pub hτL R q

/-- The committed, `σ′` and `KS` region values are true. -/
def aRegs (ry rv : List E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  rv.getD 0 0 = regSum Ti (· == .com) (zwE (Ti.zOf L pub q.1 q.2)) ry ∧
    rv.getD 2 0 = regSum Ti (· == .sigma) (zwE (Ti.zOf L pub q.1 q.2)) ry ∧
    rv.getD 3 0 = regSum Ti (· == .ks) (zwE (Ti.zOf L pub q.1 q.2)) ry

/-- `C_rec`'s words over `E`. -/
abbrev recE (q : Column L.nuMain × Column L.nuRec) : ℕ → E := fun n ↦ ofK (q.2.values.getD n 0)

/-- The mini-bus's carried predicate (the typed claims' meaning, and `R`). -/
def aRm (w : List E × List E × List E) (r : List E × E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  (r.2 = mleZ L.nuRec (recE L q) r.1 ∧ aRegs Ti L pub w.1 w.2.2 q) ∧ R q

variable {L₀ : ℕ} {εmax : ℝ≥0∞} (S : Set (Column L.nuMain × Column L.nuRec)) (hS : S.ncard ≤ L₀)

/-- **The zerocheck** (`τ` and 20 equality-mode rounds): from doom of the wiring relation on the cube to doom of
the three values at `r_x`; lead `20·L₀/|E|`. -/
noncomputable def zeroSpecT (he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) :
    Spec zeroProg
      (Doomed (fun _ ↦ S) (fun q ↦ ZeroOn (relE Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) [] xVars ∧
        aR0 Ti L pub hτL R q))
      (fun z h ↦ z.1.length = xVars ∧ Doomed (fun _ ↦ S) (aABC Ti L pub hτL R z) h) εmax (leadT L₀)
      ((L₀ : ℝ≥0∞) * errE 2 + 0) := by
  unfold zeroProg
  refine (Lvm.KG.zeroSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS)
    (fun q ↦ relE Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) (aR0 Ti L pub hτL R) (n := xVars) (m := xVars) le_rfl
    (εmax := εmax) (T := 0)).bind fun τ ↦ ?_
  exact if hτ : τ.length = xVars then
    ((eqSumcheckSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS) (aR0 Ti L pub hτL R)
        (F := fun q acc ↦ eqCubeSum τ xVars (zeroGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) acc)
        (eqCubeSum_eqFamily τ xVars 2 hτ _ fun q pre post ↦ polyLE_zeroG _ _ _ pre post)
        (count := 3) (by norm_num) (by norm_num) zero_le he τ [] 0 (by simp)).mono
      (fun _ hp ↦ Doomed.mono hp.2 fun q hq ↦ ⟨(zeroOn_full _ hτ).mpr (by rw [← zero_nil]; exact hq.1.symm),
        hq.2⟩)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun rf ↦
      if hrf : rf.1.length = xVars then
        ((doomReadN (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
            (fun q ↦ rf.2 = eqCubeSum τ xVars (zeroGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) ([] ++ rf.1) ∧
              aR0 Ti L pub hτL R q) he 2).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind
          fun abc ↦
          (Spec.require (Pre := fun h ↦ abc.length = 2 + 1 ∧ Doomed (fun _ ↦ S) (fun q ↦ rf.2 =
              eqCubeSum τ xVars (zeroGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) ([] ++ rf.1) ∧ aR0 Ti L pub hτL R q) h)
            (Post := fun _ h ↦ Doomed (fun _ ↦ S)
              (aABC Ti L pub hτL R (rf.1, abc.getD 0 0, abc.getD 1 0, abc.getD 2 0)) h)
            fun _ hp hc ↦ Doomed.mono hp.2 fun q hq ↦ ⟨by
              rw [List.nil_append, eqCubeSum_full τ xVars _ hrf hτ, hc, zeroGT, ← hq.1.1, ← hq.1.2.1,
                ← hq.1.2.2], hq.2⟩).bind fun _ ↦
            (Spec.ret (Post := fun z h ↦ z.1.length = xVars ∧ Doomed (fun _ ↦ S) (aABC Ti L pub hτL R z) h)
              (rf.1, abc.getD 0 0, abc.getD 1 0, abc.getD 2 0)).mono (fun _ hp ↦ ⟨hrf, hp⟩)
              (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hp ↦ hrf (hp.1.trans hτ)) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hτ hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

/-- **The mini-bus** (`lbusTableCheckProg` at depth 13, `midBusTableSpecB` on the fixed candidate set): from doom
of the mini-bus relation with the carried predicate to doom of the returned claims' blocks with it, and the
table phase's return facts. -/
noncomputable def miniSpecTy (hfin : S.Finite) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth) {T : ℝ≥0∞}
    (hab : abError (inst L Ti.mbT hτL) L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : xiError (inst L Ti.mbT hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout Ti.mbT).tableLogHeights.foldl max 0) none) T ≤ εmax)
    (w : List E × List E × List E) (r : List E × E) :
    Spec (miniBusProg Ti)
      (fun h ↦ (∃ W, firstWord h = some W) ∧ Doomed (fun _ ↦ S) (fun q ↦
        M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧ aRm Ti L pub R w r q) h)
      (fun cl h ↦ Lvm.ASM.TabRet Ti.mbT cl ∧ Doomed (fun _ ↦ S) (fun q ↦
        (∀ c ∈ cl, Lvm.M3.BlockHolds L Ti.mbT q.1 q.2 c) ∧ aRm Ti L pub R w r q) h)
      εmax (abError (inst L Ti.mbT hτL) L₀ + 0) T :=
  Spec.congr (by rw [hμ]; rfl)
    ((Lvm.KG.specWithRet (Lvm.M3.midBusTableSpecB L Ti.mbT hτL (fun _ ↦ S) (aRm Ti L pub R w r) hlay hsc hkey
        hw hfix (fun _ ↦ True) (fun _ _ _ ↦ rfl) (fun _ ↦ hfin) (fun _ ↦ hS) (by rw [hμ]; norm_num) hab he4 hT
        hlam he3 hTf hxi) (Lvm.ASM.retOK_lbusTableCheckProg _ _)).mono (fun _ hp ↦ ⟨trivial, hp⟩)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl)

end Phases

/-! ## At P20: the good pair, `Good₂`, `midSpecOfRel`, `kcertSJ` -/

/-- **What the typed instance must meet at P20** (INT discharges it by `decide`/`norm_num`; the mini-bus's facts
as `MidHyp`'s). -/
structure THyp (Ti : TInst) : Prop where
  ok : Ti.Ok
  maps : Ti.MapsFit lay26
  /-- `acc_in` has `phiVars = 43` coordinates (false at today's `accVars = 28`: INT's refreeze sets 43). -/
  acc : ∀ x, (pubX x).accIn.pt.length = phiVars
  hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ
  sc : AllSc Ti.mbT
  layOk : LayOk lay26 Ti.mbT
  keys : KeysOk Ti.mbT
  width : ∀ t ∈ Ti.mbT, 0 < t.w
  fix : FixOk Ti.mbT
  /-- The mini-bus's columns are few (its claims' counts, as `side_assembleS`'s). -/
  widths : (Ti.mbT.map (·.w)).sum ≤ 2 ^ 38
  μBus : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), (inst lay26 Ti.mbT h).μBus = miniDepth
  errs : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), TErrs 37696 (inst lay26 Ti.mbT h) εS LkSJ

variable {Ti : TInst}

/-- **The bus half of a good pair, typed** (`GbA`'s shape: the typed half with the boundary claims, and the
incoming accumulator). -/
def GbT (Ti : TInst) (H : THyp Ti) (x : List UInt8) (p : Pair) : Prop :=
  (TGood Ti lay26 H.hτ (pubX x) p ∧ BndS x p.1) ∧ AccOkT Ti (pubX x)

/-- **The good pair of the typed backend**: `Good = Gb ∧ Gk` keeps `GoodA`'s shape (`GkS` unchanged). -/
def GoodT (Ti : TInst) (H : THyp Ti) : GoodRel := fun x qm qr ↦ GbT Ti H x (qm, qr) ∧ GkS x (qm, qr)

/-- The typed phases' claims hold on a pair, with the boundary claims (`BS`'s shape). -/
def BT (x : List UInt8) (a : OpenClaims) (p : Pair) : Prop := TClaimsHold lay26 a p ∧ BndS x p.1

/-- The typed phases' return facts (multiaffine claims, the counts). -/
def TRet (a : OpenClaims) : Prop :=
  (∀ c ∈ a.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ a.2, IsMultiaffine CMain.nu20 c.1) ∧ a.1.length ≤ 2 ^ 54 ∧
    a.2.length ≤ 2 ^ 39

/-- `eq(·, m)` is multiaffine on any number of coordinates. -/
theorem isMultiaffine_eqAt (n m : ℕ) : IsMultiaffine n fun X ↦ eqAt X m := by
  intro l hl k hk X
  have e : ∀ Y, eqAt (l.set k Y) m = LeanVM.Protocol.Verifier.eqEval (boolPoint n m) (l.set k Y) := fun Y ↦ by
    rw [eqEval_comm, ← eqEval_boolPoint_eqAt (l.set k Y) m, List.length_set, hl]
  show eqAt (l.set k X) m = (1 - X) * eqAt (l.set k 0) m + X * eqAt (l.set k 1) m
  rw [e, e, e]
  exact Lvm.ASM.isMultiaffine_eqEvalN (boolPoint n m) n l hl k hk X

/-- A region claim's weight is multiaffine. -/
theorem isMultiaffine_regClaim (Ti : TInst) (n : ℕ) (s : YSrc) (w : ℕ → ℕ) (ry : List E) (v : E) :
    IsMultiaffine n (regClaim Ti s w ry v).1 := by
  refine Lvm.Shape.isMultiaffine_list_sum _ _ fun reg _ ↦ ?_
  by_cases hS : (reg.src == s) = true
  · simp only [hS, ite_true]
    exact Lvm.Shape.isMultiaffine_list_sum _ _ fun i _ ↦ (isMultiaffine_eqAt n _).const_mul _
  · simp only [hS, Bool.false_eq_true, ite_false]
    exact IsMultiaffine.zero

/-- The mini-bus's claims on one commitment are multiaffine on it (`LayOk` at `lay26`). -/
theorem isMultiaffine_miniClaims (Ti : TInst) (hlay : LayOk lay26 Ti.mbT) (com : Lvm.Com)
    (cl : List LeanVM.Protocol.Verifier.ColumnClaim) :
    ∀ c ∈ miniClaims Ti com cl, IsMultiaffine (Lvm.ASM.nuOf com) c.1 := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  obtain ⟨he, hcom⟩ := List.mem_filter.mp he
  obtain ⟨hv, hw⟩ := Lvm.ASM.okC_tableClaimsE Ti.mbT cl hlay e he
  obtain ⟨com', b⟩ := e
  have : com' = com := by simpa using hcom
  subst this
  exact Lvm.ASM.isMultiaffine_onStack b hv hw

theorem length_miniClaims (Ti : TInst) (com : Lvm.Com) (cl : List LeanVM.Protocol.Verifier.ColumnClaim) :
    (miniClaims Ti com cl).length ≤ cl.length := by
  unfold miniClaims
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_filterMap_le _ _)

end Lvm.Typed
