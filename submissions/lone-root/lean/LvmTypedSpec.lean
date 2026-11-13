-- New for lvm2 (roll 8 = B1, B1-S0 skeleton; B-DES §1.2, §2): the typed backend's phases on the wire (zerocheck,
-- wiring, the `S_flat` relayout, A23 at `Φ_Q`, the mini-bus) and `typedSpecR`, in `midBusTableAccSpecB`'s shape
-- (`LvmAccSpecMid`); the new bus half `GbT`, `Good₂` of `GoodT`, `midSpecOfRel` and `kcertSJ` applied unchanged
-- (`LvmShape`, `LvmCertSMid3`, `LvmCertSKJ`). Not wired into `certified` (wave X/INT).
import LvmTyped
import LvmTypedAcc
import LvmTypedSpecP
import LvmShape
import LvmCertSKJ

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

/-- **The typed phases commit nothing and ask no proof of work.** -/
theorem cg_typedProg (Ti : TInst) (pub : Lvm.Pub) : NoCG (typedProg Ti pub) := by
  unfold typedProg zeroProg wireProg relayProg miniBusProg accProgQ lbusTableCheckProg
  refine Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (cg_sampleChallenges _) fun _ ↦ Lvm.M3.NoCG.bind (cg_sumcheck _ _ _)
    fun _ ↦ Lvm.M3.NoCG.bind (cg_readScalars _) fun _ ↦ Lvm.M3.NoCG.bind (cg_require _) fun _ ↦ cg_ret _)
    fun _ ↦ ?_
  refine Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind cg_sample fun _ ↦ Lvm.M3.NoCG.bind (cg_sumcheck _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_readScalars _) fun _ ↦ Lvm.M3.NoCG.bind (cg_readScalars _) fun _ ↦
      Lvm.M3.NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ ?_
  refine Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (cg_sumcheck _ _ _) fun _ ↦ Lvm.M3.NoCG.bind cg_readScalar fun _ ↦
    Lvm.M3.NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ ?_
  exact Lvm.M3.NoCG.bind (Lvm.Acc.cg_accProg _ _ _ _ _ _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (cg_lvmBusProg _) fun _ ↦ cg_tablePhaseClaims _ _ _)
      fun _ ↦ Lvm.M3.NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ cg_ret _

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
    rw [comCell_of_lt L qm qr false (by simp; have := Finset.mem_range.mp hn; omega)]
    rfl
  · simp only [ite_true] at hfit hmem
    have hh := h1 _ (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩)
    rw [Lvm.ASM.holds_point hdvd hfit c.point hz c.value qr] at hh
    rw [← hh]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [comCell_of_lt L qm qr true (by simp; have := Finset.mem_range.mp hn; omega)]
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

/-- The typed phases' program, unfolded. -/
theorem typedProg_eq (Ti : TInst) (pub : Lvm.Pub) : typedProg Ti pub =
    zeroProg.bind fun z ↦ (wireProg Ti pub z.2).bind fun w ↦ (relayProg Ti w.1 (w.2.2.getD 1 0)).bind fun r ↦
      (accProgQ Ti.Q Ti.lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (z.1 ++ w.1) w.2.1).bind
        fun _ ↦ (miniBusProg Ti).bind fun cl ↦ VerifierProgram.ret (typedClaims Ti w.1 w.2.2 r.1 r.2 cl) := by
  rw [typedProg]

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

/-- The four matrix values are the matrices' extensions at `r_x ++ r_y`. -/
def VsTrue (rxy vs : List E) : Prop := ∀ o < 4, vs.getD o 0 = matMle Ti.Q Ti.lay o rxy

/-- The committed, `σ′` and `KS` region values are true. -/
def aRegs (ry rv : List E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  rv.getD 0 0 = regSum Ti (· == .com) (zwE (Ti.zOf L pub q.1 q.2)) ry ∧
    rv.getD 2 0 = regSum Ti (· == .sigma) (zwE (Ti.zOf L pub q.1 q.2)) ry ∧
    rv.getD 3 0 = regSum Ti (· == .ks) (zwE (Ti.zOf L pub q.1 q.2)) ry

/-- Carried through the relayout. -/
def aR1 (z : List E × E × E × E) (w : List E × List E × List E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  VsTrue Ti (z.1 ++ w.1) w.2.1 ∧ aRegs Ti L pub w.1 w.2.2 q ∧ aR0 Ti L pub hτL R q

/-- **After the wiring**: `S_flat`'s value is true, with the rest. -/
def aW (z : List E × E × E × E) (w : List E × List E × List E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  w.2.2.getD 1 0 = regSum Ti (· == .sflat) (zwE (Ti.zOf L pub q.1 q.2)) w.1 ∧ aR1 Ti L pub hτL R z w q

/-- `C_rec`'s words over `E`. -/
abbrev recE (q : Column L.nuMain × Column L.nuRec) : ℕ → E := fun n ↦ ofK (q.2.values.getD n 0)

/-- **After the relayout**: `C_rec`'s extension at the point, with the rest. -/
def aRl (z : List E × E × E × E) (w : List E × List E × List E) (r : List E × E)
    (q : Column L.nuMain × Column L.nuRec) : Prop :=
  r.2 = mleZ L.nuRec (recE L q) r.1 ∧ aR1 Ti L pub hτL R z w q

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

/-- **`γ`'s escape**: a wrong triple batched by `γ` meets the true one at `2/|E|` of the `γ`. -/
theorem wire_escape (hTi : Ti.Ok) (z : List E × E × E × E) (q : Column L.nuMain × Column L.nuRec)
    (hq : ¬ aABC Ti L pub hτL R z q) :
    avgE (fun γ ↦ indE (z.2.1 + γ * z.2.2.1 + γ * γ * z.2.2.2 =
      tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) [] ∧ aR0 Ti L pub hτL R q)) ≤ errE 2 := by
  by_cases hR : aR0 Ti L pub hτL R q
  · have hne := fun h ↦ hq ⟨h, hR⟩
    refine (avgE_mono fun γ ↦ indE_mono fun hγ ↦ ?_).trans (quadT_escape hne)
    rw [wire_nil _ _ hTi.1] at hγ
    exact hγ.1
  · refine (avgE_mono fun γ ↦ indE_mono (q := False) fun h ↦ hR h.2).trans ?_
    exact (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le

/-- **The wiring** (`γ`, 21 plain rounds, the matrix and region values, the final check): from doom of the three
values at `r_x` to doom of the region values at `r_y` and the matrix values; lead `L₀·2/|E|`. -/
noncomputable def wireSpecT (hTi : Ti.Ok) (he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) (z : List E × E × E × E) :
    Spec (wireProg Ti pub z.2)
      (fun h ↦ z.1.length = xVars ∧ Doomed (fun _ ↦ S) (aABC Ti L pub hτL R z) h)
      (fun w h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧ w.2.2.length = 4 ∧
        Doomed (fun _ ↦ S) (aW Ti L pub hτL R z w) h) εmax ((L₀ : ℝ≥0∞) * errE 2 + 0) 0 := by
  exact if hz : z.1.length = xVars then by
    unfold wireProg
    refine ((doomSample (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS) (aABC Ti L pub hτL R z)
      (fun γ q ↦ z.2.1 + γ * z.2.2.1 + γ * γ * z.2.2.2 =
        tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) [] ∧ aR0 Ti L pub hτL R q)
      (errE 2) (fun q hq ↦ wire_escape Ti L pub hτL R hTi z q hq) (εmax := εmax) (T := 0)).mono
      (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun γ ↦ ?_
    refine (LeanVM.Protocol.KeccakGkr.sumcheckSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS)
      (aR0 Ti L pub hτL R) (F := fun q acc ↦ tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) acc)
      (tCubeSum_plainFamily yVars 2 _ fun q pre post ↦ polyLE_wireG _ _ _ _ _ pre post)
      (count := 3) (by norm_num) (by norm_num) zero_le he yVars [] _ (by simp)).bind fun rf ↦ ?_
    exact if hry : rf.1.length = yVars then
      ((doomReadN (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
          (fun q ↦ rf.2 = tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) ([] ++ rf.1) ∧
            aR0 Ti L pub hτL R q) (zero_le) 3).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl
          le_rfl).bind fun vs ↦
        if hvs : vs.length = 4 then
          ((doomReadN (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
              (fun q ↦ rf.2 = tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) ([] ++ rf.1) ∧
                aR0 Ti L pub hτL R q) (zero_le) 3).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl
              le_rfl).bind fun rv ↦
            if hrv : rv.length = 4 then
              (Spec.require (Pre := fun h ↦ rv.length = 3 + 1 ∧ Doomed (fun _ ↦ S) (fun q ↦ rf.2 =
                  tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) ([] ++ rf.1) ∧
                    aR0 Ti L pub hτL R q) h)
                (Post := fun _ h ↦ Doomed (fun _ ↦ S) (aW Ti L pub hτL R z (rf.1, vs, rv)) h)
                fun _ hp hc ↦ Doomed.mono hp.2 fun q ⟨hS1, hV, ⟨h0, h2, h3⟩, hR⟩ ↦ ⟨by
                  rw [List.nil_append, tCubeSum_full _ _ hry, wireGT, wireM_full _ _ hTi.1 _ _ _ hz,
                    mleZ_zOf Ti L pub hTi, hc, sum_four rv hrv]
                  simp only at hS1 h0 h2 h3
                  rw [← hV 0 (by norm_num), ← hV 1 (by norm_num), ← hV 2 (by norm_num), ← hV 3 (by norm_num),
                    h0, hS1, h2, h3], hR⟩).bind fun _ ↦
                (Spec.ret (Post := fun w h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧
                    w.2.2.length = 4 ∧ Doomed (fun _ ↦ S) (aW Ti L pub hτL R z w) h) (rf.1, vs, rv)).mono
                  (fun _ hp ↦ ⟨hz, hry, hvs, hrv, hp⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
            else Spec.dead.mono (fun _ hp ↦ hrv hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
        else Spec.dead.mono (fun _ hp ↦ hvs hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
    else Spec.dead.mono (fun _ hp ↦ hry hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hz hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

/-- **The `S_flat` relayout** (19 plain rounds, `v_R`, the final check): from doom of `S_flat`'s region value at
`r_y` to doom of `C_rec`'s extension at the point; lead `0`, follower `Tf`. -/
noncomputable def relaySpecT (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) {Tf : ℝ≥0∞} (hTf : Tf ≤ εmax) (z : List E × E × E × E)
    (w : List E × List E × List E) :
    Spec (relayProg Ti w.1 (w.2.2.getD 1 0))
      (fun h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧ w.2.2.length = 4 ∧
        Doomed (fun _ ↦ S) (aW Ti L pub hτL R z w) h)
      (fun r h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧ r.1.length = relayRounds ∧
        Doomed (fun _ ↦ S) (aRl Ti L pub hτL R z w r) h) εmax 0 Tf := by
  exact if hl : z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 then by
    unfold relayProg
    refine ((LeanVM.Protocol.KeccakGkr.sumcheckSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS)
      (aR1 Ti L pub hτL R z w)
      (F := fun q acc ↦ tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW w.1 L.nuRec (recE L q)) acc)
      (tCubeSum_plainFamily L.nuRec 2 _ fun q pre post ↦ polyLE_relayG _ _ _ _ _ pre post)
      (count := 3) (by norm_num) (by norm_num) zero_le he relayRounds [] _ (by simp [hrec])).mono
      (fun _ hp ↦ Doomed.mono hp.2.2.2.2 fun q hq ↦ ⟨by
        rw [hq.1, relay_true Ti L pub hTi hmaps q.1 q.2 w.1], hq.2⟩)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun rf ↦ ?_
    exact if hrr : rf.1.length = relayRounds then
      ((doomRead (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
          (fun q ↦ rf.2 = tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW w.1 L.nuRec (recE L q)) ([] ++ rf.1) ∧
            aR1 Ti L pub hτL R z w q) hTf).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind
        fun vR ↦
        (Spec.require (Pre := Doomed (fun _ ↦ S) (fun q ↦
              rf.2 = tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW w.1 L.nuRec (recE L q)) ([] ++ rf.1) ∧
                aR1 Ti L pub hτL R z w q))
            (Post := fun _ h ↦ Doomed (fun _ ↦ S) (aRl Ti L pub hτL R z w (rf.1, vR)) h)
            fun _ hp hc ↦ Doomed.mono hp fun q hq ↦ ⟨by
              have h1 : vR = mleZ L.nuRec (recE L q) rf.1 := hq.1
              rw [List.nil_append, tCubeSum_full _ _ (hrr.trans hrec.symm), relayGT, hc, h1]
              rfl, hq.2⟩).bind fun _ ↦
          (Spec.ret (Post := fun r h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧
              r.1.length = relayRounds ∧ Doomed (fun _ ↦ S) (aRl Ti L pub hτL R z w r) h) (rf.1, vR)).mono
            (fun _ hp ↦ ⟨hl.1, hl.2.1, hl.2.2, hrr, hp⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hrr hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hl ⟨hp.1, hp.2.1, hp.2.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

/-- **A23 at `Φ_Q`** (`accSpecQ`): outside `AccGood` (a wrong matrix value or a wrong `acc_in`) the phase's own
escape bounds the run (`1/|E|` per `κ_j`, `43/|E|` at `t`); inside it, the matrix values and `AccOk acc_in` are true
and leave the carried predicate. -/
noncomputable def accSpecTy (hTi : Ti.Ok) (hacc : pub.accIn.pt.length = phiVars) {Tm : ℝ≥0∞}
    (hD : errE phiVars ≤ εmax) (hTm : Tm ≤ εmax) (z : List E × E × E × E) (w : List E × List E × List E)
    (r : List E × E) :
    Spec (accProgQ Ti.Q Ti.lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (z.1 ++ w.1) w.2.1)
      (fun h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧ r.1.length = relayRounds ∧
        Doomed (fun _ ↦ S) (aRl Ti L pub hτL R z w r) h)
      (fun _ h ↦ Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧
        aRm Ti L pub R w r q) h) εmax (max (2 * errE 1) Tm) Tm :=
  if hl : z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 then
    (accSpecQ Ti.Q Ti.lay hTi.1 (ok := true) (yIn := FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3)
        (z.1 ++ w.1) w.2.1 (by rw [List.length_map, hacc]) (by rw [List.length_append, hl.1, hl.2.1])
        hl.2.2 (Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧
          aRm Ti L pub R w r q)) (fun _ _ _ h ↦ h) hD hTm).mono
      (fun _ hp ↦ by
        by_cases hg : Lvm.Acc.AccGood 2 true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (PhiQ Ti.Q Ti.lay)
            (deltaQ Ti.Q Ti.lay w.2.1 (z.1 ++ w.1))
        · refine .inr (Doomed.mono hp.2.2.2.2 fun q ⟨hm, ⟨hv, hrg⟩, hR⟩ ↦ ⟨hv, fun o ho ↦ ?_, hrg, hm, hR, hg.2.1⟩)
          have h0 := hg.2.2 o (by norm_num; omega)
          rw [deltaQ, ite_eq_left ho, sub_eq_zero] at h0
          exact h0
        · exact .inl hg)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hl ⟨hp.1, hp.2.1, hp.2.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

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

/-- **The typed phases on a fixed candidate set** (`typedSpecR` at `C h = S`): the zerocheck, the wiring, the
relayout, A23 and the mini-bus composed; the first commitment's word carried to the mini-bus. -/
noncomputable def typedSpecIn (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVars) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (hfin : S.Finite) {T : ℝ≥0∞} (herr : TErrs L₀ (inst L Ti.mbT hτL) εmax T) :
    Spec (typedProg Ti pub)
      (fun h ↦ (∃ W, firstWord h = some W) ∧
        Doomed (fun _ ↦ S) (fun p ↦ TGood Ti L hτL pub p ∧ R p ∧ AccOkT Ti pub) h)
      (fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold L out p ∧ R p) h) εmax (leadT L₀) T := by
  obtain ⟨he, hLacc, hD, hTm, hab, he4, hTl, hlam, he3, hTf, hxi⟩ := herr.facts
  have hJ : ∀ {α : Type} (p : VerifierProgram α) (h₀ l : List Ev), p.Reach h₀ l →
      (∃ W, firstWord h₀ = some W) → ∃ W, firstWord (h₀ ++ l) = some W :=
    fun _ _ l _ ⟨W, hW⟩ ↦ ⟨W, firstWord_append hW l⟩
  refine Spec.congr (typedProg_eq Ti pub).symm ?_
  refine (((zeroSpecT Ti L pub hτL R S hS he).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨Doomed.mono hp.2 fun q hq ↦ ⟨⟨(wiringRel_iff _ _ hTi.1 _).mpr ((zeroOn_nil _ _).mp hq.1),
      hq.2.1⟩, hq.2.2.1, hq.2.2.2⟩, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun z ↦ ?_
  refine ((wireSpecT Ti L pub hτL R S hS hTi he z).frame _ (hJ _)).bind fun w ↦ ?_
  -- the relayout's follower is A23, whose lead is `max (2/|E|) (abError + 0)` (`hLacc`)
  refine ((relaySpecT Ti L pub hτL R S hS hTi hmaps hrec he hLacc z w).frame _ (hJ _)).bind fun r ↦ ?_
  exact if hr1 : r.1.length = relayRounds then
    ((accSpecTy Ti L pub hτL R S hTi hacc hD hTm z w r).frame _ (hJ _)).bind fun _ ↦
      ((miniSpecTy Ti L pub hτL R S hS hfin hsc hlay hkey hw hfix hμ hab he4 hTl hlam he3 hTf (hxi _) w r).mono
        (fun _ hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun cl ↦
        (Spec.ret (Post := fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold L out p ∧ R p) h)
          (typedClaims Ti w.1 w.2.2 r.1 r.2 cl)).mono
          (fun _ hp ↦ Doomed.mono hp.2 fun q hq ↦ by
            obtain ⟨⟨h1, h2⟩, hR⟩ := hq
            refine ⟨blockHolds_mini L hlay hp.1
                (fun c hc ↦ h1 c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)))
                (fun c hc ↦ h2 c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))), ⟨?_, ?_, ?_, ?_⟩, hR⟩
            · exact ((holds_relayPoint L hrec r.1 hr1 r.2 q.2).mp (h1 _ (List.mem_cons_self ..))).symm
            · exact ((holds_com Ti L pub hTi hmaps q.1 q.2 w.1 _).mp (h2 _ (List.mem_cons_self ..))).symm
            · exact ((holds_sigma Ti L pub hTi hmaps q.1 q.2 w.1 _).mp
                (h1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).symm
            · exact ((holds_ks Ti L pub hTi hmaps q.1 q.2 w.1 _).mp
                (h2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).symm)
          (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hr1 hp.1.2.2.2.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

end Phases

/-- **The typed phases' specification** (B-DES §2's `typedSpecR`, in `midBusTableAccSpecB`'s shape, generic in
the candidate set `C` and the carried `R`): from `G ∧ firstWord ∧ Doomed C (TGood ∧ R ∧ AccOkT)` to the doom of the
returned claims with `R`. Owner **L-B** (B1-V: the programs' final form). -/
noncomputable def typedSpecR (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
    (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVars) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (C : List Ev → Set (Column L.nuMain × Column L.nuRec)) (R : Column L.nuMain × Column L.nuRec → Prop)
    {L₀ : ℕ} {εmax T : ℝ≥0∞} (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (herr : TErrs L₀ (inst L Ti.mbT hτL) εmax T) :
    Spec (typedProg Ti pub)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ TGood Ti L hτL pub p ∧ R p ∧ AccOkT Ti pub) h)
      (fun out h ↦ Doomed C (fun p ↦ TClaimsHold L out p ∧ R p) h) εmax (leadT L₀) T :=
  (Lvm.M3.Spec.glue (ι := {S : Set (Column L.nuMain × Column L.nuRec) // S.Finite ∧ S.ncard ≤ L₀})
      (fun h ↦ ⟨C h, hf h, hc h⟩) G (fun h₀ l hG ↦ Subtype.ext (hCG h₀ l hG))
      fun S ↦ typedSpecIn Ti L pub hτL R S.1 S.2.2 hTi hmaps hrec hacc hsc hlay hkey hw hfix hμ S.2.1 herr).mono
    (fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

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

/-- **`NodeSound` for `Good₂ (GoodT Ti H)`** from the big layout's (`LvmShape.nodeSound₂`, unchanged). -/
theorem nodeSoundT₂ (H : THyp Ti) {VS : Lvm.T.SProg} {vk : RecursionFast.Digest}
    {child : Column 19 → RecursionFast.Signed} (h : Lvm.ASM.NodeSound VS vk (GoodT Ti H) child) :
    Lvm.ASM.NodeSound VS vk (Good₂ (GoodT Ti H)) child :=
  Lvm.Shape.nodeSound₂ h

/-- The typed phases' claims hold on a pair, with the boundary claims (`BS`'s shape). -/
def BT (x : List UInt8) (a : OpenClaims) (p : Pair) : Prop := TClaimsHold lay26 a p ∧ BndS x p.1

/-- **The typed claims and the Keccak phases' claims, in both shapes** (`assembleS₂`'s): `C_main`'s through
`onStackZ` when small. -/
def assembleT₂ (x : List UInt8) (a : OpenClaims) (kg : KgOut) : OpenClaims :=
  (a.1 ++ (assembleS [] (pubX x) [] kg).1, onStackZs x (a.2 ++ (assembleS [] (pubX x) [] kg).2))

/-- **The middle phases of the typed backend in both shapes**: the typed phases, V_S phases 4–7, the claims. -/
def midT₂ (Ti : TInst) (x : List UInt8) : VerifierProgram OpenClaims :=
  typedProg Ti (pubX x) >>= fun a ↦ kgProgS (hdX x).s (pubX x).n >>= fun k ↦
    VerifierProgram.ret (assembleT₂ x a k)

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

/-- **Every return of the typed phases meets `TRet`.** Owner **L-B**. -/
theorem retOK_typedProg (H : THyp Ti) (pub : Lvm.Pub) : RetOK TRet (typedProg Ti pub) := by
  rw [typedProg_eq]
  refine RetOK.bind_true fun z ↦ RetOK.bind_true fun w ↦ RetOK.bind_true fun r ↦ RetOK.bind_true fun _ ↦ ?_
  refine (Lvm.ASM.retOK_lbusTableCheckProg Ti.mbT miniDepth).bind fun cl hcl ↦ RetOK.ret ?_
  have hm1 := isMultiaffine_miniClaims Ti H.layOk .crec cl
  have hm2 := isMultiaffine_miniClaims Ti H.layOk .main cl
  have hl1 := length_miniClaims Ti .crec cl
  have hl2 := length_miniClaims Ti .main cl
  have hcl' : cl.length ≤ 2 ^ 38 := hcl.2.trans H.widths
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_, ?_⟩
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact Lvm.ASM.isMultiaffine_onStack _ le_rfl (Lvm.ASM.isMultiaffine_eqEvalN _ _)
    rcases List.mem_cons.mp hc with rfl | hc
    · exact isMultiaffine_regClaim Ti 19 _ _ _ _
    · exact hm1 c hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact isMultiaffine_regClaim Ti _ _ _ _ _
    rcases List.mem_cons.mp hc with rfl | hc
    · exact isMultiaffine_regClaim Ti _ _ _ _ _
    · exact hm2 c hc
  · simp only [typedClaims, List.length_cons]; omega
  · simp only [typedClaims, List.length_cons]; omega

/-- **The semantic link, typed** (`link_assembleS₂`'s): the assembled claims holding on a pair give the Keccak
phases' relation and the typed claims with the boundary claims on the view. Owner **L-B**. -/
theorem linkT₂ (x : List UInt8) (a : OpenClaims) (k : KgOut) (p : Pair) (ha : TRet a) (hk : KgRet k)
    (h1 : ∀ c ∈ (assembleT₂ x a k).1, LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c p.2)
    (h2 : ∀ c ∈ (assembleT₂ x a k).2, LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c p.1) :
    KcS k (vp x p) ∧ BT x a (vp x p) := by
  have h2' : ∀ c ∈ a.2 ++ (assembleS [] (pubX x) [] k).2,
      LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c (vp x p).1 := by
    intro c hc
    unfold assembleT₂ onStackZs at h2
    unfold vp view
    by_cases hs : Lvm.Shape.small x = true
    · simp only [hs, ite_true, List.mem_map] at h2 ⊢
      exact (Lvm.Shape.holds_onStackZ c p.1).mp (h2 _ ⟨c, hc, rfl⟩)
    · simp only [hs, ite_false, Bool.false_eq_true] at h2 ⊢
      exact h2 c hc
  have h1' : ∀ c ∈ a.1 ++ (assembleS [] (pubX x) [] k).1, LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c p.2 := h1
  have hc := Lvm.ASM.holdsC_of_assembleS (fun c hc ↦ h1' c (List.mem_append_right _ hc))
    (fun c hc ↦ h2' c (List.mem_append_right _ hc))
  obtain ⟨⟨hr, -, -⟩, ⟨hrk, -, hck, -, -, hkc, hks⟩⟩ := hk
  have hm : ∀ b, (Lvm.Com.main, b) ∈ Lvm.ASM.claimsS [] (pubX x) [] k →
      LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 b.onStack (vp x p).1 := fun b hb ↦ hc _ hb
  have hTP : ∀ b ∈ Lvm.VEq.tapeClaimsE k.1 (pubX x),
      LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 b.onStack (vp x p).1 :=
    fun b hb ↦ hm b (by simp [Lvm.ASM.claimsS, hb])
  have hKK : ∀ b ∈ Lvm.VEq.keccakClaimsE Lvm.VEq.ksBlk k.2.1,
      LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 b.onStack (vp x p).1 :=
    fun b hb ↦ hm b (by simp [Lvm.ASM.claimsS, hb])
  have hsub : ∀ l : List (Lvm.Com × BClaim), (∀ e ∈ l, e ∈ Lvm.ASM.claimsS [] (pubX x) [] k) →
      ∀ e ∈ l, Lvm.ASM.HoldsC (vp x p).1 (vp x p).2 e := fun l hl e he ↦ hc e (hl e he)
  refine ⟨⟨Lvm.ASM.tapeClaims_of k.1 hr (pubX x) hTP,
    ⟨Lvm.ASM.callerClaims_ks k.2.1 hrk hck hKK (hsub _ (fun e he ↦ by simp [Lvm.ASM.claimsS, he])),
      Lvm.ASM.ksLinkClaims_of k.2.2.1 k.2.2.2.1 k.2.2.2.2 hkc hks
        (hsub _ (fun e he ↦ by simp [Lvm.ASM.claimsS, he]))⟩⟩,
    ⟨fun c hc ↦ h1' c (List.mem_append_left _ hc), fun c hc ↦ h2' c (List.mem_append_left _ hc)⟩,
    Lvm.ASM.bndS_of_tape x _ hTP⟩

/-- **The side conditions, typed** (`side_midS₂`'s). Owner **L-B**. -/
theorem sideT₂ (x : List UInt8) (a : OpenClaims) (k : KgOut) (ha : TRet a) (hk : KgRet k) :
    (∀ c ∈ (assembleT₂ x a k).1, IsMultiaffine 19 c.1) ∧
    (∀ c ∈ (assembleT₂ x a k).2, IsMultiaffine CMain.nu20 c.1) ∧
    (assembleT₂ x a k).1.length ≤ 2 ^ 55 ∧ (assembleT₂ x a k).2.length ≤ 2 ^ 40 := by
  obtain ⟨s1, s2, s3, s4⟩ := Lvm.ASM.side_assembleS [] (pubX x) [] k (fun _ h ↦ by simp at h)
    ⟨fun _ h ↦ by simp at h, by simp⟩ (by simp) hk (by rw [Lvm.ASM.length_pubX_h]; norm_num)
  obtain ⟨a1, a2, a3, a4⟩ := ha
  have hk1 : (k.2.1.2.2.1.1).length ≤ 1 := hk.2.2.2.2.1
  have l1 : (assembleS [] (pubX x) [] k).1.length ≤ 1 := by
    rw [Lvm.ASM.assembleS_eq, List.length_map]
    simpa using Lvm.ASM.length_crec_le [] (pubX x) [] k
  have l2 : (assembleS [] (pubX x) [] k).2.length ≤ 40 := by
    rw [Lvm.ASM.assembleS_eq, List.length_map]
    have h := Lvm.ASM.length_claimsS [] (pubX x) [] k
    have h0 : (tableClaimsE [] []).length = 0 := rfl
    rw [Lvm.ASM.length_pubX_h, h0] at h
    exact (List.length_filter_le _ _).trans (by omega)
  have hm : ∀ c ∈ a.2 ++ (assembleS [] (pubX x) [] k).2, IsMultiaffine CMain.nu20 c.1 := fun c hc ↦ by
    rcases List.mem_append.mp hc with hc | hc
    · exact a2 c hc
    · exact s2 c hc
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hc with hc | hc
    · exact a1 c hc
    · exact s1 c hc
  · unfold assembleT₂ onStackZs at hc
    split_ifs at hc
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact Lvm.Shape.isMultiaffine_onStackZ (hm c' hc')
    · exact hm c hc
  · simp only [assembleT₂, List.length_append]
    omega
  · simp only [assembleT₂, onStackZs]
    split_ifs <;> simp only [List.length_map, List.length_append] <;> omega

/-- **The typed phases on the viewed pairs** (`specBusA₂`'s: `typedSpecR` at `imgC x`, the doom pulled back to
`candPairs`). -/
noncomputable def specBusT₂ (H : THyp Ti) (x : List UInt8) (N : Pair → Prop) :
    Spec (typedProg Ti (pubX x))
      (fun h ↦ RootShape h ∧
        Doomed candPairs (fun p ↦ GbT Ti H x (vp x p) ∧ (GkS x (vp x p) ∧ N (vp x p))) h)
      (fun a h ↦ Doomed candPairs
        (fun p ↦ (BT x a (vp x p) ∧ N (vp x p)) ∧ (GkS x (vp x p) ∧ N (vp x p))) h ∧ RootShape h)
      εS εS LkSJ :=
  have S0 := typedSpecR Ti lay26 (pubX x) H.hτ H.ok H.maps rfl (H.acc x) H.sc H.layOk H.keys H.width H.fix
    (H.μBus H.hτ) (imgC x)
    (fun p ↦ BndS x p.1 ∧ GkS x p ∧ N p) (L₀ := 37696) (εmax := εS) (T := LkSJ)
    (fun h ↦ 2 ≤ (commits h).length) (imgC_append x) (fun _ ↦ Set.toFinite _) (imgC_ncard_le x) (H.errs H.hτ)
  (S0.frame RootShape (fun _ _ hl hr ↦ Lvm.M3.rootShape_append
      ((cg_typedProg Ti (pubX x)).1.reach_commits hl) hr)).mono
    (fun _ ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.M3.rootShape_two hr, Lvm.M3.rootShape_firstWord hr, doomed_imgC.mpr
      (Doomed.mono hDm fun _ hq ↦ ⟨⟨⟨hq.1, hq.2.1.1⟩, hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgC.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩, hp.2⟩)
    le_rfl (H.errs H.hτ).lead le_rfl

/-- **O6 for the typed backend in both shapes** (`midSpecR₂`'s proof): `MidSpecR (midT₂ Ti) (Good₂ (GoodT Ti H))
εS εS` by `midSpecOfRel`, with `LvmShape.specKgS₂` unchanged. -/
theorem midSpecR_T₂ (H : THyp Ti) : MidSpecR (midT₂ Ti) (Good₂ (GoodT Ti H)) εS εS := by
  intro x₀ T hT
  have M : MidSpecR (fun _ ↦ typedProg Ti (pubX x₀) >>= fun a ↦
        kgProgS (hdX x₀).s (pubX x₀).n >>= fun k ↦ VerifierProgram.ret (assembleT₂ x₀ a k))
      (fun _ qm qr ↦ GbT Ti H x₀ (vp x₀ (qm, qr)) ∧ GkS x₀ (vp x₀ (qm, qr))) εS εS :=
    midSpecOfRel
      (busP := fun _ ↦ typedProg Ti (pubX x₀))
      (kgP := fun _ ↦ kgProgS (hdX x₀).s (pubX x₀).n)
      (asm := fun _ a k ↦ assembleT₂ x₀ a k) (Lb := εS) (Lk := LkSJ)
      (Gb := fun _ p ↦ GbT Ti H x₀ (vp x₀ p)) (Gk := fun _ p ↦ GkS x₀ (vp x₀ p))
      (B := fun _ a p ↦ BT x₀ a (vp x₀ p)) (Kc := fun k p ↦ KcS k (vp x₀ p))
      (Qa := fun _ ↦ TRet) (Qk := KgRet)
      (fun _ ↦ specBusT₂ H x₀ fun p ↦ ¬ (GbT Ti H x₀ p ∧ GkS x₀ p))
      (fun _ ↦ retOK_typedProg H _)
      (fun _ a T hT ↦ (specKgS₂ x₀
          (fun p ↦ BT x₀ a (vp x₀ p) ∧ ¬ (GbT Ti H x₀ (vp x₀ p) ∧ GkS x₀ (vp x₀ p))) T hT).mono
        (fun _ hd ↦ Doomed.mono hd fun _ hq ↦ ⟨⟨hq.1, hq.2.2⟩, hq.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl
        le_rfl)
      (fun _ ↦ retOK_kgProgS _ _) (fun _ ↦ cg_kgProgS _ _)
      (fun _ a k p ha hk h1 h2 ↦ linkT₂ x₀ a k p ha hk h1 h2)
      (fun _ a k ha hk ↦ sideT₂ x₀ a k ha hk)
  obtain ⟨S⟩ := M x₀ T hT
  have S' : Spec (midT₂ Ti x₀) RootShape (Lvm.ASM.OpenPostR
      (fun _ qm qr ↦ GbT Ti H x₀ (vp x₀ (qm, qr)) ∧ GkS x₀ (vp x₀ (qm, qr))) x₀) εS εS T := by
    unfold midT₂
    exact S
  refine ⟨S'.mono (fun _ h ↦ h) (fun cl h hp ↦ ?_) le_rfl le_rfl le_rfl⟩
  exact (openPostR_congr
    (G := fun _ qm qr ↦ GbT Ti H x₀ (vp x₀ (qm, qr)) ∧ GkS x₀ (vp x₀ (qm, qr)))
    (G' := Good₂ (GoodT Ti H)) fun _ _ ↦ Iff.rfl).mp hp

/-- **The middle phases' shape, typed** (`midShape_midS₂`'s). -/
theorem midShape_T₂ (H : THyp Ti) : MidShape (midT₂ Ti) where
  noCommit _ := (Lvm.M3.NoCG.bind (cg_typedProg _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_kgProgS _ _) fun _ ↦ Lvm.M3.cg_ret _).1
  noGrind _ := (Lvm.M3.NoCG.bind (cg_typedProg _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_kgProgS _ _) fun _ ↦ Lvm.M3.cg_ret _).2
  recAffine x l cl hl :=
    ((retOK_typedProg H _).bind fun a ha ↦ (retOK_kgProgS _ _).bind fun k hk ↦
      RetOK.ret (sideT₂ x a k ha hk).1 :
      RetOK (fun cl : OpenClaims ↦ ∀ c ∈ cl.1, IsMultiaffine 19 c.1) (midT₂ Ti x)) l cl hl

/-- **The knowledge certificate of the typed backend** (J2C-DES T9's `kcertSJ`, unchanged): from `midSpecR_T₂`,
`midShape_T₂` and an extraction for `Good₂ (GoodT Ti H)` (J2C-C's `extJ` at the typed `NodeSound`, L-D/INT). -/
noncomputable def kcertT (H : THyp Ti) {VS : Lvm.T.SProg} {vk : RecursionFast.Digest}
    (X : ExtJ (midT₂ Ti) (Good₂ (GoodT Ti H)) VS vk) :
    Lvm.FS.KCert (schemeS vk (PSWith (midT₂ Ti))) (RecursionFast.Rel (Lvm.T.accV VS vk)) :=
  kcertSJ (midSpecR_T₂ H) le_rfl (midShape_T₂ H) X

end Lvm.Typed
