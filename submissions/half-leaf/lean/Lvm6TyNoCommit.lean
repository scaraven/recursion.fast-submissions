-- New for lvm6 Y1 (2026-11-23): the typed phases and the mini-bus at `E` commit nothing (CAND-decision §4 step 2:
-- `Stmt.noCommit` of `typedProgE` and of `miniBusLProg6`, owed by Y1).
import Lvm6TyProg
import LvmCertSFrame

/-!
# No commitment in the typed phases and the mini-bus

`VerifierProgram.NoCommit` (`LvmCertSFrame`) for every program of `Lvm6TyProg` and `Lvm6MbProg`; then the form
`Stmt.noCommit` asks: every run has no commitment (`typedProgE_noCommit`, `miniBusLProg6_noCommit`, by
`NoCommit.reach_commits`), so `(commits h).length` is unchanged across them.
-/

set_option autoImplicit false

namespace Lvm6.Ty

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.VerifierProgram
open Lvm.E2V Lvm6.Mb

section Leaves

variable {α β : Type}

theorem nc_ret (a : α) : (VerifierProgram.ret a).NoCommit := trivial

theorem nc_pure (a : α) : (pure a : VerifierProgram α).NoCommit := trivial

theorem nc_bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : p.NoCommit)
    (hf : ∀ a, (f a).NoCommit) : (p >>= f).NoCommit := NoCommit.bind hp hf

theorem nc_readScalar : (VerifierProgram.readScalar).NoCommit := fun _ ↦ trivial

theorem nc_sampleChallenge : (VerifierProgram.sampleChallenge).NoCommit := fun _ ↦ trivial

theorem nc_require (c : Prop) {_ : Decidable c} : (VerifierProgram.require c).NoCommit := by
  unfold VerifierProgram.require; split <;> trivial

theorem nc_sampleChallenges : ∀ n, (VerifierProgram.sampleChallenges n).NoCommit
  | 0 => trivial
  | n + 1 => nc_bind nc_sampleChallenge fun _ ↦ nc_bind (nc_sampleChallenges n) fun _ ↦ trivial

end Leaves

/-! ## The `E2` reads and samples -/

theorem nc_e2Read : e2Read.NoCommit := nc_bind nc_readScalar fun _ ↦ trivial

theorem nc_e2Reads : ∀ n, (e2Reads n).NoCommit
  | 0 => trivial
  | n + 1 => nc_bind nc_e2Read fun _ ↦ nc_bind (nc_e2Reads n) fun _ ↦ trivial

theorem nc_e2Sample (g : ℕ) : (e2Sample g).NoCommit :=
  nc_bind nc_readScalar fun _ ↦ nc_bind nc_sampleChallenge fun _ ↦ nc_bind (nc_require _) fun _ ↦ trivial

theorem nc_e2Samples (g : ℕ) : ∀ n, (e2Samples g n).NoCommit
  | 0 => trivial
  | n + 1 => nc_bind (nc_e2Sample g) fun _ ↦ nc_bind (nc_e2Samples g n) fun _ ↦ trivial

theorem nc_e2SampleN (g : ℕ) : ∀ n, (e2SampleN g n).NoCommit
  | 0 => trivial
  | n + 1 => nc_bind nc_readScalar fun _ ↦ nc_bind nc_sampleChallenge fun _ ↦ nc_bind (nc_require _) fun _ ↦
      nc_bind (nc_sampleChallenges n) fun _ ↦ trivial

theorem nc_roundPolyE2 (count : ℕ) (claim : E2) (mode : Option E2) : (roundPolyE2 count claim mode).NoCommit := by
  cases mode with
  | none => exact nc_bind nc_e2Read fun _ ↦ nc_bind (nc_e2Reads _) fun _ ↦ trivial
  | some r => exact nc_bind (nc_e2Reads _) fun _ ↦ trivial

theorem nc_sumcheckE2 (g : ℕ) (count : ℕ) : ∀ (modes : List (Option E2)) (claim : E2),
    (sumcheckE2 g claim count modes).NoCommit
  | [], _ => trivial
  | m :: ms, claim => nc_bind (nc_roundPolyE2 count claim m) fun _ ↦ nc_bind (nc_e2Sample g) fun _ ↦
      nc_bind (nc_sumcheckE2 g count ms _) fun _ ↦ trivial

/-! ## The mini-bus -/

theorem nc_gkrStepG (gy step : ℕ) (s : GkrStateG) : (gkrStepG gy step s).NoCommit :=
  nc_bind (nc_e2Sample _) fun _ ↦ nc_bind (nc_sumcheckE2 _ _ _ _) fun _ ↦ nc_bind (nc_e2Reads _) fun _ ↦
    nc_bind (nc_e2Reads _) fun _ ↦ nc_bind (nc_e2Reads _) fun _ ↦ nc_bind (nc_require _) fun _ ↦
      nc_bind (nc_e2SampleN _ _) fun _ ↦ trivial

theorem nc_gkrLayersG : ∀ (n : ℕ) (s : GkrStateG), (gkrLayersG n s).NoCommit
  | 0, _ => trivial
  | 1, s => nc_gkrStepG _ _ s
  | n + 2, s => by
    unfold gkrLayersG
    split
    · exact nc_bind (nc_gkrStepG _ _ s) fun s' ↦ nc_gkrLayersG (n + 1) s'
    · exact nc_bind (nc_gkrStepG _ _ s) fun s' ↦ nc_gkrLayersG n s'

theorem nc_lvmBusProgG (μ : ℕ) : (lvmBusProgG μ).NoCommit :=
  nc_bind (nc_e2SampleN _ _) fun _ ↦
    nc_bind (nc_bind nc_e2Read fun _ ↦ nc_bind nc_e2Read fun _ ↦ nc_bind (nc_gkrLayersG _ _) fun _ ↦ trivial)
      fun _ ↦ nc_bind (nc_require _) fun _ ↦ trivial

theorem nc_miniBusLProg6 (L : Lvm.M3.Lay) (tabs : List Lvm.M3.Tab) (μ : ℕ) :
    (miniBusLProg6 L tabs μ).NoCommit :=
  nc_bind (nc_lvmBusProgG μ) fun _ ↦ trivial

/-- **The mini-bus commits nothing** (`Stmt.noCommit`'s form). -/
theorem miniBusLProg6_noCommit (L : Lvm.M3.Lay) (tabs : List Lvm.M3.Tab) (μ : ℕ) :
    ∀ h₀ l, (miniBusLProg6 L tabs μ).Reach h₀ l → commits l = [] :=
  fun _ _ hl ↦ (nc_miniBusLProg6 L tabs μ).reach_commits hl

/-! ## The typed phases -/

theorem nc_zeroProgE : zeroProgE.NoCommit :=
  nc_bind (nc_e2Samples _ _) fun _ ↦ nc_bind (nc_sumcheckE2 _ _ _ _) fun _ ↦ nc_bind (nc_e2Reads _) fun _ ↦
    nc_bind (nc_require _) fun _ ↦ trivial

theorem nc_wireProgE (Ti : TInst6) (pw : ℕ → Lvm.FK) (v : List E2) : (wireProgE Ti pw v).NoCommit :=
  nc_bind (nc_e2Sample _) fun _ ↦ nc_bind (nc_sumcheckE2 _ _ _ _) fun _ ↦ nc_bind (nc_e2Reads _) fun _ ↦
    nc_bind (nc_e2Reads _) fun _ ↦ nc_bind (nc_require _) fun _ ↦ trivial

theorem nc_relayProgE (Ti : TInst6) (ry : List E2) (vS : E2) : (relayProgE Ti ry vS).NoCommit :=
  nc_bind (nc_sumcheckE2 _ _ _ _) fun _ ↦ nc_bind nc_e2Read fun _ ↦ nc_bind (nc_require _) fun _ ↦ trivial

theorem nc_accShape (n : ℕ) (P : List E2 → List E2 → E2 → Prop) (dec : ∀ a b c, Decidable (P a b c)) :
    (e2Samples gKappa selBitsE >>= fun κ ↦ e2Reads n >>= fun hs ↦ e2Sample gT >>= fun t ↦
      @VerifierProgram.require (P κ hs t) (dec κ hs t)).NoCommit :=
  nc_bind (nc_e2Samples _ _) fun _ ↦ nc_bind (nc_e2Reads n) fun _ ↦ nc_bind (nc_e2Sample _) fun _ ↦ nc_require _

theorem nc_accProgE (Q : Lvm.Loop.Program) (lay : Lvm.Typed.Lay) (yIn : E2) (a rxy vs : List E2) :
    (accProgE Q lay yIn a rxy vs).NoCommit :=
  nc_accShape (phiVarsE + 1) _ _

theorem nc_typedProgE (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → Lvm.FK) (acc : List E2 × E2) :
    (typedProgE Ti L pw acc).NoCommit := by
  unfold typedProgE
  exact nc_bind nc_zeroProgE fun _ ↦ nc_bind (nc_wireProgE _ _ _) fun _ ↦ nc_bind (nc_relayProgE _ _ _) fun _ ↦
    nc_bind (nc_accProgE _ _ _ _ _ _) fun _ ↦ nc_bind (nc_miniBusLProg6 _ _ _) fun _ ↦ trivial

/-- **The typed phases commit nothing** (`Stmt.noCommit`'s form): every run has no commitment, so the commit count
is the same before and after them. -/
theorem typedProgE_noCommit (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → Lvm.FK) (acc : List E2 × E2) :
    ∀ h₀ l, (typedProgE Ti L pw acc).Reach h₀ l → commits l = [] :=
  fun _ _ hl ↦ (nc_typedProgE Ti L pw acc).reach_commits hl

end Lvm6.Ty
