-- New for lvm6 K1 (CAND-decision.md): the tree and sponge programs make no commitment, so the history's
-- commitments are unchanged across them (`Stmt.noCommit`'s body: every run has `commits l = []`).
import Lvm6KProg
import LvmCertSFrame
import Lvm6StmtPhase

/-!
# The K1 programs commit nothing

Season 1's `VerifierProgram.NoCommit` (`LvmCertSFrame`, closed under `bind`) for every K1 program, and
the run form `∀ h₀ l, p.Reach h₀ l → commits l = []` (`NoCommit.reach_commits`), which is WP S's
`Stmt.noCommit p`:

* **`treeProg_noCommit κ`**, **`spongeCore6_noCommit P inst output`**, **`spCaller6_noCommit h`**.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (Shape)
open Lvm.E2V Lvm6.KPack
open VerifierProgram (NoCommit)

theorem nc_ret {α : Type} (a : α) : (pure a : VerifierProgram α).NoCommit := trivial

theorem nc_bind' {α γ : Type} {p : VerifierProgram α} {f : α → VerifierProgram γ} (hp : p.NoCommit)
    (hf : ∀ a, (f a).NoCommit) : (p >>= f).NoCommit := hp.bind hf

theorem nc_require (c : Prop) {inst : Decidable c} : (@VerifierProgram.require c inst).NoCommit := by
  unfold VerifierProgram.require; split <;> trivial

theorem nc_readScalar : VerifierProgram.readScalar.NoCommit := fun _ ↦ trivial

theorem nc_sampleChallenge : VerifierProgram.sampleChallenge.NoCommit := fun _ ↦ trivial

theorem nc_e2Read : e2Read.NoCommit := nc_bind' nc_readScalar fun _ ↦ nc_ret _

theorem nc_e2Reads : ∀ n, (e2Reads n).NoCommit
  | 0 => nc_ret _
  | n + 1 => by
    unfold e2Reads
    exact nc_bind' nc_e2Read fun _ ↦ nc_bind' (nc_e2Reads n) fun _ ↦ nc_ret _

theorem nc_e2Sample (g : ℕ) : (e2Sample g).NoCommit := by
  unfold e2Sample
  exact nc_bind' nc_readScalar fun _ ↦ nc_bind' nc_sampleChallenge fun _ ↦
    nc_bind' (nc_require _) fun _ ↦ nc_ret _

theorem nc_e2Samples (g : ℕ) : ∀ n, (e2Samples g n).NoCommit
  | 0 => nc_ret _
  | n + 1 => by
    unfold e2Samples
    exact nc_bind' (nc_e2Sample g) fun _ ↦ nc_bind' (nc_e2Samples g n) fun _ ↦ nc_ret _

theorem nc_kReads : ∀ n, (kReads n).NoCommit
  | 0 => nc_ret _
  | n + 1 => by
    unfold kReads kRead
    exact nc_bind' (nc_bind' nc_readScalar fun _ ↦ nc_ret _) fun _ ↦
      nc_bind' (nc_kReads n) fun _ ↦ nc_ret _

theorem nc_dDraws : ∀ n, (dDraws n).NoCommit
  | 0 => nc_ret _
  | n + 1 => by
    unfold dDraws dDraw
    exact nc_bind' (nc_bind' nc_sampleChallenge fun _ ↦ nc_ret _) fun _ ↦
      nc_bind' (nc_dDraws n) fun _ ↦ nc_ret _

theorem nc_gPoint (g n : ℕ) : (gPoint g n).NoCommit := by
  unfold gPoint
  exact nc_bind' (nc_e2Sample g) fun _ ↦ nc_bind' (nc_dDraws n) fun _ ↦ nc_ret _

theorem nc_roundPolyE2 (count : ℕ) (claim : E2) : ∀ mode, (roundPolyE2 count claim mode).NoCommit
  | none => by
    unfold roundPolyE2
    exact nc_bind' nc_e2Read fun _ ↦ nc_bind' (nc_e2Reads _) fun _ ↦ nc_ret _
  | some _ => by
    unfold roundPolyE2
    exact nc_bind' (nc_e2Reads _) fun _ ↦ nc_ret _

theorem nc_sumcheckE2 (g count : ℕ) : ∀ (modes : List (Option E2)) (claim : E2),
    (sumcheckE2 g claim count modes).NoCommit
  | [], _ => nc_ret _
  | mode :: modes, claim => by
    unfold sumcheckE2
    exact nc_bind' (nc_roundPolyE2 count claim mode) fun _ ↦ nc_bind' (nc_e2Sample g) fun _ ↦
      nc_bind' (nc_sumcheckE2 g count modes _) fun _ ↦ nc_ret _

theorem nc_packRoundsN (g : ℕ) : ∀ (rs : List E2) (value : E2), (packRoundsN g rs value).NoCommit
  | [], _ => nc_ret _
  | r :: rs, value => by
    unfold packRoundsN
    exact nc_bind' (nc_roundPolyE2 3 value (some r)) fun _ ↦ nc_bind' (nc_e2Sample g) fun _ ↦
      nc_bind' (nc_packRoundsN g rs _) fun _ ↦ nc_ret _

theorem nc_layer6 (logSteps step : ℕ) (claim : KClaim E2) : (layer6 logSteps step claim).NoCommit := by
  unfold layer6 layerTailE2N
  generalize productBits = a
  generalize keccakLocalBits = b
  generalize (3 : ℕ) = c
  exact nc_bind' (nc_e2Reads _) fun _ ↦ nc_bind' (nc_require _) fun _ ↦
    nc_bind' (nc_e2Sample _) fun _ ↦ nc_bind' (nc_packRoundsN _ _ _) fun _ ↦
      nc_bind' (nc_sumcheckE2 _ _ _ _) fun _ ↦ nc_bind' (nc_e2Reads _) fun _ ↦
        nc_bind' (nc_require _) fun _ ↦ nc_bind' (nc_e2Sample _) fun _ ↦ nc_ret _

theorem nc_layers6 (logSteps : ℕ) (steps : List ℕ) :
    ∀ claim : KClaim E2, (layers6 logSteps steps claim).NoCommit := by
  induction steps with
  | nil => intro claim; exact nc_ret _
  | cons step steps ih =>
    intro claim
    rw [layers6.eq_2]
    unfold layer6 layerTailE2N
    generalize productBits = a
    generalize keccakLocalBits = b
    generalize (3 : ℕ) = c
    refine nc_bind' ?_ ih
    exact nc_bind' (nc_e2Reads _) fun _ ↦ nc_bind' (nc_require _) fun _ ↦
      nc_bind' (nc_e2Sample _) fun _ ↦ nc_bind' (nc_packRoundsN _ _ _) fun _ ↦
        nc_bind' (nc_sumcheckE2 _ _ _ _) fun _ ↦ nc_bind' (nc_e2Reads _) fun _ ↦
          nc_bind' (nc_require _) fun _ ↦ nc_bind' (nc_e2Sample _) fun _ ↦ nc_ret _

theorem nc_kHead6 (P base : ℕ) (inst output : List E2) : (kHead6 P base inst output).NoCommit := by
  unfold kHead6
  generalize List.range 12 = st
  generalize (5 : ℕ) = a
  generalize (6 : ℕ) = b
  exact nc_bind' (nc_gPoint _ _) fun _ ↦ nc_bind' nc_e2Read fun _ ↦
    nc_bind' (nc_layers6 _ _ _) fun _ ↦ nc_bind' (nc_sumcheckE2 _ _ _ _) fun _ ↦
      nc_bind' nc_e2Read fun _ ↦ nc_bind' (nc_require _) fun _ ↦ nc_ret _

theorem nc_treeEnd6 (P : ℕ) (claim : KClaim E2) : (treeEnd6 P claim).NoCommit := by
  unfold treeEnd6
  generalize (64 : ℕ) = a
  generalize (11 : ℕ) = b
  exact nc_bind' (nc_sumcheckE2 _ _ _ _) fun _ ↦ nc_bind' (nc_e2Reads _) fun _ ↦
    nc_bind' (nc_require _) fun _ ↦ nc_ret _

theorem nc_spongeEnd6 (P : ℕ) (claim : KClaim E2) : (spongeEnd6 P claim).NoCommit := by
  unfold spongeEnd6
  generalize (64 : ℕ) = a
  generalize (10 : ℕ) = b
  exact nc_bind' (nc_sumcheckE2 _ _ _ _) fun _ ↦ nc_bind' (nc_e2Reads _) fun _ ↦
    nc_bind' (nc_require _) fun _ ↦ nc_ret _

theorem nc_treeProg (κ : ℕ) : (treeProg κ).NoCommit := by
  unfold treeProg
  generalize (4 : ℕ) = a
  generalize (8 : ℕ) = b
  generalize (21 : ℕ) = c
  exact nc_bind' (nc_kReads _) fun _ ↦ nc_bind' (nc_gPoint _ _) fun _ ↦
    nc_bind' (nc_e2Reads _) fun _ ↦ nc_bind' (nc_e2Sample _) fun _ ↦
      nc_bind' (nc_e2Reads _) fun _ ↦ nc_bind' (nc_kHead6 _ _ _ _) fun _ ↦
        nc_bind' (nc_treeEnd6 _ _) fun _ ↦ nc_ret _

theorem nc_spongeCore6 (P : ℕ) (inst output : List E2) : (spongeCore6 P inst output).NoCommit := by
  unfold spongeCore6
  exact nc_bind' (nc_kHead6 _ _ _ _) fun _ ↦ nc_bind' (nc_spongeEnd6 _ _) fun _ ↦ nc_ret _

theorem nc_spCaller6 (h : ℕ) : (spCaller6 h).NoCommit := by
  unfold spCaller6
  generalize (25 : ℕ) = a
  exact nc_bind' (nc_e2Samples _ _) fun _ ↦ nc_bind' (nc_e2Reads _) fun _ ↦
    nc_bind' (nc_spongeCore6 _ _ _) fun _ ↦ nc_ret _

/-! ## The run form (`Stmt.noCommit`) -/

/-- **The tree batch commits nothing.** -/
theorem treeProg_noCommit (κ : ℕ) : Stmt.noCommit (treeProg κ) :=
  fun _ _ hl ↦ (nc_treeProg κ).reach_commits hl

/-- **The sponge core commits nothing.** -/
theorem spongeCore6_noCommit (P : ℕ) (inst output : List E2) :
    Stmt.noCommit (spongeCore6 P inst output) :=
  fun _ _ hl ↦ (nc_spongeCore6 P inst output).reach_commits hl

/-- **The sponge caller commits nothing.** -/
theorem spCaller6_noCommit (h : ℕ) : Stmt.noCommit (spCaller6 h) :=
  fun _ _ hl ↦ (nc_spCaller6 h).reach_commits hl

end Lvm6.K
