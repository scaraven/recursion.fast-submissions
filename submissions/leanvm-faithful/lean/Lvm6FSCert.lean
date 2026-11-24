-- lvm6 F1: T5 of BLUEPRINT §5, the v6 instance of season 1's KCert ⇒ KState ⇒ KS compiler
-- (`kcertOfInv`, `kstate_of_kcert`, `εFS_le_of`), and the ledger `εFS ≤ 2^-128`.
import Lvm6FSScheme
import Lvm6FSGroup
import LvmInvCert

/-!
# `kcert6`, `εFS_kcert6`

The S branch's knowledge certificate is season 1's form (`LvmCertSKJ.kcertSJ`): **no doom**
(`ε = 0`), luck "the program's invariant broke, or the extractor's luck" at
`εB = εI + εL = 7·2^-131 + 2^-132`, built by `kcertOfInv` from

* `SI x`: a whole-program specification of `P x` from the empty history, every group `≤ εI` (doom
  created at the commitments, PARAM's ledger: each group's `L₀ · errG g c ≤ εI`, `errG_le_εI`), lead
  `L ≤ εI`, with postcondition "an accepting return satisfies `Ext x h`" (T2–T4' assembled);
* no language-level proof of work (`hng`: for WP ASM's composed `prog6`, `prog6_noGrind`; grinding
  is the nonce lane and the draw's `pw` test);
* `X : Ext6 …`: the extractor's luck `BL` (its group bound `≤ 2^-132`, `εL ≤ logCap·2^-256`) and the
  extraction `ext` with `extract` (X2's obligations).

**`εFS_kcert6`**: `εFS = 0 + (εI + εL) + badCount/2^256 ≤ 2^-128` (`Params.ledger_total`).
**`ks6`**: the contract's knowledge soundness of the compiled verifier, the probability of an
accepted, unextracted output at most `(Q + qV) · 2^-128` with `qV = 16384` (`KState.ks`).
**`sound6`**: the field `sound` of WP S's `Open6` (T5 with T8's `ExtEq6`) at `P18`, from the
per-key specifications, extractor obligations and `ExtEq6` of `kcert6`.

The scheme is WP S's `schemeOf prog sh vk` (`Lvm6Stmt`: V1's `V.schemeP` of the program `prog`; WP ASM
takes `prog := prog6`, the composed phase programs).
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.T
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open scoped NNReal ENNReal

/-! ## No proof of work in the language -/

section NoGrind

variable {α : Type}

/-- A reachable history of a program with no proof of work has no grind event (season 1's
`LvmCertSNo`, parked). -/
theorem reach_noGrind {p : VerifierProgram α} (hp : p.NoGrind) {h : List Ev}
    (hr : p.Reachable h) : ∀ e ∈ h, ∀ b, e ≠ Ev.grind b := by
  induction hr with
  | nil => simp
  | read x _ _ ih | sample x _ _ ih =>
    intro e he b; rcases List.mem_append.1 he with he | he
    · exact ih e he b
    · simp at he; subst he; simp
  | query _ _ _ ih =>
    intro e he b; rcases List.mem_append.1 he with he | he
    · exact ih e he b
    · simp at he; subst he; simp
  | commit word _ _ _ ih =>
    intro e he b; rcases List.mem_append.1 he with he | he
    · exact ih e he b
    · simp at he; subst he; simp
  | grind _ ha _ => exact ((VerifierProgram.NoGrind.after hp ha) : False).elim

/-- **`hng`**: a reachable history of a program with no proof of work ends in no grind. -/
theorem reach_grindBits {p : VerifierProgram α} (hp : p.NoGrind) {h : List Ev}
    (hr : p.Reachable h) : grindBits h = 0 := by
  have hn := reach_noGrind hp hr
  unfold grindBits
  split
  · rename_i b hb
    exact absurd rfl (hn _ (List.mem_of_getLast? hb) b)
  · rfl

end NoGrind

/-! ## The certificate -/

/-- `εI = 7·2^-131`: every group's escape (PARAM). -/
noncomputable abbrev εI6 : ℝ≥0 := 7 * (2 : ℝ≥0)⁻¹ ^ 131

/-- `εL = 2^-132`: the extractor's luck (PARAM: `logCap·2^-256 = 2^-160`). -/
noncomputable abbrev εL6 : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 132

/-- **The extractor's obligations** for a scheme `S`, relation `R` and the programs' postcondition
`Ext`: the luck `BL` and its rules (prover moves keep it out; a group escapes into it with
probability `≤ 2^-132`), and the extraction from an accepting history outside luck. -/
structure Ext6 (S : Scheme) (R : Digest → Wit → Prop) (Ext : S.Stmt → List Ev → Prop) where
  BL : S.Stmt → List Ev → Prop
  BL_nil : ∀ x, ¬ BL x []
  BL_read : ∀ {x h k} (y : E), (S.P x).Reachable h → (S.P x).after h = some (.read k) →
    ¬ BL x h → ¬ BL x (h ++ [Ev.read y])
  BL_commit : ∀ {x h ht w k} (word : LeanVM.Protocol.Compile.Word), (S.P x).Reachable h →
    (S.P x).after h = some (.commit ht w k) → WellShaped w word → ¬ BL x h →
    ¬ BL x (h ++ [Ev.commit ht w word])
  BL_group : ∀ {x h p}, (S.P x).Reachable h → Boundary h → (S.P x).after h = some p →
    ((∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k)) → ¬ BL x h →
    esc (fun h' => ¬ BL x h') h p ≤ (εL6 : ℝ≥0∞)
  ext : Digest → S.Stmt → List Ev → Wit
  extract : ∀ {c x h}, S.ok c x = true → (S.P x).Reachable h →
    (S.P x).after h = some (.ret true) → Ext x h → ¬ BL x h →
    (∀ h', h' <+: h → Boundary h' → ¬ BL x h') → R c (ext c x h)

theorem εI6_add_εL6_lt_one : εI6 + εL6 < 1 := by
  rw [← NNReal.coe_lt_coe]; push_cast; norm_num

variable {R : Digest → Wit → Prop} {Ext : List UInt8 → List Ev → Prop} {L : ℝ≥0∞}

/-- **T5: the knowledge certificate of the v6 scheme** (`kcertOfInv` on WP S's `schemeOf prog sh vk`;
for WP ASM's `prog6`, `hng` is `prog6_noGrind`). -/
noncomputable def kcert6 (prog : Shape → Digest → List UInt8 → VerifierProgram Bool) (sh : Shape)
    (vk : Digest)
    (SI : ∀ x, Spec ((schemeOf prog sh vk).P x) (fun h ↦ h = []) (fun b h ↦ b = true → Ext x h)
      (εI6 : ℝ≥0∞) L 0)
    (hL : L ≤ εI6) (hng : ∀ x, (prog sh vk x).NoGrind) (X : Ext6 (schemeOf prog sh vk) R Ext) :
    KCert (schemeOf prog sh vk) R :=
  kcertOfInv (S := schemeOf prog sh vk) (εI := εI6) (εL := εL6) SI hL
    (fun x _ hr ↦ reach_grindBits (hng x) hr) X.BL X.BL_nil X.BL_read X.BL_commit
    X.BL_group εI6_add_εL6_lt_one X.ext X.extract

section
variable {prog : Shape → Digest → List UInt8 → VerifierProgram Bool} {sh : Shape} {vk : Digest}
  {SI : ∀ x, Spec ((schemeOf prog sh vk).P x) (fun h ↦ h = []) (fun b h ↦ b = true → Ext x h)
    (εI6 : ℝ≥0∞) L 0}
  {hL : L ≤ εI6} {hng : ∀ x, (prog sh vk x).NoGrind} {X : Ext6 (schemeOf prog sh vk) R Ext}

/-- **The ledger**: `εFS (kcert6 …) = 0 + (7·2^-131 + 2^-132) + badCount/2^256 ≤ 2^-128`. -/
theorem εFS_kcert6 : Scheme.εFS (kcert6 prog sh vk SI hL hng X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  Scheme.εFS_le_of _ (by
    show (0 : ℝ≥0) + (εI6 + εL6) + (2 : ℝ≥0)⁻¹ ^ 139 ≤ (2 : ℝ≥0)⁻¹ ^ 128
    exact Params.ledger_total)

/-- **Knowledge soundness of the compiled v6 verifier** in the contract's form: with `qV = 16384`
queries, an adversary of `Q` queries outputs an accepted, unextracted proof with probability at most
`(Q + qV) · 2^-128`. -/
theorem ks6 (hq : ∀ H c π, (((schemeOf prog sh vk).V c π).queries H).length ≤ Params.qV) :
    KS R (schemeOf prog sh vk).V ((schemeOf prog sh vk).Ex (kcert6 prog sh vk SI hL hng X).ext)
      ((2 : ℝ≥0)⁻¹ ^ 128) Params.qV :=
  ((Scheme.kstate_of_kcert _).mono εFS_kcert6).ks hq

end

/-- **`Open6.sound` from `kcert6`** (T5 with T8): per key, the whole-program specification at `εI`,
the extractor's obligations, and `ExtEq6` against `kcert6`'s ideal extractor give a certificate with
`εFS ≤ 2^-128` and `ExtEq6`. -/
theorem sound6 {VS : Shape → SProg} {prog : Shape → Digest → List UInt8 → VerifierProgram Bool}
    {EX : Digest → RecursionFast.Proof → Log → Option Wit}
    {Ext : Digest → List UInt8 → List Ev → Prop}
    (SI : ∀ vk x, Spec ((schemeOf prog P18 vk).P x) (fun h ↦ h = [])
      (fun b h ↦ b = true → Ext vk x h) (εI6 : ℝ≥0∞) L 0)
    (hL : L ≤ εI6) (hng : ∀ vk x, (prog P18 vk x).NoGrind)
    (X : ∀ vk, Ext6 (schemeOf prog P18 vk) (Rel (accV (VS P18) vk)) (Ext vk))
    (hE : ∀ vk, ExtEq6 EX (kcert6 prog P18 vk (SI vk) hL (hng vk) (X vk))) :
    ∀ vk, ∃ K : KCert (schemeOf prog P18 vk) (Rel (accV (VS P18) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 EX K :=
  fun vk ↦ ⟨_, εFS_kcert6, hE vk⟩

/-- **`Params.qS` is the schedule's count** (`FORMAT6.md` v2.4: 4,349). -/
theorem qS_eq_params : qSOf P18 = Params.qS := by decide +kernel

/-- **`qV` covers `qS`**: `qV = 16384` (= `qVlvm`, `claim.json`) is within the contract's `2^16` and at
least `1.5 · qSOf P18` (PARAM's `qV_ok` over the schedule's count). -/
theorem qV_ok_P18 : Params.qV ≤ 2 ^ 16 ∧ qSOf P18 * 3 / 2 ≤ Params.qV := by decide +kernel

end Lvm6
