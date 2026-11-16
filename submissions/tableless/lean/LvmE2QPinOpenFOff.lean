/- `LvmE2QPinOpenFOff` (GOLF2 off-path move, group 9 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmDecide, LvmVerifierS, LvmCertS, LvmCertSRes, LvmE2QPinOpenF,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmDecide
import LvmVerifierS
import LvmCertS
import LvmCertSRes
import LvmE2QPinOpenF
import LvmInvCertOff
import LvmChainTablePad
import LvmJBMutual
import LvmMlListLemmas
import LvmSpecRulesCert
import LvmTensorSwitch
import LvmVerifierF

-- ===== from `LvmDecide` =====

section
set_option autoImplicit false
namespace Lvm
open DM

/-- `CH`'s output lanes 0–3 on `Y` (slots `ySlot + l`) at the instance point, and the boundary claims
`in_0 = Pad43(s)` at row 0 and `Y(n − 1) = h` (BLUEPRINT §4.1; A1: `n ≥ 1`). -/
def chFixedClaims (p : Params) (blk : Placement) (ySlot : Nat) (r v : List FE) (pub : Pub) :
    List BlockClaim :=
  let slot (l : Nat) := selectorPoint l slotLog
  ((List.range 4).map fun l => BlockClaim.point blk (r ++ slot (ySlot + l)) (v.getD l 0)) ++
  ((pad43 pub.s).zipIdx.map fun (w, l) =>
    BlockClaim.point blk (selectorPoint 0 p.logN ++ slot l) (FE.ofK w)) ++
  (pub.h.zipIdx.map fun (w, l) =>
    BlockClaim.point blk (selectorPoint (pub.n - 1) p.logN ++ slot (ySlot + l)) (FE.ofK w))

end Lvm
end

section
set_option autoImplicit false
namespace Lvm
open DM

/-- **The split** (BLUEPRINT §12.4): `F = decideCore ∧ AccOk (accOutOf Σ)`. -/
theorem decideF_eq (p : Params) (m : M3) (vk c : Vector UInt8 32) (sig : ByteArray) :
    decideF p m vk c sig =
      (decideCore p m vk c sig && AccOk p m (pubOf vk c sig) (accOutOf p m vk c sig)) := by
  unfold decideF decideCore accOutOf
  generalize (decideProg p m vk c).runOn sig = r
  cases r; rfl

end Lvm
end

-- ===== from `LvmVerifierS` =====

section
set_option autoImplicit false
namespace Lvm
open RecursionFast

/-- A rejected header asks no query. -/
theorem VS_reject {p : Params} {m : M3} {vk c : Digest} {π : Proof} (h : parseOk p vk c π = false) :
    VS p m vk c π = .ret false := by
  simp [VS, h]

end Lvm
end

-- ===== from `LvmCertS` =====

section
section
namespace Lvm.FS
open LeanVM.Parameters RecursionFast
open LeanVM.Protocol.Compile hiding Proof  -- INT-1: WP-2's DSL also has a `Proof`; here it is `RecursionFast.Proof`
open scoped NNReal
namespace Scheme
variable {S : Scheme} {R : Digest → Wit → Prop}

/-- **The Fiat–Shamir compiler theorem** (the contract's knowledge soundness). -/
theorem ks_of_kcert (K : KCert S R) {qV : ℕ} (hq : ∀ H c π, ((S.V c π).queries H).length ≤ qV) :
    KS R S.V (S.Ex K.ext) (εFS K) qV :=
  (kstate_of_kcert K).ks hq

end Scheme
end Lvm.FS
end
end

section
section
namespace Lvm.FS
open LeanVM.Parameters RecursionFast
open LeanVM.Protocol.Compile hiding Proof  -- INT-1: WP-2's DSL also has a `Proof`; here it is `RecursionFast.Proof`
open scoped NNReal
namespace Scheme
variable {S : Scheme} {R : Digest → Wit → Prop}

/-- **The ε budget**: groups at `2^-129` and luck at `2^-130` fit the contract's cap `2^-128`
with the hash term. -/
theorem εFS_le (K : KCert S R) (hε : K.ε ≤ (2 : ℝ≥0)⁻¹ ^ 129) (hεB : K.εB ≤ (2 : ℝ≥0)⁻¹ ^ 130) :
    εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 := by
  unfold εFS
  refine (add_le_add (add_le_add hε hεB) badCount_div_le).trans ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  norm_num

end Scheme
end Lvm.FS
end
end

section
section
namespace Lvm.FS
open LeanVM.Parameters RecursionFast
open LeanVM.Protocol.Compile hiding Proof  -- INT-1: WP-2's DSL also has a `Proof`; here it is `RecursionFast.Proof`
open scoped NNReal

/-- An extractor that agrees with `E` on accepted proofs over logs of potential below `1`. -/
def KState.congrE {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} (k : KState R V E ε)
    (E' : Digest → Proof → Log → Option Wit)
    (h : ∀ L c π, L.length ≤ logCap → k.μ L < 1 → (V c π).runLog L = some true →
      E' c π L = E c π L) : KState R V E' ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L c π hl hμ hacc := by rw [h L c π hl hμ hacc]; exact k.final L c π hl hμ hacc

/-- A verifier whose acceptance on a log implies `V`'s. -/
def KState.congrV {R : Digest → Wit → Prop} {V V' : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} (k : KState R V E ε)
    (h : ∀ L c π, (V' c π).runLog L = some true → (V c π).runLog L = some true) :
    KState R V' E ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L c π hl hμ hacc := k.final L c π hl hμ (h L c π hacc)

end Lvm.FS
end
end

section
section
namespace Lvm.T
open RecursionFast
open RecursionFast.WitnessSending (encode decode encodeF)
open scoped NNReal

/-- (−) **The bounds are not vacuous**: a declared query bound below `qVlvm` fails them. -/
theorem not_boundsOK_qV (VS : SProg) (E : Digest → Proof → Log → Option Wit) (ext : XProg) :
    ¬ BoundsOK ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, 0, 16383,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS E ext) := fun h => by
  have h1 := h.2.2.1
  simp only [subWith, qVlvm] at h1
  omega

end Lvm.T
end
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open RecursionFast.WitnessSending (encode)
open scoped NNReal ENNReal

/-- **The doom root**: no candidate pair of the committed words is a witness of the M3 instance. -/
def CommitDoomS (Good : GoodRel) (x : List UInt8) (h : List Ev) : Prop :=
  ∀ p ∈ candPairs h, ¬ Good x p.1 p.2

/-- The doom root is WP-2/WP-8's `Doomed` over the candidate pairs (so the phase specs, generic in
the candidate type `β` and the carried predicate, compose with it). -/
theorem commitDoomS_eq (Good : GoodRel) (x : List UInt8) :
    CommitDoomS Good x = LeanVM.Protocol.EndToEnd.Front.Doomed candPairs (fun p ↦ Good x p.1 p.2) := rfl

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open RecursionFast.WitnessSending (encode)
open scoped NNReal ENNReal

/-- **The middle phases' postcondition** (in doom): every candidate pair fails a claim on `C_rec`
or on `C_main`, and the roots' shape is kept; the returned claims are multiaffine and at most
`2^63` per commitment (the WHIR specs' side conditions, `retInv` facts of the phases). -/
def OpenPost (cl : OpenClaims) (h : List Ev) : Prop :=
  (∀ p ∈ candPairs h, (∃ c ∈ cl.1, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c p.2) ∨
    (∃ c ∈ cl.2, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c p.1)) ∧ RootShape h ∧
  (∀ c ∈ cl.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ cl.2, IsMultiaffine CMain.nu20 c.1) ∧
  cl.1.length ≤ 2 ^ 63 ∧ cl.2.length ≤ 2 ^ 40

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open RecursionFast.WitnessSending (encode)
open scoped NNReal ENNReal

/-- Candidates are antitone in the threshold. -/
theorem candidates_anti {μ R A A' : ℕ} {W : LeanVM.Protocol.Compile.Word} (hA : A ≤ A')
    {q : LeanVM.Protocol.Column μ} (hq : q ∈ Candidates μ R A' W) : q ∈ Candidates μ R A W :=
  let ⟨S, hS, hag⟩ := hq; ⟨S, hA.trans hS, hag⟩

/-- J2′'s threshold is below the unique-decoding one (`16,410 ≤ 20,480`): every UD candidate is one. -/
theorem thrRec_le_ud : thrRec ≤ (codesRec20 0).thr := by
  show (codesRec20Jp 0).thr ≤ (codesRec20 0).thr
  decide

/-- **The openings' precondition splits** (no unique decoding needed): if some candidate of
`C_rec` meets all its claims, every candidate of `C_main` fails one of its claims (`MainPre`). -/
theorem openPost_split {cl : OpenClaims} {h : List Ev} (hp : OpenPost cl h) :
    StackedPreUd cfgRec20G (codesRec20 0) cl.1 (commits h) ∨ MainPre cl.2 (commits h) := by
  obtain ⟨hpairs, ⟨Wm, Wr, hc, hWm, hWr⟩, -⟩ := hp
  by_cases hr : ∀ q ∈ Candidates 19 2 thrRec (wordOf (commits h) 1),
      ∃ c ∈ cl.1, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c q
  · left
    exact ⟨by decide, by rw [hc]; rfl, ⟨Wr, by rw [hc]; rfl, hWr⟩,
      fun q hq ↦ hr q (candidates_anti thrRec_le_ud hq)⟩
  · right
    push Not at hr
    obtain ⟨qr, hqr, hall⟩ := hr
    refine ⟨by rw [hc]; rfl, ⟨Wm, by rw [hc]; rfl, hWm⟩, fun qm hqm => ?_⟩
    rcases hpairs (qm, qr) ⟨hqm, hqr⟩ with ⟨c, hc1, hn⟩ | h2
    · exact absurd (hall c hc1) hn
    · exact h2

/-- **Obligation `MidSpec`** (WP-8/9/10/11b phases, composed by WP-14): the middle phases, from the
doom root with the roots' shape, end in `OpenPost`, every group's escape at most `εm`, lead `Lm`,
for every follower's allowance `T ≤ εm`. -/
def MidSpec (mid : List UInt8 → VerifierProgram OpenClaims) (Good : GoodRel) (εm Lm : ℝ≥0∞) : Prop :=
  ∀ x (T : ℝ≥0∞), T ≤ εm →
    Nonempty (Spec (mid x) (fun h ↦ CommitDoomS Good x h ∧ RootShape h) OpenPost εm Lm T)

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open RecursionFast.WitnessSending (encode)
open scoped NNReal ENNReal

/-- Luck and extraction for a scheme, given the doom predicate `D` of every statement's program
(`KCert`'s fields other than the doom certificate). -/
structure LuckExt (S : Scheme) (R : Digest → Wit → Prop) (D : S.Stmt → List Ev → Prop) where
  /-- Luck. -/
  B : S.Stmt → List Ev → Prop
  /-- The luck bound of a group. -/
  εB : ℝ≥0
  εB_lt_one : εB < 1
  B_nil : ∀ x, ¬ B x []
  B_read : ∀ {x h k} (y : E), (S.P x).Reachable h → (S.P x).after h = some (.read k) → ¬ B x h →
    ¬ B x (h ++ [Ev.read y])
  B_commit : ∀ {x h ht w k} (word : LeanVM.Protocol.Compile.Word), (S.P x).Reachable h →
    (S.P x).after h = some (.commit ht w k) → WellShaped w word → ¬ B x h →
    ¬ B x (h ++ [Ev.commit ht w word])
  B_group : ∀ {x h p}, (S.P x).Reachable h → Boundary h → (S.P x).after h = some p →
    ((∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k)) → ¬ B x h →
    esc (fun h' => ¬ B x h') h p ≤ εB
  /-- The extraction map. -/
  ext : Digest → S.Stmt → List Ev → Wit
  /-- Extraction from an accepting history, not lucky, outside doom at every boundary. -/
  extract : ∀ {c x h}, S.ok c x = true → (S.P x).Reachable h →
    (S.P x).after h = some (.ret true) → ¬ B x h → (∀ h', h' <+: h → Boundary h' → ¬ B x h') →
    (∀ h', h' <+: h → Boundary h' → ¬ D x h') → R c (ext c x h)

/-- **A knowledge certificate from a whole-program specification** (leanVM `Spec.toCert`, as
leanVM's `leanVmCert`: the specification starts from no doom, `Pre = False`, and the doom is created
by the root commitments): doom and escape bounds are the specification's; a program with no proof
of work has every escape bound at most `εm`. -/
noncomputable def kcertOfSpec {S : Scheme} {R : Digest → Wit → Prop} {εm : ℝ≥0} {L : ℝ≥0∞}
    (SP : ∀ x, Spec (S.P x) (fun _ ↦ False) (fun b _ ↦ b = false) (εm : ℝ≥0∞) L 0)
    (hstart : ∀ x, (SP x).D [] [] → (SP x).V [] [] ≤ εm) (hε1 : εm < 1)
    (hng : ∀ x h, (S.P x).Reachable h → grindBits h = 0)
    (LE : LuckExt S R fun x ↦ (SP x).D []) : KCert S R where
  cert x := (SP x).toCert
  ε := εm
  cert_ε x h hr _ _ := by
    have := (SP x).toCert_bound (hstart x) h
    rwa [hng x h hr, pow_zero, one_mul] at this
  ε_lt_one := hε1
  B := LE.B
  εB := LE.εB
  εB_lt_one := LE.εB_lt_one
  B_nil := LE.B_nil
  B_read := LE.B_read
  B_commit := LE.B_commit
  B_group := LE.B_group
  ext := LE.ext
  extract := LE.extract

/-- The certificate's doom is the specification's from the empty history. -/
theorem kcertOfSpec_D {S : Scheme} {R : Digest → Wit → Prop} {εm : ℝ≥0} {L : ℝ≥0∞}
    (SP : ∀ x, Spec (S.P x) (fun _ ↦ False) (fun b _ ↦ b = false) (εm : ℝ≥0∞) L 0)
    (hstart : ∀ x, (SP x).D [] [] → (SP x).V [] [] ≤ εm) (hε1 : εm < 1)
    (hng : ∀ x h, (S.P x).Reachable h → grindBits h = 0)
    (LE : LuckExt S R fun x ↦ (SP x).D []) (x : S.Stmt) :
    ((kcertOfSpec SP hstart hε1 hng LE).cert x).D = (SP x).D [] := rfl

/-- The certificate's error budget: groups at `2^-129` and luck at `2^-130` give `εFS ≤ 2^-128`
(WP-5 `εFS_le`). -/
theorem εFS_kcertOfSpec {S : Scheme} {R : Digest → Wit → Prop} {εm : ℝ≥0} {L : ℝ≥0∞}
    (SP : ∀ x, Spec (S.P x) (fun _ ↦ False) (fun b _ ↦ b = false) (εm : ℝ≥0∞) L 0)
    (hstart : ∀ x, (SP x).D [] [] → (SP x).V [] [] ≤ εm) (hε1 : εm < 1)
    (hng : ∀ x h, (S.P x).Reachable h → grindBits h = 0)
    (LE : LuckExt S R fun x ↦ (SP x).D []) (hεm : εm ≤ 7 * (2 : ℝ≥0)⁻¹ ^ 131)
    (hεB : LE.εB ≤ (2 : ℝ≥0)⁻¹ ^ 132) :
    Scheme.εFS (kcertOfSpec SP hstart hε1 hng LE) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  -- lvm2 JB-VQP: the exact budget `7·2^-131 + 2^-132 + 2^-139 ≤ 2^-128`
  Scheme.εFS_le_of _ ((add_le_add (add_le_add hεm hεB) le_rfl).trans (by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num))

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open RecursionFast.WitnessSending (encode)
open scoped NNReal ENNReal

/-- (−) The header parser refuses a proof that does not start with `'S' 0^7`. -/
theorem hdrS_ctl : hdrS ⟨#[0x57]⟩ = none := by
  simp [hdrS, piSz, sPrefix]

/-- (+) `P_S` starts with the two root commitments (`C_main`: `2^19` leaves (lvm2 S2) of `64` words; `C_rec`:
`2^15` leaves of `64` words). -/
theorem PSWith_roots (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    ∃ k, PSWith mid x = .commit 19 64 (.commit 15 64 k) := ⟨_, rfl⟩

end Lvm.ASM
end

-- ===== from `LvmCertSRes` =====

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound
open scoped ENNReal
variable {α β : Type}
section Tail
variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P : LevelCode}
  {level : LeanVM.Parameters.Whir.Level} {pre : ℕ} {εmax : ℝ≥0∞}

/-- **The residual's doom**: at the boundary after the residual's last scalar, `ResC` is doom. -/
theorem resTailSpec_D (H : FinHyp μ ℓ₀ per c₀ n₀ w P level pre) (hg : g ≤ 192)
    (hQlt : eQueryFinal P level.queries < 1)
    (hεQ : (2 : ℝ≥0∞)⁻¹ ^ g * eQueryFinal P level.queries ≤ εmax)
    (hεT : eTail ≤ εmax) (r : WhirStateT × List E) {h₀ l : List Ev} {res : List E}
    (ha : (readScalars (2 ^ (μ - r.1.folds.length))).after l = some (.ret res))
    (hR : ResC μ ℓ₀ w i P level.fold pre r res (viewC c₀ n₀ (commits (h₀ ++ l)))) :
    (resTailSpec (dir := dir) (i := i) H hg hQlt hεQ hεT r).D h₀ l := by
  rw [resTailSpec, Spec.congr_D, bind_D_ret _ _ ha]
  exact ⟨⟨res, ha, hR⟩, ((grindPreInv (fun cs ↦ ResC μ ℓ₀ w i P level.fold pre r res
    (viewC c₀ n₀ cs)) g hεQ).bind fun _ ↦ finQuerySpec (dir := dir) H hg hQlt hεT r res).start_D _ hR⟩

end Tail
end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound
open scoped ENNReal
variable {α β : Type}
section Rec2
variable (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
  (hc : cfg.levels = [level, next]) (P₁ : LevelCode) (cl : List LeanVM.Protocol.Verifier.StackClaim)
  {εmax : ℝ≥0∞}
  (H : ∀ ρ, FinHyp cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ (batW cl ρ) P₁ next level.fold)
  (hg : cfg.grind ≤ 192) (hQlt : eQueryFinal P₁ next.queries < 1)
  (hεQ : (2 : ℝ≥0∞)⁻¹ ^ cfg.grind * eQueryFinal P₁ next.queries ≤ εmax)
  (hεT : eTail ≤ εmax)

/-- The doom of `recRes2Spec` after the final residual: `resTailSpec`'s. -/
theorem recRes2Spec_D {h₀ lq lf lc lgp lg lhq lf1 lres : List Ev} {ρ : E} {quad hq : List E}
    {r r₁ : WhirStateT × List E} {g : List ℕ × E × List (List K)}
    (hq' : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl ρ) none).after lq =
      some (.ret quad))
    (hf : (foldRoundsT level.fold ⟨batT cl ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (cfg.μ - r.1.folds.length - next.fold + next.logInvRate)
      (3 * 2 ^ next.fold)).after lc = some (.ret ()))
    (hgp : (grindPre cfg.grind).after lgp = some (.ret ()))
    (hgq : (queryFragG cfg.grind cfg.per (cfg.μ - r.1.folds.length + level.logInvRate)
      level.queries (cidx cfg.c₀ cfg.n₀ 0)).after lg = some (.ret g))
    (hh : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after
      lhq = some (.ret hq))
    (hf1 : (foldRoundsT next.fold (glueLv cfg.μ 0 r g.1 g.2.1 g.2.2 hq) []).after lf1 =
      some (.ret r₁))
    (hne : lres ≠ []) :
    (recRes2Spec cfg level next hc P₁ cl H hg hQlt hεQ hεT).D h₀
        ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lgp ++ (lg ++ (lhq ++ (lf1 ++ lres)))))))) ↔
      (resTailSpec (dir := cfg.direct) (i := 0 + 1) (H ρ) hg hQlt hεQ hεT r₁).D
        (h₀ ++ [Ev.sample ρ] ++ lq ++ lf ++ lc ++ lgp ++ lg ++ lhq ++ lf1) lres := by
  rw [recRes2Spec, Spec.congr_D, bind_D_after _ _ (rfl : sampleChallenge.after [Ev.sample ρ] = _)
    (by simp [hne]), bind_D_after _ _ hq' (by simp [hne]), bind_D_after _ _ hf (by simp [hne]),
    Spec.congr_D, bind_D_after _ _ hcm (by simp [hne]), bind_D_after _ _ hgp (by simp [hne]),
    bind_D_after _ _ hgq (by simp [hne]), bind_D_after _ _ hh (by simp [hne]),
    bind_D_after _ _ hf1 hne]

end Rec2
end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound
open scoped ENNReal
variable {α β : Type}

/-- Where `p` reaches a node that is not a return, it has not returned. -/
theorem retSplit_eq_none_of_after {p q : VerifierProgram α} {l : List Ev} (h : p.after l = some q)
    (hq : ∀ a, q ≠ .ret a) : p.retSplit l = none := by
  rcases hs : p.retSplit l with _ | ⟨a, l₁, l₂⟩
  · rfl
  · obtain ⟨rfl, h1⟩ := retSplit_eq_some_iff.1 hs
    rw [after_append, h1] at h
    cases l₂ with
    | nil => simp [after] at h; exact absurd h.symm (hq a)
    | cons e es => cases e <;> simp [after] at h

/-- Inside `p` (at a node that is not a return), the doom of `S.bind F` is `S`'s. -/
theorem bind_D_inside {p : VerifierProgram α} {f : α → VerifierProgram β} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {Q : β → List Ev → Prop} {εmax Lp Lf T : ℝ≥0∞}
    (S : Spec p Pre Post εmax Lp Lf) (F : ∀ a, Spec (f a) (Post a) Q εmax Lf T)
    {h₀ l : List Ev} {q : VerifierProgram α} (ha : p.after l = some q) (hq : ∀ a, q ≠ .ret a) :
    (S.bind F).D h₀ l ↔ S.D h₀ l := by
  rw [Spec.bind_D]
  exact Spec.bindD_none (retSplit_eq_none_of_after ha hq)

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound
open scoped ENNReal
variable {α β : Type}

/-- The positions' first challenge: a query group with at least one position (after the moves
before the proof of work, PI-GRIND) starts with a challenge. -/
theorem queryFrag_bind_ne_ret (gb per d t c : ℕ) (ht : t ≠ 0)
    (g : List ℕ × E × List (List K) → VerifierProgram Unit) (a : Unit) :
    ((grindPre gb).bind fun _ ↦ (queryFragG gb per d t c).bind g) ≠ .ret a := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
  by_cases hg : gb = 0
  · subst hg
    simp [grindPre, powCheck, queryFragG, queryFrag, samplePositions, samplePositionsAux,
      VerifierProgram.bind, VerifierProgram.sampleChallenge]
  · simp [grindPre, hg, VerifierProgram.bind, VerifierProgram.sampleChallenge]

/-- **A two-level stacked opening, after its level-1 commitment**, is before its level-0 query
group (the moves before the proof of work, then the group). -/
theorem after_stacked_two_commit (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
    (hc : cfg.levels = [level, next]) (cl : List LeanVM.Protocol.Verifier.StackClaim)
    {lq lf lc : List Ev} {ρ : E} {quad : List E} {r : WhirStateT × List E}
    (hq : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl ρ) none).after lq = some (.ret quad))
    (hf : (foldRoundsT level.fold ⟨batT cl ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (cfg.μ - r.1.folds.length - next.fold + next.logInvRate)
      (3 * 2 ^ next.fold)).after lc = some (.ret ())) :
    ∃ g', (verifyStackedUd cfg cl).after ([Ev.sample ρ] ++ (lq ++ (lf ++ lc))) =
      some ((grindPre cfg.grind).bind fun _ ↦
        (queryFragG cfg.grind cfg.per (cfg.μ - r.1.folds.length + level.logInvRate) level.queries
          (cidx cfg.c₀ cfg.n₀ 0)).bind g') := by
  refine ⟨fun g ↦ (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2)
    none).bind fun hq ↦ (foldRoundsT next.fold (glueLv cfg.μ 0 r g.1 g.2.1 g.2.2 hq) []).bind
      fun r₁ ↦ finTail cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ cfg.grind cfg.direct (batW cl ρ)
        (0 + 1) next r₁, ?_⟩
  rw [stacked_two_eq cfg level next hc cl,
    after_bind_append _ (rfl : sampleChallenge.after [Ev.sample ρ] = _), after_bind_append _ hq,
    after_bind_append _ hf, midTail_fin_eq, ← List.append_nil lc, after_bind_append _ hcm]
  simp [VerifierProgram.after]

/-- **A two-level stacked opening, after its final residual**, is before its level-1 query group. -/
theorem after_stacked_two_res (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
    (hc : cfg.levels = [level, next]) (cl : List LeanVM.Protocol.Verifier.StackClaim)
    {lq lf lc lgp lg lhq lf1 lres : List Ev} {ρ : E} {quad hq res : List E}
    {r r₁ : WhirStateT × List E} {g : List ℕ × E × List (List K)}
    (hq' : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl ρ) none).after lq =
      some (.ret quad))
    (hf : (foldRoundsT level.fold ⟨batT cl ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (cfg.μ - r.1.folds.length - next.fold + next.logInvRate)
      (3 * 2 ^ next.fold)).after lc = some (.ret ()))
    (hgp : (grindPre cfg.grind).after lgp = some (.ret ()))
    (hgq : (queryFragG cfg.grind cfg.per (cfg.μ - r.1.folds.length + level.logInvRate)
      level.queries (cidx cfg.c₀ cfg.n₀ 0)).after lg = some (.ret g))
    (hh : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after
      lhq = some (.ret hq))
    (hf1 : (foldRoundsT next.fold (glueLv cfg.μ 0 r g.1 g.2.1 g.2.2 hq) []).after lf1 =
      some (.ret r₁))
    (hres : (readScalars (2 ^ (cfg.μ - r₁.1.folds.length))).after lres = some (.ret res)) :
    ∃ g', (verifyStackedUd cfg cl).after
        ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lgp ++ (lg ++ (lhq ++ (lf1 ++ lres)))))))) =
      some ((grindPre cfg.grind).bind fun _ ↦
        (queryFragG cfg.grind cfg.per (cfg.μ - r₁.1.folds.length + next.logInvRate) next.queries
          (cidx cfg.c₀ cfg.n₀ (0 + 1))).bind g') := by
  refine ⟨fun g ↦ finFinish cfg.μ level.fold cfg.direct (batW cl ρ) (0 + 1) next r₁ res g.1 g.2.1
    g.2.2, ?_⟩
  rw [stacked_two_eq cfg level next hc cl,
    after_bind_append _ (rfl : sampleChallenge.after [Ev.sample ρ] = _), after_bind_append _ hq',
    after_bind_append _ hf, midTail_fin_eq, after_bind_append _ hcm, after_bind_append _ hgp,
    after_bind_append _ hgq, after_bind_append _ hh, after_bind_append _ hf1, finTail_eq,
    ← List.append_nil lres, after_bind_append _ hres]
  simp [VerifierProgram.after]

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound
open scoped ENNReal
variable {α β : Type}

theorem rec20_levels : cfgRec20G.levels = [recLevel0, recLevel1] := rfl

end Lvm.ASM
end

-- ===== from `LvmE2QPinOpenF` =====

section
set_option autoImplicit false
namespace Lvm.Q2
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Finset
variable {c : Ctx} {M : Mem}

theorem c6_mk (h : Bool) (a b : FE) : c6 h ⟨a, b⟩ = if h then b else a := rfl

end Lvm.Q2
end

section
set_option autoImplicit false
namespace Lvm.Q2
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Finset
variable {c : Ctx} {M : Mem}

theorem kcell_C2 {x : C2} (hx : KC2 x) : FE6.ofE2 (x.val M) = ⟨x.re.val M, x.im.val M⟩ := by
  simp only [FE6.ofE2, C2.val]
  rw [kcell_val hx.1, kcell_val hx.2]

end Lvm.Q2
end

section
set_option autoImplicit false
namespace Lvm.Q2
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Finset
variable {c : Ctx} {M : Mem}

/-- **The big-shape terms of one prepared claim**: no pairs; they sum to `sc · bc.onStack(x)`. -/
theorem pfTermsB_spec {F : FCtx} (hF : FCtxOk M F) {ν xb : ℕ} (sc : Cell) {fc : FClaim} {bc : BlockClaim}
    (hr : FRel M ν fc bc) (memo : Memo) (m6 : Memo6) (hm : MemoOk M (fun i => M.e (xb + i)) memo)
    (hm6 : Memo6Ok M xb m6) :
    Hs c M (pfTerms F ν xb sc (prepB F fc).1 memo m6) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
      Memo6Ok M xb r.2.1 ∧ r.2.2.1 = [] ∧
      (r.2.2.2.map (tval M (fun i => M.e (xb + i)) ν)).sum = sc.val M * bc.onStack.1 (xsOf M ν xb)) := by
  have hX : (xsOf M ν xb).length = ν := xs_length ν xb
  cases fc with
  | e3 cc =>
    obtain ⟨hwf, rfl⟩ := hr
    show Hs c M (oneClaim ν xb F.z F.o sc cc memo >>= fun r => pure (r.1, m6, [], r.2)) _
    exact hs_bind (oneClaim_spec hF.z hF.o hF.zE hwf hm) fun r ⟨hm', hv⟩ => hs_pure ⟨hm', hm6, rfl, hv⟩
  | half h parts v =>
    obtain ⟨hp, rfl⟩ := hr
    show Hs c M (halfTerms F ν xb sc h false parts m6 >>= fun r => pure (memo, r.1, r.2.1, r.2.2)) _
    refine hs_bind (halfTermsB_spec hF sc h parts m6 hp hm6) fun r ⟨hm', hn, hs⟩ => hs_pure ⟨hm, hm', hn, ?_⟩
    rw [hs, BlockClaim.onStack]
    simp only [halfB]
    rw [eqAbove_top ν _ hX, one_mul, List.take_of_length_le (by rw [hX]), c6_sumW6D]
  | dhalf h z v =>
    obtain ⟨hzK, hzl, h22, rfl⟩ := hr
    show Hs c M (halfTerms F ν xb sc h false [(F.o2, ⟨22, 0⟩, z)] m6 >>= fun r => pure (memo, r.1, r.2.1, r.2.2)) _
    refine hs_bind (halfTermsB_spec hF sc h [(F.o2, ⟨22, 0⟩, z)] m6 (fun e he => by
      simp only [List.mem_singleton] at he; subst he; exact ⟨hF.o2K, hzK, hzl, h22⟩) hm6)
      fun r ⟨hm', hn, hs⟩ => hs_pure ⟨hm, hm', hn, ?_⟩
    rw [hs, BlockClaim.onStack]
    simp only [halfB]
    rw [eqAbove_top ν _ hX, one_mul, List.take_of_length_le (i := ν) (l := xsOf M ν xb) (by rw [hX]),
      c6_sumW6D]
    simp only [partsV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hF.o2]
  | row blk z nu v =>
    obtain ⟨eqR, hnu, hne, hzK, hzl, hvc, rfl⟩ := hr
    simp only [prepB, pfTerms, Bool.false_eq_true, ↓reduceIte]
    refine hs_bind (rowLeafGL_weightN nu eqR hnu z hne hzK xb ((xsOf M ν xb).take blk.variableCount)
      (by rw [List.length_take, hX, hzl]; omega)
      (fun l hl => by rw [getD_take' _ _ (by omega), xs_getD (by omega)]) hF.z hF.zk) fun lf hlf =>
      hs_pure ⟨hm, hm6, rfl, ?_⟩
    have hE := eqAbove_prod blk (xsOf M ν xb) (fun i => M.e (xb + i)) (by rw [hX]; exact hvc)
      (fun i hi => xs_getD (by rwa [hX] at hi))
    rw [hX] at hE
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tval, kprod_keyOf, hlf, ← hE,
      BlockClaim.onStack]
    ring
  | drow z nu v =>
    obtain ⟨eqR, hnu, hne, hzK, hzl, hvc, rfl⟩ := hr
    simp only [prepB, pfTerms, Bool.false_eq_true, ↓reduceIte]
    refine hs_bind (rowLeafGL_weightN nu eqR hnu z hne hzK xb ((xsOf M ν xb).take CMain.nu20)
      (by rw [List.length_take, hX, hzl]; omega)
      (fun l hl => by rw [getD_take' _ _ (by omega), xs_getD (by omega)]) hF.z hF.zk) fun lf hlf =>
      hs_pure ⟨hm, hm6, rfl, ?_⟩
    have hE := eqAbove_prod (⟨CMain.nu20, 0⟩ : Placement) (xsOf M ν xb) (fun i => M.e (xb + i)) (by rw [hX]; exact hvc)
      (fun i hi => xs_getD (by rwa [hX] at hi))
    rw [hX] at hE
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tval, kprod_keyOf, hlf, ← hE,
      BlockClaim.onStack]
    ring

/-- **The big-shape terms of the prepared claims** from index `i` (scale cells `sp + i`). -/
theorem pfTermsAllB_spec {F : FCtx} (hF : FCtxOk M F) {ν xb sp N : ℕ} {s : FE}
    (hs : ∀ j < N, M.e (sp + j) = s ^ j) :
    ∀ (fcs : List FClaim) (bcs : List BlockClaim), List.Forall₂ (FRel M ν) fcs bcs →
      ∀ (i : ℕ) (memo : Memo) (m6 : Memo6), MemoOk M (fun i => M.e (xb + i)) memo → Memo6Ok M xb m6 →
      i + fcs.length ≤ N →
      Hs c M (pfTermsAll F ν xb sp i (fcs.map fun fc => (prepB F fc).1) memo m6) (fun r => r.1 = [] ∧
        (r.2.map (tval M (fun i => M.e (xb + i)) ν)).sum = bsum s i (bcs.map fun bc => bc.onStack.1 (xsOf M ν xb)))
  | [], [], _, _, _, _, _, _, _ => hs_pure ⟨rfl, by simp [bsum]⟩
  | fc :: fcs, bc :: bcs, .cons hr hrs, i, memo, m6, hm, hm6, hN => by
    simp only [List.length_cons] at hN
    simp only [List.map_cons]
    show Hs c M (pfTerms F ν xb (ec (sp + i)) (prepB F fc).1 memo m6 >>= fun r =>
      pfTermsAll F ν xb sp (i + 1) (fcs.map fun fc => (prepB F fc).1) r.1 r.2.1 >>= fun rs =>
        pure (r.2.2.1 ++ rs.1, r.2.2.2 ++ rs.2)) _
    refine hs_bind (pfTermsB_spec hF (ec (sp + i)) hr memo m6 hm hm6) fun r ⟨hm', hm6', hn, hv⟩ =>
      hs_bind (pfTermsAllB_spec hF hs fcs bcs hrs (i + 1) r.1 r.2.1 hm' hm6' (by omega)) fun rs ⟨hn', hv'⟩ =>
        hs_pure ⟨by rw [hn, hn', List.nil_append], ?_⟩
    rw [List.map_append, List.sum_append, hv, hv', bsum, Cell.val_E, hs i (by omega)]

/-- **The batched basis, big shape**: `Σ_i s^i·onStack_i(x)` over V's claims. -/
theorem basisGF_spec {F : FCtx} (hF : FCtxOk M F) {ν sp xb : ℕ} {s : FE} {fcs : List FClaim}
    {bcs : List BlockClaim} (hrel : List.Forall₂ (FRel M ν) fcs bcs) (hs : ∀ j < fcs.length, M.e (sp + j) = s ^ j) :
    Hs c M (basisGF F ν (fcs.map fun fc => (prepB F fc).1) sp xb) (fun r =>
      r.val M = Lvm.dot (powers s bcs.length) (bcs.map fun bc => bc.onStack.1 (xsOf M ν xb))) := by
  unfold basisGF
  refine hs_bind (pfTermsAllB_spec hF hs fcs bcs hrel 0 [] [] (fun _ he => by simp at he)
    (fun _ he => by simp at he) (by omega)) fun r ⟨_, hv⟩ => hs_mono (trieG_spec hF.z ν r.2) fun w hw => ?_
  rw [hw, hv]
  have hl : bcs.length = (bcs.map fun bc => bc.onStack.1 (xsOf M ν xb)).length := by simp
  rw [hl, dot_powers_bsum]

theorem prepB_value {F : FCtx} {ν : ℕ} {fc : FClaim} {bc : BlockClaim} (hr : FRel M ν fc bc) :
    (prepB F fc).2.val M = bc.value := by
  cases fc with
  | e3 cc => obtain ⟨-, rfl⟩ := hr; exact (cval_value cc).symm
  | half h parts v => obtain ⟨-, rfl⟩ := hr; rfl
  | dhalf h z v => obtain ⟨-, -, -, rfl⟩ := hr; rfl
  | row blk z nu v => obtain ⟨eqR, -, -, -, -, -, rfl⟩ := hr; rfl
  | drow z nu v => obtain ⟨eqR, -, -, -, -, -, rfl⟩ := hr; rfl

theorem vals_eq {F : FCtx} {ν : ℕ} : ∀ {fcs : List FClaim} {bcs : List BlockClaim},
    List.Forall₂ (FRel M ν) fcs bcs → fcs.map (fun fc => (prepB F fc).2.val M) = bcs.map (·.value)
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons hr hrs => by rw [List.map_cons, List.map_cons, prepB_value hr, vals_eq hrs]

set_option maxHeartbeats 1000000 in
/-- **`C_main`'s opening at S2GF, big shape, replays V's**: on the claim list `(pinW, pin.value) :: bcs.map onStack`
(`pinW` the pin's weight on the stack, `bcs` what the circuit's claims stand for), `verifyStackedOpening` keeps
`ok`, ends at the opening's end and leaves no message pending. -/
theorem openGF_big_run (Cm : SCfg) {F : FCtx} (hF : FCtxOk M F) (pin : CClaim) (pinB : BlockClaim)
    (hpin : FRel M Cm.nu (.e3 pin) pinB) (pinW : List FE → FE)
    (hpinW : ∀ x : List FE, x.length = Cm.nu → pinW x = pinB.onStack.1 x) (cs : List FClaim)
    (bcs : List BlockClaim) (hrel : List.Forall₂ (FRel M Cm.nu) cs bcs) (mb : List Cell) (sK g : Cell)
    {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk Cm T = true) (hg : g.val M = 1)
    (hgK : g.ty = .K) (hpos : PosOk Cm M sig 0 Cm.levels (Cm.U + 15)) (hpw : PwOk Cm M 0 Cm.levels) {p : Ptr}
    (hp : 1 ≤ p.e) (h : Lvm.QSig.Ok c M (openGF Cm false F pin cs mb sK g) p) (s : RS) (hs : pos s = 8 * Cm.U) :
    let scs := (pinW, pinB.value) :: bcs.map (·.onStack)
    (verifyStackedOpening Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2 =
      8 * stackEndL Cm.g Cm.ood Cm.levels (Cm.U + 15) ∧
    (verifyStackedOpening Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2.msg = 0 := by
  intro scs
  simp only [openGF, Bool.false_eq_true, if_false] at h
  have hrel' : List.Forall₂ (FRel M Cm.nu) (.e3 pin :: cs) (pinB :: bcs) := .cons hpin hrel
  have hlen : scs.length = cs.length + 1 := by simp [scs, hrel.length_eq]
  have hw : (PF.e3 pin false, pin.value) :: cs.map (prepB F) = (FClaim.e3 pin :: cs).map (prepB F) := rfl
  refine stackG_run Cm (cs.length + 1) _ _ _ (fun w => w = (FClaim.e3 pin :: cs).map (prepB F)) scs hlen
    (hs_pure hw) ?_ ?_ F.z F.o g hS hok hF.z hF.o hF.zE hF.oE hg hgK hpos hpw hp h s hs
  · intro w hw' sp σ hsp p' h'
    subst hw'
    have hl : (((FClaim.e3 pin :: cs).map (prepB F)).map fun e =>
        (⟨.main, .point ⟨0, 0⟩ [], e.2⟩ : CClaim)).length = cs.length + 1 := by simp
    rw [targetG_spec h' hF.z σ (fun i hi => hsp i (by rw [← hl]; exact hi)), hl]
    have hv : ((((FClaim.e3 pin :: cs).map (prepB F)).map fun e => (⟨.main, .point ⟨0, 0⟩ [], e.2⟩ : CClaim)).map
        fun cc => (cc.val M).2.value) = scs.map (·.2) := by
      rw [List.map_map, List.map_map,
        show scs.map (·.2) = (pinB :: bcs).map (·.value) by simp only [scs, List.map_cons, List.map_map]; rfl]
      exact vals_eq hrel'
    rw [hv]
  · intro w hw' sp xb σ hsp
    subst hw'
    have e : ((FClaim.e3 pin :: cs).map (prepB F)).map (·.1) = (FClaim.e3 pin :: cs).map fun fc => (prepB F fc).1 := by
      rw [List.map_map]; rfl
    rw [e]
    refine hs_mono (basisGF_spec hF hrel' fun j hj => hsp j (by simpa using hj)) fun r hr => ?_
    rw [hr]
    have hl : (pinB :: bcs).length = cs.length + 1 := by simp [hrel.length_eq]
    rw [hl]
    congr 1
    simp only [scs, List.map_cons, List.map_map]
    have hX : ((List.range Cm.nu).map fun i => M.e (xb + i)).length = Cm.nu := by simp
    refine congrArg₂ List.cons (hpinW _ hX).symm ?_
    rfl

end Lvm.Q2
end

section
set_option autoImplicit false
namespace Lvm.Q2
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Finset
variable {c : Ctx} {M : Mem}

theorem point_onStack (ν : ℕ) (z : List FE) (a : FE) (x : List FE) (hx : x.length = ν) :
    (BlockClaim.point ⟨ν, 0⟩ z a).weight x = (BlockClaim.point ⟨ν, 0⟩ z a).onStack.1 x := by
  simp only [BlockClaim.point, BlockClaim.onStack]
  rw [eqAbove_top ν x hx, one_mul, List.take_of_length_le (by omega)]

end Lvm.Q2
end

section
set_option autoImplicit false
namespace Lvm.Q2
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Finset
variable {c : Ctx} {M : Mem}

set_option maxHeartbeats 1000000 in
/-- **`C_main`'s opening at S2GF, big shape, is V's `dOpenF p false`** (`hopen` of `core_of_phasesF` for a big
child): from the opening's start with `ok`, V keeps `ok`, reads `Σ` to the opening's end and leaves no message
pending; `pinB` is V's pin claim (`pinD`'s point claim), `cls` V's other claims, each standing for the circuit's. -/
theorem openF_big_at (p : Params) (Cm : SCfg) (hlv : Cm.levels = p.mainLevels) (hnu : Cm.nu = p.nuMain)
    (hgr : Cm.g = p.grind) (hood : Cm.ood = p.mainOod) {F : FCtx} (hF : FCtxOk M F) (pin : CClaim)
    (z : List FE) (a : FE) (hpin : FRel M Cm.nu (.e3 pin) (BlockClaim.point ⟨Cm.nu, 0⟩ z a)) (cs : List FClaim)
    (cls : List (Com × BlockClaim × FE)) (hrel : List.Forall₂ (FRelT M Cm.nu) cs cls) (mb : List Cell)
    (sK g : Cell) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk Cm T = true)
    (hg : g.val M = 1) (hgK : g.ty = .K) (hpos : PosOk Cm M sig 0 Cm.levels (Cm.U + 15)) (hpw : PwOk Cm M 0 Cm.levels)
    (hend : 8 * stackEndL Cm.g Cm.ood Cm.levels (Cm.U + 15) = sig.size) {q : Ptr} (hq : 1 ≤ q.e)
    (h : Lvm.QSig.Ok c M (openGF Cm false F pin cs mb sK g) q) :
    ∀ s : RS, pos s = 8 * Cm.U → s.ok = true →
      (dOpenF p false (BlockClaim.point ⟨Cm.nu, 0⟩ z a) cls sig s).2.ok = true ∧
      (dOpenF p false (BlockClaim.point ⟨Cm.nu, 0⟩ z a) cls sig s).2.ent = sig.size ∧
      (dOpenF p false (BlockClaim.point ⟨Cm.nu, 0⟩ z a) cls sig s).2.msg = 0 := by
  intro s hs hsok
  obtain ⟨hall, hrel'⟩ := relT_main hrel
  have hrq : ({ s with ok := true && s.ok } : RS) = s := by cases s; rfl
  have e : dOpenF p false (BlockClaim.point ⟨Cm.nu, 0⟩ z a) cls sig s =
      verifyStackedOpening Cm.levels Cm.nu (((BlockClaim.point ⟨Cm.nu, 0⟩ z a).weight, a) ::
        ((cls.filter (·.1 == .main)).map (·.2.1)).map (·.onStack)) false Cm.g Cm.ood sig s := by
    unfold dOpenF
    rw [dm_bind, require_runW, hall, hrq, hlv, hnu, hgr, hood]
    simp only [Bool.false_eq_true, if_false, List.map_map]
    rfl
  rw [e]
  obtain ⟨o1, o2, o3⟩ := openGF_big_run Cm hF pin _ hpin _ (fun x hx => point_onStack Cm.nu z a x hx) cs _ hrel' mb
    sK g hS hok hg hgK hpos hpw hq h s hs
  refine ⟨o1.trans hsok, ?_, o3⟩
  simp only [pos] at o2
  rw [show (BlockClaim.point ⟨Cm.nu, 0⟩ z a).value = a from rfl] at o2 o3
  omega

end Lvm.Q2
end
