-- New for lvm2 roll 11 (M′, R11-LEAD freeze 2026-11-13): the `S` branch's certificate with one commitment
-- (`C_rec` merged into `C_main`). Definitions are final; the `sorry`s are frozen statements (owner: R11-C,
-- except `extJM`'s decoders, R11-X). A proof never changes its statement; a needed change is reported old → new.
import LvmSubmissionS
import LvmCertSNo
import LvmMPDec
import LvmMPCertOpen
import LvmMPCertExt

/-!
# M′'s certificate: one root, INV on `C_main`

M′ commits one word, `C_main` at ν = 23 (`cfgMain23Jq 1`: `(6,2,115)(4,3,77)(4,4,58)`, OOD, `g = 14`). The
stream, `σ'` and every recursion table sit in `C_main`; the middle phases return claims on `C_main` only.

INV (J2C-DES, `kcertOfInv`) with one list: the middle phases leave every **non-good** candidate of `C_main`
failing a claim (`OpenPostM`, list `≤ 124`, so `L₀ = 124`); `C_main`'s opening runs JB-L's relativised prefix
(`stackedPrefixSpecR` at `codesMain23Jq`, good set `Good x`) to the residual, where `GoodRes ∨ ResC`;
`ResC` is rejected by the suffix (`finSuffixSpecR`), `GoodRes` is recorded as `ExtIM`. No split at the
openings (`openPostR_split` goes) and no `GoodRec`.

The extractor decodes `C_main` from the residual: level 2, level 1, then level 0's stream window
(`LvmMPDec`), with luck over the three levels' lists (14 fold rounds).

* defs: `GoodRelM`, **`PSWithM`**, `RootShapeM`, `OpenPostM`, **`MidSpecM`**, `MidShapeM`, `mainPrefixProg`,
  `GoodResAtM`, **`ExtIM`**, `ExtJM`, **`NodeSoundM`**, `mainDataM`, **`extSM`**, `OpenSM`;
* frozen: `ng_PSWithM`, **`psInvM`**, `goodRes_main23Jq`, **`extJM`**, `extJM_ext`;
* assembled here: **`kcertSM`**, **`εFS_kcertSM`** (`≤ 2^-128`), **`sSound_of_openSM`**.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir (iList)
open scoped NNReal ENNReal

/-! ## Definitions -/

/-- The M3 witness relation on one `C_main` candidate (physical stack; the shape's view is the instance's). -/
abbrev GoodRelM : Type := List UInt8 → LeanVM.Protocol.Column CMain.nu20 → Prop

/-- **The IOP verifier `P_S` at M′**: one root (`cfgMain24G`'s root = `cfgMain23Jq`'s), the middle phases
(claims on `C_main` only), `C_main`'s Johnson opening with `n₀ = 1` commitment before it. -/
def PSWithM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8) :
    VerifierProgram Bool := do
  commitRootUd cfgMain24G
  let cl ← mid x
  verifyStackedJ (cfgMain23Jq 1) cl
  return true

/-- The root's shape, and nothing else committed. -/
def RootShapeM (h : List Ev) : Prop :=
  ∃ W, commits h = [(19, 64, W)] ∧ WellShaped 64 W

/-- **The middle phases' postcondition at M′**: every non-good candidate of `C_main` fails a claim; the root's
shape; multiaffine claims, at most `2^40` (`eBatch_main23Jq`). -/
def OpenPostM (Good : GoodRelM) (x : List UInt8) (cl : List LeanVM.Protocol.Verifier.StackClaim) (h : List Ev) : Prop :=
  (∀ q ∈ Candidates CMain.nu20 2 thrMain (wordOf (commits h) 0), ¬ Good x q →
      ∃ c ∈ cl, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c q) ∧
  RootShapeM h ∧ (∀ c ∈ cl, IsMultiaffine CMain.nu20 c.1) ∧ cl.length ≤ 2 ^ 40

/-- **Obligation `MidSpecM`**: the middle phases, from the root's shape, end in `OpenPostM`, every group's
escape at most `εm`, lead `Lm`, for every follower's allowance `T ≤ εm`. -/
def MidSpecM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (Good : GoodRelM) (εm Lm : ℝ≥0∞) :
    Prop :=
  ∀ x (T : ℝ≥0∞), T ≤ εm → Nonempty (Spec (mid x) RootShapeM (OpenPostM Good x) εm Lm T)

/-- The middle phases commit nothing and grind nothing. -/
structure MidShapeM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) : Prop where
  noCommit : ∀ x, (mid x).NoCommit
  noGrind : ∀ x, (mid x).NoGrind

/-- **The run up to `C_main`'s residual**: the root, the middle phases, `C_main`'s opening up to the residual. -/
def mainPrefixProg (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8) :
    VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim × E × ((WhirStateT × List E) × List E)) :=
  commitRootUd cfgMain24G >>= fun _ ↦ mid x >>= fun cl ↦
    stackPrefixJ (cfgMain23Jq 1) cl >>= fun a ↦ .ret (cl, a)

/-- **The residual is good** (`PostR`'s left disjunct at `cfgMain23Jq 1`, final level `2`, good root set
`Good x`). -/
def GoodResAtM (Good : GoodRelM) (x : List UInt8) (a : E × ((WhirStateT × List E) × List E))
    (h₁ : List Ev) : Prop :=
  let cs := viewC 0 1 (commits h₁)
  GoodRes (codesMain23Jq 2) 2
    (gdFinal codesMain23Jq cs a.2.1.1.folds 0 0 (cfgMain23Jq 1).levels (gdRoot (codesMain23Jq 0) (Good x) cs))
    a.2.1 a.2.2 cs

/-- **What an accepting run in the invariant has**: a prefix is a completed `mainPrefixProg` run with a good
residual. -/
def ExtIM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (Good : GoodRelM) (x : List UInt8)
    (h : List Ev) : Prop :=
  ∃ h₁ cl a, h₁ <+: h ∧ (mainPrefixProg mid x).after h₁ = some (.ret (cl, a)) ∧ GoodResAtM Good x a h₁

theorem ExtIM.append {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
    {x : List UInt8} {h : List Ev} (hE : ExtIM mid Good x h) (l : List Ev) : ExtIM mid Good x (h ++ l) := by
  obtain ⟨h₁, cl, a, hp, ha, hg⟩ := hE
  exact ⟨h₁, cl, a, hp.trans (List.prefix_append h l), ha, hg⟩

/-- **The extraction's interface at M′** (as `ExtJ`, on `PSWithM` and `ExtIM`). -/
structure ExtJM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (Good : GoodRelM) (VS : SProg)
    (vk : Digest) : Type where
  BL : List UInt8 → List Ev → Prop
  BL_nil : ∀ x, ¬ BL x []
  BL_read : ∀ {x h k} (y : E), (PSWithM mid x).Reachable h → (PSWithM mid x).after h = some (.read k) →
    ¬ BL x h → ¬ BL x (h ++ [Ev.read y])
  BL_commit : ∀ {x h ht w k} (word : LeanVM.Protocol.Compile.Word), (PSWithM mid x).Reachable h →
    (PSWithM mid x).after h = some (.commit ht w k) → WellShaped w word → ¬ BL x h →
    ¬ BL x (h ++ [Ev.commit ht w word])
  BL_group : ∀ {x h p}, (PSWithM mid x).Reachable h → Boundary h → (PSWithM mid x).after h = some p →
    ((∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k)) → ¬ BL x h →
    esc (fun h' => ¬ BL x h') h p ≤ (((2 : ℝ≥0)⁻¹ ^ 132 : ℝ≥0) : ℝ≥0∞)
  ext : Digest → List UInt8 → List Ev → Wit
  extract : ∀ {c x h}, okS vk c x = true → (PSWithM mid x).Reachable h →
    (PSWithM mid x).after h = some (.ret true) → ExtIM mid Good x h → ¬ BL x h →
    (∀ h', h' <+: h → Boundary h' → ¬ BL x h') → Rel (accV VS vk) c (ext c x h)

/-- **Obligation `NodeSoundM`**: a statement the header check accepts and a good `C_main` candidate give the
relation for the witness whose left child is read from the candidate's stream window (`winOf`; `child` reads the
stream at the statement's shape). -/
def NodeSoundM (VS : SProg) (vk : Digest) (Good : GoodRelM)
    (child : List UInt8 → List BF64 → Signed) : Prop :=
  ∀ c x q, okS vk c x = true → Good x q → Rel (accV VS vk) c (witOf x (child x (Lvm.X.winOf q)))

/-- **`C_main`'s values**, read off a history as `mainPrefixProg`'s return: all fold challenges (`6 + 4 + 4`)
and the residual. -/
def mainDataM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8) (h : List Ev) :
    Option (List E × List E) :=
  match (mainPrefixProg mid x).retSplit h with
  | none => none
  | some ((_, _, r, res), _, _) => some (r.1.folds, res)

/-- **M′'s extraction map**: the three decoders on `C_main`'s words (`commits h` `0, 1, 2`), the fold challenges
`α₀ = folds[0,6)`, `α₁ = folds[6,10)`, `α₂ = folds[10,14)` and the residual; the witness with the child read
from the decoded window. No choice. -/
noncomputable def extSM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim))
    (child : List UInt8 → List BF64 → Signed) (_c : RecursionFast.Digest) (x : List UInt8) (h : List Ev) :
    Wit :=
  witOf x (child x (((mainDataM mid x h).bind fun d ↦
    (Lvm.X.decodeMP2 (Lvm.X.wdOf (wordOf (commits h) 2)) (Lvm.X.alphaN1 fun i ↦ d.1.getD (10 + i) 0)
        (Lvm.X.fNk 9 (resMsg d.2))).bind fun m₂ ↦
      (Lvm.X.decodeMP1 (Lvm.X.wdOf (wordOf (commits h) 1)) (Lvm.X.alphaN1 fun i ↦ d.1.getD (6 + i) 0)
          m₂).bind fun m₁ ↦
        Lvm.X.decodeMP0 (Lvm.X.wdOf (wordOf (commits h) 0)) (Lvm.X.alphaN fun i ↦ d.1.getD i 0) m₁).getD []))

/-! ## Frozen statements -/

section Frozen

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}

/-- `P_S` at M′ grinds nothing outside its query groups. -/
theorem ng_PSWithM (hm : ∀ x, (mid x).NoGrind) (x : List UInt8) : (PSWithM mid x).NoGrind :=
  ng_PSWithMH hm x

/-- **`P_S` at M′ in the invariant**: from the empty history, every group at most `εS`, lead `0`; an accepting
return has `ExtIM`. With `Good := ⊥` this is soundness. -/
noncomputable def psInvM (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    (x : List UInt8) :
    Spec (PSWithM mid x) (fun h ↦ h = []) (fun b h ↦ b = true → ExtIM mid Good x h) εS 0 0 :=
  (Spec.bind' (rootInvM hLm) fun _ ↦
    Spec.bind' (((hmid x εS le_rfl).some.traced
        (fun h ↦ (commitRootUd cfgMain24G).after h = some (.ret ()))).mono (fun _ h ↦ h) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl)
      fun cl ↦ (mainOpenInv (Gd := Good x) (M := ExtIM mid Good x) (J := RunMidM mid x cl)
        (fun _ l h ↦ h.append l)
        (fun a h₀ l hr ha hg ↦ ⟨h₀ ++ l, cl, a, List.prefix_refl _, mainPrefixProg_afterM hr ha, hg⟩)).mono
        (fun h ⟨⟨hcand, ⟨W, hc, hW⟩, hma, hlen⟩, hrun⟩ ↦
          ⟨⟨⟨by decide, by rw [hc]; rfl, ⟨W, by rw [hc]; rfl, hW⟩, hcand⟩, hma, hlen⟩, hrun⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).congr rfl

/-- **M′'s good residual, unfolded** (as `goodRes_rec20Jp`, three levels): a good root candidate `q`, a member
`V₁` of level 1's list on `q`'s path after `α₀`, a member `V₂` of level 2's list on `q`'s path after
`α₀ ++ α₁`, and the residual is `q`'s path after `α₀ ++ α₁ ++ α₂`. -/
theorem goodRes_main23Jq {G : LeanVM.Protocol.Column CMain.nu20 → Prop} {cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)}
    {r : WhirStateT × List E} {res : List E} (α₀ : Fin 6 → E) (α₁ α₂ : Fin 4 → E)
    (hfs : r.1.folds = List.ofFn α₀ ++ List.ofFn α₁ ++ List.ofFn α₂)
    (hG : GoodRes (codesMain23Jq 2) 2
      (gdFinal codesMain23Jq cs r.1.folds 0 0 (cfgMain23Jq 1).levels (gdRoot (codesMain23Jq 0) G cs))
      r res cs) :
    ∃ q ∈ Candidates CMain.nu20 2 (codesMain23Jq 0).thr (wordOf cs 0), G q ∧
      (∃ V₁ ∈ iList (codesMain23Jq 1).code (codesMain23Jq 1).thr (rowsOf 4 (laneO 1 cs (codesMain23Jq 1).n)),
        PathAt q (List.ofFn α₀) (decode (codesMain23Jq 1) V₁)) ∧
      (∃ V₂ ∈ iList (codesMain23Jq 2).code (codesMain23Jq 2).thr (rowsOf 4 (laneO 2 cs (codesMain23Jq 2).n)),
        PathAt q (List.ofFn α₀ ++ List.ofFn α₁) (decode (codesMain23Jq 2) V₂)) ∧
      (∀ y : Fin (codesMain23Jq 2).κ → Bool,
        resMsg res y = qMle q (List.ofFn α₀ ++ List.ofFn α₁ ++ List.ofFn α₂ ++ bitsL y)) :=
  goodRes_main23JqH α₀ α₁ α₂ hfs hG

/-- **M′'s extraction** (luck over `C_main`'s three lists, `≤ 2^-132` per group; the map `extSM`). -/
noncomputable def extJM (hsh : MidShapeM mid) {VS : SProg} {vk : RecursionFast.Digest}
    {child : List UInt8 → List BF64 → Signed} (hnode : NodeSoundM VS vk Good child) : ExtJM mid Good VS vk := by
  exact
    { BL := LuckBM mid
      BL_nil := fun _ ↦ not_luckBM_nil
      BL_read := fun _ _ _ hB ↦ not_luckBM_snoc rfl hB
      BL_commit := fun _ _ _ _ hB ↦ not_luckBM_snoc rfl hB
      BL_group := fun {_ h p} _ _ _ _ hB ↦ (esc_luckBM_le_132 p h hB).trans coe_εB.ge
      ext := extSM mid child
      extract := fun {c x _} hok hreach _ hE hB _ ↦ by
        obtain ⟨h₁, cl, ⟨ρ, r, res⟩, ⟨t, rfl⟩, hpre, hg⟩ := hE
        obtain ⟨q, hq, hdec⟩ := decode_SMH (hsh.noCommit x) hpre hg (reachable_commit_ws hreach) hB
        have hd : mainDataM mid x (h₁ ++ t) = some (r.1.folds, res) := by
          unfold mainDataM
          rw [VerifierProgram.retSplit_of_after _ _ _ hpre]
        dsimp only at hdec
        unfold extSM
        rw [hd, Option.bind_some]
        dsimp only
        rw [hdec, Option.getD_some]
        exact hnode c x q hok hq }

/-- **`extJM`'s map is the decoder chain** (no choice). -/
theorem extJM_ext (hsh : MidShapeM mid) {VS : SProg} {vk : RecursionFast.Digest}
    {child : List UInt8 → List BF64 → Signed} (hnode : NodeSoundM VS vk Good child) :
    (extJM hsh hnode).ext = extSM mid child := by
  rfl

end Frozen

/-! ## Assembly -/

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}
  {VS : SProg} {vk : RecursionFast.Digest}

/-- **The knowledge certificate of the `S` branch at M′**: no doom, luck `¬ Inv ∨ BL` at
`εB = 7·2^-131 + 2^-132`. -/
noncomputable def kcertSM (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    (X : ExtJM mid Good VS vk) : KCert (schemeS vk (PSWithM mid)) (Rel (accV VS vk)) :=
  kcertOfInv (S := schemeS vk (PSWithM mid)) (εI := 7 * (2 : ℝ≥0)⁻¹ ^ 131) (εL := (2 : ℝ≥0)⁻¹ ^ 132)
    (Ext := ExtIM mid Good)
    (fun x ↦ (psInvM hmid hLm hsh x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) coe_εS.ge le_rfl le_rfl)
    zero_le (fun x _ hr ↦ NoGrind.reach_grindBits (ng_PSWithM hsh.noGrind x) hr)
    X.BL X.BL_nil X.BL_read X.BL_commit X.BL_group
    (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) X.ext X.extract

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertSM (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    (X : ExtJM mid Good VS vk) : Scheme.εFS (kcertSM hmid hLm hsh X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  Scheme.εFS_le_of _ (by
    show (0 : ℝ≥0) + (7 * (2 : ℝ≥0)⁻¹ ^ 131 + (2 : ℝ≥0)⁻¹ ^ 132) + (2 : ℝ≥0)⁻¹ ^ 139 ≤ (2 : ℝ≥0)⁻¹ ^ 128
    rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **M′'s open obligations** (as `OpenS`): the middle phases on `C_main` only, `NodeSoundM`, the refinement of
`V_S` to `PSWithM`, the executable extractor on good logs. -/
structure OpenSM (VS : SProg) (E : Digest → Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  hmid : MidSpecM mid Good εS Lm
  hLm : Lm ≤ εS
  hsh : MidShapeM mid
  child : List UInt8 → List BF64 → Signed
  hnode : ∀ vk, NodeSoundM VS vk Good child
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeS vk (PSWithM mid)).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSM hmid hLm hsh (extJM hsh (hnode vk))) L < 1 →
    ((schemeS vk (PSWithM mid)).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeS vk (PSWithM mid)).Ex (kcertSM hmid hLm hsh (extJM hsh (hnode vk))).ext c π L

/-- **`SSound` from M′'s open obligations.** -/
theorem sSound_of_openSM {E : Digest → Proof → Log → Option Wit} (o : OpenSM VS E) (vk : Digest) :
    SSound VS E vk :=
  sSound_of VS E vk (PSWithM o.mid) (kcertSM o.hmid o.hLm o.hsh (extJM o.hsh (o.hnode vk)))
    (εFS_kcertSM o.hmid o.hLm o.hsh (extJM o.hsh (o.hnode vk))) (o.refines vk)
    fun L c π hS hl hμ hv ↦ o.ext_eq vk L c π hS hl hμ hv

end Lvm.ASM
