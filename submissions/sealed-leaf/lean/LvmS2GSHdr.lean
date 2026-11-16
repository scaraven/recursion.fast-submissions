-- New for lvm2 σ_LEAF (SLF-L, 2026-11-16): the `S` header without `σ_leaf` (stage S2GS) at the contract's side.
-- DAY-0 STATEMENTS: every `sorry` is tagged `-- SLF-STMT <n>`. A proof never changes its statement; a needed change
-- goes to the lead old → new.
import LvmS2GSSched
import LvmCertF20
import LvmNodeSound
import LvmE2VPub

/-!
# S2GS: the native checks without `σ_leaf`, the node's own leaf signature from the window

At S2GS the header is `'S' pad[7] | b | vk | c_L | s | n | h | acc_in`; `σ_leaf` sits in the node's decoded window and
the node circuit checks `SigOk vk (traceDigest []) σ_leaf` against `V`'s input `vk` (lead decision D1).

* **`parseOkS`**: `parseOk` without the zero check of `σ_leaf` (`b = 0`) and without the native leaf `SigOk`
  (`b = 1`). **`okSL`**: the scheme's native check, `okS` without its `SigOk` conjunct.
* **`witOfL x child sl`**: `witOf` with the right leaf's signature `sl` a parameter (`witOf x child =
  witOfL x child (hdrOf x).sig`, `witOf_eq_L`).
* **`NodeSoundS`**, **`nodeSoundS_of`**: `NodeSound`'s twin whose right leaf signs with `sl x qm` (read off the `C_main`
  candidate); the right leaf's `SigOk` is a hypothesis (`hright`, from the node circuit's second walk), not `okS`'s
  conjunct.
* **The scheme at S2GS** (`schemeSWS`: `ok := okSL vk`) and M′'s knowledge-certificate chain over it, verbatim copies of
  `ExtJM`, `extJML`, `kcertSMWτ`, `OpenSMW`, `kcertSFWτ`, `OpenSFW`, `openSFW`, `certificateR_openW` with `okSL` and
  `witOfL` (`ExtJMS`, `extJMLS`, `kcertSMWSτ`, `OpenSMWS`, `kcertSFWSτ`, `OpenSFWS`, `openSFWS`,
  `certificateR_openWS`).
* **`pubOfWS`**, **`pubXTS`**: the public values without `σ_leaf` lanes, `acc_in` from header byte `hdrFixS`.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **`V_S`'s native checks at S2GS** (`parseOk` without `σ_leaf`: no zero check for `b = 0`, no native leaf
`SigOk` for `b = 1`; the node circuit checks the node's own `σ_leaf` on its window). -/
def parseOkS (p : Params) (vk c : Digest) (π : ByteArray) : Bool :=
  π.size == piSize p && π.get! 0 == 0x53 && zeroBytes π 1 7 &&
    let hd := Header.ofProof π
    (hd.b == 0 || hd.b == 1) && hd.vk == vk && 1 ≤ hd.n && hd.n ≤ chainCap && hd.n ≤ 2 ^ p.logN &&
    (if hd.b = 0 then hd.cL == zeroDigest && c == hd.stmt else c == hd.stmt)

/-- **The public values at S2GS** (`pubOfW fe16At 16 accVT` without `σ_leaf`'s lanes; `acc_in`'s 16-B entries from
header byte `hdrFixS`). -/
def pubOfWS (vk c : Vector UInt8 32) (sig : ByteArray) : Pub :=
  { pubOfW fe16At 16 Lvm.VEq.accVT vk c sig with
    sigLeaf := [],
    accIn := ⟨(List.range Lvm.VEq.accVT).map fun i => fe16At sig (headerAt (hdrFixS + 16 * i)),
      fe16At sig (headerAt (hdrFixS + 16 * Lvm.VEq.accVT))⟩ }

/-- **The statement's public values at S2GS** (`pubXT`'s twin). -/
def pubXTS (x : List UInt8) : Pub := pubOfWS (Lvm.VEq.hdX x).vk (Lvm.VEq.hdX x).stmt (Lvm.VEq.sigOfX x)

end Lvm

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open RecursionFast.WitnessSending (encode)
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped NNReal ENNReal

/-- **The native statement check at S2GS** (`okS` without the leaf signature's `SigOk`). -/
def okSL (vk c : Digest) (x : List UInt8) : Bool :=
  let hd := hdrOf x
  (hd.b == 0 || hd.b == 1) && hd.vk == vk && decide (1 ≤ hd.n) && decide (hd.n ≤ chainCap) &&
    (if hd.b = 0 then decide (c = leafStmt hd.h hd.n)
     else decide (c = nodeStmt hd.cL (leafStmt hd.h hd.n)))

/-- **The witness of the statement `x`** with left child `child` and the right leaf's signature `sl`. -/
def witOfL (x : List UInt8) (child : Signed) (sl : Sig) : Wit :=
  let hd := hdrOf x
  if hd.b = 0 then .leaf hd.s hd.n
  else .node hd.cL (leafStmt hd.h hd.n) child ⟨encode (.leaf hd.s hd.n), [], sl⟩

/-- `witOf` is `witOfL` at the header's `σ_leaf`. -/
theorem witOf_eq_L (x : List UInt8) (child : Signed) : witOf x child = witOfL x child (hdrOf x).sig := rfl

/-- `okS` implies `okSL`. -/
theorem okSL_of_okS {vk c : Digest} {x : List UInt8} (h : okS vk c x = true) : okSL vk c x = true := by
  unfold okS at h
  unfold okSL
  generalize hdrOf x = hd at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  split
  · rename_i h0; simpa [h0] using h.2
  · rename_i h0; simp only [h0, if_false, Bool.and_eq_true] at h; exact h.2.1

/-- **Obligation `NodeSoundS`** (`NodeSound` at S2GS): a statement `okSL` accepts and a good candidate pair give the
relation for the witness whose left child is read from `C_rec`'s candidate and whose right leaf signs with
`sl x qm`, read off the `C_main` candidate. -/
def NodeSoundS (VS : SProg) (vk : Digest) (Good : GoodRel) (child : LeanVM.Protocol.Column 19 → Signed)
    (sl : List UInt8 → LeanVM.Protocol.Column CMain.nu20 → Sig) : Prop :=
  ∀ c x qm qr, okSL vk c x = true → Good x qm qr → Rel (accV VS vk) c (witOfL x (child qr) (sl x qm))

/-- **The `S` branch's scheme at a format, S2GS** (`schemeSW` with the native check `okSL`). -/
def schemeSWS (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) : Scheme :=
  { schemeSW f vk P with ok := okSL vk }

/-- **`extSML` at S2GS**: the right leaf signs with `sl` of the window. -/
noncomputable def extSMLS (lo : List UInt8 → ℕ)
    (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim))
    (child : List UInt8 → List BF64 → Signed) (sl : List UInt8 → List BF64 → Sig) (_c : RecursionFast.Digest)
    (x : List UInt8) (h : List Ev) : Wit :=
  let w := ((mainDataM mid x h).bind fun d ↦
    (Lvm.X.decodeMP2 (Lvm.X.wdOf (wordOf (commits h) 2)) (Lvm.X.alphaN1 fun i ↦ d.1.getD (10 + i) 0)
        (Lvm.X.fNk 9 (resMsg d.2))).bind fun m₂ ↦
      (Lvm.X.decodeMP1 (Lvm.X.wdOf (wordOf (commits h) 1)) (Lvm.X.alphaN1 fun i ↦ d.1.getD (6 + i) 0)
          m₂).bind fun m₁ ↦
        Lvm.X.decodeMP0L (lo x) (Lvm.X.wdOf (wordOf (commits h) 0)) (Lvm.X.alphaN fun i ↦ d.1.getD i 0) m₁).getD []
  witOfL x (child x w) (sl x w)

/-- **`NodeSoundML` at S2GS** (the window from lane `lo x` gives both the left child and the right leaf's
signature). -/
def NodeSoundMLS (lo : List UInt8 → ℕ) (VS : SProg) (vk : Digest) (Good : GoodRelM)
    (child : List UInt8 → List BF64 → Signed) (sl : List UInt8 → List BF64 → Sig) : Prop :=
  ∀ c x q, okSL vk c x = true → Good x q →
    Rel (accV VS vk) c (witOfL x (child x (Lvm.X.winOfL (lo x) q)) (sl x (Lvm.X.winOfL (lo x) q)))

/-- **`ExtJM` at S2GS** (`extract` under `okSL`). -/
structure ExtJMS (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (Good : GoodRelM)
    (VS : SProg) (vk : Digest) : Type where
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
  extract : ∀ {c x h}, okSL vk c x = true → (PSWithM mid x).Reachable h →
    (PSWithM mid x).after h = some (.ret true) → ExtIM mid Good x h → ¬ BL x h →
    (∀ h', h' <+: h → Boundary h' → ¬ BL x h') → Rel (accV VS vk) c (ext c x h)

section Chain

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}

/-- **M′'s extraction at S2GS** (`extJML`'s proof; the map `extSMLS lo`). -/
noncomputable def extJMLS (lo : List UInt8 → ℕ) (hlo : ∀ x, lo x + Lvm.X.winC ≤ 64) (hsh : MidShapeM mid)
    {VS : SProg} {vk : RecursionFast.Digest} {child : List UInt8 → List BF64 → Signed}
    {sl : List UInt8 → List BF64 → Sig} (hnode : NodeSoundMLS lo VS vk Good child sl) : ExtJMS mid Good VS vk := by
  exact
    { BL := LuckBM mid
      BL_nil := fun _ ↦ not_luckBM_nil
      BL_read := fun _ _ _ hB ↦ not_luckBM_snoc rfl hB
      BL_commit := fun _ _ _ _ hB ↦ not_luckBM_snoc rfl hB
      BL_group := fun {_ h p} _ _ _ _ hB ↦ (esc_luckBM_le_132 p h hB).trans coe_εB.ge
      ext := extSMLS lo mid child sl
      extract := fun {c x _} hok hreach _ hE hB _ ↦ by
        obtain ⟨h₁, cl, ⟨ρ, r, res⟩, ⟨t, rfl⟩, hpre, hg⟩ := hE
        obtain ⟨q, hq, hdec⟩ := decode_SMHL (lo x) (hlo x) (hsh.noCommit x) hpre hg (reachable_commit_ws hreach) hB
        have hd : mainDataM mid x (h₁ ++ t) = some (r.1.folds, res) := by
          unfold mainDataM
          rw [VerifierProgram.retSplit_of_after _ _ _ hpre]
        dsimp only at hdec
        unfold extSMLS
        rw [hd, Option.bind_some]
        dsimp only
        rw [hdec, Option.getD_some]
        exact hnode c x q hok hq }

variable (f : SFmt) {VS : SProg} {vk : RecursionFast.Digest}

/-- **`kcertSMWτ` at S2GS** (the same construction over `schemeSWS`). -/
noncomputable def kcertSMWSτ {τ : ℝ≥0∞} (hmid : MidSpecMτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hLm : Lm ≤ εS)
    (hsh : MidShapeM mid) (X : ExtJMS mid Good VS vk) : KCert (schemeSWS f vk (PSWithM mid)) (Rel (accV VS vk)) :=
  kcertOfInv (S := schemeSWS f vk (PSWithM mid)) (εI := 7 * (2 : ℝ≥0)⁻¹ ^ 131) (εL := (2 : ℝ≥0)⁻¹ ^ 132)
    (Ext := ExtIM mid Good)
    (fun x ↦ (psInvMτ hmid hτ hLm hsh x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) coe_εS.ge le_rfl le_rfl)
    zero_le (fun x _ hr ↦ NoGrind.reach_grindBits (ng_PSWithM hsh.noGrind x) hr)
    X.BL X.BL_nil X.BL_read X.BL_commit X.BL_group
    (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) X.ext X.extract

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertSMWSτ {τ : ℝ≥0∞} (hmid : MidSpecMτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hLm : Lm ≤ εS)
    (hsh : MidShapeM mid) (X : ExtJMS mid Good VS vk) :
    Scheme.εFS (kcertSMWSτ f hmid hτ hLm hsh X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  Scheme.εFS_le_of _ (by
    show (0 : ℝ≥0) + (7 * (2 : ℝ≥0)⁻¹ ^ 131 + (2 : ℝ≥0)⁻¹ ^ 132) + (2 : ℝ≥0)⁻¹ ^ 139 ≤ (2 : ℝ≥0)⁻¹ ^ 128
    rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **M′'s open obligations at a format, S2GS** (`OpenSMW` over `schemeSWS`, the right leaf from the window). -/
structure OpenSMWS (VS : SProg) (E : Digest → Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  τ : ℝ≥0∞ := εS
  hτ : leadOpenM ≤ τ := by exact leadOpenM_le_εS
  hmid : MidSpecMτ mid Good εS Lm τ
  hLm : Lm ≤ εS
  hsh : MidShapeM mid
  child : List UInt8 → List BF64 → Signed
  sl : List UInt8 → List BF64 → Sig
  lo : List UInt8 → ℕ := fun _ ↦ Lvm.X.winLo
  hlo : ∀ x, lo x + Lvm.X.winC ≤ 64 := by intro; decide
  hnode : ∀ vk, NodeSoundMLS lo VS vk Good child sl
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeSWS f vk (PSWithM mid)).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSMWSτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))) L < 1 →
    ((schemeSWS f vk (PSWithM mid)).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeSWS f vk (PSWithM mid)).Ex
        (kcertSMWSτ f hmid hτ hLm hsh (extJMLS lo hlo hsh (hnode vk))).ext c π L

/-- **`SSound` from M′'s open obligations at S2GS.** -/
theorem sSound_of_openSMWS {E : Digest → Proof → Log → Option Wit} (o : OpenSMWS f VS E) (vk : Digest) :
    SSound VS E vk :=
  ⟨schemeSWS f vk (PSWithM o.mid), kcertSMWSτ f o.hmid o.hτ o.hLm o.hsh (extJMLS o.lo o.hlo o.hsh (o.hnode vk)),
    εFS_kcertSMWSτ f o.hmid o.hτ o.hLm o.hsh (extJMLS o.lo o.hlo o.hsh (o.hnode vk)), o.refines vk,
    fun L c π hS hl hμ hv ↦ o.ext_eq vk L c π hS hl hμ hv⟩

end Chain

/-- **`NodeSoundS` from its halves**: the chain for both flags, the left child's acceptance and the right leaf's
signature (the node circuit's second walk, not `okS`) for `b = 1`. -/
theorem nodeSoundS_of {VS : SProg} {vk : Digest} {Good : GoodRel} {child : LeanVM.Protocol.Column 19 → Signed}
    {sl : List UInt8 → LeanVM.Protocol.Column CMain.nu20 → Sig}
    (hchain : ∀ c x qm qr, okSL vk c x = true → Good x qm qr →
      chainEnd (hdrOf x).s (hdrOf x).n = (hdrOf x).h)
    (hleft : ∀ c x qm qr, okSL vk c x = true → (hdrOf x).b = 1 → Good x qm qr →
      accV VS vk (hdrOf x).cL (child qr) = true)
    (hright : ∀ c x qm qr, okSL vk c x = true → (hdrOf x).b = 1 → Good x qm qr →
      SigOk vk (traceDigest []) (sl x qm) = true) :
    NodeSoundS VS vk Good child sl := by
  intro c x qm qr hok hG
  have hch := hchain c x qm qr hok hG
  have hl := fun h1 => hleft c x qm qr hok h1 hG
  have hr := fun h1 => hright c x qm qr hok h1 hG
  have hok' := hok
  unfold okSL at hok'
  unfold witOfL
  generalize sl x qm = σ at hr ⊢
  generalize hdrOf x = hd at hok' hch hl hr ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨hb, -⟩, -⟩, hnc⟩, hrest⟩ := hok'
  by_cases h0 : hd.b = 0
  · simp only [h0, if_true, decide_eq_true_eq] at hrest ⊢
    exact ⟨hnc, by rw [hrest, hch]⟩
  · have h1 : hd.b = 1 := hb.resolve_left h0
    simp only [h0, if_false, decide_eq_true_eq] at hrest ⊢
    exact ⟨hrest, hl h1, Lvm.NS.accV_right VS vk _ hnc hch (hr h1)⟩

end Lvm.ASM

namespace Lvm.E2F

open RecursionFast Lvm.FS Lvm.T Lvm.ASM
open LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
  {Lm : ℝ≥0∞} (f : SFmt)

/-- **`kcertSFWτ` at S2GS.** -/
noncomputable def kcertSFWSτ {τ : ℝ≥0∞} (hm : MidSpecPinτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hsh : MidShapeM mid)
    (hL : leadP Lm ≤ εS) {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJMS (midP mid) Good VS vk) :
    KCert (schemeSWS f vk (PSWithM (midP mid))) (Rel (accV VS vk)) :=
  kcertSMWSτ f (midSpecP_ofτ hm hsh hL) hτ hL (midShapeP_of hsh) X

/-- **S1's open obligations at a format, S2GS** (`OpenSFW` over `schemeSWS`, the right leaf from the window). -/
structure OpenSFWS (VS : SProg) (E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  τ : ℝ≥0∞ := εS
  hτ : leadOpenM ≤ τ := by exact leadOpenM_le_εS
  hmid : MidSpecPinτ mid Good εS Lm τ
  hsh : MidShapeM mid
  hL : leadP Lm ≤ εS
  child : List UInt8 → List BF64 → Signed
  sl : List UInt8 → List BF64 → Sig
  lo : List UInt8 → ℕ := fun _ ↦ Lvm.X.winLo
  hlo : ∀ x, lo x + Lvm.X.winC ≤ 64 := by intro; decide
  hnode : ∀ vk, NodeSoundMLS lo VS vk Good child sl
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeSWS f vk (PSWithM (midP mid))).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSFWSτ f hmid hτ hsh hL (extJMLS lo hlo (midShapeP_of hsh) (hnode vk))) L < 1 →
    ((schemeSWS f vk (PSWithM (midP mid))).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeSWS f vk (PSWithM (midP mid))).Ex
        (kcertSFWSτ f hmid hτ hsh hL (extJMLS lo hlo (midShapeP_of hsh) (hnode vk))).ext c π L

/-- **`OpenSFWS` is `OpenSMWS` at the pinned middle phases.** -/
noncomputable def openSFWS {VS : SProg} {E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit}
    (o : OpenSFWS f VS E) : OpenSMWS f VS E where
  mid := midP o.mid
  Good := o.Good
  Lm := leadP o.Lm
  τ := o.τ
  hτ := o.hτ
  hmid := midSpecP_ofτ o.hmid o.hsh o.hL
  hLm := o.hL
  hsh := midShapeP_of o.hsh
  child := o.child
  sl := o.sl
  lo := o.lo
  hlo := o.hlo
  hnode := o.hnode
  refines := o.refines
  ext_eq := o.ext_eq

end Lvm.E2F

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.E2F
open scoped NNReal ENNReal

/-- **The certificate from the open obligations at a format, S2GS** (`certificateR_openW` over `OpenSMWS`). -/
theorem certificateR_openWS (f : SFmt) (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (X : ExtF20) (o : OpenSMWS f VS X.E) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS X.E X.ext) :=
  certificateR_claim VS _ X.ext
    ⟨fun H vk c π _ ↦ hq H vk c π, X.computes, X.size, X.W, sSound_of_openSMWS f o⟩

end Lvm.CT
