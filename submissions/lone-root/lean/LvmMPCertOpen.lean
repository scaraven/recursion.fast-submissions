-- New for lvm2 roll 11 (M′, R11-C): `C_main`'s Johnson opening in the invariant with one commitment, generic
-- in the predicate that records the good residual (`LvmMPCert`'s `ExtIM`). Adapted from `LvmCertSOpenJ`
-- (`stackedPrefixRec20JpSpecS`, `finSuffixRec20JpSpecS`, `recSuffixInv`, `recInvSpec`, `rootsInv`).
import LvmCertSOpenJ

/-!
# M′'s opening in the invariant

M′ commits one root (`C_main`, `cfgMain23Jq 1`: `(6,2,115)(4,3,77)(4,4,58)`, OOD, `g = 14`, root `0` of `1`).

* `stackedPrefixMainSpecS`: JB-L's relativised prefix (`stackedPrefixSpecR`) at `codesMain23Jq`, every group
  within `εS` (`whirEps_main23Jq`'s margin), follower's allowance the final query group `finLeadJ`;
* `finSuffixMainSpecS`: the final level `(4,4,58)` (index `2`, `codeJ9R4`, `10` fold challenges before it)
  rejects from the residual's doom `ResC` (`finSuffixSpecR`);
* **`mainInvSpec`**: the whole opening from `StackedPreR` and a predicate `J` of the start: every group
  within `εS`, lead the batching `eBatch`; a completed run has `M`, for any append-stable `M` that a good
  residual (`PostR`'s left disjunct) after a `J` start gives;
* `rootInvM`: the root from the empty history, the run recorded; `RunMidM`, `mainPrefixProg_afterM`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped NNReal ENNReal

/-! ## The opening at `εS` -/

/-- **M′'s `C_main` opening up to the residual, relativised, at `εS`** (`stackedPrefixSpecR` at
`codesMain23Jq`, `whirEps_main23Jq`'s margin through `le_εS_of_margin`). -/
noncomputable def stackedPrefixMainSpecS (Gd : LeanVM.Protocol.Column CMain.nu20 → Prop)
    (claims : List LeanVM.Protocol.Verifier.StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine CMain.nu20 c.1) :
    Spec (stackPrefixJ (cfgMain23Jq 1) claims)
      (fun h ↦ StackedPreR (cfgMain23Jq 1).toUdConfig (codesMain23Jq 0) Gd claims (commits h))
      (fun a h ↦ PostR (cfgMain23Jq 1).μ LeanVM.Protocol.EndToEnd.laneBits
        (fun point ↦ LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers a.1 claims.length)
          (claims.map fun c ↦ c.1 point)) codesMain23Jq
        (cfgMain23Jq 1).c₀ (cfgMain23Jq 1).n₀ 0 0 (cfgMain23Jq 1).levels
        (gdRoot (codesMain23Jq 0) Gd (viewC (cfgMain23Jq 1).c₀ (cfgMain23Jq 1).n₀ (commits h))) a.2 h)
      εS (eBatch claims.length (codesMain23Jq 0)) (finLeadJ codesMain23Jq 14 0 (cfgMain23Jq 1).levels) :=
  stackedPrefixSpecR Gd claims hcl rfl rfl (by norm_num [cfgMain23Jq]) rfl
    (by norm_num [cfgMain23Jq]) (by norm_num [cfgMain23Jq]) (by norm_num [cfgMain23Jq])
    (ladderArith_main23Jq 1) (le_εS_of_margin (whirEps_main23Jq 1))

/-- **M′'s `C_main` after the residual at `εS`**: the final level `(4,4,58)` (index `2`, `codeJ9R4`, `10`
fold challenges before it) rejects from `ResC`. -/
noncomputable def finSuffixMainSpecS (w : List E → E) (hw : IsMultiaffine CMain.nu20 w)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ CMain.nu20 LeanVM.Protocol.EndToEnd.laneBits 8 0 1 14 false w 2 ⟨4, 4, 58⟩ a)
      (fun h ↦ ResC CMain.nu20 LeanVM.Protocol.EndToEnd.laneBits w 2 codeJ9R4 4 10 a.1 a.2
        (viewC 0 1 (commits h)))
      (fun _ _ ↦ False) εS ((2 : ℝ≥0∞)⁻¹ ^ 14 * eQueryFinal codeJ9R4 58) 0 :=
  finSuffixSpecR (level := ⟨4, 4, 58⟩) ⟨hw, by norm_num, by norm_num [codeJ9R4], rfl, by norm_num,
      by norm_num, by norm_num [codeJ9R4]⟩ (by norm_num)
    (eps_main23Jq.2.2.2.2.2.2.2.trans_lt seven_inv_lt_one) (disc7 eps_main23Jq.2.2.2.2.2.2.2)
    (le_seven_of (by norm_num) eTail_le) a

/-! ## The opening in the invariant -/

section Inv

variable (Gd : LeanVM.Protocol.Column CMain.nu20 → Prop) (M J : List Ev → Prop)
  (cl : List LeanVM.Protocol.Verifier.StackClaim)

/-- **The good residual after a start `h₀`** (`PostR`'s left disjunct at `cfgMain23Jq 1`, final level `2`). -/
def GoodResM (a : E × ((WhirStateT × List E) × List E)) (h : List Ev) : Prop :=
  GoodRes (codesMain23Jq 2) 2
    (gdFinal codesMain23Jq (viewC 0 1 (commits h)) a.2.1.1.folds 0 0 (cfgMain23Jq 1).levels
      (gdRoot (codesMain23Jq 0) Gd (viewC 0 1 (commits h))))
    a.2.1 a.2.2 (viewC 0 1 (commits h))

variable {Gd M J cl}

/-- The traced prefix's post gives the residual's doom or `M`. -/
theorem resC_or_M (hext : ∀ a h₀ l, J h₀ → (stackPrefixJ (cfgMain23Jq 1) cl).after l = some (.ret a) →
      GoodResM Gd a (h₀ ++ l) → M (h₀ ++ l))
    (a : E × ((WhirStateT × List E) × List E)) {h : List Ev}
    (hp : PostR (cfgMain23Jq 1).μ LeanVM.Protocol.EndToEnd.laneBits
        (fun point ↦ LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers a.1 cl.length)
          (cl.map fun c ↦ c.1 point)) codesMain23Jq
        (cfgMain23Jq 1).c₀ (cfgMain23Jq 1).n₀ 0 0 (cfgMain23Jq 1).levels
        (gdRoot (codesMain23Jq 0) Gd (viewC (cfgMain23Jq 1).c₀ (cfgMain23Jq 1).n₀ (commits h))) a.2 h ∧
      ∃ h₀ l, h = h₀ ++ l ∧ J h₀ ∧ (stackPrefixJ (cfgMain23Jq 1) cl).after l = some (.ret a)) :
    ResC CMain.nu20 LeanVM.Protocol.EndToEnd.laneBits
        (fun point ↦ LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers a.1 cl.length)
          (cl.map fun c ↦ c.1 point)) 2 codeJ9R4 4 10 a.2.1 a.2.2 (viewC 0 1 (commits h)) ∨ M h := by
  obtain ⟨hg | hres, h₀, l, rfl, hJ, ha⟩ := hp
  · exact .inr (hext a h₀ l hJ ha hg)
  · exact .inl hres

/-- `C_main`'s suffix in the invariant: from the residual's doom it rejects, `M` is carried to the end. -/
noncomputable def mainSuffixInv (hMa : ∀ h l, M h → M (h ++ l))
    (hext : ∀ a h₀ l, J h₀ → (stackPrefixJ (cfgMain23Jq 1) cl).after l = some (.ret a) →
      GoodResM Gd a (h₀ ++ l) → M (h₀ ++ l))
    (hcl : ∀ c ∈ cl, IsMultiaffine CMain.nu20 c.1) (a : E × ((WhirStateT × List E) × List E)) :
    Spec (stackSuffixJ (cfgMain23Jq 1) cl (List.cons_ne_nil _ _) a)
      (fun h ↦ PostR (cfgMain23Jq 1).μ LeanVM.Protocol.EndToEnd.laneBits
        (fun point ↦ LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers a.1 cl.length)
          (cl.map fun c ↦ c.1 point)) codesMain23Jq
        (cfgMain23Jq 1).c₀ (cfgMain23Jq 1).n₀ 0 0 (cfgMain23Jq 1).levels
        (gdRoot (codesMain23Jq 0) Gd (viewC (cfgMain23Jq 1).c₀ (cfgMain23Jq 1).n₀ (commits h))) a.2 h ∧
      ∃ h₀ l, h = h₀ ++ l ∧ J h₀ ∧ (stackPrefixJ (cfgMain23Jq 1) cl).after l = some (.ret a))
      (fun _ h ↦ M h) εS (finLeadJ codesMain23Jq 14 0 (cfgMain23Jq 1).levels) 0 :=
  ((((finSuffixMainSpecS _ (isMultiaffine_batched cl hcl a.1) a.2).liftT 0).orStable
      (M := M) (fun _ l _ hM ↦ hMa _ l hM) zero_le).congr
      rfl).mono (fun _ hp ↦ resC_or_M hext a hp) (fun _ _ h ↦ h) le_rfl (max_le le_rfl zero_le) le_rfl

/-- **`C_main`'s opening in the invariant** (M′): from `StackedPreR` for the good set `Gd` and `J`, every
group within `εS`, lead `eBatch`; a completed run has `M`. -/
noncomputable def mainInvSpec (hMa : ∀ h l, M h → M (h ++ l))
    (hext : ∀ a h₀ l, J h₀ → (stackPrefixJ (cfgMain23Jq 1) cl).after l = some (.ret a) →
      GoodResM Gd a (h₀ ++ l) → M (h₀ ++ l))
    (hcl : ∀ c ∈ cl, IsMultiaffine CMain.nu20 c.1) :
    Spec (verifyStackedJ (cfgMain23Jq 1) cl)
      (fun h ↦ StackedPreR (cfgMain23Jq 1).toUdConfig (codesMain23Jq 0) Gd cl (commits h) ∧ J h)
      (fun _ h ↦ M h) εS (eBatch cl.length (codesMain23Jq 0)) 0 :=
  (((stackedPrefixMainSpecS Gd cl hcl).traced J).bind (mainSuffixInv hMa hext hcl)).congr
    (verifyStackedJ_eq_prefix (cfgMain23Jq 1) rfl (List.cons_ne_nil _ _) cl).symm

open Classical in
/-- **The opening and `true` in the invariant** (M′): from `StackedPreR`, multiaffine claims, at most
`2^40` of them, and `J`, every group within `εS`, lead `εS`; an accepting return has `M`. -/
noncomputable def mainOpenInv (hMa : ∀ h l, M h → M (h ++ l))
    (hext : ∀ a h₀ l, J h₀ → (stackPrefixJ (cfgMain23Jq 1) cl).after l = some (.ret a) →
      GoodResM Gd a (h₀ ++ l) → M (h₀ ++ l)) :
    Spec (verifyStackedJ (cfgMain23Jq 1) cl >>= fun _ ↦ VerifierProgram.ret true)
      (fun h ↦ (StackedPreR (cfgMain23Jq 1).toUdConfig (codesMain23Jq 0) Gd cl (commits h) ∧
        (∀ c ∈ cl, IsMultiaffine CMain.nu20 c.1) ∧ cl.length ≤ 2 ^ 40) ∧ J h)
      (fun b h ↦ b = true → M h) εS εS 0 :=
  if hside : (∀ c ∈ cl, IsMultiaffine CMain.nu20 c.1) ∧ cl.length ≤ 2 ^ 40 then
    ((mainInvSpec hMa hext hside.1).bind' fun _ ↦
      ((Spec.ret (Post := fun b h ↦ b = true → M h) (εmax := εS) (T := 0) true).mono
        (fun _ h _ ↦ h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl :
        Spec (VerifierProgram.ret true) (fun h ↦ M h) (fun b h ↦ b = true → M h) εS 0 0)).mono
      (fun _ hp ↦ ⟨hp.1.1, hp.2⟩) (fun _ _ h ↦ h) le_rfl (eBatch_main23Jq _ hside.2) le_rfl
  else Spec.dead.mono (fun _ hp ↦ hside hp.1.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Inv

/-! ## The good residual, unfolded -/

/-- **M′'s good residual, unfolded** (`LvmMPCert`'s `goodRes_main23Jq`, three levels; as `goodRes_rec20Jp`). -/
theorem goodRes_main23JqH {G : LeanVM.Protocol.Column CMain.nu20 → Prop} {cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)}
    {r : WhirStateT × List E} {res : List E} (α₀ : Fin 6 → E) (α₁ α₂ : Fin 4 → E)
    (hfs : r.1.folds = List.ofFn α₀ ++ List.ofFn α₁ ++ List.ofFn α₂)
    (hG : GoodRes (codesMain23Jq 2) 2
      (gdFinal codesMain23Jq cs r.1.folds 0 0 (cfgMain23Jq 1).levels (gdRoot (codesMain23Jq 0) G cs))
      r res cs) :
    ∃ q ∈ Candidates CMain.nu20 2 (codesMain23Jq 0).thr (wordOf cs 0), G q ∧
      (∃ V₁ ∈ LeanVM.Protocol.Whir.iList (codesMain23Jq 1).code (codesMain23Jq 1).thr
          (rowsOf 4 (laneO 1 cs (codesMain23Jq 1).n)),
        PathAt q (List.ofFn α₀) (decode (codesMain23Jq 1) V₁)) ∧
      (∃ V₂ ∈ LeanVM.Protocol.Whir.iList (codesMain23Jq 2).code (codesMain23Jq 2).thr
          (rowsOf 4 (laneO 2 cs (codesMain23Jq 2).n)),
        PathAt q (List.ofFn α₀ ++ List.ofFn α₁) (decode (codesMain23Jq 2) V₂)) ∧
      (∀ y : Fin (codesMain23Jq 2).κ → Bool,
        resMsg res y = qMle q (List.ofFn α₀ ++ List.ofFn α₁ ++ List.ofFn α₂ ++ bitsL y)) := by
  obtain ⟨-, q, hq, hpath⟩ := hG
  have h6 : r.1.folds.take (0 + 6) = List.ofFn α₀ := by rw [hfs]; simp
  have h10 : r.1.folds.take (0 + 6 + 4) = List.ofFn α₀ ++ List.ofFn α₁ := by rw [hfs]; simp
  have hq' : ((q ∈ Candidates CMain.nu20 2 (codesMain23Jq 0).thr (wordOf cs 0) ∧ G q) ∧
      ConsAt (codesMain23Jq 1) 4 1 cs (r.1.folds.take (0 + 6)) q) ∧
      ConsAt (codesMain23Jq 2) 4 2 cs (r.1.folds.take (0 + 6 + 4)) q := hq
  rw [h6, h10] at hq'
  obtain ⟨⟨⟨hcand, hgood⟩, hc1⟩, hc2⟩ := hq'
  refine ⟨q, hcand, hgood, hc1, hc2, fun y ↦ ?_⟩
  rw [hpath y, hfs]

/-! ## No proof of work outside the query groups -/

section NG

attribute [local irreducible] verifyStackedJ

/-- **`P_S` at M′ grinds nothing outside its query groups** (the program of `LvmMPCert`'s `PSWithM`). -/
theorem ng_PSWithMH {β : Type} {mid : β → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)}
    (hm : ∀ x, (mid x).NoGrind) (x : β) :
    ((commitRootUd cfgMain24G).bind fun _ ↦ (mid x).bind fun cl ↦
      (verifyStackedJ (cfgMain23Jq 1) cl).bind fun _ ↦ VerifierProgram.ret true).NoGrind :=
  VerifierProgram.NoGrind.bind (ng_commitRootUd cfgMain24G) fun _ ↦ VerifierProgram.NoGrind.bind (hm x)
    fun cl ↦ VerifierProgram.NoGrind.bind (ng_stackedJ (cfgMain23Jq 1) cl) fun _ ↦ ng_ret _

end NG

/-! ## The root and the run -/

/-- **The root from the empty history**, the run recorded: post the root's shape and that the history is a
completed run of the root commitment. -/
noncomputable def rootInvM {T : ℝ≥0∞} (hT : T ≤ εS) :
    Spec (commitRootUd cfgMain24G) (fun h ↦ h = [])
      (fun _ h ↦ (∃ W, commits h = [(19, 64, W)] ∧ WellShaped 64 W) ∧
        (commitRootUd cfgMain24G).after h = some (.ret ())) εS 0 T :=
  (((Spec.commitP (Pre := fun h ↦ h = [])
      (Post := fun _ h ↦ ∃ W, commits h = [(19, 64, W)] ∧ WellShaped 64 W) (εmax := εS) 19 64
      (fun _ w hh hw ↦ ⟨w, by rw [hh]; rfl, hw⟩) hT).congr rfl).traced
    (fun h ↦ h = [])).mono (fun _ h ↦ ⟨h, h⟩)
    (fun _ _ ⟨hR, h₀, l, he, h0, hl⟩ ↦ ⟨hR, by rw [he, h0, List.nil_append]; exact hl⟩) le_rfl le_rfl
    le_rfl

/-- **The root then the middle phases** (M′): `h` is a completed run of the root commitment followed by a
completed run of `mid x` returning `cl`. -/
def RunMidM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8)
    (cl : List LeanVM.Protocol.Verifier.StackClaim) (h : List Ev) : Prop :=
  ∃ hr lm, h = hr ++ lm ∧ (commitRootUd cfgMain24G).after hr = some (.ret ()) ∧
    (mid x).after lm = some (.ret cl)

/-- A completed run of the root, the middle phases and `C_main`'s prefix is a completed run of the program
up to the residual (`LvmMPCert`'s `mainPrefixProg`). -/
theorem mainPrefixProg_afterM {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)}
    {x : List UInt8} {cl : List LeanVM.Protocol.Verifier.StackClaim} {h₀ l : List Ev}
    {a : E × ((WhirStateT × List E) × List E)} (hr : RunMidM mid x cl h₀)
    (ha : (stackPrefixJ (cfgMain23Jq 1) cl).after l = some (.ret a)) :
    (commitRootUd cfgMain24G >>= fun _ ↦ mid x >>= fun cl ↦
      stackPrefixJ (cfgMain23Jq 1) cl >>= fun a ↦ VerifierProgram.ret (cl, a)).after (h₀ ++ l) =
      some (.ret (cl, a)) := by
  obtain ⟨hr, lm, rfl, h1, h2⟩ := hr
  rw [List.append_assoc]
  show ((commitRootUd cfgMain24G).bind fun _ ↦
    (mid x).bind fun cl ↦ (stackPrefixJ (cfgMain23Jq 1) cl).bind fun a ↦ .ret (cl, a)).after _ = _
  rw [VerifierProgram.after_bind_append _ h1, VerifierProgram.after_bind_append _ h2, ← List.append_nil l,
    VerifierProgram.after_bind_append _ ha]
  rfl

end Lvm.ASM
