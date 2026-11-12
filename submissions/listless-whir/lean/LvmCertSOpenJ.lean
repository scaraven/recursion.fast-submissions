-- New for lvm2 (J2C-B, J2′): the openings and `P_S` under the INV certificate (J2C-DES §3 T4–T6). Statements
-- written at G0 by the lead; the proofs are J2C-B's.
import LvmCertSNo
import LvmCertSInv
import LvmCertSFrameJ
import LvmWhirSpecR
import LvmWhirSuffixR

/-!
# The openings and `P_S` in the invariant (J2C-DES §1 items 3–5, §3 T4–T6)

* **`openPostR_split`**: `OpenPostR` splits into "every non-`GoodRec` member of `C_rec`'s list fails a `C_rec`
  claim" (`StackedPreR`) or "every `C_main` candidate fails a `C_main` claim" (`MainPre`).
* **`recInvSpec`**: `C_rec`'s Johnson opening (`verifyStackedJ cfgRec20Jp`) from `StackedPreR` and the run so
  far: JB-L's `stackedPrefixSpecR` (traced), then at the residual `GoodResAt` (carried as `ExtI`) or `ResC`
  (`finSuffixSpecR`, lifted by `Spec.liftT`); post `ExtI`.
* **`openInv`**: both openings from `OpenPostR` and the run so far; `MainPre` is carried across `C_rec`'s
  opening (`Spec.orPost`), `C_main`'s `stackedMain24JSpecS` rejects, `ExtI` is carried across it (`orStable`).
* **`psInv`**: `P_S` from the empty history, post "accept → `ExtI`", every group at most `εS`, lead `0`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped NNReal ENNReal

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {x : List UInt8}

/-! ## The numbers -/

/-- `2^-c ≤ N / M` from `M ≤ N · 2^c`. -/
theorem inv_pow_le_natCast_div {N M c : ℕ} (hM : 0 < M) (h : M ≤ N * 2 ^ c) :
    (2 : ℝ≥0∞)⁻¹ ^ c ≤ (N : ℝ≥0∞) / M := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hM.ne')) (Or.inl (ENNReal.natCast_ne_top M))]
  calc (2 : ℝ≥0∞)⁻¹ ^ c * M ≤ (2 : ℝ≥0∞)⁻¹ ^ c * ((N : ℝ≥0∞) * 2 ^ c) := by gcongr; exact_mod_cast h
    _ = N := by
      rw [mul_comm (N : ℝ≥0∞), ← mul_assoc, ← mul_pow,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

/-- **`C_rec`'s batching at the Johnson list bound** (`L = 304`): `(J − 1)·304/|E| ≤ εS` for at most
`2^55` claims (it is `2^-128.75`). -/
theorem eBatch_rec20Jp (J : ℕ) (hJ : J ≤ 2 ^ 55) : eBatch J (codesRec20Jp 0) ≤ εS := by
  unfold eBatch
  rw [card_E_ennreal, ← two_pow_cast 192, show (codesRec20Jp 0).listMax = 304 from rfl]
  refine (natCast_div_le_mul_inv_pow (k := 7) (c := 131) ?_).trans_eq (by rw [Nat.cast_ofNat])
  calc (J - 1) * 304 * 2 ^ 131 ≤ 2 ^ 55 * 304 * 2 ^ 131 := by gcongr; exact (Nat.sub_le J 1).trans hJ
    _ ≤ 7 * 2 ^ 192 := by norm_num

/-- `C_rec`'s final query group is at least `2^-145` (`2^-14·((1450/4096)^77)`, its first term). -/
theorem inv_pow_145_le_finLead : (2 : ℝ≥0∞)⁻¹ ^ 145 ≤ finLeadJ codesRec20Jp 14 0 cfgRec20Jp.levels := by
  show (2 : ℝ≥0∞)⁻¹ ^ 145 ≤ (2 : ℝ≥0∞)⁻¹ ^ 14 * eQueryFinal codeJ9R3 77
  rw [show (145 : ℕ) = 14 + 131 from rfl, pow_add]
  refine mul_le_mul' le_rfl ?_
  unfold eQueryFinal
  refine le_trans ?_ le_self_add
  rw [natCast_div_pow]
  exact inv_pow_le_natCast_div (by norm_num [codeJ9R3, LevelCode.n]) (by norm_num [codeJ9R3, LevelCode.n])

/-- **`C_main`'s batching fits under `C_rec`'s final query group** (`hT` of `recInvSpec`): for at most
`2^40` claims, `(J − 1)·98/|E| ≤ 2^-145.4 ≤ 2^-14·eQueryFinal(codeJ9R3, 77)`. -/
theorem eBatch_main24J_le_finLead (J : ℕ) (hJ : J ≤ 2 ^ 40) :
    eBatch J (codesMain24J 0) ≤ finLeadJ codesRec20Jp 14 0 cfgRec20Jp.levels := by
  refine le_trans ?_ inv_pow_145_le_finLead
  unfold eBatch
  rw [card_E_ennreal, ← two_pow_cast 192, show (codesMain24J 0).listMax = 98 from rfl]
  refine natCast_div_le_inv_pow (by positivity) ?_
  calc (J - 1) * 98 * 2 ^ 145 ≤ 2 ^ 40 * 98 * 2 ^ 145 := by gcongr; exact (Nat.sub_le J 1).trans hJ
    _ ≤ 2 ^ 192 := by norm_num

/-- `C_rec`'s final query group is within `εS`. -/
theorem finLead_rec20Jp_le : finLeadJ codesRec20Jp 14 0 cfgRec20Jp.levels ≤ εS :=
  disc7 eps_rec20Jp.2.2.2.2

/-! ## `C_rec`'s Johnson opening at `εS` -/

/-- **J2′'s `C_rec` opening up to the residual, relativised, at `εS`** (`stackedPrefixRec20JpSpec` with
`whirEps_rec20Jp`'s margin through `le_εS_of_margin`). -/
noncomputable def stackedPrefixRec20JpSpecS (Gd : LeanVM.Protocol.Column 19 → Prop)
    (claims : List LeanVM.Protocol.Verifier.StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine 19 c.1) :
    Spec (stackPrefixJ cfgRec20Jp claims)
      (fun h ↦ StackedPreR cfgRec20Jp.toUdConfig (codesRec20Jp 0) Gd claims (commits h))
      (fun a h ↦ PostR cfgRec20Jp.μ LeanVM.Protocol.EndToEnd.laneBits
        (fun point ↦ LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers a.1 claims.length) (claims.map fun c ↦ c.1 point)) codesRec20Jp
        cfgRec20Jp.c₀ cfgRec20Jp.n₀ 0 0 cfgRec20Jp.levels
        (gdRoot (codesRec20Jp 0) Gd (viewC cfgRec20Jp.c₀ cfgRec20Jp.n₀ (commits h))) a.2 h)
      εS (eBatch claims.length (codesRec20Jp 0)) (finLeadJ codesRec20Jp 14 0 cfgRec20Jp.levels) :=
  stackedPrefixSpecR Gd claims hcl rfl rfl (by norm_num [cfgRec20Jp]) rfl
    (by norm_num [cfgRec20Jp]) (by norm_num [cfgRec20Jp]) (by norm_num [cfgRec20Jp])
    ladderArith_rec20Jp (le_εS_of_margin whirEps_rec20Jp)

/-- **J2′'s `C_rec` after the residual at `εS`** (`finSuffixRec20JpSpec` at the exact budget). -/
noncomputable def finSuffixRec20JpSpecS (w : List E → E) (hw : IsMultiaffine 19 w)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ 19 LeanVM.Protocol.EndToEnd.laneBits 8 1 2 14 false w 1 ⟨4, 3, 77⟩ a)
      (fun h ↦ ResC 19 LeanVM.Protocol.EndToEnd.laneBits w 1 codeJ9R3 4 6 a.1 a.2 (viewC 1 2 (commits h)))
      (fun _ _ ↦ False) εS ((2 : ℝ≥0∞)⁻¹ ^ 14 * eQueryFinal codeJ9R3 77) 0 :=
  finSuffixSpecR (level := ⟨4, 3, 77⟩) ⟨hw, by norm_num, by norm_num [codeJ9R3], rfl, by norm_num,
      by norm_num, by norm_num [codeJ9R3]⟩ (by norm_num)
    (eps_rec20Jp.2.2.2.2.trans_lt seven_inv_lt_one) (disc7 eps_rec20Jp.2.2.2.2)
    (le_seven_of (by norm_num) eTail_le) a

/-! ## The split (T4) -/

/-- **The openings' precondition splits** at the Johnson threshold (J2C-DES T4): if `candPairs` reads
`C_rec`'s list at `(codesRec20Jp 0).thr` (J2C-A's `thrRec`), either every non-`GoodRec` member of
`C_rec`'s list fails a `C_rec` claim, or some non-`GoodRec` member meets them all, and then every
`C_main` candidate fails a `C_main` claim (each pair with it is non-good). -/
theorem openPostR_split_of (hthr : thrRec = (codesRec20Jp 0).thr) {cl : OpenClaims} {h : List Ev}
    (hp : OpenPostR Good x cl h) :
    StackedPreR cfgRec20Jp.toUdConfig (codesRec20Jp 0) (GoodRec Good x) cl.1 (commits h) ∨
      MainPre cl.2 (commits h) := by
  obtain ⟨hpairs, ⟨Wm, Wr, hc, hWm, hWr⟩, -⟩ := hp
  by_cases hr : ∀ q ∈ Candidates 19 2 (codesRec20Jp 0).thr (wordOf (commits h) 1),
      ¬ GoodRec Good x q → ∃ c ∈ cl.1, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c q
  · left
    exact ⟨by decide, by rw [hc]; rfl, ⟨Wr, by rw [hc]; rfl, hWr⟩, hr⟩
  · right
    push Not at hr
    obtain ⟨qr, hqr, hng, hall⟩ := hr
    refine ⟨by rw [hc]; rfl, ⟨Wm, by rw [hc]; rfl, hWm⟩, fun qm hqm => ?_⟩
    rcases hpairs (qm, qr) ⟨hqm, by rw [hthr]; exact hqr⟩ (fun hg ↦ hng ⟨qm, hg⟩) with
      ⟨c, hc1, hn⟩ | h2
    · exact absurd (hall c hc1) hn
    · exact h2

/-- **The openings' precondition splits** (J2C-DES T4). -/
theorem openPostR_split {cl : OpenClaims} {h : List Ev} (hp : OpenPostR Good x cl h) :
    StackedPreR cfgRec20Jp.toUdConfig (codesRec20Jp 0) (GoodRec Good x) cl.1 (commits h) ∨
      MainPre cl.2 (commits h) :=
  openPostR_split_of thrRec_eq hp

/-! ## `C_rec`'s opening in the invariant (T5) -/

/-- A completed run of the roots, the middle phases and `C_rec`'s prefix is a completed run of
`recPrefixProg`. -/
theorem recPrefixProg_after {cl : OpenClaims} {h₀ l : List Ev}
    {a : E × ((WhirStateT × List E) × List E)} (hr : RunMid mid x cl h₀)
    (ha : (stackPrefixJ cfgRec20Jp cl.1).after l = some (.ret a)) :
    (recPrefixProg mid x).after (h₀ ++ l) = some (.ret (cl, a)) := by
  obtain ⟨hr, lm, rfl, h1, h2⟩ := hr
  rw [List.append_assoc]
  show ((commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G).bind fun _ ↦
    (mid x).bind fun cl ↦ (stackPrefixJ cfgRec20Jp cl.1).bind fun a ↦ .ret (cl, a)).after _ = _
  rw [VerifierProgram.after_bind_append _ h1, VerifierProgram.after_bind_append _ h2, ← List.append_nil l,
    VerifierProgram.after_bind_append _ ha]
  rfl

/-- The post of `C_rec`'s prefix (traced from `RunMid`) gives the residual's doom or `ExtI`. -/
theorem resC_or_extI {cl : OpenClaims} (a : E × ((WhirStateT × List E) × List E)) {h : List Ev}
    (hp : PostR cfgRec20Jp.μ LeanVM.Protocol.EndToEnd.laneBits
        (fun point ↦ LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers a.1 cl.1.length) (cl.1.map fun c ↦ c.1 point)) codesRec20Jp
        cfgRec20Jp.c₀ cfgRec20Jp.n₀ 0 0 cfgRec20Jp.levels
        (gdRoot (codesRec20Jp 0) (GoodRec Good x) (viewC cfgRec20Jp.c₀ cfgRec20Jp.n₀ (commits h))) a.2 h ∧
      ∃ h₀ l, h = h₀ ++ l ∧ RunMid mid x cl h₀ ∧
        (stackPrefixJ cfgRec20Jp cl.1).after l = some (.ret a)) :
    ResC 19 LeanVM.Protocol.EndToEnd.laneBits (fun point ↦ LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers a.1 cl.1.length) (cl.1.map fun c ↦ c.1 point)) 1
        codeJ9R3 4 6 a.2.1 a.2.2 (viewC 1 2 (commits h)) ∨ ExtI mid Good x h := by
  obtain ⟨hg | hres, h₀, l, rfl, hrun, ha⟩ := hp
  · exact .inr ⟨h₀ ++ l, cl, a, List.prefix_refl _, recPrefixProg_after hrun ha, hg⟩
  · exact .inl hres

/-- `C_rec`'s suffix (after the residual) in the invariant: from the residual's doom it rejects, and
`ExtI` is carried to the end. -/
noncomputable def recSuffixInv (cl : OpenClaims) (hcl : ∀ c ∈ cl.1, IsMultiaffine 19 c.1) (T : ℝ≥0∞)
    (hT : T ≤ finLeadJ codesRec20Jp 14 0 cfgRec20Jp.levels) (a : E × ((WhirStateT × List E) × List E)) :
    Spec (stackSuffixJ cfgRec20Jp cl.1 (List.cons_ne_nil _ _) a)
      (fun h ↦ PostR cfgRec20Jp.μ LeanVM.Protocol.EndToEnd.laneBits
        (fun point ↦ LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers a.1 cl.1.length) (cl.1.map fun c ↦ c.1 point)) codesRec20Jp
        cfgRec20Jp.c₀ cfgRec20Jp.n₀ 0 0 cfgRec20Jp.levels
        (gdRoot (codesRec20Jp 0) (GoodRec Good x) (viewC cfgRec20Jp.c₀ cfgRec20Jp.n₀ (commits h))) a.2 h ∧
      ∃ h₀ l, h = h₀ ++ l ∧ RunMid mid x cl h₀ ∧
        (stackPrefixJ cfgRec20Jp cl.1).after l = some (.ret a))
      (fun _ h ↦ ExtI mid Good x h) εS (finLeadJ codesRec20Jp 14 0 cfgRec20Jp.levels) T :=
  ((((finSuffixRec20JpSpecS _ (isMultiaffine_batched cl.1 hcl a.1) a.2).liftT T).orStable
      (M := ExtI mid Good x) (fun _ l _ hM ↦ hM.append l) (hT.trans finLead_rec20Jp_le)).congr
      rfl).mono (fun _ hp ↦ resC_or_extI a hp) (fun _ _ h ↦ h) le_rfl (max_le le_rfl hT) le_rfl

/-- **`C_rec`'s opening in the invariant** (J2C-DES T5): every group at most `εS`, lead the batching
`eBatch J (codesRec20Jp 0)`; a completed run has `ExtI`. -/
noncomputable def recInvSpec (cl : OpenClaims) (hcl : ∀ c ∈ cl.1, IsMultiaffine 19 c.1) (T : ℝ≥0∞)
    (hT : T ≤ finLeadJ codesRec20Jp 14 0 cfgRec20Jp.levels) :
    Spec (verifyStackedJ cfgRec20Jp cl.1)
      (fun h ↦ StackedPreR cfgRec20Jp.toUdConfig (codesRec20Jp 0) (GoodRec Good x) cl.1 (commits h) ∧
        RunMid mid x cl h)
      (fun _ h ↦ ExtI mid Good x h) εS (eBatch cl.1.length (codesRec20Jp 0)) T :=
  (((stackedPrefixRec20JpSpecS (GoodRec Good x) cl.1 hcl).traced (RunMid mid x cl)).bind
    (recSuffixInv cl hcl T hT)).congr
    (verifyStackedJ_eq_prefix cfgRec20Jp rfl (List.cons_ne_nil _ _) cl.1).symm

/-! ## Both openings and `P_S` (T6) -/

open Classical in
/-- **Both openings in the invariant**, for a split of `OpenPostR` (`openPostR_split_of`). -/
noncomputable def openInvOf (hthr : thrRec = (codesRec20Jp 0).thr) (cl : OpenClaims) :
    Spec (openProg cl) (fun h ↦ OpenPostR Good x cl h ∧ RunMid mid x cl h)
      (fun b h ↦ b = true → ExtI mid Good x h) εS εS 0 :=
  if hside : (∀ c ∈ cl.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ cl.2, IsMultiaffine CMain.nu20 c.1) ∧
      cl.1.length ≤ 2 ^ 55 ∧ cl.2.length ≤ 2 ^ 40 then
    have hb1 := eBatch_rec20Jp _ hside.2.2.1
    have hb2 := eBatch_main24J _ hside.2.2.2
    let S1 := (recInvSpec (mid := mid) (Good := Good) (x := x) cl hside.1
        (eBatch cl.2.length (codesMain24J 0)) (eBatch_main24J_le_finLead _ hside.2.2.2)).orPost
      (M := fun h ↦ MainPre cl.2 (commits h))
      (M' := fun h ↦ StackedPreUd (cfgMain24J 3).toUdConfig (codesMain24J 0) cl.2 (commits h))
      (fun _ _ _ _ ha hM ↦ by
        rw [LeanVM.Protocol.Whir.Sound.commits_append]
        exact stackedPreUd_of_mainPre hM (recCommitsOneJ _ ha)) hb2
    let S2 := (((stackedMain24JSpecS cl.2 hside.2.1 0).orStable (M := ExtI mid Good x)
        (fun _ l _ hM ↦ hM.append l) zero_le).mono (fun _ h ↦ h.symm) (fun _ _ h ↦ h) le_rfl
        (max_le le_rfl zero_le) le_rfl).bind' fun _ ↦
      ((Spec.ret (Post := fun b h ↦ b = true → ExtI mid Good x h) (εmax := εS) (T := 0) true).mono
        (fun _ h _ ↦ h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl :
        Spec (VerifierProgram.ret true) (fun h ↦ ExtI mid Good x h)
          (fun b h ↦ b = true → ExtI mid Good x h) εS 0 0)
    (S1.bind' fun _ ↦ S2).mono
      (fun _ hp ↦ (openPostR_split_of hthr hp.1).imp_left fun h ↦ ⟨h, hp.2⟩) (fun _ _ h ↦ h) le_rfl
      (max_le hb1 hb2) le_rfl
  else Spec.dead.mono (fun _ hp ↦ hside hp.1.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **Both openings in the invariant** (J2C-DES T6): from `OpenPostR` and the run so far, every group at
most `εS`, lead `εS`; an accepting return has `ExtI`. -/
noncomputable def openInv (cl : OpenClaims) :
    Spec (openProg cl) (fun h ↦ OpenPostR Good x cl h ∧ RunMid mid x cl h)
      (fun b h ↦ b = true → ExtI mid Good x h) εS εS 0 :=
  openInvOf thrRec_eq cl

/-- **The two roots from the empty history**, the run recorded: post the roots' shape and that the
history is a completed run of the two root commitments. -/
noncomputable def rootsInv {T : ℝ≥0∞} (hT : T ≤ εS) :
    Spec (commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G) (fun h ↦ h = [])
      (fun _ h ↦ RootShape h ∧ (commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G).after h =
        some (.ret ())) εS 0 T :=
  ((Spec.bind' ((Spec.commitP (Pre := fun h ↦ h = [])
      (Post := fun _ h ↦ ∃ W, h = [Ev.commit 19 64 W] ∧ WellShaped 64 W) (εmax := εS) 19 64
      (fun _ w hh hw ↦ ⟨w, by rw [hh]; rfl, hw⟩) zero_le).congr rfl) fun _ ↦
    (Spec.commitP (Pre := fun h ↦ ∃ W, h = [Ev.commit 19 64 W] ∧ WellShaped 64 W)
      (Post := fun _ h ↦ RootShape h) 15 64
      (fun _ w ⟨W, hh, hW⟩ hw ↦ ⟨W, w, by rw [hh]; rfl, hW, hw⟩) hT).congr rfl).traced
    (fun h ↦ h = [])).mono (fun _ h ↦ ⟨h, h⟩)
    (fun _ _ ⟨hR, h₀, l, he, h0, hl⟩ ↦ ⟨hR, by rw [he, h0, List.nil_append]; exact hl⟩) le_rfl le_rfl
    le_rfl

/-- **`P_S` in the invariant**, for J2C-A's threshold. -/
noncomputable def psInvOf (hthr : thrRec = (codesRec20Jp 0).thr) {Lm : ℝ≥0∞}
    (hmid : MidSpecR mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    Spec (PSWith mid x) (fun h ↦ h = []) (fun b h ↦ b = true → ExtI mid Good x h) εS 0 0 :=
  (Spec.bind' (rootsInv hLm) fun _ ↦
    Spec.bind' (((hmid x εS le_rfl).some.traced
        (fun h ↦ (commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G).after h =
          some (.ret ()))).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
      fun cl ↦ openInvOf hthr cl).congr (PSWith_eq mid x).symm

/-- **`P_S` in the invariant** (J2C-DES T6): from the empty history, every group at most `εS`, lead `0`; an
accepting return has `ExtI`. With `Good := ⊥` this is soundness. -/
noncomputable def psInv {Lm : ℝ≥0∞} (hmid : MidSpecR mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    Spec (PSWith mid x) (fun h ↦ h = []) (fun b h ↦ b = true → ExtI mid Good x h) εS 0 0 :=
  psInvOf thrRec_eq hmid hLm x

end Lvm.ASM
