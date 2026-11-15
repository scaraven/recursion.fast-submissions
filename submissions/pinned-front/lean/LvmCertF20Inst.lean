-- New for lvm2 E2F (E2F-L2, 2026-11-13): statement 18 at the S2GF instance: the guarded S2GF submission and its
-- certificate, from E2F-C's statement 16 (`nodeF20`) and the instance facts (`THypX TiF20`, `TRefHypX` at
-- `NTF20 QF20 layF20`) of the guard's Booleans.
import LvmCertF20X
import LvmCertM20
import LvmE2QNodeF

/-!
# The S2GF certificate (statement 18)

* `p20F_facts`; **`thypF20`**: `THypX TiF20` from the guard's facts (roll 11's `thyp20` at `mbTOf cfgF20 frzF20`;
  `errsX_at`: the coordinate-split error terms at `L₀ = 37,696`); **`trefF20`**: `TRefHypX NTF20 QF20 layF20`
  (`PhiQCX_eq` through `phiX_of_cacheWX`).
* **`staticOkF20`** `= staticOkBF20` (E2F-C's guard); **`submissionF20`** `= subGF staticOkF20 (VSFX NTF20)`
  (S2GF's extractor `EXF20`/`extXF20`).
* **`certificateF20S`**: `certificateSF20` at the instance, the child `childSP P20F` (`childF20_win`), the node
  soundness `nodeF20`.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-! ## The instance facts -/

/-- `P20F`'s record: `P20`'s `ν`, mini-bus depth and evaluations. -/
theorem p20F_facts : P20F.nuMain = 23 ∧ P20F.nuRec = 19 ∧ P20F.busDepth = 12 ∧ P20F.tableEvals = 633 :=
  p20_facts

open LeanVM.Protocol.KeccakGkr (errE errE_mono) in
open LeanVM.Protocol.EndToEnd.Front in
/-- **The coordinate-split typed phases' error terms** (`TErrsX`) at `L₀ = 37,696` against `εS` with follower
`LkSJ`, for an instance of depth `12` without constraints (`errs_at`'s proof with `τ`'s group of 21 and `κ`'s 3). -/
theorem errsX_at (I : LeanVM.Protocol.M3Instance) (hμ : I.μBus = 12) (hB : I.B = 0) :
    TErrsX 37696 I εS LkSJ := by
  have hab : abError I 37696 = errE (37696 * (4 * 2 ^ 12)) := by
    rw [abError, coe_overE, errE_smul, hμ]
  have hr : ∀ d, roundError 37696 d = errE (37696 * d) := fun d ↦ by
    rw [roundError, coe_div_card, errE_smul]
  have hl : lambdaError 37696 = errE (37696 * 2) := by
    rw [lambdaError, coe_div_card, errE_smul]
  have hu : unitError 37696 = errE (37696 * 1) := by
    rw [← errE_smul]; simp [unitError, errE]
  have hx : xiError I 37696 = errE (37696 * (I.B + 3 - 1)) := by
    rw [xiError, coe_div_card, errE_smul]
  have hlead : leadTX 37696 = errE (21 * (37696 * 1)) := by
    simp only [leadTX, add_zero, errE_smul, Lvm.Typed.xVars]
  have h3 : (3 : ℝ≥0∞) * errE 1 = errE (3 * 1) := by rw [← errE_smul]; norm_num
  have hM : leadMaxTX 37696 I LkSJ ≤ errE (37696 * (4 * 2 ^ 12)) := by
    unfold leadMaxTX
    rw [hlead, hab, add_zero, h3, LkSJ_eq]
    exact max_le (errE_mono (by norm_num)) (max_le le_rfl (max_le (errE_mono (by norm_num))
      (errE_mono (by norm_num))))
  have fin : ∀ a : ℕ, a ≤ 2 ^ 62 → errE a + leadMaxTX 37696 I LkSJ ≤ εS := by
    intro a ha
    calc errE a + leadMaxTX 37696 I LkSJ ≤ errE a + errE (37696 * (4 * 2 ^ 12)) := by gcongr
      _ = errE (a + 37696 * (4 * 2 ^ 12)) := errE_add _ _
      _ ≤ εS := errE_le_εS (Nat.le_trans (Nat.add_le_add_right ha _) (by norm_num))
  refine ⟨?_, fun d hd ↦ ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hlead]; exact errE_le_εS (by norm_num)
  · rw [hr]; exact fin _ (by omega)
  · exact fin _ (by norm_num [Lvm.Typed.phiVarsX, Lvm.Typed.xVars, Lvm.Typed.yVars])
  · rw [hab]; exact lt_of_le_of_lt (errE_le_εS (by norm_num)) εS_lt_one
  · rw [hab]; exact fin _ (by norm_num)
  · rw [interpLead_eq, hu, hl, errE_smul, errE_add]; exact fin _ (by norm_num)
  · rw [hl]; exact fin _ (by norm_num)
  · rw [hx, hB]; exact fin _ (by norm_num)
  · exact hM.trans (errE_le_εS (by norm_num))

/-- **`THypX` of the S2GF typed instance** from the guard's facts (`thyp20`'s proof at `mbTOf cfgF20 frzF20`). -/
theorem thypF20 (S : SFF20) : THypX TiF20 := by
  have st := S.1.st
  have hmb : TiF20.mbT = mbTOf cfgF20 frzF20 := S.1.mb
  have hm : TypedV.fitsMiniB P20F (mbTOf cfgF20 frzF20) = true := hmb ▸ st.mini
  unfold TypedV.fitsMiniB at hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hb⟩, -⟩, -⟩, -⟩, hf⟩, hg⟩, hh⟩, -⟩ := hm
  have ht : Lvm.M3.tabsOkB (mbTOf cfgF20 frzF20) = true := tabsOkB_mbT _ _ _ _
  have hsc : AllSc (mbTOf cfgF20 frzF20) := Lvm.M3.allSc_of_B ht
  have hsum : Lvm.M3.sumcheckTabs (mbTOf cfgF20 frzF20) = mbTOf cfgF20 frzF20 := sc_all _ hsc
  have hτ : ∀ t ∈ TiF20.mbT, t.τ ≤ lay26.μ := hmb ▸ hτ_of_hi (com_mbT _ _ _ _ fun _ ↦ rfl) hh
  have hμ : ∀ (h : ∀ t ∈ TiF20.mbT, t.τ ≤ lay26.μ), (inst lay26 TiF20.mbT h).μBus = miniDepth := fun h ↦ by
    have e : (inst lay26 TiF20.mbT h).μBus = P20F.busDepth := by
      rw [LeanVM.Protocol.M3Instance.μBus, Lvm.VEq.pushLeaves_inst, hmb, hb, Lvm.VEq.log2Ceil_eq_clog,
        Lvm.M3.pushLeavesR, hsum]
    rw [e, p20F_facts.2.2.1]
  refine
    { ok := ⟨st.hlay, src_one_of NTF20 QF20 layF20 S.2.2⟩
      maps := mapsFit_inst NTF20 QF20 layF20 st.hlayOk (by
        have h := st.regs
        rwa [show cfgF20.p = P20F from rfl, p20F_facts.1, p20F_facts.2.1] at h)
      acc := fun x ↦ Lvm.VEq.length_pubXF x
      hτ := hτ
      sc := hmb ▸ hsc
      layOk := hmb ▸ layOk_of_fit ⟨p20F_facts.1, p20F_facts.2.1⟩ hg
      keys := hmb ▸ Lvm.M3.keys_of_B ht
      width := hmb ▸ Lvm.M3.width_pos_of_B ht
      fix := hmb ▸ fixOk_mbT _ _ _ _
      widths := by
        rw [hmb]
        rw [hsum] at hf
        rw [← hf, p20F_facts.2.2.2]
        norm_num
      μBus := hμ
      errs := fun h ↦ errsX_at _ (hμ h) (Nat.le_zero.mp ((B_inst_le lay26 TiF20.mbT h).trans
        (by rw [hmb]; exact (cons_mbT _ _ _ _).le))) }

/-- The mini-bus check reads only fields `P20F` shares with `P20`. -/
theorem fitsMiniB_P20F (m : List Lvm.M3.Tab) : TypedV.fitsMiniB P20F m = TypedV.fitsMiniB P20 m := rfl

/-- **`TRefHypX` at the S2GF instance** from the guard's facts and `THypX` (`PhiQCX cacheF20` is `PhiQFX`:
statement 13 through `phiX_of_cacheWX`). -/
theorem trefF20 (S : SFF20) (H : THypX TiF20) : Lvm.VEq.TRefHypX NTF20 QF20 layF20 where
  ok := by
    have h := S.1.st.regs
    rw [show cfgF20.p = P20F from rfl, p20F_facts.1, p20F_facts.2.1] at h
    rw [p20_facts.1, p20_facts.2.1]
    exact h
  hlay := S.1.st.hlayOk
  mini := by
    have h := S.1.st.mini
    rw [show cfgF20.p = P20F from rfl, fitsMiniB_P20F] at h
    exact h
  sc := H.sc
  phi := fun pt hpt ↦ by
    show PhiQCX cacheF20 pt = _
    rw [cacheF20_eq S.1.st.hlay]
    exact PhiQCX_eq QF20 layF20 S.1.st.hlay S.1.st.cache pt hpt

/-! ## The submission and its certificate -/

/-- **S2GF's static guard**: E2F-C's `staticOkBF20` (the typed guard, the node checks, `σ′` in `S`, the HAR's
checks, the layout's word `1` in a `1` region). -/
def staticOkF20 : Bool := staticOkBF20

/-- **The S2GF submission**: `V_S` at S2GF behind the static guard, S2GF's extractor. -/
def submissionF20 : Submission := subGF staticOkF20 (VSFX NTF20)

/-- **Statement 18: the certificate of the S2GF submission** against the declared claim. -/
theorem certificateF20S :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionF20 :=
  certificateR_guardF fun h ↦
    have S := sfF20 h
    have H := thypF20 S
    certificateSF20 NTF20 QF20 layF20 H (trefF20 S H) S.1.sig (Lvm.NS.childSP P20F)
      (fun x q ↦ childF20_win x q) (nodeF20 S H)

end Lvm.CT
