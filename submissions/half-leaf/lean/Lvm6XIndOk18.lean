-- lvm6 EXF phase 3 (EXI's last hypothesis `hok`): `DescOk6` of the fill block followed by the descent at `P17`, and
-- `open6XC`: Open6's extractor fields with only `hw`, `hX`, `hlog` left. New.
import Lvm6XIndOpen18

/-!
# `hok` discharged

* **`partOk_cpsIR`** (generic), **`partOk_fillIR`**: `PartOk fillIR 2944`, reached behind `generalize` (the
  record elaborated at the concrete `fillTab` hits maximum recursion).
* **`cost_desc_le`**: the descent's cost at every `t` within the five levels' `lvB` and `finCap` (as in
  `descOk6`).
* **`descOk6_FDep`**: `DescOk6 (.seq fillIR (descX6 (LvD FDep) finX))` (`descOk6_seq`, `budgetF`).
* **`open6XC`**: `open6XF` with `hok` discharged (`open6XFront` is taken by `Lvm6XInd18`'s generic form).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm.T
open scoped NNReal ENNReal

/-- The copies are a part: well formed, no `loopT`, no output, `21` steps a copy plus `4`. -/
theorem partOk_cpsIR (tab : List (Bool × ℕ × ℕ)) : PartOk (cpsIR tab) (21 * tab.length + 4) :=
  ⟨wf_cpsIR tab, noLoopT_cpsIR tab, fun t ↦ outs_cpsIR t tab, fun t ↦ cost_cpsIR t tab⟩

/-- **The fill block is a part within `2944` steps.** -/
theorem partOk_fillIR : PartOk fillIR 2944 := by
  have hl := fill_ok.2.2.2.2.2.2
  unfold fillIR
  generalize fillTab = tab at hl ⊢
  have h := partOk_cpsIR tab
  rw [hl] at h
  exact h

/-- **The descent's cost at `P17`**, at every `t`: the five levels' `lvB` and `finCap`. -/
theorem cost_desc_le (F : FrontA) (t : ℕ) : cost (descX6 (LvD F) finX) t ≤
    lvB 0 6 191 6 + lvB 1 4 128 1 + lvB 2 4 128 1 + lvB 3 4 128 1 + lvB 4 4 128 1 + finCap + 5 := by
  have hg : ∀ i < 5, ∀ g ∈ (LvD F i).gs, GroupOk i g := fun i hi ↦ by
    have := groupOk hi; interval_cases i <;> exact this
  have hn : ∀ i < 5, ∀ g ∈ (LvD F i).gs, g.nr ≤ rds i := fun i hi ↦ by
    have := nrD hi; interval_cases i <;> exact this
  have hf := finIR_part34 (fun m ↦ colBD 0 + strD 0 * (2 * m))
  have c0 : cost (levelX 0 (LvD F 0)) t ≤ lvB 0 6 191 6 := by
    have h := cost_levelX_le' (trPart F (i := 0) (by norm_num)) (hg 0 (by norm_num)) (hn 0 (by norm_num)) t
    have e1 : ((LvD F 0).gs.map GroupX.nr).sum = 6 := by simp [LvD, gsD, grpD]
    have e2 : ((LvD F 0).gs.map fun g ↦ g.nr * g.n).sum = 191 := by simp [LvD, gsD, grpD]
    have e3 : (LvD F 0).gs.length = 6 := by simp [LvD, gsD]
    rw [e1, e2, e3] at h
    exact h
  have c1 : cost (levelX 1 (LvD F 1)) t ≤ lvB 1 4 128 1 := by
    have h := cost_levelX_le' (trPart F (i := 1) (by norm_num)) (hg 1 (by norm_num)) (hn 1 (by norm_num)) t
    have e1 : ((LvD F 1).gs.map GroupX.nr).sum = 4 := by simp [LvD, gsD, grpD]
    have e2 : ((LvD F 1).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [LvD, gsD, grpD]
    have e3 : (LvD F 1).gs.length = 1 := by simp [LvD, gsD]
    rw [e1, e2, e3] at h
    exact h
  have c2 : cost (levelX 2 (LvD F 2)) t ≤ lvB 2 4 128 1 := by
    have h := cost_levelX_le' (trPart F (i := 2) (by norm_num)) (hg 2 (by norm_num)) (hn 2 (by norm_num)) t
    have e1 : ((LvD F 2).gs.map GroupX.nr).sum = 4 := by simp [LvD, gsD, grpD]
    have e2 : ((LvD F 2).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [LvD, gsD, grpD]
    have e3 : (LvD F 2).gs.length = 1 := by simp [LvD, gsD]
    rw [e1, e2, e3] at h
    exact h
  have c3 : cost (levelX 3 (LvD F 3)) t ≤ lvB 3 4 128 1 := by
    have h := cost_levelX_le' (trPart F (i := 3) (by norm_num)) (hg 3 (by norm_num)) (hn 3 (by norm_num)) t
    have e1 : ((LvD F 3).gs.map GroupX.nr).sum = 4 := by simp [LvD, gsD, grpD]
    have e2 : ((LvD F 3).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [LvD, gsD, grpD]
    have e3 : (LvD F 3).gs.length = 1 := by simp [LvD, gsD]
    rw [e1, e2, e3] at h
    exact h
  have c4 : cost (levelX 4 (LvD F 4)) t ≤ lvB 4 4 128 1 := by
    have h := cost_levelX_le' (trPart F (i := 4) (by norm_num)) (hg 4 (by norm_num)) (hn 4 (by norm_num)) t
    have e1 : ((LvD F 4).gs.map GroupX.nr).sum = 4 := by simp [LvD, gsD, grpD]
    have e2 : ((LvD F 4).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [LvD, gsD, grpD]
    have e3 : (LvD F 4).gs.length = 1 := by simp [LvD, gsD]
    rw [e1, e2, e3] at h
    exact h
  have cf : cost finX t ≤ finCap := hf.cost t
  rw [cost_descX6]
  generalize lvB 0 6 191 6 = b0 at c0 ⊢
  generalize lvB 1 4 128 1 = b1 at c1 ⊢
  generalize lvB 2 4 128 1 = b2 at c2 ⊢
  generalize lvB 3 4 128 1 = b3 at c3 ⊢
  generalize lvB 4 4 128 1 = b4 at c4 ⊢
  generalize finCap = bf at cf ⊢
  omega

/-- **`hok`**: the fill block followed by the descent is `DescOk6`. -/
theorem descOk6_FDep : DescOk6 (.seq fillIR (descX6 (LvD FDep) finX)) :=
  descOk6_seq partOk_fillIR (descOk6 FDep) fun t ↦ by
    have h1 := cost_desc_le FDep t
    have h2 := budgetF
    generalize lvB 0 6 191 6 = b0 at h1 h2
    generalize lvB 1 4 128 1 = b1 at h1 h2
    generalize lvB 2 4 128 1 = b2 at h1 h2
    generalize lvB 3 4 128 1 = b3 at h1 h2
    generalize lvB 4 4 128 1 = b4 at h1 h2
    generalize finCap = bf at h1 h2
    generalize descCost6 = dc at h2 ⊢
    generalize (2 : ℕ) ^ 43 = e at h2 ⊢
    generalize cost (descX6 (LvD FDep) finX) t = C at h1 ⊢
    omega

section Assembly

variable {Φ : Phases} {SGood TGood : Hdr → Stack → Prop} (H : PhaseSpecs Φ Whir.I6 SGood TGood)
  (HG : Stmt.openGoodC Whir.GWDc Φ.whir) (hPF : PhasesFollow Φ P17) {VS : Shape → SProg}
  (Xe : ∀ vk, Ext6 (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)) (G6 SGood TGood))

include H HG hPF in
/-- **The extractor's fields of `Open6` at `P17`** for `front6 ; fillIR ; descX6 (LvD FDep) finX`, with `DescOk6`
discharged: only the deployed opening `hw`, the extraction map `hX` and the tape sizes of available logs `hlog`. -/
theorem open6XC (hw : Φ.whir = whirAt Whir.whirP) (hX : ∀ vk, (Xe vk).ext = ExtSpec6 (Whir.I6 P17))
    (hlog : ∀ vk c π L, Avail (kcertAsmG H HG hPF vk (Xe vk)) c π L →
      (∀ e ∈ L, e.1.size < 2 ^ 64) ∧ (extractorInput c π L).length ≤ 2 ^ 64) :
    (∀ vk, ∃ K : KCert (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 (EX6 (.seq fillIR (descX6 (LvD FDep) finX))) K) ∧
    (∀ c π L, isS π = false → EX6 (.seq fillIR (descX6 (LvD FDep) finX)) c π L =
      RecursionFast.WitnessSending.decode π) ∧
    Computes (extX6 (.seq fillIR (descX6 (LvD FDep) finX))) (EX6 (.seq fillIR (descX6 (LvD FDep) finX)))
      fuel6 ∧
    (extX6 (.seq fillIR (descX6 (LvD FDep) finX))).body.size ≤ progCap :=
  open6XF H HG hPF Xe hw hX hlog descOk6_FDep

end Assembly

end Lvm6.X
