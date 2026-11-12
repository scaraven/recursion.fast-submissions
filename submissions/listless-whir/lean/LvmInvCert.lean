-- New for lvm2 (J2C, J2′ at G0): a knowledge certificate from an invariant (J2C-DES §0, D3 "INV": no doom,
-- luck = "the invariant broke, or the extractor's luck"). J2C-DES's Lean probe,
-- as is.
import LvmCompileCert
import LvmSpecRulesCert
import LvmPotential

set_option autoImplicit false
open LeanVM.Parameters LeanVM.Protocol.Compile RecursionFast VerifierProgram
open scoped NNReal ENNReal

namespace LeanVM.Protocol.Compile

/-- No doom. -/
def Cert.none (P : VerifierProgram Bool) : Cert P where
  D _ := False
  ε _ := 0
  read _ _ _ h := h
  grind _ _ h := h
  commit _ _ _ _ h := h
  group _ _ _ _ h := h.elim
  final _ _ h := h

namespace Spec
variable {P : VerifierProgram Bool} {Post : Bool → List Ev → Prop} {εmax L : ENNReal}

/-- `Spec.esc_le` for any postcondition, from the empty history. -/
theorem esc_le_inv (S : Spec P (fun h ↦ h = []) Post εmax L 0) :
    ∀ (q : VerifierProgram Bool) {l : List Ev}, P.Reachable l → P.after l = some q →
      esc (S.D []) l q ≤ S.V [] l
  | .ret true, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.retEnd (reach_nil_iff.2 hl) ha hD
  | .ret false, l, _, _ => by simp [esc]
  | .fail, l, _, _ => by simp [esc]
  | .read k, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.moveEnd (reach_nil_iff.2 hl) ha trivial hD
  | .grind b k, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.moveEnd (reach_nil_iff.2 hl) ha trivial hD
  | .commit ht w k, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.moveEnd (reach_nil_iff.2 hl) ha trivial hD
  | .sample k, l, hl, ha => by
    simp only [esc]
    calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, esc (S.D []) (l ++ [Ev.sample c]) (k c)
        ≤ (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, S.V [] (l ++ [Ev.sample c]) := by
          gcongr with c
          exact esc_le_inv S (k c) (.sample c hl ha) (by rw [after_snoc _ ha]; simp [after])
      _ ≤ S.V [] l := S.sample (reach_nil_iff.2 hl) ha
  | .query i ps k, l, hl, ha => by
    simp only [esc]
    split
    · rename_i rows hans
      exact (esc_le_inv S (k rows) (.query hl ha hans) (by rw [after_snoc _ ha]; simp [after])).trans
        (S.query (reach_nil_iff.2 hl) ha (by simpa using hans))
    · exact zero_le

/-- The invariant's group bound. -/
theorem inv_group (S : Spec P (fun h ↦ h = []) Post εmax L 0) (hL : L ≤ εmax)
    (hng : ∀ h, P.Reachable h → grindBits h = 0) {h : List Ev} {p : VerifierProgram Bool}
    (hr : P.Reachable h) (hb : Boundary h) (ha : P.after h = some p) (hD : S.D [] h) :
    esc (S.D []) h p ≤ εmax := by
  refine (esc_le_inv S p hr ha).trans ?_
  rcases eq_or_ne h [] with rfl | hne
  · exact (S.start_V [] rfl).trans hL
  · have := S.bound (reach_nil_iff.2 hr) hne ((endsMove_iff_boundary hne).2 hb) hD
    rwa [hng h hr, pow_zero, one_mul] at this

end Spec

/-- Two invariants: the escape of the conjunction is at most the sum. -/
theorem esc_and_le (D₁ D₂ : List Ev → Prop) : ∀ (p : VerifierProgram Bool) (h : List Ev),
    esc (fun h ↦ D₁ h ∧ D₂ h) h p ≤ esc D₁ h p + esc D₂ h p
  | .ret true, h => by
    simp only [esc]; split_ifs <;> simp_all
  | .ret false, h => by simp [esc]
  | .fail, h => by simp [esc]
  | .read k, h => by simp only [esc]; split_ifs <;> simp_all
  | .grind b k, h => by simp only [esc]; split_ifs <;> simp_all
  | .commit ht w k, h => by simp only [esc]; split_ifs <;> simp_all
  | .sample k, h => by
    simp only [esc]
    rw [← mul_add, ← Finset.sum_add_distrib]
    gcongr with c
    exact esc_and_le D₁ D₂ (k c) _
  | .query i ps k, h => by
    simp only [esc]
    split
    · exact esc_and_le D₁ D₂ _ _
    · simp

end LeanVM.Protocol.Compile

namespace Lvm.FS

/-- **A knowledge certificate from an invariant**: no doom; luck is "the invariant broke, or the
extractor's luck". -/
noncomputable def kcertOfInv {S : Scheme} {R : Digest → Wit → Prop} {εI εL : ℝ≥0} {L : ℝ≥0∞}
    {Ext : S.Stmt → List Ev → Prop}
    (SI : ∀ x, Spec (S.P x) (fun h ↦ h = []) (fun b h ↦ b = true → Ext x h) (εI : ℝ≥0∞) L 0)
    (hL : L ≤ εI) (hng : ∀ x h, (S.P x).Reachable h → grindBits h = 0)
    (BL : S.Stmt → List Ev → Prop) (BL_nil : ∀ x, ¬ BL x [])
    (BL_read : ∀ {x h k} (y : E), (S.P x).Reachable h → (S.P x).after h = some (.read k) →
      ¬ BL x h → ¬ BL x (h ++ [Ev.read y]))
    (BL_commit : ∀ {x h ht w k} (word : Word), (S.P x).Reachable h →
      (S.P x).after h = some (.commit ht w k) → WellShaped w word → ¬ BL x h →
      ¬ BL x (h ++ [Ev.commit ht w word]))
    (BL_group : ∀ {x h p}, (S.P x).Reachable h → Boundary h → (S.P x).after h = some p →
      ((∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k)) → ¬ BL x h →
      esc (fun h' => ¬ BL x h') h p ≤ εL)
    (hlt : εI + εL < 1)
    (ext : Digest → S.Stmt → List Ev → Wit)
    (extract : ∀ {c x h}, S.ok c x = true → (S.P x).Reachable h →
      (S.P x).after h = some (.ret true) → Ext x h → ¬ BL x h →
      (∀ h', h' <+: h → Boundary h' → ¬ BL x h') → R c (ext c x h)) : KCert S R where
  cert x := Cert.none _
  ε := 0
  cert_ε _ _ _ _ hD := hD.elim
  ε_lt_one := zero_lt_one
  B x h := ¬ (SI x).D [] h ∨ BL x h
  εB := εI + εL
  εB_lt_one := hlt
  B_nil x := by
    simp only [not_or, not_not]; exact ⟨(SI x).start_D [] rfl, BL_nil x⟩
  B_read {x h k} y hr ha hB := by
    simp only [not_or, not_not] at hB ⊢
    exact ⟨(SI x).read y (reach_nil_iff.2 hr) ha hB.1, BL_read y hr ha hB.2⟩
  B_commit {x h ht w k} word hr ha hw hB := by
    simp only [not_or, not_not] at hB ⊢
    exact ⟨(SI x).commit word (reach_nil_iff.2 hr) ha hw hB.1, BL_commit word hr ha hw hB.2⟩
  B_group {x h p} hr hb ha hp hB := by
    simp only [not_or, not_not] at hB ⊢
    refine (esc_and_le _ _ p h).trans ?_
    rw [ENNReal.coe_add]
    exact add_le_add ((SI x).inv_group hL (hng x) hr hb ha hB.1) (BL_group hr hb ha hp hB.2)
  ext := ext
  extract {c x h} hok hr ha hB hBp _ := by
    simp only [not_or, not_not] at hB
    exact extract hok hr ha ((SI x).post (reach_nil_iff.2 hr) ha hB.1 rfl) hB.2
      (fun h' hp hb ↦ fun hbl ↦ hBp h' hp hb (Or.inr hbl))

/-- The budget: no doom term. -/
theorem εFS_kcertOfInv_eq {S : Scheme} {R : Digest → Wit → Prop} (K : KCert S R) (h0 : K.ε = 0)
    (hB : K.εB ≤ 7 * (2 : ℝ≥0)⁻¹ ^ 131 + (2 : ℝ≥0)⁻¹ ^ 132)
    (hh : (badCount : ℝ≥0) / 2 ^ 256 ≤ (2 : ℝ≥0)⁻¹ ^ 139) :
    Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 := by
  unfold Scheme.εFS
  rw [h0, zero_add]
  refine (add_le_add hB hh).trans ?_
  rw [← NNReal.coe_le_coe]; push_cast; norm_num

end Lvm.FS
