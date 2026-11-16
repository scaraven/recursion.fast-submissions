/- `LvmInvCertOff` (GOLF2 off-path move, group 12 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmSpecRulesCert, LvmInvCert,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmSpecRulesCert
import LvmInvCert
import LvmMlListLemmas

-- ===== from `LvmSpecRulesCert` =====

section
namespace LeanVM.Protocol.Compile
open LeanVM.Parameters VerifierProgram
section
namespace Spec
variable {P : VerifierProgram Bool} {εmax L : ENNReal}

open Classical in
/-- The escape bound of the certificate: the potential at a reachable boundary in doom. -/
noncomputable def certε (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0)
    (h : List Ev) : ENNReal :=
  if P.Reachable h ∧ Boundary h ∧ S.D [] h then S.V [] h else 0

/-- **The doom certificate of a specification** of a whole program: doom `S.D []`, escape bound
the potential at reachable boundaries in doom. -/
noncomputable def toCert (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0) :
    Cert P where
  D := S.D []
  ε := certε S
  read x hl ha hD := S.read x (reach_nil_iff.2 hl) ha hD
  grind hl ha hD := S.grind (reach_nil_iff.2 hl) ha hD
  commit word hl ha hw hD := S.commit word (reach_nil_iff.2 hl) ha hw hD
  group {h p} hl hb ha _ hD := by
    have hc : P.Reachable h ∧ Boundary h ∧ S.D [] h := ⟨hl, hb, hD⟩
    simp only [certε, hc]
    exact esc_le S p hl ha
  final hl ha hD := by simpa using S.post (reach_nil_iff.2 hl) ha hD

/-- The doom of the certificate is the specification's from the empty history. -/
theorem toCert_D (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0) :
    S.toCert.D = S.D [] := rfl

open Classical in
/-- The escape bound of the certificate. -/
theorem toCert_ε (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0) (h : List Ev) :
    S.toCert.ε h = if P.Reachable h ∧ Boundary h ∧ S.D [] h then S.V [] h else 0 := rfl

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
group, is at most `εmax`, given the bound of the start group. -/
theorem toCert_bound (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0)
    (hstart : S.D [] [] → S.V [] [] ≤ εmax) (h : List Ev) :
    (2 : ENNReal)⁻¹ ^ grindBits h * S.toCert.ε h ≤ εmax := by
  rw [toCert_ε]
  split_ifs with hc
  · obtain ⟨hl, hb, hD⟩ := hc
    rcases eq_or_ne h [] with rfl | hne
    · simpa [grindBits] using hstart hD
    · exact S.bound (reach_nil_iff.2 hl) hne ((endsMove_iff_boundary hne).2 hb) hD
  · simp

/-- The specification of a whole program from the empty history, as one from no history. -/
noncomputable def ofStart (S : Spec P (fun h ↦ h = []) (fun b _ ↦ b = false) εmax L 0) :
    Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0 :=
  S.mono (fun _ h ↦ h.elim) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The doom certificate of a specification from the empty history**. -/
noncomputable def toCertOfLead (S : Spec P (fun h ↦ h = []) (fun b _ ↦ b = false) εmax L 0) :
    Cert P :=
  S.ofStart.toCert

/-- The doom of `toCertOfLead`. -/
theorem toCertOfLead_D (S : Spec P (fun h ↦ h = []) (fun b _ ↦ b = false) εmax L 0) :
    S.toCertOfLead.D = S.D [] := rfl

/-- **The certificate's bound** from a lead at most `εmax`. -/
theorem toCertOfLead_bound (S : Spec P (fun h ↦ h = []) (fun b _ ↦ b = false) εmax L 0)
    (hL : L ≤ εmax) (h : List Ev) :
    (2 : ENNReal)⁻¹ ^ grindBits h * S.toCertOfLead.ε h ≤ εmax :=
  S.ofStart.toCert_bound (fun _ ↦ (S.start_V [] rfl).trans hL) h

end Spec
end
end LeanVM.Protocol.Compile
end

-- ===== from `LvmInvCert` =====

section
set_option autoImplicit false
open LeanVM.Parameters LeanVM.Protocol.Compile RecursionFast VerifierProgram
open scoped NNReal ENNReal
namespace Lvm.FS

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
end
