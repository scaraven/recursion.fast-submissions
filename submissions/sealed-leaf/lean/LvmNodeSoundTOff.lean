/- `LvmNodeSoundTOff` (GOLF2 off-path move, group 14 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmJBCounting, LvmJBMain, LvmJBMutual, LvmJBComplete, LvmNodeSoundLeft, LvmNodeSoundTr, LvmNodeSoundT,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmJBCounting
import LvmJBMain
import LvmJBMutual
import LvmJBComplete
import LvmNodeSoundLeft
import LvmNodeSoundTr
import LvmNodeSoundT
import LvmE2VWidthsFOff
import LvmSubmissionSOff
import LvmVerifierSTOff
import LvmChainTablePad
import LvmMlListLemmas
import LvmQAsmHar47
import LvmSpecRulesCert
import LvmVerifierST

-- ===== from `LvmJBCounting` =====

section
namespace JBAgreement
open Finset
variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι]
section Incidence
variable {α β : Type*} [Fintype α] [DecidableEq α]

/-- **The exceptional set carries more than `k` incidences per parameter on
average.**

This is the mass form of `card_exceptional_ge`.  Under the same strict
incidence budget, it retains the information discarded by the cardinality
conclusion: the total number of incidences *inside* `I` is greater than
`k * |S|`.  In particular, the conclusion is useful when the points of `I`
are selected agreement columns rather than generic identity columns. -/
theorem exceptional_incidence_mass_gt
    (S : Finset β) (I : Finset α) (P : α → β → Prop)
    [∀ x z, Decidable (P x z)] (a k B : ℕ) (hka : k ≤ a)
    (hrow : ∀ z ∈ S, a ≤ (univ.filter fun x => P x z).card)
    (hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B)
    (hS : Fintype.card α * B < (a - k) * S.card) :
    k * S.card < ∑ z ∈ S, (I.filter fun x => P x z).card := by
  have hfubini : ∑ z ∈ S, (univ.filter fun x => P x z).card =
      ∑ x : α, (S.filter fun z => P x z).card := by
    simp_rw [card_filter]
    exact sum_comm
  have hrowsum : a * S.card ≤
      ∑ z ∈ S, (univ.filter fun x => P x z).card := by
    calc
      a * S.card = ∑ _z ∈ S, a := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum hrow
  have hIsub : I ⊆ univ := subset_univ I
  have hsplit : ∑ x : α, (S.filter fun z => P x z).card =
      (∑ x ∈ I, (S.filter fun z => P x z).card) +
        ∑ x ∈ univ \ I, (S.filter fun z => P x z).card := by
    rw [← sum_union (disjoint_sdiff)]
    congr 1
    exact (union_sdiff_of_subset hIsub).symm
  have hout : (∑ x ∈ univ \ I, (S.filter fun z => P x z).card) ≤
      Fintype.card α * B := by
    calc
      (∑ x ∈ univ \ I, (S.filter fun z => P x z).card) ≤
          ∑ _x ∈ univ \ I, B :=
        sum_le_sum fun x hx => hcol x (mem_sdiff.mp hx).2
      _ = (univ \ I).card * B := by rw [sum_const, smul_eq_mul]
      _ ≤ Fintype.card α * B := by
        exact Nat.mul_le_mul_right B
          (card_le_card (subset_univ (univ \ I)))
  have hinside : a * S.card ≤
      (∑ x ∈ I, (S.filter fun z => P x z).card) +
        Fintype.card α * B := by
    rw [hfubini, hsplit] at hrowsum
    omega
  have hfubiniI : ∑ x ∈ I, (S.filter fun z => P x z).card =
      ∑ z ∈ S, (I.filter fun x => P x z).card := by
    simp_rw [card_filter]
    exact sum_comm
  rw [hfubiniI] at hinside
  have hak : k * S.card + (a - k) * S.card = a * S.card := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hka]
  omega

/-- **Surplus incidence mass survives deletion of an arbitrary core.**

Suppose the strict detector budget is run with cutoff `k+s`, so the
exceptional set carries more than `(k+s)|S|` incidences.  Deleting any
`k`-element core can remove at most `k|S|` of them, leaving more than
`s|S|` incidences on `I \ K`.

This is the quantitative form needed for a singular-anchor core: the columns
of `K` may have completely unbounded occupancy. -/
theorem exceptional_incidence_mass_off_core_gt
    (S : Finset β) (I K : Finset α) (P : α → β → Prop)
    [∀ x z, Decidable (P x z)] (a k s B : ℕ)
    (hks : k + s ≤ a)
    (hrow : ∀ z ∈ S, a ≤ (univ.filter fun x => P x z).card)
    (hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B)
    (hKI : K ⊆ I) (hK : K.card ≤ k)
    (hS : Fintype.card α * B < (a - (k + s)) * S.card) :
    s * S.card < ∑ z ∈ S, ((I \ K).filter fun x => P x z).card := by
  have hmass := exceptional_incidence_mass_gt S I P a (k + s) B hks
    hrow hcol hS
  have hsplit : ∑ z ∈ S, (I.filter fun x => P x z).card ≤
      (∑ z ∈ S, (K.filter fun x => P x z).card) +
        ∑ z ∈ S, ((I \ K).filter fun x => P x z).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _hz
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    by_cases hxK : x ∈ K
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxK, hx'.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hx'.1, hxK⟩, hx'.2⟩)
  have hKle : K.card ≤ k :=
    (le_min hK (Finset.card_le_card hKI)).trans (min_le_left _ _)
  have hcore : ∑ z ∈ S, (K.filter fun x => P x z).card ≤ k * S.card := by
    calc
      ∑ z ∈ S, (K.filter fun x => P x z).card ≤ ∑ _z ∈ S, K.card :=
        Finset.sum_le_sum fun z _ => Finset.card_filter_le _ _
      _ = K.card * S.card := by simp [mul_comm]
      _ ≤ k * S.card := Nat.mul_le_mul_right S.card hKle
  have hmass' : (k + s) * S.card < k * S.card +
      ∑ z ∈ S, ((I \ K).filter fun x => P x z).card :=
    hmass.trans_le (hsplit.trans (Nat.add_le_add_right hcore _))
  rw [Nat.add_mul] at hmass'
  omega

/-- **The output of §3.**

If every parameter in `S` is incident to at least `a` coordinates, every coordinate
outside `I` is incident to at most `B` parameters, and `S` is large enough, then the
exceptional set `I` has more than `k` elements.

Downstream `k` is the code dimension and `I = {x | g x = 0}`.  A dimension-`k`
polynomial is determined by `k` evaluations; the stronger conclusion `k < |I|`
therefore supplies enough coordinates. -/
theorem card_exceptional_ge (S : Finset β) (I : Finset α) (P : α → β → Prop)
    [∀ x z, Decidable (P x z)] (a k B : ℕ) (hka : k ≤ a)
    (hrow : ∀ z ∈ S, a ≤ (univ.filter fun x => P x z).card)
    (hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B)
    (hS : Fintype.card α * B < (a - k) * S.card) :
    k < I.card := by
  apply Nat.lt_of_not_ge
  intro hcon
  have hinc := incidence_bound S I P a B hrow hcol
  -- Weaken `(n - |I|) * B` to `n * B`.
  have hweak : a * S.card ≤ I.card * S.card + Fintype.card α * B := by
    have : (Fintype.card α - I.card) * B ≤ Fintype.card α * B :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  -- Cancel the common `|I| * S.card`.
  have hIa : I.card ≤ a := le_trans hcon hka
  obtain ⟨d, hd⟩ : ∃ d, a = I.card + d := ⟨a - I.card, by omega⟩
  have hd_s : d * S.card ≤ Fintype.card α * B := by
    rw [hd, add_mul] at hweak
    omega
  have hak : a - k ≤ d := by omega
  have : (a - k) * S.card ≤ d * S.card := Nat.mul_le_mul_right _ hak
  omega

end Incidence
end JBAgreement
end

-- ===== from `LvmJBMain` =====

section
namespace JBAgreement
open Finset Polynomial
variable {F : Type*} [Field F]
variable {ι : Type*}
variable [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- The correlated agreement *set* is large: at least `n - e` coordinates carry
simultaneous agreement of `u₀` with `v₀` and of `u₁` with `v₁`. -/
theorem card_correlatedAgreement_set_ge
    (dom : ι → F) (u₀ u₁ : ι → F) (v₀ v₁ : F[X]) (e : ℕ) (S : Finset F)
    (hS : e + 1 < S.card)
    (hagree : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x)
                (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) :
    Fintype.card ι - e ≤
      (univ.filter fun x => u₀ x = v₀.eval (dom x) ∧ u₁ x = v₁.eval (dom x)).card := by
  have hbad := correlatedAgreement_of_branch dom u₀ u₁ v₀ v₁ e S hS hagree
  -- The good set is the complement of `pairDisagree`.
  have hcompl :
      (univ.filter fun x => u₀ x = v₀.eval (dom x) ∧ u₁ x = v₁.eval (dom x))
        = univ \ pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_pairDisagree, RSeval_apply,
      not_or, not_not]
  rw [hcompl, card_sdiff_of_subset (subset_univ _), card_univ]
  omega

end JBAgreement
end

-- ===== from `LvmJBMutual` =====

section
namespace JBAgreement
open Finset Polynomial
variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Field F] in
/-- `Λ` is the complement of the correlated disagreement set `E`. -/
lemma corrAgree_eq_compl (u₀ u₁ v₀ v₁ : ι → F) :
    corrAgree u₀ u₁ v₀ v₁ = univ \ pairDisagree u₀ u₁ v₀ v₁ := by
  ext x
  simp only [mem_corrAgree, mem_sdiff, mem_univ, true_and, mem_pairDisagree, not_or, not_not]

omit [DecidableEq ι] in
/-- Correlated agreement always implies agreement along the line. -/
lemma corrAgree_subset_lineAgree (u₀ u₁ v₀ v₁ : ι → F) (z : F) :
    corrAgree u₀ u₁ v₀ v₁ ⊆ lineAgree u₀ u₁ v₀ v₁ z := by
  intro x hx
  rw [mem_corrAgree] at hx
  rw [mem_lineAgree, hx.1, hx.2]

/-- **The count of accidental agreements.**

The parameters at which the line agreement set strictly exceeds the correlated agreement
set are at most as many as the correlated disagreement set has coordinates.

Each such parameter consumes at least one coordinate of `E`, and no coordinate can be
consumed twice: at a coordinate of `E` the agreement equation is a nontrivial affine
equation in `z`, so it has a single root. -/
theorem card_mutual_bad_le (u₀ u₁ v₀ v₁ : ι → F) (S : Finset F) :
    (S.filter fun z => lineAgree u₀ u₁ v₀ v₁ z ≠ corrAgree u₀ u₁ v₀ v₁).card
      ≤ (pairDisagree u₀ u₁ v₀ v₁).card := by
  set Bad := S.filter fun z => lineAgree u₀ u₁ v₀ v₁ z ≠ corrAgree u₀ u₁ v₀ v₁ with hBad
  set D : F → Finset ι := fun z => lineAgree u₀ u₁ v₀ v₁ z \ corrAgree u₀ u₁ v₀ v₁ with hD
  -- Each `D z` lands in the correlated disagreement set.
  have hDsub : ∀ z, D z ⊆ pairDisagree u₀ u₁ v₀ v₁ := by
    intro z x hx
    rw [hD] at hx
    simp only [mem_sdiff, mem_corrAgree, not_and_or] at hx
    rw [mem_pairDisagree]
    rcases hx.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- Distinct parameters consume distinct coordinates.
  have hdisj : ∀ z ∈ Bad, ∀ z' ∈ Bad, z ≠ z' → Disjoint (D z) (D z') := by
    intro z _ z' _ hne
    rw [Finset.disjoint_left]
    intro x hxz hxz'
    have hx : x ∈ pairDisagree u₀ u₁ v₀ v₁ := hDsub z hxz
    rw [hD, mem_sdiff, mem_lineAgree] at hxz hxz'
    exact hne (eq_of_mem_pairDisagree hx hxz.1 hxz'.1)
  -- A bad parameter really does consume a coordinate.
  have hne : ∀ z ∈ Bad, 1 ≤ (D z).card := by
    intro z hz
    rw [hBad, mem_filter] at hz
    have hss : corrAgree u₀ u₁ v₀ v₁ ⊂ lineAgree u₀ u₁ v₀ v₁ z :=
      lt_of_le_of_ne (corrAgree_subset_lineAgree u₀ u₁ v₀ v₁ z) (Ne.symm hz.2)
    obtain ⟨x, hx1, hx2⟩ := Finset.exists_of_ssubset hss
    exact Finset.card_pos.mpr ⟨x, by rw [hD, mem_sdiff]; exact ⟨hx1, hx2⟩⟩
  -- Count.
  have hbi : (Bad.biUnion D).card = ∑ z ∈ Bad, (D z).card := card_biUnion hdisj
  have hle : ∑ z ∈ Bad, (D z).card ≤ (pairDisagree u₀ u₁ v₀ v₁).card := by
    rw [← hbi]
    refine card_le_card fun x hx => ?_
    obtain ⟨z, _, hz⟩ := mem_biUnion.mp hx
    exact hDsub z hz
  calc Bad.card = ∑ _z ∈ Bad, 1 := by simp
    _ ≤ ∑ z ∈ Bad, (D z).card := sum_le_sum hne
    _ ≤ _ := hle

/-- **Mutual correlated agreement (Haböck).**

Under the hypotheses of §4 — every line point `u₀ + z u₁`, `z ∈ S`, is within distance
`e` of the corresponding point of a fixed line of codewords, and `|S| > e + 1` — the
line agreement set *equals* the correlated agreement set for all but at most `e`
parameters of `S`.

So the correlated agreement produced by the branch argument is not merely a lower bound
on what a random `z` sees: it is exactly what a random `z` sees. -/
theorem card_mutual_bad_le_of_agree {u₀ u₁ v₀ v₁ : ι → F} {e : ℕ} {S : Finset F}
    (hdis : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (fun x => v₀ x + z * v₁ x)).card ≤ e)
    (hS : e + 1 < S.card) :
    (S.filter fun z => lineAgree u₀ u₁ v₀ v₁ z ≠ corrAgree u₀ u₁ v₀ v₁).card ≤ e :=
  le_trans (card_mutual_bad_le u₀ u₁ v₀ v₁ S) (card_pairDisagree_le hdis hS)

/-- The Reed–Solomon form: for all but at most `e` parameters `z`, the coordinates on
which `u₀ + z u₁` agrees with the codeword `v₀ + z v₁` are exactly the coordinates of
correlated agreement of `(u₀, u₁)` with `(v₀, v₁)`. -/
theorem mutual_correlatedAgreement (dom : ι → F) (u₀ u₁ : ι → F) (v₀ v₁ : F[X]) (e : ℕ)
    (S : Finset F) (hS : e + 1 < S.card)
    (hagree : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x)
                (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) :
    (S.filter fun z =>
        lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z
          ≠ corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e := by
  refine card_mutual_bad_le_of_agree (e := e) (S := S) ?_ hS
  intro z hz
  have h := hagree z hz
  simpa only [RSeval_line dom v₀ v₁] using h

end JBAgreement
end

-- ===== from `LvmJBComplete` =====

section
section
namespace JBAgreement
open Polynomial Finset
section Ghat
variable {A : Type*} [CommRing A]

/-- The coordinate polynomial `ĝ_x` for the generic odd clearing exponent `2r+1`. -/
def ghat (γ : A[X]) (ξ : A) (r : ℕ) (w val : A) : A :=
  ghatExp γ ξ (2 * r + 1) w val

end Ghat
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
section Ghat
variable {A : Type*} [CommRing A]

/-- **The size of `ĝ_x` is linear in `r`.**  Both instances matter: with the `T`-degree
size system this is `O(r·D_Y)`, with the `Z`-height size system `O(r·D_Z)`. -/
theorem size_ghat (SS : SizeSystem A) {γ : A[X]} {ξ w val : A} {r mγ mw mξ mval m : ℕ}
    (hdeg : γ.natDegree ≤ r) (hc : ∀ i, SS.P (γ.coeff i) mγ)
    (hw : SS.P w mw) (hξ : SS.P ξ mξ) (hval : SS.P val mval)
    (h1 : mγ + r * mw ≤ m) (h2 : (2 * r + 1) * mξ + mval ≤ m) :
    SS.P (ghat γ ξ r w val) m := by
  exact size_ghat_exp SS hdeg hc hw hξ hval h1 h2

end Ghat
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
section Slice
variable {A : Type*} [CommRing A]

/-- The obstruction constant `H₀ = R(x₀, a₀)` has size `mR + d·mα`. -/
theorem size_jetConst (SS : SizeSystem A) (R₀ : A[X][X]) (a₀ : A) {d mR mα : ℕ}
    (hd : R₀.natDegree ≤ d) (hR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR) (ha : SS.P a₀ mα) :
    SS.P (jetConst R₀ a₀) (mR + d * mα) :=
  size_slice_eval SS R₀ a₀ hd (fun j => hR j 0) ha

/-- The simple-root value `ξ` has size `mR + d·mα`: differentiating in `Y` only
multiplies coefficients by integers. -/
theorem size_xi (SS : SizeSystem A) (R₀ : A[X][X]) (a₀ : A) {d mR mα : ℕ}
    (hd : R₀.natDegree ≤ d) (hR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR) (ha : SS.P a₀ mα) :
    SS.P (xi R₀ a₀) (mR + d * mα) := by
  refine size_slice_eval SS (hasseDeriv 1 R₀) a₀ ?_ (fun j => ?_) ha
  · exact le_trans (natDegree_hasseDeriv_le R₀ 1) (le_trans (Nat.sub_le _ _) hd)
  · have hc : (hasseDeriv 1 R₀).coeff j = (j + 1).choose 1 • R₀.coeff (j + 1) := by
      rw [hasseDeriv_coeff, ← nsmul_eq_mul]
    rw [hc, coeff_smul]
    exact SS.nsmul (hR (j + 1) 0) _

end Slice
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
section Slice
variable {A : Type*} [CommRing A]

/-- An irreducible primitive polynomial is nonconstant. -/
theorem natDegree_pos_of_irreducible_of_isPrimitive {Rz : Type*} [CommRing Rz] {H : Rz[X]}
    (hirr : Irreducible H) (hprim : H.IsPrimitive) : 1 ≤ H.natDegree := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h0
  have hC : H = C (H.coeff 0) := eq_C_of_natDegree_eq_zero h0
  have hu : IsUnit (H.coeff 0) := hprim _ ⟨1, by rw [mul_one, ← hC]⟩
  exact hirr.not_isUnit (by rw [hC]; exact hu.map C)

end Slice
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial
variable {R : Type*} [CommSemiring R]
section TwoVar
variable {F : Type*} [Field F]

/-- The `T`-degree of a factor is at most the `T`-degree of the multiple. -/
theorem natDegree_of_dvd {p q : F[X][X]} {m : ℕ} (hdvd : p ∣ q) (hq : q ≠ 0)
    (hdeg : q.natDegree ≤ m) : p.natDegree ≤ m :=
  le_trans (natDegree_le_of_dvd hdvd hq) hdeg

end TwoVar
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial
variable {R : Type*} [CommSemiring R]
section ThreeVar
variable {F : Type*} [Field F]

/-- **`Y`-degrees pass to factors** in `F[Z][X][Y]`. -/
theorem degY_of_dvd {P Q : F[X][X][X]} {m : ℕ} (hdvd : P ∣ Q) (hQ : Q ≠ 0)
    (h : Q.natDegree ≤ m) : P.natDegree ≤ m :=
  le_trans (natDegree_le_of_dvd hdvd hQ) h

end ThreeVar
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
section EndToEnd
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Sharp end-to-end correlated agreement.**  The derivative-sensitive branch
ledger gives total capacity `4k·dY·dZ+dY`. -/
theorem correlatedAgreement_of_GS_sharp
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hfield : 2 * dY * dX < Fintype.card F)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
      (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e ∧
      (∀ S₂ : Finset F, e + 1 < S₂.card →
        (∀ z ∈ S₂, (disagree (fun x => u₀ x + z * u₁ x)
            (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) →
        (S₂.filter fun z =>
          lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z
            ≠ corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e) := by
  obtain ⟨v₀, v₁, S', hS'S, hS'card, hdeg₀, hdeg₁, hpz⟩ :=
    exists_affine_bucket_of_GS_sharp dom hdom u₀ u₁ k e hk S p hpdeg hprox Q hQ0
      dX dY dZ hQY hQX hQZ hGS hfield hslack hS
  refine ⟨v₀, v₁, hdeg₀, hdeg₁, ?_, ?_⟩
  · refine correlatedAgreement_of_branch dom u₀ u₁ v₀ v₁ e S' hS'card ?_
    intro z hz
    have h := hprox z (hS'S hz)
    rw [hpz z hz] at h
    exact h
  · intro S₂ hS₂ hagree
    exact mutual_correlatedAgreement dom u₀ u₁ v₀ v₁ e S₂ hS₂ hagree

end EndToEnd
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset

/-- The summed factor capacity is `O(k/eta³)` when `dY = O(1/eta)` and
 dZ is O(1/eta^2).  This is the bound used by the weighted selector. -/
theorem sharpGSThreshold_le {k dY dZ : ℕ} {η c₁ c₂ : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hDY : (dY : ℝ) ≤ c₁ / η) (hDZ : (dZ : ℝ) ≤ c₂ / η ^ 2) :
    (sharpGSBound k dY dZ : ℝ) ≤
      (4 * (k : ℕ) * c₁ * c₂ + c₁) / η ^ 3 := by
  have hDY' : (dY : ℝ) * η ≤ c₁ := (le_div_iff₀ hη).mp hDY
  have hDZ' : (dZ : ℝ) * η ^ 2 ≤ c₂ := (le_div_iff₀ (by positivity)).mp hDZ
  have hc₁ : 0 ≤ c₁ := le_trans (by positivity) hDY'
  have hc₂ : 0 ≤ c₂ := le_trans (by positivity) hDZ'
  have hprod : (dY : ℝ) * dZ * η ^ 3 ≤ c₁ * c₂ := by
    calc (dY : ℝ) * dZ * η ^ 3 = ((dY : ℝ) * η) * ((dZ : ℝ) * η ^ 2) := by ring
      _ ≤ c₁ * c₂ := mul_le_mul hDY' hDZ' (by positivity) hc₁
  have hlinear : (dY : ℝ) * η ^ 3 ≤ c₁ := by
    have hη2 : η ^ 2 ≤ 1 := by nlinarith
    calc (dY : ℝ) * η ^ 3 = ((dY : ℝ) * η) * η ^ 2 := by ring
      _ ≤ c₁ * 1 := mul_le_mul hDY' hη2 (by positivity) hc₁
      _ = c₁ := by ring
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < η ^ 3)]
  have hcast : (sharpGSBound k dY dZ : ℝ) =
      4 * (k : ℝ) * ((dY : ℝ) * dZ) + dY := by
    rw [sharpGSBound]
    push_cast
    ring
  rw [hcast]
  calc (4 * (k : ℝ) * ((dY : ℝ) * dZ) + dY) * η ^ 3
      = 4 * (k : ℝ) * ((dY : ℝ) * dZ * η ^ 3) +
          (dY : ℝ) * η ^ 3 := by ring
    _ ≤ 4 * (k : ℝ) * (c₁ * c₂) + c₁ :=
      add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity)) hlinear
    _ = 4 * (k : ℕ) * c₁ * c₂ + c₁ := by ring

end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
section Lift
variable {F K : Type*} [Field F] [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [DecidableEq F] [Fintype K] [DecidableEq K]

/-- Sharp correlated agreement over an arbitrary finite base field. -/
theorem correlatedAgreement_of_GS_sharp_noFieldSize
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
      (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e ∧
      (∀ S₂ : Finset F, e + 1 < S₂.card →
        (∀ z ∈ S₂, (disagree (fun x => u₀ x + z * u₁ x)
            (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) →
        (S₂.filter fun z =>
          lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z
            ≠ corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e) := by
  obtain ⟨v₀, v₁, S', hS'S, hS'card, hv₀, hv₁, hpaff⟩ :=
    exists_affine_bucket_of_GS_sharp_noFieldSize dom hdom u₀ u₁ k e hk S p
      hpdeg hprox Q hQ0 dX dY dZ hQY hQX hQZ hGS hslack hS
  refine ⟨v₀, v₁, hv₀, hv₁, ?_, ?_⟩
  · refine correlatedAgreement_of_branch dom u₀ u₁ v₀ v₁ e S' hS'card ?_
    intro z hz
    have h := hprox z (hS'S hz)
    rw [hpaff z hz] at h
    exact h
  · intro S₂ hS₂ hagree
    exact mutual_correlatedAgreement dom u₀ u₁ v₀ v₁ e S₂ hS₂ hagree

end Lift
end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
section Shift
variable {A B : Type*} [CommRing A] [CommRing B]

lemma xShift_xShift (x₀ x₁ : A) (p : A[X]) :
    xShift x₀ (xShift x₁ p) = xShift (x₀ + x₁) p := by
  have h : (xShift x₀).comp (xShift x₁) = xShift (x₀ + x₁) := by
    refine ringHom_ext ?_ ?_
    · intro a
      simp [xShift]
    · simp [xShift, add_assoc]
  exact RingHom.congr_fun h p

end Shift
end JBAgreement
end
end

section
namespace JBAgreement
open Polynomial Finset
section Unconditional
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Unconditional sharp theorem with no field-size hypothesis.**  Guruswami–Sudan
is constructed over the base field, while only the good-slice/branch stage is run in
a sufficiently large finite scalar extension and then descended. -/
theorem correlatedAgreement_unconditional_sharp_noFieldSize
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F)
    (hclose : ∀ z ∈ S, ∃ p : F[X], p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e)
    (m D dY dZ : ℕ)
    (hkdY : (k - 1) * dY ≤ D)
    (hcnt : Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - (k - 1) * (dY * (dY + 1))) * (dZ + 1))
    (hroot : D < m * (Fintype.card ι - e))
    (hslack : 1 ≤ Fintype.card ι - e - (k))
    (hS : dY * (e + 2) +
        (Fintype.card ι - (k)) * (4 * (k) * (dY * dZ) + dY) /
          (Fintype.card ι - e - (k)) + dZ + 3 * (dY * dZ) < S.card) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
      (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e ∧
      (∀ S₂ : Finset F, e + 1 < S₂.card →
        (∀ z ∈ S₂, (disagree (fun x => u₀ x + z * u₁ x)
            (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) →
        (S₂.filter fun z =>
          lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z
            ≠ corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e) := by
  classical
  have hchoice : ∀ z : F, ∃ p : F[X], z ∈ S → (p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e) := by
    intro z
    by_cases hz : z ∈ S
    · obtain ⟨p, hp⟩ := hclose z hz
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose p hp using hchoice
  obtain ⟨Q, hQ0, hQY, hQX, hQZ, hGS⟩ :=
    exists_gs_for dom hdom u₀ u₁ k e S p (fun z hz => (hp z hz).1)
      (fun z hz => (hp z hz).2) m D dY dZ hkdY hcnt hroot
  exact correlatedAgreement_of_GS_sharp_noFieldSize dom hdom u₀ u₁ k e hk S p
    (fun z hz => (hp z hz).1) (fun z hz => (hp z hz).2)
    Q hQ0 D dY dZ hQY hQX hQZ hGS hslack hS

end Unconditional
end JBAgreement
end

-- ===== from `LvmNodeSoundLeft` =====

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig

/-- Every planned query is within `queryCap` (the plan's one-pass decision, `LvmPlanP20`). -/
theorem planCap_P20 : ((plan P20).all fun e => decide (e.len ≤ queryCap)) = true :=
  List.all_eq_true.mpr fun e he => decide_eq_true (Lvm.PlanChk.cap_P20 e he)

theorem planCap_P20' : ∀ i < (plan P20).length, ((plan P20).getD i default).len ≤ queryCap := by
  intro i hi
  have h := List.all_eq_true.mp planCap_P20 _ (List.getElem_mem hi)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h

end Lvm.NS
end

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig

/-- **The trace bridge** (stated here; proved in `LvmNodeSoundTr`): WP-13a's reader of the stream
lanes is QL's `decode`. -/
def TrBridge : Prop := ∀ W : ℕ → Word, Lvm.X.readTraceL W = decode P20 (wsOf W)

end Lvm.NS
end

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig

/-- **The left child is accepted** (generic in the M3 instance `m` of `V_S`). -/
theorem accV_childW_of (hH : HdrBridge) (hT : TrBridge) (m : M3) {M : Mem} {I : SigIn}
    (w : ℕ → Word) {vk cL : RecursionFast.Digest} {σl : Sig}
    (hlink : LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf w))))
    (harith : decideF P20 m vk cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf w)))) = true)
    (hsig : SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true)
    (hchild : ChildOk I M.k) (hln : I.ln = 20)
    (hvk : digAt M.k I.vk = vk) (hcL : digAt M.k I.cL = cL) (hsl : sigAt' M.k I.sl = σl)
    (hmd : digAt M.k I.md = traceDigest (decode P20 (wsOf (Lvm.X.laneOf w))))
    (hsg : sigAt' M.k I.sg = Lvm.X.sigOfF (Lvm.X.sigCol w))
    (hhd : ∀ k < 615, M.k (I.hd + k) = laneK (wsOf (Lvm.X.laneOf w)) (11 + k))
    (hσl : SigOk vk (traceDigest []) σl = true) :
    accV (VS P20 m) vk cL (childW w) = true := by
  have hws : hashedLen P20 ≤ 8 * (wsOf (Lvm.X.laneOf w)).length := by
    rw [wsOf, List.length_map, List.length_range, sizes_P20.2.2.2.2.2.1]; norm_num
  unfold childW
  rw [hT]
  refine accV_reassemble P20 rfl m vk cL _ _ planOk_P20 (by rw [plan_P20]; decide) planCap_P20'
    (by rw [sizes_P20.1]; norm_num) hlink
    (hH M I _ vk cL σl hlink hws hhd hchild hln hvk hcL hsl hσl) harith ?_
  rw [← hsg, ← hmd, ← hvk]
  exact hsig

end Lvm.NS
end

-- ===== from `LvmNodeSoundTr` =====

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.Replay Lvm.QLink

/-- A plan that passes `raChk` against `L` has the lengths `L`. -/
theorem map_len_of_raChk : ∀ (P : List PE) (L : List ℕ), Lvm.X.raChk P L = true → P.map PE.len = L
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Lvm.X.raChk] at h
  | _ :: _, [], h => by simp [Lvm.X.raChk] at h
  | e :: P, l :: L, h => by
    simp only [Lvm.X.raChk, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.map_cons, h.1.1, map_len_of_raChk P L h.2]

/-- The plan's query lengths at `P20` (XA's `ra_plan_chk`). -/
theorem lens_P20 : lens P20 = 7 :: Lvm.X.lensL := map_len_of_raChk _ _ Lvm.X.ra_plan_chk

/-- Lane-aligned lengths: `8 · Σ (5 + len / 8) = Σ (40 + len)`. -/
theorem lanes_sum : ∀ l : List ℕ, (∀ len ∈ l, len % 8 = 0) →
    8 * (l.map fun len => 5 + len / 8).sum = (l.map (40 + ·)).sum
  | [], _ => rfl
  | len :: r, h => by
    have h0 := h len (by simp)
    have ih := lanes_sum r fun x hx => h x (by simp [hx])
    simp only [List.map_cons, List.sum_cons]
    (clear * - h0 ih; omega)

/-- The walk of the entries after `q₀` ends inside the stream lanes (from `Σ (40 + len)`, the
plan's one-pass decision `LvmPlanP20`). -/
theorem walkEnd_le : 6 + (Lvm.X.lensL.map fun len => 5 + len / 8).sum ≤ nLanes := by
  have h8 : ∀ len ∈ Lvm.X.lensL, len % 8 = 0 := fun len h => by
    have := List.all_eq_true.mp Lvm.X.lensL_facts.2 len h
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  have hs := Lvm.PlanChk.slen_P20
  rw [lens_P20, slenS, List.map_cons, List.sum_cons] at hs
  have := lanes_sum _ h8
  show _ ≤ 278528
  (clear * - hs this; omega)

end Lvm.NS
end

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.Replay Lvm.QLink

/-- **The trace bridge**: WP-13a's reader of the stream lanes is QL's `decode`. -/
theorem trBridge : TrBridge := by
  intro W
  have h8 : ∀ len ∈ Lvm.X.lensL, len % 8 = 0 := fun len h => by
    have := List.all_eq_true.mp Lvm.X.lensL_facts.2 len h
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  rw [decode, lens_P20, readEntries, entryAt_q0, show 1 + 40 + 7 = 8 * 6 by rfl,
    readEntries_walk W _ 6 h8 walkEnd_le]
  rfl

end Lvm.NS
end

-- ===== from `LvmNodeSoundT` =====

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig
open Lvm.TypedV (TNat decideFT)

/-- **Replay of the typed `V_S`**: on a trace of the schedule whose reassembled proof passes the header checks,
`VST` asks exactly the trace and returns `decideFT` on its stream. -/
theorem VST_replay (p : Params) (hA : p.accV = accVars) (N : TNat) (vk c : RecursionFast.Digest) (hP : PlanOk p) (tr : Trace) (hL : LinkOk p tr)
    (hparse : parseOk p vk c (reassemble p tr) = true) :
    (VST p N vk c (reassemble p tr)).runSeq tr = some (decideFT p N vk c (traceBytesB tr)) := by
  simp only [VST, hparse, ite_true]
  exact drive_replay p hA hP tr hL _

/-- **The left child is accepted by the typed `V_S`** (`accV_reassembleD` at `VST p N`). -/
theorem accV_reassembleT (p : Params) (_hA : p.accV = accVars) (N : TNat) (vk cL : RecursionFast.Digest) (tr : Trace)
    (σ : Sig) (hP : PlanOk p) (hq : (plan p).length ≤ qVlvm)
    (hcap : ∀ i < (plan p).length, ((plan p).getD i default).len ≤ queryCap)
    (hpi : piSize p < 2 ^ 64) (hL : LinkOk p tr)
    (hparse : parseOk p vk cL (reassemble p tr) = true)
    (hdec : decideFT p N vk cL (traceBytesB tr) = true)
    (hsig : SigOk vk (traceDigest tr) σ = true) :
    accV (VST p N) vk cL ⟨reassemble p tr, tr, σ⟩ = true :=
  accV_reassembleD (VST p N) p (decideFT p N) (fun _ _ _ => rfl) vk cL tr σ hP hq hcap hpi hL hparse hdec hsig

/-- **The left child is accepted by the typed `V_S`** from what the circuit's memory gives (`accV_childW_of` on
`VST`). -/
theorem accV_childW_ofT (hH : HdrBridge) (hT : TrBridge) (N : TNat) {M : Mem} {I : SigIn}
    (w : ℕ → Word) {vk cL : RecursionFast.Digest} {σl : Sig}
    (hlink : LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf w))))
    (harith : decideFT P20 N vk cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf w)))) = true)
    (hsig : SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true)
    (hchild : ChildOk I M.k) (hln : I.ln = 20)
    (hvk : digAt M.k I.vk = vk) (hcL : digAt M.k I.cL = cL) (hsl : sigAt' M.k I.sl = σl)
    (hmd : digAt M.k I.md = traceDigest (decode P20 (wsOf (Lvm.X.laneOf w))))
    (hsg : sigAt' M.k I.sg = Lvm.X.sigOfF (Lvm.X.sigCol w))
    (hhd : ∀ k < 615, M.k (I.hd + k) = laneK (wsOf (Lvm.X.laneOf w)) (11 + k))
    (hσl : SigOk vk (traceDigest []) σl = true) :
    accV (VST P20 N) vk cL (childW w) = true := by
  have hws : hashedLen P20 ≤ 8 * (wsOf (Lvm.X.laneOf w)).length := by
    rw [wsOf, List.length_map, List.length_range, sizes_P20.2.2.2.2.2.1]; norm_num
  unfold childW
  rw [hT]
  refine accV_reassembleT P20 rfl N vk cL _ _ planOk_P20 (by rw [plan_P20]; decide) planCap_P20'
    (by rw [sizes_P20.1]; norm_num) hlink
    (hH M I _ vk cL σl hlink hws hhd hchild hln hvk hcL hsl hσl) harith ?_
  rw [← hsg, ← hmd, ← hvk]
  exact hsig

end Lvm.NS
end

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig
open Lvm.TypedV (TNat decideFT)
section Typed
open Lvm.Loop.Build Lvm.M3 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

/-- `parts_of_holdsP` at `P20`. -/
theorem parts_of_holds {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ} {M : Mem}
    (hH : (Qn lay I qa nK nE).Holds M) (hA : (Qn lay I qa nK nE).Asserts M) :
    Ok (ctxOf (Qn lay I qa nK nE)) M (qlink P20 lay) (p0 nK nE) ∧
      Ok (ctxOf (Qn lay I qa nK nE)) M (qsig I) (p1 lay nK nE) ∧
      Ok (ctxOf (Qn lay I qa nK nE)) M qa (p2 lay I nK nE) :=
  parts_of_holdsP hH hA

/-- **Q_arith of the B program at `P20`**: phases 4–7, then `qarithB` (the typed verifier, the claims, the
openings). -/
abbrev qaB : BM Unit := Lvm.Har.phases47 cfg20 >>= qarithB cfg20 tdata20

theorem qprogB20 : qprogB cfg20 tdata20 = qprog (lay cfg20) (sigIn cfg20) qaB := rfl

/-- **The B program at `P20` is a node program** (Q_link, Q_sig, `qaB`). -/
theorem QB20_qn : QB20 = Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0 := by
  rw [QB20_eq]
  show toProgram (nK cfg20) 0 (qprogB cfg20 tdata20) = _
  rw [qprogB20]

end Typed
end Lvm.NS
end

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig
open Lvm.TypedV (TNat decideFT)
section Typed
open Lvm.Loop.Build Lvm.M3 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

/-- The Keccak half of a good pair with its boundary claims (`okS` bounds `n` by `2^20`). -/
theorem goodK_of {H : THyp TiB} {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20}
    {qr : Column 19} (hok : okS vk c x = true) (hG : GoodT TiB H x qm qr) : GoodK x (qm, qr) :=
  ⟨hG.2.1, hG.2.2, hG.1.1.2 (okS_n hok).2⟩

/-- **`QB20`'s rows hold and assert on the pair's memory** (`holds_of_wiring`). -/
theorem holds_memT {H : THyp TiB} (S : StaticFactsT cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20)
    {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} (hG : GoodT TiB H x qm qr)
    (hrd : ReaddOk QB20 (memT x qm qr)) :
    QB20.Holds (memT x qm qr) ∧ QB20.Asserts (memT x qm qr) :=
  holds_of_wiring QB20 layT20 (zT x qm qr) S.wf S.hlay (zT_one H x qm qr) (goodT_wiring hG) hrd S.noE2

end Typed
end Lvm.NS
end

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig
open Lvm.TypedV (TNat decideFT)
section Typed
open Lvm.Loop.Build Lvm.M3 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

/-- **`NodeSound` for the typed backend on any good relation `G` below `GoodT`** (R11-N, M′: `nodeT20` uses
`G = GoodT ∧ SBlk`; the hypotheses are asked on `G`'s pairs only). -/
theorem nodeSoundTG (vk : RecursionFast.Digest) (H : THyp TiB) (S : Lvm.CT.SF20) (G : GoodRel)
    (hGT : ∀ x qm qr, G x qm qr → GoodT TiB H x qm qr)
    (hrd : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ReaddOk QB20 (memT x qm qr))
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ y < (qltData P20 (lay cfg20)).length,
        (memT x qm qr).k ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t,
        ∀ z < ((opens P20).getD k default).L.height,
        (memT x qm qr).k (bitBase P20 (lay cfg20) k + ((opens P20).getD k default).L.height * j + z) =
          if ansBit P20 (wsC qr) (((opens P20).getD k default).pe + j / 8)
            (j % 8 * ((opens P20).getD k default).L.height + z) then 1 else 0)
    (hbits : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      SigBits (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 (memT x qm qr).k)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr →
      LaneLink P20 (wsC qr) → LinkOk P20 (decode P20 (wsC qr)) →
      Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) (memT x qm qr) qaB
        (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0) →
      decideFT P20 NT20 vk (hdrOf x).cL (traceBytesB (decode P20 (wsC qr))) = true) :
    NodeSound VSB20 vk G childS := by
  refine nodeSound_of (fun c x qm qr hok hG ↦ chain_of_goodK hok (goodK_of hok (hGT _ _ _ hG)))
    fun c x qm qr hok hb hG' ↦ ?_
  have hG := hGT _ _ _ hG'
  have hK := goodK_of hok hG
  obtain ⟨hH, hA⟩ := holds_memT S.toStaticFactsT hG (hrd c x qm qr hok hb hG')
  have hinj := S.inj
  rw [QB20_qn] at hH hA hinj
  have P := parts_of_holds hH hA
  have mp := hmap c x qm qr hok hb hG'
  have hwsl : 2 ^ (lay cfg20).m ≤ (wsC qr).length := by
    rw [wsC, wsOf, List.length_map, List.length_range]; exact hws20
  have hqin : QIn P20 (lay cfg20) (wsC qr) (memT x qm qr) :=
    ⟨by rw [hfg20]; exact mp.flag, mp.stream, hqlt c x qm qr hok hb hG', hpos c x qm qr hok hb hG'⟩
  have hN : (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)).cells .K ≤
      max ((Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0).cells .K)
        ((Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0).cells .E) := by
    rw [ctxOf_cells]; exact le_max_left _ _
  have hNs : (lay cfg20).sb + 2 ^ (lay cfg20).m ≤
      max ((Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0).cells .K)
        ((Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0).cells .E) :=
    le_trans (by decide : (lay cfg20).sb + 2 ^ (lay cfg20).m ≤ nK cfg20)
      (le_trans (nK_le_cells _ _ _) (le_max_left _ _))
  obtain ⟨hLL, hpad⟩ := qlink_sound hS20 hQ20 hqin hwsl hinj hN hNs P.1.1 P.1.2
  have hlink := linkOk_of_laneLink hS20 hLL
  have hks := sigKSin_of_goodK hK mp.xs mp.ys mp.yc mp.yls mp.yns
  obtain ⟨hsig, hchild⟩ := qsig_sound_in (by rw [hln20]; omega) P.2.1 mp.flag hks (hbits c x qm qr hok hb hG')
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h
  have hmd := (digAt_of_cells mp.md).trans (traceDigest_of_goodK hK hLL hpad)
  have har := harith c x qm qr hok hb hG' mp hLL hlink P.2.2
  exact accV_childW_ofT hdrBridge trBridge NT20 (wOfCol qr) hlink har hsig hchild hln20 mp.vk mp.cL mp.sl hmd
    mp.sg mp.hd (okS_sig hok hb)

/-- **`NodeSound` for the typed backend** (`nodeSound_main` on the B program at `P20`; see the module docstring). -/
theorem nodeSoundT (vk : RecursionFast.Digest) (H : THyp TiB) (S : Lvm.CT.SF20)
    (hrd : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      ReaddOk QB20 (memT x qm qr))
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      ∀ y < (qltData P20 (lay cfg20)).length,
        (memT x qm qr).k ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t,
        ∀ z < ((opens P20).getD k default).L.height,
        (memT x qm qr).k (bitBase P20 (lay cfg20) k + ((opens P20).getD k default).L.height * j + z) =
          if ansBit P20 (wsC qr) (((opens P20).getD k default).pe + j / 8)
            (j % 8 * ((opens P20).getD k default).L.height + z) then 1 else 0)
    (hbits : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      SigBits (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 (memT x qm qr).k)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr →
      LaneLink P20 (wsC qr) → LinkOk P20 (decode P20 (wsC qr)) →
      Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) (memT x qm qr) qaB
        (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0) →
      decideFT P20 NT20 vk (hdrOf x).cL (traceBytesB (decode P20 (wsC qr))) = true) :
    NodeSound VSB20 vk (GoodT TiB H) childS :=
  nodeSoundTG vk H S _ (fun _ _ _ h ↦ h) hrd hmap hqlt hpos hbits harith

end Typed
end Lvm.NS
end
