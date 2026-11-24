-- lvm6 X6b (X4 §4 items 1–2, X5 §3 `goodL`): the descent's hypotheses against W1's deployed instance. The
-- level domain `domE` is X4's `K(ptK j)` (`hdom`), `E2` has the `K`-basis `basisE2`, `descD_correct` at the deployed
-- levels (`descD_correctE`), and the price of X4's `GoodL`: W1's fold escapes together with the MCA exceptional pairs
-- cost no more than the escapes alone (`card_foldEsc_union_excSet_le`). New.
import Lvm6XDesc
import Lvm6WhirCode
import Lvm6XRead

/-!
# The descent at W1's deployed levels

* **`domE_ptK`** (`hdom`): W1's position `p` of a level is `algebraMap K E2 (ptK p)` (definitional).
* **`basisE2`**: the `K`-basis `(1, X)` of `E2 = K[X]/(X² + gX + 1)` (Mathlib's `QuadraticAlgebra.basis`).
* **`descD_correctE`**: X4's `descD_correct` with `F = E2`, `dom = domE h`, `b = basisE2`: no deployed hypothesis
  left but the level's own (`GoodL`, the start tuple and its agreement).
* **`foldBadR_union_excSet_subset`**, **`card_foldBadR_union_le`**: `lem:fold-list`'s count already covers the
  exceptional pairs: `foldBadR ∪ excSet(g, f) ⊆ excSet(g, f) ∪ ⋃ B2`, so the union has at most
  `|excSet| + 2 jl n (A − 1) d |F|` pairs.
* **`card_foldEsc_union_excSet_le`**: W1's round escape `foldEsc` joined with the pairs X4's `GoodL` excludes at the
  same threshold is within W1's per-round bound `nAff + 2 jl n (A − 1) d |F|` (`card_foldEsc_le`). A round
  specification whose escape is this union (and whose invariant records `(α, β) ∉ excSet`) costs W1's ledger
  nothing extra; that is the form `goodL` needs (see `docs/lvm6/stages/X6b.md`).
-/

set_option autoImplicit false

namespace Lvm6.X

open Polynomial Finset Lvm.Nb Lvm.X Lvm6.FD Lvm6.Whir LeanVM.Protocol.Whir.AffineCombiner LeanVM.Parameters

/-! ## `hdom` and the `K`-basis -/

/-- **`hdom` at W1's levels**: position `p` of `domE h` is `K(ptK p)`. -/
theorem domE_ptK (h : ℕ) (hh : h ≤ 64) (p : Fin (2 ^ h)) : domE h hh p = algebraMap BF64 E2 (ptK p) := rfl

/-- **The `K`-basis of `E2`** (`re`, `im`). -/
noncomputable def basisE2 : Module.Basis (Fin 2) BF64 E2 := QuadraticAlgebra.basis 1 g

/-- **X4's level descent at a deployed level** (`F = E2`, `dom = domE h`, `b = basisE2`). -/
theorem descD_correctE {m N d h : ℕ} (hh : h ≤ 64) (hN : h + 1 ≤ N) (hN64 : N ≤ 64) (hd : d + 1 ≤ 2 ^ h)
    (j : ℕ) (ch : List (E2 × E2)) (Q : Wd E2 (2 ^ h) (m + j)) (a : ℕ) (Tc : CT E2 m) (T : Tup E2 m)
    (hj : d + 3 + j ≤ a) (hG : GoodL d (domE h hh) j ch Q a) (hR : RepT d Tc T) (hT : DegLE d T)
    (hA : a ≤ (agree (domE h hh) T (foldsQX (domE h hh) j ch Q)).card) :
    ∃ T₀ : Tup E2 (m + j), RepT d (descD basisE2 N d (domE h hh) j ch Q Tc) T₀ ∧ DegLE d T₀ ∧
      a - j ≤ (agree (domE h hh) T₀ Q).card :=
  descD_correct basisE2 hN hN64 hd (domE_ptK h hh) j ch Q a Tc T hj hG hR hT hA

/-- **At the five deployed levels** (`h = ht6 i`, the decoder's table dimension `ht6 i + 1`). -/
theorem descD_correct6 (i : ℕ) {m d : ℕ} (hd : d + 1 ≤ 2 ^ ht6 i) (j : ℕ) (ch : List (E2 × E2))
    (Q : Wd E2 (2 ^ ht6 i) (m + j)) (a : ℕ) (Tc : CT E2 m) (T : Tup E2 m) (hj : d + 3 + j ≤ a)
    (hG : GoodL d (domE (ht6 i) ((ht6_le i).trans (by norm_num))) j ch Q a) (hR : RepT d Tc T)
    (hT : DegLE d T)
    (hA : a ≤ (agree (domE (ht6 i) ((ht6_le i).trans (by norm_num))) T
      (foldsQX (domE (ht6 i) ((ht6_le i).trans (by norm_num))) j ch Q)).card) :
    ∃ T₀ : Tup E2 (m + j), RepT d (descD basisE2 (ht6 i + 1) d (domE (ht6 i) ((ht6_le i).trans (by norm_num)))
        j ch Q Tc) T₀ ∧ DegLE d T₀ ∧ a - j ≤ (agree (domE (ht6 i) ((ht6_le i).trans (by norm_num))) T₀ Q).card :=
  descD_correctE _ le_rfl (by have := ht6_le i; omega) hd j ch Q a Tc T hj hG hR hT hA

/-! ## The price of `GoodL` -/

section Price

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ρ]

/-- **`lem:fold-list` with the exceptional pairs**: `card_foldBadR_le`'s count also covers `excSet(g, f)`. -/
theorem card_foldBadR_union_le (dom : ι ↪ F) (f g : ρ → ι → F) {A d : ℕ}
    (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F) (Bp : (ρ → F[X]) × (ρ → F[X]) → Prop)
    (hviol : ∀ p ∈ pairList dom f g (A - 1) d, Bp p → Λ₀ p.1 + Λ₁ p.2 ≠ c) (u₀ v c₀ c₁ : F) :
    (foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp ∪ excSet dom g f d A).card ≤
      (excSet dom g f d A).card + 2 * jl (Fintype.card ι) (A - 1) d * Fintype.card F := by
  classical
  set pairs := (pairList dom f g (A - 1) d).filter Bp
  let B2 : (ρ → F[X]) × (ρ → F[X]) → Finset (F × F) := fun p ↦ univ.filter fun t ↦
    ClaimHolds Λ₀ Λ₁ t.1 t.2 c u₀ v c₀ c₁ fun r ↦ p.2 r + lin t.1 t.2 * p.1 r
  have hB2 : ∀ p ∈ pairs, (B2 p).card ≤ 2 * Fintype.card F := by
    intro p hp
    obtain ⟨hp, hBp⟩ := mem_filter.mp hp
    refine le_trans (card_le_card ?_) (card_quad_zero_le (Λ₀ p.2 - u₀)
      ((Λ₀ p.1 + Λ₁ p.2 - Λ₀ p.2) - (c - u₀)) ((Λ₁ p.1 - Λ₀ p.1) - v)
      (Λ₀ (fun r ↦ X * p.1 r) - c₀)
      ((Λ₁ (fun r ↦ X * p.1 r) - Λ₀ (fun r ↦ X * p.1 r)) - (c₁ - c₀)) ?_)
    · intro t ht
      have ht := (mem_filter.mp ht).2
      simp only [ClaimHolds, map_fold] at ht
      exact mem_filter.mpr ⟨mem_univ _, by linear_combination ht⟩
    · rintro ⟨ha₀, ha₁, -, -, -⟩
      apply hviol p hp hBp
      linear_combination ha₁ + ha₀
  have hsub : foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp ∪ excSet dom g f d A ⊆
      excSet dom g f d A ∪ pairs.biUnion B2 := by
    intro t ht'
    rcases mem_union.mp ht' with ht | ht
    swap
    · exact mem_union_left _ ht
    obtain ⟨P, hP, hpull, hclaim⟩ := (mem_filter.mp ht).2
    rw [mem_tupleList] at hP
    by_cases hE : IsExceptional dom g f d A t.1 t.2
    · exact mem_union_left _ ((mem_excSet _ _ _ _ _ _).mpr hE)
    obtain ⟨U, V, hU, hV, hPUV, hloss⟩ : ∃ U V, IsWitness dom g f d t.1 t.2 P U V := by
      by_contra hw
      exact hE ⟨P, hP.1, hP.2, hw⟩
    let p : (ρ → F[X]) × (ρ → F[X]) := (V, U)
    set S := agree dom P (comb dom g f t.1 t.2) with hS
    have hagr : S.filter (fun x ↦ ¬ ∃ r, (U r).eval (dom x) ≠ g r x ∨
        (V r).eval (dom x) ≠ f r x) ⊆ agree dom p.1 f ∩ agree dom p.2 g := by
      intro x hx
      obtain ⟨-, hx⟩ := mem_filter.mp hx
      simp only [not_exists, not_or, not_not] at hx
      exact mem_inter.mpr ⟨(mem_agree _ _ _ _).mpr fun r ↦ (hx r).2,
        (mem_agree _ _ _ _).mpr fun r ↦ (hx r).1⟩
    have hcardS : A ≤ S.card := hP.2
    have hsplit := card_filter_add_card_filter_not (s := S) (fun x ↦ ∃ r,
      (U r).eval (dom x) ≠ g r x ∨ (V r).eval (dom x) ≠ f r x)
    have hloss' : (S.filter fun x ↦ ∃ r, (U r).eval (dom x) ≠ g r x ∨
        (V r).eval (dom x) ≠ f r x).card ≤ 1 := by
      convert hloss
    have hA1 : A - 1 ≤ (agree dom p.1 f ∩ agree dom p.2 g).card :=
      le_trans (by omega) (card_le_card hagr)
    have hdV : DegLE d V := fun r ↦ (hV r).trans (Nat.sub_le _ _)
    have hnear : NearPair dom f g d (agree dom P (foldW dom f g t.1 t.2)) p := by
      refine ⟨hdV, hU, le_trans (le_of_eq (congrArg Finset.card ?_)) hloss'⟩
      ext x
      simp only [mem_filter, hS, foldW]
      exact and_congr_right fun _ ↦ exists_congr fun r ↦ or_comm
    have hp : p ∈ pairs :=
      mem_filter.mpr ⟨(mem_pairList _ _ _ _ _ _).mpr ⟨hdV, hU, hA1⟩, hpull p hnear⟩
    refine mem_union_right _ (mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩)
    have hPeq : (fun r ↦ p.2 r + lin t.1 t.2 * p.1 r) = P := by
      funext r; exact (hPUV r).symm
    rw [hPeq]
    exact hclaim
  calc (foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp ∪ excSet dom g f d A).card
      ≤ (excSet dom g f d A).card + (pairs.biUnion B2).card :=
        (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ (excSet dom g f d A).card + pairs.card * (2 * Fintype.card F) := by
        gcongr
        exact card_biUnion_le_card_mul _ _ _ hB2
    _ ≤ (excSet dom g f d A).card + jl (Fintype.card ι) (A - 1) d * (2 * Fintype.card F) := by
        gcongr
        exact (card_filter_le _ _).trans (card_pairList_le_jl dom f g (A - 1) d hgap)
    _ = _ := by ring

end Price

section Round

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n m : ℕ} (dom : Fin n ↪ F)

omit [DecidableEq F] in
/-- W1's round escape is among `lem:fold-list`'s relativised pairs (the inclusion inside `card_foldEsc_le`). -/
theorem foldEsc_subset_foldBadR (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (A d : ℕ)
    (B : Tup F (m + 1) → Prop) (u₀ w c₀ c₁ : F) :
    foldEsc dom Q W σ A d B u₀ w c₀ c₁ ⊆ foldBadR dom (fun u ↦ Q (Fin.cons false u))
      (fun u ↦ Q (Fin.cons true u)) A d (W ∘ₗ inlT) (W ∘ₗ inrT) σ u₀ w c₀ c₁ (fun p ↦ B (joinT p.1 p.2)) := by
  classical
  intro t ht
  rw [foldEsc, Finset.mem_filter] at ht
  simp only [TViol, not_forall, not_not, exists_prop] at ht
  obtain ⟨P, hP, hag, hpull, hc⟩ := ht.2
  rw [foldBadR, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, P, ?_, fun p hnear ↦ ?_, ?_⟩
  · rw [mem_tupleList]
    exact ⟨hP, hag⟩
  · exact hpull hag _ (nearT_joinT dom (P := p.1) (G := p.2) hnear)
  · rw [ClaimHolds, ← foldClaim, ← hc, foldFn_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply]

/-- **The price of `GoodL`**: from W1's invariant at `A − 1`, the round's escapes together with the exceptional
pairs that X4's `GoodL` excludes at threshold `A` are at most W1's per-round count `nAff + 2 jl n (A − 1) d |F|`
(the bound of `card_foldEsc_le`, unchanged). -/
theorem card_foldEsc_union_excSet_le (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F)
    {A d mm D Bb : ℕ} (hgap : n * d < (A - 1) * (A - 1)) (hadm : Admissible n d A mm D Bb)
    {B : Tup F (m + 1) → Prop} (hv : TViol dom Q W σ (A - 1) d B) (u₀ w c₀ c₁ : F) :
    ((foldEsc dom Q W σ A d B u₀ w c₀ c₁ ∪
        excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d A).card : ℚ) ≤
      nAff (Fintype.card F) n d A mm D Bb + 2 * jl n (A - 1) d * (Fintype.card F : ℚ) := by
  classical
  have hn : Fintype.card (Fin n) = n := Fintype.card_fin n
  have h := card_foldBadR_union_le dom (fun u ↦ Q (Fin.cons false u)) (fun u ↦ Q (Fin.cons true u)) (d := d)
    (A := A) (by rwa [hn]) (W ∘ₗ inlT) (W ∘ₗ inrT) σ (fun p ↦ B (joinT p.1 p.2))
    (fun p hp hb ↦ by
      rw [mem_pairList] at hp
      have := hv (joinT p.1 p.2) (degLE_joinT hp.1 hp.2.1) (by rw [agree_joinT]; exact hp.2.2) hb
      rwa [map_joinT] at this) u₀ w c₀ c₁
  have hmca := Lvm6.Aff.card_excSet_le_nAff dom (by rwa [hn]) (fun u ↦ Q (Fin.cons true u))
    (fun u ↦ Q (Fin.cons false u))
  rw [hn] at h hmca
  have hsub := Finset.card_le_card (Finset.union_subset_union (foldEsc_subset_foldBadR dom Q W σ A d B u₀ w c₀ c₁)
    (le_refl (excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d A)))
  calc (((foldEsc dom Q W σ A d B u₀ w c₀ c₁ ∪
          excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d A).card : ℕ) : ℚ)
      ≤ ((excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d A).card : ℚ) +
          2 * jl n (A - 1) d * (Fintype.card F : ℚ) := by exact_mod_cast hsub.trans h
    _ ≤ _ := by gcongr

end Round

end Lvm6.X
