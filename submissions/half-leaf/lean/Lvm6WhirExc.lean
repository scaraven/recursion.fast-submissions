-- New for lvm6 (WP W2, X6b's F-X6b-2/F-X6b-3). The fold rounds with the extractor's facts carried as a
-- separate conjunct, with or without the opening's doom: the pair avoids the MCA exceptional set of the
-- round's word (`NoExc`, X4's `GoodL` per round) and the claim goes back through the fold (`ClaimBack`,
-- the backward step of the descent). Both are priced at W1's existing per-round count `N` (`RoundOK`):
-- `lem:fold-list`'s count already covers the exceptional pairs (X6b's `card_foldBadR_union_le` and
-- `foldEsc_subset_foldBadR`, `lvm6/X6b` 139c94d1, ported here under W1 names), so the ledger is unchanged.
import Lvm6WhirFinal

/-!
# The fold rounds with the extractor's conjunct (W2)

* `NoExc dom Q d A α β`: `(α, β) ∉ excSet(G, F; d, A)` for the halves of `Q` (X4's `GoodL`, one round).
* `ClaimBack dom Q W σ A d α β u₀ w c₀ c₁`: every tuple of degree `≤ d` agreeing with the fold on `≥ A`
  columns and satisfying the folded claim has a near tuple of `Q` on that agreement set satisfying `(W, σ)`.
* `RGood`: both. **`card_rbad_le`**: from any word and table (and, when `b`, from `TViol` at `A − 1`), the pairs
  `(α, β)` breaking `RGood` (or, when `b`, the doom at `A`) are at most `N`: the union `foldBadR ∪ excSet` is
  `lem:fold-list`'s count (`card_foldBadR_exc_le`, X6b's `card_foldBadR_union_le`).
* **`roundSpecU`** (one round), **`roundsSpecU`** (a level's rounds): `J` framed, the doom conjunct under
  `b = true → …` exactly as `roundSpecJ`/`roundsSpecJ`, and `RGood` (rounds: `GoodRs`) **unconditionally**;
  escape `eRound g p` per round, as before.
* **`TailBack`** (F-X6b-3, a level transition): every member of the next level's list satisfying the glued
  claim has a zero discrepancy (`coefQ = 0`: the base claim, the OOD value, the queried values) and its candidate
  `cand hi U` agrees with the folded word on `≥ A` columns. **`card_tbad_le`**: its bad `(positions, λ)` are within
  `card_qryBad_le`'s count (the query group's `eQry`), with no doom (only the OOD group's `OodOK`).
* `agree_of_posOK` (the final level): W1's position fact `PosOK` and the row check give the final polynomial's
  agreement `≥ A` (its count `card_posBad_le`/`eFin` is already unconditional).
* `GoodLv`: X4's `GoodL` shape (start agreement `a`, round `s` of `j` at `a − (j − 1 − s)`) on `Rnd`s;
  **`goodRs_goodLv`**: `GoodRs` at W1's thresholds gives `GoodLv` at the level's last threshold.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  LeanVM.Protocol.Whir.AffineCombiner Polynomial
open scoped ENNReal

/-! ## The count (after X6b's `Lvm6XDescW`) -/

section Price

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ρ]

omit [DecidableEq F] [DecidableEq ι] in
open Classical in
/-- `foldBadR` grows with its predicate. -/
theorem foldBadR_mono (dom : ι ↪ F) (f g : ρ → ι → F) (A d : ℕ) (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F)
    (c u₀ v c₀ c₁ : F) {Bp Bp' : (ρ → F[X]) × (ρ → F[X]) → Prop} (h : ∀ p, Bp p → Bp' p) :
    foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp ⊆ foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp' := by
  intro t ht
  rw [foldBadR, mem_filter] at ht ⊢
  obtain ⟨hu, P, hP, hn, hc⟩ := ht
  exact ⟨hu, P, hP, fun p hp ↦ h p (hn p hp), hc⟩

/-- **`lem:fold-list` with the exceptional pairs** (X6b's `card_foldBadR_union_le`): `card_foldBadR_le`'s count
also covers `excSet(g, f)`. -/
theorem card_foldBadR_exc_le (dom : ι ↪ F) (f g : ρ → ι → F) {A d : ℕ}
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

omit [DecidableEq F] [DecidableEq ι] in
/-- A higher threshold has fewer exceptional pairs. -/
theorem excSet_anti (dom : ι ↪ F) (f g : ρ → ι → F) {d A A' : ℕ} (h : A ≤ A') :
    excSet dom f g d A' ⊆ excSet dom f g d A := by
  intro p hp
  rw [mem_excSet] at hp ⊢
  obtain ⟨P, hP, hA, hw⟩ := hp
  exact ⟨P, hP, h.trans hA, hw⟩

end Price

/-! ## The round's facts -/

section Facts

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n m : ℕ} (dom : Fin n ↪ F)

/-- **The round's MCA condition** (X4's `GoodL`, one round): `(α, β)` is not exceptional for the halves
`G = Q(1, ·)`, `F = Q(0, ·)` of `Q` at threshold `A`. -/
def NoExc (Q : Wd F n (m + 1)) (d A : ℕ) (α β : F) : Prop :=
  (α, β) ∉ excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d A

omit [DecidableEq F] in
theorem NoExc.mono {Q : Wd F n (m + 1)} {d A A' : ℕ} {α β : F} (h : NoExc dom Q d A α β) (hA : A ≤ A') :
    NoExc dom Q d A' α β :=
  fun hm ↦ h (excSet_anti dom _ _ hA hm)

/-- **The claim goes back through the fold**: every tuple of degree `≤ d` agreeing with the fold on `≥ A`
columns and satisfying the folded claim has a near tuple of `Q` on that agreement set (`NearT`: degree `≤ d`,
agreement loss one) satisfying `(W, σ)`. -/
def ClaimBack (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (A d : ℕ) (α β u₀ w c₀ c₁ : F) :
    Prop :=
  ∀ P : Tup F m, DegLE d P → A ≤ (agree dom P (foldQ dom α β Q)).card →
    foldFn W α P = foldClaim σ α β u₀ w c₀ c₁ →
    ∃ T, NearT dom Q d (agree dom P (foldQ dom α β Q)) T ∧ W T = σ

/-- **The extractor's facts of a round** `r` on the word `Q` with the claim `(W, σ)` at threshold `A`. -/
abbrev RGood (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (A d : ℕ) (r : Rnd F) : Prop :=
  NoExc dom Q d A r.α r.β ∧ ClaimBack dom Q W σ A d r.α r.β r.u₀ r.w r.c₀ r.c₁

/-- The violating pairs (the predicate of `foldBadR` whose complement is `ClaimBack`). -/
def violP (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (p : Tup F m × Tup F m) : Prop :=
  (W ∘ₗ inlT) p.1 + (W ∘ₗ inrT) p.2 ≠ σ

omit [DecidableEq F] in
theorem claimBack_of_not_mem (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (A d : ℕ)
    (u₀ w c₀ c₁ : F) (t : F × F)
    (ht : t ∉ foldBadR dom (fun u ↦ Q (Fin.cons false u)) (fun u ↦ Q (Fin.cons true u)) A d (W ∘ₗ inlT)
      (W ∘ₗ inrT) σ u₀ w c₀ c₁ (violP W σ)) :
    ClaimBack dom Q W σ A d t.1 t.2 u₀ w c₀ c₁ := by
  classical
  intro P hP hag hc
  by_contra hno
  apply ht
  rw [foldBadR, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, P, ?_, fun p hnear heq ↦ ?_, ?_⟩
  · rw [mem_tupleList]
    exact ⟨hP, hag⟩
  · refine hno ⟨joinT p.1 p.2, nearT_joinT dom (P := p.1) (G := p.2) hnear, ?_⟩
    rw [map_joinT]
    simpa only [LinearMap.coe_comp, Function.comp_apply] using heq
  · rw [ClaimHolds, ← foldClaim, ← hc, foldFn_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply]

omit [DecidableEq F] in
/-- W1's round escape is among `lem:fold-list`'s relativised pairs (X6b's `foldEsc_subset_foldBadR`). -/
theorem foldEsc_sub_foldBadR (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (A d : ℕ)
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

open Classical in
/-- **The round's bad pairs, with or without doom** (the escape set `foldBadR ∪ excSet`): at most `N`. With
`b = true` this is X6b's `card_foldEsc_union_excSet_le` plus `ClaimBack`; with `b = false` it needs no
invariant. -/
theorem card_rbad_le {d : ℕ} {p : RoundPar} (hp : RoundOK (Fintype.card F) n d p) (b : Bool)
    (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (B : Tup F (m + 1) → Prop)
    (hv : b = true → TViol dom Q W σ (p.A - 1) d B) (u₀ w c₀ c₁ : F) :
    (univ.filter fun u : Fin 2 → F ↦ ¬ ((b = true → TViol dom (foldQ dom (u 0) (u 1) Q) (foldFn W (u 0))
        (foldClaim σ (u 0) (u 1) u₀ w c₀ c₁) p.A d (pullT dom Q p.A d (u 0) (u 1) B)) ∧
        RGood dom Q W σ p.A d ⟨u₀, w, c₀, c₁, u 0, u 1⟩)).card ≤ p.N := by
  have hn : Fintype.card (Fin n) = n := Fintype.card_fin n
  set Bp : Tup F m × Tup F m → Prop := fun q ↦ (b = true ∧ B (joinT q.1 q.2)) ∨ violP W σ q
  set S := foldBadR dom (fun u ↦ Q (Fin.cons false u)) (fun u ↦ Q (Fin.cons true u)) p.A d (W ∘ₗ inlT)
      (W ∘ₗ inrT) σ u₀ w c₀ c₁ Bp ∪
    excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d p.A
  have hS : (S.card : ℚ) ≤ p.N := by
    have h := card_foldBadR_exc_le dom (fun u ↦ Q (Fin.cons false u)) (fun u ↦ Q (Fin.cons true u))
      (d := d) (A := p.A) (by rw [hn]; exact hp.1) (W ∘ₗ inlT) (W ∘ₗ inrT) σ Bp
      (fun q hq hb ↦ by
        rcases hb with ⟨hb, hB⟩ | hb
        · rw [mem_pairList] at hq
          have := hv hb (joinT q.1 q.2) (degLE_joinT hq.1 hq.2.1) (by rw [agree_joinT]; exact hq.2.2) hB
          rwa [map_joinT] at this
        · exact hb) u₀ w c₀ c₁
    have hmca := Lvm6.Aff.card_excSet_le_nAff dom (by rw [hn]; exact hp.2.1)
      (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u))
    rw [hn] at h hmca
    have h' : S.card ≤ (excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d
        p.A).card + 2 * jl n (p.A - 1) d * Fintype.card F := h
    calc (S.card : ℚ) ≤ ((excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d
            p.A).card : ℚ) + 2 * jl n (p.A - 1) d * (Fintype.card F : ℚ) := by exact_mod_cast h'
      _ ≤ nAff (Fintype.card F) n d p.A p.mm p.D p.Bb + 2 * jl n (p.A - 1) d * (Fintype.card F : ℚ) := by
          gcongr
      _ ≤ p.N := hp.2.2
  have hinj : (univ.filter fun u : Fin 2 → F ↦ ¬ ((b = true → TViol dom (foldQ dom (u 0) (u 1) Q)
        (foldFn W (u 0)) (foldClaim σ (u 0) (u 1) u₀ w c₀ c₁) p.A d (pullT dom Q p.A d (u 0) (u 1) B)) ∧
        RGood dom Q W σ p.A d ⟨u₀, w, c₀, c₁, u 0, u 1⟩)).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun u ↦ (u 0, u 1)) (fun u hu ↦ ?_) (fun u _ v _ huv ↦ ?_)
    · have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      refine Finset.mem_coe.mpr ?_
      by_cases hx : (u 0, u 1) ∈ excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d p.A
      · exact Finset.mem_union_right _ hx
      refine Finset.mem_union_left _ ?_
      by_cases hc : ClaimBack dom Q W σ p.A d (u 0) (u 1) u₀ w c₀ c₁
      · have hb : b = true ∧ ¬ TViol dom (foldQ dom (u 0) (u 1) Q) (foldFn W (u 0))
            (foldClaim σ (u 0) (u 1) u₀ w c₀ c₁) p.A d (pullT dom Q p.A d (u 0) (u 1) B) := by
          by_contra hno
          refine hu' ⟨fun hb ↦ ?_, hx, hc⟩
          by_contra ht
          exact hno ⟨hb, ht⟩
        have hm : (u 0, u 1) ∈ foldEsc dom Q W σ p.A d B u₀ w c₀ c₁ := by
          rw [foldEsc, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hb.2⟩
        exact foldBadR_mono dom _ _ _ _ _ _ _ _ _ _ _ (Bp := fun q ↦ B (joinT q.1 q.2)) (Bp' := Bp)
          (fun q hq ↦ Or.inl ⟨hb.1, hq⟩)
          (foldEsc_sub_foldBadR dom Q W σ p.A d B u₀ w c₀ c₁ hm)
      · by_contra hno
        refine hc (claimBack_of_not_mem dom Q W σ p.A d u₀ w c₀ c₁ (u 0, u 1) fun hm ↦ hno ?_)
        exact foldBadR_mono dom _ _ _ _ _ _ _ _ _ _ _ (Bp := violP W σ) (Bp' := Bp) (fun q hq ↦ Or.inr hq) hm
    · simp only [Prod.mk.injEq] at huv
      funext i
      fin_cases i
      · exact huv.1
      · exact huv.2
  exact_mod_cast (Nat.cast_le.mpr hinj).trans hS

end Facts

/-! ## The rounds with the conjunct -/

section Rounds

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] (I : ChalIface F) {n m : ℕ} (dom : Fin n ↪ F)
  {εmax : ℝ≥0∞}

/-- **One fold round with the extractor's conjunct** (`b = true`: `roundSpecJ`'s doom as well): from `J` (and,
when `b`, `TViol` at `A − 1`) to `J`, (when `b`) the doom at `A`, and **`RGood` unconditionally**; the escape
is `eRound g p`, as `roundSpecJ`'s. -/
noncomputable def roundSpecU (J : List (ℕ × ℕ × Word) → Prop) (b : Bool) (g : ℕ) (hg : g ≤ I.gmax) {d : ℕ}
    {p : RoundPar} (hp : RoundOK (Fintype.card F) n d p) (he : eRound F g p < 1)
    (heT : eRound F g p ≤ εmax) (Qf : List (ℕ × ℕ × Word) → Wd F n (m + 1))
    (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (B : List (ℕ × ℕ × Word) → Tup F (m + 1) → Prop) :
    Spec (roundP I g)
      (fun h ↦ J (commits h) ∧ (b = true → TViol dom (Qf (commits h)) W σ (p.A - 1) d (B (commits h))))
      (fun r h ↦ J (commits h) ∧ (b = true → roundPost dom Qf W σ p.A d B r (commits h)) ∧
        RGood dom (Qf (commits h)) W σ p.A d r) εmax 0 0 := by
  classical
  have h0 : (0 : ℝ≥0∞) ≤ εmax := by positivity
  set Inv : List (ℕ × ℕ × Word) → Prop := fun cs ↦
    J cs ∧ (b = true → TViol dom (Qf cs) W σ (p.A - 1) d (B cs))
  unfold roundP
  refine (readFSpec I (Inv := Inv) h0).bind' fun u₀ ↦ (readFSpec I (Inv := Inv) h0).bind' fun w ↦
    (readFSpec I (Inv := Inv) h0).bind' fun c₀ ↦ (readFSpec I (Inv := Inv) h0).bind' fun c₁ ↦ ?_
  refine ((I.grpSpec g 1 hg Inv (fun u cs ↦ J cs ∧ (b = true → TViol dom (foldQ dom (u 0) (u 1) (Qf cs))
      (foldFn W (u 0)) (foldClaim σ (u 0) (u 1) u₀ w c₀ c₁) p.A d
      (pullT dom (Qf cs) p.A d (u 0) (u 1) (B cs))) ∧ RGood dom (Qf cs) W σ p.A d ⟨u₀, w, c₀, c₁, u 0, u 1⟩)
      (eRound F g p) he fun cs hI ↦ ?_).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) heT le_rfl le_rfl).bind' fun v ↦ ?_
  · unfold grpE eRound
    gcongr
    refine le_trans (Finset.card_le_card (t := univ.filter fun u : Fin 2 → F ↦ ¬ ((b = true → TViol dom
      (foldQ dom (u 0) (u 1) (Qf cs)) (foldFn W (u 0)) (foldClaim σ (u 0) (u 1) u₀ w c₀ c₁)
      p.A d (pullT dom (Qf cs) p.A d (u 0) (u 1) (B cs))) ∧
      RGood dom (Qf cs) W σ p.A d ⟨u₀, w, c₀, c₁, u 0, u 1⟩)) fun u hu ↦ ?_) ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact fun h ↦ hu ⟨hI.1, h⟩
    · exact card_rbad_le dom hp b _ W σ _ hI.2 u₀ w c₀ c₁
  · exact (Spec.ret (Post := fun r h ↦ J (commits h) ∧ (b = true → roundPost dom Qf W σ p.A d B r (commits h)) ∧
        RGood dom (Qf (commits h)) W σ p.A d r)
      ⟨u₀, w, c₀, c₁, v.getD 0 0, v.getD 1 0⟩).mono (fun h hG ↦ hG) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl

/-- **The extractor's facts of a level's rounds**: round `s ∈ [t, t + j)` at threshold `Ar s` on the word folded
by the earlier rounds, with the claim folded likewise (`RGood`, first round first). -/
def GoodRs (Ar : ℕ → ℕ) (d : ℕ) : (j t : ℕ) → List (Rnd F) → Wd F n (m + j) → (Tup F (m + j) →ₗ[F] F) →
    F → Prop
  | 0, _, _, _, _, _ => True
  | j + 1, t, rs, Q, W, σ =>
    RGood dom Q W σ (Ar t) d (rs.headD default) ∧
      GoodRs Ar d j (t + 1) rs.tail (foldQ dom (rs.headD default).α (rs.headD default).β Q)
        (foldFn W (rs.headD default).α)
        (foldClaim σ (rs.headD default).α (rs.headD default).β (rs.headD default).u₀ (rs.headD default).w
          (rs.headD default).c₀ (rs.headD default).c₁)

omit [DecidableEq F] in
theorem goodRs_succ (Ar : ℕ → ℕ) (d j t : ℕ) (rs : List (Rnd F)) (Q : Wd F n (m + (j + 1)))
    (W : Tup F (m + (j + 1)) →ₗ[F] F) (σ : F) :
    GoodRs dom Ar d (j + 1) t rs Q W σ ↔ RGood dom Q W σ (Ar t) d (rs.headD default) ∧
      GoodRs dom Ar d j (t + 1) rs.tail (foldQ dom (rs.headD default).α (rs.headD default).β Q)
        (foldFn W (rs.headD default).α)
        (foldClaim σ (rs.headD default).α (rs.headD default).β (rs.headD default).u₀ (rs.headD default).w
          (rs.headD default).c₀ (rs.headD default).c₁) := Iff.rfl

/-- **The fold rounds of a level with the extractor's conjunct**: `roundsSpecJ` with its doom under `b = true`,
and `GoodRs` at W1's thresholds `(par s).A` **unconditionally**; escapes as `roundsSpecJ`'s. -/
noncomputable def roundsSpecU (J : List (ℕ × ℕ × Word) → Prop) (b : Bool) (g : ℕ) (hg : g ≤ I.gmax) {d : ℕ}
    (par : ℕ → RoundPar) :
    (j t : ℕ) → (∀ s, t ≤ s → s < t + j → RoundOK (Fintype.card F) n d (par s)) →
      (∀ s, t ≤ s → s < t + j → eRound F g (par s) < 1) →
      (∀ s, t ≤ s → s < t + j → eRound F g (par s) ≤ εmax) →
      (∀ s, t ≤ s → s + 1 < t + j → (par s).A ≤ (par (s + 1)).A - 1) →
      (Qf : List (ℕ × ℕ × Word) → Wd F n (m + j)) → (W : Tup F (m + j) →ₗ[F] F) →
      (σ : F) → (a : ℕ) → (0 < j → a ≤ (par t).A - 1) →
      (B : List (ℕ × ℕ × Word) → Tup F (m + j) → Prop) →
      Spec (roundsP I g j)
        (fun h ↦ J (commits h) ∧ (b = true → TViol dom (Qf (commits h)) W σ a d (B (commits h))))
        (fun rs h ↦ J (commits h) ∧ (b = true → roundsPost dom par d j t Qf W σ a B rs (commits h)) ∧
          GoodRs dom (fun s ↦ (par s).A) d j t rs (Qf (commits h)) W σ) εmax 0 0
  | 0, t, _, _, _, _, Qf, W, σ, a, _, B =>
    (Spec.ret (Post := fun rs h ↦ J (commits h) ∧
        (b = true → roundsPost dom par d 0 t Qf W σ a B rs (commits h)) ∧
        GoodRs dom (fun s ↦ (par s).A) d 0 t rs (Qf (commits h)) W σ) []).mono
      (fun _ hv ↦ ⟨hv.1, hv.2, trivial⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | j + 1, t, hpar, he, heT, hchain, Qf, W, σ, a, ha, B =>
    ((roundSpecU I dom J b g hg (hpar t le_rfl (by omega)) (he t le_rfl (by omega))
        (heT t le_rfl (by omega)) Qf W σ B).mono
        (fun _ hv ↦ ⟨hv.1, fun hb ↦ (hv.2 hb).mono (ha (by omega)) le_rfl fun _ h ↦ h⟩) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl).bind'
      fun r ↦ ((roundsSpecU (fun cs ↦ J cs ∧ RGood dom (Qf cs) W σ (par t).A d r) b g hg par j (t + 1)
          (fun s h1 h2 ↦ hpar s (by omega) (by omega)) (fun s h1 h2 ↦ he s (by omega) (by omega))
          (fun s h1 h2 ↦ heT s (by omega) (by omega)) (fun s h1 h2 ↦ hchain s (by omega) (by omega))
          (fun cs ↦ foldQ dom r.α r.β (Qf cs)) (foldFn W r.α)
          (foldClaim σ r.α r.β r.u₀ r.w r.c₀ r.c₁) (par t).A
          (fun hj ↦ hchain t le_rfl (by omega))
          (fun cs ↦ pullT dom (Qf cs) (par t).A d r.α r.β (B cs))).mono
          (fun _ hv ↦ ⟨⟨hv.1, hv.2.2⟩, hv.2.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun rs ↦
        (Spec.ret (Post := fun rs h ↦ J (commits h) ∧
            (b = true → roundsPost dom par d (j + 1) t Qf W σ a B rs (commits h)) ∧
            GoodRs dom (fun s ↦ (par s).A) d (j + 1) t rs (Qf (commits h)) W σ)
          (r :: rs)).mono (fun _ hv ↦ ⟨hv.1.1, hv.2.1, (goodRs_succ dom _ d j t (r :: rs) _ W σ).2
            ⟨hv.1.2, hv.2.2⟩⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## X4's `GoodL` shape -/

/-- **X4's `GoodL` on rounds**: start agreement `a`, round `s` of `j` outside the exceptional pairs at
threshold `a − (j − 1 − s)` (first round first). `GoodL d dom j (rs.map fun r ↦ (r.α, r.β)) Q a` is this
(`List.headD` of the map is the map of `headD`; `default : Rnd F` has `α = β = 0`). -/
def GoodLv (d : ℕ) : (j : ℕ) → List (Rnd F) → Wd F n (m + j) → ℕ → Prop
  | 0, _, _, _ => True
  | j + 1, rs, Q, a =>
    GoodLv d j rs.tail (foldQ dom (rs.headD default).α (rs.headD default).β Q) a ∧
      NoExc dom Q d (a - j) (rs.headD default).α (rs.headD default).β

omit [DecidableEq F] in
/-- **`GoodRs` gives X4's `GoodL`** whenever every round's threshold is at most the level's start agreement
less the rounds after it. -/
theorem goodRs_goodLv {Ar : ℕ → ℕ} {d : ℕ} : ∀ (j t : ℕ) (rs : List (Rnd F)) (Q : Wd F n (m + j))
    (W : Tup F (m + j) →ₗ[F] F) (σ : F) (a : ℕ),
    (∀ s, t ≤ s → s < t + j → Ar s + (t + j - 1 - s) ≤ a) →
    GoodRs dom Ar d j t rs Q W σ → GoodLv dom d j rs Q a
  | 0, _, _, _, _, _, _, _, _ => trivial
  | j + 1, t, rs, Q, W, σ, a, hA, hG => by
    rw [goodRs_succ] at hG
    refine ⟨goodRs_goodLv j (t + 1) rs.tail _ _ _ a (fun s h1 h2 ↦ ?_) hG.2, hG.1.1.mono dom ?_⟩
    · have := hA s (by omega) (by omega)
      omega
    · have := hA t le_rfl (by omega)
      omega

/-- Thresholds increasing by at least one per round. -/
theorem add_le_of_step {Ar : ℕ → ℕ} {t j : ℕ}
    (hstep : ∀ s, t ≤ s → s + 1 < t + j → Ar s + 1 ≤ Ar (s + 1)) :
    ∀ k s, t ≤ s → s + k < t + j → Ar s + k ≤ Ar (s + k)
  | 0, _, _, _ => le_rfl
  | k + 1, s, h1, h2 => by
    have := add_le_of_step hstep k s h1 (by omega)
    have := hstep (s + k) (by omega) (by omega)
    rw [show s + (k + 1) = s + k + 1 by omega]
    omega

omit [DecidableEq F] in
/-- **At the level's last threshold**: with W1's thresholds increasing by at least one per round, `GoodRs`
gives X4's `GoodL` at start agreement `Ar (t + j − 1)` (W1's `aOut` for `j > 0`). -/
theorem goodRs_goodLv_last {Ar : ℕ → ℕ} {d j t : ℕ}
    (hstep : ∀ s, t ≤ s → s + 1 < t + j → Ar s + 1 ≤ Ar (s + 1)) (rs : List (Rnd F)) (Q : Wd F n (m + j))
    (W : Tup F (m + j) →ₗ[F] F) (σ : F) (hG : GoodRs dom Ar d j t rs Q W σ) :
    GoodLv dom d j rs Q (Ar (t + j - 1)) :=
  goodRs_goodLv dom j t rs Q W σ _ (fun s h1 h2 ↦ by
    have := add_le_of_step hstep (t + j - 1 - s) s h1 (by omega)
    rwa [show s + (t + j - 1 - s) = t + j - 1 by omega] at this) hG

/-- W1's chain (`(par s).A ≤ (par (s + 1)).A − 1`) with `RoundOK` (so `2 ≤ A`) is a step of at least one. -/
theorem step_of_chain {q d : ℕ} {par : ℕ → RoundPar} {t j : ℕ}
    (hpar : ∀ s, t ≤ s → s < t + j → RoundOK q n d (par s))
    (hchain : ∀ s, t ≤ s → s + 1 < t + j → (par s).A ≤ (par (s + 1)).A - 1) :
    ∀ s, t ≤ s → s + 1 < t + j → (par s).A + 1 ≤ (par (s + 1)).A := by
  intro s h1 h2
  have hc := hchain s h1 h2
  have hp := (hpar (s + 1) (by omega) h2).1
  have h2A : 1 ≤ (par (s + 1)).A := by
    by_contra h0
    have : (par (s + 1)).A - 1 = 0 := by omega
    rw [this] at hp
    simp at hp
  omega

end Rounds

/-! ## The level transitions and the final level (F-X6b-3) -/

section Trans

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n n' m' : ℕ} (L : TailIface F n n' m')

/-- **The transition fact** at a level's query group `(v, λ)` (F-X6b-3): every member `U` of the next level's
list (degree `≤ d'`, agreement `≥ A'` with the next word `g`) satisfying the glued claim has a zero discrepancy
(`W (φ U) = σ`, `ood z U = y`, `φ U` = `f − hp` at the positions) and its candidate `cand hi U` agrees with the
folded word `f` on `≥ A` columns. -/
def TailBack (f : Wd F n 0) (g : Wd F n' m') (W : Tup F 0 →ₗ[F] F) (σ y : F) (A A' : ℕ) (hi : List F)
    (z : Fin (L.ko + 1) → F) (v : Fin (L.kq + 1) → F) (lam : F) : Prop :=
  ∀ U ∈ tupleList L.dom' g A' L.d',
    glued L W z lam (L.pos v) U = gluedC σ y lam (qVals L f hi (L.pos v)) →
    coefQ L W σ y z (L.pos v) (qVals L f hi (L.pos v)) U = 0 ∧
      A ≤ (agree L.dom (L.cand hi U) f).card

open Classical in
/-- **The transition's bad values** (no doom; the OOD group's `OodOK` only): at most `card_qryBad_le`'s count. A
member with a nonzero discrepancy has at most `t + 1` roots `λ`; members with zero discrepancy share the OOD
value, hence (`OodOK`) the message and the candidate, so the positions of a bad pair all fall in one agreement
set of size `< A`. -/
theorem card_tbad_le (f : Wd F n 0) (g : Wd F n' m') (W : Tup F 0 →ₗ[F] F) (σ y : F) (A A' : ℕ) (hi : List F)
    (z : Fin (L.ko + 1) → F) (hood : OodOK L z g A') (hgap : n' * L.d' < A' * A') :
    ((univ.filter fun u : Fin (L.kq + 2) → F ↦
        ¬ TailBack L f g W σ y A A' hi z (Fin.init u) (u (Fin.last _))).card : ℝ≥0∞) ≤
      (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * (((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) +
        Fintype.card F * ((Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) *
          (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ L.t) := by
  set Ls := tupleList L.dom' g A' L.d'
  set co := fun (v : Fin (L.kq + 1) → F) (U : Tup F m') ↦
    coefQ L W σ y z (L.pos v) (qVals L f hi (L.pos v)) U
  let PosBad : (Fin (L.kq + 1) → F) → Prop := fun v ↦
    ∃ U ∈ Ls, co v U = 0 ∧ (agree L.dom (L.cand hi U) f).card < A
  have hwit : ∀ v lam, ¬ TailBack L f g W σ y A A' hi z v lam →
      ∃ U ∈ Ls, ∑ j : Fin (L.t + 2), co v U j * lam ^ (j : ℕ) = 0 ∧
        ¬ (co v U = 0 ∧ A ≤ (agree L.dom (L.cand hi U) f).card) := by
    intro v lam hb
    simp only [TailBack, not_forall, exists_prop] at hb
    obtain ⟨U, hU, he, hn⟩ := hb
    exact ⟨U, hU, by rw [← glued_sub, he, sub_self], hn⟩
  have hlam : ∀ v, ((univ.filter fun lam ↦ ¬ TailBack L f g W σ y A A' hi z v lam).card : ℝ≥0∞) ≤
      (((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) + (if PosBad v then (Fintype.card F : ℝ≥0∞) else 0) := by
    intro v
    let R : Tup F m' → Finset F := fun U ↦
      univ.filter fun lam ↦ ∑ j : Fin (L.t + 2), co v U j * lam ^ (j : ℕ) = 0
    have hsub : (univ.filter fun lam ↦ ¬ TailBack L f g W σ y A A' hi z v lam) ⊆
        ((Ls.filter fun U ↦ co v U ≠ 0).biUnion R) ∪ (if PosBad v then univ else ∅) := by
      intro lam hl
      obtain ⟨U, hU, hz, hn⟩ := hwit v lam (Finset.mem_filter.mp hl).2
      by_cases hc : co v U = 0
      · have hp : PosBad v := ⟨U, hU, hc, by
          by_contra hlt
          exact hn ⟨hc, by omega⟩⟩
        simp [hp]
      · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨U, Finset.mem_filter.mpr ⟨hU, hc⟩, ?_⟩)
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hz
    have hR : ∀ U ∈ Ls.filter fun U ↦ co v U ≠ 0, (R U).card ≤ L.t + 1 := by
      intro U hU
      have hne : ∃ j, co v U j ≠ 0 := by
        by_contra hall
        simp only [not_exists, ne_eq, not_not] at hall
        exact (Finset.mem_filter.mp hU).2 (funext hall)
      exact LeanVM.Protocol.Whir.card_powerBatch_eq_zero_le (co v U) hne
    have h1 : ((Ls.filter fun U ↦ co v U ≠ 0).biUnion R).card ≤ (L.t + 1) * jl n' A' L.d' :=
      calc _ ≤ ∑ U ∈ Ls.filter fun U ↦ co v U ≠ 0, (R U).card := Finset.card_biUnion_le
        _ ≤ ∑ _U ∈ Ls.filter fun U ↦ co v U ≠ 0, (L.t + 1) := Finset.sum_le_sum hR
        _ = (Ls.filter fun U ↦ co v U ≠ 0).card * (L.t + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ jl n' A' L.d' * (L.t + 1) := Nat.mul_le_mul_right _
            ((Finset.card_filter_le _ _).trans (card_tupleList_le_jl L.dom' g A' L.d' hgap))
        _ = _ := by ring
    calc ((univ.filter fun lam ↦ ¬ TailBack L f g W σ y A A' hi z v lam).card : ℝ≥0∞)
        ≤ (((Ls.filter fun U ↦ co v U ≠ 0).biUnion R ∪ (if PosBad v then univ else ∅)).card : ℝ≥0∞) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (((Ls.filter fun U ↦ co v U ≠ 0).biUnion R).card : ℝ≥0∞) +
            ((if PosBad v then univ else ∅ : Finset F).card : ℝ≥0∞) := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ _ := add_le_add (by exact_mod_cast h1) (by split_ifs <;> simp)
  have hpos : ((univ.filter PosBad).card : ℝ≥0∞) ≤
      (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ L.t := by
    by_cases h0 : ∃ U₀ ∈ Ls, L.ood z U₀ = y ∧ (agree L.dom (L.cand hi U₀) f).card < A
    · obtain ⟨U₀, hU₀, hy₀, hlt₀⟩ := h0
      set S := agree L.dom (L.cand hi U₀) f
      have hS : S.card ≤ A - 1 := by omega
      have hsub : univ.filter PosBad ⊆ univ.filter fun v ↦ ∀ k, L.pos v k ∈ S := by
        intro v hv'
        obtain ⟨U, hU, hc, -⟩ := (Finset.mem_filter.mp hv').2
        have hkey : L.key U = L.key U₀ := by
          by_contra hk
          have := congrFun hc (Fin.succ 0)
          simp only [co, coefQ, Fin.cons_succ, Fin.cons_zero, Pi.zero_apply, sub_eq_zero] at this
          exact hood U hU U₀ hU₀ hk (this.trans hy₀.symm)
        have hφ := L.φ_key U U₀ hkey
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro k
        have := congrFun hc k.succ.succ
        simp only [co, coefQ, Fin.cons_succ, Pi.zero_apply, sub_eq_zero, qVals, evx,
          LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [mem_agree0]
        simp only [TailIface.cand, Pi.add_apply, Polynomial.eval_add, ← hφ, this]
        ring
      calc ((univ.filter PosBad).card : ℝ≥0∞)
          ≤ ((univ.filter fun v ↦ ∀ k, L.pos v k ∈ S).card : ℝ≥0∞) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * ((S.card : ℝ≥0∞) / n) ^ L.t := L.card_pos S
        _ ≤ _ := by gcongr
    · have : univ.filter PosBad = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun v _ ⟨U, hU, hc, hlt⟩ ↦ h0 ⟨U, hU, ?_, hlt⟩
        have := congrFun hc (Fin.succ 0)
        simpa [co, coefQ, sub_eq_zero] using this
      rw [this]
      simp
  have hsplit : (univ.filter fun u : Fin (L.kq + 2) → F ↦
        ¬ TailBack L f g W σ y A A' hi z (Fin.init u) (u (Fin.last _))).card =
      ∑ v : Fin (L.kq + 1) → F, (univ.filter fun lam ↦ ¬ TailBack L f g W σ y A A' hi z v lam).card := by
    rw [Finset.card_filter, ← (Fin.snocEquiv fun _ ↦ F).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun lam _ ↦ ?_
    simp [Fin.snocEquiv, Fin.init_snoc, Fin.snoc_last]
  rw [hsplit, Nat.cast_sum]
  calc ∑ v : Fin (L.kq + 1) → F,
        ((univ.filter fun lam ↦ ¬ TailBack L f g W σ y A A' hi z v lam).card : ℝ≥0∞)
      ≤ ∑ v : Fin (L.kq + 1) → F, ((((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) +
          (if PosBad v then (Fintype.card F : ℝ≥0∞) else 0)) := Finset.sum_le_sum fun v _ ↦ hlam v
    _ = (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * (((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) +
          Fintype.card F * ((univ.filter PosBad).card : ℝ≥0∞) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul, mul_comm (Fintype.card F : ℝ≥0∞)]
        push_cast
        ring
    _ ≤ _ := by gcongr

/-- **The final level's agreement** (F-X6b-3 at `P^fin`): W1's position fact and the row check (every
position in the agreement of the final polynomial with the folded word) give agreement `≥ A`. -/
theorem agree_of_posOK {Fv : FinIface F n} {A : ℕ} {P : Tup F 0}
    {f : Wd F n 0} {u : Fin (Fv.kq + 1) → F} (h : PosOK Fv A P f u)
    (hin : ∀ k, Fv.pos u k ∈ agree Fv.dom P f) : A ≤ (agree Fv.dom P f).card := by
  by_contra hlt
  obtain ⟨k, hk⟩ := h (by omega)
  exact hk (hin k)

end Trans

end Lvm6.Whir
