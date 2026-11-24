-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Folds.lean` (formal rev 40f877dc) as `LvmWhirFolds` for
-- lvm (WP-7). Changed: `foldRoundsSpec` reads the invariant on a view `V` of the commitments (lvm: the opening's
-- `viewC`; leanVM: `id`).
/-
  LeanVM.Protocol.Whir.Sound.Folds

  The specification of a WHIR level's fold rounds: the invariant `A(i, j)` (every member of the
  list of the level's oracle folded by its first `j` challenges violates the running claim) is
  kept by each round except at `2·L + 2^(ℓ−j)·E_mca` challenges.
-/
import LvmWhirProg
import LvmWhirLanes
import LvmWhirCounting
import LvmWhirProb

-- ===== merged from `LvmWhirEscape` (GOLF module merge: `LvmWhirEscape.lean` is now a stub importing `LvmWhirFolds`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Escape.lean` (formal rev 40f877dc) as `LvmWhirEscape`
-- for lvm (WP-7). Changed for the unique-decoding regime: the out-of-domain separation (`oodVal`, `OodSep`,
-- `card_oodSep_bad_le` and its helpers) and the three-term glue are cut with the step; `QueryGood`/`exists_agreeSet`
-- become `QueryGoodUd`/`exists_agreeSet_ud`, whose one candidate comes from the list bound (`card ≤ 1`) instead of
-- the out-of-domain answer; new: `mem_iList_of_close`, `FinViol` (the final level's doom after the residual) and
-- `exists_agreeSet_finViol`. The batching sums, `viol_of_close` and the final level's step are leanVM's.
/-
  LeanVM.Protocol.Whir.Sound.Escape

  The escape counts of a WHIR level interface in the unique-decoding regime: the query positions
  catch the one candidate of the next oracle's list unless they all land in an agreement set of
  fewer than `A` columns; and the level's batching challenge `λ` keeps every list member violating
  the glued claim except at `t·L` values (`t` on the final level, no list).
-/

/-!
# Escapes at the level interface

Annex B of the leanVM specification (leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), proof of Theorem `thm:rbr`, "Query
message" and "Batching challenge", for lvm's order of messages (`whirLevelsUd`): commitment of the
next oracle `O'`, the query positions, `λ`, the openings, the query intro polynomial. The level's
claims are glued with powers of `λ`: the running claim with `λ⁰`, the `t` consistency claims with
`λ^(1+q)`. On the final level the residual `f` is sent instead of `O'`. There is no out-of-domain
step: in the unique-decoding regime the next list has at most one member (`listMax = 1`).

* `QueryGoodUd`: after positions `qs`, every member `V` of the next list violates the running
  claim or the consistency claim at some queried column. `exists_agreeSet_ud`: under the doom
  before the positions and a list of at most one member, there is a set `A` of at most `thr − 1`
  columns such that positions breaking `QueryGoodUd` all lie in `A`: the one candidate `V*`
  either is close to the folded word, then it violates the running claim by the doom, or agrees
  with it on fewer than `thr` columns.
* `card_glue_bad_le_final`: a nonzero discrepancy polynomial of degree `t` in `λ` has at most `t`
  roots (the glue of a mid level and of the final level alike).
* The final level: `exists_agreeSet_final`, and `FinViol P C Φ σ G` (the residual `G` violates the
  running claim, or its encoding is not in the list of the folded word `C`), which the doom of every
  member implies (`finViol_of_viol`) and which suffices for the query step
  (`exists_agreeSet_finViol`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset CompPoly
  CMlPolynomialEval

section

/-! ## Batching sums -/

/-- The batched sum with `powers λ`: `Σ_q λ^q f(q)`. -/
theorem sum_zip_powersFrom (lam acc : E) (qs : List ℕ) (f : ℕ → E) :
    (((powersFrom acc lam qs.length).zip qs).map fun wq ↦ wq.1 * f wq.2).sum =
      ∑ k : Fin qs.length, acc * lam ^ (k : ℕ) * f qs[k] := by
  induction qs generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.length_cons, powersFrom, List.zip_cons_cons, List.map_cons, List.sum_cons, ih,
      Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun k _ ↦ ?_)
    simp only [pow_succ]
    ring_nf
    rfl

theorem sum_zip_powers (lam : E) (qs : List ℕ) (f : ℕ → E) :
    (((powers lam qs.length).zip qs).map fun wq ↦ wq.1 * f wq.2).sum =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) * f qs[k] := by
  rw [powers, sum_zip_powersFrom]
  simp

/-- `powers λ t` has `t` entries. -/
theorem length_powers (lam : E) (t : ℕ) : (powers lam t).length = t := by
  rw [powers]
  suffices h : ∀ acc, (powersFrom acc lam t).length = t from h 1
  induction t with
  | zero => intro; rfl
  | succ t ih => intro acc; simp [powersFrom, ih]

/-! ## Query positions -/

/-- An entry of a word at an integer position (`0` outside). -/
def wordAt {n : ℕ} (C : Fin n → E) (q : ℕ) : E := if h : q < n then C ⟨q, h⟩ else 0

/-- After positions `qs`, every member of the list of `Q'` violates the running claim `(Φ, σ)` or
the consistency claim at a queried column of the folded word `C`. -/
def QueryGoodUd (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (qs : List ℕ) : Prop :=
  ∀ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) ≠ σ ∨
    ∃ q ∈ qs, encAt P.κ P.R (joinMsg hκ (decode P' V)) q ≠ wordAt C q

/-- A message whose encoding agrees with the folded word on `thr` columns is in its list. -/
theorem mem_iList_of_close (P : LevelCode) (C : Fin P.n → E) (G : (Fin P.κ → Bool) → E)
    (hclose : P.thr ≤ (univ.filter fun x ↦ enc P.κ P.R G x = C x).card) :
    (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G) ∈ iList P.code P.thr fun _ ↦ C := by
  rw [mem_iList]
  refine ⟨fun _ ↦ ?_, _, hclose, fun _ x hx ↦ ((Finset.mem_filter.mp hx).2).symm⟩
  show _ ∈ rsCode (domain P.κ P.R P.h64) (2 ^ P.κ)
  rw [← range_enc P.h64]; exact LinearMap.mem_range_self _ _

/-- A message whose encoding agrees with the folded word on `thr` columns is caught by the
running claim. -/
theorem viol_of_close (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) (G : (Fin P.κ → Bool) → E)
    (hclose : P.thr ≤ (univ.filter fun x ↦ enc P.κ P.R G x = C x).card) :
    ∑ x, Φ (bitsL x) * G x ≠ σ := by
  have hmem : (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G) ∈ iList P.code P.thr fun _ ↦ C := by
    rw [mem_iList]
    refine ⟨fun _ ↦ ?_, _, hclose, fun _ x hx ↦ ((Finset.mem_filter.mp hx).2).symm⟩
    show _ ∈ rsCode (domain P.κ P.R P.h64) (2 ^ P.κ)
    rw [← range_enc P.h64]; exact LinearMap.mem_range_self _ _
  have := hviol _ hmem
  rwa [decode_enc P (fun _ ↦ G), claimSum_zero] at this

/-- **The query step** (unique decoding). Under the doom before the positions (every member of the
list of the folded word `C` violates `(Φ, σ)`) and a list of `Q'` with at most one member, the
positions breaking `QueryGoodUd` all lie in a set of at most `thr − 1` columns. -/
theorem exists_agreeSet_ud (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hone : (iList P'.code P'.thr Q').card ≤ 1) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodUd P P' hκ Q' C Φ σ qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hex : ∃ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) = σ
  · obtain ⟨V₀, hV₀, hclaim⟩ := hex
    set G := joinMsg hκ (decode P' V₀)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact viol_of_close P C Φ σ hviol G (Nat.lt_succ_iff.mp (not_le.mp hlt))
        (by rw [sum_joinMsg]; exact hclaim)
    · intro hlt
      simp only [QueryGoodUd, not_forall, not_or, not_not, exists_prop, not_exists,
        not_and] at hqs
      obtain ⟨V, hV, -, hall⟩ := hqs
      have hVV : V = V₀ := Finset.card_le_one.mp hone _ hV _ hV₀
      subst hVV
      have h := hall q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd ?_ hqs⟩
    intro V hV
    exact Or.inl fun h ↦ hex ⟨V, hV, h⟩

/-! ## The batching challenge -/

/-- **The final batching step.** If the residual violates the running claim or a consistency
claim, the glued claim with powers `1, λ, …, λ^t` holds at at most `t` values `λ`. -/
theorem card_glue_bad_le_final {t : ℕ} (a σ : E) (e c : Fin t → E)
    (h : a ≠ σ ∨ ∃ k, e k ≠ c k) :
    (univ.filter fun lam : E ↦ a + lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k =
        σ + lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k).card ≤ t := by
  let d : Fin (t + 1) → E := Fin.cons (a - σ) fun k ↦ e k - c k
  have hd : ∃ k, d k ≠ 0 := by
    rcases h with h | ⟨k, hk⟩
    · exact ⟨0, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨k.succ, by simpa [d, sub_eq_zero] using hk⟩
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans (card_powerBatch_eq_zero_le d hd)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
  have hs : ∑ k : Fin t, (e k - c k) * lam ^ ((k : ℕ) + 1) =
      lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k - lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [d, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, hs]
  linear_combination hlam

/-! ## The final level's query step -/

/-- After positions `qs` on the final level, the residual `G` violates the running claim or the
consistency claim at a queried column. -/
def QueryGoodFinal (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (qs : List ℕ) : Prop :=
  ∑ x, Φ (bitsL x) * G x ≠ σ ∨ ∃ q ∈ qs, encAt P.κ P.R G q ≠ wordAt C q

/-- **The final query step.** Positions breaking `QueryGoodFinal` lie in a set of at most
`thr − 1` columns. -/
theorem exists_agreeSet_final (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) (G : (Fin P.κ → Bool) → E) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodFinal P C Φ σ G qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hc : ∑ x, Φ (bitsL x) * G x = σ
  · refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact viol_of_close P C Φ σ hviol G (Nat.lt_succ_iff.mp (not_le.mp hlt)) hc
    · simp only [QueryGoodFinal, not_or, not_not, not_exists, not_and] at hqs
      intro hlt
      have h := hqs.2 q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd (Or.inl hc) hqs⟩

/-- **The final level's doom after the residual** `G`: `G` violates the running claim, or its
encoding is not in the list of the folded word `C`. -/
def FinViol (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) : Prop :=
  ∑ x, Φ (bitsL x) * G x ≠ σ ∨
    (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G) ∉ iList P.code P.thr fun _ ↦ C

/-- The doom of every member of the list implies the residual's. -/
theorem finViol_of_viol (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) (G : (Fin P.κ → Bool) → E) :
    FinViol P C Φ σ G := by
  by_cases hc : ∑ x, Φ (bitsL x) * G x = σ
  · refine Or.inr fun hmem ↦ ?_
    have := hviol _ hmem
    rw [decode_enc P (fun _ ↦ G), claimSum_zero] at this
    exact this hc
  · exact Or.inl hc

/-- **The final query step from the residual's doom.** Positions breaking `QueryGoodFinal` lie in
a set of at most `thr − 1` columns. -/
theorem exists_agreeSet_finViol (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (hD : FinViol P C Φ σ G) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodFinal P C Φ σ G qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hc : ∑ x, Φ (bitsL x) * G x = σ
  · have hfar : (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G) ∉ iList P.code P.thr fun _ ↦ C :=
      hD.resolve_left (not_not.mpr hc)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact hfar (mem_iList_of_close P C G (Nat.lt_succ_iff.mp (not_le.mp hlt)))
    · simp only [QueryGoodFinal, not_or, not_not, not_exists, not_and] at hqs
      intro hlt
      have h := hqs.2 q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd (Or.inl hc) hqs⟩

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirEscape` =====

-- ===== merged from `LvmWhirState` (GOLF module merge: `LvmWhirState.lean` is now a stub importing `LvmWhirFolds`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/State.lean` (formal rev 40f877dc) as `LvmWhirState` for
-- lvm (WP-7). Cut: `glue_two` (the out-of-domain glue).
/-
  LeanVM.Protocol.Whir.Sound.State

  The meaning of the WHIR verifier's running state: the running weight it owes at the terminal
  point (`runW`), the shape of its round polynomial, the effect of a fold and of gluing a level's
  claims, and the lane oracles the committed words define.
-/

/-!
# The running state of `verify_whir`

`LeanVM.Protocol.Verifier.WhirState` (`verify_whir`'s locals `running_target`, `running_quad`,
`folds`, `glued`, leanVM `40f877dc`, `crates/verifier/src/whir.rs:141-265`) holds the running
claim as a target value and a list of glued claims whose weights are only evaluated at the
terminal point. This module reads it as a
weighted claim:

* `runW w ℓ₀ s x`: the running weight at the point `x` of the remaining variables. It is literally
  the terminal check's `weight` at `x = tail_folds`: the opening weight `w` at the rotated point
  `(folds ++ x)[ℓ₀:] ++ (folds ++ x)[:ℓ₀]`, plus each glued claim's scalar times its weight at
  `folds[fold_start:] ++ x`.
* `runW_fold`: a fold challenge `c` binds the first remaining variable,
  `runW (s with folds ++ [c]) x = runW s (c :: x)`; `isMultiaffine_runW`: the running weight is
  multiaffine in the remaining variables.
* `QuadOK quad σ`: the round polynomial has three coefficients and `q(0) + q(1) = σ`, which
  `sumcheckRoundPoly 3 σ none` guarantees by construction (`quadOK_roundPoly`).
* `glue`: gluing claims adds their weights with the powers of `λ` to the running weight and their
  values to the target, and keeps `QuadOK` (`glue_one`; lvm glues one claim per level).
* `laneO i cs`: the lane oracle of commitment `i` of the commitments `cs`: lane `j` of column `v`
  is entry `j` of the reversed leaf (level `0`, `row.reverse.map ofK`) or of the leaf regrouped
  into `E` (deeper levels, `ext_row`). `enforcedSum_eq`: the verifier's `enforcedSum` of the
  opened rows is `Σ_q λ^q c[x_q]` with `c` the oracle folded by the level's challenges.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Finset

section

/-! ## The running weight -/

/-- The running weight of the state `s` at the point `x` of the remaining variables. -/
def runW (w : List E → E) (ℓ₀ : ℕ) (s : WhirStateT) (x : List E) : E :=
  s.glued.foldl (fun weight claim ↦
      weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ x))
    (w (rotL ℓ₀ (s.folds ++ x)))

/-- `foldl` of a sum is the initial value plus the sum. -/
theorem foldl_add_map {γ : Type*} (f : γ → E) (a : E) (l : List γ) :
    l.foldl (fun acc c ↦ acc + f c) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem runW_eq (w : List E → E) (ℓ₀ : ℕ) (s : WhirStateT) (x : List E) :
    runW w ℓ₀ s x = w (rotL ℓ₀ (s.folds ++ x)) +
      (s.glued.map fun c ↦ c.scalar * c.weightAt (s.folds.drop c.foldStart ++ x)).sum :=
  foldl_add_map _ _ _

/-- Every glued claim started at or before the current fold and owes a multiaffine weight on the
variables left when it was glued. -/
def GluedOK (μ : ℕ) (s : WhirStateT) : Prop :=
  ∀ c ∈ s.glued, c.foldStart ≤ s.folds.length ∧ IsMultiaffine (μ - c.foldStart) c.weightAt

/-- **A fold binds the first remaining variable.** -/
theorem runW_fold (w : List E → E) (ℓ₀ : ℕ) (s : WhirStateT) (c t : E) (q : List E)
    (hg : ∀ g ∈ s.glued, g.foldStart ≤ s.folds.length) (x : List E) :
    runW w ℓ₀ { s with target := t, quad := q, folds := s.folds ++ [c] } x =
      runW w ℓ₀ s (c :: x) := by
  rw [runW_eq, runW_eq]
  dsimp only
  rw [List.append_assoc, List.singleton_append]
  refine congrArg (_ + ·) (congrArg List.sum (List.map_congr_left fun g hgm ↦ ?_))
  rw [List.drop_append_of_le_length (hg g hgm), List.append_assoc, List.singleton_append]

/-- A list sum of multiaffine weights is multiaffine. -/
theorem isMultiaffine_listSum_mem {n : ℕ} {γ : Type*} (xs : List γ) (F : γ → List E → E)
    (hF : ∀ a ∈ xs, IsMultiaffine n (F a)) :
    IsMultiaffine n fun l ↦ (xs.map fun a ↦ F a l).sum := by
  induction xs with
  | nil => simpa using (IsMultiaffine.zero (n := n))
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF a (List.mem_cons_self ..)).add (ih fun b hb ↦ hF b (List.mem_cons_of_mem _ hb))

/-- **The running weight is multiaffine** in the remaining variables. -/
theorem isMultiaffine_runW {μ : ℕ} {w : List E → E} (hw : IsMultiaffine μ w) {ℓ₀ : ℕ}
    (hℓ₀ : ℓ₀ ≤ μ) (s : WhirStateT) (hs : s.folds.length ≤ μ) (hg : GluedOK μ s) :
    IsMultiaffine (μ - s.folds.length) (runW w ℓ₀ s) := by
  have hrot : IsMultiaffine (s.folds.length + (μ - s.folds.length))
      fun l ↦ w (rotL ℓ₀ l) := by
    rw [Nat.add_sub_cancel' hs]; exact isMultiaffine_rotL hw hℓ₀
  have h1 := hrot.append s.folds rfl
  have key : ∀ c ∈ s.glued, IsMultiaffine (μ - s.folds.length)
      (fun x ↦ c.scalar * c.weightAt (s.folds.drop c.foldStart ++ x)) := by
    intro c hc
    obtain ⟨hfs, hma⟩ := hg c hc
    have heq : (s.folds.drop c.foldStart).length + (μ - s.folds.length) = μ - c.foldStart := by
      rw [List.length_drop]; (clear * - hs hfs; omega)
    have h' : IsMultiaffine ((s.folds.drop c.foldStart).length + (μ - s.folds.length))
        c.weightAt := by
      rw [heq]; exact hma
    exact (h'.append _ rfl).const_mul c.scalar
  have h2 : IsMultiaffine (μ - s.folds.length) fun x ↦
      (s.glued.map fun c ↦ c.scalar * c.weightAt (s.folds.drop c.foldStart ++ x)).sum :=
    isMultiaffine_listSum_mem s.glued
      (fun c x ↦ c.scalar * c.weightAt (s.folds.drop c.foldStart ++ x)) key
  have := h1.add h2
  intro l hl k hk X
  simp only [runW_eq]
  exact this l hl k hk X

/-! ## Round polynomials -/

/-- The round polynomial has three coefficients and `q(0) + q(1) = σ`. -/
def QuadOK (quad : List E) (σ : E) : Prop :=
  ∃ c₀ c₁ c₂, quad = [c₀, c₁, c₂] ∧ polyEval quad 0 + polyEval quad 1 = σ

/-- The quadratic `sumcheckRoundPoly 3 σ none` builds from `c₀` and `[c₂]` has `q(0)+q(1) = σ`. -/
theorem quadOK_roundPoly (σ c₀ c₂ : E) :
    QuadOK (c₀ :: (σ + sumE [c₂]) :: [c₂]) σ := by
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [polyEval_three, sumE, List.foldl_cons, List.foldl_nil, zero_add]
  ring_nf
  rw [show (2 : E) = 0 from CharTwo.two_eq_zero]
  ring

/-- The sum of two quadratics with a scalar keeps the coefficient form. -/
theorem quadOK_zipWith {q i : List E} {σ v : E} (hq : QuadOK q σ) (hi : QuadOK i v) (c : E) :
    QuadOK (List.zipWith (fun a b ↦ a + c * b) q i) (σ + c * v) := by
  obtain ⟨a₀, a₁, a₂, rfl, ha⟩ := hq
  obtain ⟨b₀, b₁, b₂, rfl, hb⟩ := hi
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, polyEval_three] at ha hb ⊢
  rw [← ha, ← hb]
  ring

/-! ## Gluing -/

/-- Gluing one claim (every lvm level): the consistency claims with `λ`. -/
theorem glue_one (lam : E) (s : WhirStateT) (e : E) (he : List E) (we : List E → E) :
    glueT lam s [(e, he, we)] =
      { target := s.target + 1 * lam * e
        quad := List.zipWith (fun q i ↦ q + 1 * lam * i) s.quad he
        folds := s.folds
        glued := s.glued ++ [⟨1 * lam, s.folds.length, we⟩] } := by
  simp [glueT]

/-- Glued claims at the current fold add their weights. -/
theorem runW_glue (w : List E → E) (ℓ₀ : ℕ) (s : WhirStateT) (new : List GluedClaim)
    (hnew : ∀ c ∈ new, c.foldStart = s.folds.length) (x : List E) :
    runW w ℓ₀ { s with glued := s.glued ++ new } x =
      runW w ℓ₀ s x + (new.map fun c ↦ c.scalar * c.weightAt x).sum := by
  rw [runW_eq, runW_eq]
  dsimp only
  rw [List.map_append, List.sum_append, add_assoc]
  refine congrArg (_ + ·) (congrArg (_ + ·) (congrArg List.sum (List.map_congr_left fun c hc ↦ ?_)))
  rw [hnew c hc, List.drop_length, List.nil_append]

/-! ## Lane oracles of committed words -/

/-- The word of commitment `i` (the empty word if there is none). -/
def wordOf (cs : List (ℕ × ℕ × Word)) (i : ℕ) : Word :=
  (cs[i]?.map fun c ↦ c.2.2).getD fun _ ↦ []

/-- The lanes of a leaf: reversed at level `0`, regrouped into `E` deeper. -/
def lanesOf (i : ℕ) (row : List K) : List E :=
  if i = 0 then row.reverse.map ofK else extRow row

/-- **The lane oracle of commitment `i`**: lane `j` of column `v`. -/
def laneO (i : ℕ) (cs : List (ℕ × ℕ × Word)) (n : ℕ) : ℕ → Fin n → E :=
  fun j v ↦ (lanesOf i (wordOf cs i v)).getD j 0

theorem length_extRow (m : ℕ) : ∀ (l : List K), l.length = 3 * m → (extRow l).length = m
  | c0 :: c1 :: c2 :: rest, h => by
    rw [extRow, List.length_cons]
    cases m with
    | zero => simp at h
    | succ m => rw [length_extRow m rest (by simp at h; (clear * - rest m h; omega))]
  | [c0, c1], h => by simp at h; (clear * - c0 c1 m h; omega)
  | [c0], h => by simp at h; (clear * - c0 m h; omega)
  | [], h => by simp at h; subst h; rfl

/-- The lanes of a well-shaped leaf: `2^ℓ` of them. -/
theorem length_lanesOf {i ℓ : ℕ} (row : List K)
    (h : row.length = if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ) : (lanesOf i row).length = 2 ^ ℓ := by
  unfold lanesOf
  split_ifs at h ⊢ with hi
  · simp [h]
  · exact length_extRow _ row h

/-- The word of a commitment that is present. -/
theorem wordOf_eq {cs : List (ℕ × ℕ × Word)} {i ht wd : ℕ} {W : Word}
    (hc : cs[i]? = some (ht, wd, W)) : wordOf cs i = W := by
  simp [wordOf, hc]

/-- **The enforced sum** of the opened rows is `Σ_q λ^q c[x_q]`, `c` the lane oracle folded by
the level's challenges. -/
theorem enforcedSum_eq (i : ℕ) (cs : List (ℕ × ℕ × Word)) {n ℓ : ℕ} (lf : List E)
    (hlf : lf.length = ℓ) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < n) (lam : E)
    (hshape : ∀ q ∈ qs, (wordOf cs i q).length = if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ) :
    enforcedSum ((qs.map (wordOf cs i)).map (lanesOf i)) lf (powers lam qs.length) =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) *
        wordAt (fun v : Fin n ↦ foldsN lf (laneO i cs n) 0 v) qs[k] := by
  rw [← sum_zip_powers]
  unfold enforcedSum
  rw [List.map_map]
  simp only
  have hzip : ∀ (ws : List E), ws.length = qs.length →
      (List.zip ws (qs.map (lanesOf i ∘ wordOf cs i))).foldl
          (fun total (wr : E × List E) ↦ total + wr.1 * dot wr.2 (eqKernel lf)) 0 =
        ((ws.zip qs).map fun wq ↦ wq.1 *
          wordAt (fun v : Fin n ↦ foldsN lf (laneO i cs n) 0 v) wq.2).sum := by
    intro ws hws
    rw [foldl_add_map (fun wr : E × List E ↦ wr.1 * dot wr.2 (eqKernel lf))]
    rw [zero_add, List.zip_map_right, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun wq hwq ↦ ?_)
    have hq := (List.of_mem_zip hwq).2
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    congr 1
    rw [dot_eqKernel _ _ (by rw [hlf]; exact length_lanesOf _ (hshape _ hq))]
    simp only [wordAt, hqs _ hq, ↓reduceDIte]
    rw [foldsN_apply lf (laneO i cs n)]
    rfl
  exact hzip _ (length_powers lam qs.length)

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirState` =====

-- ===== merged from `LvmWhirGeneric` (GOLF module merge: `LvmWhirGeneric.lean` is now a stub importing `LvmWhirFolds`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Generic.lean` (formal rev 40f877dc) as `LvmWhirGeneric` for lvm (WP-7).
/-
  LeanVM.Protocol.Whir.Sound.Generic

  Specifications of the verifier's prover moves for doom predicates that are functions of the
  commitments of the history: scalars, round polynomials, proofs of work and commitments keep
  them.
-/

/-!
# Moves under a commitment invariant

The WHIR doom predicates (`LeanVM.Protocol.Whir.Sound.Level`) depend on a history only through
its commitments (the oracles' words) and on values the program carries (its state, the
challenges). A scalar, a proof of work, a sample and an opening commit nothing, so such a
predicate is kept by every move but a commitment, where the new word is appended.

* `readInv`, `readNInv`, `roundPolyInv`: scalars and the round polynomial
  `sumcheckRoundPoly 3 σ none` keep the invariant; the round polynomial comes out in the form
  `QuadOK q σ`.
* `grindInv`: a proof of work keeps it, the follower's lead discounted by `2^-b`.
* `commitInv`: a commitment appends its word.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier VerifierProgram

section

/-! ## Commitments of histories -/

theorem commits_append (h l : List Ev) : commits (h ++ l) = commits h ++ commits l := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [commits, ih]

@[simp] theorem commits_read (h : List Ev) (x : E) : commits (h ++ [Ev.read x]) = commits h := by
  simp [commits_append, commits]

@[simp] theorem commits_grind (h : List Ev) (b : ℕ) : commits (h ++ [Ev.grind b]) = commits h := by
  simp [commits_append, commits]

@[simp] theorem commits_sample (h : List Ev) (c : E) :
    commits (h ++ [Ev.sample c]) = commits h := by
  simp [commits_append, commits]

@[simp] theorem commits_commit (h : List Ev) (ht wd : ℕ) (W : Word) :
    commits (h ++ [Ev.commit ht wd W]) = commits h ++ [(ht, wd, W)] := by
  simp [commits_append, commits]

/-! ## Moves -/

/-- An invariant of the commitments. -/
abbrev CInv : Type := List (ℕ × ℕ × Word) → Prop

variable {εmax T : ENNReal}

/-- A scalar keeps a commitment invariant. -/
noncomputable def readInv (I : CInv) (hT : T ≤ εmax) :
    Spec readScalar (fun h ↦ I (commits h)) (fun _ h ↦ I (commits h)) εmax 0 T :=
  Spec.readE (fun h₀ x hI ↦ by simpa using hI) hT

/-- `n` scalars keep a commitment invariant (lead at most the follower's). -/
noncomputable def readNInv (I : CInv) (hT : T ≤ εmax) :
    (n : ℕ) → Spec (readScalars n) (fun h ↦ I (commits h))
      (fun xs h ↦ xs.length = n ∧ I (commits h)) εmax T T
  | 0 => (Spec.ret (Post := fun xs h ↦ xs.length = 0 ∧ I (commits h)) []).mono
      (fun _ h ↦ ⟨rfl, h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1 => ((readInv I (T := T) hT).bind' fun x ↦
      (readNInv I hT n).bind' fun xs ↦
        (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-- **A round polynomial** keeps a commitment invariant and has `q(0) + q(1) = σ`. -/
noncomputable def roundPolyInv (I : CInv) (σ : E) (hT : T ≤ εmax) :
    Spec (sumcheckRoundPoly 3 σ none) (fun h ↦ I (commits h))
      (fun q h ↦ QuadOK q σ ∧ I (commits h)) εmax 0 T :=
  (readInv I (T := T) hT).bind' fun c₀ ↦
    (readNInv I hT 1).bind' fun tail ↦
      (Spec.ret (c₀ :: (σ + sumE tail) :: tail)).mono
        (fun h hI ↦ ⟨by
          obtain ⟨hl, -⟩ := hI
          match tail, hl with
          | [c₂], _ => exact quadOK_roundPoly σ c₀ c₂, hI.2⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- A proof of work keeps a commitment invariant. -/
noncomputable def grindInv (I : CInv) (b : ℕ) (hT : (2 : ENNReal)⁻¹ ^ b * T ≤ εmax) :
    Spec (grindProofOfWork b) (fun h ↦ I (commits h)) (fun _ h ↦ I (commits h)) εmax 0 T :=
  Spec.grindP b (fun h₀ hI ↦ by simpa using hI) hT

/-- A commitment appends its word. -/
noncomputable def commitInv (I I' : CInv) (ht wd : ℕ)
    (hI : ∀ cs W, I cs → WellShaped wd W → I' (cs ++ [(ht, wd, W)])) (hT : T ≤ εmax) :
    Spec (readCommitment ht wd) (fun h ↦ I (commits h)) (fun _ h ↦ I' (commits h)) εmax 0 T :=
  Spec.commitP ht wd (fun h₀ W hI0 hW ↦ by simpa using hI _ W hI0 hW) hT

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirGeneric` =====

/-!
# The fold rounds

`foldRounds ℓ s []` (`LeanVM.Protocol.Verifier.foldRounds`, `verify_whir`'s inner loop,
`crates/verifier/src/whir.rs:158-165` at leanVM `40f877dc`)
samples a challenge `c`, moves the running claim to `q(c)` and reads the next round polynomial.

`FoldInv` is the doom of the design note's `A(i, j)`, together with the bookkeeping the step needs:
the state has `pre + j` folds, `j ≤ ℓ`, the level's code has `κ = μ − pre − ℓ` message variables,
the glued claims are well formed (`GluedOK`), the round polynomial sums to the target
(`QuadOK`), and every member of the list of the level's oracle `laneO i cs` folded by the level's
`j` challenges (`foldsN lf`, `ℓ − j` lanes left) violates the running claim
`(runW w ℓ₀ s, s.target)`.

* `card_foldBad_le_eFold`: one round's escape count, `2·listMax + 2^(ℓ−j−1)·mcaMax`
  (`card_foldStep_bad_le`), at most `eFold P ℓ · |E|`.
* `foldRoundsSpec`: the rounds keep `FoldInv` with lead `eFold P ℓ` (the first round's escape;
  the later rounds' are smaller), and return in `FoldInv` with all `ℓ` challenges.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-- The fold rounds' escape bound at a level with `ℓ` folds:
`(2·listMax + 2^(ℓ−1)·mcaMax) / |E|`. -/
noncomputable def eFold (P : LevelCode) (ℓ : ℕ) : ENNReal :=
  ((2 * P.listMax + 2 ^ (ℓ - 1) * P.mcaMax : ℕ) : ENNReal) / Fintype.card E

section

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (ℓ pre : ℕ)

/-- **The fold invariant `A(i, j)`** after the challenges `lf` of level `i`. -/
def FoldInv (s : WhirStateT) (lf : List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  s.folds.length = pre + lf.length ∧ lf.length ≤ ℓ ∧ P.κ + pre + ℓ = μ ∧ GluedOK μ s ∧
    QuadOK s.quad s.target ∧
    Viol P (rowsOf (ℓ - lf.length) (foldsN lf (laneO i cs P.n))) (runW w ℓ₀ s) s.target

/-- The doom right after a fold challenge, before the next round polynomial. -/
def FoldMid (s : WhirStateT) (lf : List E) (c : E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  s.folds.length = pre + lf.length ∧ lf.length < ℓ ∧ P.κ + pre + ℓ = μ ∧ GluedOK μ s ∧
    Viol P (rowsOf (ℓ - (lf.length + 1)) (foldsN (lf ++ [c]) (laneO i cs P.n)))
      (fun r ↦ runW w ℓ₀ s (c :: r)) (polyEval s.quad c)

variable {μ ℓ₀ w i P ℓ pre}

open Classical in
/-- One round's escape: at most `2·listMax + 2^(ℓ−1)·mcaMax` challenges break the invariant. -/
theorem card_foldBad_le_eFold (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (s : WhirStateT)
    (lf : List E) (hlf : lf.length < ℓ) (cs : List (ℕ × ℕ × Word))
    (hI : FoldInv μ ℓ₀ w i P ℓ pre s lf cs) :
    (univ.filter fun c ↦ ¬ FoldMid μ ℓ₀ w i P ℓ pre s lf c cs).card ≤
      2 * P.listMax + 2 ^ (ℓ - 1) * P.mcaMax := by
  obtain ⟨hlen, -, hκ, hg, ⟨c₀, c₁, c₂, hq, hσ⟩, hviol⟩ := hI
  set m := ℓ - (lf.length + 1) with hm
  have hm1 : ℓ - lf.length = m + 1 := by (clear * - ℓ lf m μ ℓ₀ P pre s hlf hlen; omega)
  have hma : IsMultiaffine (m + 1 + P.κ) (runW w ℓ₀ s) := by
    have := isMultiaffine_runW hw hℓ₀ s (by (clear * - s μ ℓ₀ P ℓ pre lf hlf hlen hκ; omega)) hg
    rwa [show μ - s.folds.length = m + 1 + P.κ by (clear * - μ s m P ℓ₀ ℓ pre lf hlf hlen hκ hm1; omega)] at this
  rw [hm1] at hviol
  rw [hq] at hσ
  have hstep := card_foldStep_bad_le P (runW w ℓ₀ s) hma (foldsN lf (laneO i cs P.n)) s.target
    c₀ c₁ c₂ hσ hviol
  refine (Finset.card_le_card fun c hc ↦ ?_).trans (hstep.trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, FoldMid, not_and] at hc ⊢
    intro hv
    refine hc hlen hlf hκ hg ?_
    rw [hq]
    rwa [foldsN, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
      (by (clear * - m ℓ μ ℓ₀ w i P pre s lf hlf cs hlen c₀ c₁ c₂ hm1; omega)))) _

open Classical in
/-- The escape count as the calculus averages it. -/
theorem avg_foldBad_le (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (s : WhirStateT)
    (lf : List E) (hlf : lf.length < ℓ) (cs : List (ℕ × ℕ × Word))
    (hI : FoldInv μ ℓ₀ w i P ℓ pre s lf cs) :
    (Fintype.card E : ENNReal)⁻¹ *
      ((univ.filter fun c ↦ ¬ FoldMid μ ℓ₀ w i P ℓ pre s lf c cs).card : ENNReal) ≤
        eFold P ℓ := by
  rw [eFold, ENNReal.div_eq_inv_mul]
  gcongr
  exact_mod_cast card_foldBad_le_eFold hw hℓ₀ s lf hlf cs hI

/-- After the round polynomial: the invariant with one more challenge. -/
theorem foldInv_step (s : WhirStateT) (lf : List E) (c : E) (cs : List (ℕ × ℕ × Word))
    (quad : List E) (hmid : FoldMid μ ℓ₀ w i P ℓ pre s lf c cs)
    (hq : QuadOK quad (polyEval s.quad c)) :
    FoldInv μ ℓ₀ w i P ℓ pre
      { s with target := polyEval s.quad c, quad := quad, folds := s.folds ++ [c] }
      (lf ++ [c]) cs := by
  obtain ⟨hlen, hlf, hκ, hg, hviol⟩ := hmid
  refine ⟨by simp [hlen]; (clear * - pre lf μ P ℓ s; omega), by simp; (clear * - hlf; omega), hκ, fun g hgm ↦ ?_, hq, ?_⟩
  · obtain ⟨h1, h2⟩ := hg g hgm
    exact ⟨by simp; (clear * - g s μ P ℓ pre lf hlen hκ h1; omega), h2⟩
  · have hfun := funext (runW_fold w ℓ₀ s c (polyEval s.quad c) quad
      fun g hgm ↦ (hg g hgm).1)
    rw [hfun, List.length_append, List.length_singleton]
    exact hviol

variable (μ ℓ₀ w i P ℓ pre)

/-- **The fold rounds' specification**: from `FoldInv` with `n` rounds left on the view `V`
of the commitments (and an extra invariant `X` of the commitments, which the rounds do not
touch), the rounds keep the invariant
(each escaping at most `eFold P ℓ`) and return it with all `ℓ` challenges. -/
noncomputable def foldRoundsSpec {εmax : ENNReal} (V : List (ℕ × ℕ × Word) → List (ℕ × ℕ × Word))
    (X : CInv) (hw : IsMultiaffine μ w)
    (hℓ₀ : ℓ₀ ≤ μ) (hε : eFold P ℓ ≤ εmax) :
    (n : ℕ) → (s : WhirStateT) → (lf : List E) →
      Spec (foldRoundsT n s lf)
        (fun h ↦ (FoldInv μ ℓ₀ w i P ℓ pre s lf (V (commits h)) ∧ X (commits h)) ∧
          lf.length + n = ℓ)
        (fun r h ↦ (FoldInv μ ℓ₀ w i P ℓ pre r.1 r.2 (V (commits h)) ∧ X (commits h)) ∧
          r.2.length = ℓ)
        εmax (eFold P ℓ) 0
  | 0, s, lf => (Spec.ret (s, lf)).mono (fun _ h ↦ ⟨h.1, by simpa using h.2⟩)
      (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  | n + 1, s, lf =>
    ((Spec.sampleE (Pre := fun h ↦ (FoldInv μ ℓ₀ w i P ℓ pre s lf (V (commits h)) ∧ X (commits h)) ∧
          lf.length + (n + 1) = ℓ)
        (Post := fun c h ↦ (FoldMid μ ℓ₀ w i P ℓ pre s lf c (V (commits h)) ∧ X (commits h)) ∧
          lf.length + (n + 1) = ℓ) (εmax := εmax) (T := 0) (eFold P ℓ) fun h₀ hp ↦ by
        refine le_trans ?_ (avg_foldBad_le hw hℓ₀ s lf (by omega) (V (commits h₀)) hp.1.1)
        gcongr with c
        intro hm
        simp only [commits_sample]
        exact ⟨⟨hm, hp.1.2⟩, hp.2⟩).bind' fun c ↦
      (roundPolyInv (fun cs ↦ (FoldMid μ ℓ₀ w i P ℓ pre s lf c (V cs) ∧ X cs) ∧
          lf.length + (n + 1) = ℓ) (polyEval s.quad c) (T := eFold P ℓ) hε).bind' fun quad ↦
        (foldRoundsSpec V X hw hℓ₀ hε n
          { s with target := polyEval s.quad c, quad := quad, folds := s.folds ++ [c] }
          (lf ++ [c])).mono
          (fun h hp ↦ ⟨⟨foldInv_step s lf c (V (commits h)) quad hp.2.1.1 hp.1, hp.2.1.2⟩, by
            simp; omega⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

end

end
end LeanVM.Protocol.Whir.Sound
