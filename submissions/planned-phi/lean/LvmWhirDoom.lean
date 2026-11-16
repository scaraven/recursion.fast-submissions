-- New for lvm (WP-7): the commitment-level doom of a unique-decoding root (lvm's `C_rec`) and the facts the
-- extractor (WP-13) and the certificate (WP-14) consume (BLUEPRINT §6.2 "Correctness", §7.2): not doomed after the
-- commitment and after the final residual `f`, the unique close codeword's message folds to `f`, and off the
-- luck event its agreement set is the one `E` computes. Built on WP-6's `LvmUdMany` (`foldAll`,
-- `agreeSet_foldAll_eq`) and `LvmRS` (`card_iList_le_one`), and leanVM's candidate bridge (`LvmWhirCandidates`).
/-
  LeanVM.Protocol.Whir.Sound (lvm: the extractor's doom facts)

  The doom of a committed level-0 word in the unique-decoding regime, the final residual's doom,
  and the extraction facts: under neither, the word's unique candidate satisfies the relation,
  its blocks fold to the residual, and the agreement set of the folded word with the residual's
  encoding is the word's agreement set with the candidate's encoding (off the luck event).
-/
import LvmWhirSpec
import LvmMcaUd

-- ===== merged from `LvmUdMany` (GOLF module merge: `LvmUdMany.lean` is now a stub importing `LvmWhirDoom`) =====
section
-- WP-6 (UD). New: the fold by `ℓ` challenges at once, as `ℓ` one-coordinate folds (leanVM's row
-- convention: `Whir/Sound/Code.lean` `consRows`, `foldN`, bit `0` first), and its counts by
-- induction on `ℓ` from the per-round counts of `LvmMcaUd`.

/-!
# Mutual correlated agreement for `ℓ` challenges (unique decoding)

For an interleaved word `O` with rows `Fin ℓ → Bool` (row `u` is the word `f_u`) and challenges
`α : Fin ℓ → F`, `foldAll α O` folds bit `0` at `α 0`, then bit `1` at `α 1`, and so on
(leanVM's `foldsN` on `rowsOf`, first challenge on the low bit). `foldAll_eq_sum`: it is the
eq-weighted sum `Σ_u eq(α, u) f_u`, `eq(α, u) = Π_i (u_i ? α_i : 1 − α_i)`.

Given a per-round fold-list count `M` (`∀ ρ O, |foldBad C A O| ≤ |ρ| · M`, which
`CodeFacts.card_foldBad_le` provides, `M = mcaUd n k A` in the unique-decoding range):

* `card_foldAllBad_le`: the `α ∈ F^ℓ` with `Λ(foldAll α O) ≠ foldAll α '' Λ(O)` are at most a
  `(2^ℓ − 1) · M / |F|` fraction;
* **`nonempty_iList_of_card_close`** (mutual correlated agreement): if more than that fraction of
  the `α` make `Σ_u eq(α, u) f_u` close to the code at threshold `A`, then all rows `f_u` agree
  with codewords on one common set of at least `A` coordinates;
* `card_foldAllLuck_le`: the `α` for which a column on which `O` and `U` differ agrees after the
  fold are at most an `ℓ · n / |F|` fraction (Schwartz–Zippel for multilinear columns, the
  extractor's luck); `agreeSet_foldAll_eq` off that event.

WHIR's soundness analysis does not use these: its fold challenges are separate rounds
(`LvmMcaUd`). They are the statement over `α ∈ F^ℓ` for the extractor and for comparison.
-/

namespace LeanVM.Protocol.Whir.Ud

open Finset

variable {F : Type*} [Field F] {ι M : Type*}

/-! ## Rows on `m + 1` bits, split on the low bit -/

/-- The rows of a word on `m + 1` bits, split on the low bit (leanVM `consRows`). -/
def splitLow {m : ℕ} (Q : (Fin (m + 1) → Bool) → ι → M) : Bool × (Fin m → Bool) → ι → M :=
  fun r ↦ Q (Fin.cons r.1 r.2)

/-- Rejoin split rows (leanVM `unconsRows`). -/
def joinLow {m : ℕ} (Q : Bool × (Fin m → Bool) → ι → M) : (Fin (m + 1) → Bool) → ι → M :=
  fun u ↦ Q (u 0, Fin.tail u)

theorem splitLow_joinLow {m : ℕ} (Q : Bool × (Fin m → Bool) → ι → M) :
    splitLow (joinLow Q) = Q := by
  funext r
  simp [splitLow, joinLow]

theorem joinLow_splitLow {m : ℕ} (Q : (Fin (m + 1) → Bool) → ι → M) :
    joinLow (splitLow Q) = Q := by
  funext u
  simp [splitLow, joinLow, Fin.cons_self_tail]

section Reindex

variable [Fintype F] [Fintype ι] {ρ ρ' : Type*} [Fintype ρ] [Fintype ρ']

/-- Reindexing the rows keeps list membership. -/
theorem comp_mem_iList (C : Submodule F (ι → F)) {A : ℕ} {O U : ρ → ι → F} (f : ρ' → ρ)
    (hU : U ∈ iList C A O) : (fun r ↦ U (f r)) ∈ iList C A (fun r ↦ O (f r)) := by
  rw [mem_iList] at hU ⊢
  obtain ⟨hcw, S, hS, hag⟩ := hU
  exact ⟨fun r ↦ hcw (f r), S, hS, fun r x hx ↦ hag (f r) x hx⟩

/-- The list of the split word is the split of the list. -/
theorem iList_splitLow [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F)) (A : ℕ)
    {m : ℕ} (O : (Fin (m + 1) → Bool) → ι → F) :
    iList C A (splitLow O) = (iList C A O).image splitLow := by
  ext V
  rw [mem_image]
  constructor
  · intro hV
    refine ⟨joinLow V, ?_, splitLow_joinLow V⟩
    have := comp_mem_iList C (fun u : Fin (m + 1) → Bool ↦ (u 0, Fin.tail u)) hV
    rwa [show (fun u : Fin (m + 1) → Bool ↦ splitLow O (u 0, Fin.tail u)) = O from
      joinLow_splitLow O] at this
  · rintro ⟨U, hU, rfl⟩
    exact comp_mem_iList C (fun r : Bool × (Fin m → Bool) ↦ (Fin.cons r.1 r.2 : Fin (m + 1) → Bool)) hU

omit [Field F] [Fintype F] in
/-- The agreement set does not see the row order. -/
theorem agreeSet_splitLow [DecidableEq F] {m : ℕ} (O U : (Fin (m + 1) → Bool) → ι → F) :
    agreeSet (splitLow O) (splitLow U) = agreeSet O U := by
  ext x
  simp only [mem_agreeSet, splitLow]
  constructor
  · intro h u
    simpa [Fin.cons_self_tail] using h (u 0, Fin.tail u)
  · intro h r
    exact h _

end Reindex

/-! ## The fold by `m` challenges -/

/-- **The fold by `α ∈ F^m`**: bit `0` at `α 0` first, then the rest. The result has the single
row `Fin 0 → Bool`. -/
def foldAll : {m : ℕ} → (Fin m → F) → ((Fin m → Bool) → ι → F) → (Fin 0 → Bool) → ι → F
  | 0, _, O => O
  | _ + 1, α, O => foldAll (Fin.tail α) (fold (α 0) (splitLow O))

theorem foldAll_zero (α : Fin 0 → F) (O : (Fin 0 → Bool) → ι → F) : foldAll α O = O := rfl

theorem foldAll_succ {m : ℕ} (α : Fin (m + 1) → F) (O : (Fin (m + 1) → Bool) → ι → F) :
    foldAll α O = foldAll (Fin.tail α) (fold (α 0) (splitLow O)) := rfl

theorem foldAll_cons {m : ℕ} (s : F) (α : Fin m → F) (O : (Fin (m + 1) → Bool) → ι → F) :
    foldAll (Fin.cons s α : Fin (m + 1) → F) O = foldAll α (fold s (splitLow O)) := by
  rw [foldAll_succ, Fin.tail_cons, Fin.cons_zero]

omit [Field F] in
/-- `Fin.consEquiv` on constant fibres is `Fin.cons`. -/
theorem consEquiv_apply' {α : Type*} {m : ℕ} (p : α × (Fin m → α)) :
    (Fin.consEquiv fun _ : Fin (m + 1) ↦ α) p = Fin.cons p.1 p.2 := rfl

/-- The weight `eq(α, u) = Π_i (u_i ? α_i : 1 − α_i)`. -/
def eqW {m : ℕ} (α : Fin m → F) (u : Fin m → Bool) : F :=
  ∏ i, if u i then α i else 1 - α i

/-- **The fold is the eq-weighted sum** `Σ_u eq(α, u) O[u, x]` (Annex B, `def:interleaved`). -/
theorem foldAll_eq_sum : ∀ {m : ℕ} (α : Fin m → F) (O : (Fin m → Bool) → ι → F)
    (v : Fin 0 → Bool) (x : ι), foldAll α O v x = ∑ u, eqW α u * O u x
  | 0, α, O, v, x => by
    rw [foldAll_zero, Fintype.sum_unique]
    simp only [eqW, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact congrArg (O · x) (Subsingleton.elim _ _)
  | m + 1, α, O, v, x => by
    rw [foldAll_succ, foldAll_eq_sum, ← (Fin.consEquiv fun _ ↦ Bool).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp only [fold, splitLow, eqW, consEquiv_apply', Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.tail, ite_true, Bool.false_eq_true, ite_false]
    ring

/-! ## Counts over `α ∈ F^m` -/

section Counts

variable [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

omit [Field F] [DecidableEq F] in
/-- A count over `F × G` of a predicate on the first coordinate. -/
theorem card_filter_fst_add {G : Type*} [Fintype G] (P : F → Prop) (Q : F → G → Prop)
    [DecidablePred P] [∀ s, DecidablePred (Q s)] (R : F → G → Prop) [∀ s, DecidablePred (R s)]
    (hR : ∀ s g, R s g → P s ∨ Q s g) :
    (∑ s, (univ.filter (R s)).card) ≤
      (univ.filter P).card * Fintype.card G + ∑ s, (univ.filter (Q s)).card := by
  have h1 : ∀ s, (univ.filter (R s)).card ≤
      (if P s then Fintype.card G else 0) + (univ.filter (Q s)).card := by
    intro s
    by_cases hs : P s
    · simp only [hs, ite_true]
      exact (card_le_univ _).trans (Nat.le_add_right _ _)
    · simp only [hs, ite_false, zero_add]
      exact card_le_card fun g hg ↦ mem_filter.mpr ⟨mem_univ _,
        ((hR s g (mem_filter.mp hg).2).resolve_left hs)⟩
  refine (Finset.sum_le_sum fun s _ ↦ h1 s).trans ?_
  rw [Finset.sum_add_distrib, Finset.card_filter, Finset.sum_mul]
  gcongr with s
  split_ifs <;> simp

omit [Field F] [DecidableEq F] in
/-- A count over `Fin (m + 1) → F` as a sum over the first coordinate. -/
theorem card_filter_cons {m : ℕ} (P : (Fin (m + 1) → F) → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ s, (univ.filter fun α : Fin m → F ↦ P (Fin.cons s α)).card := by
  rw [card_filter, ← (Fin.consEquiv fun _ ↦ F).sum_comp, Fintype.sum_prod_type]
  simp only [card_filter, consEquiv_apply']
  rfl

open Classical in
/-- **The bad challenges of `m` folds**: if every word with rows `Bool × ρ` has at most `|ρ| M`
fold-bad challenges, the `α ∈ F^m` with `Λ(foldAll α O) ≠ foldAll α '' Λ(O)` are at most
`(2^m − 1) M |F|^(m−1)`. -/
theorem card_foldAllBad_le (C : Submodule F (ι → F)) (A K : ℕ)
    (hK : ∀ (ρ : Type) [Fintype ρ] (O : Bool × ρ → ι → F),
      (foldBad C A O).card ≤ Fintype.card ρ * K) :
    ∀ {m : ℕ} (O : (Fin m → Bool) → ι → F),
      (univ.filter fun α : Fin m → F ↦
          iList C A (foldAll α O) ≠ (iList C A O).image (foldAll α)).card * Fintype.card F ≤
        (2 ^ m - 1) * K * Fintype.card F ^ m
  | 0, O => by
    have : (univ.filter fun α : Fin 0 → F ↦
        iList C A (foldAll α O) ≠ (iList C A O).image (foldAll α)) = ∅ := by
      refine filter_eq_empty_iff.mpr fun α _ ↦ ?_
      simp only [foldAll_zero, ne_eq, not_not]
      exact (Finset.image_id' (s := iList C A O)).symm
    simp [this]
  | m + 1, O => by
    set q := Fintype.card F
    have hcard : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
    -- one round: a bad `cons s α` has `s` fold-bad or `α` bad for the folded word
    have hstep : ∀ s (α : Fin m → F),
        iList C A (foldAll (Fin.cons s α : Fin (m + 1) → F) O) ≠
            (iList C A O).image (foldAll (Fin.cons s α : Fin (m + 1) → F)) →
          s ∈ foldBad C A (splitLow O) ∨
            iList C A (foldAll α (fold s (splitLow O))) ≠
              (iList C A (fold s (splitLow O))).image (foldAll α) := by
      intro s α hbad
      by_contra hgood
      push Not at hgood
      obtain ⟨hs, hα⟩ := hgood
      rw [mem_foldBad, not_not, iList_splitLow] at hs
      apply hbad
      rw [foldAll_cons, hα, hs, image_image, image_image]
      exact congrArg (fun f ↦ (iList C A O).image f) (funext fun U ↦ (foldAll_cons s α U).symm)
    rw [card_filter_cons]
    have hsum := card_filter_fst_add (G := Fin m → F) (fun s ↦ s ∈ foldBad C A (splitLow O))
      (fun s α ↦ iList C A (foldAll α (fold s (splitLow O))) ≠
        (iList C A (fold s (splitLow O))).image (foldAll α)) _ hstep
    have hfb : (univ.filter fun s ↦ s ∈ foldBad C A (splitLow O)).card ≤ 2 ^ m * K := by
      rw [filter_mem_eq_inter, univ_inter, ← hcard]
      exact hK _ _
    have hih : ∀ s, (univ.filter fun α : Fin m → F ↦ iList C A (foldAll α (fold s (splitLow O))) ≠
        (iList C A (fold s (splitLow O))).image (foldAll α)).card * q ≤ (2 ^ m - 1) * K * q ^ m :=
      fun s ↦ card_foldAllBad_le C A K hK (fold s (splitLow O))
    have hG : Fintype.card (Fin m → F) = q ^ m := by simp [q]
    rw [hG] at hsum
    have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    calc (∑ s, (univ.filter fun α : Fin m → F ↦ iList C A (foldAll (Fin.cons s α : Fin (m + 1) → F) O) ≠
            (iList C A O).image (foldAll (Fin.cons s α : Fin (m + 1) → F))).card) * q
        ≤ ((univ.filter fun s ↦ s ∈ foldBad C A (splitLow O)).card * q ^ m +
            ∑ s, (univ.filter fun α : Fin m → F ↦
              iList C A (foldAll α (fold s (splitLow O))) ≠
                (iList C A (fold s (splitLow O))).image (foldAll α)).card) * q :=
          Nat.mul_le_mul_right _ hsum
      _ ≤ (2 ^ m * K * q ^ m) * q + ∑ _s : F, (2 ^ m - 1) * K * q ^ m := by
          rw [add_mul, Finset.sum_mul]
          exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hfb))
            (Finset.sum_le_sum fun s _ ↦ hih s)
      _ = (2 ^ (m + 1) - 1) * K * q ^ (m + 1) := by
          rw [Finset.sum_const, card_univ, smul_eq_mul, pow_succ, pow_succ]
          have : 2 ^ m * 2 - 1 = 2 ^ m + (2 ^ m - 1) := by omega
          rw [this]
          ring

open Classical in
/-- **Mutual correlated agreement over `α ∈ F^m`**: if more than a `(2^m − 1) M / |F|` fraction
of the challenges make `foldAll α O = Σ_u eq(α, u) O[u, ·]` close to the code at threshold `A`,
then the list of `O` is nonempty: all rows agree with codewords on one common set of at least `A`
coordinates. -/
theorem nonempty_iList_of_card_close (C : Submodule F (ι → F)) (A K : ℕ)
    (hK : ∀ (ρ : Type) [Fintype ρ] (O : Bool × ρ → ι → F),
      (foldBad C A O).card ≤ Fintype.card ρ * K)
    {m : ℕ} (O : (Fin m → Bool) → ι → F)
    (h : (2 ^ m - 1) * K * Fintype.card F ^ m <
      (univ.filter fun α : Fin m → F ↦ (iList C A (foldAll α O)).Nonempty).card *
        Fintype.card F) :
    (iList C A O).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  refine absurd ((Nat.mul_le_mul_right _ (card_le_card fun α hα ↦ ?_)).trans
    (card_foldAllBad_le C A K hK O)) (not_le.mpr h)
  rw [mem_filter] at hα ⊢
  refine ⟨mem_univ _, fun heq ↦ ?_⟩
  rw [heq, hne, image_empty] at hα
  exact not_nonempty_empty hα.2

omit [Fintype F] [DecidableEq ι] in
/-- Folding never shrinks the agreement set. -/
theorem agreeSet_subset_foldAll : ∀ {m : ℕ} (α : Fin m → F) (O U : (Fin m → Bool) → ι → F),
    agreeSet O U ⊆ agreeSet (foldAll α O) (foldAll α U)
  | 0, _, _, _ => subset_rfl
  | m + 1, α, O, U => by
    rw [foldAll_succ, foldAll_succ, ← agreeSet_splitLow]
    exact (agreeSet_subset_agreeSet_fold _ _ _).trans (agreeSet_subset_foldAll _ _ _)

open Classical in
/-- **The extractor's luck over `α ∈ F^m`**: the `α` for which some column on which `O` and `U`
differ agrees after the fold are at most `m n |F|^(m−1)`. -/
theorem card_foldAllLuck_le : ∀ {m : ℕ} (O U : (Fin m → Bool) → ι → F),
    (univ.filter fun α : Fin m → F ↦
        ¬ agreeSet (foldAll α O) (foldAll α U) ⊆ agreeSet O U).card * Fintype.card F ≤
      m * Fintype.card ι * Fintype.card F ^ m
  | 0, O, U => by simp [foldAll_zero]
  | m + 1, O, U => by
    set q := Fintype.card F
    have hstep : ∀ s (α : Fin m → F),
        ¬ agreeSet (foldAll (Fin.cons s α : Fin (m + 1) → F) O)
            (foldAll (Fin.cons s α : Fin (m + 1) → F) U) ⊆ agreeSet O U →
          ¬ agreeSet (fold s (splitLow O)) (fold s (splitLow U)) ⊆
              agreeSet (splitLow O) (splitLow U) ∨
            ¬ agreeSet (foldAll α (fold s (splitLow O))) (foldAll α (fold s (splitLow U))) ⊆
              agreeSet (fold s (splitLow O)) (fold s (splitLow U)) := by
      intro s α hbad
      by_contra hgood
      push Not at hgood
      apply hbad
      rw [foldAll_cons, foldAll_cons, ← agreeSet_splitLow]
      exact hgood.2.trans hgood.1
    rw [card_filter_cons]
    have hsum := card_filter_fst_add (G := Fin m → F)
      (fun s ↦ ¬ agreeSet (fold s (splitLow O)) (fold s (splitLow U)) ⊆
        agreeSet (splitLow O) (splitLow U))
      (fun s α ↦ ¬ agreeSet (foldAll α (fold s (splitLow O))) (foldAll α (fold s (splitLow U))) ⊆
        agreeSet (fold s (splitLow O)) (fold s (splitLow U))) _ hstep
    have hG : Fintype.card (Fin m → F) = q ^ m := by simp [q]
    rw [hG] at hsum
    have hl := card_foldLuck_le (splitLow O) (splitLow U)
    have hih : ∀ s, (univ.filter fun α : Fin m → F ↦
        ¬ agreeSet (foldAll α (fold s (splitLow O))) (foldAll α (fold s (splitLow U))) ⊆
          agreeSet (fold s (splitLow O)) (fold s (splitLow U))).card * q ≤
        m * Fintype.card ι * q ^ m :=
      fun s ↦ card_foldAllLuck_le (fold s (splitLow O)) (fold s (splitLow U))
    calc _ ≤ ((univ.filter fun s ↦ ¬ agreeSet (fold s (splitLow O)) (fold s (splitLow U)) ⊆
              agreeSet (splitLow O) (splitLow U)).card * q ^ m + ∑ s, (univ.filter fun α : Fin m → F ↦
              ¬ agreeSet (foldAll α (fold s (splitLow O))) (foldAll α (fold s (splitLow U))) ⊆
                agreeSet (fold s (splitLow O)) (fold s (splitLow U))).card) * q :=
          Nat.mul_le_mul_right _ hsum
      _ ≤ (Fintype.card ι * q ^ m) * q + ∑ _s : F, m * Fintype.card ι * q ^ m := by
          rw [add_mul, Finset.sum_mul]
          exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hl))
            (Finset.sum_le_sum fun s _ ↦ hih s)
      _ = (m + 1) * Fintype.card ι * q ^ (m + 1) := by
          rw [Finset.sum_const, card_univ, smul_eq_mul, pow_succ]
          ring

omit [Fintype F] [DecidableEq ι] in
/-- Off the luck event the agreement set of the fold is that of the word. -/
theorem agreeSet_foldAll_eq {m : ℕ} {α : Fin m → F} {O U : (Fin m → Bool) → ι → F}
    (h : agreeSet (foldAll α O) (foldAll α U) ⊆ agreeSet O U) :
    agreeSet (foldAll α O) (foldAll α U) = agreeSet O U :=
  Finset.Subset.antisymm h (agreeSet_subset_foldAll α O U)

omit [DecidableEq ι] in
/-- **The extractor's agreement set** (BLUEPRINT §6.2 step 5): let `U` be in the list of `O`, that
list have at most one member, `α` be neither fold-bad for `O` nor lucky for `(O, U)`. If a single
word `V` (the encoding of the final message) is in the list of `foldAll α O`, then
`V = foldAll α U`, and the columns where `foldAll α O` agrees with `V` are exactly those where
every row of `O` agrees with `U`. -/
theorem agreeSet_foldAll_of_mem (C : Submodule F (ι → F)) {A m : ℕ} {α : Fin m → F}
    {O U : (Fin m → Bool) → ι → F} {V : (Fin 0 → Bool) → ι → F}
    (hU : U ∈ iList C A O) (hone : (iList C A O).card ≤ 1)
    (hgood : iList C A (foldAll α O) = (iList C A O).image (foldAll α))
    (hluck : agreeSet (foldAll α O) (foldAll α U) ⊆ agreeSet O U)
    (hV : V ∈ iList C A (foldAll α O)) :
    V = foldAll α U ∧ agreeSet (foldAll α O) V = agreeSet O U := by
  rw [hgood, mem_image] at hV
  obtain ⟨U', hU', rfl⟩ := hV
  obtain rfl : U' = U := Finset.card_le_one.mp hone _ hU' _ hU
  exact ⟨rfl, agreeSet_foldAll_eq hluck⟩

end Counts

end LeanVM.Protocol.Whir.Ud
end
-- ===== end of `LvmUdMany` =====

/-!
# The commitment-level doom and the extractor's facts

Setting: a root committed as a level-0 word `W` (`2^(μ−6+R)` leaves of `2^6` `K`-words; lvm's
`C_rec`: `μ = 19`, `R = 2`), the level-0 code `RS[E, D_{μ−6,R}, 2^(μ−6)]` at a threshold `A` in
the unique-decoding range (`2^(μ−6+R) + 2^(μ−6) ≤ 2 A`, e.g. `udThr (μ−6) R`), the opening's
level-0 fold challenges `α ∈ E^6` and the final residual `f` (lvm's `C_rec` has one level, so its
residual is the fold of the root's word).

* `laneRows μ R W`: the root's lanes as rows indexed by six lane bits (`u ↦ laneWord (⟨u⟩)`), the
  word the opening folds (`rowsOf 6 (laneO 0 …)`, `rowsOf_laneO_zero`); `encRows μ R q`: the same
  for the encoding of a stack `q`.
* `CommitDoomUd μ R A Good W`: **the commitment's doom**: no candidate of `W` (a `K`-valued stack
  whose encoding agrees with `W` on `A` columns) satisfies `Good` (WP-14's relation on the decoded
  stack). Its negation is the existence of a good candidate.
* `FinalDoomUd μ R A h64 W α f`: **the final residual's doom**: the encoding of `f` is not in the
  list of the folded word `foldAll α (laneRows μ R W)` (it agrees with it on fewer than `A`
  columns). The WHIR specification's doom at the boundary after the residual, `ResC`, contains
  `FinViol` of the residual, whose negation gives `¬ FinalDoomUd` (`not_finalDoomUd`).
* `foldMsg α q`: the fold `Σ_u eq(α, u) · block_u(q)` of a stack's blocks.
* **`ud_extract`**: `¬ CommitDoomUd ∧ ¬ FinalDoomUd` ⇒ there is exactly one candidate `q`, it is
  good, `f = foldMsg α q`, `A ≤ |agreeSet (laneRows W) (encRows q)|`, and if `α` is not lucky for
  `(laneRows W, encRows q)` then `agreeSet (foldAll α (laneRows W)) (Enc f) =
  agreeSet (laneRows W) (encRows q)`: the set `E` computes from the log and `f` is the joint
  agreement set, on which every one of the 64 rows of `W` is the candidate's encoding
  (BLUEPRINT §6.2 step 5). No "not fold-bad" hypothesis is needed: with a list of at most one
  member, the folded list is the fold of the list (`foldAll_mem_iList`).
* `FoldAllLuck α O U` and `foldAllLuck_cons`: the luck event over `α ∈ E^m` splits into a first
  round's luck (`card_foldLuck_le`: at most `n` challenges) or the rest's: the per-round luck
  predicate of the certificate (`N₀/|E| = 2^-177` per round at P20, `N₀ = 2^15` columns, A13).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset

section

/-! ## Folding a list member -/

/-- **The fold of a list member is in the list of the fold**, for `m` challenges. -/
theorem foldAll_mem_iList {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    [DecidableEq ι] (C : Submodule F (ι → F)) {A : ℕ} :
    ∀ {m : ℕ} (α : Fin m → F) {O U : (Fin m → Bool) → ι → F}, U ∈ iList C A O →
      foldAll α U ∈ iList C A (foldAll α O)
  | 0, _, _, _, h => h
  | m + 1, α, O, U, h => by
    have h1 : splitLow U ∈ iList C A (splitLow O) := by
      rw [iList_splitLow]; exact Finset.mem_image_of_mem _ h
    rw [foldAll_succ α O, foldAll_succ α U]
    exact foldAll_mem_iList C (Fin.tail α) (fold_mem_iList C h1 (α 0))

/-- **The fold of row-wise encodings is the encoding of the folded messages** (`enc` linear). -/
theorem foldAll_enc {m κ R : ℕ} (α : Fin m → E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    foldAll α (fun u ↦ enc κ R (g u)) = fun _ ↦ enc κ R (∑ u, eqW α u • g u) := by
  funext v x
  rw [foldAll_eq_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- **The opening's fold rounds are WP-6's `foldAll`**: folding an integer-indexed lane oracle by
the challenges `l` (first challenge, low bit) is `foldAll` of its rows by `l`. -/
theorem rowsOf_foldsN_eq_foldAll {ι : Type*} :
    ∀ (m : ℕ) (l : List E), l.length = m → ∀ (O : ℕ → ι → E),
      rowsOf 0 (foldsN l O) = foldAll (fun i : Fin m ↦ l.getD i 0) (rowsOf m O)
  | 0, l, hl, O => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    rfl
  | m + 1, l, hl, O => by
    obtain ⟨s, l', rfl⟩ : ∃ s l', l = s :: l' := by
      cases l with
      | nil => simp at hl
      | cons s l' => exact ⟨s, l', rfl⟩
    have hl' : l'.length = m := by simpa using hl
    have h1 : foldsN (s :: l') O = foldsN l' (foldN s O) := rfl
    rw [h1, rowsOf_foldsN_eq_foldAll m l' hl' (foldN s O), rowsOf_foldN, foldAll_succ]
    rfl

/-! ## The level-0 rows -/

/-- The root's lanes as rows indexed by six lane bits. -/
def laneRows (μ R : ℕ) (W : Word) : (Fin laneBits → Bool) → Fin (2 ^ (μ - laneBits + R)) → E :=
  fun u ↦ laneWord μ R W (bitsEquiv laneBits u)

/-- A stack's lane-wise encoding as rows indexed by six lane bits. -/
noncomputable def encRows (μ R : ℕ) (q : Column μ) :
    (Fin laneBits → Bool) → Fin (2 ^ (μ - laneBits + R)) → E :=
  fun u ↦ enc (μ - laneBits) R (blockOf q (bitsEquiv laneBits u))

/-- The fold of a stack's blocks by `α ∈ E^6`: `Σ_u eq(α, u) · block_u(q)`. -/
noncomputable def foldMsg {μ : ℕ} (α : Fin laneBits → E) (q : Column μ) :
    (Fin (μ - laneBits) → Bool) → E :=
  ∑ u, eqW α u • blockOf q (bitsEquiv laneBits u)

/-! ## The doom predicates -/

/-- **The commitment's doom** (unique decoding): no candidate of the committed word satisfies
`Good`. -/
def CommitDoomUd (μ R A : ℕ) (Good : Column μ → Prop) (W : Word) : Prop :=
  ∀ q ∈ Candidates μ R A W, ¬ Good q

/-- **The final residual's doom**: the encoding of `f` is not in the list of the root's word folded
by `α`. -/
def FinalDoomUd (μ R A : ℕ) (h64 : μ - laneBits + R ≤ 64) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E) : Prop :=
  (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R f) ∉
    iList (rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))) A
      (foldAll α (laneRows μ R W))

/-- Luck over `α ∈ E^m`: a column on which `O` and `U` differ agrees after the fold. -/
def FoldAllLuck {ι : Type*} [Fintype ι] {m : ℕ} (α : Fin m → E)
    (O U : (Fin m → Bool) → ι → E) : Prop :=
  ¬ agreeSet (foldAll α O) (foldAll α U) ⊆ agreeSet O U

/-- **The luck event splits by rounds**: lucky for `cons s α` is lucky at the first round or for
`α` after it. -/
theorem foldAllLuck_cons {ι : Type*} [Fintype ι] {m : ℕ} (s : E) (α : Fin m → E)
    (O U : (Fin (m + 1) → Bool) → ι → E)
    (h : FoldAllLuck (Fin.cons s α : Fin (m + 1) → E) O U) :
    ¬ agreeSet (fold s (splitLow O)) (fold s (splitLow U)) ⊆
        agreeSet (splitLow O) (splitLow U) ∨
      FoldAllLuck α (fold s (splitLow O)) (fold s (splitLow U)) := by
  simp only [FoldAllLuck] at h ⊢
  by_contra hgood
  push Not at hgood
  apply h
  rw [foldAll_cons, foldAll_cons, ← agreeSet_splitLow]
  exact hgood.2.trans hgood.1

/-! ## The extractor's facts -/

/-- The encoding rows are the candidates' encoding `encStack`, reindexed by the lane bits. -/
theorem encRows_eq {μ R : ℕ} (q : Column μ) :
    encRows μ R q = fun u ↦ encStack μ R q (bitsEquiv laneBits u) := rfl

/-- The fold of the encoding rows is the encoding of the folded blocks. -/
theorem foldAll_encRows {μ R : ℕ} (α : Fin laneBits → E) (q : Column μ) :
    foldAll α (encRows μ R q) = fun _ ↦ enc (μ - laneBits) R (foldMsg α q) :=
  foldAll_enc α _

/-- **The extractor's facts** (BLUEPRINT §6.2, "Correctness"): not doomed at the commitment and
not doomed at the final residual, the committed word has exactly one candidate `q`; it is good;
its blocks fold to the residual; it agrees with the word on at least `A` columns; and off the
luck event the agreement set of the folded word with the residual's encoding is the word's
agreement set with the candidate's encoding. -/
theorem ud_extract {μ R A : ℕ} (hμ : laneBits ≤ μ) (h64 : μ - laneBits + R ≤ 64)
    (hud : 2 ^ (μ - laneBits + R) + 2 ^ (μ - laneBits) ≤ 2 * A)
    (Good : Column μ → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E)
    (hC : ¬ CommitDoomUd μ R A Good W) (hF : ¬ FinalDoomUd μ R A h64 W α f) :
    ∃ q ∈ Candidates μ R A W, Good q ∧ (∀ q' ∈ Candidates μ R A W, q' = q) ∧
      f = foldMsg α q ∧ A ≤ (agreeSet (laneRows μ R W) (encRows μ R q)).card ∧
      (¬ FoldAllLuck α (laneRows μ R W) (encRows μ R q) →
        agreeSet (foldAll α (laneRows μ R W)) (fun _ ↦ enc (μ - laneBits) R f) =
          agreeSet (laneRows μ R W) (encRows μ R q)) := by
  classical
  set C := rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
  have hn : Fintype.card (Fin (2 ^ (μ - laneBits + R))) + 2 ^ (μ - laneBits) ≤ 2 * A := by
    rwa [Fintype.card_fin]
  -- the good candidate
  simp only [CommitDoomUd, not_forall, not_not, exists_prop] at hC
  obtain ⟨q, hq, hgood⟩ := hC
  have hmem64 : encStack μ R q ∈ iList C A (laneWord μ R W) := mem_iList_of_candidate h64 hq
  have hmem : encRows μ R q ∈ iList C A (laneRows μ R W) := by
    rw [encRows_eq]; exact comp_mem_iList C (bitsEquiv laneBits) hmem64
  -- uniqueness
  have huniq : ∀ q' ∈ Candidates μ R A W, q' = q := fun q' hq' ↦
    encStack_injective hμ h64 (Finset.card_le_one.mp (card_iList_le_one _ hn _) _
      (mem_iList_of_candidate h64 hq') _ hmem64)
  -- the residual's encoding is the fold of the candidate's
  have hF' : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R f) ∈
      iList C A (foldAll α (laneRows μ R W)) := not_not.mp hF
  have hfold : foldAll α (encRows μ R q) ∈ iList C A (foldAll α (laneRows μ R W)) :=
    foldAll_mem_iList C α hmem
  have heq : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R f) = foldAll α (encRows μ R q) :=
    Finset.card_le_one.mp (card_iList_le_one _ hn _) _ hF' _ hfold
  have hf : f = foldMsg α q := by
    rw [foldAll_encRows] at heq
    exact enc_injective h64 (congrFun heq (Fin.elim0 : Fin 0 → Bool))
  refine ⟨q, hq, hgood, huniq, hf, ?_, fun hluck ↦ ?_⟩
  · exact (isClose_iff_le_card_agreeSet A _ _).mp ((mem_iList _ _ _ _).mp hmem).2
  · rw [heq]
    exact agreeSet_foldAll_eq (not_not.mp hluck)

/-- **The level-0 extractor's facts for `C_rec` at P20** (`μ = 19`, `R = 2`, threshold `udThr 13 2`;
`2^15` columns, `2^13`-scalar level-0 fold). With S4's second level the fold `f` is not sent; it is
the level-1 word's decoded message (`LvmWhirDoom2.ud_extract_rec20`), and `¬ FinalDoomUd` holds for
it (`not_finalDoomUd_foldMsg`). -/
theorem ud_extract_rec20_l0 (Good : Column 19 → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (19 - laneBits) → Bool) → E)
    (hC : ¬ CommitDoomUd 19 2 (udThr 13 2) Good W)
    (hF : ¬ FinalDoomUd 19 2 (udThr 13 2) (by norm_num) W α f) :
    ∃ q ∈ Candidates 19 2 (udThr 13 2) W, Good q ∧
      (∀ q' ∈ Candidates 19 2 (udThr 13 2) W, q' = q) ∧ f = foldMsg α q ∧
      udThr 13 2 ≤ (agreeSet (laneRows 19 2 W) (encRows 19 2 q)).card ∧
      (¬ FoldAllLuck α (laneRows 19 2 W) (encRows 19 2 q) →
        agreeSet (foldAll α (laneRows 19 2 W)) (fun _ ↦ enc (19 - laneBits) 2 f) =
          agreeSet (laneRows 19 2 W) (encRows 19 2 q)) :=
  ud_extract (by norm_num) (by norm_num) (by norm_num [udThr]) Good W α f hC hF

/-- **The level-0 extractor's facts for `C_rec` at P8** (`μ = 17`, `R = 2`, threshold `udThr 11 2`). -/
theorem ud_extract_rec8_l0 (Good : Column 17 → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (17 - laneBits) → Bool) → E)
    (hC : ¬ CommitDoomUd 17 2 (udThr 11 2) Good W)
    (hF : ¬ FinalDoomUd 17 2 (udThr 11 2) (by norm_num) W α f) :
    ∃ q ∈ Candidates 17 2 (udThr 11 2) W, Good q ∧
      (∀ q' ∈ Candidates 17 2 (udThr 11 2) W, q' = q) ∧ f = foldMsg α q ∧
      udThr 11 2 ≤ (agreeSet (laneRows 17 2 W) (encRows 17 2 q)).card ∧
      (¬ FoldAllLuck α (laneRows 17 2 W) (encRows 17 2 q) →
        agreeSet (foldAll α (laneRows 17 2 W)) (fun _ ↦ enc (17 - laneBits) 2 f) =
          agreeSet (laneRows 17 2 W) (encRows 17 2 q)) :=
  ud_extract (by norm_num) (by norm_num) (by norm_num [udThr]) Good W α f hC hF

/-- The all-zero committed word: `2^6` zero words in every leaf. -/
def zeroWord : Word := fun _ ↦ List.replicate (2 ^ laneBits) 0

/-- The zero stack. -/
def zeroCol (μ : ℕ) : Column μ := ⟨Vector.replicate _ 0⟩

/-- The zero stack's blocks are zero, for a variable height: at `μ = 19` the kernel would
evaluate the `2^19`-word `Vector.replicate` (78 s, 10 GB). -/
private theorem blockOf_zeroCol (μ : ℕ) (u : Fin (2 ^ laneBits)) : blockOf (zeroCol μ) u = 0 := by
  funext x
  simp only [blockOf, zeroCol, Vector.getD, Vector.toArray_replicate, Array.getD_eq_getD_getElem?,
    Array.getElem?_replicate]
  split_ifs <;> simp

/-- **Non-vacuity of `ud_extract_rec20_l0`**: the all-zero root word, with the zero stack as the good
candidate and the zero residual, satisfies both hypotheses (the honest instance), for every `α`. -/
theorem ud_extract_rec20_l0_nonvacuous (α : Fin laneBits → E) :
    ¬ CommitDoomUd 19 2 (udThr 13 2) (fun q ↦ q = zeroCol 19) zeroWord ∧
      ¬ FinalDoomUd 19 2 (udThr 13 2) (by norm_num) zeroWord α 0 := by
  have hA : udThr 13 2 ≤ (univ : Finset (Fin (2 ^ (19 - laneBits + 2)))).card := by
    simp only [card_univ, Fintype.card_fin, udThr, laneBits]; norm_num
  have hlane : ∀ u v, laneOf zeroWord u v = 0 := fun u v ↦ by
    simp [laneOf, zeroWord, List.getD_eq_getElem?_getD]
  have hblock : ∀ u, blockOf (zeroCol 19) u = 0 := blockOf_zeroCol 19
  refine ⟨fun hD ↦ hD (zeroCol 19) ⟨univ, hA, fun v _ u ↦ ?_⟩ rfl, fun hF ↦ hF ?_⟩
  · rw [hlane, hblock, map_zero]; rfl
  · have hrows : laneRows 19 2 zeroWord = 0 := by
      funext u v; simp [laneRows, laneWord, hlane]
    rw [mem_iList]
    refine ⟨fun _ ↦ by rw [map_zero]; exact Submodule.zero_mem _, univ, hA, fun _ x _ ↦ ?_⟩
    rw [foldAll_eq_sum, hrows, map_zero]
    simp

/-! ## From the WHIR specification's doom -/

/-- **The final residual's doom from the specification's.** On the level-0 code of a UD level
(`LevelCode.ud (μ − 6) R`), if the residual `G` does not satisfy `FinViol` against the word folded
by the level's challenges `r.2` (six of them), it satisfies the running claim and is not
final-doomed: `Enc(G)` is in the list of `foldAll α (laneRows W)`, `α = r.2`, `W` the root's word
in the view. -/
theorem not_finalDoomUd {μ R : ℕ} (h64 : μ - laneBits + R ≤ 64) (hκ : 1 ≤ μ - laneBits)
    (hR : 1 ≤ R) (r : WhirStateT × List E) (hlf : r.2.length = laneBits)
    (cs : List (ℕ × ℕ × Word)) (Φ : List E → E) (σ : E)
    (G : (Fin (μ - laneBits) → Bool) → E)
    (h : ¬ FinViol (LevelCode.ud (μ - laneBits) R h64 hκ hR)
      (foldedW 0 (LevelCode.ud (μ - laneBits) R h64 hκ hR) r cs) Φ σ G) :
    ∑ x, Φ (bitsL x) * G x = σ ∧
      ¬ FinalDoomUd μ R (udThr (μ - laneBits) R) h64 (wordOf cs 0)
        (fun i ↦ r.2.getD i 0) G := by
  simp only [FinViol, not_or, not_not] at h
  refine ⟨h.1, fun hD ↦ hD ?_⟩
  obtain ⟨-, hmem⟩ := h
  rw [show (fun _ : Fin 0 → Bool ↦ foldedW 0 (LevelCode.ud (μ - laneBits) R h64 hκ hR) r cs) =
      rowsOf 0 (foldsN r.2 (laneO 0 cs (LevelCode.ud (μ - laneBits) R h64 hκ hR).n)) from
      (rowsOf_zero (foldsN r.2 (laneO 0 cs (LevelCode.ud (μ - laneBits) R h64 hκ hR).n))).symm,
    rowsOf_foldsN_eq_foldAll laneBits r.2 hlf] at hmem
  change (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R G) ∈
    iList (rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))) (udThr (μ - laneBits) R)
      (foldAll (fun i : Fin laneBits ↦ r.2.getD i 0)
        (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))))) at hmem
  rwa [rowsOf_laneO_zero μ R cs] at hmem

/-- `ResC`'s bookkeeping and the negation of `ResC` give the negation of `FinViol`. -/
theorem not_finViol_of_not_resC {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P : LevelCode} {ℓ pre : ℕ}
    {r : WhirStateT × List E} {res : List E} {cs : List (ℕ × ℕ × Word)}
    (hbook : res.length = 2 ^ (μ - r.1.folds.length) ∧ FinBook μ i P ℓ pre r cs)
    (h : ¬ ResC μ ℓ₀ w i P ℓ pre r res cs) :
    ¬ FinViol P (foldedW i P r cs) (runW w ℓ₀ r.1) r.1.target (resMsg res) :=
  fun hv ↦ h ⟨hbook, hv⟩

/-- **The commitment's doom from the stacked opening's**: not in `StackedPreUd` while the
bookkeeping holds, some candidate of the root satisfies every claim. -/
theorem exists_candidate_of_not_stackedPreUd {cfg : UdConfig} {P₀ : LevelCode}
    {claims : List StackClaim} {cs : List (ℕ × ℕ × Word)} (hc : cfg.c₀ < cfg.n₀)
    (hlen : cs.length = cfg.n₀)
    (hW : ∃ W, cs[cfg.c₀]? = some (P₀.κ + P₀.R, 2 ^ laneBits, W) ∧ WellShaped (2 ^ laneBits) W)
    (h : ¬ StackedPreUd cfg P₀ claims cs) :
    ¬ CommitDoomUd cfg.μ P₀.R P₀.thr (fun q ↦ ∀ c ∈ claims, StackClaim.Holds cfg.μ c q)
      (wordOf cs cfg.c₀) := by
  intro hD
  refine h ⟨hc, hlen, hW, fun q hq ↦ ?_⟩
  have := hD q hq
  simp only [not_forall, exists_prop] at this
  exact this

end
end LeanVM.Protocol.Whir.Sound
