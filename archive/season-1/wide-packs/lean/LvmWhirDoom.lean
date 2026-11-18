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

-- (GOLF2: 21 declarations that `certified` does not use moved verbatim to `LvmXDec1UdOff`, outside its import closure.)

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

section Reindex

variable [Fintype F] [Fintype ι] {ρ ρ' : Type*} [Fintype ρ] [Fintype ρ']

/-- Reindexing the rows keeps list membership. -/
theorem comp_mem_iList (C : Submodule F (ι → F)) {A : ℕ} {O U : ρ → ι → F} (f : ρ' → ρ)
    (hU : U ∈ iList C A O) : (fun r ↦ U (f r)) ∈ iList C A (fun r ↦ O (f r)) := by
  rw [mem_iList] at hU ⊢
  obtain ⟨hcw, S, hS, hag⟩ := hU
  exact ⟨fun r ↦ hcw (f r), S, hS, fun r x hx ↦ hag (f r) x hx⟩

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

omit [Fintype F] [DecidableEq ι] in
/-- Folding never shrinks the agreement set. -/
theorem agreeSet_subset_foldAll : ∀ {m : ℕ} (α : Fin m → F) (O U : (Fin m → Bool) → ι → F),
    agreeSet O U ⊆ agreeSet (foldAll α O) (foldAll α U)
  | 0, _, _, _ => subset_rfl
  | m + 1, α, O, U => by
    rw [foldAll_succ, foldAll_succ, ← agreeSet_splitLow]
    exact (agreeSet_subset_agreeSet_fold _ _ _).trans (agreeSet_subset_foldAll _ _ _)

omit [Fintype F] [DecidableEq ι] in
/-- Off the luck event the agreement set of the fold is that of the word. -/
theorem agreeSet_foldAll_eq {m : ℕ} {α : Fin m → F} {O U : (Fin m → Bool) → ι → F}
    (h : agreeSet (foldAll α O) (foldAll α U) ⊆ agreeSet O U) :
    agreeSet (foldAll α O) (foldAll α U) = agreeSet O U :=
  Finset.Subset.antisymm h (agreeSet_subset_foldAll α O U)

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

/-! ## From the WHIR specification's doom -/

/-- `ResC`'s bookkeeping and the negation of `ResC` give the negation of `FinViol`. -/
theorem not_finViol_of_not_resC {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P : LevelCode} {ℓ pre : ℕ}
    {r : WhirStateT × List E} {res : List E} {cs : List (ℕ × ℕ × Word)}
    (hbook : res.length = 2 ^ (μ - r.1.folds.length) ∧ FinBook μ i P ℓ pre r cs)
    (h : ¬ ResC μ ℓ₀ w i P ℓ pre r res cs) :
    ¬ FinViol P (foldedW i P r cs) (runW w ℓ₀ r.1) r.1.target (resMsg res) :=
  fun hv ↦ h ⟨hbook, hv⟩

end
end LeanVM.Protocol.Whir.Sound
