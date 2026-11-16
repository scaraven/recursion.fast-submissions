/- `LvmXDec1UdOff` (GOLF2 off-path move, group 16 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmWhirDoom, LvmWhirDoom2, LvmXDec1Ud,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmWhirDoom
import LvmWhirDoom2
import LvmXDec1Ud
import LvmMlListLemmas

-- ===== from `LvmWhirDoom` =====

section
section
namespace LeanVM.Protocol.Whir.Ud
open Finset
variable {F : Type*} [Field F] {ι M : Type*}

theorem splitLow_joinLow {m : ℕ} (Q : Bool × (Fin m → Bool) → ι → M) :
    splitLow (joinLow Q) = Q := by
  funext r
  simp [splitLow, joinLow]

theorem joinLow_splitLow {m : ℕ} (Q : (Fin (m + 1) → Bool) → ι → M) :
    joinLow (splitLow Q) = Q := by
  funext u
  simp [splitLow, joinLow, Fin.cons_self_tail]

end LeanVM.Protocol.Whir.Ud
end
end

section
section
namespace LeanVM.Protocol.Whir.Ud
open Finset
variable {F : Type*} [Field F] {ι M : Type*}
section Reindex
variable [Fintype F] [Fintype ι] {ρ ρ' : Type*} [Fintype ρ] [Fintype ρ']

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

end Reindex
end LeanVM.Protocol.Whir.Ud
end
end

section
section
namespace LeanVM.Protocol.Whir.Ud
open Finset
variable {F : Type*} [Field F] {ι M : Type*}
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

end Counts
end LeanVM.Protocol.Whir.Ud
end
end

section
section
namespace LeanVM.Protocol.Whir.Ud
open Finset
variable {F : Type*} [Field F] {ι M : Type*}
section Counts
variable [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

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

end Counts
end LeanVM.Protocol.Whir.Ud
end
end

section
section
namespace LeanVM.Protocol.Whir.Ud
open Finset
variable {F : Type*} [Field F] {ι M : Type*}
section Counts
variable [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

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
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset
section

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

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset
section

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

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset
section

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

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset
section

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
end

-- ===== from `LvmWhirDoom2` =====

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset
section

/-- A candidate's level-0 fold is in the list of the folded root word. -/
theorem foldMsg_mem {μ R A : ℕ} (h64 : μ - laneBits + R ≤ 64) {W : Word} {q : Column μ}
    (hq : q ∈ Candidates μ R A W) (α : Fin laneBits → E) :
    (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R (foldMsg α q)) ∈
      iList (rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))) A
        (foldAll α (laneRows μ R W)) := by
  have hmem64 := mem_iList_of_candidate h64 hq
  have hmem : encRows μ R q ∈ iList (rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))) A
      (laneRows μ R W) := by
    rw [encRows_eq]; exact comp_mem_iList _ (bitsEquiv laneBits) hmem64
  rw [← foldAll_encRows]
  exact foldAll_mem_iList _ α hmem

/-- **The level-0 fold of a candidate is never final-doomed** (v1's level-0 decoder facts then
apply with `f := foldMsg α q`). -/
theorem not_finalDoomUd_foldMsg {μ R A : ℕ} (h64 : μ - laneBits + R ≤ 64) {W : Word}
    {q : Column μ} (hq : q ∈ Candidates μ R A W) (α : Fin laneBits → E) :
    ¬ FinalDoomUd μ R A h64 W α (foldMsg α q) :=
  fun hD ↦ hD (foldMsg_mem h64 hq α)

/-- **The extractor's facts at two levels** (BLUEPRINT2 §3.2, S4): not doomed at the root's
commitment, at the level-1 commitment and at the final residual, the root has exactly one
candidate `q`, it is good; the level-1 list has exactly one member `V`; `V`'s level-0 message is
the fold of `q`; the residual is the fold of `V`'s messages; both levels' agreement sets are at
least their thresholds, and off each level's luck event the extractor's agreement set (the folded
word against the encoding of the next message) is the joint one. -/
theorem ud_extract2 {μ R A ℓ₁ : ℕ} (hμ : laneBits ≤ μ) (h64 : μ - laneBits + R ≤ 64)
    (hud : 2 ^ (μ - laneBits + R) + 2 ^ (μ - laneBits) ≤ 2 * A)
    (P₁ : LevelCode) (hκ : μ - laneBits = ℓ₁ + P₁.κ) (hL : P₁.listMax ≤ 1)
    (Good : Column μ → Prop) (W₀ : Word) (α₀ : Fin laneBits → E)
    (Q' : (Fin ℓ₁ → Bool) → Fin P₁.n → E) (α₁ : Fin ℓ₁ → E) (f₂ : (Fin P₁.κ → Bool) → E)
    (hC : ¬ CommitDoomUd μ R A Good W₀)
    (hM : ¬ MidDoomUd A P₁ hκ (foldAll α₀ (laneRows μ R W₀) Fin.elim0) Q')
    (hF : ¬ FinalDoomL P₁ Q' α₁ f₂) :
    ∃ q ∈ Candidates μ R A W₀, Good q ∧ (∀ q' ∈ Candidates μ R A W₀, q' = q) ∧
      ∃ V ∈ iList P₁.code P₁.thr Q', (∀ V' ∈ iList P₁.code P₁.thr Q', V' = V) ∧
        joinMsg hκ (decode P₁ V) = foldMsg α₀ q ∧
        f₂ = ∑ u, eqW α₁ u • decode P₁ V u ∧
        P₁.thr ≤ (agreeSet Q' V).card ∧
        (¬ FoldAllLuck α₁ Q' V →
          agreeSet (foldAll α₁ Q') (fun _ ↦ enc P₁.κ P₁.R f₂) = agreeSet Q' V) ∧
        A ≤ (agreeSet (laneRows μ R W₀) (encRows μ R q)).card ∧
        (¬ FoldAllLuck α₀ (laneRows μ R W₀) (encRows μ R q) →
          agreeSet (foldAll α₀ (laneRows μ R W₀))
              (fun _ ↦ enc (μ - laneBits) R (foldMsg α₀ q)) =
            agreeSet (laneRows μ R W₀) (encRows μ R q)) := by
  classical
  set C₀ := rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
  have hn : Fintype.card (Fin (2 ^ (μ - laneBits + R))) + 2 ^ (μ - laneBits) ≤ 2 * A := by
    rwa [Fintype.card_fin]
  -- level 0: the good candidate, unique (`ud_extract`'s argument)
  simp only [CommitDoomUd, not_forall, not_not, exists_prop] at hC
  obtain ⟨q, hq, hgood⟩ := hC
  have hmem64 : encStack μ R q ∈ iList C₀ A (laneWord μ R W₀) := mem_iList_of_candidate h64 hq
  have hmem : encRows μ R q ∈ iList C₀ A (laneRows μ R W₀) := by
    rw [encRows_eq]; exact comp_mem_iList C₀ (bitsEquiv laneBits) hmem64
  have huniq : ∀ q' ∈ Candidates μ R A W₀, q' = q := fun q' hq' ↦
    encStack_injective hμ h64 (Finset.card_le_one.mp (card_iList_le_one _ hn _) _
      (mem_iList_of_candidate h64 hq') _ hmem64)
  have hfold0 := foldMsg_mem h64 hq α₀
  -- level 1: the member close to the folded root word
  simp only [MidDoomUd, not_forall, not_lt, exists_prop] at hM
  obtain ⟨V, hV, hclose⟩ := hM
  have hone : (iList P₁.code P₁.thr Q').card ≤ 1 := (P₁.card_iList_le Q').trans hL
  have hVuniq : ∀ V' ∈ iList P₁.code P₁.thr Q', V' = V := fun V' hV' ↦
    Finset.card_le_one.mp hone _ hV' _ hV
  -- its level-0 encoding is in the folded root word's list, hence the fold of `q`
  have hrow : (fun _ : Fin 0 → Bool ↦ foldAll α₀ (laneRows μ R W₀) Fin.elim0) =
      foldAll α₀ (laneRows μ R W₀) := by
    funext v; rw [Subsingleton.elim v Fin.elim0]
  have hmemV : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R (joinMsg hκ (decode P₁ V))) ∈
      iList C₀ A (foldAll α₀ (laneRows μ R W₀)) := by
    rw [← hrow, mem_iList]
    refine ⟨fun _ ↦ ?_, _, hclose, fun _ x hx ↦ ((Finset.mem_filter.mp hx).2).symm⟩
    show _ ∈ rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
    rw [← range_enc h64]; exact LinearMap.mem_range_self _ _
  have hjoin : joinMsg hκ (decode P₁ V) = foldMsg α₀ q :=
    enc_injective h64 (congrFun (Finset.card_le_one.mp (card_iList_le_one _ hn _) _ hmemV _ hfold0)
      (Fin.elim0 : Fin 0 → Bool))
  -- the residual is the fold of `V`
  have hVcw : IsInterleavedCodeword P₁.code V := ((mem_iList _ _ _ _).mp hV).1
  have hVenc : V = fun u ↦ enc P₁.κ P₁.R (decode P₁ V u) := funext fun u ↦ (enc_decode P₁ hVcw u).symm
  have hfoldV : foldAll α₁ V ∈ iList P₁.code P₁.thr (foldAll α₁ Q') := foldAll_mem_iList _ α₁ hV
  have hF' : (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R f₂) ∈ iList P₁.code P₁.thr (foldAll α₁ Q') :=
    not_not.mp hF
  have hone' : (iList P₁.code P₁.thr (foldAll α₁ Q')).card ≤ 1 :=
    (P₁.card_iList_le _).trans hL
  have heq1 : (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R f₂) = foldAll α₁ V :=
    Finset.card_le_one.mp hone' _ hF' _ hfoldV
  have hf₂ : f₂ = ∑ u, eqW α₁ u • decode P₁ V u := by
    have h2 : foldAll α₁ V = fun _ ↦ enc P₁.κ P₁.R (∑ u, eqW α₁ u • decode P₁ V u) := by
      conv_lhs => rw [hVenc]
      exact foldAll_enc α₁ _
    rw [h2] at heq1
    exact enc_injective P₁.h64 (congrFun heq1 (Fin.elim0 : Fin 0 → Bool))
  refine ⟨q, hq, hgood, huniq, V, hV, hVuniq, hjoin, hf₂, ?_, fun hluck ↦ ?_, ?_, fun hluck ↦ ?_⟩
  · exact (isClose_iff_le_card_agreeSet _ _ _).mp ((mem_iList _ _ _ _).mp hV).2
  · rw [heq1]
    exact agreeSet_foldAll_eq (not_not.mp hluck)
  · exact (isClose_iff_le_card_agreeSet A _ _).mp ((mem_iList _ _ _ _).mp hmem).2
  · rw [← foldAll_encRows]
    exact agreeSet_foldAll_eq (not_not.mp hluck)

/-- **The extractor's facts for `C_rec` at P20** (S4: levels `(6, 2)`, `(4, 3)`; thresholds
`udThr 13 2`, `udThr 9 3`; `2^15` and `2^12` columns; a `2^9`-scalar residual). -/
theorem ud_extract_rec20 (Good : Column 19 → Prop) (W₀ : Word) (α₀ : Fin laneBits → E)
    (Q' : (Fin 4 → Bool) → Fin (codesRec20 1).n → E) (α₁ : Fin 4 → E)
    (f₂ : (Fin (codesRec20 1).κ → Bool) → E)
    (hC : ¬ CommitDoomUd 19 2 (udThr 13 2) Good W₀)
    (hM : ¬ MidDoomUd (udThr 13 2) (codesRec20 1) (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ)
      (foldAll α₀ (laneRows 19 2 W₀) Fin.elim0) Q')
    (hF : ¬ FinalDoomL (codesRec20 1) Q' α₁ f₂) :
    ∃ q ∈ Candidates 19 2 (udThr 13 2) W₀, Good q ∧
      (∀ q' ∈ Candidates 19 2 (udThr 13 2) W₀, q' = q) ∧
      ∃ V ∈ iList (codesRec20 1).code (codesRec20 1).thr Q',
        (∀ V' ∈ iList (codesRec20 1).code (codesRec20 1).thr Q', V' = V) ∧
        joinMsg (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ) (decode (codesRec20 1) V) =
          foldMsg α₀ q ∧
        f₂ = ∑ u, eqW α₁ u • decode (codesRec20 1) V u ∧
        (codesRec20 1).thr ≤ (agreeSet Q' V).card ∧
        (¬ FoldAllLuck α₁ Q' V →
          agreeSet (foldAll α₁ Q') (fun _ ↦ enc (codesRec20 1).κ (codesRec20 1).R f₂) =
            agreeSet Q' V) ∧
        udThr 13 2 ≤ (agreeSet (laneRows 19 2 W₀) (encRows 19 2 q)).card ∧
        (¬ FoldAllLuck α₀ (laneRows 19 2 W₀) (encRows 19 2 q) →
          agreeSet (foldAll α₀ (laneRows 19 2 W₀)) (fun _ ↦ enc (19 - laneBits) 2 (foldMsg α₀ q)) =
            agreeSet (laneRows 19 2 W₀) (encRows 19 2 q)) :=
  ud_extract2 (by norm_num) (by norm_num) (by norm_num [udThr]) (codesRec20 1) rfl le_rfl Good W₀ α₀
    Q' α₁ f₂ hC hM hF

/-- **The extractor's facts for `C_rec` at P8** (S2's P8, μ = 18; S4: levels `(6, 2)`, `(4, 3)`; `κ = 12, 8`). -/
theorem ud_extract_rec18 (Good : Column 18 → Prop) (W₀ : Word) (α₀ : Fin laneBits → E)
    (Q' : (Fin 4 → Bool) → Fin (codesRec18 1).n → E) (α₁ : Fin 4 → E)
    (f₂ : (Fin (codesRec18 1).κ → Bool) → E)
    (hC : ¬ CommitDoomUd 18 2 (udThr 12 2) Good W₀)
    (hM : ¬ MidDoomUd (udThr 12 2) (codesRec18 1) (by rfl : 18 - laneBits = 4 + (codesRec18 1).κ)
      (foldAll α₀ (laneRows 18 2 W₀) Fin.elim0) Q')
    (hF : ¬ FinalDoomL (codesRec18 1) Q' α₁ f₂) :
    ∃ q ∈ Candidates 18 2 (udThr 12 2) W₀, Good q ∧
      (∀ q' ∈ Candidates 18 2 (udThr 12 2) W₀, q' = q) ∧
      ∃ V ∈ iList (codesRec18 1).code (codesRec18 1).thr Q',
        (∀ V' ∈ iList (codesRec18 1).code (codesRec18 1).thr Q', V' = V) ∧
        joinMsg (by rfl : 18 - laneBits = 4 + (codesRec18 1).κ) (decode (codesRec18 1) V) =
          foldMsg α₀ q ∧
        f₂ = ∑ u, eqW α₁ u • decode (codesRec18 1) V u ∧
        (codesRec18 1).thr ≤ (agreeSet Q' V).card ∧
        (¬ FoldAllLuck α₁ Q' V →
          agreeSet (foldAll α₁ Q') (fun _ ↦ enc (codesRec18 1).κ (codesRec18 1).R f₂) =
            agreeSet Q' V) ∧
        udThr 12 2 ≤ (agreeSet (laneRows 18 2 W₀) (encRows 18 2 q)).card ∧
        (¬ FoldAllLuck α₀ (laneRows 18 2 W₀) (encRows 18 2 q) →
          agreeSet (foldAll α₀ (laneRows 18 2 W₀)) (fun _ ↦ enc (18 - laneBits) 2 (foldMsg α₀ q)) =
            agreeSet (laneRows 18 2 W₀) (encRows 18 2 q)) :=
  ud_extract2 (by norm_num) (by norm_num) (by norm_num [udThr]) (codesRec18 1) rfl le_rfl Good W₀ α₀
    Q' α₁ f₂ hC hM hF

/-- The zero level-1 word is in its own list. -/
theorem zero_mem_iList1 {ℓ₁ : ℕ} (P₁ : LevelCode) (hthr : P₁.thr ≤ P₁.n) :
    (0 : (Fin ℓ₁ → Bool) → Fin P₁.n → E) ∈ iList P₁.code P₁.thr 0 := by
  rw [mem_iList]
  refine ⟨fun _ ↦ Submodule.zero_mem _, univ, ?_, fun _ _ _ ↦ rfl⟩
  rw [Finset.card_univ, Fintype.card_fin]
  exact hthr

/-- The zero words are not level-1 doomed. -/
theorem not_midDoomUd_zero {κ₀ R₀ ℓ₁ A : ℕ} (P₁ : LevelCode) (hκ : κ₀ = ℓ₁ + P₁.κ)
    (hthr : P₁.thr ≤ P₁.n) (hA : A ≤ 2 ^ (κ₀ + R₀)) : ¬ MidDoomUd (R₀ := R₀) A P₁ hκ 0 0 := by
  intro hD
  have h := hD 0 (zero_mem_iList1 P₁ hthr)
  have hdec : decode P₁ (0 : (Fin ℓ₁ → Bool) → Fin P₁.n → E) = 0 := by
    have := decode_enc P₁ (fun _ : Fin ℓ₁ → Bool ↦ (0 : (Fin P₁.κ → Bool) → E))
    simp only [map_zero] at this
    exact this
  have hj : joinMsg hκ (0 : (Fin ℓ₁ → Bool) → (Fin P₁.κ → Bool) → E) = 0 := rfl
  rw [hdec, hj, map_zero, Finset.filter_true_of_mem (fun _ _ ↦ rfl), Finset.card_univ,
    Fintype.card_fin] at h
  omega

/-- The zero residual of the zero words is not final-doomed. -/
theorem not_finalDoomL_zero {ℓ₁ : ℕ} (P₁ : LevelCode) (hthr : P₁.thr ≤ P₁.n) (α₁ : Fin ℓ₁ → E) :
    ¬ FinalDoomL P₁ 0 α₁ 0 := by
  intro hD
  apply hD
  have h0 : (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R 0) = foldAll α₁ (0 : (Fin ℓ₁ → Bool) → Fin P₁.n → E) := by
    funext v x
    rw [map_zero, foldAll_eq_sum]
    simp
  rw [h0]
  exact foldAll_mem_iList _ α₁ (zero_mem_iList1 P₁ hthr)

/-- **Non-vacuity of `ud_extract_rec20`**: the all-zero words (root and level 1), with the zero
stack as the good candidate and the zero residual, satisfy all three hypotheses, for every
`α₀`, `α₁` (the honest instance). -/
theorem ud_extract_rec20_nonvacuous (α₀ : Fin laneBits → E) (α₁ : Fin 4 → E) :
    ¬ CommitDoomUd 19 2 (udThr 13 2) (fun q ↦ q = zeroCol 19) zeroWord ∧
      ¬ MidDoomUd (udThr 13 2) (codesRec20 1) (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ)
        (foldAll α₀ (laneRows 19 2 zeroWord) Fin.elim0) 0 ∧
      ¬ FinalDoomL (codesRec20 1) 0 α₁ 0 := by
  obtain ⟨h1, -⟩ := ud_extract_rec20_l0_nonvacuous α₀
  have hrows : laneRows 19 2 zeroWord = 0 := by
    funext u v
    simp [laneRows, laneWord, laneOf, zeroWord, List.getD_eq_getElem?_getD]
  have hC : foldAll α₀ (laneRows 19 2 zeroWord) Fin.elim0 = 0 := by
    funext x
    rw [foldAll_eq_sum, hrows]
    simp
  have hthr : (codesRec20 1).thr ≤ (codesRec20 1).n := by
    show udThr 9 3 ≤ 2 ^ (9 + 3)
    simp only [udThr]; norm_num
  rw [hC]
  exact ⟨h1, not_midDoomUd_zero _ _ hthr (by simp only [udThr, laneBits]; norm_num),
    not_finalDoomL_zero _ hthr α₁⟩

end
end LeanVM.Protocol.Whir.Sound
end

-- ===== from `LvmXDec1Ud` =====

section
namespace Lvm.X
open Finset Lvm.Nb CompPoly.Extension BF64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd

/-- **`decodeRec1_of_ud` for a member of the level-1 list** (`ud_extract_rec20`'s `V`). -/
theorem decodeRec1_of_mem (W₁ : Compile.Word) (hW : ∀ v < 2 ^ 12, (W₁ v).length = 48)
    (α₁ : Fin 4 → E) (f₂ : (Fin (codesRec20 1).κ → Bool) → E) {A : ℕ} (hA : 2 ^ 9 ≤ A) :
    ∀ V ∈ iList (codesRec20 1).code A (rows1 4 (codesRec20 1).n W₁),
      f₂ = ∑ u, eqW α₁ u • decode (codesRec20 1) V u →
      ¬ FoldAllLuck α₁ (rows1 4 (codesRec20 1).n W₁) V →
      decodeRec1 (wdOf W₁) (alphaN1 α₁) (fN2 f₂) =
        some (fNr (joinMsg (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ)
          (decode (codesRec20 1) V))) := by
  simp only [mem_iList]
  intro V hV hf hL
  exact decodeRec1_of_ud W₁ hW α₁ f₂ V hV.1 hA hV.2 hf hL

end Lvm.X
end
