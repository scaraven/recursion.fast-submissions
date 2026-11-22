-- New for lvm2 (WP J2P-L, roll 5): the extractor's facts for J2′'s two-level `C_rec` at the Johnson radius:
-- the list version of X-REC2's `ud_extract2` (lvm2/XREC2 `LvmWhirDoom2`), fed by JB-L's `GoodRes`; luck over the
-- list per round; the cert's candidate-pair count.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: J2′ extraction)
-/
import LvmWhirParamsJp
import LvmWhirParamsJ23
import LvmWhirDoom

-- (GOLF2: 9 declarations that `certified` does not use moved verbatim to `LvmWhirDoomJ2Off`, outside its import closure.)

-- ===== merged from `LvmWhirDoomJ` (GOLF module merge: `LvmWhirDoomJ.lean` is now a stub importing `LvmWhirDoomJ2`) =====
section
-- New for lvm2 (WP JB-L, J2): the extractor's facts for a level-0 word decoded at the Johnson radius
-- (JB-DES §3 option B: decoding with advice, the decoder program unchanged), the list version of
-- `LvmWhirDoom.ud_extract`; the per-member luck union.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: the extractor's facts with a list)
-/

/-!
# Extraction with a list (`C_rec` at the Johnson radius)

`ud_extract` takes uniqueness from the unique-decoding radius (`card_iList_le_one`): the one
candidate is the good one, and the residual is its fold. At the Johnson radius the root's word has
a list of up to `L` candidates, and the residual `f` is the advice that selects one (JB-DES §3 B,
decoding with advice; the decoder program is unchanged). The doom is restricted accordingly:

* **the restricted final doom** `FinalRDoomJ`: `f` is not the fold of any good candidate. Its
  negation is exactly what the extractor needs, and it is the end state of a WHIR invariant
  relativised to the list members that are not folds of good candidates (open, see below): no
  fold-bad or collision event appears in the extractor's statement, those stay inside the WHIR
  groups' escapes.
* **luck over the list** `FoldAllLuckL`: some list member's agreement set grows under the fold.
  `card_foldLuckL_le`: per fold round at most `L·n` challenges (`card_foldLuck_le` per member),
  the luck term `L·n/|E|` of JB-DES §2.2. Off it, the selected member's pair is not lucky
  (`foldAllLuck_of_luckL`).

`j_extract`, the list version of `ud_extract`: from `¬ FinalRDoomJ`, a good candidate `q` whose
blocks fold to `f`, agreeing with the word on at least `A` columns and, off the luck of its pair,
with `agreeSet (foldAll α W) (Enc f) = agreeSet W (Enc q)`, the set `E` computes. `decodeRec_correct`
consumes exactly these (it needs `2^κ₀ ≤ A` agreeing columns: `A₀ = 23261 ≥ 2^13` for
`codeJ13R3`). `not_finalRDoomJ_of_ud`: in the unique-decoding range `ud_extract`'s hypotheses
imply `¬ FinalRDoomJ`, so the restricted doom is never stronger than v1's.

**Open (J2):** that an accepting transcript is, except with the charged escapes, not in
`FinalRDoomJ`: the WHIR invariant relativised to tracked members (JB-L report §4).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset

section

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirDoomJ` =====

/-!
# J2′: from `GoodRes` to the two-level decoder's facts

X-REC2's two-level extractor decodes level 1 first (the level-1 member `V` on the agreement set of
the level-1 rows folded by `α₁` with `Enc₁(f₂)`), then level 0 as v1 with `f₁ := joinMsg (decode V)`.
In unique decoding (`ud_extract2`) it gets `V`, `q` and their relations from uniqueness. At the Johnson
radius they come from the good branch of the relativised opening (`PostR`, JB-L):

* `GoodRes` + the final good set `gdFinal` give a good root candidate `q`, a member `V` of the level-1
  list on `q`'s path after `α₀` (`ConsAt`), and the residual `f₂` = `q`'s path after `α₀ ++ α₁`.
* `pathAt_zero_iff_foldMsg`: a level-0-folded message is on `q`'s path after `α₀` iff it is `q`'s
  level-0 fold `foldMsg α₀ q` (the multilinear extension at `α₀` on the lane variables).
* `sum_eqW_path`: folding a path by `α₁` is the path after `α₀ ++ α₁`.
* **`j_extract2`**: from those, exactly `ud_extract2`'s conclusions about `q` and `V` (the relations
  `joinMsg (decode V) = foldMsg α₀ q`, `f₂ = Σ_u eq(α₁, u)·decode V u`, the thresholds and the
  agreement-set equalities off each level's luck), without uniqueness.
* **Luck over the list**: `foldAllLuckL_cons` splits it by rounds (the folded list contains the
  folds of the list); per round `card_foldLuckL_le` (`L·n`); `luckL_rec20Jp`: J2′'s total
  `(6·304·2^15 + 4·311·2^12)/|E| ≤ 2^-165`.
* `candPairsJ_ncard_le`: the cert's candidate pairs (`C_main` J1's root at `codesMain23Jq`, `C_rec` J2′'s
  at `codesRec20Jp`) are at most `98 · 304` (`kgSpec`'s `L₀`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset

section

/-! ## Paths and folds -/

/-- **Folding a path by `α₁` is the path after `α₀ ++ α₁`.** -/
theorem sum_eqW_path {μ ℓ κ : ℕ} (q : Column μ) (fs : List E) (α₁ : Fin ℓ → E)
    (g : (Fin ℓ → Bool) → (Fin κ → Bool) → E) (hg : PathAt q fs g) (x : Fin κ → Bool) :
    (∑ u, eqW α₁ u • g u) x = qMle q (fs ++ List.ofFn α₁ ++ bitsL x) := by
  induction ℓ generalizing fs with
  | zero =>
    rw [Finset.sum_apply, Fintype.sum_unique]
    simp only [eqW, Finset.univ_eq_empty, Finset.prod_empty, one_smul, List.ofFn_zero,
      List.append_nil]
    rw [hg, bitsL_zero, List.append_nil]
  | succ m ih =>
    have hfold := ih (fs ++ [α₁ 0]) (Fin.tail α₁) (foldRows (α₁ 0) g) (pathAt_fold hg (α₁ 0))
    have hl : fs ++ List.ofFn α₁ ++ bitsL x = fs ++ [α₁ 0] ++ List.ofFn (Fin.tail α₁) ++ bitsL x := by
      simp only [List.ofFn_succ, List.append_assoc, List.cons_append]
      rfl
    rw [hl, ← hfold, Finset.sum_apply, Finset.sum_apply, sum_cube_succ]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, foldRows, eqW, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.tail, ite_true, Bool.false_eq_true, ite_false]
    ring

/-- **A level-0-folded message is on `q`'s path after `α₀` iff it is `q`'s level-0 fold.** -/
theorem pathAt_zero_iff_foldMsg {μ : ℕ} (q : Column μ) (α₀ : Fin laneBits → E)
    (g : (Fin 0 → Bool) → (Fin (μ - laneBits) → Bool) → E) :
    PathAt q (List.ofFn α₀) g ↔ g Fin.elim0 = foldMsg α₀ q := by
  have hroot : PathAt q [] (rootMsg q) := fun u x ↦ by rw [List.nil_append, qMle_bitsL]
  have hfm : ∀ x, foldMsg α₀ q x = qMle q (List.ofFn α₀ ++ bitsL x) := fun x ↦ by
    have := sum_eqW_path q [] α₀ (rootMsg q) hroot x
    rw [List.nil_append] at this
    exact this
  constructor
  · intro h
    funext x
    rw [hfm, h Fin.elim0 x, bitsL_zero, List.append_nil]
  · intro h u x
    rw [Subsingleton.elim u Fin.elim0, h, hfm, bitsL_zero, List.append_nil]

/-! ## The extractor's facts -/

/-! ## Luck over the list -/

/-! ## The cert's candidate pairs -/

/-- **The candidate pairs** of `C_main` (B1's `codeJ17R2` at ν = 23) and `C_rec` (J2′'s) are at most `124 · 304`
(`L₀ = 37,696`, B1-P3P4). -/
theorem candPairsJ_ncard_le (W₁ W₂ : Word) :
    ({p : Column 23 × Column 19 | p.1 ∈ Candidates 23 2 (codesMain23Jq 0).thr W₁ ∧
        p.2 ∈ Candidates 19 2 (codesRec20Jp 0).thr W₂}).ncard ≤ 124 * 304 := by
  change (Candidates 23 2 (codesMain23Jq 0).thr W₁ ×ˢ
    Candidates 19 2 (codesRec20Jp 0).thr W₂).ncard ≤ 124 * 304
  rw [Set.ncard_prod]
  exact Nat.mul_le_mul (candidates_main23Jq_ncard_le W₁) (candidates_rec20Jp_ncard_le W₂)

end
end LeanVM.Protocol.Whir.Sound
