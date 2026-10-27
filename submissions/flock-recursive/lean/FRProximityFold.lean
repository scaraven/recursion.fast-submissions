-- New for `flock-recursive` (BLUEPRINT §5.2 rows P1/P2, §5.3, §5.4 step 2; BP-C-M8).
import FRProximityLine
import Mathlib.Algebra.Order.Field.Basic

/-!
# Folding, F-valuedness, positions (BLUEPRINT §5.3, §5.4)

Generic over a field `K`, distinct points `x : Fin n → K`, `C = RS[K, x, k]`, `2e + k ≤ n`:

* `JointClose C e U A`: the rows `U` have codeword rows whose **joint** agreement set is exactly
  `A`, and `|A| ≥ n − e`.
* **`fold_preserves`** (P1): one fold round pairs rows `(U₀ c, U₁ c)` and outputs
  `U₀ c + z (U₁ c − U₀ c)`. If `z` is in no line's bad set (`lineBad`, bounded by
  `round_bad_cover`), the input rows are jointly close with agreement set `A` iff the output
  rows are; `fold_lift` also returns codewords that fold to the given ones. Iterating over a
  level's rounds is the consumer's induction (the row order is the transcript's).
* **`interp_F`**: a codeword over `M ⊇ L` that is `L`-valued on `k` positions is the image of a
  codeword over `L` (`interp_F_D`: in `C_K`, `F`-valued on `k` positions, it is `Enc` of an
  `F`-message).
* **`positions_bad_le`** (P2): the `t`-tuples of positions inside a set of `≤ n − e − 1`
  positions are at most a `(1 − e/n)^t` fraction of all `n^t`.
-/

namespace FR

open Polynomial Finset

section Fold

variable {K : Type*} [Field K] [DecidableEq K] {n : ℕ}

/-- The joint agreement set of a family of rows `U` with a family of words `V`. -/
def jointAgree {ι : Type*} [Fintype ι] (U V : ι → Fin n → K) : Finset (Fin n) :=
  univ.filter fun j => ∀ i, U i j = V i j

omit [Field K] in
@[simp] theorem mem_jointAgree {ι : Type*} [Fintype ι] {U V : ι → Fin n → K} {j : Fin n} :
    j ∈ jointAgree U V ↔ ∀ i, U i j = V i j := by
  simp [jointAgree]

/-- **`JointClose C e U A`**: the rows `U` agree with codeword rows exactly on `A`, `|A| ≥ n − e`
(BLUEPRINT §5.4: "`e`-close to `C^{rows}` with joint agreement `A`"). -/
def JointClose {ι : Type*} [Fintype ι] (C : Submodule K (Fin n → K)) (e : ℕ)
    (U : ι → Fin n → K) (A : Finset (Fin n)) : Prop :=
  n - e ≤ A.card ∧ ∃ V : ι → Fin n → K, (∀ i, V i ∈ C) ∧ jointAgree U V = A

/-- The rows `U₀ c` (`false`) and `U₁ c` (`true`) of one fold round as one family. -/
def pairRows {κ : Type*} (U₀ U₁ : κ → Fin n → K) : Bool × κ → Fin n → K :=
  fun p => if p.1 then U₁ p.2 else U₀ p.2

omit [Field K] [DecidableEq K] in
@[simp] theorem pairRows_false {κ : Type*} (U₀ U₁ : κ → Fin n → K) (c : κ) :
    pairRows U₀ U₁ (false, c) = U₀ c := rfl

omit [Field K] [DecidableEq K] in
@[simp] theorem pairRows_true {κ : Type*} (U₀ U₁ : κ → Fin n → K) (c : κ) :
    pairRows U₀ U₁ (true, c) = U₁ c := rfl

/-- One fold round: `U₀ c + z (U₁ c − U₀ c)`. -/
def foldRows {κ : Type*} (z : K) (U₀ U₁ : κ → Fin n → K) : κ → Fin n → K :=
  fun c => U₀ c + z • (U₁ c - U₀ c)

variable {x : Fin n → K} {k e : ℕ}

/-- A close line point has a pair of codewords whose joint agreement is its agreement set, when
`z` is not bad. -/
theorem good_line (hz : z ∉ lineBad (rsCode x k) e u₀ u₁) {w : Fin n → K}
    (hw : w ∈ rsCode x k) (hcl : n - e ≤ (agreeSet (u₀ + z • (u₁ - u₀)) w).card) :
    ∃ v₀ ∈ rsCode x k, ∃ v₁ ∈ rsCode x k,
      agreeSet₂ u₀ u₁ v₀ v₁ = agreeSet (u₀ + z • (u₁ - u₀)) w := by
  by_contra hne
  exact hz ⟨w, hw, hcl, hne⟩

theorem card_le_of_superset {A B : Finset (Fin n)} (h : A ⊆ B) (hA : n - e ≤ A.card) :
    n - e ≤ B.card := hA.trans (card_le_card h)

/-- **`fold_lift`**: under no bad `z`, codeword rows `W` jointly agreeing with the fold exactly on
`A` (`|A| ≥ n − e`) lift to codeword pairs `(V₀ c, V₁ c)` that fold to `W c` and agree with
`(U₀, U₁)` exactly on `A`. -/
theorem fold_lift (hx : Function.Injective x) (h : 2 * e + k ≤ n) {κ : Type*} [Fintype κ]
    {U₀ U₁ : κ → Fin n → K} {z : K} (hz : ∀ c, z ∉ lineBad (rsCode x k) e (U₀ c) (U₁ c))
    {A : Finset (Fin n)} (hA : n - e ≤ A.card) {W : κ → Fin n → K} (hW : ∀ c, W c ∈ rsCode x k)
    (hWA : jointAgree (foldRows z U₀ U₁) W = A) :
    ∃ V₀ V₁ : κ → Fin n → K, (∀ c, V₀ c ∈ rsCode x k) ∧ (∀ c, V₁ c ∈ rsCode x k) ∧
      (∀ c, W c = V₀ c + z • (V₁ c - V₀ c)) ∧ jointAgree (pairRows U₀ U₁) (pairRows V₀ V₁) = A := by
  have hsup : ∀ c, A ⊆ agreeSet (foldRows z U₀ U₁ c) (W c) := fun c j hj => by
    rw [← hWA, mem_jointAgree] at hj; exact mem_agreeSet.2 (hj c)
  choose V₀ hV₀ V₁ hV₁ hV using fun c => good_line (hz c) (hW c) (card_le_of_superset (hsup c) hA)
  have key : ∀ c j, (U₀ c j = V₀ c j ∧ U₁ c j = V₁ c j) ↔ foldRows z U₀ U₁ c j = W c j :=
    fun c j => mem_agreeSet₂.symm.trans (hV c ▸ mem_agreeSet)
  refine ⟨V₀, V₁, hV₀, hV₁, fun c => ?_, ?_⟩
  · -- both are codewords agreeing with the fold on `A`
    refine rs_eq_of_agree hx (hW c) (add_mem (hV₀ c) (Submodule.smul_mem _ _
      (sub_mem (hV₁ c) (hV₀ c)))) A (by omega) fun j hj => ?_
    obtain ⟨h0, h1⟩ := (key c j).2 (mem_agreeSet.1 (hsup c hj))
    rw [← mem_agreeSet.1 (hsup c hj)]; simp [foldRows, h0, h1]
  · ext j
    rw [← hWA, mem_jointAgree, mem_jointAgree]
    constructor
    · exact fun hj c => (key c j).1 ⟨hj (false, c), hj (true, c)⟩
    · rintro hj ⟨_ | _, c⟩
      exacts [((key c j).2 (hj c)).1, ((key c j).2 (hj c)).2]

/-- **`fold_preserves`** (BLUEPRINT §5.3): if `z` is in no line's bad set, the pair rows
`(U₀, U₁)` are jointly close to `C` with agreement set `A` iff the folded rows are. -/
theorem fold_preserves (hx : Function.Injective x) (h : 2 * e + k ≤ n) {κ : Type*} [Fintype κ]
    {U₀ U₁ : κ → Fin n → K} {z : K} (hz : ∀ c, z ∉ lineBad (rsCode x k) e (U₀ c) (U₁ c))
    (A : Finset (Fin n)) :
    JointClose (rsCode x k) e (pairRows U₀ U₁) A ↔
      JointClose (rsCode x k) e (foldRows z U₀ U₁) A := by
  constructor
  · rintro ⟨hA, V, hV, hVA⟩
    have hU : ∀ c, ∀ i ∈ A, U₀ c i = V (false, c) i ∧ U₁ c i = V (true, c) i := fun c i hi => by
      rw [← hVA, mem_jointAgree] at hi
      exact ⟨hi (false, c), hi (true, c)⟩
    have hF : ∀ c, foldRows z (fun c => V (false, c)) (fun c => V (true, c)) c ∈ rsCode x k :=
      fun c => add_mem (hV _) (Submodule.smul_mem _ _ (sub_mem (hV _) (hV _)))
    have hsup : ∀ c, A ⊆ agreeSet (foldRows z U₀ U₁ c)
        (foldRows z (fun c => V (false, c)) (fun c => V (true, c)) c) := fun c j hj => by
      simp [foldRows, hU c j hj]
    refine ⟨hA, _, hF, ?_⟩
    ext j
    refine ⟨fun hj => ?_, fun hj => mem_jointAgree.2 fun c => mem_agreeSet.1 (hsup c hj)⟩
    rw [← hVA, mem_jointAgree]
    rintro ⟨b, c⟩
    obtain ⟨v₀, hv₀, v₁, hv₁, hv⟩ := good_line (hz c) (hF c) (card_le_of_superset (hsup c) hA)
    have hA₂ : ∀ i ∈ A, U₀ c i = v₀ i ∧ U₁ c i = v₁ i := fun i hi =>
      mem_agreeSet₂.1 (hv ▸ hsup c hi)
    have e0 : v₀ = V (false, c) := rs_eq_of_agree hx hv₀ (hV _) A (by omega) fun i hi =>
      (hA₂ i hi).1.symm.trans (hU c i hi).1
    have e1 : v₁ = V (true, c) := rs_eq_of_agree hx hv₁ (hV _) A (by omega) fun i hi =>
      (hA₂ i hi).2.symm.trans (hU c i hi).2
    have hj' : j ∈ agreeSet₂ (U₀ c) (U₁ c) v₀ v₁ := by
      rw [hv, mem_agreeSet]; exact mem_jointAgree.1 hj c
    rw [mem_agreeSet₂, e0, e1] at hj'
    cases b
    exacts [hj'.1, hj'.2]
  · rintro ⟨hA, W, hW, hWA⟩
    obtain ⟨V₀, V₁, hV₀, hV₁, -, hV⟩ := fold_lift hx h hz hA hW hWA
    exact ⟨hA, pairRows V₀ V₁, fun ⟨b, c⟩ => by cases b <;> simp [hV₀, hV₁], hV⟩

end Fold

/-! ## F-valuedness once per level (`interp_F`) -/

section InterpF

variable {L M : Type*} [Field L] [Field M] [Algebra L M] {n : ℕ}

/-- An `L`-codeword maps to an `M`-codeword of the same code over the image points. -/
theorem rsCode_map {x : Fin n → L} {k : ℕ} {v : Fin n → L} (hv : v ∈ rsCode x k) :
    (fun j => algebraMap L M (v j)) ∈ rsCode (fun j => algebraMap L M (x j)) k := by
  obtain ⟨p, hp, rfl⟩ := mem_rsCode.1 hv
  refine mem_rsCode.2 ⟨p.map (algebraMap L M), ?_, funext fun j => ?_⟩
  · rwa [degree_map]
  · simp [evalWord, eval_map, eval₂_at_apply]

/-- **`interp_F`**: a codeword of `RS[M, x, k]` (points in `L`) that is `L`-valued on `k`
positions is the image of a codeword of `RS[L, x, k]`. -/
theorem interp_F [DecidableEq M] {x : Fin n → L} (hx : Function.Injective x) {k : ℕ}
    {v : Fin n → M} (hv : v ∈ rsCode (fun j => algebraMap L M (x j)) k) (f : Fin n → L)
    (A : Finset (Fin n)) (hA : k ≤ A.card) (hvA : ∀ j ∈ A, v j = algebraMap L M (f j)) :
    ∃ v' ∈ rsCode x k, v = fun j => algebraMap L M (v' j) := by
  obtain ⟨J, hJA, hJ⟩ := exists_subset_card_eq hA
  obtain ⟨v', hv', hv'J⟩ := rs_interp hx J hJ.le f
  refine ⟨v', hv', rs_eq_of_agree ((algebraMap L M).injective.comp hx) hv (rsCode_map hv') J
    hJ.ge fun j hj => ?_⟩
  rw [hvA j (hJA hj), hv'J j hj]

/-- `Enc` commutes with the field embedding: `Enc_M(ι ∘ c) = ι ∘ Enc_L(c)`. -/
theorem enc_algebraMap (pt : ℕ → L) (n k : ℕ) (c : Fin k → L) (j : Fin n) :
    enc (M := M) pt n k (fun x => algebraMap L M (c x)) j = algebraMap L M (enc pt n k c j) := by
  simp [enc, map_sum, map_mul]

end InterpF

/-- **`interp_F` on the protocol's code**: a word of `C_K` (on `D`, `n, k ≤ 2^64`) that is
`F`-valued on `k` positions is `Enc_K` of an `F`-message, i.e. lies in `C_F`. -/
theorem interp_F_D {n k : ℕ} (hn : n ≤ nMax) (hk : k ≤ nMax) {v : Fin n → K}
    (hv : v ∈ encCode (M := K) D n k) (f : Fin n → F) (A : Finset (Fin n)) (hA : k ≤ A.card)
    (hvA : ∀ j ∈ A, v j = algebraMap F K (f j)) :
    ∃ c : Fin k → F, v = enc (M := K) D n k (fun x => algebraMap F K (c x)) := by
  rw [encCode_D hk] at hv
  obtain ⟨v', hv', rfl⟩ := interp_F (Dpts_injective hn) hv f A hA hvA
  rw [← encCode_D (M := F) hk] at hv'
  obtain ⟨c, rfl⟩ := hv'
  exact ⟨c, funext fun j => (enc_algebraMap D n k c j).symm⟩

/-! ## Positions (row P2) -/

section Positions

variable {n : ℕ}

/-- The `t`-tuples of positions all inside `S` are `|S|^t` many. -/
theorem positions_card (S : Finset (Fin n)) (t : ℕ) :
    (univ.filter fun f : Fin t → Fin n => ∀ i, f i ∈ S).card = S.card ^ t := by
  rw [show (univ.filter fun f : Fin t → Fin n => ∀ i, f i ∈ S) = Fintype.piFinset fun _ => S by
    ext f; simp [Fintype.mem_piFinset], Fintype.card_piFinset]
  simp

/-- **`positions_bad_le`** (row P2): if the agreement set `S` has at most `n − e − 1` positions,
the fraction of the `n^t` position tuples that land only in `S` is at most `(1 − e/n)^t`. -/
theorem positions_bad_le (S : Finset (Fin n)) (t e : ℕ) (hS : S.card + e < n) :
    ((univ.filter fun f : Fin t → Fin n => ∀ i, f i ∈ S).card : ℚ) / (n : ℚ) ^ t ≤
      (1 - (e : ℚ) / n) ^ t := by
  have hn : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [positions_card, Nat.cast_pow, ← div_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ t
  rw [div_le_iff₀ hn, sub_mul, one_mul, div_mul_cancel₀ _ hn.ne']
  have : (S.card : ℚ) + e ≤ n := by exact_mod_cast hS.le
  linarith

end Positions

/-! ## Controls (BLUEPRINT §5.6) -/

section Controls

/-- The Ligerito levels `(n, k, e)` of both shapes (BLUEPRINT §2.2: `P30` then `L32`,
`e = ⌊(n − k)/2⌋`). -/
def pcsLevels : List (ℕ × ℕ × ℕ) :=
  [(2 ^ 18, 2 ^ 17), (2 ^ 16, 2 ^ 14), (2 ^ 14, 2 ^ 11), (2 ^ 12, 2 ^ 8), (2 ^ 10, 2 ^ 5),
    (2 ^ 20, 2 ^ 19), (2 ^ 18, 2 ^ 16), (2 ^ 16, 2 ^ 13), (2 ^ 14, 2 ^ 10), (2 ^ 12, 2 ^ 7)].map
    fun p => (p.1, p.2, (p.1 - p.2) / 2)

/-- **Positive control of `mca_ud_line`'s use**: at every level the hypotheses hold
(`2e + k ≤ n ≤ nMax`), `C_mca ≤ 2^60` (the stage requirement) and the P1 row with `2^6` lines,
`(2^6 C_mca + 2)/2^256`, is at most `2^-190` (BLUEPRINT §5.2). -/
theorem pcsLevels_ok : ∀ p ∈ pcsLevels, 2 * p.2.2 + p.2.1 ≤ p.1 ∧ p.1 ≤ nMax ∧
    cMca p.1 p.2.1 p.2.2 ≤ 2 ^ 60 ∧ 2 ^ 6 * cMca p.1 p.2.1 p.2.2 + 2 ≤ 2 ^ 66 := by
  decide

/-- A codeword of `RS[K, x, 1]` is constant. -/
theorem rsCode_one_const {K : Type*} [Field K] {n : ℕ} {x : Fin n → K} {w : Fin n → K}
    (hw : w ∈ rsCode x 1) (i j : Fin n) : w i = w j := by
  obtain ⟨p, hp, rfl⟩ := mem_rsCode.1 hw
  rw [eq_C_of_degree_le_zero (p := p) (Nat.WithBot.lt_one_iff_le_zero.1 (by exact_mod_cast hp))]
  simp [evalWord]

/-- **Positive control of `lineBad`**: a line of codewords has no bad `z`
(`2e + k ≤ n`). -/
theorem lineBad_codewords {K : Type*} [Field K] [DecidableEq K] {n : ℕ} {x : Fin n → K}
    (hx : Function.Injective x) {k e : ℕ} (h : 2 * e + k ≤ n) {u₀ u₁ : Fin n → K}
    (h₀ : u₀ ∈ rsCode x k) (h₁ : u₁ ∈ rsCode x k) : lineBad (rsCode x k) e u₀ u₁ = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨w, hw, hcl, hnot⟩
  have huz : u₀ + z • (u₁ - u₀) ∈ rsCode x k :=
    add_mem h₀ (Submodule.smul_mem _ _ (sub_mem h₁ h₀))
  have hfull : n - e ≤ (agreeSet (u₀ + z • (u₁ - u₀)) (u₀ + z • (u₁ - u₀))).card := by
    simp [agreeSet]
  obtain rfl := close_unique hx h hw huz hcl hfull
  exact hnot ⟨u₀, h₀, u₁, h₁, by ext j; simp⟩

theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] fact_prime_five

/-- **Negative control of `lineBad`**: it is not always empty. Over `GF(5)`, points `0, 1, 2`,
`k = 1`, `e = 1` (`2e + k ≤ n`): the line from `(0, 0, 1)` to `(0, 1, 0)` is bad at `z = 0`
(`(0, 0, 1)` is close to `0` on `{0, 1}`, where `u₁ = (0, 1)` is not constant). -/
theorem lineBad_nonempty :
    (0 : ZMod 5) ∈ lineBad (rsCode ![(0 : ZMod 5), 1, 2] 1) 1 ![0, 0, 1] ![0, 1, 0] := by
  refine ⟨0, zero_mem _, by decide, ?_⟩
  rintro ⟨v₀, -, v₁, hv₁, hagree⟩
  have h0 : (0 : Fin 3) ∈ agreeSet₂ ![(0 : ZMod 5), 0, 1] ![0, 1, 0] v₀ v₁ := by
    rw [hagree]; decide
  have h1 : (1 : Fin 3) ∈ agreeSet₂ ![(0 : ZMod 5), 0, 1] ![0, 1, 0] v₀ v₁ := by
    rw [hagree]; decide
  rw [mem_agreeSet₂] at h0 h1
  have := rsCode_one_const hv₁ 0 1
  rw [← h0.2, ← h1.2] at this
  exact absurd this (by decide)

/-- **Negative control of `fold_preserves`** (S-D-m2): at the bad `z = 0` of
`lineBad_nonempty` the fold is jointly close with `A = {0, 1}`, the pair rows are not. -/
theorem fold_preserves_fails_at_bad :
    JointClose (rsCode ![(0 : ZMod 5), 1, 2] 1) 1
      (foldRows (0 : ZMod 5) (fun _ : Unit => ![(0 : ZMod 5), 0, 1]) (fun _ => ![0, 1, 0]))
        {0, 1} ∧
    ¬ JointClose (rsCode ![(0 : ZMod 5), 1, 2] 1) 1
      (pairRows (fun _ : Unit => ![(0 : ZMod 5), 0, 1]) (fun _ => ![0, 1, 0])) {0, 1} := by
  constructor
  · refine ⟨by decide, fun _ => 0, fun _ => zero_mem _, ?_⟩
    ext j; simp only [mem_jointAgree, foldRows]; fin_cases j <;> decide
  · rintro ⟨-, V, hV, hA⟩
    have h0 : (0 : Fin 3) ∈ jointAgree (pairRows (fun _ : Unit => ![(0 : ZMod 5), 0, 1])
      (fun _ => ![0, 1, 0])) V := by rw [hA]; decide
    have h1 : (1 : Fin 3) ∈ jointAgree (pairRows (fun _ : Unit => ![(0 : ZMod 5), 0, 1])
      (fun _ => ![0, 1, 0])) V := by rw [hA]; decide
    rw [mem_jointAgree] at h0 h1
    have := rsCode_one_const (hV (true, ())) 0 1
    have e0 := h0 (true, ()); have e1 := h1 (true, ())
    simp only [pairRows_true] at e0 e1
    rw [← e0, ← e1] at this
    exact absurd this (by decide)

/-- **Negative control of `close_unique`** (BLUEPRINT §5.6, "`2e = d`"): without `2e + k ≤ n`
two codewords can be equally close. Over `GF(5)`, points `0, 1`, `k = 1`, `e = 1` (`2e = d = 2`):
the word `(0, 1)` agrees with the codewords `0` and `1` on one position each. -/
theorem close_not_unique_at_d :
    ∃ u w w' : Fin 2 → ZMod 5, w ∈ rsCode ![(0 : ZMod 5), 1] 1 ∧ w' ∈ rsCode ![(0 : ZMod 5), 1] 1 ∧
      2 - 1 ≤ (agreeSet u w).card ∧ 2 - 1 ≤ (agreeSet u w').card ∧ w ≠ w' := by
  refine ⟨![0, 1], 0, 1, zero_mem _, mem_rsCode.2 ⟨1, by simp, by ext j; simp [evalWord]⟩,
    by decide, by decide, fun h => absurd (congrFun h 0) (by decide)⟩

/-- **Positive control of `positions_card`** on a toy: `n = 4`, `t = 2`, `S = {0, 1}`:
`4 = 2^2` of the `16` position pairs. -/
theorem positions_card_toy :
    (univ.filter fun f : Fin 2 → Fin 4 => ∀ i, f i ∈ ({0, 1} : Finset (Fin 4))).card = 4 := by
  decide

/-- `D (2^64) = D 0` (the `UInt64` wrap). -/
theorem D_two_pow_64 : D (2 ^ 64) = D 0 := rfl

/-- **Negative control of `D_injOn`**: its bound is sharp, `D` is not injective on
`[0, 2^64 + 1)`. -/
theorem D_not_injOn_succ : ¬ Set.InjOn D (Set.Iio (2 ^ 64 + 1)) := fun h =>
  absurd (h (Set.mem_Iio.2 (by norm_num)) (Set.mem_Iio.2 (by norm_num)) D_two_pow_64)
    (by norm_num)

/-- The `FRRS` lemmas instantiated on `D` (a remark, not a control): `Ŵ_v(D[2^v]) = 1` and `X_x` has degree `x`
for `x < 2^64` (the hypotheses of the `FRRS` lemmas are discharged by `D_injOn`). -/
theorem novel_D_ok {v x : ℕ} (hv : v < 64) (hx : x < 2 ^ 64) :
    (normW D v).eval (D (2 ^ v)) = 1 ∧ novelX D x ≠ 0 ∧ (novelX D x).natDegree = x :=
  ⟨normW_eval_self D_injOn hv, novelX_natDegree D_injOn hx⟩

/-- **Negative control of block-triangularity**: the vanishing stops at `2^v`: `X_{2^v}` is
`1` at `D[2^v]`, while it vanishes on `D[0 … 2^v)`. -/
theorem novel_D_triangular {v j : ℕ} (hv : v < 64) (hj : j < 2 ^ v) :
    (novelX D (2 ^ v)).eval (D j) = 0 ∧ (novelX D (2 ^ v)).eval (D (2 ^ v)) = 1 := by
  refine ⟨novelX_eval_zero D (Nat.testBit_two_pow_self) hj, ?_⟩
  rw [novelX_eq_bitProd D (show 2 ^ v < 2 ^ (v + 1) from Nat.pow_lt_pow_right (by norm_num)
    (by omega)), show 2 ^ v = 2 ^ v + 0 by rfl, bitProd_succ_hi _ (by positivity)]
  simp [bitProd, bitSel, normW_eval_self D_injOn hv]

/-- **Control of `Enc`** (BLUEPRINT §5.6, "distinct messages differ"): on `D`, distinct messages
give codewords that differ in at least `n − k + 1` positions (`k ≤ n ≤ nMax`); in particular a
codeword has one message (the round trip of `coeffs_of_values`). -/
theorem enc_D_dist {M : Type*} [Field M] [Algebra F M] [DecidableEq M] {n k : ℕ}
    (hn : n ≤ nMax) (hkn : k ≤ n) {c c' : Fin k → M} (h : c ≠ c') :
    n + 1 ≤ k + hammingDist (enc (M := M) D n k c) (enc D n k c') := by
  have hk : k ≤ nMax := hkn.trans hn
  have hmem : ∀ c : Fin k → M, enc (M := M) D n k c ∈ rsCode (Dpts n) k := fun c => by
    rw [← encCode_D hk]; exact LinearMap.mem_range.2 ⟨c, rfl⟩
  exact rs_minDist (Dpts_injective hn) (hmem c) (hmem c')
    (fun e => h (enc_injective D_injOn_nMax hk hn hkn e))

end Controls

end FR
