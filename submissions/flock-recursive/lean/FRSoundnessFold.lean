-- New for `flock-recursive` (BLUEPRINT A.10 P1.i, C.i, P3.i, §5.3; stage S-G1i).
-- RET-1: position-free declarations moved to `FRSoundnessCoreWeights`.
import FRSoundnessWeights
import FRSoundnessWalk
import FRSoundnessCoreWeights

/-!
# The Ligerito tail's doom ingredients: intermediate folds (the far doom) and P3's batched table

* **Part A: the far doom of P1.i** (A.10: "the fold rounds also carry the proximity doom").
  `pf κ L es i l` is level `i`'s word after `l` fold rounds (row `r` is
  `Σ_{u<2^l} eq(sᵢ, u)·W[u + 2^l r]`, `pf_succ`: one more round folds rows `2r`, `2r + 1` at
  `s_l`). **`closeP l`**: the intermediate fold is jointly `eᵢ`-close. `closeP_zero`: at `l = 0` this is
  `¬ far_i`; `closeP_succ`: closeness survives a fold; **`closeP_unfold`**: if the fold is close
  but the intermediate fold before it is not, `s_l` lies in a set of at most `2^(ℓ−l−1)·C_mca`
  elements (`fold_lift`, `round_bad_cover`); **`closeP_of_truthP2`**: after all `ℓᵢ` rounds, a
  close next codeword (`truthP2`) makes the fold close, so a far fold refutes `truthP2`.
* **Part B: P3.i's batched table** (A.10 P3.i). `p3T κ L es i d`: the 512 query errors
  `consErr q` (`0` past `tᵢ`) plus the claim's offset `d`. **`p3T_mle`**: its extension at `κ_c` is
  `d + p3Batch`; **`vNext_sub`**: `v_{i+1} − ⟨wNext Wf, f⁽ⁱ⁺¹⁾⟩ = d + p3Batch` with
  `d = c − ⟨Wf, f⁽ⁱ⁺¹⁾⟩`; **`p3T_ne_zero`**: the table is nonzero when a query is inconsistent
  or `d ≠ 0`; `mlDoomF_step`: binding F coordinates (embedded in K) loses at most one value each.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: intermediate folds -/

section Generic

variable {K' : Type*} [Field K'] [DecidableEq K'] {n : ℕ}

end Generic

/-- Level `i`'s word with ℕ-indexed rows (`0` past the rows). -/
noncomputable def wN (κ : Kind) (L es : Log) (i r : ℕ) : Fin (2 ^ (lvl κ i).logN) → K :=
  fun j => if h : r < (lvl κ i).rows then wordK κ L es i ⟨r, h⟩ j else 0

/-- **Level `i`'s word after `l` fold rounds**: row `r` is `Σ_{u<2^l} eq(sᵢ, u)·W[u + 2^l r]`
(the rounds bind the row bits low first). -/
noncomputable def pf (κ : Kind) (L es : Log) (i l r : ℕ) : Fin (2 ^ (lvl κ i).logN) → K :=
  fun j => ∑ u ∈ range (2 ^ l), eqBits (sAt es i) l u * wN κ L es i (u + 2 ^ l * r) j

/-- **The intermediate fold is close**: its `2^(ℓᵢ−l)` rows are jointly `eᵢ`-close to `C_K`. P1.i's
far doom is `¬ closeP` at the rounds answered. -/
def closeP (κ : Kind) (L es : Log) (i l : ℕ) : Prop :=
  CloseN (codeK κ i) (lvE κ i) (2 ^ ((lvl κ i).ell - l)) (pf κ L es i l)

/-- One more round folds rows `2r`, `2r + 1` at `s_l`. -/
theorem pf_succ (κ : Kind) (L es : Log) (i l : ℕ) :
    pf κ L es i (l + 1) = foldN (sAt es i l) (pf κ L es i l) := by
  funext r j
  set s := sAt es i
  have e1 : ∀ u ∈ range (2 ^ l), eqBits s (l + 1) u = eqBits s l u * (1 - s l) :=
    fun u hu => bitSel_succ_lo _ _ (mem_range.1 hu)
  have e2 : ∀ u ∈ range (2 ^ l), eqBits s (l + 1) (2 ^ l + u) = eqBits s l u * s l :=
    fun u hu => bitSel_succ_hi _ _ (mem_range.1 hu)
  have hA : ∀ u, u + 2 ^ (l + 1) * r = u + 2 ^ l * (2 * r) := fun u => by ring
  have hB : ∀ u, 2 ^ l + u + 2 ^ (l + 1) * r = u + 2 ^ l * (2 * r + 1) := fun u => by ring
  simp only [pf, foldN, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hr : range (2 ^ (l + 1)) = range (2 ^ l + 2 ^ l) := by congr 1; ring
  have s1 : ∑ u ∈ range (2 ^ l), eqBits s (l + 1) u * wN κ L es i (u + 2 ^ (l + 1) * r) j =
      ∑ u ∈ range (2 ^ l), eqBits s l u * (1 - s l) * wN κ L es i (u + 2 ^ l * (2 * r)) j :=
    sum_congr rfl fun u hu => by rw [e1 u hu, hA]
  have s2 : ∑ u ∈ range (2 ^ l),
      eqBits s (l + 1) (2 ^ l + u) * wN κ L es i (2 ^ l + u + 2 ^ (l + 1) * r) j =
      ∑ u ∈ range (2 ^ l), eqBits s l u * s l * wN κ L es i (u + 2 ^ l * (2 * r + 1)) j :=
    sum_congr rfl fun u hu => by rw [e2 u hu, hB]
  rw [hr, sum_range_add, s1, s2, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun u _ => by ring

theorem pf_zero (κ : Kind) (L es : Log) (i r : ℕ) : pf κ L es i 0 r = wN κ L es i r := by
  funext j; simp [pf, eqBits, bitSel]

/-- **`closeP 0` is `¬ far_i`.** -/
theorem closeP_zero {κ : Kind} {L es : Log} {i : ℕ} : closeP κ L es i 0 ↔ ¬ farL κ L es i := by
  have hrow : (lvl κ i).rows = 2 ^ ((lvl κ i).ell - 0) := by rw [Nat.sub_zero]; rfl
  have heq : (fun r : Fin (2 ^ ((lvl κ i).ell - 0)) => pf κ L es i 0 r) =
      wordK κ L es i ∘ finCongr hrow.symm := by
    funext r j
    simp only [pf_zero, wN, Function.comp_apply, finCongr_apply, Fin.cast]
    have hr : (r : ℕ) < (lvl κ i).rows := by rw [hrow]; exact r.2
    simp only [hr, ↓reduceDIte]
  simp only [closeP, CloseN, heq, jointClose_equiv, farL, not_forall, not_not]

/-- Closeness survives the rounds. -/
theorem closeP_succ {κ : Kind} {L es : Log} {i l : ℕ} (hl : l < (lvl κ i).ell)
    (h : closeP κ L es i l) : closeP κ L es i (l + 1) := by
  unfold closeP at h ⊢
  rw [two_pow_sub hl] at h
  rw [pf_succ]
  exact closeN_fold _ h

theorem closeP_of_not_far {κ : Kind} {L es : Log} {i : ℕ} (hf : ¬ farL κ L es i) :
    ∀ l ≤ (lvl κ i).ell, closeP κ L es i l
  | 0, _ => closeP_zero.mpr hf
  | l + 1, hl => closeP_succ (by omega) (closeP_of_not_far hf l (by omega))

/-- The bad set of round `l` (`round_bad_cover`): at most `2^(ℓᵢ−l−1)·C_mca(nᵢ, kᵢ, eᵢ)` values. -/
theorem closeP_cover {κ : Kind} {i : ℕ} (hi : i < 5) (L es : Log) {l : ℕ}
    (hl : l < (lvl κ i).ell) :
    ∃ B : Finset K, B.card ≤ 2 ^ ((lvl κ i).ell - (l + 1)) * cMca (lvN κ i) (lvK κ i) (lvE κ i) ∧
      ∀ z ∉ B, closeP κ L es i l ∨ ¬ CloseN (codeK κ i) (lvE κ i) (2 ^ ((lvl κ i).ell - (l + 1)))
        (foldN z (pf κ L es i l)) := by
  obtain ⟨hek, hN, -, -, hn⟩ := lv_params κ hi
  have hnN : 2 ^ (lvl κ i).logN ≤ nMax := hn ▸ hN
  obtain ⟨B, hB, hsub⟩ := round_bad_cover (Dpts_injective hnN) (by rw [← hn]; exact hek)
    (fun c : Fin (2 ^ ((lvl κ i).ell - (l + 1))) => pf κ L es i l (2 * c))
    (fun c => pf κ L es i l (2 * c + 1))
  refine ⟨B, by simpa [lvN, Fintype.card_fin] using hB, fun z hz => ?_⟩
  by_cases hc : CloseN (codeK κ i) (lvE κ i) (2 ^ ((lvl κ i).ell - (l + 1)))
    (foldN z (pf κ L es i l))
  · left
    unfold closeP
    rw [two_pow_sub hl]
    exact closeN_unfold (Dpts_injective hnN) (by rw [← hn]; exact hek)
      (fun c hzc => hz (hsub c hzc)) hc
  · exact Or.inr hc

/-- Level `i`'s encoding is a codeword of `C_K`. -/
theorem encAt_eq_enc {κ : Kind} {i : ℕ} (hi : i < 5) (m : ℕ → K)
    (j : Fin (2 ^ (lvl κ i).logN)) :
    encAt κ i m j = enc D (2 ^ (lvl κ i).logN) _ (fun x : Fin (2 ^ mLog κ i) => m x) j := by
  obtain ⟨-, hN, hm, -, hn⟩ := lv_params κ hi
  rw [encAt, encF_eq hm (lt_of_lt_of_le j.2 (hn ▸ hN)), enc_eq_encN]

theorem enc_mem_codeK {κ : Kind} {i : ℕ} (hi : i < 5) (c : Fin (2 ^ mLog κ i) → K) :
    enc D (2 ^ (lvl κ i).logN) _ c ∈ codeK κ i := by
  obtain ⟨-, hN, -, hk, hn⟩ := lv_params κ hi
  have hkn : 2 ^ mLog κ i ≤ 2 ^ (lvl κ i).logN := by
    rw [← hk, ← hn]; unfold lvK; exact Nat.div_le_self _ _
  rw [codeK, hk, ← encCode_D (hkn.trans (hn ▸ hN))]
  exact LinearMap.mem_range_self _ c

/-- After all rounds the single row is the column fold `foldAt`. -/
theorem pf_full (κ : Kind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (lvl κ i).logN)) :
    pf κ L es i (lvl κ i).ell 0 j = foldAt κ L es i j := by
  simp only [pf, mul_zero, add_zero, foldAt]
  rw [← Fin.sum_univ_eq_sum_range (fun u => eqBits (sAt es i) (lvl κ i).ell u * wN κ L es i u j)]
  refine sum_congr rfl fun u _ => ?_
  simp only [wN, Level.rows, u.2, ↓reduceDIte]

/-- **A close next codeword makes the full fold close** (`truthP2`): a far fold refutes it. -/
theorem closeP_of_truthP2 {κ : Kind} {L es : Log} {i : ℕ} (hi : i < 5)
    (h : truthP2 κ L es i) : closeP κ L es i (lvl κ i).ell := by
  classical
  refine ⟨consSet κ L es i, h, fun _ => enc D _ _ fun x : Fin (2 ^ mLog κ i) =>
    nextMsg κ L es i x, fun _ => enc_mem_codeK hi _, ?_⟩
  ext j
  simp only [mem_jointAgree, consSet, mem_filter, mem_univ, true_and]
  rw [encAt_eq_enc hi]
  constructor
  · intro hj; have := hj 0; rwa [Fin.val_zero, pf_full] at this
  · intro hj r
    have hr0 : (r : ℕ) = 0 := by have := r.2; simp only [Nat.sub_self, pow_zero] at this; omega
    rw [hr0, pf_full]; exact hj

/-! ## Part B: P3.i's batched table -/

/-- **P3.i's table** (512 entries over `κ_c`'s 9 coordinates): query `q`'s consistency error
(`0` past `tᵢ`), plus the folded claim's offset `d`. -/
noncomputable def p3T (κ : Kind) (L es : Log) (i : ℕ) (d : K) : Array K :=
  Array.ofFn (n := 2 ^ 9) fun q => (if (q : ℕ) < (lvl κ i).t then consErr κ L es i q else 0) + d

theorem p3T_size (κ : Kind) (L es : Log) (i : ℕ) (d : K) : (p3T κ L es i d).size = 2 ^ 9 :=
  Array.size_ofFn

theorem tbl_p3T (κ : Kind) (L es : Log) (i : ℕ) (d : K) (q : Fin (2 ^ 9)) :
    tbl 9 (p3T κ L es i d) q = (if (q : ℕ) < (lvl κ i).t then consErr κ L es i q else 0) + d := by
  simp [tbl, p3T, Array.getD_eq_getD_getElem?]

theorem lvl_t_lt (κ : Kind) {i : ℕ} (hi : i < 5) : (lvl κ i).t < 2 ^ 9 - 1 := by
  cases κ <;> interval_cases i <;> decide

/-- **The table's extension at `κ_c`** is `d + p3Batch`. -/
theorem p3T_mle (κ : Kind) (L es : Log) {i : ℕ} (hi : i < 5) (d : K) :
    ∑ q : Fin (2 ^ 9), eqBits (fun v => algebraMap F K (kcAt es i v)) 9 q *
      tbl 9 (p3T κ L es i d) q = d + p3Batch κ L es i := by
  set e : ℕ → K := fun q => eqBits (fun v => algebraMap F K (kcAt es i v)) 9 q
  set g : ℕ → K := fun q => if q < (lvl κ i).t then consErr κ L es i q else 0
  have h1 : ∀ q : Fin (2 ^ 9), e q * tbl 9 (p3T κ L es i d) q = e q * g q + e q * d :=
    fun q => by rw [tbl_p3T, mul_add]
  rw [sum_congr rfl fun q _ => h1 q, sum_add_distrib, ← sum_mul,
    Fin.sum_univ_eq_sum_range e, Fin.sum_univ_eq_sum_range (fun q => e q * g q)]
  suffices hs : ∑ q ∈ range (2 ^ 9), e q * g q = p3Batch κ L es i by
    rw [hs, show ∑ q ∈ range (2 ^ 9), e q = 1 from sum_eqBits_one _ _, one_mul, add_comm]
  have ht : (lvl κ i).t ≤ 2 ^ 9 := by have := lvl_t_lt κ hi; omega
  rw [← Finset.sum_range_add_sum_Ico _ ht, Finset.sum_eq_zero (s := Ico _ _) fun q hq => by
    have : ¬ q < (lvl κ i).t := by simp only [mem_Ico] at hq; omega
    simp only [g, this, ↓reduceIte, mul_zero],
    add_zero, p3Batch]
  refine sum_congr rfl fun q hq => ?_
  simp only [g, e, mem_range.1 hq, ↓reduceIte, K.smulF_eq_mul, ← K.algebraMap_eq_ofF,
    algebraMap_eqBits]

/-- **The next claim's error** (A.10 P3.i): `v_{i+1} − ⟨wNext Wf, f⁽ⁱ⁺¹⁾⟩ = d + p3Batch`, with
`d = c − ⟨Wf, f⁽ⁱ⁺¹⁾⟩` over level `i`'s folded message. -/
theorem vNext_sub (κ : Kind) (L es : Log) (i : ℕ) (Wf : ℕ → K) (c : K) :
    vNext κ L es i c - ∑ x ∈ range (2 ^ mLog κ i), wNext κ es i Wf x * nextMsg κ L es i x =
      (c - ∑ x ∈ range (2 ^ mLog κ i), Wf x * nextMsg κ L es i x) + p3Batch κ L es i := by
  have hq : ∀ q, foldAtN κ L es i (qPos κ es i q) = consErr κ L es i q +
      ∑ x ∈ range (2 ^ mLog κ i), nextMsg κ L es i x * gW κ i (qPos κ es i q) x := by
    intro q; rw [consErr, ← encAt_eq_sum]; ring
  simp only [vNext, p3Batch, wNext, hq, K.smulF_eq_mul, mul_add, sum_add_distrib, add_mul,
    mul_sum, sum_mul]
  rw [sum_comm (s := range (lvl κ i).t)]
  have hc : ∑ y ∈ range (2 ^ mLog κ i), ∑ q ∈ range (lvl κ i).t,
      K.ofF (eqBits (kcAt es i) 9 q) * (nextMsg κ L es i y * gW κ i (qPos κ es i q) y) =
      ∑ y ∈ range (2 ^ mLog κ i), ∑ q ∈ range (lvl κ i).t,
        K.ofF (eqBits (kcAt es i) 9 q) * gW κ i (qPos κ es i q) y * nextMsg κ L es i y :=
    sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [hc]
  ring

/-- **The table is nonzero** when a query is inconsistent or the offset is nonzero (`tᵢ < 511`,
so the last entry is `d`). -/
theorem p3T_ne_zero {κ : Kind} {L es : Log} {i : ℕ} (hi : i < 5) {d : K}
    (h : ¬ truthP3 κ L es i ∨ d ≠ 0) : tbl 9 (p3T κ L es i d) ≠ 0 := by
  intro hz
  have ht := lvl_t_lt κ hi
  have hd : d = 0 := by
    have := congrFun hz ⟨2 ^ 9 - 1, by omega⟩
    rwa [tbl_p3T, ite_eq_right_iff.mpr fun h => absurd h (by simp; omega), zero_add] at this
  rcases h with h | h
  · refine h fun q hq => ?_
    have := congrFun hz ⟨q, by omega⟩
    rwa [tbl_p3T, ite_eq_left_iff.mpr fun h => absurd hq h, hd, add_zero] at this
  · exact h hd

end FR.Snd
