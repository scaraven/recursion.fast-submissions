-- New for `flock-recursive` (BLUEPRINT A.10 P1.i, C.i, P3.i, §5.3; stage S-G1i).
import FRSoundnessWeights
import FRSoundnessWalk

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

/-- `ι`-indexed rows are close iff their reindexing is. -/
theorem jointClose_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (σ : ι' ≃ ι)
    {C : Submodule K' (Fin n → K')} {e : ℕ} {U : ι → Fin n → K'} {A : Finset (Fin n)} :
    JointClose C e (U ∘ σ) A ↔ JointClose C e U A := by
  constructor
  · rintro ⟨hA, V, hV, rfl⟩
    refine ⟨hA, V ∘ σ.symm, fun i => hV _, ?_⟩
    ext j
    simp only [mem_jointAgree, Function.comp_apply]
    exact ⟨fun h i' => by simpa using h (σ i'), fun h i => by simpa using h (σ.symm i)⟩
  · rintro ⟨hA, V, hV, rfl⟩
    refine ⟨hA, V ∘ σ, fun i => hV _, ?_⟩
    ext j
    simp only [mem_jointAgree, Function.comp_apply]
    exact ⟨fun h i => by simpa using h (σ.symm i), fun h i' => h (σ i')⟩

/-- Rows `0 … 2m−1` as (parity, half). -/
def evOdd (m : ℕ) : Fin (2 * m) ≃ Bool × Fin m where
  toFun r := (r.val % 2 = 1, ⟨r.val / 2, by omega⟩)
  invFun p := ⟨2 * p.2.val + (if p.1 then 1 else 0), by have := p.2.2; split <;> omega⟩
  left_inv r := by
    ext
    simp only [decide_eq_true_eq]
    split <;> omega
  right_inv p := by
    obtain ⟨b, c⟩ := p
    cases b <;> refine Prod.ext ?_ (Fin.ext ?_)
    all_goals simp
    all_goals omega

/-- The first `m` ℕ-indexed rows are jointly close. -/
def CloseN (C : Submodule K' (Fin n → K')) (e m : ℕ) (U : ℕ → Fin n → K') : Prop :=
  ∃ A, JointClose C e (fun r : Fin m => U r) A

/-- One fold of rows `2c`, `2c + 1` at `z`. -/
def foldN (z : K') (U : ℕ → Fin n → K') (c : ℕ) : Fin n → K' :=
  U (2 * c) + z • (U (2 * c + 1) - U (2 * c))

/-- **Closeness survives a fold** (no bad-set condition: fold the codewords too). -/
theorem closeN_fold {C : Submodule K' (Fin n → K')} {e m : ℕ} {U : ℕ → Fin n → K'} (z : K')
    (h : CloseN C e (2 * m) U) : CloseN C e m (foldN z U) := by
  classical
  obtain ⟨A, hA, V, hV, hVA⟩ := h
  let V' : Fin m → Fin n → K' := fun c =>
    V ⟨2 * c, by omega⟩ + z • (V ⟨2 * c + 1, by omega⟩ - V ⟨2 * c, by omega⟩)
  refine ⟨_, ?_, V', fun c => add_mem (hV _) (Submodule.smul_mem _ _ (sub_mem (hV _) (hV _))),
    rfl⟩
  refine hA.trans (card_le_card fun j hj => ?_)
  rw [← hVA, mem_jointAgree] at hj
  rw [mem_jointAgree]
  intro c
  have h0 := hj ⟨2 * c, by omega⟩
  have h1 := hj ⟨2 * c + 1, by omega⟩
  simp only [foldN, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, V'] at h0 h1 ⊢
  rw [h0, h1]

/-- **A fold that becomes close from far rows hit a bad line** (`fold_lift`): if the fold at `z`
is close and `z` is in no line's bad set, the rows were close. -/
theorem closeN_unfold {x : Fin n → K'} (hx : Function.Injective x) {k e m : ℕ}
    (hk : 2 * e + k ≤ n) {U : ℕ → Fin n → K'} {z : K'}
    (hz : ∀ c : Fin m, z ∉ lineBad (rsCode x k) e (U (2 * c)) (U (2 * c + 1)))
    (h : CloseN (rsCode x k) e m (foldN z U)) : CloseN (rsCode x k) e (2 * m) U := by
  obtain ⟨A, hA, W, hW, hWA⟩ := h
  obtain ⟨V₀, V₁, hV₀, hV₁, -, hV⟩ := fold_lift (U₀ := fun c : Fin m => U (2 * c))
    (U₁ := fun c : Fin m => U (2 * c + 1)) hx hk hz hA hW hWA
  have hc : JointClose (rsCode x k) e (pairRows (fun c : Fin m => U (2 * c))
      (fun c : Fin m => U (2 * c + 1))) A :=
    ⟨hA, pairRows V₀ V₁, fun ⟨b, c⟩ => by cases b <;> simp [hV₀, hV₁], hV⟩
  refine ⟨A, ?_⟩
  rw [← jointClose_equiv (evOdd m)] at hc
  convert hc using 2
  funext r
  simp only [Function.comp_apply, evOdd, Equiv.coe_fn_mk, pairRows, decide_eq_true_eq]
  split <;> congr 1 <;> omega

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

theorem two_pow_sub {ℓ l : ℕ} (h : l < ℓ) : 2 ^ (ℓ - l) = 2 * 2 ^ (ℓ - (l + 1)) := by
  rw [← pow_succ']; congr 1; omega

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

theorem sum_eqBits_one {R : Type*} [CommRing R] (r : ℕ → R) (ℓ : ℕ) :
    ∑ q ∈ range (2 ^ ℓ), eqBits r ℓ q = 1 := by
  have := tensor_identity r (fun _ => 1) ℓ
  simp only [bitProd, mul_one, sub_add_cancel, prod_const_one] at this
  rw [← this]
  refine sum_congr rfl fun q _ => ?_
  simp [bitSel]

theorem algebraMap_eqBits (r : ℕ → F) (ℓ q : ℕ) :
    algebraMap F K (eqBits r ℓ q) = eqBits (fun v => algebraMap F K (r v)) ℓ q := by
  simp only [eqBits, bitSel, map_prod, apply_ite, map_sub, map_one]

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

open Classical in
/-- **Binding F coordinates (embedded in K) of a K table**: each loses at most one value. -/
theorem mlDoomF_step {n : ℕ} {t : Array K} (ht : t.size = 2 ^ n) (l : List F)
    (hd : mlDoom n t (l.map (algebraMap F K))) :
    (univ.filter fun c : F => ¬ mlDoom n t ((l ++ [c]).map (algebraMap F K))).card ≤
      if l.length < n then 1 else 0 := by
  classical
  have h := mlDoom_step ht _ hd
  rw [List.length_map] at h
  refine le_trans ?_ h
  rw [← card_map ⟨algebraMap F K, (algebraMap F K).injective⟩]
  refine card_le_card fun c hc => ?_
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk] at hc ⊢
  obtain ⟨c', hc', rfl⟩ := hc
  simpa using hc'

/-- `¬ mlDoom` at nine F coordinates: the table's extension at them vanishes. -/
theorem not_mlDoom_nine {t : Array K} (ht : t.size = 2 ^ 9) (l : List K) (hl : 9 ≤ l.length) :
    ¬ mlDoom 9 t l ↔ ∑ q : Fin (2 ^ 9), eqBits (fun v => l.getD v 0) 9 q * tbl 9 t q = 0 := by
  have hk : (l.take 9).length = 9 := by simp; omega
  have key : tbl 0 (bindL t (l.take 9)) 0 =
      ∑ q : Fin (2 ^ 9), eqBits (fun v => l.getD v 0) 9 q * tbl 9 t q := by
    rw [bindL_mle _ _ (by rw [ht, hk]), ← mleEval_eq, mleEval_eq' t _ hk, mle]
    refine sum_congr rfl fun u _ => ?_
    rw [eqBits_eq_eq]
    congr 2
    funext v
    simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_take, v.2, ite_true]
  rw [mlDoom, hk, Nat.sub_self, not_not, ← key]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    funext u
    obtain ⟨u, hu⟩ := u
    obtain rfl : u = 0 := by simp at hu; omega
    exact h

end FR.Snd
