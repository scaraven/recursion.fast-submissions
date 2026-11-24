-- lvm6 X1 (BLUEPRINT §3 `FD1`): correctness of the pure decoder. New; the dual-code step uses
-- Mathlib's `Lagrange.coeff_eq_sum`.
import Lvm6FDTree

/-!
# `FD1` is correct

**`fd1_correct`**: if `y` agrees with `Enc(c)` on the `k + 2` positions `S` except possibly at one
(`OneErr`), `fd1` returns `c` (zero-padded to `2^ℓ`).

The steps, with `Λ = lamPoly S ℓ`, `T = S.toFinset`, `f = encPoly ptK c`:

* `Λ` vanishes on `V ∖ S` and nowhere else on `ptK [0, 2^N)` (`lamPoly_eval_out`,
  `lamPoly_eval_ne`); its degree is `2^ℓ − |T|` (`natDegree_lamPoly`).
* The dual multipliers: `Λ(ptK i) · Π_{j ∈ T∖i} (ptK i − ptK j) = c_V` for `i ∈ T`, with
  `c_V = Π_{0 < c < 2^ℓ} ptK c` independent of `i` (`lam_mul_prod_eq`, `V` is additive).
* **`dual_sum`**: `Σ_{i ∈ T} F(ptK i) Λ(ptK i) = 0` for `deg F < |T| − 1` (Lagrange: the
  coefficient `|T| − 1` of the interpolant). With `F = f` and `F = f·X`: the syndromes of a
  codeword vanish, so `s₀ = δ Λ(a*)`, `s₁ = δ Λ(a*) a*` for the error `δ` at `a*`.
* `gIn` are the values of `f·Λ` on `V` (`gIn_eq`), `deg (f·Λ) < 2^ℓ`, so `gEval` is `f·Λ` on
  `ptK [0, 2^(ℓ+1))` (`extend_eval`) and `fCos` is `f` on the coset; the coset's inverse NTT gives
  `f`'s coefficients, unique since the novel basis is triangular (`encPoly_ne_zero`).
-/

namespace Lvm6.FD

open Lvm.Nb Lvm.X Finset Polynomial

/-! ## `Λ` -/

section Lam
variable (S : List ℕ) (ℓ : ℕ)

theorem eval_lamPoly (x : BF64) :
    (lamPoly S ℓ).eval x = ∏ j ∈ range (2 ^ ℓ), if j ∈ S then 1 else x - ptK j := by
  simp only [lamPoly, eval_prod]
  refine prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem lamPoly_eval_out {j : ℕ} (hj : j < 2 ^ ℓ) (hjS : j ∉ S) : (lamPoly S ℓ).eval (ptK j) = 0 := by
  rw [eval_lamPoly]
  exact prod_eq_zero (mem_range.2 hj) (by simp [hjS])

theorem lamPoly_eval_ne (hℓ : ℓ ≤ 64) {i : ℕ} (hi : i < 2 ^ 64) (h : i ∈ S ∨ 2 ^ ℓ ≤ i) :
    (lamPoly S ℓ).eval (ptK i) ≠ 0 := by
  rw [eval_lamPoly]
  refine prod_ne_zero_iff.2 fun j hj => ?_
  split_ifs with hjS
  · exact one_ne_zero
  · have hj' := mem_range.1 hj
    have hij : i ≠ j := by rintro rfl; rcases h with h | h <;> [exact hjS h; omega]
    have h64 : j < 2 ^ 64 := hj'.trans_le (Nat.pow_le_pow_right (by norm_num) hℓ)
    exact sub_ne_zero.2 fun e => hij (ptK_injOn64 (Set.mem_Iio.2 hi) (Set.mem_Iio.2 h64) e)

theorem natDegree_lamPoly (hS : ∀ j ∈ S, j < 2 ^ ℓ) :
    (lamPoly S ℓ).natDegree = 2 ^ ℓ - S.toFinset.card := by
  classical
  rw [lamPoly, natDegree_prod_of_monic _ _ (fun j _ => by split_ifs <;> simp [monic_X_sub_C])]
  have e1 : ∀ j ∈ range (2 ^ ℓ), (if j ∈ S then (1 : BF64[X]) else X - C (ptK j)).natDegree =
      if j ∈ S then 0 else 1 := fun j _ => by split_ifs <;> simp
  rw [sum_congr rfl e1, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add]
  have e2 : (range (2 ^ ℓ)).filter (fun j => j ∈ S) = S.toFinset := by
    ext j; simp only [mem_filter, mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hS j h, h⟩⟩
  have := card_filter_add_card_filter_not (s := range (2 ^ ℓ)) (fun j => j ∈ S)
  rw [e2, card_range] at this
  omega

/-- `c_V`: the product of the nonzero points of `V = ptK [0, 2^ℓ)`. -/
noncomputable def cV : BF64 := ∏ c ∈ (range (2 ^ ℓ)).erase 0, ptK c

theorem prod_erase_eq_cV {i : ℕ} (hi : i < 2 ^ ℓ) :
    ∏ j ∈ (range (2 ^ ℓ)).erase i, (ptK i - ptK j) = cV ℓ := by
  rw [cV]
  refine prod_nbij' (fun j => i ^^^ j) (fun c => i ^^^ c) (fun j hj => ?_) (fun c hc => ?_)
    (fun j _ => by simp) (fun c _ => by simp) (fun j _ => ?_)
  · obtain ⟨hji, hj⟩ := mem_erase.1 hj
    refine mem_erase.2 ⟨fun h => hji ?_, mem_range.2 (Nat.xor_lt_two_pow hi (mem_range.1 hj))⟩
    have := congrArg (fun z => i ^^^ z) h
    simpa [← Nat.xor_assoc] using this
  · obtain ⟨hc0, hc⟩ := mem_erase.1 hc
    refine mem_erase.2 ⟨fun h => hc0 ?_, mem_range.2 (Nat.xor_lt_two_pow hi (mem_range.1 hc))⟩
    have := congrArg (fun z => i ^^^ z) h
    simpa [← Nat.xor_assoc] using this
  · rw [ptK_xor, CharTwo.sub_eq_add]

theorem pt_lt64 (hℓ : ℓ ≤ 64) {j : ℕ} (hj : j < 2 ^ ℓ) : j < 2 ^ 64 :=
  hj.trans_le (Nat.pow_le_pow_right (by norm_num) hℓ)

theorem injOn_S (hℓ : ℓ ≤ 64) (hS : ∀ j ∈ S, j < 2 ^ ℓ) : Set.InjOn ptK (S.toFinset : Set ℕ) :=
  fun a ha b hb e => ptK_injOn64 (Set.mem_Iio.2 (pt_lt64 ℓ hℓ (hS a (by simpa using ha))))
    (Set.mem_Iio.2 (pt_lt64 ℓ hℓ (hS b (by simpa using hb)))) e

theorem prodS_ne (hℓ : ℓ ≤ 64) (hS : ∀ j ∈ S, j < 2 ^ ℓ) {i : ℕ} (hi : i ∈ S) :
    ∏ j ∈ S.toFinset.erase i, (ptK i - ptK j) ≠ 0 :=
  prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 fun e => (mem_erase.1 hj).1
    (injOn_S S ℓ hℓ hS (by simpa using (mem_erase.1 hj).2) (by simpa using hi) e.symm)

/-- **The dual multipliers**: `Λ(ptK i) · Π_{j ∈ S∖i} (ptK i − ptK j) = c_V` for `i ∈ S`. -/
theorem lam_mul_prod_eq (hS : ∀ j ∈ S, j < 2 ^ ℓ) {i : ℕ} (hi : i ∈ S) :
    (lamPoly S ℓ).eval (ptK i) * ∏ j ∈ S.toFinset.erase i, (ptK i - ptK j) = cV ℓ := by
  classical
  rw [← prod_erase_eq_cV ℓ (hS i hi), eval_lamPoly]
  have e1 : ∏ j ∈ range (2 ^ ℓ), (if j ∈ S then (1 : BF64) else ptK i - ptK j) =
      ∏ j ∈ (range (2 ^ ℓ)).filter (fun j => j ∉ S), (ptK i - ptK j) := by
    rw [prod_filter]; exact prod_congr rfl fun j _ => by split_ifs <;> simp_all
  rw [e1, ← prod_union]
  · congr 1
    ext j
    simp only [mem_union, mem_filter, mem_range, mem_erase, List.mem_toFinset]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨fun h => h2 (h ▸ hi), h1⟩
      · exact ⟨h1, hS j h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hj : j ∈ S
      · exact Or.inr ⟨h1, hj⟩
      · exact Or.inl ⟨h2, hj⟩
  · refine disjoint_left.2 fun j h1 h2 => ?_
    simp only [mem_filter, mem_erase, List.mem_toFinset] at h1 h2
    exact h1.2 h2.2

/-- **The dual code** (generalised RS on `S` with multipliers `Λ/c_V`): `Σ_{i ∈ S} F(ptK i) Λ(ptK i)
= 0` for `deg F < |S| − 1`. -/
theorem dual_sum (hℓ : ℓ ≤ 64) (hS : ∀ j ∈ S, j < 2 ^ ℓ) (F : BF64[X])
    (hF : F.degree < (S.toFinset.card - 1 : ℕ)) :
    ∑ i ∈ S.toFinset, F.eval (ptK i) * (lamPoly S ℓ).eval (ptK i) = 0 := by
  have hc := Lagrange.coeff_eq_sum (injOn_S S ℓ hℓ hS) (P := F)
    (hF.trans_le (by exact_mod_cast Nat.sub_le _ _))
  rw [coeff_eq_zero_of_degree_lt hF] at hc
  have e : ∀ i ∈ S.toFinset, F.eval (ptK i) * (lamPoly S ℓ).eval (ptK i) =
      cV ℓ * (F.eval (ptK i) / ∏ j ∈ S.toFinset.erase i, (ptK i - ptK j)) := fun i hi => by
    have hi' : i ∈ S := by simpa using hi
    rw [← lam_mul_prod_eq S ℓ hS hi']
    field_simp [prodS_ne S ℓ hℓ hS hi']
  rw [sum_congr rfl e, ← mul_sum, ← hc, mul_zero]

end Lam

/-! ## Uniqueness of novel-basis coefficients on the coset -/

theorem encPoly_pad {n k : ℕ} (hk : k ≤ n) (c : Fin k → BF64) :
    encPoly ptK (fun x : Fin n => if h : (x : ℕ) < k then c ⟨x, h⟩ else 0) = encPoly ptK c := by
  let g : ℕ → BF64[X] := fun x =>
    C (if h : x < k then c ⟨x, h⟩ else 0) * (novelX ptK x).map (algebraMap BF64 BF64)
  have e1 : encPoly ptK (fun x : Fin n => if h : (x : ℕ) < k then c ⟨x, h⟩ else 0) =
      ∑ x ∈ range n, g x := Fin.sum_univ_eq_sum_range g n
  have e2 : encPoly ptK c = ∑ x ∈ range k, g x := by
    rw [← Fin.sum_univ_eq_sum_range g k, encPoly]
    exact sum_congr rfl fun x _ => by simp [g, x.2]
  rw [e1, e2]
  exact (sum_subset (range_subset_range.2 hk) fun x _ hx => by
    simp [g, show ¬ x < k from fun h => hx (mem_range.2 h)]).symm

/-- The coset's inverse NTT returns the novel-basis coefficients of a message of length
`k ≤ 2^ℓ`. -/
theorem coset_coeffs {N ℓ k : ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hk : k ≤ 2 ^ ℓ)
    (c : Fin k → BF64) {x : ℕ} (hx : x < 2 ^ ℓ) :
    coeffsAt ptK N ℓ (2 ^ ℓ) (fun j => (encPoly ptK c).eval (ptK (2 ^ ℓ + j))) x =
      if h : x < k then c ⟨x, h⟩ else 0 := by
  classical
  have hpt := ptK_injOn hN64
  have h2N : 2 ^ ℓ + 2 ^ ℓ ≤ 2 ^ N := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hN; rw [pow_succ] at this; omega
  set w : Fin (2 ^ ℓ) → BF64 := fun x =>
    coeffsAt ptK N ℓ (2 ^ ℓ) (fun j => (encPoly ptK c).eval (ptK (2 ^ ℓ + j))) x with hw
  set cp : Fin (2 ^ ℓ) → BF64 := fun x => if h : (x : ℕ) < k then c ⟨x, h⟩ else 0 with hcp
  have hnN : 2 ^ ℓ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpoly : encPoly ptK w = encPoly ptK cp := by
    rw [hcp, encPoly_pad hk c]
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := range (2 ^ ℓ))
      (v := fun j => ptK (2 ^ ℓ + j)) (fun a ha b hb e => ?_) ?_ ?_ fun j hj => ?_
    · have := hpt (Set.mem_Iio.2 (show 2 ^ ℓ + a < 2 ^ N by have := mem_range.1 ha; omega))
        (Set.mem_Iio.2 (show 2 ^ ℓ + b < 2 ^ N by have := mem_range.1 hb; omega)) e
      omega
    · rw [card_range]; exact mem_degreeLT.1 (encPoly_mem hpt hnN w)
    · rw [card_range]
      exact (mem_degreeLT.1 (encPoly_mem hpt (hk.trans hnN) c)).trans_le (by exact_mod_cast hk)
    · have hj' := mem_range.1 hj
      have hsp := coeffsAt_spec ptK_xor hpt ℓ (2 ^ ℓ) (fun j => (encPoly ptK c).eval (ptK (2 ^ ℓ + j)))
        (by omega) h2N (fun i hi => by rw [two_pow_add_eq_xor hi, ptK_xor]) j hj'
      rw [encPoly_eval_K, encN, ← hsp]
      exact Fin.sum_univ_eq_sum_range (fun x => coeffsAt ptK N ℓ (2 ^ ℓ)
        (fun j => (encPoly ptK c).eval (ptK (2 ^ ℓ + j))) x *
          algebraMap BF64 BF64 ((novelX ptK x).eval (ptK (2 ^ ℓ + j)))) _
  have hwc : w = cp := by
    by_contra hne
    apply encPoly_ne_zero hpt hnN (sub_ne_zero.2 hne)
    rw [show encPoly ptK (w - cp) = encPoly ptK w - encPoly ptK cp by
      simp [encPoly, sub_mul, sum_sub_distrib], hpoly, sub_self]
  have := congrFun hwc ⟨x, hx⟩
  simpa [hw, hcp] using this

/-! ## The main theorem -/

theorem two_eq_zero_K : (2 : BF64) = 0 := CharTwo.two_eq_zero

/-- **`fd1_correct`**: with at most one error on the `k + 2` positions `S`, `FD1` returns the
message (zero-padded to `2^ℓ`). -/
theorem fd1_correct {N ℓ k : ℕ} {S : List ℕ} {y : ℕ → BF64} {c : Fin k → BF64}
    (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (h : OneErr ℓ k S y c) :
    ∀ x < 2 ^ ℓ, fd1 N ℓ S y x = if hx : x < k then c ⟨x, hx⟩ else 0 := by
  classical
  obtain ⟨hnd, hlen, hSn, e, he⟩ := h
  have hℓ64 : ℓ ≤ 64 := by omega
  have hT : S.toFinset.card = k + 2 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  have hTn : k + 2 ≤ 2 ^ ℓ := by
    rw [← hT, ← card_range (2 ^ ℓ)]
    exact card_le_card fun j hj => mem_range.2 (hSn j (by simpa using hj))
  have hnN : 2 ^ ℓ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
  have h2N : 2 ^ (ℓ + 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hN64' : 2 ^ N ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hN64
  set f := encPoly ptK c with hf
  set L := lamPoly S ℓ with hLdef
  have hfdeg : f.degree < k := mem_degreeLT.1 (encPoly_mem (ptK_injOn hN64) (by omega) c)
  have hfe : ∀ j, f.eval (ptK j) = encN ptK c j := encPoly_eval_K c
  have hlam : ∀ i < 2 ^ (ℓ + 1), lam N S ℓ i = L.eval (ptK i) := fun i hi => lam_root hN hN64 S hi
  have hL0 : ∀ j < 2 ^ ℓ, j ∉ S → L.eval (ptK j) = 0 := fun j hj hjS => lamPoly_eval_out S ℓ hj hjS
  have hLne : ∀ j ∈ S, L.eval (ptK j) ≠ 0 := fun j hj =>
    lamPoly_eval_ne S ℓ hℓ64 (pt_lt64 ℓ hℓ64 (hSn j hj)) (Or.inl hj)
  -- the dual sums
  have d0 : ∑ j ∈ S.toFinset, f.eval (ptK j) * L.eval (ptK j) = 0 :=
    dual_sum S ℓ hℓ64 hSn f (by rw [hT]; exact hfdeg.trans_le (by exact_mod_cast (by omega : k ≤ k + 2 - 1)))
  have d1 : ∑ j ∈ S.toFinset, (f * X).eval (ptK j) * L.eval (ptK j) = 0 := by
    refine dual_sum S ℓ hℓ64 hSn (f * X) ?_
    rw [hT]
    rcases eq_or_ne f 0 with hf0 | hf0
    · rw [hf0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_mul_X, degree_eq_natDegree hf0]
      have := (natDegree_lt_iff_degree_lt hf0).2 hfdeg
      exact_mod_cast (by omega : f.natDegree + 1 < k + 2 - 1)
  -- the syndromes
  have hs0 : syn0 N ℓ S y = ∑ j ∈ S.toFinset, y j * L.eval (ptK j) := by
    rw [syn0, ← List.sum_toFinset _ hnd]
    exact sum_congr rfl fun j hj => by rw [hlam j (by have := hSn j (by simpa using hj); omega)]
  have hs1 : syn1 N ℓ S y = ∑ j ∈ S.toFinset, y j * L.eval (ptK j) * ptK j := by
    rw [syn1, ← List.sum_toFinset _ hnd]
    exact sum_congr rfl fun j hj => by rw [hlam j (by have := hSn j (by simpa using hj); omega)]
  set δ : ℕ → BF64 := fun j => y j - f.eval (ptK j) with hδ
  have hδ0 : ∀ j ∈ S, j ≠ e → δ j = 0 := fun j hj hje => by
    simp only [hδ, he j hj hje, hfe, sub_self]
  set D : BF64 := if e ∈ S then δ e * L.eval (ptK e) else 0 with hD
  have hsumδ : ∀ g : ℕ → BF64, ∑ j ∈ S.toFinset, δ j * g j = if e ∈ S then δ e * g e else 0 := by
    intro g
    split_ifs with heS
    · exact sum_eq_single_of_mem e (by simpa using heS) fun j hj hje => by
        rw [hδ0 j (by simpa using hj) hje, zero_mul]
    · exact sum_eq_zero fun j hj => by
        rw [hδ0 j (by simpa using hj) (fun h => heS (h ▸ by simpa using hj)), zero_mul]
  have hs0D : syn0 N ℓ S y = D := by
    rw [hs0]
    calc ∑ j ∈ S.toFinset, y j * L.eval (ptK j)
        = ∑ j ∈ S.toFinset, (f.eval (ptK j) * L.eval (ptK j) + δ j * L.eval (ptK j)) :=
          sum_congr rfl fun j _ => by simp only [hδ]; ring
      _ = D := by rw [sum_add_distrib, d0, zero_add, hsumδ]
  have hs1D : syn1 N ℓ S y = D * ptK e := by
    have d1' : ∑ j ∈ S.toFinset, f.eval (ptK j) * (L.eval (ptK j) * ptK j) = 0 := by
      rw [← d1]; exact sum_congr rfl fun j _ => by rw [eval_mul, eval_X]; ring
    rw [hs1]
    calc ∑ j ∈ S.toFinset, y j * L.eval (ptK j) * ptK j
        = ∑ j ∈ S.toFinset, (f.eval (ptK j) * (L.eval (ptK j) * ptK j) +
            δ j * (L.eval (ptK j) * ptK j)) :=
          sum_congr rfl fun j _ => by simp only [hδ]; ring
      _ = D * ptK e := by
          rw [sum_add_distrib, d1', zero_add, hsumδ, hD]
          split_ifs <;> ring
  -- `gIn` is `f·Λ` on `V`
  have hg : ∀ j < 2 ^ ℓ, gIn N ℓ S y j = (f * L).eval (ptK j) := by
    by_cases hD0 : D = 0
    · have hnc : ∀ j, ¬ corrAt N ℓ S y j := fun j hc => hc.1 (hs0D.trans hD0)
      have hyS : ∀ j ∈ S, y j = f.eval (ptK j) := fun j hj => by
        by_cases hje : j = e
        · subst hje
          have : δ j * L.eval (ptK j) = 0 := by rw [hD, if_pos hj] at hD0; exact hD0
          have := (mul_eq_zero.1 this).resolve_right (hLne j hj)
          simpa [hδ, sub_eq_zero] using this
        · rw [he j hj hje, hfe]
      intro j hj
      simp only [gIn, hnc, if_false, add_zero, hlam j (by omega), eval_mul]
      split_ifs with hjS
      · rw [hyS j hjS]
      · rw [hL0 j hj hjS, mul_zero]
    · have heS : e ∈ S := by by_contra h'; exact hD0 (by rw [hD, if_neg h'])
      have hs0ne : syn0 N ℓ S y ≠ 0 := hs0D ▸ hD0
      have hidx : errIdx N ℓ S y = e := by
        rw [errIdx, hs1D, hs0D, show D * ptK e * D⁻¹ = ptK e by field_simp]
        simp only [ptK, BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (pt_lt64 ℓ hℓ64 (hSn e heS))
      have hcorr : ∀ j, corrAt N ℓ S y j ↔ j = e := fun j =>
        ⟨fun hc => hc.2.2.symm.trans hidx, fun hje => ⟨hs0ne, hidx ▸ hSn e heS, hidx.trans hje.symm⟩⟩
      intro j hj
      simp only [gIn, hlam j (by omega), eval_mul]
      by_cases hje : j = e
      · subst hje
        rw [if_pos heS, if_pos ((hcorr j).2 rfl), hs0D, hD, if_pos heS]
        simp only [hδ]
        linear_combination (y j - f.eval (ptK j)) * L.eval (ptK j) * two_eq_zero_K
      · rw [if_neg (fun hc => hje ((hcorr j).1 hc)), add_zero]
        split_ifs with hjS
        · rw [he j hjS hje, hfe]
        · rw [hL0 j hj hjS, mul_zero]
  -- `deg (f·Λ) < 2^ℓ`
  have hgdeg : (f * L).degree < (2 ^ ℓ : ℕ) := by
    rcases eq_or_ne f 0 with hf0 | hf0
    · rw [hf0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
    have hLm : L.Monic := monic_prod_of_monic _ _ fun j _ => by split_ifs <;> simp [monic_X_sub_C]
    rw [degree_eq_natDegree (mul_ne_zero hf0 hLm.ne_zero), natDegree_mul hf0 hLm.ne_zero,
      natDegree_lamPoly S ℓ hSn, hT]
    have := (natDegree_lt_iff_degree_lt hf0).2 hfdeg
    exact_mod_cast (by omega : f.natDegree + (2 ^ ℓ - (k + 2)) < 2 ^ ℓ)
  have hge : ∀ i < 2 ^ (ℓ + 1), gEval N ℓ S y i = (f * L).eval (ptK i) :=
    extend_eval hN hN64 _ hgdeg _ hg
  have hfc : ∀ j < 2 ^ ℓ, fCos N ℓ S y (2 ^ ℓ + j) = f.eval (ptK (2 ^ ℓ + j)) := fun j hj => by
    have hne : L.eval (ptK (2 ^ ℓ + j)) ≠ 0 :=
      lamPoly_eval_ne S ℓ hℓ64 (by omega) (Or.inr (by omega))
    rw [fCos, if_neg (by omega), hge _ (by omega), hlam _ (by omega), eval_mul, mul_assoc,
      mul_inv_cancel₀ hne, mul_one]
  have hfc0 : ∀ j < 2 ^ ℓ, fCos N ℓ S y j = 0 := fun j hj => by rw [fCos, if_pos hj]
  intro x hx
  rw [fd1, bflyRun_eq ptK N 0 (ℓ + 1) _ (by omega)]
  simp only [coeffsAt]
  rw [if_neg (by omega), Nat.add_sub_cancel_left, coeffsAt_zero N ℓ 0 _ hfc0 x hx, sub_zero, Nat.zero_add,
    coeffsAt_congr N ℓ (2 ^ ℓ) _ (fun j => f.eval (ptK (2 ^ ℓ + j))) (fun j hj => hfc j hj) x hx]
  exact coset_coeffs hN hN64 (by omega) c hx

/-- Non-vacuity with a nonzero message and a real error: the constant message `1` (`k = 1`) on
`S = [0, 1, 2]`, with the value at position `2` wrong. -/
theorem oneErr_example1 :
    OneErr 2 1 [0, 1, 2] (fun j => if j = 2 then 0 else 1) (fun _ => 1) := by
  refine ⟨by decide, rfl, by decide, 2, fun j hj hj2 => ?_⟩
  simp [encN, novelX, bitProd, bitSel, hj2]

/-- `FD1` corrects that error: the decoded message is `1`. -/
theorem fd1_example1 : fd1 3 2 [0, 1, 2] (fun j => if j = 2 then 0 else 1) 0 = 1 := by
  rw [fd1_correct (k := 1) (c := fun _ => 1) (by norm_num) (by norm_num) oneErr_example1 0 (by norm_num)]
  rfl

end Lvm6.FD
