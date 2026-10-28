-- New for `flock-recursive` (BLUEPRINT A.10 P1.i … Pf, §5.2; stage S-G1i).
import FRSoundnessTailD

/-!
# The Ligerito tail's per-phase obligations (A.10 P1.i → Pf)

For the dooms of `FRSoundnessTailD` (parametric in `W₀`, `c₀` with `FrontLocal`):

* **Part A: reads.** `closeP_same`, `Same.take`, `agree_ext`; the D2 tables are local
  (`p1_local`, `pf_local`); `trueSum_lvT_fold`: P1.i's true sum after its rounds is `foldSum`.
* **Part B: the absorbs** (`habs`): inside P1.i (`habs_P1`) and Pf (`habs_Pf`); the handoffs
  P1.i → C.i (`habs_C`: a far fold refutes `truthP2`, `closeP_of_truthP2`), P3.i → P1.(i+1)
  (`habs_P1_next`) and P3.4 → Pf (`habs_Pf_first`).
* **Part C: the single squeezes** (`hsingle`): P1.i's round (`single_P1`: at most
  `2 + 2^(ℓᵢ−l−1)·C_mca`, the asserted round over K plus the far fold's bad set) and Pf's
  (`single_Pf`: `2`).
* **Part D: the asserted checks** (`rejT_ok`: `RejOK`).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: reads -/

theorem pf_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {i : ℕ} (hi : i < 5)
    (κ : Kind) {l : ℕ} (hl : p1Start i + 2 * l ≤ p) : pf κ L es i l = pf κ L' es' i l := by
  have hc := (tail_pos hi).1
  have he : ∀ u, eqBits (sAt es i) l u = eqBits (sAt es' i) l u :=
    eqBits_congr fun v hv => sAt_same h (by omega)
  funext r j
  simp only [pf, wN, wordK_same h hi κ (by omega), he]

theorem closeP_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {i : ℕ} (hi : i < 5)
    (κ : Kind) {l : ℕ} (hl : p1Start i + 2 * l ≤ p) :
    closeP κ L es i l ↔ closeP κ L' es' i l := by
  simp only [closeP, pf_same h hi κ hl]

theorem Same.take {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {m : ℕ} (hm : m ≤ p) :
    Same L (es.take m) L' (es'.take m) m := by
  have hA : Agree (es.take m) es m := fun q hq => entAt_take hq
  have hA' : Agree (es'.take m) es' m := fun q hq => entAt_take hq
  refine ⟨fun q hq => by rw [hA q hq, hA' q hq, h.1 q (by omega)], fun κ i hi hc => ?_⟩
  rw [(same_of_agree L hA).2 κ i hi hc, h.2 κ i hi (by omega), (same_of_agree L' hA').2 κ i hi hc]

theorem agree_ext (es₀ : Log) (as : List Digest) : Agree (ext es₀ as) es₀ es₀.length :=
  fun q hq => by rw [← entAt_take (es := ext es₀ as) hq, take_ext]

theorem kindOf_ext (es₀ : Log) (as : List Digest) (h : 0 < es₀.length) :
    kindOf (ext es₀ as) = kindOf es₀ := kindOf_congr ((agree_ext es₀ as).mono h)

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

theorem p1_local (hF : FrontLocal W₀ c₀) {i : ℕ} (hi : i < 5) :
    TruthLocal2 (p1Start i) (lvC c₀ i) (lvT W₀ i) := fun L _ _ h =>
  ⟨lvT_same hF (same_of_agree L h) hi le_rfl, lvC_same hF (same_of_agree L h) hi le_rfl⟩

theorem pf_local (hF : FrontLocal W₀ c₀) : TruthLocal2 pfStart (lvC c₀ 5) (tPf W₀) :=
  fun L _ _ h => ⟨tPf_same hF (same_of_agree L h) le_rfl, lvC5_same hF (same_of_agree L h) le_rfl⟩

theorem lvT_size (i : ℕ) (L es : Log) : ∀ t ∈ lvT W₀ i L es, t.size = 2 ^ nrP i (kindOf es) :=
  tabs_size _ _ _

theorem tPf_size (L es : Log) : ∀ t ∈ tPf W₀ L es, t.size = 2 ^ 7 := tabs_size _ _ _

theorem rchs2_sAt (es : Log) (i l : ℕ) :
    rchs2 (p1Start i) chK es l = (List.range l).map (sAt es i) := rfl

theorem fold_fTab (κ : Kind) (L es : Log) (i x : ℕ) :
    ∑ u ∈ range (2 ^ (lvl κ i).ell), eqBits (sAt es i) (lvl κ i).ell u *
      fTab κ L es i (u + 2 ^ (lvl κ i).ell * x) = foldMsg κ L es i x := by
  rw [foldMsg, ← Fin.sum_univ_eq_sum_range (fun u => eqBits (sAt es i) (lvl κ i).ell u *
    fTab κ L es i (u + 2 ^ (lvl κ i).ell * x))]
  refine sum_congr rfl fun u _ => ?_
  have hu := u.2
  simp only [fTab, Level.rows, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hu, zero_add]

/-- **P1.i's true sum after its `ℓᵢ` rounds is the folded claim's truth.** -/
theorem trueSum_lvT_fold {i : ℕ} (hi : i < 5) (L es : Log) :
    trueSum e2 (bindAll (lvT W₀ i L es) (rchs2 (p1Start i) chK es (hEll i)))
      (nrP i (kindOf es) - hEll i) = foldSum W₀ i L es := by
  rw [rchs2_sAt, lvT, nrP, ← lvl_ell (kindOf es) hi, Nat.add_sub_cancel_left,
    trueSum_tabs_fold, foldSum]
  exact sum_congr rfl fun x _ => by rw [fold_fTab, wFold]

/-! ## Part B: the absorbs -/

section Absorbs

variable (hF : FrontLocal W₀ c₀) {L es : Log} (x : ByteArray × Digest)
include hF

/-- **Inside P1.i** an absorb keeps the doom (the round count and the fold do not move). -/
theorem habs_P1 {i l : ℕ} (hi : i < 5) (hl : 1 ≤ l) (hlen : es.length = p1Start i + 2 * l) :
    D1 W₀ c₀ i L es → D1 W₀ c₀ i L (es ++ [x]) := by
  have hc := (tail_pos hi).1
  have h1 := (tail_pos hi).2.1
  have hS := same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := kindOf_append x (by omega)
  have hr : hRnd (es ++ [x]) i = hRnd es i := by
    simp only [hRnd, List.length_append, List.length_singleton]; congr 1; omega
  have hr2 : p1Start i + 2 * hRnd es i ≤ es.length := by unfold hRnd; omega
  unfold D1
  rw [hk, hr, closeP_same hS hi _ hr2, farL_same hS hi _ (by omega),
    D2_append_iff h1 (p1_local hF hi) x (by omega) (Or.inl (by omega))]
  exact id

/-- **Inside Pf** an absorb keeps the doom. -/
theorem habs_Pf {l : ℕ} (hl : 1 ≤ l) (hlen : es.length = pfStart + 2 * l) :
    DPf W₀ c₀ L es → DPf W₀ c₀ L (es ++ [x]) := by
  have hp := pfStart_eq
  unfold DPf
  rw [D2_append_iff (by omega) (pf_local hF) x (by omega) (Or.inl (by omega))]
  exact id

/-- **P1.i → C.i** (A.10): a far fold refutes `truthP2` (`closeP_of_truthP2`); a close word with a
false final claim gives a false folded claim (`trueSum_lvT_fold`). -/
theorem habs_C {i : ℕ} (hi : i < 5) (hlen : es.length = cStart i) :
    D1 W₀ c₀ i L es → DCi W₀ c₀ i L (es ++ [x]) := by
  obtain ⟨hc, h1, h3, -, -⟩ := tail_pos hi
  have hS := same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := kindOf_append x (by omega)
  have hell := lvl_ell (kindOf es) hi
  have hr : hRnd es i = hEll i := by unfold hRnd; rw [min_eq_left]; omega
  unfold D1 DCi
  rw [hk]
  rintro (hf | ⟨hf, hd, hw⟩)
  · left
    intro h2
    refine hf ?_
    rw [hr, ← hell, ← closeP_same hS hi _ (by omega)]
    exact closeP_of_truthP2 hi h2
  · right
    rw [farL_same hS hi _ (by omega), c1_same hF hS hi (by omega),
      foldSum_same hF hS hi (by omega)]
    refine ⟨hf, ?_⟩
    have ha : ans3 (p1Start i) (nrP i) es = hEll i := by
      unfold ans3 nrP; rw [hlen, ← h3, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ two_pos,
        ← hell, min_eq_right (by omega)]
    rw [ha, Wrong2, trueSum_lvT_fold hi] at hw
    exact hw

/-- **P3.i → P1.(i+1)** (A.10): a far next level is P1.(i+1)'s far fold at `l = 0`; a false next
claim is its asserted rounds' false initial claim. -/
theorem habs_P1_next {i : ℕ} (hi : i + 1 < 5) (hlen : es.length = p1Start (i + 1)) :
    finP3 W₀ c₀ i L es → D1 W₀ c₀ (i + 1) L (es ++ [x]) := by
  obtain ⟨hc, h1, -, -, -⟩ := tail_pos hi
  have hS := same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := kindOf_append x (by omega)
  have hr : hRnd (es ++ [x]) (i + 1) = 0 := by
    simp only [hRnd, List.length_append, List.length_singleton, hlen]
    rw [show p1Start (i + 1) + 1 - p1Start (i + 1) = 1 by omega]; simp
  have hfar := farL_same hS hi (kindOf es) (i := i + 1) (by omega)
  unfold finP3 D1
  rw [hk, hr, closeP_zero, not_not, hfar]
  rintro (⟨-, hf⟩ | hw)
  · exact Or.inl hf
  by_cases hf : farL (kindOf es) L es (i + 1)
  · exact Or.inl hf
  refine Or.inr ⟨hf, by simp [hlen], ?_⟩
  have ha : ans3 (p1Start (i + 1)) (nrP (i + 1)) (es ++ [x]) = 0 := by
    simp [ans3, hlen]
  rw [ha, Wrong2]
  simp only [clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero, hk]
  rw [lvT, hk, trueSum_tabs, lvC_same hF hS hi (by omega), lvW_same hF hS hi (by omega),
    fTab_same hS hi _ (by omega)]
  unfold nxSum at hw
  rwa [ite_pos' (show i < 4 by omega)] at hw

/-- **P3.4 → Pf**: a false final claim is Pf's false initial claim. -/
theorem habs_Pf_first (hlen : es.length = pfStart) :
    finP3 W₀ c₀ 4 L es → DPf W₀ c₀ L (es ++ [x]) := by
  have hS := same_append L es [x]
  have hp := pfStart_eq
  unfold finP3 DPf
  rintro (⟨h, -⟩ | hw)
  · omega
  refine ⟨by simp [hlen], ?_⟩
  have ha : ans3 pfStart (fun _ => 7) (es ++ [x]) = 0 := by simp [ans3, hlen]
  rw [ha, Wrong2]
  simp only [clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [tPf, trueSum_tabs, lvC5_same hF hS (by omega)]
  have h4 : (4 : ℕ) < 5 := by norm_num
  obtain ⟨-, -, -, h44, h45⟩ := tail_pos h4
  have hnx : nxStart 4 = pfStart := rfl
  have hk : kindOf (es ++ [x]) = kindOf es := kindOf_append x (by omega)
  have hw' : wPf W₀ L (es ++ [x]) = wPf W₀ L es := by
    funext y
    simp only [wPf, hk, wFold_same hF hS h4 (by omega), wNext_same hS h4 _ (by omega)]
  have h46 : cStart 4 = phStart 47 := rfl
  have hf' : finalAt (es ++ [x]) = finalAt es := funext fun y => by
    simp only [finalAt, msgAt, hS.1 (phStart 47) (by omega)]
  unfold nxSum at hw
  rw [ite_neg' (by norm_num)] at hw
  rw [hw', hf']
  exact hw

end Absorbs

/-! ## Part C: the single squeezes -/

theorem rounds_P1 {i l : ℕ} (hi : i < 5) (hl : l < hEll i) :
    fsItems[p1Start i + 2 * l]? = some (.absorb 96) ∧
      fsItems[p1Start i + 2 * l + 1]? = some .squeeze := by
  have h := rounds_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.1 i hi l hl

theorem rounds_Pf {l : ℕ} (hl : l < 7) :
    fsItems[pfStart + 2 * l]? = some (.absorb 96) ∧ fsItems[pfStart + 2 * l + 1]? = some .squeeze := by
  have h := rounds_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.2 l hl

theorem fsItems_length : fsItems.length = 497 := by
  have h := rounds_check
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem hEll_le {i : ℕ} (hi : i < 5) : hEll i ≤ 6 := by
  unfold hEll lvlStar; interval_cases i <;> decide

/-- P1's single-squeeze count fits `N = 239·2^128`. -/
theorem p1_N_le (κ : Kind) {i : ℕ} (hi : i < 5) :
    2 + 2 ^ 5 * cMca (lvN κ i) (lvK κ i) (lvE κ i) ≤ 239 * 2 ^ 128 := by
  cases κ <;> interval_cases i <;> decide

theorem sAt_ext1 (es : Log) (a : Digest) {i l : ℕ} (h : es.length = p1Start i + 2 * l + 1) :
    sAt (ext1 es a) i l = chK a := by
  simp only [sAt, kAt, ansAt]
  rw [show phStart (26 + 5 * i) + 2 * l + 1 = es.length by unfold p1Start at h; omega,
    entAt_ext1]

open Classical in
/-- **P1.i's round squeeze** (A.10): an escape either makes the far fold close (its challenge in
the round's bad set, `closeP_cover`) or makes a false asserted claim true (`D2_single` over K,
`2` answers). -/
theorem single_P1 (hF : FrontLocal W₀ c₀) {i l : ℕ} (hi : i < 5) (hl : l < hEll i) {L es : Log}
    (hlen : es.length = p1Start i + 2 * l + 1) (hr : ¬ RejT c₀ L es) :
    (univ.filter fun a => D1 W₀ c₀ i L es ∧ ¬ D1 W₀ c₀ i L (ext1 es a)).card ≤
      2 + 2 ^ 5 * cMca (lvN (kindOf es) i) (lvK (kindOf es) i) (lvE (kindOf es) i) := by
  obtain ⟨hc, h1, -, -, -⟩ := tail_pos hi
  set κ := kindOf es with hκ
  have hell := lvl_ell κ hi
  obtain ⟨B, hB, hBz⟩ := closeP_cover (κ := κ) hi L es (l := l) (by omega)
  have hchk : ∀ j, es.length = p1Start i + 2 * j + 1 → j < nrP i (kindOf es) →
      Chk2 (p1Start i) 32 readK chK (lvC c₀ i) L es j := by
    intro j hj _
    by_contra hcj
    exact hr (Or.inl ⟨i, hi, j, by omega, by omega, hcj⟩)
  have hD2 := D2_single (R := K) h1 (p1_local hF hi) e2_deg (M := 1)
    (fun S => by rw [card_chK_fiber, mul_one]) (lvT_size i) L es hchk
  refine (card_le_card (t := (univ.filter fun a => chK a ∈ B) ∪
    (univ.filter fun a => D2 (p1Start i) 32 readK chK (lvC c₀ i) (nrP i) e2 (lvT W₀ i) L es ∧
      ¬ D2 (p1Start i) 32 readK chK (lvC c₀ i) (nrP i) e2 (lvT W₀ i) L (ext1 es a))) ?_).trans ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and, mem_union] at ha ⊢
    obtain ⟨hd, hnd⟩ := ha
    have hS : Same L (ext1 es a) L es es.length := same_append L es _
    have hk : kindOf (ext1 es a) = κ := kindOf_ext1 es a (by omega)
    obtain ⟨hR1, hR2⟩ := hRnd_ext1 es a hl hlen
    unfold D1 at hd hnd
    rw [hk, hR2, farL_same hS hi _ (by omega), not_or, not_not] at hnd
    rw [hR1] at hd
    rcases hd with hf | ⟨hfar, hd2⟩
    · left
      by_contra hz
      rcases hBz (chK a) hz with hcl | hcl
      · exact hf hcl
      · apply hcl
        have := hnd.1
        unfold closeP at this
        rwa [pf_succ, sAt_ext1 es a hlen, pf_same hS hi κ (by omega)] at this
    · right
      exact ⟨hd2, fun h => hnd.2 ⟨hfar, h⟩⟩
  · refine (card_union_le _ _).trans ?_
    rw [card_chK_fiber]
    have h5 : 2 ^ ((lvl κ i).ell - (l + 1)) ≤ 2 ^ 5 :=
      Nat.pow_le_pow_right two_pos (by have := hEll_le hi; omega)
    have := Nat.mul_le_mul_right (cMca (lvN κ i) (lvK κ i) (lvE κ i)) h5
    omega

open Classical in
/-- **Pf's round squeeze**: `D2_single` over K, `2` answers. -/
theorem single_Pf (hF : FrontLocal W₀ c₀) {l : ℕ} {L es : Log}
    (hlen : es.length = pfStart + 2 * l + 1) (hr : ¬ RejT c₀ L es) :
    (univ.filter fun a => DPf W₀ c₀ L es ∧ ¬ DPf W₀ c₀ L (ext1 es a)).card ≤ 2 := by
  have hp := pfStart_eq
  have := D2_single (R := K) (show 1 ≤ pfStart by omega) (pf_local hF) e2_deg (M := 1)
    (nr := fun _ => 7) (fun S => by rw [card_chK_fiber, mul_one]) (fun L es => tPf_size L es) L es
    (fun j hj _ => by
      by_contra hcj
      exact hr (Or.inr ⟨j, by omega, by omega, hcj⟩))
  refine le_trans (le_of_eq ?_) this
  congr 1

/-! ## Part D: the asserted checks -/

/-- **`RejT` is a valid rejection predicate** (monotone, unchanged at squeezes, stable). -/
theorem rejT_ok (hF : FrontLocal W₀ c₀) : RejOK (RejT c₀) where
  mono L es x h := by
    have hS := same_append L es [x]
    rcases h with ⟨i, hi, j, hj, hlt, hc⟩ | ⟨j, hj, hlt, hc⟩
    · refine Or.inl ⟨i, hi, j, hj, by simp; omega, fun h' => hc ?_⟩
      rwa [chk2_same hS hlt (lvC_same hF hS hi (by omega))] at h'
    · refine Or.inr ⟨j, hj, by simp; omega, fun h' => hc ?_⟩
      rwa [chk2_same hS hlt (lvC5_same hF hS (by omega))] at h'
  sq L es x hsq := by
    have hS := same_append L es [x]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with ⟨i, hi, j, hj, hlt, hc⟩ | ⟨j, hj, hlt, hc⟩
      · have hne : p1Start i + 2 * j ≠ es.length := fun he => by
          have := (rounds_P1 hi hj).1; rw [he, hsq] at this; simp at this
        simp only [List.length_append, List.length_singleton] at hlt
        refine Or.inl ⟨i, hi, j, hj, by omega, fun h' => hc ?_⟩
        rwa [chk2_same hS (by omega) (lvC_same hF hS hi (by omega))]
      · have hne : pfStart + 2 * j ≠ es.length := fun he => by
          have := (rounds_Pf hj).1; rw [he, hsq] at this; simp at this
        simp only [List.length_append, List.length_singleton] at hlt
        refine Or.inr ⟨j, hj, by omega, fun h' => hc ?_⟩
        rwa [chk2_same hS (by omega) (lvC5_same hF hS (by omega))]
    · rcases h with ⟨i, hi, j, hj, hlt, hc⟩ | ⟨j, hj, hlt, hc⟩
      · refine Or.inl ⟨i, hi, j, hj, by simp; omega, fun h' => hc ?_⟩
        rwa [chk2_same hS hlt (lvC_same hF hS hi (by omega))] at h'
      · refine Or.inr ⟨j, hj, by simp; omega, fun h' => hc ?_⟩
        rwa [chk2_same hS hlt (lvC5_same hF hS (by omega))] at h'
  stab L n hb hci X hX := by
    have hS := same_stabX hb hci hX
    refine or_congr ⟨fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩,
      fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩⟩
      ⟨fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩,
      fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩⟩
    · exact (chk2_same hS hlt (lvC_same hF hS hi (by omega))).mpr h'
    · exact (chk2_same hS hlt (lvC_same hF hS hi (by omega))).mp h'
    · exact (chk2_same hS hlt (lvC5_same hF hS (by omega))).mpr h'
    · exact (chk2_same hS hlt (lvC5_same hF hS (by omega))).mp h'

end FR.Snd
