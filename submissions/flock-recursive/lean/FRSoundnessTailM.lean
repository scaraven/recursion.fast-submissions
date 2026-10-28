-- New for `flock-recursive` (BLUEPRINT A.10 P2.i, P3.i, §5.2; stage S-G1i).
import FRSoundnessTailO

/-!
# The Ligerito tail's multi-squeeze phases and the stability of its dooms

* **Part A: the phase facts** (checked once, `tail_ph`): the phases of C.i's, P2.i's and P3.i's
  positions, their `fsRanges` entries.
* **Part B: P2.i** (`hfin_P2`, through `p2_hround`): the escape puts every queried position in
  the consistency set of a level with `¬ truthP2` (with `truthP2`, the C.i doom already gives
  `truthC` by `truthC_of`, so no escape is possible).
* **Part C: P3.i** (`hfin_P3`, through `hfin_seq`): the escape makes the extension of the batched
  table `p3T` vanish at `κ_c` (`vNext_sub`, `p3T_mle`, `wSplit_sum`), and P2.i's final doom makes
  it nonzero (`p3T_ne_zero`): `9/2^128`.
* **Part D: stability** (`DT_stab`): every tail doom reads the same off two logs whose words agree
  (`Same` at the chain's length), once the chain has reached the phase.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: the phase facts -/

theorem tail_ph_check : (List.range 5).all (fun i => phOf (p1Start i) == 25 + 5 * i &&
    phOf (cStart i) == 26 + 5 * i && phOf (cStart i + 1) == 27 + 5 * i &&
    phOf (p3S0 i) == 27 + 5 * i && phOf (p3S0 i + 1) == 29 + 5 * i &&
    phStart (27 + 5 * i) == cStart i + 1 && phStart (28 + 5 * i) == p3S0 i + 1 &&
    phStart (29 + 5 * i) == p3S0 i + 1 && phStart (30 + 5 * i) == nxStart i &&
    fsRanges.contains (cStart i, (lvlStar i).sq) && fsRanges.contains (p3S0 i, 5)) = true := by
  unfold nxStart p1Start pfStart cStart p3S0 phOf phStart
  rw [fsStarts_eq, fsRanges_eq]; decide +kernel

theorem tail_ph {i : ℕ} (hi : i < 5) : phOf (p1Start i) = 25 + 5 * i ∧
    phOf (cStart i) = 26 + 5 * i ∧ phOf (cStart i + 1) = 27 + 5 * i ∧
    phOf (p3S0 i) = 27 + 5 * i ∧ phOf (p3S0 i + 1) = 29 + 5 * i ∧
    phStart (27 + 5 * i) = cStart i + 1 ∧ phStart (28 + 5 * i) = p3S0 i + 1 ∧
    phStart (29 + 5 * i) = p3S0 i + 1 ∧ phStart (30 + 5 * i) = nxStart i ∧
    (cStart i, (lvlStar i).sq) ∈ fsRanges ∧ (p3S0 i, 5) ∈ fsRanges := by
  have h := tail_ph_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h i hi
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

theorem ms_P2 {Dk : ℕ → Log → Log → Prop} {i : ℕ} (hi : i < 5)
    (hC : Dk (26 + 5 * i) = DCi W₀ c₀ i) (hP : Dk (27 + 5 * i) = DP2 W₀ c₀ i) :
    Dk (phOf (cStart i + 1)) = msD (Dk (phOf (cStart i))) (finP2 W₀ c₀ i) (cStart i)
      (lvlStar i).sq := by
  obtain ⟨-, h2, h3, -⟩ := tail_ph hi
  rw [h2, h3, hC, hP, DP2]

theorem ms_P3 {Dk : ℕ → Log → Log → Prop} {i : ℕ} (hi : i < 5)
    (hP : Dk (27 + 5 * i) = DP2 W₀ c₀ i) (hQ : Dk (29 + 5 * i) = DP3 W₀ c₀ i) :
    Dk (phOf (p3S0 i + 1)) = msD (Dk (phOf (p3S0 i))) (finP3 W₀ c₀ i) (p3S0 i) 5 := by
  obtain ⟨-, -, -, h4, h5, -⟩ := tail_ph hi
  rw [h4, h5, hP, hQ, DP3]

/-! ## Part B: P2.i -/

theorem lvE_lt_lvN (κ : Kind) {i : ℕ} (hi : i < 5) : lvE κ i < lvN κ i := by
  cases κ <;> interval_cases i <;> decide

open Classical in
/-- **P2.i's charge** (A.10, `p2_hround`): at most `deltaR`. -/
theorem hfin_P2 (hF : FrontLocal W₀ c₀) {Dk : ℕ → Log → Log → Prop} {i : ℕ} (hi : i < 5)
    (hC : Dk (26 + 5 * i) = DCi W₀ c₀ i) (hP : Dk (27 + 5 * i) = DP2 W₀ c₀ i)
    (L es₀ : Log) (hl : es₀.length = cStart i + 1) :
    condCount (DPos (Dp Dk)) L es₀ (lvlStar i).sq [] ≤ deltaR := by
  obtain ⟨-, h2, -, -, -, -, -, -, -, hmem, -⟩ := tail_ph hi
  have hms := ms_P2 hi hC hP
  set κ := kindOf es₀
  let S : Finset (Fin (2 ^ (lvl κ i).logN)) :=
    if truthP2 κ L es₀ i then ∅ else consSet κ L es₀ i
  refine p2_hround κ i hi hl S ?_ fun as has he => ?_
  · by_cases h : truthP2 κ L es₀ i
    · simp only [S, h, ite_true, card_empty, zero_add]; exact lvE_lt_lvN κ hi
    · simp only [S, h, ite_false]; exact consSet_card_of_not κ h
  obtain ⟨hd, hnf⟩ := esc_msD hmem hms hl as has he
  rw [h2, hC] at hd
  set X := ext es₀ as
  have hS : Same L X L es₀ (cStart i + 1) := hl ▸ same_of_agree L (agree_ext es₀ as)
  have hk : kindOf X = κ := kindOf_ext es₀ as (by omega)
  unfold finP2 at hnf
  rw [hk, not_or, not_not] at hnf
  obtain ⟨h3, hn⟩ := hnf
  rw [farL_same hS hi _ (by have := (tail_pos hi).1; have := (tail_pos hi).2.2.1; omega),
    truthC_same hS hi _ le_rfl, c1_same hF hS hi (by omega),
    foldSum_same hF hS hi (by omega)] at hn
  have hP2 : ¬ truthP2 κ L es₀ i := by
    intro h2'
    rcases hd with hd | ⟨hf, hw⟩
    · exact hd h2'
    · exact hn ⟨hf, truthC_of hi hf h2', hw⟩
  intro k hk'
  have hq := h3 k hk'
  have hlt : qPos κ X i k < 2 ^ (lvl κ i).logN := idx_lt _ _ _
  simp only [consErr, foldAtN, hlt, ↓reduceDIte, sub_eq_zero] at hq
  simp only [S, hP2, ite_false]
  refine mem_map.mpr ⟨⟨qPos κ X i k, hlt⟩, ?_, rfl⟩
  rw [← consSet_same hS hi κ le_rfl]
  simp only [consSet, mem_filter, mem_univ, true_and]
  exact hq

/-! ## Part C: P3.i -/

/-- P3.i's offset `d = c1 − ⟨Wf, f⁽ⁱ⁺¹⁾⟩`. -/
noncomputable def dP3 (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (i : ℕ) (L es : Log) : K :=
  c1 c₀ i L es - ∑ x ∈ range (2 ^ mLog (kindOf es) i),
    wFold W₀ i L es x * nextMsg (kindOf es) L es i x

theorem mLog4_le (κ : Kind) : mLog κ 4 ≤ 7 := by cases κ <;> decide

/-- `nxSum` as the next weight's inner product with level `i`'s folded message. -/
theorem nxSum_eq (W₀ : Log → Log → ℕ → K) {i : ℕ} (hi : i < 5)
    (L es : Log) : nxSum W₀ i L es = ∑ x ∈ range (2 ^ mLog (kindOf es) i),
      wNext (kindOf es) es i (wFold W₀ i L es) x * nextMsg (kindOf es) L es i x := by
  unfold nxSum
  by_cases h4 : i < 4
  · rw [ite_pos' h4, nrP, ← wSplit_sum (show i + 1 < 5 by omega)]
    rfl
  · obtain rfl : i = 4 := by omega
    rw [ite_neg' h4]
    have hm := mLog4_le (kindOf es)
    have hle : 2 ^ mLog (kindOf es) 4 ≤ 2 ^ 7 := Nat.pow_le_pow_right two_pos hm
    rw [← Finset.sum_range_add_sum_Ico _ hle, Finset.sum_eq_zero (s := Ico _ _) fun x hx => by
      simp only [mem_Ico] at hx; simp only [wPf, show ¬ x < 2 ^ mLog (kindOf es) 4 by omega,
        ↓reduceIte, zero_mul], add_zero]
    refine sum_congr rfl fun x hx => ?_
    simp only [wPf, mem_range.1 hx, ↓reduceIte, nextMsg, nLevels, lt_irrefl]

theorem dP3_same (hF : FrontLocal W₀ c₀) {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p)
    {i : ℕ} (hi : i < 5) (hp : cStart i + 1 ≤ p) : dP3 W₀ c₀ i L es = dP3 W₀ c₀ i L' es' := by
  have h1 := (tail_pos hi).2.1
  rw [dP3, dP3, c1_same hF h hi (by omega), wFold_same hF h hi (by omega), h.kind (by omega),
    nextMsg_same h hi _ hp]

theorem p3T_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {i : ℕ} (hi : i < 5)
    (κ : Kind) (hp : p3S0 i + 1 ≤ p) (d : K) : p3T κ L es i d = p3T κ L' es' i d := by
  have e : ∀ q : Fin (2 ^ 9), ((if (q : ℕ) < (lvl κ i).t then consErr κ L es i q else 0) + d) =
      ((if (q : ℕ) < (lvl κ i).t then consErr κ L' es' i q else 0) + d) := fun q => by
    by_cases hq : (q : ℕ) < (lvl κ i).t
    · simp only [hq, ↓reduceIte, consErr_same h hi κ hp hq]
    · simp only [hq, ↓reduceIte]
  unfold p3T
  simp only [e]

theorem ofFn_coord_getD (X : Log) (i v : ℕ) (hv : v < 10) :
    ((List.ofFn fun j : Fin (5 * 2) => coordAt X (p3S0 i) j).map (algebraMap F K)).getD v 0 =
      algebraMap F K (kcAt X i v) := by
  simp [List.getD_eq_getElem?_getD, hv, kcAt, p3S0]
  interval_cases v <;> rfl

open Classical in
/-- **P3.i's charge** (A.10, `hfin_seq` over the 9 coordinates of `κ_c`): at most `9/2^128`. -/
theorem hfin_P3 (hF : FrontLocal W₀ c₀) {Dk : ℕ → Log → Log → Prop} {i : ℕ} (hi : i < 5)
    (hP : Dk (27 + 5 * i) = DP2 W₀ c₀ i) (hQ : Dk (29 + 5 * i) = DP3 W₀ c₀ i)
    (L es₀ : Log) (hl : es₀.length = p3S0 i + 1) :
    condCount (DPos (Dp Dk)) L es₀ 5 [] ≤ deltaR := by
  obtain ⟨-, -, -, h4, -, -, -, -, -, -, hmem⟩ := tail_ph hi
  obtain ⟨hc, h1, h3, hsq, h5⟩ := tail_pos hi
  have hms := ms_P3 hi hP hQ
  refine hfin_seq hmem hms (fun j => if j < 9 then 1 else 0) (by decide)
    (fun L es₀ l => es₀.length = p3S0 i + 1 →
      mlDoom 9 (p3T (kindOf es₀) L es₀ i (dP3 W₀ c₀ i L es₀)) (l.map (algebraMap F K)))
    (fun L es₀ l hd => ?_) ?_ ?_ L es₀ hl
  · by_cases hlen : es₀.length = p3S0 i + 1
    · have := mlDoomF_step (p3T_size _ _ _ _ _) l (hd hlen)
      refine le_trans (card_le_card fun c hc => ?_) this
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact fun h => hc fun _ => h
    · refine le_trans (card_le_card (t := ∅) fun c hc => ?_) (by simp)
      simp only [mem_filter, mem_univ, true_and] at hc
      exact absurd (fun h' => absurd h' hlen) hc
  · intro L es₀ hd hlen
    rw [h4, hP, DP2, msD, ite_neg' (by omega)] at hd
    have hne : tbl 9 (p3T (kindOf es₀) L es₀ i (dP3 W₀ c₀ i L es₀)) ≠ 0 := by
      refine p3T_ne_zero hi ?_
      rcases hd with hd | ⟨-, hC, hw⟩
      · exact Or.inl hd
      · right
        rw [dP3, sub_ne_zero]
        convert hw using 1
        refine sum_congr rfl fun x hx => ?_
        rw [hC x (mem_range.1 hx)]
    simp only [List.map_nil]
    exact hne
  · intro L es₀ as hl' has _ hnf hD
    have hm := hD hl'
    set X := ext es₀ as
    have hS : Same L X L es₀ (p3S0 i + 1) := hl' ▸ same_of_agree L (agree_ext es₀ as)
    have hk : kindOf X = kindOf es₀ := kindOf_ext es₀ as (by omega)
    unfold finP3 at hnf
    rw [not_or, not_not] at hnf
    have hv : vNext (kindOf X) L X i (c1 c₀ i L X) = nxSum W₀ i L X := hnf.2
    have hsub := vNext_sub (kindOf X) L X i (wFold W₀ i L X) (c1 c₀ i L X)
    rw [hv, nxSum_eq W₀ hi, sub_self] at hsub
    have hmle := p3T_mle (kindOf X) L X hi (dP3 W₀ c₀ i L X)
    rw [dP3, ← hsub] at hmle
    rw [← dP3, p3T_same hS hi _ le_rfl, dP3_same hF hS hi (by omega), hk] at hmle
    refine (not_mlDoom_nine (p3T_size _ _ _ _ _) _ (by simp)).mpr ?_ hm
    refine Eq.trans (sum_congr rfl fun q _ => ?_) hmle
    rw [eqBits_congr fun v hv => ofFn_coord_getD X i v (by omega)]

/-! ## Part D: stability -/

theorem D2_congrL {R : Type*} [Field R] {b wd : ℕ} {rd : ByteArray → ℕ → R} {ch : Digest → R}
    {c0 : Log → Log → R} {nr : Kind → ℕ} {e : Expr} {T : Log → Log → Array (Array R)}
    {L L' Y : Log} (hT : T L Y = T L' Y) (hc : c0 L Y = c0 L' Y) :
    D2 b wd rd ch c0 nr e T L Y ↔ D2 b wd rd ch c0 nr e T L' Y := by
  unfold D2 Wrong2
  rw [hT, clR2_same (L' := L') (es' := Y) hc (fun _ _ => rfl)]

theorem DT_Q (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) {i : ℕ} (hi : i < 5) :
    DT W₀ c₀ (28 + 5 * i) = fun _ _ => False := by
  unfold DT
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_pos' (by omega)]

section Stab

variable (hF : FrontLocal W₀ c₀) {L L' Y : Log} {p : ℕ} (h : Same L Y L' Y p) {i : ℕ}
  (hi : i < 5)
include hF h hi

theorem D1_stab (hY : Y.length ≤ p) (hp : p1Start i + 1 ≤ p) :
    D1 W₀ c₀ i L Y ↔ D1 W₀ c₀ i L' Y := by
  have hc := (tail_pos hi).1
  have hr : p1Start i + 2 * hRnd Y i ≤ p := by unfold hRnd; omega
  unfold D1
  rw [closeP_same h hi _ hr, farL_same h hi _ (by omega),
    D2_congrL (lvT_same hF h hi (by omega)) (lvC_same hF h hi (by omega))]

theorem DCi_stab (hp : cStart i + 1 ≤ p) : DCi W₀ c₀ i L Y ↔ DCi W₀ c₀ i L' Y := by
  obtain ⟨hc, h1, h3, -, -⟩ := tail_pos hi
  unfold DCi
  rw [truthP2_same h hi _ hp, farL_same h hi _ (by omega), c1_same hF h hi (by omega),
    foldSum_same hF h hi (by omega)]

theorem finP2_stab (hp : p3S0 i + 1 ≤ p) : finP2 W₀ c₀ i L Y ↔ finP2 W₀ c₀ i L' Y := by
  obtain ⟨hc, h1, h3, h4, -⟩ := tail_pos hi
  unfold finP2
  rw [truthP3_same h hi _ hp, truthC_same h hi _ (by omega), farL_same h hi _ (by omega),
    c1_same hF h hi (by omega), foldSum_same hF h hi (by omega)]

omit h in
theorem DP2_stab (h : Same L Y L' Y p) (hY : Y.length ≤ p) (hp : cStart i + 1 ≤ p) :
    DP2 W₀ c₀ i L Y ↔ DP2 W₀ c₀ i L' Y := by
  have h4 := (tail_pos hi).2.2.2.1
  unfold DP2 msD
  split_ifs with hl
  · exact DCi_stab hF (h.take (m := cStart i + 1) hp) hi le_rfl
  · exact finP2_stab hF h hi (by omega)

theorem finP3_stab (hp : nxStart i ≤ p) : finP3 W₀ c₀ i L Y ↔ finP3 W₀ c₀ i L' Y := by
  obtain ⟨hc, h1, h3, h4, h5⟩ := tail_pos hi
  have hC : lvC c₀ (i + 1) L Y = lvC c₀ (i + 1) L' Y :=
    (chain_same hF (i + 1) (by omega) h (by rw [lvB_succ hi]; exact hp)).2
  have hN : nxSum W₀ i L Y = nxSum W₀ i L' Y := by
    rw [nxSum_eq W₀ hi, nxSum_eq W₀ hi, wFold_same hF h hi (by omega),
      wNext_same h hi _ hp, nextMsg_same h hi _ (by omega)]
  unfold finP3
  rw [hC, hN]
  by_cases h4' : i < 4
  · rw [farL_same h (show i + 1 < 5 by omega) _ (by rw [capPos_succ]; omega)]
  · simp [h4']

omit h in
theorem DP3_stab (h : Same L Y L' Y p) (hY : Y.length ≤ p) (hp : p3S0 i + 1 ≤ p) :
    DP3 W₀ c₀ i L Y ↔ DP3 W₀ c₀ i L' Y := by
  obtain ⟨-, -, -, h4, h5⟩ := tail_pos hi
  unfold DP3 msD
  split_ifs with hl
  · exact DP2_stab hF hi (h.take (m := p3S0 i + 1) hp) (by simp) (by omega)
  · exact finP3_stab hF h hi (by omega)

end Stab

theorem DPf_stab (hF : FrontLocal W₀ c₀) {L L' Y : Log} {p : ℕ} (h : Same L Y L' Y p)
    (hp : pfStart ≤ p) : DPf W₀ c₀ L Y ↔ DPf W₀ c₀ L' Y :=
  D2_congrL (tPf_same hF h hp) (lvC5_same hF h hp)

/-- **Every tail doom is stable** (`hstab`): on two logs whose words agree up to the chain's
length, once the chain has reached phase `k`. -/
theorem DT_stab (hF : FrontLocal W₀ c₀) {k : ℕ} (hk1 : 25 ≤ k) (hk2 : k ≤ 50) {L L' Y : Log}
    {p : ℕ} (h : Same L Y L' Y p) (hY : Y.length ≤ p) (hp : phStart k + 1 ≤ p) :
    DT W₀ c₀ k L Y ↔ DT W₀ c₀ k L' Y := by
  by_cases h50 : k = 50
  · subst h50; rw [DT_Pf]; exact DPf_stab hF h (by unfold pfStart; omega)
  obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 5 ∧ k = 25 + 5 * i + t :=
    ⟨(k - 25) / 5, (k - 25) % 5, Nat.mod_lt _ (by norm_num), by omega⟩
  have hi : i < 5 := by omega
  obtain ⟨-, -, -, -, -, h27, h28, h29, -⟩ := tail_ph hi
  interval_cases t
  · rw [add_zero, DT_P1 W₀ c₀ hi]; exact D1_stab hF h hi hY hp
  · rw [show 25 + 5 * i + 1 = 26 + 5 * i by ring, DT_C W₀ c₀ hi]
    exact DCi_stab hF h hi (by rw [show 25 + 5 * i + 1 = 26 + 5 * i by ring] at hp; exact hp)
  · rw [show 25 + 5 * i + 2 = 27 + 5 * i by ring, DT_P2 W₀ c₀ hi]
    rw [show 25 + 5 * i + 2 = 27 + 5 * i by ring, h27] at hp
    exact DP2_stab hF hi h hY (by omega)
  · rw [show 25 + 5 * i + 3 = 28 + 5 * i by ring, DT_Q W₀ c₀ hi]
  · rw [show 25 + 5 * i + 4 = 29 + 5 * i by ring, DT_P3 W₀ c₀ hi]
    rw [show 25 + 5 * i + 4 = 29 + 5 * i by ring, h29] at hp
    exact DP3_stab hF hi h hY (by omega)

end FR.Snd
