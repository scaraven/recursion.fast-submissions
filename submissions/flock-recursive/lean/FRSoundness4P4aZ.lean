-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Z1 … Zend; stage P4a pass 4 (P4d)):
-- a copy-port of `FRSoundnessFrZ`'s obligations to `seq4` and `CKind`.
import FRSoundness4P4aS2

/-!
# Z's obligations at `seq4` (positions 2 … 67), against T4's foundation

3.x's `FrZ` part "Positions" … "Z3 and Zend" over T4's `Same`, `Reads`, `D3`, `RejOK`,
`hfin_seq` and P4a's revision 4.1 tables (`ZLM4`, the witness `zw : Wit`). The renaming is
`kindOf → kindOfC`, `mm 6 → mC 6`, `zW_same → ZwSame`, `fsItems/phOf → fsItems4/phOf4`. Two
hypotheses are new:

* **`ZLM4.EtLocal`**: the targets read the log before position 2 (a segment's target reads its
  last block `L` off `stmt`, B-12; 3.x's targets did not read the log). **`zlm4_etLocal`**: P4a's
  `zlm4` meets it for any node maps.
* **`WitBits`**: the witness is bit-valued (3.x's `unpack_boolean` was inline); **`witBits_zW`**:
  T4's `zW` is.

The obligations: **`z_unit_pos4`** (positions), the reads (`zHolds_reads4`, `zEnd_reads4`,
`pendZ_reads4`, `z2Bad_reads4`, `zendBad_reads4`, `rejZ_reads4`, `zDooms_log4`), **`z1_hfin4`**
(`≤ deltaR` at `(2, 10)`), **`z2_habs4`**, **`z2_single4`** (`126·2^128`), **`z3_habs4`**,
**`z3_single4`** (`3·2^128`), **`zend_habs4`**, **`rejZ_ok4`** (`T4.RejOK (RejZ M)`), and
`rejOK_at4` (3.x's `rejOK_at` at `seq4`).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## The new hypotheses -/

/-- **The targets read the log before position 2** (a segment's `L` from `stmt`). -/
def ZLM4.EtLocal (M : ZLM4) : Prop := ∀ κ es es', Agree es es' 2 → M.Et κ es = M.Et κ es'

theorem zlm4_etLocal (indN : Rev4.NodeKind → Fin 9 → ℕ → F)
    (etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F) : (zlm4 indN etN).EtLocal := fun κ es es' h => by
  funext t p
  cases κ <;> simp only [zlm4, lastL_congr h le_rfl]

/-- **The witness is bit-valued.** -/
def WitBits (zw : Wit) : Prop := ∀ κ L es b, IsBitF (zw κ L es b)

theorem witBits_zW : WitBits T4.zW := fun _ _ _ _ => unpack_boolean _ _

/-! ## Positions and dimensions -/

/-- **Z's and L's positions at `seq4`** (identity below 170): Z1's ten squeezes after 2 (phase 3),
Z2 at 13–14 (4), Z3 from 15 (5), Zend at 67 (6), L1 at 68 (7), L2 from 69 (8), L3 at 97 (9), L3β
at 98 (10), S1 from 99 (11). -/
theorem z_unit_pos4 :
    (2, 10) ∈ fsRanges4 ∧ phOf4 2 = 2 ∧ phOf4 3 = 3 ∧ phOf4 12 = 3 ∧ phOf4 13 = 4 ∧
    phOf4 14 = 4 ∧ phOf4 15 = 5 ∧ phOf4 66 = 5 ∧ phOf4 67 = 6 ∧ phOf4 68 = 7 ∧ phOf4 69 = 8 ∧
    phOf4 96 = 8 ∧ phOf4 97 = 9 ∧ phOf4 98 = 10 ∧ phOf4 99 = 11 := by
  refine ⟨by rw [fsRanges4_eq]; simp, ?_⟩
  have hph : ∀ q, phOf4 q = (fsStarts4.filter (· ≤ q)).length - 1 := fun _ => rfl
  simp only [hph, fsStarts4_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mC6_eq4 (κ : CKind) : mC 6 κ = 7 + (κ.m - 13) := by
  unfold mC; rcases κ.m_mem with h | h | h <;> omega

theorem m13_le4 (κ : CKind) : κ.m - 13 ≤ 19 := by rcases κ.m_mem with h | h | h <;> omega

theorem mC6_le (κ : CKind) : mC 6 κ ≤ 26 := by
  unfold mC; rcases κ.m_mem with h | h | h <;> omega

/-- A squeeze's entry is one more `Same` entry (T4's `same_append`). -/
theorem same_ext1_4 (L es : Log) (a : Digest) : T4.Same L (ext1 es a) L es es.length :=
  T4.same_append L es _

/-- A check that holds from position `p + 1` on and reads the entries before it is a `T4.RejOK`
when `p` is not a `seq4` squeeze (3.x's `rejOK_at`). -/
theorem rejOK_at4 {p : ℕ} {P : Log → Log → Prop} (hP : T4.Reads (p + 1) P)
    (hp : fsItems4[p]? ≠ some .squeeze) : T4.RejOK fun L es => p + 1 ≤ es.length ∧ P L es where
  mono L es x h := ⟨by simp; omega, (hP.append L es [x] h.1).mpr h.2⟩
  sq L es x hit := by
    by_cases hle : p + 1 ≤ es.length
    · exact and_congr (by simp; omega) (hP.append L es [x] hle)
    · have hne : es.length ≠ p := fun he => hp (he ▸ hit)
      exact ⟨fun h => absurd h.1 (by simp; omega), fun h => absurd h.1 hle⟩
  stab L i hb hci X hX := by
    by_cases hle : p + 1 ≤ X.length
    · exact and_congr Iff.rfl (hP.stab hb hci hX hle)
    · exact ⟨fun h => absurd h.1 hle, fun h => absurd h.1 hle⟩

/-! ## Reads (Z1) -/

section Reads
variable {M : ZLM4} {zw : Wit} {L es L' es' : Log} {p : ℕ}

theorem zrL_agree4 (h : Agree es es' 13) : zrL es = zrL es' := by
  have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.mono (by norm_num))
  have hm := m13_le4 (kindOfC es)
  unfold zrL
  rw [← hk]
  refine congrArg _ (List.map_congr_left fun j hj => ?_)
  simp only [List.mem_range] at hj
  unfold coordAt
  exact fAt_congr h (by omega) _

theorem zBk_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (κ : CKind) :
    zBk zw κ L es = zBk zw κ L' es' := by
  funext t k; simp only [zBk, hz κ L es L' es' p h hp]

theorem aZ_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (ℓ : ℕ) (κ : CKind) :
    aZ M zw ℓ κ L es = aZ M zw ℓ κ L' es' := by
  funext σ u; simp only [aZ, mvZ, zBk_same4 hz h hp κ]

theorem bZ_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (ℓ : ℕ) (κ : CKind) :
    bZ M zw ℓ κ L es = bZ M zw ℓ κ L' es' := by
  funext σ u; simp only [bZ, mvZ, zBk_same4 hz h hp κ]

theorem zZ_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (ℓ : ℕ) (κ : CKind) :
    zZ zw ℓ κ L es = zZ zw ℓ κ L' es' := by
  funext σ u; simp only [zZ, zBk_same4 hz h hp κ]

theorem eZ_agree4 (hE : M.EtLocal) (h : Agree es es' p) (hp : 2 ≤ p) (ℓ : ℕ) (κ : CKind) :
    eZ M ℓ κ es = eZ M ℓ κ es' := by
  funext σ u; simp only [eZ, hE κ es es' (h.mono hp)]

theorem zHolds_same4 (hz : ZwSame zw) (hE : M.EtLocal) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) :
    ZHolds M zw L es ↔ ZHolds M zw L' es' := by
  have hk := h.kind (by omega)
  unfold ZHolds
  rw [hk, aZ_same4 hz h hp, bZ_same4 hz h hp, zZ_same4 hz h hp, eZ_agree4 hE h.1 (by omega)]

theorem zHolds_reads4 (hz : ZwSame zw) (hE : M.EtLocal) : T4.Reads 3 (ZHolds M zw) :=
  fun _ _ _ _ _ _ h => zHolds_same4 hz hE h le_rfl

/-- `ZEnd` from a nonzero residual at Z1's point read off a longer chain. -/
theorem zEnd_of4 (hz : ZwSame zw) (hE : M.EtLocal) (h : T4.Same L es L' es' 3) {i : Fin 64}
    (hne : mle (zres M zw L' es' i) (ptOf (mC 6 (kindOfC es')) (List.ofFn pinnedRho ++
      (List.range ((kindOfC es').m - 13)).map (coordAt es 2))) ≠ 0) : ZEnd M zw L es := by
  have hk := h.kind (by norm_num)
  refine ⟨i, ?_⟩
  unfold zres zrL
  rw [hk, aZ_same4 hz h le_rfl, bZ_same4 hz h le_rfl, zZ_same4 hz h le_rfl,
    eZ_agree4 hE h.1 (by norm_num)]
  exact hne

theorem zEnd_reads4 (hz : ZwSame zw) (hE : M.EtLocal) : T4.Reads 13 (ZEnd M zw) :=
  fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  unfold ZEnd zres
  rw [hk, zrL_agree4 h.1, aZ_same4 hz h (by norm_num), bZ_same4 hz h (by norm_num),
    zZ_same4 hz h (by norm_num), eZ_agree4 hE h.1 (by norm_num)]

end Reads

/-! ## Bits -/

section Bits
variable {M : ZLM4} {zw : Wit}

theorem mvZ_bit4 (hM : M.Bits) (hb : WitBits zw) {A : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F}
    (hA : ∀ j p k, IsBitF (A j p k)) (κ : CKind) (L es : Log) (t : ℕ) (p : Fin (2 ^ 14)) :
    IsBitF (mvZ M zw A κ L es t p) :=
  sum_bitF _ _ fun j _ => isBit_mul (hM.2.2.1 κ j t)
    (sum_bitF _ _ fun k _ => isBit_mul (hA j p k) (hb _ _ _ _))

theorem zres_bit4 (hM : M.Bits) (hb : WitBits zw) (L es : Log) (i : Fin 64)
    (u : Fin (2 ^ mC 6 (kindOfC es))) : IsBitF (zres M zw L es i u) :=
  bzRes_bit (fun _ _ => mvZ_bit4 hM hb hM.1 _ L es _ _) (fun _ _ => mvZ_bit4 hM hb hM.2.1 _ L es _ _)
    (fun _ _ => hb _ _ _ _) (fun _ _ => hM.2.2.2 _ _ _ _) i u

end Bits

/-! ## Z1 (`hfin`, positions 3 … 12) -/

/-- Z1's doom on the coordinate list: the background, or a pinned-fixed residual slice whose
extension is nonzero at the coordinates bound so far (3.x's `Z1Doom`). -/
def Z1Doom4 (M : ZLM4) (zw : Wit) (Bg : Log → Log → Prop) (L es₀ : Log) (l : List F) : Prop :=
  Bg L es₀ ∨ ∃ i : Fin 64, ∃ t : Array F,
    t.size = 2 ^ ((kindOfC es₀).m - 13) ∧ mlDoom ((kindOfC es₀).m - 13) t l ∧
    ∀ cs : List F, cs.length = (kindOfC es₀).m - 13 →
      mle (tbl ((kindOfC es₀).m - 13) t) (ptOf ((kindOfC es₀).m - 13) cs) =
        mle (zres M zw L es₀ i) (ptOf (mC 6 (kindOfC es₀)) (List.ofFn pinnedRho ++ cs))

open Classical in
/-- **Z1's charge at `seq4`** (A.10 Z1, `≤ 19/2^128 ≤ deltaR`): with the entry's doom
`Bg ∨ ¬ ZHolds` and a final doom containing `Bg ∨ ZEnd`, the ten squeezes escape with conditional
probability at most `deltaR`. -/
theorem z1_hfin4 {M : ZLM4} {zw : Wit} (hM : M.Bits) (hb : WitBits zw) (hz : ZwSame zw)
    (hE : M.EtLocal) {Dk : ℕ → Log → Log → Prop} {Bg : Log → Log → Prop}
    (hBg : T4.Reads 3 Bg) (hprev : ∀ L es, Dk (phOf4 2) L es → Bg L es ∨ ¬ ZHolds M zw L es)
    {fin : Log → Log → Prop} (hfin : Dk (phOf4 3) = msD (Dk (phOf4 2)) fin 2 10)
    (hfinI : ∀ L es, Bg L es ∨ ZEnd M zw L es → fin L es)
    (L es₀ : Log) (hl : es₀.length = 3) : condCount (DPos (T4.Dp Dk)) L es₀ 10 [] ≤ deltaR := by
  have hsum : ∑ i ∈ range (10 * 2), (if i < 19 then 1 else 0) ≤ 239 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  refine T4.hfin_seq z_unit_pos4.1 hfin (fun i => if i < 19 then 1 else 0) hsum (Z1Doom4 M zw Bg)
    (fun L es₀ l hd => ?_) (fun L es₀ hd => ?_) (fun L es₀ as hl' has hd hnf => ?_) L es₀ hl
  · rcases hd with hb | ⟨i, t, hts, hd, hcs⟩
    · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun c _ h =>
        h (.inl hb))).trans_le (Nat.zero_le _)
    refine le_trans (card_le_card fun c hc => ?_) ((mlDoom_step hts l hd).trans ?_)
    · simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact fun h => hc (.inr ⟨i, t, hts, h, hcs⟩)
    · have := m13_le4 (kindOfC es₀); split_ifs <;> omega
  · rcases hprev L es₀ hd with hb | hzh
    · exact .inl hb
    obtain ⟨i, hi⟩ := bz_start hzh
    obtain ⟨t, hts, ht0, hcs⟩ := pinned_table (mC6_eq4 (kindOfC es₀)) (zres M zw L es₀ i)
      (zres_bit4 hM hb L es₀ i) hi
    exact .inr ⟨i, t, hts, mlDoom_nil ht0, hcs⟩
  · obtain ⟨ys, hy⟩ := T4.ext_eq_append es₀ as
    have hS : T4.Same L (ext es₀ as) L es₀ 3 := by
      rw [hy]; exact (T4.same_append L es₀ ys).mono (by omega)
    rintro (hbg | ⟨i, t, hts, hd, hcs⟩)
    · exact hnf (hfinI _ _ (.inl ((hBg.ext L es₀ as (by omega)).mpr hbg)))
    have hk := m13_le4 (kindOfC es₀)
    have hlen : (kindOfC es₀).m - 13 ≤ (List.ofFn fun j : Fin (10 * 2) =>
        coordAt (ext es₀ as) 2 j).length := by simp; omega
    rw [mlDoom_full t hts _ hlen, hcs _ (by simp; omega),
      take_ofFn_coord (ext es₀ as) (by omega : (kindOfC es₀).m - 13 ≤ 10 * 2)] at hd
    exact hnf (hfinI _ _ (.inr (zEnd_of4 hz hE hS hd)))

/-! ## Reads of Z2 … Zend -/

section Reads2
variable {M : ZLM4} {zw : Wit} {L es L' es' X : Log} {p : ℕ}

theorem z2_agree14_4 (h : Agree es es' 14) :
    kindOfC es = kindOfC es' ∧ zrL es = zrL es' ∧ pzL es = pzL es' ∧ pabL es = pabL es' := by
  refine ⟨kindOfC_congr (h.mono (by norm_num)), zrL_agree4 (h.mono (by norm_num)), ?_, ?_⟩ <;>
  · funext k; simp only [pzL, pabL, msgAt_congr h (show 13 < 14 by norm_num)]

theorem z2_agree4 (h : Agree es es' 15) :
    kindOfC es = kindOfC es' ∧ zrL es = zrL es' ∧ lamL es = lamL es' ∧ pzL es = pzL es' ∧
      pabL es = pabL es' := by
  obtain ⟨h1, h2, h3, h4⟩ := z2_agree14_4 (h.mono (by norm_num))
  exact ⟨h1, h2, fAt_congr h (by norm_num) 0, h3, h4⟩

theorem peL_agree4 (hE : M.EtLocal) (h : Agree es es' 14) : peL M es = peL M es' := by
  obtain ⟨hk, hz, -, -⟩ := z2_agree14_4 h
  unfold peL; rw [hk, hz, eZ_agree4 hE h (by norm_num)]

theorem c0Z_agree4 (hE : M.EtLocal) (h : Agree es es' 15) : c0Z M es = c0Z M es' := by
  obtain ⟨-, -, hl, hp, hq⟩ := z2_agree4 h
  unfold c0Z; rw [hl, hp, hq, peL_agree4 hE (h.mono (by norm_num))]

theorem pzT_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 13 ≤ p) :
    pzT zw L es = pzT zw L' es' := by
  have hk := h.kind (by omega)
  unfold pzT; rw [hk, zrL_agree4 (h.1.mono hp), zZ_same4 hz h (by omega)]

theorem pabT_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 13 ≤ p) :
    pabT M zw L es = pabT M zw L' es' := by
  have hk := h.kind (by omega)
  unfold pabT; rw [hk, zrL_agree4 (h.1.mono hp), aZ_same4 hz h (by omega), bZ_same4 hz h (by omega)]

theorem pendZ_reads4 (hz : ZwSame zw) : T4.Reads 15 (PendZ zw) := fun L es L' es' h1 h2 h => by
  have hl := (z2_agree4 h.1).2.2.1
  rw [PendZ, PendZ, pzStar_agree h.1, pzT_same4 hz h (by norm_num), hl]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem z2Bad_reads4 (hz : ZwSame zw) (hE : M.EtLocal) : T4.Reads 15 (Z2Bad M zw) :=
  fun L es L' es' h1 h2 h => by
  have hl := (z2_agree4 h.1).2.2.1
  unfold Z2Bad
  rw [c0Z_agree4 hE h.1, pabT_same4 hz h (by norm_num), hl, pendZ_reads4 hz L es L' es' h1 h2 h]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem TZ_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 15 ≤ p) :
    TZ M zw L es = TZ M zw L' es' := by
  obtain ⟨hk, hzr, hl, -, -⟩ := z2_agree4 (h.1.mono hp)
  unfold TZ; rw [hk, hzr, hl, aZ_same4 hz h (by omega), bZ_same4 hz h (by omega)]

theorem TZ_local4 (hz : ZwSame zw) (hE : M.EtLocal) :
    TruthLocal 15 (fun _ es => c0Z M es) (TZ M zw) := fun L _ _ h =>
  ⟨TZ_same4 hz (T4.same_of_agree L h) le_rfl, c0Z_agree4 hE h⟩

theorem TZ_size4 (L es : Log) : ∀ t ∈ TZ M zw L es, t.size = 2 ^ mC 6 (kindOfC es) :=
  bz_sizes _ _ _ _

/-- Z's dooms read the log only through the level-0 word: on one chain, two logs whose words
agree give the same dooms (`hstab`). -/
theorem zDooms_log4 (hz : ZwSame zw) (h : T4.Same L X L' X p) (hp : 3 ≤ p) :
    (ZEnd M zw L X ↔ ZEnd M zw L' X) ∧ (Z2D M zw L X ↔ Z2D M zw L' X) ∧
      (D3Z M zw L X ↔ D3Z M zw L' X) ∧ (ZendBad M zw L X ↔ ZendBad M zw L' X) ∧
      (PendZ zw L X ↔ PendZ zw L' X) ∧ (ZHolds M zw L X ↔ ZHolds M zw L' X) := by
  have hzz := zZ_same4 hz h hp; have ha := aZ_same4 (M := M) hz h hp
  have hb := bZ_same4 (M := M) hz h hp
  have h1 : ZEnd M zw L X ↔ ZEnd M zw L' X := by unfold ZEnd zres; rw [ha, hb, hzz]
  have h2 : PendZ zw L X ↔ PendZ zw L' X := by unfold PendZ pzT; rw [hzz]
  have h3 : Z2Bad M zw L X ↔ Z2Bad M zw L' X := by unfold Z2Bad pabT; rw [ha, hb, h2]
  refine ⟨h1, ?_, ?_, ?_, h2, ?_⟩
  · unfold Z2D; split_ifs; exacts [h1, h3]
  · exact (T4.D3_log_congr (b := 15) (c0 := fun _ es => c0Z M es) (nr := mC 6) (e := bzExpr)
      (T := TZ M zw) (by unfold TZ; rw [ha, hb]) rfl).symm
  · unfold ZendBad aStar bStar; rw [ha, hb]
  · unfold ZHolds; rw [ha, hb, hzz]

theorem rZ_agree4 (h : Agree es es' 67) : rZ es = rZ es' := by
  have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.mono (by norm_num))
  unfold rZ rchs; rw [hk]
  refine List.map_congr_left fun j hj => ?_
  have := mC6_le (kindOfC es'); simp only [List.mem_range] at hj
  exact rch_congr h (by omega)

theorem zendBad_reads4 (hz : ZwSame zw) : T4.Reads 68 (ZendBad M zw) :=
  fun L es L' es' h1 h2 h => by
  obtain ⟨hk, -, hl, -, -⟩ := z2_agree4 (h.1.mono (by norm_num))
  have hr := rZ_agree4 (h.1.mono (by norm_num))
  have hv : ∀ j, vZ es j = vZ es' j := fun j => by
    simp only [vZ, msgAt_congr h.1 (show 67 < 68 by norm_num)]
  unfold ZendBad aStar bStar
  rw [hk, hl, hr, hv, hv, aZ_same4 hz h (by norm_num), bZ_same4 hz h (by norm_num)]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem rejZ_reads4 (hE : M.EtLocal) : T4.Reads 68 fun L es =>
    clR 15 (fun _ es => c0Z M es) L es (mC 6 (kindOfC es)) ≠
      eq (ptOf (mC 6 (kindOfC es)) (zrL es)) (ptOf (mC 6 (kindOfC es)) (rZ es)) *
        (vZ es 0 * vZ es 1) :=
  fun L es L' es' h1 h2 h => by
  obtain ⟨hk, hzr, -, -, -⟩ := z2_agree4 (h.1.mono (by norm_num))
  have hr := rZ_agree4 (h.1.mono (by norm_num))
  have hv : ∀ j, vZ es j = vZ es' j := fun j => by
    simp only [vZ, msgAt_congr h.1 (show 67 < 68 by norm_num)]
  have hc : clR 15 (fun _ es => c0Z M es) L es (mC 6 (kindOfC es)) =
      clR 15 (fun _ es => c0Z M es) L' es' (mC 6 (kindOfC es)) := by
    rw [clR_log_congr (L := L) (L' := L') rfl]
    have := mC6_le (kindOfC es)
    exact clR_congr (c0 := fun _ es => c0Z M es) (c0Z_agree4 hE (h.1.mono (by norm_num)))
      (h.1.mono (by omega))
  beta_reduce
  rw [hc, hk, hzr, hr, hv, hv]

end Reads2

/-! ## Z2 (`habs` at 13, `hsingle` at 14) -/

section Z2
variable {M : ZLM4} {zw : Wit}

/-- **Into Z2** (`habs` at 13): Z1's final doom carries over Z2's absorb. -/
theorem z2_habs4 (hz : ZwSame zw) (hE : M.EtLocal) {L es : Log} (x : ByteArray × Digest)
    (hl : es.length = 13) (hzE : ZEnd M zw L es) : Z2D M zw L (es ++ [x]) := by
  have : (es ++ [x]).length ≤ 14 := by simp; omega
  rw [Z2D, if_pos this]; exact ((zEnd_reads4 hz hE).append L es [x] (by omega)).mpr hzE

theorem z2_ext1_4 (hz : ZwSame zw) (hE : M.EtLocal) (L es : Log) (a : Digest) (hl : es.length = 14) :
    c0Z M (ext1 es a) = interpolateAt node127 (z2Vals (pzL es) (pabL es) (peL M es)) (chF a 0) ∧
    pzStar (ext1 es a) = interpolateAt lNode (pzL es) (chF a 0) ∧
    pabT M zw L (ext1 es a) = pabT M zw L es ∧ pzT zw L (ext1 es a) = pzT zw L es ∧
    lamL (ext1 es a) = chF a 0 := by
  have hS := same_ext1_4 L es a
  rw [hl] at hS
  obtain ⟨-, -, hp, hq⟩ := z2_agree14_4 (hS.1 : Agree (ext1 es a) es 14)
  have hlam : lamL (ext1 es a) = chF a 0 := by
    have := entAt_ext1 es a; rw [hl] at this
    simp only [lamL, fAt, ansAt, this]
  refine ⟨?_, ?_, pabT_same4 hz hS (by norm_num), pzT_same4 hz hS (by norm_num), hlam⟩
  · unfold c0Z; rw [hp, hq, hlam, peL_agree4 hE hS.1]
  · unfold pzStar; rw [hp, hlam]

open Classical in
/-- **Z2's squeeze** (A.10 Z2, `126·2^128`; `skip_pair_bad_le`). -/
theorem z2_single4 (hz : ZwSame zw) (hE : M.EtLocal) (L es : Log) (hl : es.length = 14) :
    (univ.filter fun a => Z2D M zw L es ∧ ¬ Z2D M zw L (ext1 es a)).card ≤ 126 * 2 ^ 128 := by
  have hle : es.length ≤ 14 := by omega
  have hgt : ∀ a, ¬ (ext1 es a).length ≤ 14 := fun a => by rw [length_ext1]; omega
  by_cases hzE : ZEnd M zw L es
  swap
  · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ h =>
      hzE (by rw [Z2D, if_pos hle] at h; exact h.1))).trans_le (Nat.zero_le _)
  obtain ⟨i, hi⟩ := hzE
  have hb : ∃ b : Fin 64, (pabT M zw L es).eval (skipNode (Fin.castLE (by norm_num) b)) ≠
      (pzT zw L es).eval (skipNode (Fin.castLE (by norm_num) b)) + peL M es b := ⟨i, bz_end hi⟩
  have hcnt := skip_pair_bad_le (pzL es) (pabL es) (peL M es) (pabT M zw L es) (pzT zw L es)
    (pabPoly_natDegree _ _ _) (pzPoly_natDegree _ _) (.inl hb)
  refine single_F_le' _ _ hcnt fun a ⟨_, hn⟩ => ?_
  simp only [Z2D, hgt a, if_false] at hn
  obtain ⟨h1, h2, h3, h4, h5⟩ := z2_ext1_4 hz hE L es a hl
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_contra hc
  refine hn ⟨by rw [length_ext1]; omega, ?_⟩
  rw [h1, h3, h5, PendZ, h2, h4, h5]
  by_cases hab : interpolateAt node127 (z2Vals (pzL es) (pabL es) (peL M es)) (chF a 0) =
    (pabT M zw L es).eval (chF a 0)
  · exact .inr ⟨by rw [length_ext1]; omega, fun h => hc ⟨hab, h⟩⟩
  · exact .inl hab

end Z2

/-! ## Z3 (`habs` at 15, `hsingle` per round) and Zend (`habs` at 67) -/

section Z3
variable {M : ZLM4} {zw : Wit}

/-- **Into Z3** (`habs` at 15): a false initial claim `P^{ab}*(λ)` is Z3's round doom; otherwise
the c-claim is pending false. -/
theorem z3_habs4 (hz : ZwSame zw) (hE : M.EtLocal) {L es : Log} (x : ByteArray × Digest)
    (hl : es.length = 15) (hzb : Z2Bad M zw L es) :
    D3Z M zw L (es ++ [x]) ∨ PendZ zw L (es ++ [x]) := by
  have hS := T4.same_append L es [x]
  rw [hl] at hS
  rcases hzb.2 with hc | hp
  · refine .inl ⟨by simp; omega, ?_⟩
    have ha0 : T4.ans3 15 (mC 6) (es ++ [x]) = 0 := by
      simp only [T4.ans3, List.length_append, List.length_singleton, hl]; simp
    rw [ha0]
    simp only [T4.Wrong3, clR, rchs, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
    rw [TZ_same4 hz hS le_rfl, c0Z_agree4 (M := M) hE hS.1, hS.kind (by norm_num)]
    unfold TZ; rw [bz_trueSum]; exact hc
  · exact .inr (((pendZ_reads4 hz).append L es [x] (by omega)).mpr hp)

open Classical in
/-- **Z3's squeezes** (A.10 Z3, `3·2^128`, T4's `D3_single`). -/
theorem z3_single4 (hz : ZwSame zw) (hE : M.EtLocal) (L es : Log) :
    (univ.filter fun a => D3Z M zw L es ∧ ¬ D3Z M zw L (ext1 es a)).card ≤ 3 * 2 ^ 128 :=
  T4.D3_single (by norm_num) (TZ_local4 hz hE) bzExpr_deg (TZ_size4 (M := M)) L es

/-- **At Zend's absorb** (67): a false final Z3 claim gives `RejZ` or a wrong pair `(â, b̂)`. -/
theorem zend_habs4 (hz : ZwSame zw) (hE : M.EtLocal) {L es : Log} (x : ByteArray × Digest)
    (hl : es.length = 67) (hd : D3Z M zw L es) :
    RejZ M L (es ++ [x]) ∨ ZendBad M zw L (es ++ [x]) := by
  have hS := T4.same_append L es [x]
  rw [hl] at hS
  have hk : kindOfC (es ++ [x]) = kindOfC es := hS.kind (by norm_num)
  have hm := mC6_le (kindOfC es)
  obtain ⟨-, hw⟩ := hd
  have ha : T4.ans3 15 (mC 6) es = mC 6 (kindOfC es) := by
    simp only [T4.ans3, hl]; omega
  rw [ha] at hw
  unfold T4.Wrong3 at hw
  rw [Nat.sub_self] at hw
  have hfin : trueSum bzExpr (bindAll (TZ M zw L es) (rchs 15 es (mC 6 (kindOfC es)))) 0 =
      eq (ptOf (mC 6 (kindOfC es)) (zrL es)) (ptOf (mC 6 (kindOfC es)) (rZ es)) *
        (aStar M zw L es * bStar M zw L es) :=
    bz_final _ _ (by simp [rchs]) _ _ _
  rw [hfin] at hw
  have hag : Agree (es ++ [x]) es 67 := hS.1
  obtain ⟨-, hzr, hlam, -, -⟩ := z2_agree4 (hag.mono (by norm_num))
  have hr : rZ (es ++ [x]) = rZ es := rZ_agree4 hag
  have hc : clR 15 (fun _ es => c0Z M es) L (es ++ [x]) (mC 6 (kindOfC es)) =
      clR 15 (fun _ es => c0Z M es) L es (mC 6 (kindOfC es)) :=
    clR_congr (c0Z_agree4 hE (hag.mono (by norm_num))) (hag.mono (by omega))
  have haS : aStar M zw L (es ++ [x]) = aStar M zw L es ∧
      bStar M zw L (es ++ [x]) = bStar M zw L es := by
    unfold aStar bStar
    rw [hk, hlam, hr, aZ_same4 hz hS (by norm_num), bZ_same4 hz hS (by norm_num)]
    exact ⟨rfl, rfl⟩
  by_cases hrej : RejZ M L (es ++ [x])
  · exact .inl hrej
  refine .inr ⟨by simp; omega, ?_⟩
  have hchk : clR 15 (fun _ es => c0Z M es) L es (mC 6 (kindOfC es)) =
      eq (ptOf (mC 6 (kindOfC es)) (zrL es)) (ptOf (mC 6 (kindOfC es)) (rZ es)) *
        (vZ (es ++ [x]) 0 * vZ (es ++ [x]) 1) := by
    by_contra hne
    exact hrej ⟨by simp; omega, by rw [hk, hzr, hr, hc]; exact hne⟩
  rw [haS.1, haS.2]
  exact bz_triple_wrong hw hchk

/-- **`relZ`'s first conjunct is a `T4.RejOK`** (Zend's absorb, 67, is not a squeeze). -/
theorem rejZ_ok4 (hE : M.EtLocal) : T4.RejOK (RejZ M) :=
  rejOK_at4 (p := 67) (rejZ_reads4 hE) p4a_abs.1

end Z3

end FR.Snd.P4a
