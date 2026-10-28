-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows L1 … L3β; stage P4a pass 4 (P4d)):
-- a copy-port of `FRSoundnessFrL`'s and `FRSoundnessFrLN`'s obligations to `seq4` and `CKind`.
import FRSoundness4P4aZ

/-!
# L's obligations at `seq4` (positions 68 … 98), against T4's foundation

3.x's `FrL` (reads, `l1_single`, `l2_habs`, `l2_single`, `rejL2_ok`, `l3_habs`, `l3b_single`), the
node half of `FrLN` that does not read the node maps (`L3BadN`, `PendLcN`, `l3N_habs`,
`l3bN_single`) and `FrZM`'s `rejLc2_ok`, over T4's `Same`, `Reads`, `D2`, `RejOK` and P4a's
revision 4.1 tables (renaming as in `FRSoundness4P4aZ`).

* Zend's pair in the lincheck's form: **`aStar_eq4`**, **`bStar_eq4`** (3.x's `aStar_bridge`).
* Reads: `lin_agree4`, `aLin_same4`, `l1Bad_reads4`, `TL_same4`, **`TL_local4`**, `zfL_same4`,
  `l3Bad_reads4`, `pendLc_reads4`, `pLc_reads4`, `l3BadN_reads4`, `pendLcN_reads4`, `lDooms_log4`.
* **`l1_single4`** (`1·2^128`), **`l2_habs4`**, **`l2_single4`** (`2·2^128`), **`rejL2_ok4`**,
  **`l3_habs4`** (a segment), **`l3N_habs4`** (a node), **`l3b_single4`** and **`l3bN_single4`**
  (L3β, `7·2^128`), **`rejLc2_ok4`**, **`rejLcN_ok4`**.
* The node's L3 doom **`L3BadN`** and pending batch **`PendLcN`** (`tNL`: the true values of the
  eight non-`chain` kinds). Binding `PendLcN` to RS claim 2 needs the node's kind factor (S-E's
  node maps), so it stays with the node half.
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

noncomputable section

/-! ## Zend's pair in the lincheck's form -/

section Bridge
variable (M : ZLM4) (zw : Wit)

theorem aStar_eq4 (L es : Log) : aStar M zw L es = aLin M zw L es :=
  aStar_bridge (mC6_q _) M.Ak (M.Ind (kindOfC es)) (zw (kindOfC es) L es) _ _

theorem bStar_eq4 (L es : Log) : bStar M zw L es = bLin M zw L es :=
  aStar_bridge (mC6_q _) M.Bk (M.Ind (kindOfC es)) (zw (kindOfC es) L es) _ _

end Bridge

/-! ## The node's L3 and L3β dooms (generic in the matrices) -/

section NodeDooms
variable (M : ZLM4) (zw : Wit)

/-- **L3's doom on a node**: some masked value is not its kind's true value. -/
def L3BadN (L es : Log) : Prop :=
  98 ≤ es.length ∧ (kindOfC es).isNode = true ∧ ∃ j, vM (kindOfC es) es j ≠ zfL M zw L es j

/-- A node's batch's true values: the eight non-`chain` kinds'. -/
def tNL (L es : Log) (i : Fin 8) : F := zfL M zw L es i.succ

/-- **L3β's doom on a node**: `v_β` is not the true batch `Σ_i β^i z̄̃_{i+1}(r_k)`. -/
def PendLcN (L es : Log) : Prop :=
  99 ≤ es.length ∧ (kindOfC es).isNode = true ∧
    vBetaL es ≠ ∑ i : Fin 8, fAt es 98 0 ^ i.val * tNL M zw L es i

end NodeDooms

/-! ## Reads -/

section Reads
variable {M : ZLM4} {zw : Wit} {L es L' es' X : Log} {p : ℕ}

theorem lin_agree4 (h : Agree es es' 69) :
    kindOfC es = kindOfC es' ∧ lamL es = lamL es' ∧ rZ es = rZ es' ∧ alL es = alL es' ∧
      vZ es 0 = vZ es' 0 ∧ vZ es 1 = vZ es' 1 := by
  refine ⟨kindOfC_congr (h.mono (by norm_num)), fAt_congr h (by norm_num) 0,
    rZ_agree4 (h.mono (by norm_num)), fAt_congr h (by norm_num) 0, ?_, ?_⟩ <;>
  simp only [vZ, msgAt_congr h (show 67 < 69 by norm_num)]

theorem zN_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (κ : CKind) :
    zN zw κ L es = zN zw κ L' es' := by
  funext q b; simp only [zN, hz κ L es L' es' p h hp]

theorem aLin_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 67 ≤ p) :
    aLin M zw L es = aLin M zw L' es' ∧ bLin M zw L es = bLin M zw L' es' := by
  have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.1.mono (by omega))
  have hl : lamL es = lamL es' := fAt_congr (h.1.mono hp) (by norm_num) 0
  have hr := rZ_agree4 (h.1.mono hp)
  unfold aLin bLin rbLc rwL rhiL
  rw [zN_same4 hz h (by omega), hk, hl, hr]; exact ⟨rfl, rfl⟩

theorem l1Bad_reads4 (hz : ZwSame zw) : T4.Reads 69 (L1Bad M zw) := fun L es L' es' h1 h2 h => by
  obtain ⟨-, -, -, ha, h0, h1'⟩ := lin_agree4 h.1
  obtain ⟨e1, e2⟩ := aLin_same4 (M := M) hz h (by norm_num)
  unfold L1Bad; rw [ha, h0, h1', e1, e2]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem TL_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 69 ≤ p) :
    TL M zw L es = TL M zw L' es' := by
  obtain ⟨hk, hl, hr, ha, -, -⟩ := lin_agree4 (h.1.mono hp)
  unfold TL rbLc rwL rhiL
  rw [zN_same4 hz h (by omega), hk, hl, hr, ha]

theorem TL_local4 (hz : ZwSame zw) : TruthLocal2 69 (fun _ es => c0L es) (TL M zw) :=
  fun L _ _ h => ⟨TL_same4 hz (T4.same_of_agree L h) le_rfl, c0L_agree h⟩

theorem TL_size4 (L es : Log) : ∀ t ∈ TL M zw L es, t.size = 2 ^ (fun _ => 14) (kindOfC es) :=
  kindTables_size _ _

theorem rkL_agree4 (h : Agree es es' p) (hp : 97 ≤ p) : rkL es = rkL es' := by
  unfold rkL rchs; exact List.map_congr_left fun j hj => by
    simp only [List.mem_range] at hj; exact rch_congr h (by omega)

theorem zfL_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 97 ≤ p) :
    zfL M zw L es = zfL M zw L' es' := by
  obtain ⟨hk, -, hr, -, -, -⟩ := lin_agree4 (h.1.mono (by omega))
  unfold zfL rbLc; rw [zN_same4 hz h (by omega), hk, hr, rkL_agree4 h.1 hp]

theorem vM_agree4 (h : Agree es es' 98) : vM (kindOfC es) es = vM (kindOfC es') es' := by
  have hk := kindOfC_congr (h.mono (by norm_num))
  funext j; simp only [vM, vL, msgAt_congr h (show 97 < 98 by norm_num), hk]

theorem l3Bad_reads4 (hz : ZwSame zw) : T4.Reads 98 (L3Bad M zw) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  unfold L3Bad; rw [vM_agree4 h.1, zfL_same4 hz h (by norm_num), hk]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem l3BadN_reads4 (hz : ZwSame zw) : T4.Reads 98 (L3BadN M zw) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  unfold L3BadN; rw [vM_agree4 h.1, zfL_same4 hz h (by norm_num), hk]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem vBetaL_agree4 (h : Agree es es' 99) : vBetaL es = vBetaL es' ∧ fAt es 98 0 = fAt es' 98 0 :=
  ⟨by simp only [vBetaL, fAt_congr h (show 98 < 99 by norm_num),
    msgAt_congr h (show 97 < 99 by norm_num)], fAt_congr h (show 98 < 99 by norm_num) 0⟩

theorem pendLc_reads4 (hz : ZwSame zw) : T4.Reads 99 (PendLc M zw) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  obtain ⟨hb, hf⟩ := vBetaL_agree4 h.1
  have ht : tL M zw L es = tL M zw L' es' := by
    funext i; simp only [tL, zfL_same4 hz h (by norm_num)]
  unfold PendLc; rw [hb, ht, hk, hf]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem pendLcN_reads4 (hz : ZwSame zw) : T4.Reads 99 (PendLcN M zw) :=
  fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  obtain ⟨hb, hf⟩ := vBetaL_agree4 h.1
  have ht : tNL M zw L es = tNL M zw L' es' := by
    funext i; simp only [tNL, zfL_same4 hz h (by norm_num)]
  unfold PendLcN; rw [hb, ht, hk, hf]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem pLc_reads4 (b : Bool) : T4.Reads 98 (PLc M b) := fun L es L' es' _ _ hS => by
  obtain ⟨hk, hl, hr, ha, -, -⟩ := lin_agree4 (hS.1.mono (by norm_num))
  have hc := clR2_same (b := 69) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c0 := fun _ es => c0L es) (L := L) (L' := L') (c0L_agree (hS.1.mono (by norm_num)))
    (l := 14) (hS.1.mono (by norm_num))
  have hrw : rwL es = rwL es' := by unfold rwL rhiL; rw [hl, hr]
  unfold PLc; rw [hc, vM_agree4 hS.1, rkL_agree4 hS.1 (by norm_num), hrw, ha, hk]

/-- L's dooms read the log only through the level-0 word (`hstab`). -/
theorem lDooms_log4 (hz : ZwSame zw) (h : T4.Same L X L' X p) (hp : 3 ≤ p) :
    (L1Bad M zw L X ↔ L1Bad M zw L' X) ∧ (D2L M zw L X ↔ D2L M zw L' X) ∧
      (L3Bad M zw L X ↔ L3Bad M zw L' X) ∧ (PendLc M zw L X ↔ PendLc M zw L' X) ∧
      (L3BadN M zw L X ↔ L3BadN M zw L' X) ∧ (PendLcN M zw L X ↔ PendLcN M zw L' X) := by
  have hzN := zN_same4 hz h hp (kindOfC X)
  have ha : aLin M zw L X = aLin M zw L' X ∧ bLin M zw L X = bLin M zw L' X := by
    unfold aLin bLin; rw [hzN]; exact ⟨rfl, rfl⟩
  have hf : zfL M zw L X = zfL M zw L' X := by unfold zfL; rw [hzN]
  refine ⟨by unfold L1Bad; rw [ha.1, ha.2], T4.D2_congrL (by unfold TL; rw [hzN]) rfl,
    by unfold L3Bad; rw [hf], by unfold PendLc tL; rw [hf], by unfold L3BadN; rw [hf],
    by unfold PendLcN tNL; rw [hf]⟩

end Reads

/-! ## L1 and L2 -/

section L12
variable {M : ZLM4} {zw : Wit}

open Classical in
/-- **L1's squeeze** (A.10 L1, `1·2^128`; `batch_count` at 2 claims). -/
theorem l1_single4 (hz : ZwSame zw) (L es : Log) (hl : es.length = 68) :
    (univ.filter fun a => ZendBad M zw L es ∧ ¬ L1Bad M zw L (ext1 es a)).card ≤ 1 * 2 ^ 128 := by
  by_cases hzb : ZendBad M zw L es
  swap
  · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ h =>
      hzb h.1)).trans_le (Nat.zero_le _)
  refine batch_count _ (fun i : Fin 2 => if i.val = 0 then vZ es 0 else vZ es 1)
    (fun i : Fin 2 => if i.val = 0 then aLin M zw L es else bLin M zw L es) (fun he => ?_)
    fun a ⟨_, hn⟩ => ?_
  · apply hzb.2
    have h0 := congrFun he 0; have h1 := congrFun he 1
    simp only [Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false] at h0 h1
    rw [aStar_eq4, bStar_eq4, h0, h1]
  · have hS := same_ext1_4 L es a
    rw [hl] at hS
    have hal : alL (ext1 es a) = chF a 0 := by
      have := entAt_ext1 es a; rw [hl] at this
      simp only [alL, fAt, ansAt, this]
    have hv : ∀ j, vZ (ext1 es a) j = vZ es j := fun j => by
      simp only [vZ, msgAt_congr hS.1 (show 67 < 68 by norm_num)]
    obtain ⟨e1, e2⟩ := aLin_same4 (M := M) hz hS (by norm_num)
    have hn' : vZ es 0 + chF a 0 * vZ es 1 = aLin M zw L es + chF a 0 * bLin M zw L es := by
      by_contra hc
      exact hn ⟨by rw [length_ext1]; omega, by rw [hal, hv, hv, e1, e2]; exact hc⟩
    simpa [Fin.sum_univ_two] using hn'

/-- **Into L2** (`habs` at 69): a false `â + α b̂` is L2's false initial claim. -/
theorem l2_habs4 (hz : ZwSame zw) {L es : Log} (x : ByteArray × Digest) (hl : es.length = 69)
    (hb : L1Bad M zw L es) : D2L M zw L (es ++ [x]) := by
  have hS := T4.same_append L es [x]
  rw [hl] at hS
  refine ⟨by simp; omega, ?_⟩
  have ha0 : T4.ans3 69 (fun _ => 14) (es ++ [x]) = 0 := by
    simp only [T4.ans3, List.length_append, List.length_singleton, hl]; simp
  rw [ha0]
  simp only [T4.Wrong2, clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [TL_same4 hz hS le_rfl, c0L_agree hS.1]
  unfold TL; rw [lin_trueSum_kinds]
  exact hb.2

open Classical in
/-- **L2's squeezes** (A.10 L2, `2·2^128`; T4's `D2_single`), with the round checks from
`¬ RejL2`. -/
theorem l2_single4 (hz : ZwSame zw) (L es : Log)
    (hchk : ∀ j, es.length = 69 + 2 * j + 1 → j < 14 →
      Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es j) :
    (univ.filter fun d => D2L M zw L es ∧ ¬ D2L M zw L (ext1 es d)).card ≤ 2 * 2 ^ 128 :=
  T4.D2_single (by norm_num) (TL_local4 hz) (kindExpr_deg 8) card_chF_fiber (TL_size4 (M := M))
    L es hchk

/-- An L2 round's absorb keeps the doom. -/
theorem append_L2_4 (hz : ZwSame zw) {L es : Log} (x : ByteArray × Digest) (hlen : 69 < es.length)
    (hc : (es.length - 69) % 2 = 0 ∨ 14 ≤ (es.length - 69) / 2) :
    D2L M zw L (es ++ [x]) ↔ D2L M zw L es :=
  T4.D2_append_iff (by norm_num) (TL_local4 hz) x hlen hc

/-- **L2's round checks are a `T4.RejOK`** (the rounds' absorbs are not `seq4` squeezes). -/
theorem rejL2_ok4 : T4.RejOK RejL2 where
  mono L es x := rejL2_mono x
  sq L es x hit := by
    refine ⟨fun ⟨j, hj, hlt, hc⟩ => ?_, rejL2_mono x⟩
    simp only [List.length_append, List.length_singleton] at hlt
    by_cases he : 69 + 2 * j = es.length
    · exact absurd (he ▸ hit) (p4a_abs.2.2.1 j hj)
    exact ⟨j, hj, by omega, fun h' => hc ((chkL_agree (agree_append es [x] (by omega))).mpr h')⟩
  stab L i hb hci X hX := by
    show FR.Snd.RejL2 _ _ ↔ FR.Snd.RejL2 _ _
    unfold FR.Snd.RejL2 Chk2
    simp only [clR2L_log (L.take i) L X]

end L12

/-! ## L3 (`habs` at 97) and L3β (`hsingle` at 98) -/

section L3
variable {M : ZLM4} {zw : Wit}

/-- L2's final claim against the masked values, at L3's absorb (3.x's `l3_habs` core): unless
`finLc` (ii) fails for the kind's flag, some masked value is wrong. -/
theorem l3_core (hz : ZwSame zw) {L es : Log} (x : ByteArray × Digest) (hl : es.length = 97)
    (hd : D2L M zw L es) :
    PLc M (kindOfC es).isNode L (es ++ [x]) ∨
      ∃ j, vM (kindOfC es) (es ++ [x]) j ≠ zfL M zw L (es ++ [x]) j := by
  have hS := T4.same_append L es [x]
  rw [hl] at hS
  have hk : kindOfC (es ++ [x]) = kindOfC es := hS.kind (by norm_num)
  obtain ⟨-, hw⟩ := hd
  have ha : T4.ans3 69 (fun _ => 14) es = 14 := by simp [T4.ans3, hl]
  rw [ha] at hw
  unfold T4.Wrong2 at hw
  rw [Nat.sub_self] at hw
  have hfin : trueSum (kindExpr 8) (bindAll (TL M zw L es) (rchs2 69 (fun d => chF d 0) es 14)) 0 =
      ∑ j, mle (linM (M.Ak j) (M.Bk j) (rwL es) (alL es)) (ptOf 14 (rkL es)) * zfL M zw L es j :=
    lin_final_kinds _ _ _ _ _ _ _ _ (by simp [rchs2])
  rw [hfin] at hw
  obtain ⟨-, hlam, hr, hal, -, -⟩ := lin_agree4 (hS.1.mono (by norm_num))
  have hrk : rkL (es ++ [x]) = rkL es := rkL_agree4 hS.1 le_rfl
  have hrw : rwL (es ++ [x]) = rwL es := by unfold rwL rhiL; rw [hlam, hr]
  have hc : clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (es ++ [x]) 14 =
      clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 :=
    clR2_congr (c0L_agree (hS.1.mono (by norm_num))) (hS.1.mono (by norm_num))
  by_cases hrej : PLc M (kindOfC es).isNode L (es ++ [x])
  · exact .inl hrej
  refine .inr ?_
  have hchk : clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 =
      ∑ j, vM (kindOfC es) (es ++ [x]) j *
        mle (linM (M.Ak j) (M.Bk j) (rwL es) (alL es)) (ptOf 14 (rkL es)) := by
    by_contra hne
    exact hrej ⟨by rw [hk], by rw [hk, hc, hrw, hal, hrk]; exact hne⟩
  rw [zfL_same4 hz hS (by norm_num)]
  by_contra hall
  push Not at hall
  refine hw (hchk.trans (Finset.sum_congr rfl fun j _ => ?_))
  rw [hall j, mul_comm]

/-- **At L3's absorb on a segment** (97): `RejLc2` or a wrong masked value. -/
theorem l3_habs4 (hz : ZwSame zw) {L es : Log} (x : ByteArray × Digest) (hl : es.length = 97)
    (hn : (kindOfC es).isNode = false) (hd : D2L M zw L es) :
    RejLc2 M L (es ++ [x]) ∨ L3Bad M zw L (es ++ [x]) := by
  have hk : kindOfC (es ++ [x]) = kindOfC es := (T4.same_append L es [x]).kind (by omega)
  rcases l3_core hz x hl hd with h | ⟨j, hj⟩
  · rw [hn] at h; exact .inl ⟨by simp; omega, h⟩
  · exact .inr ⟨by simp; omega, by rw [hk]; exact hn, j, by rw [hk]; exact hj⟩

/-- **At L3's absorb on a node** (97): `RejLcN` or a wrong masked value. -/
theorem l3N_habs4 (hz : ZwSame zw) {L es : Log} (x : ByteArray × Digest) (hl : es.length = 97)
    (hn : (kindOfC es).isNode = true) (hd : D2L M zw L es) :
    RejLcN M L (es ++ [x]) ∨ L3BadN M zw L (es ++ [x]) := by
  have hk : kindOfC (es ++ [x]) = kindOfC es := (T4.same_append L es [x]).kind (by omega)
  rcases l3_core hz x hl hd with h | ⟨j, hj⟩
  · rw [hn] at h; exact .inl ⟨by simp; omega, h⟩
  · exact .inr ⟨by simp; omega, by rw [hk]; exact hn, j, by rw [hk]; exact hj⟩

/-- L3β's answer and message on the squeezed log. -/
theorem l3b_ext1 (hz : ZwSame zw) (L es : Log) (a : Digest) (hl : es.length = 98) :
    fAt (ext1 es a) 98 0 = chF a 0 ∧ msgAt (ext1 es a) 97 = msgAt es 97 ∧
      zfL M zw L (ext1 es a) = zfL M zw L es ∧ kindOfC (ext1 es a) = kindOfC es := by
  have hS := same_ext1_4 L es a
  rw [hl] at hS
  refine ⟨?_, msgAt_congr hS.1 (by norm_num), zfL_same4 hz hS (by norm_num),
    hS.kind (by norm_num)⟩
  have := entAt_ext1 es a; rw [hl] at this
  simp only [fAt, ansAt, this]

theorem vBetaL_ext1 (es : Log) (a : Digest) (hb : fAt (ext1 es a) 98 0 = chF a 0)
    (hm : msgAt (ext1 es a) 97 = msgAt es 97) :
    vBetaL (ext1 es a) = ∑ i : Fin 8, chF a 0 ^ i.val * vL es i := by
  rw [vBetaL, hb, hm, Finset.sum_range (fun i => chF a 0 ^ i * readF (msgAt es 97) (16 * i))]
  rfl

open Classical in
/-- **L3β's squeeze on a segment** (A.10 L3β, `7·2^128`; `batch_count` at 8 values). -/
theorem l3b_single4 (hz : ZwSame zw) (hI : M.IndKinds) (L es : Log) (hl : es.length = 98) :
    (univ.filter fun a => L3Bad M zw L es ∧ ¬ PendLc M zw L (ext1 es a)).card ≤ 7 * 2 ^ 128 := by
  by_cases hb : L3Bad M zw L es
  swap
  · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ h =>
      hb h.1)).trans_le (Nat.zero_le _)
  have hzr : ∀ j : Fin 9, (∀ t, M.Ind (kindOfC es) j t = 0) → zfL M zw L es j = 0 := fun j h =>
    mle_zfoldK_zero (Ind := IndF M (kindOfC es) _) (fun t => h t.val) _ _ _
  refine batch_count _ (fun i : Fin 8 => vL es i) (tL M zw L es) (fun he => ?_)
    fun a ⟨_, hn⟩ => ?_
  · obtain ⟨-, hn, j, hj⟩ := hb
    by_cases h0 : j = 0
    · subst h0
      have := congrFun he 0
      simp only [tL, vM, hn, Fin.val_zero, if_true] at this hj
      exact hj (by simpa using this)
    · have := hzr j fun t => (hI (kindOfC es) t).2 hn j h0
      simp only [vM, hn, if_false, show j.val ≠ 0 from fun h => h0 (Fin.ext h)] at hj
      exact hj (by simp [this])
  · obtain ⟨hβ, hm, hzf, hk⟩ := l3b_ext1 (M := M) hz L es a hl
    have ht : tL M zw L (ext1 es a) = tL M zw L es := by funext i; simp only [tL, hzf]
    have hn' : vBetaL (ext1 es a) = ∑ i : Fin 8, chF a 0 ^ i.val * tL M zw L es i := by
      by_contra hc
      exact hn ⟨by rw [length_ext1]; omega, by rw [hk]; exact hb.2.1, by rw [hβ, ht]; exact hc⟩
    rw [← hn', vBetaL_ext1 es a hβ hm]

open Classical in
/-- **L3β's squeeze on a node** (`7·2^128`; `batch_count` at 8 values). -/
theorem l3bN_single4 (hz : ZwSame zw) (hI : M.IndKinds) (L es : Log) (hl : es.length = 98) :
    (univ.filter fun a => L3BadN M zw L es ∧ ¬ PendLcN M zw L (ext1 es a)).card ≤
      7 * 2 ^ 128 := by
  by_cases hb : L3BadN M zw L es
  swap
  · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ h =>
      hb h.1)).trans_le (Nat.zero_le _)
  refine batch_count _ (fun i : Fin 8 => vL es i) (tNL M zw L es) (fun he => ?_)
    fun a ⟨_, hn⟩ => ?_
  · obtain ⟨-, hn, j, hj⟩ := hb
    by_cases h0 : j = 0
    · subst h0
      have h0' : zfL M zw L es 0 = 0 :=
        mle_zfoldK_zero (Ind := IndF M (kindOfC es) _)
          (fun t => (hI (kindOfC es) t.val).1 hn) _ _ _
      simp only [vM, hn, if_true, Fin.val_zero, h0'] at hj
      exact hj rfl
    · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h0
      have := congrFun he i
      simp only [vM, hn, if_true, Fin.val_succ, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel] at hj
      exact hj (by simpa [tNL] using this)
  · obtain ⟨hβ, hm, hzf, hk⟩ := l3b_ext1 (M := M) hz L es a hl
    have ht : tNL M zw L (ext1 es a) = tNL M zw L es := by funext i; simp only [tNL, hzf]
    have hn' : vBetaL (ext1 es a) = ∑ i : Fin 8, chF a 0 ^ i.val * tNL M zw L es i := by
      by_contra hc
      exact hn ⟨by rw [length_ext1]; omega, by rw [hk]; exact hb.2.1, by rw [hβ, ht]; exact hc⟩
    rw [← hn', vBetaL_ext1 es a hβ hm]

/-- **`finLc` (ii)'s failure on a segment is a `T4.RejOK`** (from L3's absorb at 97 on). -/
theorem rejLc2_ok4 : T4.RejOK (RejLc2 M) :=
  rejOK_at4 (p := 97) (pLc_reads4 false) p4a_abs.2.1

/-- **`finLc` (ii)'s failure on a node is a `T4.RejOK`.** -/
theorem rejLcN_ok4 : T4.RejOK (RejLcN M) :=
  rejOK_at4 (p := 97) (pLc_reads4 true) p4a_abs.2.1

end L3

end

end FR.Snd.P4a
