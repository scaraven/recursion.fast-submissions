-- New for `flock-recursive` (BLUEPRINT A.10 rows L3, L3β on a node, §5.2 row L3; revision 3.16;
-- stage S-G11).
import FRSoundnessFrDF

/-!
# The node's L3 and L3β (revision 3.16): `NodeLF` discharged

The node's lincheck end (`finLc` (ii) at 3.16: the walk at the mask `[0, v₀ … v₆, 0]` plus the
`free` term, which is `Σ_j v′_j M̃_j(r_k)` with `zlmFR`'s matrices, `M̃_free` by `linM_free_mle`),
its L3 values and L3β's batch, with the leaf's binding `v = v_β` (`lin_beta_claim`):

* **`indKW_eq`**: the verifier's kind intervals (`KW.ivsQ 16`) are `nodeBK`'s classes, i.e.
  `zlmFR`'s node indicators (`part_one`: the kinds partition the blocks).
* **`trueL_node`**: RS claim 2's true value on a node (the kind-weighted claim of `gL`) is
  `Σ_i β^i z̄̃_{i+1}(r_k)`, the true batch.
* **`RejLcN`**, **`L3BadN`**, **`PendLcN`**: the node's `finLc` (ii) failure, L3's doom (a value is
  not its kind's), L3β's (`v_β` is not the true batch).
* **`nodeLF`**: `NodeLF oLcV RejLcN L3BadN PendLcN` with **`oLcV κ es v := v = vBetaL es`** for
  every kind. L3β's count is `7·2^128 ≤ 8·2^128`.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## The verifier's kind intervals are `nodeBK`'s classes -/

section Ind

theorem selOf_nonneg (ivs : List (ℕ × ℕ)) {n : ℕ} (x : Fin (2 ^ n)) : 0 ≤ (selOf ivs x : ℤ) :=
  List.sum_nonneg fun y hy => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy
    split_ifs <;> norm_num

theorem selOf_castF (ivs : List (ℕ × ℕ)) {n : ℕ} (x : Fin (2 ^ n)) :
    (selOf ivs x : F) = ((selOf ivs x : ℤ) : F) := by
  simp only [selOf, Int.cast_list_sum, List.map_map, Function.comp_def, Int.cast_ite,
    Int.cast_one, Int.cast_zero]

theorem nodeBK_free {t : ℕ} (h : nodeBK t = .free) : Layout.wmBase ≤ t := by
  by_contra hlt
  push Not at hlt
  revert h
  unfold nodeBK Layout.wotsKindAt
  split_ifs <;> first | decide | omega

theorem nodeKinds_cover (b : BlockKind) (hb : b ≠ .chain) :
    ∃ i < 8, KW.nodeKinds.getD i .free = b := by
  cases b <;> first | exact absurd rfl hb | decide

theorem nodeKinds_inj : ∀ i < 8, ∀ j < 8, KW.nodeKinds.getD i .free = KW.nodeKinds.getD j .free →
    i = j := by decide

theorem selOf_pos {t : ℕ} (ht : t < 2 ^ 16) :
    1 ≤ (selOf (KW.ivsQ 16 (nodeBK t)) (⟨t, ht⟩ : Fin (2 ^ 16)) : ℤ) := by
  by_cases hf : nodeBK t = .free
  · have := nodeBK_free hf
    simp only [KW.ivsQ, hf, if_true, selOf, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [if_pos ⟨this, ht⟩]
  · simp only [KW.ivsQ, hf, if_false]
    have hI := ind_nodeBK (blk := t) ht
    simp only [Layout.Ind, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hI
    obtain ⟨iv, hm, ⟨hk, hlo⟩, hhi⟩ := hI
    refine le_trans ?_ (List.single_le_sum (fun y hy => ?_) (if iv.lo ≤ t ∧ t < iv.hi then 1 else 0)
      (List.mem_map.mpr ⟨(iv.lo, iv.hi), ?_, rfl⟩))
    · rw [if_pos ⟨hlo, hhi⟩]
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy
      split_ifs <;> norm_num
    · exact List.mem_map.mpr ⟨iv, List.mem_filter.mpr ⟨hm, by simp [hk]⟩, rfl⟩

/-- **The verifier's kind intervals are `nodeBK`'s classes**: on a node block `t`, kind `i`'s
indicator (`indKW`) is `1` exactly when `nodeKinds[i]` is the block's class. -/
theorem indKW_eq (i : Fin 8) {t : ℕ} (ht : t < 2 ^ 16) :
    indKW i ⟨t, ht⟩ = if KW.nodeKinds.getD i .free = nodeBK t then 1 else 0 := by
  set S : ℕ → ℤ := fun i => selOf (KW.ivsQ 16 (KW.nodeKinds.getD i .free)) (⟨t, ht⟩ : Fin (2 ^ 16))
  have hsum : ∑ i ∈ range 8, S i = 1 := KW.part_one (R := ℤ) le_rfl ⟨t, ht⟩
  have hnn : ∀ i ∈ range 8, 0 ≤ S i := fun i _ => selOf_nonneg _ _
  obtain ⟨i₀, hi₀, hk₀⟩ := nodeKinds_cover _ (nodeBK_ne_chain t)
  have hpos : 1 ≤ S i₀ := by simp only [S, hk₀]; exact selOf_pos ht
  have hm₀ : i₀ ∈ range 8 := mem_range.mpr hi₀
  rw [← add_sum_erase _ _ hm₀] at hsum
  have hnn' : ∀ i ∈ (range 8).erase i₀, 0 ≤ S i := fun i hi => hnn i (mem_of_mem_erase hi)
  have hrest := sum_nonneg hnn'
  have h0 : ∀ i ∈ (range 8).erase i₀, S i = 0 := (sum_eq_zero_iff_of_nonneg hnn').mp (by omega)
  rw [indKW, selOf_castF]
  split_ifs with hk
  · have : i.val = i₀ := nodeKinds_inj _ i.isLt _ hi₀ (hk.trans hk₀.symm)
    have h1 : S i₀ = 1 := by omega
    rw [← this] at h1
    change ((S i.val : ℤ) : F) = 1
    rw [h1, Int.cast_one]
  · have hne : i.val ≠ i₀ := fun he => hk (he ▸ hk₀)
    have := h0 i.val (mem_erase.mpr ⟨hne, mem_range.mpr i.isLt⟩)
    change ((S i.val : ℤ) : F) = 0
    rw [this, Int.cast_zero]

/-- `zlmFR`'s node indicator of kind `i + 1` is `indKW i`. -/
theorem ind_succ_eq (i : Fin 8) {t : ℕ} (ht : t < 2 ^ 16) :
    zlmFR.Ind .N30 i.succ t = indKW i ⟨t, ht⟩ := by
  rw [indKW_eq i ht]
  simp only [zlmFR, Kind.isNode, if_true]
  have : bkOf i.succ = KW.nodeKinds.getD i .free := by fin_cases i <;> rfl
  rw [this]

/-- **A node's kind factor** in `zlmFR`'s indicators. -/
theorem kfT_node {es : Log} {t : ℕ} (ht : t < 2 ^ 16) :
    kfT .N30 es t = ∑ i : Fin 8, fAt es 98 0 ^ i.val * zlmFR.Ind .N30 i.succ t := by
  simp only [kfT, Kind.isNode, if_true, kindFac, Nat.mod_eq_of_lt ht, ind_succ_eq _ ht]

end Ind

/-! ## RS claim 2's true value on a node -/

/-- Kind `k`'s true value as a sum on the cube. -/
theorem zfL_eq (L es : Log) (k : Fin 9) : zfL zlmFR L es k =
    ∑ t ∈ range (2 ^ qL (kindOf es)), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 (rkL es)) j * eqAtR (rbLc es) t * zlmFR.Ind (kindOf es) k t *
        zW (kindOf es) L es (j + 2 ^ 14 * t) := by
  unfold zfL zfoldK mle IndF
  simp only [eq_cube_eqAtR, zN, join, mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ j ∈ range (2 ^ 14), eqAtR (ptOf 14 (rkL es)) j *
      eqAtR (rbLc es) t * zlmFR.Ind (kindOf es) k t * zW (kindOf es) L es (j + 2 ^ 14 * t)),
    sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => eqAtR (ptOf 14 (rkL es)) j *
      eqAtR (rbLc es) t.val * zlmFR.Ind (kindOf es) k t.val *
        zW (kindOf es) L es (j + 2 ^ 14 * t.val))]
  exact sum_congr rfl fun j _ => by rw [add_comm (2 ^ 14 * t.val)]; ring

theorem kind_node {κ : Kind} (hn : κ.isNode = true) : κ = .N30 := by
  cases κ <;> first | rfl | exact absurd hn (by decide)

theorem kfT_nodeK {κ : Kind} (hn : κ.isNode = true) {es : Log} {t : ℕ} (ht : t < 2 ^ 16) :
    kfT κ es t = ∑ i : Fin 8, fAt es 98 0 ^ i.val * zlmFR.Ind κ i.succ t := by
  obtain rfl := kind_node hn; exact kfT_node ht

/-- The node's true batch: kind `i + 1`'s true value (`finLc`'s `v_i` order). -/
noncomputable def tN (L es : Log) (i : Fin 8) : F := zfL zlmFR L es i.succ

theorem kindOf_node {es : Log} (hn : (kindOf es).isNode = true) : kindOf es = .N30 :=
  kind_node hn

/-- **RS claim 2's true value on a node is the true batch** `Σ_i β^i z̄̃_{i+1}(r_k)`
(`trueL_one`'s kind factor, `lin_beta_claim`'s weight `W_β`). -/
theorem trueL_node {L es : Log} (hn : (kindOf es).isNode = true) :
    trueL (kindOf es) L es 1 = ∑ i : Fin 8, fAt es 98 0 ^ i.val * tN L es i := by
  rw [trueL_one]
  simp only [tN, zfL_eq, mul_sum]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun t ht => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  have ht' : t < 2 ^ 16 := by
    have := mem_range.mp ht; rw [kindOf_node hn] at this; exact this
  rw [kfT_nodeK hn ht', mul_sum, sum_mul]
  exact sum_congr rfl fun i _ => by ring

/-! ## The node's checks and dooms -/

/-- `finLc` (ii) fails on the log (kind flag `b`): L2's last claim is not `Σ_j v′_j M̃_j(r_k)`. -/
def PLc (b : Bool) (L es : Log) : Prop :=
  (kindOf es).isNode = b ∧ clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 ≠
    ∑ j, vM (kindOf es) es j * mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rwL es) (alL es))
      (ptOf 14 (rkL es))

theorem pLc_reads (b : Bool) : Reads 98 (PLc b) := fun L es L' es' _ _ hS => by
  obtain ⟨hk, hl, hr, ha, -, -⟩ := lin_agree (hS.1.mono (by norm_num))
  have hc := clR2_same (b := 69) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c0 := fun _ es => c0L es) (L := L) (L' := L') (c0L_agree (hS.1.mono (by norm_num)))
    (l := 14) (hS.1.mono (by norm_num))
  have hv : vM (kindOf es) es = vM (kindOf es') es' := by
    funext j; simp only [vM, vL, msgAt_congr hS.1 (show 97 < 98 by norm_num), hk]
  have hrk : rkL es = rkL es' := by
    unfold rkL rchs; exact List.map_congr_left fun j hj => by
      simp only [List.mem_range] at hj; exact rch_congr hS.1 (by omega)
  have hrw : rwL es = rwL es' := by unfold rwL rhiL; rw [hl, hr]
  unfold PLc; rw [hc, hv, hrk, hrw, ha, hk]

/-- **The node's `finLc` (ii) fails** (from 98; revision 3.16: walk plus `free` term). -/
def RejLcN (L es : Log) : Prop := 98 ≤ es.length ∧ PLc true L es

/-- **L3's doom on a node**: some masked value is not its kind's true value. -/
def L3BadN (L es : Log) : Prop :=
  98 ≤ es.length ∧ (kindOf es).isNode = true ∧ ∃ j, vM (kindOf es) es j ≠ zfL zlmFR L es j

/-- **L3β's doom on a node**: `v_β` is not the true batch `Σ_i β^i z̄̃_{i+1}(r_k)`. -/
def PendLcN (L es : Log) : Prop :=
  99 ≤ es.length ∧ (kindOf es).isNode = true ∧
    vBetaL es ≠ ∑ i : Fin 8, fAt es 98 0 ^ i.val * tN L es i

/-- **Claim 2's binding** (every kind; ruling 3.16): `finLc` (iii)'s `v = v_β`. -/
def oLcV (_ : Kind) (es : Log) (v : F) : Prop := v = vBetaL es

/-! ## The units -/

variable {L es : Log}

theorem rejLcN_reads : Reads 98 RejLcN := fun L es L' es' h1 h2 h => by
  unfold RejLcN
  exact and_congr ⟨fun _ => h2, fun _ => h1⟩ (pLc_reads true L es L' es' h1 h2 h)

theorem rejLcN_ok (hp : fsItems[97]? ≠ some .squeeze) : RejOK RejLcN :=
  rejOK_at (p := 97) (pLc_reads true) hp

theorem l3BadN_reads : Reads 98 L3BadN := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  have hv : ∀ i, vL es i = vL es' i := fun i => by
    simp only [vL, msgAt_congr h.1 (show 97 < 98 by norm_num)]
  have hvm : vM (kindOf es) es = vM (kindOf es') es' := by
    funext j; simp only [vM, hv, hk]
  unfold L3BadN; rw [hvm, zfL_same h (by norm_num), hk]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem pendLcN_reads : Reads 99 PendLcN := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  have hb : vBetaL es = vBetaL es' := by
    simp only [vBetaL, fAt_congr h.1 (show 98 < 99 by norm_num),
      msgAt_congr h.1 (show 97 < 99 by norm_num)]
  have ht : tN L es = tN L' es' := by
    funext i; simp only [tN, zfL_same h (by norm_num)]
  unfold PendLcN; rw [hb, ht, hk, fAt_congr h.1 (show 98 < 99 by norm_num)]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

/-- **At L3's absorb on a node** (97): a false final L2 claim gives `RejLcN` or a wrong value
(`lin_final_kinds`). -/
theorem l3N_habs (x : ByteArray × Digest) (hl : es.length = 97) (hn : (kindOf es).isNode = true)
    (hd : D2L zlmFR L es) : RejLcN L (es ++ [x]) ∨ L3BadN L (es ++ [x]) := by
  have hS := same_append L es [x]
  rw [hl] at hS
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by norm_num)
  obtain ⟨-, hw⟩ := hd
  have ha : ans3 69 (fun _ => 14) es = 14 := by simp [ans3, hl]
  rw [ha] at hw
  unfold Wrong2 at hw
  rw [Nat.sub_self] at hw
  have hfin : trueSum (kindExpr 8) (bindAll (TL zlmFR L es) (rchs2 69 (fun d => chF d 0) es 14))
      0 = ∑ j, mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rwL es) (alL es)) (ptOf 14 (rkL es)) *
        zfL zlmFR L es j :=
    lin_final_kinds _ _ _ _ _ _ _ _ (by simp [rchs2])
  rw [hfin] at hw
  obtain ⟨-, hlam, hr, hal, -, -⟩ := lin_agree (hS.1.mono (by norm_num))
  have hrk : rkL (es ++ [x]) = rkL es := by
    unfold rkL rchs; exact List.map_congr_left fun j hj => by
      simp only [List.mem_range] at hj; exact rch_congr hS.1 (by omega)
  have hrw : rwL (es ++ [x]) = rwL es := by unfold rwL rhiL; rw [hlam, hr]
  have hc : clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (es ++ [x]) 14 =
      clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 :=
    clR2_congr (c0L_agree (hS.1.mono (by norm_num))) (hS.1.mono (by norm_num))
  by_cases hrej : RejLcN L (es ++ [x])
  · exact .inl hrej
  refine .inr ⟨by simp; omega, by rw [hk]; exact hn, ?_⟩
  have hchk : clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 =
      ∑ j, vM (kindOf es) (es ++ [x]) j *
        mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rwL es) (alL es)) (ptOf 14 (rkL es)) := by
    by_contra hne
    exact hrej ⟨by simp; omega, by rw [hk]; exact hn, by rw [hk, hc, hrw, hal, hrk]; exact hne⟩
  rw [zfL_same hS (by norm_num), hk]
  by_contra hall
  push Not at hall
  refine hw (hchk.trans (Finset.sum_congr rfl fun j _ => ?_))
  rw [hall j, mul_comm]

open Classical in
/-- **L3β's squeeze on a node** (§5.2 row L3, `7·2^128 ≤ 8·2^128`; `batch_count` at 8 values). -/
theorem l3bN_single (L es : Log) (hl : es.length = 98) :
    (univ.filter fun a => L3BadN L es ∧ ¬ PendLcN L (ext1 es a)).card ≤ 8 * 2 ^ 128 := by
  refine le_trans ?_ (show 7 * 2 ^ 128 ≤ 8 * 2 ^ 128 by norm_num)
  by_cases hb : L3BadN L es
  swap
  · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ h =>
      hb h.1)).trans_le (Nat.zero_le _)
  refine batch_count _ (fun i : Fin 8 => vL es i) (tN L es) (fun he => ?_) fun a ⟨_, hn⟩ => ?_
  · obtain ⟨-, hn, j, hj⟩ := hb
    by_cases h0 : j = 0
    · subst h0
      have h0' : zfL zlmFR L es 0 = 0 :=
        mle_zfoldK_zero (Ind := IndF zlmFR (kindOf es) _)
          (fun t => (zlmFR_indKinds (kindOf es) t.val).1 hn) _ _ _
      simp only [vM, hn, if_true, Fin.val_zero, h0'] at hj
      exact hj rfl
    · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h0
      have := congrFun he i
      simp only [vM, hn, if_true, Fin.val_succ, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel] at hj
      exact hj (by simpa [tN] using this)
  · have hS := same_ext1 L es a
    rw [hl] at hS
    have hβ : fAt (ext1 es a) 98 0 = chF a 0 := by
      have := entAt_ext1 es a; rw [hl] at this
      simp only [fAt, ansAt, this]
    have hm : msgAt (ext1 es a) 97 = msgAt es 97 := msgAt_congr hS.1 (by norm_num)
    have ht : tN L (ext1 es a) = tN L es := by
      funext i; simp only [tN, zfL_same hS (by norm_num)]
    have hn' : vBetaL (ext1 es a) = ∑ i : Fin 8, chF a 0 ^ i.val * tN L es i := by
      by_contra hc
      exact hn ⟨by rw [length_ext1]; omega, by rw [hS.kind (by norm_num)]; exact hb.2.1,
        by rw [hβ, ht]; exact hc⟩
    rw [← hn', vBetaL, hβ, hm,
      Finset.sum_range (fun i => chF a 0 ^ i * readF (msgAt es 97) (16 * i))]
    rfl

/-- **The node's L meets `NodeLF`** with the leaf's binding `v = v_β` for every kind. -/
theorem nodeLF (hp : fsItems[97]? ≠ some .squeeze) : NodeLF oLcV RejLcN L3BadN PendLcN where
  rej := rejLcN_ok hp
  rejReads := rejLcN_reads
  rejLen _ _ h := h.1
  l3Reads := l3BadN_reads
  pendReads := pendLcN_reads
  habs L es x hl hn hd := l3N_habs x hl hn hd
  single := l3bN_single
  pend L es h ho := h.2.2 (by rw [← trueL_node h.2.1]; exact ho.symm)
  okReads κ es es' h := by
    have hv : vBetaL es = vBetaL es' := by
      simp only [vBetaL, fAt_congr h (show 98 < 312 by norm_num),
        msgAt_congr h (show 97 < 312 by norm_num)]
    funext v; simp only [oLcV, hv]
  leaf _ _ _ := Iff.rfl

/-! ## Controls -/

/-- Control (positive): a leaf's kind factor is `1`. -/
theorem kfT_leaf (es : Log) (t : ℕ) : kfT .P30 es t = 1 := rfl

/-- Control (positive): at `β = 1` a node's kind factor is `1` (the kinds partition the blocks). -/
theorem kfT_node_one {es : Log} (h : fAt es 98 0 = 1) (t : ℕ) : kfT .N30 es t = 1 := by
  simp only [kfT, Kind.isNode, if_true, kindFac, h, one_pow, one_mul, indKW]
  rw [Fin.sum_univ_eq_sum_range (fun i => (selOf (KW.ivsQ 16 (KW.nodeKinds.getD i .free))
    (⟨t % 2 ^ 16, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ 16)) : F)) 8]
  exact KW.part_one le_rfl _

/-- Control (negative): at `β = 0` a node's kind factor vanishes on a block of kind `v_3`
(`hashA`, the statement's first block), so the weight is not the plain `eq`. -/
theorem kfT_node_zero {es : Log} (h : fAt es 98 0 = 0) : kfT .N30 es Layout.stmtBase = 0 := by
  have hs : Layout.stmtBase < 2 ^ 16 := by decide
  rw [kfT_node hs, h]
  refine sum_eq_zero fun i _ => ?_
  by_cases hi : i = 0
  · subst hi
    have : zlmFR.Ind .N30 (0 : Fin 8).succ Layout.stmtBase = 0 := by
      rw [ind_succ_eq _ hs, indKW_eq _ hs, if_neg (by decide)]
    rw [this, mul_zero]
  · rw [zero_pow (fun h => hi (Fin.ext h)), zero_mul]

/-- Control (negative): `oLcV` refuses every value but `v_β`. -/
theorem not_oLcV (κ : Kind) (es : Log) : ¬ oLcV κ es (vBetaL es + 1) := by simp [oLcV]

theorem not_rejLcN_leaf {L es : Log} (hn : (kindOf es).isNode = false) : ¬ RejLcN L es :=
  fun h => by rw [h.2.1] at hn; exact Bool.noConfusion hn

end FR.Snd
