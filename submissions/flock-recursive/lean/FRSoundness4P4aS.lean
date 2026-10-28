-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.10 S1/S2; stage P4a pass 3 (P4c)).
import FRSoundness4P4aBridge
import FRSoundness4TailFront

/-!
# S1 at revision 4.1: S2's true sum, the residual, S1's charge

* **`trueSum_TS_seg`**: a segment's S2 true sum (`TS`, the masked weight at `L = lastL`) is its
  initial claim `c0S` plus the batched residual of `resSeg` (`sh_sum_seg`, `c0S_seg`).
* **`SNode`**: what a node kind's S2 law must supply (its residual tables, their count `J`, the sum
  law, the truth's failure leaves a nonzero table, congruence): S-E's, a parameter (S-G13 F3).
* **`resS4`**, **`TR4`**, **`trueSum_TS4`**, **`tr_ne4`**: the residual by kind; a failed S truth
  leaves a nonzero residual table.
* **`ZwSame`**: the witness reads the log before position 3 (level 0's word and the seed);
  **`zwSame_zW`**: T4's `zW` does.
* **`s1_hfin4`**: S1's charge at `seq4`'s `(98, 15)`, `≤ (nb + 10 + J − 1)/2^128`.
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## The witness reads the log before position 3 -/

/-- **`zw` reads only the seed and the level-0 word** (T4's `Same` at 3). -/
def ZwSame (zw : Wit) : Prop :=
  ∀ κ L es L' es' p, T4.Same L es L' es' p → 3 ≤ p → zw κ L es = zw κ L' es'

theorem capPos_zero4 : T4.capPos 0 = 2 := by
  have h := congrArg (·[0]?) T4.capPos_eq
  simp only [List.getElem?_map, List.getElem?_range (show 0 < 5 by norm_num), Option.map_some,
    List.getElem?_cons_zero, Option.some.injEq] at h
  exact h

/-- **T4's witness `z = unpack f⁽⁰⁾` reads before position 3.** -/
theorem zwSame_zW : ZwSame T4.zW := fun κ L es L' es' p h hp => by
  funext b
  simp only [T4.zW, T4.fF, T4.fTab_same h (i := 0) (by norm_num) κ (by rw [capPos_zero4]; omega)]

/-! ## A segment's S2 true sum -/

section Sum
variable (wN : CKind → Log → ℕ → ℕ → F) (zw : Wit)

/-- **A segment's residual on the log** (`resSeg` at `L = lastL`, the statement's boundary). -/
def resSegL (κ : CKind) (L es : Log) : ℕ → ℕ → ℕ → F :=
  resSeg (nbC κ) (lastL es) (zNodeC zw κ L es) (sbL κ es) (hbL κ es)

theorem sum_TS (L es : Log) :
    trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es)) =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        wS wN (kindOfC es) es y q * zNodeC zw (kindOfC es) L es y q := by
  rw [nrS, TS, prod_trueSum]
  rw [Fin.sum_univ_eq_sum_range (fun i => wS wN (kindOfC es) es (i % 2 ^ nbC (kindOfC es))
      (i / 2 ^ nbC (kindOfC es)) * zNodeC zw (kindOfC es) L es (i % 2 ^ nbC (kindOfC es))
        (i / 2 ^ nbC (kindOfC es))), sum_range_pow_add]
  exact sum_congr rfl fun q _ => sum_congr rfl fun y hy => by
    obtain ⟨h1, h2⟩ := idx_split (q := q) (mem_range.1 hy); rw [h1, h2]

/-- **A segment's S2 true sum is its initial claim plus the residual** (B-12: the end at `L`, the
successor masked there). -/
theorem trueSum_TS_seg {L es : Log} (hn : (kindOfC es).isNode = false)
    (hL : lastL es < 2 ^ nbC (kindOfC es)) :
    trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es)) = c0S es +
      resSum (nbC (kindOfC es)) 2 (resSegL zw (kindOfC es) L es)
        (ptOf (nbC (kindOfC es)) (tauL (kindOfC es) es)) (ptOf 10 (thL es)) (ksL es) := by
  rw [sum_TS, c0S_seg hn hL]
  simp only [wS, hn, Bool.false_eq_true, if_false, resSegL]
  exact sh_sum_seg hL _ _ _ _ _ _

end Sum

/-! ## The node's S2 law (a parameter) and the residual by kind -/

/-- **A node kind's S2 law** (S-E's, S-G13 F3): `J` residual tables `res`, whose batched sum is the
true sum minus the initial claim, one of which is nonzero when the node's S truth fails; they read
the log before S1's first squeeze. -/
structure SNode (wN : CKind → Log → ℕ → ℕ → F) (truthSN : CKind → Log → Log → Prop) (zw : Wit)
    where
  nJ : CKind → ℕ
  res : CKind → Log → Log → ℕ → ℕ → ℕ → F
  nJ_pos : ∀ κ, 1 ≤ nJ κ
  nJ_le : ∀ κ, nbC κ + 10 + (nJ κ - 1) ≤ 239
  sum : ∀ L es, (kindOfC es).isNode = true →
    trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es)) = c0S es +
      resSum (nbC (kindOfC es)) (nJ (kindOfC es)) (res (kindOfC es) L es)
        (ptOf (nbC (kindOfC es)) (tauL (kindOfC es) es)) (ptOf 10 (thL es)) (ksL es)
  ne : ∀ κ L es, κ.isNode = true → ¬ truthSN κ L es →
    ∃ j < nJ κ, ∃ u < 2 ^ nbC κ, ∃ q < 2 ^ 10, res κ L es j u q ≠ 0
  same : ∀ κ L es L' es' p, T4.Same L es L' es' p → 99 ≤ p → res κ L es = res κ L' es'
  truth_same : ∀ κ L es L' es' p, T4.Same L es L' es' p → 3 ≤ p →
    (truthSN κ L es ↔ truthSN κ L' es')

section Kind
variable {wN : CKind → Log → ℕ → ℕ → F} {truthSN : CKind → Log → Log → Prop} {zw : Wit}
  (hN : SNode wN truthSN zw)

/-- The residual tables' count by kind. -/
def nJ4 (κ : CKind) : ℕ := if κ.isNode then hN.nJ κ else 2

/-- **The S residual by kind**: a node's `hN.res`, a segment's `resSegL`. -/
def resS4 (κ : CKind) (L es : Log) : ℕ → ℕ → ℕ → F :=
  if κ.isNode then hN.res κ L es else resSegL zw κ L es

/-- The residual tables `R_j` as arrays (index `u + 2^nb q`). -/
noncomputable def TR4 (κ : CKind) (L es : Log) (j : ℕ) : Array F :=
  Array.ofFn (n := 2 ^ (nbC κ + 10)) fun i => resS4 hN κ L es j (i.val % 2 ^ nbC κ) (i.val / 2 ^ nbC κ)

theorem TR4_size (κ : CKind) (L es : Log) (j : ℕ) : (TR4 hN κ L es j).size = 2 ^ (nbC κ + 10) := by
  simp [TR4]

theorem TR4_mle (κ : CKind) (L es : Log) (j : ℕ) (l : List F) :
    mle (tbl (nbC κ + 10) (TR4 hN κ L es j)) (ptOf (nbC κ + 10) l) =
      ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ nbC κ),
        eqAtR (ptOf (nbC κ) l) u * eqAtR (ptOf 10 (l.drop (nbC κ))) q * resS4 hN κ L es j u q := by
  rw [TR4]
  refine (mle_ofFn_split _ 10 (fun i => resS4 hN κ L es j (i % 2 ^ nbC κ) (i / 2 ^ nbC κ)) l).trans ?_
  exact sum_congr rfl fun q _ => sum_congr rfl fun u hu => by
    obtain ⟨h1, h2⟩ := idx_split (q := q) (mem_range.1 hu); rw [h1, h2]

/-- **S2's true sum is its initial claim plus the residual**, by kind (a segment's `L` among its
blocks). -/
theorem trueSum_TS4 {L es : Log}
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es)) :
    trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es)) = c0S es +
      resSum (nbC (kindOfC es)) (nJ4 hN (kindOfC es)) (resS4 hN (kindOfC es) L es)
        (ptOf (nbC (kindOfC es)) (tauL (kindOfC es) es)) (ptOf 10 (thL es)) (ksL es) := by
  unfold nJ4 resS4
  cases hn : (kindOfC es).isNode
  · simp only [Bool.false_eq_true, if_false]; exact trueSum_TS_seg wN zw hn (hL hn)
  · simp only [if_true]; exact hN.sum L es hn

/-- **A failed S truth leaves a nonzero residual table.** -/
theorem tr_ne4 {L es : Log} (h : ¬ truthS truthSN zw L es) :
    ∃ j < nJ4 hN (kindOfC es), tbl (nbC (kindOfC es) + 10) (TR4 hN (kindOfC es) L es j) ≠ 0 ∧
      ((kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es)) := by
  generalize hκ : kindOfC es = κ
  have key : ∀ j u q, u < 2 ^ nbC κ → q < 2 ^ 10 → resS4 hN κ L es j u q ≠ 0 →
      tbl (nbC κ + 10) (TR4 hN κ L es j) ≠ 0 := fun j u q hu hq hne he => by
    have hi : u + 2 ^ nbC κ * q < 2 ^ (nbC κ + 10) := by
      rw [pow_add]; nlinarith
    have := congrFun he ⟨u + 2 ^ nbC κ * q, hi⟩
    obtain ⟨h1, h2⟩ := idx_split (q := q) hu
    simp only [TR4, tbl_ofFn, Pi.zero_apply, h1, h2] at this
    exact hne this
  unfold truthS at h
  rw [hκ] at h
  unfold nJ4
  cases hn : κ.isNode
  · simp only [hn, Bool.false_eq_true, if_false, Classical.not_imp] at h ⊢
    obtain ⟨hL, hS⟩ := h
    obtain ⟨j, hj, u, hu, q, hq, hne⟩ := res_ne_seg hL hS
    have hne' : resS4 hN κ L es j u q ≠ 0 := by simp only [resS4, hn]; exact hne
    exact ⟨j, hj, key j u q hu hq hne', fun _ => hL⟩
  · simp only [hn, if_true] at h ⊢
    obtain ⟨j, hj, u, hu, q, hq, hne⟩ := hN.ne κ L es hn h
    have hne' : resS4 hN κ L es j u q ≠ 0 := by simp only [resS4, hn, if_true]; exact hne
    exact ⟨j, hj, key j u q hu hq hne', fun h => absurd h (by simp)⟩

end Kind

/-! ## Reads -/

section Reads
variable {L es L' es' : Log} {p : ℕ}

theorem nStmt_congr (h : Agree es es' p) (hp : 2 ≤ p) : nStmt es = nStmt es' := by
  simp only [nStmt, msgAt_congr h (show 1 < p by omega)]

theorem lastL_congr (h : Agree es es' p) (hp : 2 ≤ p) : lastL es = lastL es' := by
  simp only [lastL, nStmt_congr h hp]

theorem bndL_congr4 (h : Agree es es' p) (hp : 2 ≤ p) (κ : CKind) : bndL κ es = bndL κ es' := by
  simp only [bndL, h 0 (by omega), msgAt_congr h (show 1 < p by omega)]

theorem sbL_congr4 (h : Agree es es' p) (hp : 2 ≤ p) (κ : CKind) : sbL κ es = sbL κ es' := by
  funext σ; simp only [sbL, bndL_congr4 h hp κ]

theorem hbL_congr4 (h : Agree es es' p) (hp : 2 ≤ p) (κ : CKind) : hbL κ es = hbL κ es' := by
  funext σ; simp only [hbL, bndL_congr4 h hp κ]

theorem s1_congr4 (h : Agree es es' p) (hp : 114 ≤ p) (κ : CKind) :
    tauL κ es = tauL κ es' ∧ thL es = thL es' ∧ ksL es = ksL es' := by
  have hn := nbC_le κ
  refine ⟨List.map_congr_left fun l hl => coS_congr h (by simp at hl; omega),
    List.map_congr_left fun l hl => coS_congr h (by simp at hl; omega), coS_congr h (by omega)⟩

theorem endBits_congr4 (h : Agree es es' p) (hp : 2 ≤ p) (κ : CKind) :
    endBits κ es = endBits κ es' := by
  simp only [endBits, lastBits, nStmt_congr h hp]

theorem c0S_agree4 (h : Agree es es' p) (hp : 114 ≤ p) : c0S es = c0S es' := by
  have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.mono (by omega))
  obtain ⟨h1, h2, h3⟩ := s1_congr4 h hp (kindOfC es)
  simp only [c0S, hk, h2, h3, bndL_congr4 h (by omega), endBits_congr4 h (by omega)]
  rw [← hk, h1]

variable {zw : Wit}

theorem zNodeC_same (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (κ : CKind) :
    zNodeC zw κ L es = zNodeC zw κ L' es' := by
  funext b q; simp only [zNodeC, hz κ L es L' es' p h hp]

theorem resSegL_same (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (κ : CKind) :
    resSegL zw κ L es = resSegL zw κ L' es' := by
  simp only [resSegL, zNodeC_same hz h hp, lastL_congr h.1 (by omega), sbL_congr4 h.1 (by omega),
    hbL_congr4 h.1 (by omega)]

theorem resS4_same {wN : CKind → Log → ℕ → ℕ → F} {truthSN : CKind → Log → Log → Prop}
    (hN : SNode wN truthSN zw) (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 99 ≤ p)
    (κ : CKind) : resS4 hN κ L es = resS4 hN κ L' es' := by
  simp only [resS4, resSegL_same hz h (by omega), hN.same κ L es L' es' p h hp]

/-- **The S truth reads before position 3.** -/
theorem truthS_same4 {truthSN : CKind → Log → Log → Prop}
    (hT : ∀ κ L es L' es' p, T4.Same L es L' es' p → 3 ≤ p → (truthSN κ L es ↔ truthSN κ L' es'))
    (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) :
    truthS truthSN zw L es ↔ truthS truthSN zw L' es' := by
  have hk := h.kind (by omega)
  simp only [truthS, hk, zNodeC_same hz h hp, lastL_congr h.1 (by omega),
    sbL_congr4 h.1 (by omega), hbL_congr4 h.1 (by omega), hT _ L es L' es' p h hp]

end Reads

/-! ## S1's charge -/

/-- **S's positions at `seq4`** (identity below 170): S1 is the range `(98, 15)` (phase 11), S2's
rounds from 114 (phase 12), Lr1 from 170 (phase 13). -/
theorem s_unit_pos4 :
    (98, 15) ∈ fsRanges4 ∧ phOf4 98 = 10 ∧ phOf4 99 = 11 ∧ phOf4 113 = 11 ∧ phOf4 114 = 12 ∧
    phOf4 169 = 12 ∧ phOf4 170 = 13 := by
  refine ⟨by rw [fsRanges4_eq]; simp, ?_⟩
  have hph : ∀ q, phOf4 q = (fsStarts4.filter (· ≤ q)).length - 1 := fun _ => rfl
  simp only [hph, fsStarts4_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem selC_coords4 (κ : CKind) (X : Log) :
    ptOf (nbC κ) (selC (nbC κ) (List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i)) =
        ptOf (nbC κ) (tauL κ X) ∧
      ptOf 10 ((selC (nbC κ) (List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i)).drop (nbC κ)) =
        ptOf 10 (thL X) := by
  have hn := nbC_le κ
  set cl := List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i
  have hd : (selC (nbC κ) cl).drop (nbC κ) = (cl.drop 18).take 10 := by
    rw [selC, List.drop_left' (by simp [cl]; omega)]
  refine ⟨funext fun l => ?_, funext fun l => ?_⟩
  · have hl := l.isLt
    simp only [ptOf, selC, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [cl]; omega), List.getElem?_take, if_pos hl,
      ← List.getD_eq_getElem?_getD, coordS_getD X (by omega)]
    simp [tauL, hl]
  · have hl := l.isLt
    simp only [ptOf, hd, List.getD_eq_getElem?_getD]
    rw [List.getElem?_take, if_pos hl, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
      coordS_getD X (by omega)]
    simp [thL, hl]

open Classical in
/-- **S1's charge at `seq4`** (A.10 S1, `(nb + 10 + J − 1)/2^128`): with the doom of S1's entry
`Bg ∨ ¬ truthS` and its final doom `Bg ∨ S2Bad`. -/
theorem s1_hfin4 {wN : CKind → Log → ℕ → ℕ → F} {truthSN : CKind → Log → Log → Prop} {zw : Wit}
    (hN : SNode wN truthSN zw) (hz : ZwSame zw) {Dk : ℕ → Log → Log → Prop}
    {Bg : Log → Log → Prop} (hBg : T4.Reads 99 Bg)
    (hprev : Dk (phOf4 98) = fun L es => Bg L es ∨ ¬ truthS truthSN zw L es)
    (hfin : Dk (phOf4 99) = msD (Dk (phOf4 98)) (fun L es => Bg L es ∨ S2Bad wN zw L es) 98 15)
    (L es₀ : Log) (hl : es₀.length = 99) :
    condCount (DPos (T4.Dp Dk)) L es₀ 15 [] ≤ deltaR := by
  set κ := kindOfC es₀
  have hn := nbC_le κ
  have hJ : 1 ≤ nJ4 hN κ := by unfold nJ4; split_ifs; exact hN.nJ_pos κ; norm_num
  have hJ' : nbC κ + 10 + (nJ4 hN κ - 1) ≤ 239 := by
    unfold nJ4; split_ifs; exact hN.nJ_le κ; omega
  by_cases hd : ¬ truthS truthSN zw L es₀
  · obtain ⟨j, hj, hne, hL⟩ := tr_ne4 hN hd
    have h0 : DoomS (nbC κ) (nJ4 hN κ) (TR4 hN κ L es₀) [] := by
      unfold DoomS
      rw [if_pos (by simp)]
      refine ⟨j, hj, ?_⟩
      have hs : selC (nbC κ) ([] : List F) = [] := by simp [selC]
      unfold mlDoom
      rw [hs]
      exact hne
    refine (seq_round_le hl (DoomS (nbC κ) (nJ4 hN κ) (TR4 hN κ L es₀)) (bS (nbC κ) (nJ4 hN κ))
      (fun l hdl => doomS_step hn hJ (TR4_size hN κ L es₀) l hdl) h0 fun as has he => ?_).trans
      (coord_le_deltaR ?_)
    · obtain ⟨-, -, hnf⟩ := T4.esc_msD_frame s_unit_pos4.1 hBg hprev hfin hl as has he
      set X := ext es₀ as
      obtain ⟨ys, hy⟩ := T4.ext_eq_append es₀ as
      have hS : T4.Same L X L es₀ 99 := by
        rw [show X = es₀ ++ ys from hy, ← hl]; exact T4.same_append L es₀ ys
      have hk : kindOfC X = κ := hS.kind (by norm_num)
      have hLX : (kindOfC X).isNode = false → lastL X < 2 ^ nbC (kindOfC X) := by
        rw [hk, lastL_congr hS.1 (by norm_num)]; exact hL
      have hres := trueSum_TS4 hN (L := L) hLX
      rw [not_not.mp hnf |>.symm] at hres
      have hr0 := add_eq_left.mp hres.symm
      rw [hk, resS4_same hN hz hS le_rfl] at hr0
      unfold resSum at hr0
      unfold DoomS
      rw [if_neg (by simp), not_not]
      simp only [TR4_mle]
      rw [(selC_coords4 κ X).1, (selC_coords4 κ X).2, coordS_getD X (by norm_num : 28 < 30)]
      exact hr0
    · rw [sum_bS hn]; exact hJ'
  · rw [condCount_eq_zero fun as has he =>
      hd (T4.esc_msD_frame s_unit_pos4.1 hBg hprev hfin hl as has he).2.1]
    exact zero_le

end FR.Snd.P4a
