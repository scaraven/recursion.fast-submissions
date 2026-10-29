-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.3, A.9, §5.1; track R4g). The 3.x template is
-- `FRSoundnessAccCol` (`capDig_eq`, `ys_facts`) with `FRSoundnessAccPf.lvl_facts`.
import FRSoundness4R4Qv

/-!
# `FinRest4.cols`: P2.i's opened columns on the log

* **`lv_facts4`**: the kind's ladder against `seq4`'s (the same `t` and `ell`, no deeper Merkle
  path, no larger cap, the P2 squeezes cover the positions); **`lvK_eq4`**: the program's kind
  level `seq4.lvK m i` is T4's `lvOf m i`.
* Table certificates (`decide +kernel` on `seq4`'s tables): the level phases (`phases4_lvl`),
  the cap messages (`capMsg4`), the columns inside π (`colsEnd4`).
* **`capDig_eq4`**: level `i`'s cap entry on the log is π's 32 bytes where `posOps4` compares.
* **`ys_facts4`** (3.x's `ys_facts`): the fold registers `yReg4 p i q` hold
  `Σ_r eq(sᵢ, r)·col_q[r]`, with a path on the log from `col_q` at `qPos` to its cap entry.
* **`cols4_of_run`**: `FinRest4.cols` for `yv4`, the fold registers' values.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Merkle Finset

/-! ## Levels and tables -/

theorem lvK_eq4 (m i : ℕ) : seq4.lvK m i = lvOf m i := by
  rw [seq4_eq]; rfl

theorem lv_facts4 {m : ℕ} (hm : m = 30 ∨ m = 31 ∨ m = 32) {i : ℕ} (hi : i < 5) :
    (lvOf m i).t = (seq4.lv i).t ∧ (lvOf m i).sib ≤ (seq4.lv i).sib ∧
      (lvOf m i).cap ≤ (lvOf m i).logN ∧ (lvOf m i).cap ≤ (seq4.lv i).cap ∧
      ((lvOf m i).t - 1) / (lvOf m i).per < (seq4.lv i).sq ∧ 0 < (lvOf m i).per ∧
      (lvOf m i).ell = hEll i ∧ 2 ^ hEll i ≤ colBytes i / 16 ∧ 0 < (seq4.lv i).sq ∧
      0 < (lvOf m i).t := by
  rw [seq4_eq]; rcases hm with rfl | rfl | rfl <;> interval_cases i <;> decide

/-- Level `i`'s phases P1, C, P2, Q in `seq4`'s table. -/
theorem phases4_lvl {i : ℕ} (hi : i < 5) :
    (phasesOf seq4)[27 + 5 * i]? = some ("C", .absorb (capField i) (capBytesOf seq4 i)) ∧
      (phasesOf seq4)[28 + 5 * i]? = some ("P2", .squeezes (seq4.lv i).sq (.pos i)) ∧
      (phasesOf seq4)[29 + 5 * i]? = some ("Q", .queries i) := by
  interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem phStart4_P2 {i : ℕ} (hi : i < 5) : phStart4 (28 + 5 * i) = phStart4 (27 + 5 * i) + 1 := by
  rw [phStart4, phStart4, fsStarts4_eq]; interval_cases i <;> rfl

/-- **The cap messages** (a table certificate): level `i`'s cap is absorbed at `capPos i`, from
the caps field at `capOff4 seq4 i`. -/
theorem capMsg4 {i : ℕ} (hi : i < 5) :
    (fsMsgs4 seq4).getD (T4.capPos i) none =
      some (fieldOffOf seq4 fCaps + capOff4 seq4 i, 2 ^ (seq4.lv i).cap * 32) := by
  rw [T4.capPos, phStart4, phStart4, fsStarts4_eq, fsMsgs4, capOff4, fieldOffOf, seq4_eq]
  interval_cases i <;> decide +kernel

/-- **The columns lie inside π** (a table certificate). -/
theorem colsEnd4 {i : ℕ} (hi : i < 5) :
    fieldOffOf seq4 fCols + phaseOffOf seq4 (29 + 5 * i) fCols + (seq4.lv i).t * colBytes i ≤
      piSizeOf seq4 := by
  rw [fieldOffOf, phaseOffOf, piSizeOf, seq4_eq]
  interval_cases i <;> decide +kernel

/-! ## The caps and the folds on an accepted run -/

section Run
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- **Level `i`'s cap entry on the log is π's** where `posOps4` compares (3.x's `capDig_eq`). -/
theorem capDig_eq4 (h : SkRun4 impl p inp tr y) {i : ℕ} (hi : i < 5) {e : ℕ}
    (he : e < 2 ^ (seq4.lv i).cap) :
    T4.capDig (fsOf tr (itemsOf seq4)) i e =
      bytesAt inp.π (fieldOffOf seq4 fCaps + capOff4 seq4 i + 32 * e) 32 := by
  have hp : T4.capPos i < 482 ∧ T4.capPos i ≠ 0 := by
    rw [T4.capPos, phStart4, phStart4, fsStarts4_eq]; interval_cases i <;> decide
  have e1 := h.hq _ hp.1
  rw [capMsg4 hi] at e1
  simp only [qOf, hp.2, if_false] at e1
  have h32 := Nat.mul_le_mul_right 32 (Nat.succ_le_of_lt he)
  rw [T4.capDig, msgAt_of_q e1, bytesAt_extract_of_le inp.π (by rw [Nat.succ_mul] at h32; omega)]

/-- The fold register of query `q` of level `i` (Q.i's outs). -/
def yReg4 (p : KindP) (i q : ℕ) : Reg := ((skeleton4 seq4 p).2.outs.getD (29 + 5 * i) []).getD q 0

/-- **The column folds** (`FinRest4`'s `y`): the fold registers' values. -/
def yv4 (p : KindP) (R : Array Val) (i q : ℕ) : K := (rd R (yReg4 p i q)).toK

/-- **Q.i's folds on the log** (3.x's `ys_facts`): the fold register of query `q` holds
`Σ_r eq(sᵢ, r)·col_q[r]`, and `col_q` has a path on `L` from `qPos` to its cap entry. -/
theorem ys_facts4 (h : SkRun4 impl p inp tr y) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) (hπ : inp.π.size = piSizeOf seq4)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {i : ℕ} (hi : i < 5) :
    ∀ q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).t, ∃ col : ByteArray, ∃ ss : List Digest,
      ss.length = (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).sib ∧
      (openPath (frEnc i) col (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) i q) ss).runLog L =
        some (T4.capDig (fsOf tr (itemsOf seq4)) i
          (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) i q /
            2 ^ (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).sib)) ∧
      rd (#[] ++ y.1.toArray) (yReg4 p i q) =
        .k (∑ r : Fin (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).rows,
          eqBits (T4.sAt (fsOf tr (itemsOf seq4)) i) (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).ell r *
            algebraMap F K (readF col (16 * r))) := by
  set es := fsOf tr (itemsOf seq4)
  set κ := kindOfC es
  set R := #[] ++ y.1.toArray with hRd
  have hLk : CKind.lv κ i = lvOf κ.m i := rfl
  obtain ⟨hT, hsib, hcapN, hcap, hper, hper0, hell, hcol, hsq0, -⟩ := lv_facts4 (CKind.m_mem κ) hi
  rw [← hLk] at hT hsib hcapN hcap hper hper0 hell
  have hK : seq4.lvK p.d.m i = CKind.lv κ i := by rw [hm, lvK_eq4]; rfl
  obtain ⟨hC, hP2, hQ⟩ := phases4_lvl hi
  obtain ⟨hnC, eC⟩ := ph4 hC
  obtain ⟨hnP, eP⟩ := ph4 hP2
  obtain ⟨hnQ, eQ⟩ := ph4 hQ
  obtain ⟨hn1, e1⟩ := ph4 (phases4_p1 seq4 hi)
  -- P1.i: its challenge registers
  set fi0 : FinIn := ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
  have hfi0 : fi0.outs = (skeleton4 seq4 p).2.outs := rfl
  obtain ⟨b1, hout1, hsv, -⟩ := p1_view4 h hfi0 hi
  have hb1 : b1 = (cAt4 seq4 p (26 + 5 * i)).next := by
    rw [lvOuts_eq4 hfi0, skeleton4_outs seq4 p hn1, e1, genPhase4_roundsK seq4 p _ "P1" fP1 _ _ rfl
      (by rw [seq4_ell hi]; unfold hEll; interval_cases i <;> decide)] at hout1
    have := congrArg List.head? hout1
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at this
    omega
  -- the context at Q.i
  have hcQ : cAt4 seq4 p (29 + 5 * i) =
      (genPhase4 seq4 p (28 + 5 * i) ("P2", .squeezes (seq4.lv i).sq (.pos i)) (cAt4 seq4 p (28 + 5 * i))).2 := by
    rw [show 29 + 5 * i = 28 + 5 * i + 1 by ring, cAt4_succ seq4 p hnP, eP]
  have hcP : cAt4 seq4 p (28 + 5 * i) =
      (genPhase4 seq4 p (27 + 5 * i) ("C", .absorb (capField i) (capBytesOf seq4 i)) (cAt4 seq4 p (27 + 5 * i))).2 := by
    rw [show 28 + 5 * i = 27 + 5 * i + 1 by ring, cAt4_succ seq4 p hnC, eC]
  have hc1 : cAt4 seq4 p (27 + 5 * i) =
      (genPhase4 seq4 p (26 + 5 * i) ("P1", .rounds fP1 (seq4.lv i).ell 2 true) (cAt4 seq4 p (26 + 5 * i))).2 := by
    rw [show 27 + 5 * i = 26 + 5 * i + 1 by ring, cAt4_succ seq4 p hn1, e1]
  have hfR : (cAt4 seq4 p (29 + 5 * i)).foldR = (List.range (hEll i)).map (fun j => b1 + 13 * j + 6) := by
    rw [hcQ, (genPhase4_pos_ctx ..).1, hcP, (genPhase4_absorb_ctx ..).1, hc1,
      genPhase4_roundsK_foldR _ _ _ _ _ rfl, seq4_ell hi, hb1]
  have hpA : (cAt4 seq4 p (29 + 5 * i)).posAns = (List.range (seq4.lv i).sq).map ((cAt4 seq4 p (28 + 5 * i)).next + ·) := by
    rw [hcQ, (genPhase4_pos_ctx ..).2.1]
  obtain ⟨-, -, hans⟩ := pos_view4 h hnP (by rw [eP]) hsq0
  obtain ⟨bQ, houtQ, -, hQv⟩ := queries_view4 h hL hin hnQ (by rw [eQ]) (by rw [hK]; exact hsib)
  intro q hq
  have hq' : q < (seq4.lv i).t := hT ▸ hq
  obtain ⟨hidx, hy, ss, hss, hpath⟩ := hQv q hq'
  have hgy : yReg4 p i q = bQ + 2 + posW4 seq4 i * q + 3 := by
    rw [yReg4, houtQ, List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range]
  have hfr : ((cAt4 seq4 p (29 + 5 * i)).foldR.map fun x => (rd R x).toK) =
      (List.range (hEll i)).map (T4.sAt es i) := by
    rw [hfR, List.map_map]
    exact List.map_congr_left fun j hj => by
      simp only [Function.comp_apply]; rw [hsv j (List.mem_range.1 hj)]; rfl
  have hqp : q / (CKind.lv κ i).per < (seq4.lv i).sq :=
    lt_of_le_of_lt (Nat.div_le_div_right (by omega)) hper
  have hj : idxOf (CKind.lv κ i).logN ((rd R ((cAt4 seq4 p (29 + 5 * i)).posAns.getD
      (q / (CKind.lv κ i).per) 0)).toD) (q % (CKind.lv κ i).per) = T4.qPos κ es i q := by
    rw [hpA, List.getD_eq_getElem _ _ (by simpa using hqp), List.getElem_map, List.getElem_range,
      hans _ hqp, T4.qPos, posAt, phStart4_P2 hi]
    rfl
  simp only [hK, ← hRd] at hidx hy hpath hss
  simp only [hj, hfr] at hy hpath
  have hqlt : T4.qPos κ es i q < 2 ^ (CKind.lv κ i).logN := idx_lt _ _ _
  have hcb : T4.qPos κ es i q / 2 ^ (CKind.lv κ i).sib < 2 ^ (seq4.lv i).cap := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_le hqlt (Nat.pow_le_pow_right (by norm_num) (by unfold Level.sib; omega))
  set col := inp.π.extract (absOff 0 (fieldOffOf seq4 fCols + phaseOffOf seq4 (29 + 5 * i) fCols +
      q * colBytes i)) (absOff 0 (fieldOffOf seq4 fCols + phaseOffOf seq4 (29 + 5 * i) fCols +
      q * colBytes i) + colBytes i) with hcold
  have hsz : col.size = colBytes i := by
    have h1 := colsEnd4 hi
    have h2 : q * colBytes i + colBytes i ≤ (seq4.lv i).t * colBytes i := by
      have := Nat.mul_le_mul_right (colBytes i) (show q + 1 ≤ (seq4.lv i).t by omega)
      rwa [Nat.add_mul, one_mul] at this
    rw [hcold, ByteArray.size_extract, absOff_zero, hπ]; omega
  refine ⟨col, ss, hss, ?_, ?_⟩
  · rw [hpath, absOff_zero, Nat.shiftRight_eq_div_pow, capDig_eq4 h hi hcb]
  · clear_value col
    have hs : ((List.range (hEll i)).map (T4.sAt es i)).toArray.size = hEll i := by simp
    have e1 := dotKF_eq_sum ((List.range (hEll i)).map (T4.sAt es i)).toArray col
      (by rw [hs, hsz]; exact hcol)
    rw [hs] at e1
    have e2 : (∑ r : Fin (CKind.lv κ i).rows, eqBits (T4.sAt es i) (CKind.lv κ i).ell r *
        algebraMap F K (readF col (16 * r))) = ∑ r ∈ range (2 ^ hEll i),
          eqBits (fun v => ((List.range (hEll i)).map (T4.sAt es i)).toArray.getD v 0)
            (hEll i) r * algebraMap F K (readF col (16 * r)) := by
      rw [Fin.sum_univ_eq_sum_range (fun r => eqBits (T4.sAt es i) (CKind.lv κ i).ell r *
        algebraMap F K (readF col (16 * r))), Level.rows, hell]
      refine sum_congr rfl fun r _ => ?_
      rw [eqBits_congr (r' := fun v => ((List.range (hEll i)).map (T4.sAt es i)).toArray.getD
        v 0) (fun v hv => by simp [Array.getD_eq_getD_getElem?, hv])]
    rw [hgy, hy, e1, ← e2]

/-- **`FinRest4.cols`** for the fold registers' values `yv4` (the log repeats no query). -/
theorem cols4_of_run (h : SkRun4 impl p inp tr y) {L : Log} (hb : ¬ Bad L) (hin : ∀ e ∈ tr, e ∈ L)
    (hπ : inp.π.size = piSizeOf seq4) (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) :
    ∀ i < 5, ∀ q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).t, ∃ col : ByteArray, ∃ ss : List Digest,
      ss.length = (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).sib ∧
      (openPath (frEnc i) col (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) i q) ss).runLog L =
        some (T4.capDig (fsOf tr (itemsOf seq4)) i
          (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) i q /
            2 ^ (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).sib)) ∧
      yv4 p (#[] ++ y.1.toArray) i q = ∑ r : Fin (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).rows,
        eqBits (T4.sAt (fsOf tr (itemsOf seq4)) i) (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).ell r *
          algebraMap F K (readF col (16 * r)) := by
  have hL : (L.map Prod.fst).Nodup := by by_contra hr; exact hb (.inr (.inr (.inr hr)))
  intro i hi q hq
  obtain ⟨col, ss, hss, hpath, hy⟩ := ys_facts4 h hL hin hπ hm hi q hq
  exact ⟨col, ss, hss, hpath, by rw [yv4, hy]; rfl⟩

/-- The program's kind is the chain's: a segment's. -/
theorem dm_seg4 {σ : SegKind} (h : SkRun4 impl (.ofSeg σ) inp tr y) :
    (KindP.ofSeg σ).d.m = (kindOfC (fsOf tr (itemsOf seq4))).m := by
  rw [kindOfC_seg4 h]; cases σ <;> rfl

/-- … and a node's. -/
theorem dm_node4 {ν : NodeKind} (h : SkRun4 impl (.ofNode ν) inp tr y) :
    (KindP.ofNode ν).d.m = (kindOfC (fsOf tr (itemsOf seq4))).m := by
  rw [kindOfC_node4 h]; cases ν <;> rfl

end Run

end FR.Snd.R4
