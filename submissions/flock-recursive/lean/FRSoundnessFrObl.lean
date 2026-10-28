-- New for `flock-recursive` (BLUEPRINT A.10, §5.1–§5.2; stage S-G9).
import FRSoundnessFrStab

/-!
# `FrontObl` for the front's `DF`

* **`frontCls_check`**: one checked classification of positions `0 … 317` (by item): every
  absorb is a phase boundary of `absPts` or an absorb of a rounds phase of `rndPh`; every single
  squeeze is one of `sqPts` or a squeeze of a rounds phase; each with its phases.
* **`frontObl`**: `FrontObl (RejF …) (DF …) W₀L c₀L`, from the phase lemmas of S-G5 … S-G8.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## The classification -/

/-- The boundary absorbs `(p, phOf (p − 1), phOf p)`. -/
def absPts : List (ℕ × ℕ × ℕ) := [(1, 0, 1), (2, 1, 2), (13, 3, 4), (15, 4, 5), (67, 5, 6),
  (69, 7, 8), (97, 8, 9), (114, 11, 12), (178, 13, 14), (208, 14, 15), (221, 17, 18),
  (263, 18, 19), (265, 20, 21), (311, 21, 22), (312, 22, 23)]

/-- The single squeezes outside a rounds phase `(p, phOf (p − 1), phOf p)`. -/
def sqPts : List (ℕ × ℕ × ℕ) := [(14, 4, 4), (68, 6, 7), (98, 9, 10), (209, 15, 16),
  (264, 19, 20), (317, 24, 25)]

/-- The rounds phases `(b, end, k)`: absorbs at `b + 2j`, squeezes at `b + 2j + 1`, `b < p < end`. -/
def rndPh : List (ℕ × ℕ × ℕ) := [(15, 67, 5), (69, 97, 8), (114, 170, 12), (178, 208, 14),
  (221, 263, 18), (265, 311, 21)]

def ptCls (P : List (ℕ × ℕ × ℕ)) (p : ℕ) : Bool :=
  P.any fun x => p == x.1 && phOf (p - 1) == x.2.1 && phOf p == x.2.2

def rndCls (par p : ℕ) : Bool :=
  rndPh.any fun x => decide (x.1 < p) && decide (p < x.2.1) && (p - x.1) % 2 == par &&
    phOf (p - 1) == x.2.2 && phOf p == x.2.2

/-- **A position's class** by its item. -/
def frontCls (p : ℕ) : Item → Bool
  | .squeeze => fsRnd p != none || ptCls sqPts p || rndCls 1 p
  | .absorb _ => ptCls absPts p || rndCls 0 p
  | _ => true

/-- **Checked: every position before P1.0 has its class.** -/
theorem frontCls_check : ((fsItems.take 318).zipIdx).all (fun x => frontCls x.2 x.1) = true := by
  unfold frontCls ptCls rndCls absPts sqPts rndPh phOf fsRnd
  rw [fsStarts_eq, fsRanges_eq]; decide +kernel

theorem frontCls_of {p : ℕ} {it : Item} (hp : p < 318) (h : fsItems[p]? = some it) :
    frontCls p it = true := by
  have hc := frontCls_check
  rw [List.all_eq_true] at hc
  exact hc (it, p) (List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_take, hp, h]))

theorem abs_cls {p len : ℕ} (hp : p < 318) (h : fsItems[p]? = some (.absorb len)) :
    (∃ x ∈ absPts, p = x.1 ∧ phOf (p - 1) = x.2.1 ∧ phOf p = x.2.2) ∨
    ∃ x ∈ rndPh, x.1 < p ∧ p < x.2.1 ∧ (p - x.1) % 2 = 0 ∧ phOf (p - 1) = x.2.2 ∧
      phOf p = x.2.2 := by
  have hc := frontCls_of hp h
  simp only [frontCls, ptCls, rndCls, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hc
  rcases hc with ⟨x, hx, ⟨h1, h2⟩, h3⟩ | ⟨x, hx, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact Or.inl ⟨x, hx, h1, h2, h3⟩
  · exact Or.inr ⟨x, hx, h1, h2, h3, h4, h5⟩

theorem sq_cls {p : ℕ} (hp : p < 318) (h : fsItems[p]? = some .squeeze) (hr : fsRnd p = none) :
    (∃ x ∈ sqPts, p = x.1 ∧ phOf (p - 1) = x.2.1 ∧ phOf p = x.2.2) ∨
    ∃ x ∈ rndPh, x.1 < p ∧ p < x.2.1 ∧ (p - x.1) % 2 = 1 ∧ phOf (p - 1) = x.2.2 ∧
      phOf p = x.2.2 := by
  have hc := frontCls_of hp h
  simp only [frontCls, ptCls, rndCls, hr, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, bne_self_eq_false, Bool.false_eq_true, false_or] at hc
  rcases hc with ⟨x, hx, ⟨h1, h2⟩, h3⟩ | ⟨x, hx, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact Or.inl ⟨x, hx, h1, h2, h3⟩
  · exact Or.inr ⟨x, hx, h1, h2, h3, h4, h5⟩

/-- The absorbs the checks' `RejOK`s ask about (checked against the classification). -/
def nsqPts : List ℕ := [67, 97, 263, 311, 312] ++ (List.range 14).map (69 + 2 * ·) ++
  (List.range 28).map (114 + 2 * ·) ++ (List.range 23).map (265 + 2 * ·)

theorem nsq_check : nsqPts.all (fun p => decide (p < 318) && !frontCls p .squeeze) = true := by
  unfold nsqPts frontCls ptCls rndCls absPts sqPts rndPh phOf fsRnd
  rw [fsStarts_eq, fsRanges_eq]; decide +kernel

theorem nsq {p : ℕ} (hp : p ∈ nsqPts) : fsItems[p]? ≠ some .squeeze := fun h => by
  have hc := nsq_check
  rw [List.all_eq_true] at hc
  have := hc p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
  rw [frontCls_of this.1 h] at this
  exact Bool.noConfusion this.2

theorem nsq_mem : 67 ∈ nsqPts ∧ 97 ∈ nsqPts ∧ 263 ∈ nsqPts ∧ 311 ∈ nsqPts ∧ 312 ∈ nsqPts ∧
    (∀ j < 14, 69 + 2 * j ∈ nsqPts) ∧ (∀ j < 28, 114 + 2 * j ∈ nsqPts) ∧
    ∀ j < 23, 265 + 2 * j ∈ nsqPts := by
  refine ⟨by simp [nsqPts], by simp [nsqPts], by simp [nsqPts], by simp [nsqPts],
    by simp [nsqPts], fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩ <;>
  simp only [nsqPts, List.mem_append, List.mem_map, List.mem_range]
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩))
  · exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
  · exact Or.inr ⟨j, hj, rfl⟩

theorem ph_vals : phOf 2 = 2 ∧ phOf 3 = 3 ∧ phOf 98 = 10 ∧ phOf 99 = 11 ∧ phOf 169 = 12 ∧
    phOf 170 = 13 ∧ phOf 209 = 16 ∧ phOf 210 = 17 ∧ phOf 312 = 23 ∧ phOf 313 = 24 := by
  simp only [phOf, fsStarts_eq]; decide

/-! ## The checks -/

variable {fin : Finals} {oLc : Kind → Log → F → Prop} {RejN L3N PendN : Log → Log → Prop}

theorem rejF_ok (hN : NodeLF oLc RejN L3N PendN) : RejOK (RejF fin oLc RejN) := by
  obtain ⟨n67, n97, n263, n311, n312, nL2, nS2, nE4⟩ := nsq_mem
  exact rejOK_or (rejZ_ok (nsq n67)) (rejOK_or (rejL2_ok fun j hj => nsq (nL2 j hj))
    (rejOK_or (rejLc2_ok zlmFR (nsq n97)) (rejOK_or (rejS2_ok fun j hj => nsq (nS2 j hj))
    (rejOK_or lr_rejEnd_ok (rejOK_or (e_rejEnd_ok (nsq n263))
    (rejOK_or (rejInE_ok fun j hj => nsq (nE4 j hj)) (rejOK_or (rejE4_ok fin (nsq n311))
    (rejOK_or (rejRS_ok (okF_reads hN.okReads) (nsq n312)) hN.rej))))))))

/-! ## The backgrounds read before their phases -/

theorem rd_far0 : Reads 3 far0 := reads_of_same fun _ _ _ _ h => by
  unfold far0; rw [h.kind (by norm_num)]; exact farL0_same h le_rfl _
theorem rd_nPub : Reads 3 nPub := reads_of_same fun _ _ _ _ h => by
  unfold nPub; rw [h.kind (by norm_num)]; exact (pubOK_same h le_rfl _).not
theorem rd_nS : Reads 3 nS := reads_of_same fun _ _ _ _ h => (truthS_same h le_rfl).not
theorem rd_A : Reads 3 fun L es => far0 L es ∨ nPub L es ∨ nLr L es ∨ nE fin L es :=
  rd_far0.or (rd_nPub.or (rowsBad_reads.or rowsBad_reads))
theorem rd_bgZ : Reads 3 (bgZ fin) := rd_A.or rd_nS
theorem rd_bg5 : Reads 15 (bg5 fin) := (rd_bgZ.mono (by norm_num)).or pendZ_reads
theorem rd_bg10 (hP : Reads 99 PendN) : Reads 99 (bg10 fin PendN) :=
  (rd_A.mono (by norm_num)).or ((pendZ_reads.mono (by norm_num)).or (pendLc_reads.or hP))
theorem rd_bg20 (hP : Reads 99 PendN) : Reads 170 (bg20 PendN) :=
  (rd_far0.mono (by norm_num)).or ((rd_nPub.mono (by norm_num)).or ((pendZ_reads.mono
    (by norm_num)).or ((pendLc_reads.mono (by norm_num)).or ((hP.mono (by norm_num)).or
    D2S_reads))))
theorem rd_bg12 (hP : Reads 99 PendN) : Reads 170 (bg12 fin PendN) :=
  (rd_bg20 hP).or (rowsBad_reads.mono (by norm_num))
theorem rd_bg16 (hP : Reads 99 PendN) : Reads 210 (bg16 PendN) :=
  ((rd_bg20 hP).mono (by norm_num)).or (batBad_reads (rows := Layout.lRows) (a := 15) (nc := 23)
    (on := lrOn) (b2 := 178) (by norm_num))

open Classical in
/-- **The frame at a single squeeze**, up to rearranging the doom: a background that reads before
the squeeze never escapes. -/
theorem card_frame2 {D D' Bg U U' : Log → Log → Prop} {p : ℕ} (hBg : Reads p Bg) {L es : Log}
    (hp : p ≤ es.length) (h1 : D L es → Bg L es ∨ U L es)
    (h2 : ∀ a, Bg L (ext1 es a) ∨ U' L (ext1 es a) → D' L (ext1 es a)) :
    (univ.filter fun a => D L es ∧ ¬ D' L (ext1 es a)).card ≤
      (univ.filter fun a => U L es ∧ ¬ U' L (ext1 es a)).card := by
  refine card_le_card fun a ha => ?_
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  refine ⟨(h1 ha.1).resolve_left fun hb => ha.2 (h2 a (Or.inl ((hBg.ext1 L es a hp).mpr hb))),
    fun hu => ha.2 (h2 a (Or.inr hu))⟩

open Classical in
theorem card_or_le {A B C D : Digest → Prop} :
    (univ.filter fun a => (A a ∨ B a) ∧ ¬ (C a ∨ D a)).card ≤
      (univ.filter fun a => A a ∧ ¬ C a).card + (univ.filter fun a => B a ∧ ¬ D a).card := by
  refine (card_le_card fun a ha => ?_).trans (card_union_le _ _)
  simp only [mem_filter, mem_univ, true_and, mem_union, not_or] at ha ⊢
  rcases ha.1 with h | h
  · exact Or.inl ⟨h, ha.2.1⟩
  · exact Or.inr ⟨h, ha.2.2⟩

/-! ## `habs` -/

theorem p1Start_zero : p1Start 0 = 318 := by
  simp only [p1Start, phStart, fsStarts_eq]; rfl

/-- **`FrontObl.habs`**: at every absorb before P1.0, the doom of the previous position gives a
failed check or the next position's doom. -/
theorem obl_habs (hN : NodeLF oLc RejN L3N PendN) (L es : Log) (x : ByteArray × Digest) (len : ℕ)
    (hit : fsItems[es.length]? = some (.absorb len)) (hp : es.length < p1Start 0)
    (hd : DF fin L3N PendN (phOf (es.length - 1)) L es) :
    RejC (RejF fin oLc RejN) c₀L L (es ++ [x]) ∨ DF fin L3N PendN (phOf es.length) L (es ++ [x]) := by
  rw [p1Start_zero] at hp
  have ap := fun {P : Log → Log → Prop} {q : ℕ} (h : Reads q P) (hq : q ≤ es.length) =>
    h.append L es [x] hq
  rcases abs_cls hp hit with ⟨⟨q, a, b⟩, hy, he, h1, h2⟩ | ⟨⟨q, e, k⟩, hy, hb, he, hpar, h1, h2⟩
  · simp only [absPts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at he h1 h2
    rw [h1] at hd; rw [h2]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩
    · simp [DF] at hd
    · simp [DF] at hd
    · -- 13: Z1's end into Z2
      simp only [DF, msD, if_neg (show ¬ es.length ≤ 2 + 10 by omega)] at hd
      right; simp only [DF]
      rcases hd with h | h
      · exact Or.inl ((ap rd_bgZ (by omega)).mpr h)
      · exact Or.inr (z2_habs x he h)
    · -- 15: Z2 into Z3
      simp only [DF, Z2D, if_neg (show ¬ es.length ≤ 14 by omega)] at hd
      right; simp only [DF, bg5]
      rcases hd with h | h
      · exact Or.inl (Or.inl ((ap rd_bgZ (by omega)).mpr h))
      · rcases z3_habs x he h with h' | h'
        · exact Or.inr h'
        · exact Or.inl (Or.inr h')
    · -- 67: Zend
      simp only [DF] at hd
      rcases hd with h | h
      · right; simp only [DF]; exact Or.inl ((ap rd_bg5 (by omega)).mpr h)
      · rcases zend_habs x he h with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · right; simp only [DF]; exact Or.inr h'
    · -- 69: L1 into L2
      simp only [DF] at hd
      right; simp only [DF]
      rcases hd with h | h
      · exact Or.inl ((ap rd_bg5 (by omega)).mpr h)
      · exact Or.inr (l2_habs x he h)
    · -- 97: L3
      simp only [DF] at hd
      rcases hd with h | h
      · right; simp only [DF]; exact Or.inl ((ap rd_bg5 (by omega)).mpr h)
      · by_cases hn : (kindOf es).isNode = true
        · rcases hN.habs L es x he hn h with h' | h'
          · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr h'))))))))))
          · right; simp only [DF]; exact Or.inr (Or.inr h')
        · rcases l3_habs x he (by simpa using hn) h with h' | h'
          · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h'))))
          · right; simp only [DF]; exact Or.inr (Or.inl h')
    · -- 114: S1's end into S2
      simp only [DF, msD, if_neg (show ¬ es.length ≤ 98 + 15 by omega)] at hd
      right; simp only [DF, D12F, bg12, bg20]
      rw [ap rd_far0 (by omega), ap rd_nPub (by omega), ap pendZ_reads (by omega),
        ap pendLc_reads (by omega), ap hN.pendReads (by omega),
        ap (show Reads 3 (nE fin) from rowsBad_reads) (by omega),
        ap (show Reads 3 nLr from rowsBad_reads) (by omega)]
      simp only [bg10] at hd
      rcases hd with ((h | h | h | h) | h | h | h) | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (habs_S2 x he h)))))))
    · -- 178: Lr1's end into Lr2
      simp only [DF, msD, if_neg (show ¬ es.length ≤ 169 + 8 by omega)] at hd
      right; simp only [DF]
      rcases hd with h | h
      · exact Or.inl ((ap (rd_bg12 hN.pendReads) (by omega)).mpr h)
      · exact Or.inr (lr_habs_outer x he h)
    · -- 208: Lr end
      simp only [DF] at hd
      rcases hd with h | h
      · right; simp only [DF]; exact Or.inl ((ap (rd_bg12 hN.pendReads) (by omega)).mpr h)
      · rcases lr_habs_end x he h with h' | h'
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))
        · right; simp only [DF]; exact Or.inr h'
    · -- 221: E1's end into E2
      simp only [DF, msD, if_neg (show ¬ es.length ≤ 209 + 11 by omega)] at hd
      right; simp only [DF]
      rcases hd with h | h
      · exact Or.inl ((ap (rd_bg16 hN.pendReads) (by omega)).mpr h)
      · exact Or.inr (e_habs_outer (Layout.nodeRows fin) x he h)
    · -- 263: E end
      simp only [DF] at hd
      rcases hd with h | h
      · right; simp only [DF]; exact Or.inl ((ap (rd_bg16 hN.pendReads) (by omega)).mpr h)
      · rcases e_habs_end (Layout.nodeRows fin) x he h with h' | h'
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))))
        · right; simp only [DF]; exact Or.inr h'
    · -- 265: E3 into E4
      simp only [DF] at hd
      right; simp only [DF]
      rcases hd with h | h
      · exact Or.inl ((ap (rd_bg20 hN.pendReads) (by omega)).mpr h)
      · exact Or.inr (habs_innerE x he h)
    · -- 311: E4 end
      simp only [DF] at hd
      rcases hd with h | h
      · right; simp only [DF]; exact Or.inl ((ap (rd_bg20 hN.pendReads) (by omega)).mpr h)
      · rcases habs_E4end x he h with h' | h'
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl h')))))))))
        · right; simp only [DF]; exact Or.inr h'
    · -- 312: RS0
      rcases habs_RS0 (okF_reads hN.okReads) x he (dPend_of hN (by omega) hd) with h' | h'
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl h'))))))))))
      · right; simp only [DF]; exact h'
  · simp only [rndPh, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at hb he hpar h1 h2
    rw [h1] at hd; rw [h2]; right
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [DF] at hd ⊢
      exact hd.imp (ap rd_bg5 (by omega)).mpr
        (D3_append_iff (by norm_num) TZ_local x (by omega) (Or.inl hpar)).mpr
    · simp only [DF] at hd ⊢
      exact hd.imp (ap rd_bg5 (by omega)).mpr
        (D2_append_iff (by norm_num) TL_local x (by omega) (Or.inl hpar)).mpr
    · simp only [DF, D12F, bg12, bg20] at hd ⊢
      rw [ap rd_far0 (by omega), ap rd_nPub (by omega), ap pendZ_reads (by omega),
        ap pendLc_reads (by omega), ap hN.pendReads (by omega),
        ap (show Reads 3 (nE fin) from rowsBad_reads) (by omega),
        ap (show Reads 3 nLr from rowsBad_reads) (by omega), append_S2 x (by omega) (Or.inl hpar)]
      exact hd
    · simp only [DF] at hd ⊢
      exact hd.imp (ap (rd_bg12 hN.pendReads) (by omega)).mpr (outer_append (rows := Layout.lRows)
        (a := 15) (nc := 23) (on := lrOn) (s0 := 169) (by norm_num) (by norm_num) x (by omega)
        (Or.inl hpar)).mpr
    · simp only [DF] at hd ⊢
      exact hd.imp (ap (rd_bg16 hN.pendReads) (by omega)).mpr (outer_append
        (rows := Layout.nodeRows fin) (a := 21) (nc := 23) (on := lrOn) (s0 := 209) (by norm_num)
        (by norm_num) x (by omega) (Or.inl hpar)).mpr
    · simp only [DF] at hd ⊢
      exact hd.imp (ap (rd_bg20 hN.pendReads) (by omega)).mpr
        (inner_appendE x (by omega) (Or.inl hpar)).mpr

/-! ## `hsingle` -/

open Classical in
/-- **`FrontObl.hsingle`**: at every single squeeze before P1.0, at most `239·2^128` answers escape
(the largest is Z2's `126`). -/
theorem obl_single (hN : NodeLF oLc RejN L3N PendN) (L es : Log)
    (hit : fsItems[es.length]? = some .squeeze) (hrnd : fsRnd es.length = none)
    (hp : es.length < p1Start 0) (hr : ¬ RejC (RejF fin oLc RejN) c₀L L es) :
    (univ.filter fun a => DF fin L3N PendN (phOf (es.length - 1)) L es ∧
      ¬ DF fin L3N PendN (phOf es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128 := by
  rw [p1Start_zero] at hp
  have hrF : ¬ RejF fin oLc RejN L es := fun h => hr (Or.inl h)
  rcases sq_cls hp hit hrnd with ⟨⟨q, a, b⟩, hy, he, h1, h2⟩ | ⟨⟨q, e, k⟩, hy, hb, he, hpar, h1, h2⟩
  · simp only [sqPts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at he h1 h2
    rw [h1, h2]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · -- 14: Z2's `λ`
      refine le_trans (card_frame2 (U := Z2D zlmFR) (U' := Z2D zlmFR) rd_bgZ (by omega)
        (fun h => h) (fun _ h => h)) ((z2_single L es he).trans (by norm_num))
    · -- 68: L1's `α`
      refine le_trans (card_frame2 (U := ZendBad zlmFR) (U' := L1Bad zlmFR) rd_bg5 (by omega)
        (fun h => h) (fun _ h => h)) ((l1_single L es he).trans (by norm_num))
    · -- 98: L3β's `β`
      have hc : (univ.filter fun a => (L3Bad zlmFR L es ∨ L3N L es) ∧
          ¬ (PendLc zlmFR L (ext1 es a) ∨ PendN L (ext1 es a))).card ≤ 239 * 2 ^ 128 := by
        have h7 := l3b_single zlmFR_indKinds L es he
        have h8 := hN.single L es he
        have hu := card_or_le (A := fun _ => L3Bad zlmFR L es) (B := fun _ => L3N L es)
          (C := fun a => PendLc zlmFR L (ext1 es a)) (D := fun a => PendN L (ext1 es a))
        omega
      refine le_trans (card_frame2 (U := fun L es => L3Bad zlmFR L es ∨ L3N L es)
        (U' := fun L es => PendLc zlmFR L es ∨ PendN L es) rd_bg5 (by omega)
        (fun h => h) ?_) (by convert hc using 3)
      intro a h
      simp only [DF, D10F, bg10, bg5, bgZ] at h ⊢
      rcases h with ((h | h) | h) | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · -- 209: Lr3's `κ_L`
      refine le_trans (card_frame2 (U := EndBad Layout.lRows 15 23 lrOn 178)
        (U' := BatBad Layout.lRows 15 23 lrOn 178) (rd_bg12 hN.pendReads) (by omega)
        (fun h => h) ?_) ((lr_single_batch L es he).trans (by norm_num))
      intro a h
      simp only [DF, D16F, bg16, bg12] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
    · -- 264: E3's `κ_E`
      have hc := single_batchE (rows := Layout.nodeRows fin) L es he
      have hc' : _ ≤ 239 * 2 ^ 128 := hc.trans (by norm_num)
      refine le_trans (card_frame2 (U := fun L es => EndBad (Layout.nodeRows fin) 21 23 lrOn 221 L es ∨
          BatBad Layout.lRows 15 23 lrOn 178 L es) (U' := BatBadE (Layout.nodeRows fin))
        (rd_bg20 hN.pendReads) (by omega) ?_ (fun _ h => h)) (by convert hc' using 3)
      intro h
      simp only [DF, bg16] at h
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · -- 317: B′'s `κ′`
      refine le_trans (card_frame2 (U := DRS1) (U' := DB) (reads_false 0) (Nat.zero_le _)
        ?_ ?_) ((single_B L es he).trans (by norm_num))
      · intro h
        simp only [DF, msD, if_neg (show ¬ es.length ≤ 312 + 4 by omega)] at h
        exact Or.inr h
      · intro a h
        simp only [DF]
        exact h.elim False.elim id
  · simp only [rndPh, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at hb he hpar h1 h2
    rw [h1, h2]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · refine le_trans (card_frame2 (U := D3Z zlmFR) (U' := D3Z zlmFR) rd_bg5 (by omega)
        (fun h => h) (fun _ h => h)) ((z3_single L es).trans (by norm_num))
    · refine le_trans (card_frame2 (U := D2L zlmFR) (U' := D2L zlmFR) rd_bg5 (by omega)
        (fun h => h) (fun _ h => h)) ((l2_single L es fun j hj hjn =>
          chk_of_not_rejL2 (fun h => hrF (Or.inr (Or.inl h))) j hj hjn).trans (by norm_num))
    · have hB : Reads 99 fun L es => far0 L es ∨ nPub L es ∨ PendZ L es ∨ PendLc zlmFR L es ∨
          PendN L es ∨ nE fin L es ∨ nLr L es :=
        (rd_far0.mono (by norm_num)).or ((rd_nPub.mono (by norm_num)).or ((pendZ_reads.mono
          (by norm_num)).or (pendLc_reads.or (hN.pendReads.or ((rowsBad_reads.mono
          (by norm_num)).or (rowsBad_reads.mono (by norm_num)))))))
      refine le_trans (card_frame2 (U := D2S) (U' := D2S) hB (by omega) ?_ ?_)
        ((single_S2 L es fun j hj hjn => chk_of_not_rejS2
          (fun h => hrF (Or.inr (Or.inr (Or.inr (Or.inl h))))) j hj hjn).trans (by norm_num))
      · intro h
        simp only [DF, D12F, bg12, bg20] at h
        rcases h with ((h | h | h | h | h | h) | h) | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr h
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      · intro a h
        simp only [DF, D12F, bg12, bg20]
        rcases h with (h | h | h | h | h | h | h) | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    · refine le_trans (card_frame2 (U := D3Lr) (U' := D3Lr) (rd_bg12 hN.pendReads) (by omega)
        (fun h => h) (fun _ h => h)) ((lr_single_outer L es).trans (by norm_num))
    · refine le_trans (card_frame2 (U := D3E fin) (U' := D3E fin) (rd_bg16 hN.pendReads)
        (by omega) (fun h => h) (fun _ h => h))
        ((e_single_outer (Layout.nodeRows fin) L es).trans (by norm_num))
    · refine le_trans (card_frame2 (U := D4E (Layout.nodeRows fin)) (U' := D4E (Layout.nodeRows fin))
        (rd_bg20 hN.pendReads) (by omega) (fun h => h) (fun _ h => h))
        ((single_innerE (rows := Layout.nodeRows fin) L es fun j hj hjn => chk_of_not_rejInE
          (fun h => hrF (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
          j hj hjn).trans (by norm_num))

/-! ## The multi-squeeze phases -/

theorem fsRanges_front {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges) (hs : s0 + 1 < 318) :
    (s0 = 2 ∧ r = 10) ∨ (s0 = 98 ∧ r = 15) ∨ (s0 = 169 ∧ r = 8) ∨ (s0 = 209 ∧ r = 11) ∨
      (s0 = 312 ∧ r = 4) := by
  rw [fsRanges_eq] at hmem
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  all_goals omega

/-- **`FrontObl.ms`**: every multi-squeeze phase's doom is `msD` over its entry's. -/
theorem obl_ms : ∀ s0 r, (s0, r) ∈ fsRanges → s0 + 1 < p1Start 0 →
    ∃ D, DF fin L3N PendN (phOf (s0 + 1)) = msD (DF fin L3N PendN (phOf s0)) D s0 r := by
  intro s0 r hmem hs
  rw [p1Start_zero] at hs
  obtain ⟨p2, p3, p98, p99, p169, p170, p209, p210, p312, p313⟩ := ph_vals
  rcases fsRanges_front hmem hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [p3, p2]; exact ⟨_, rfl⟩
  · rw [p99, p98]; exact ⟨_, rfl⟩
  · rw [p170, p169]; exact ⟨_, rfl⟩
  · rw [p210, p209]; exact ⟨_, rfl⟩
  · rw [p313, p312]; exact ⟨_, rfl⟩

/-- **`FrontObl.hfin`**: the charges of Z1 (`z1_hfin`), S1 (`s1_hfin`), Lr1 (`lr_zc_hfin`), E1
(`e_zc_hfin`) and RS1 (`hfin_RS1`). A node's E part of `¬ Stmt` needs the M rows to fit. -/
theorem obl_hfin (hN : NodeLF oLc RejN L3N PendN) (hfit : RowsFit (Layout.nodeRows fin) 21 23) :
    ∀ s0 r, (s0, r) ∈ fsRanges → s0 + 1 < p1Start 0 → ∀ L es₀, Matches es₀ →
      es₀.length = s0 + 1 → ¬ RejC (RejF fin oLc RejN) c₀L L es₀ →
        condCount (DPos (Dp (DF fin L3N PendN))) L es₀ r [] ≤ deltaR := by
  intro s0 r hmem hs L es₀ _ hl _
  rw [p1Start_zero] at hs
  obtain ⟨p2, p3, p98, p99, p169, p170, p209, p210, p312, p313⟩ := ph_vals
  rcases fsRanges_front hmem hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine z1_hfin (M := zlmFR) zlmFR_bits (Bg := bgZ fin) rd_bgZ ?_ (by rw [p3, p2]; rfl)
      (fun _ _ h => h) L es₀ hl
    intro L es h
    rw [p2] at h
    simp only [DF, D2F] at h
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · rcases stmt_split hfit h with h | h | h | h | h
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
  · exact s1_hfin (Bg := bg10 fin PendN) (rd_bg10 hN.pendReads) (by rw [p98]; rfl)
      (by rw [p99, p98]; rfl) L es₀ hl
  · exact lr_zc_hfin (Bg := bg12 fin PendN) (rd_bg12 hN.pendReads) (by rw [p169]; rfl)
      (by rw [p170, p169]; rfl) L es₀ hl
  · exact e_zc_hfin (Layout.nodeRows fin) (Bg := bg16 PendN) (rd_bg16 hN.pendReads)
      (by rw [p209]; rfl) (by rw [p210, p209]; rfl) L es₀ hl
  · exact hfin_RS1 hmem (by rw [p312]; rfl) (by rw [p313, p312]; rfl) L es₀ hl

/-! ## `FrontObl` -/

/-- **The PIOP front's obligations** (`FrontObl`) for `DF`, `RejF`, `W₀L`, `c₀L`: what is left is
the node's L (`NodeLF`) and the M rows' fit. -/
theorem frontObl (hN : NodeLF oLc RejN L3N PendN) (hfit : RowsFit (Layout.nodeRows fin) 21 23) :
    FrontObl (RejF fin oLc RejN) (DF fin L3N PendN) W₀L c₀L where
  loc := frontLocal_W0
  rej := rejF_ok hN
  ms := obl_ms
  habs L es x len _ hit hp _ hd := obl_habs hN L es x len hit hp hd
  handoff L es x len _ _ hl _ hd := by
    simp only [DF] at hd
    exact Or.inr (handoff_B x (by rw [hl, p1Start_zero]) hd)
  hsingle L es _ hit hrnd hp hr := obl_single hN L es hit hrnd hp hr
  hfin := obl_hfin hN hfit
  hstab := df_stab hN.l3Reads hN.pendReads

/-! ## Controls -/

/-- Control (negative, non-vacuous): Zend's absorb (67) is no squeeze class, and Z3's first
squeeze (16) is no absorb class (the classification separates the items). -/
theorem frontCls_controls : frontCls 67 .squeeze = false ∧ frontCls 16 (.absorb 48) = false := by
  unfold frontCls ptCls rndCls absPts sqPts rndPh phOf fsRnd
  rw [fsStarts_eq, fsRanges_eq]; decide

/-- Control (positive): Z3's first squeeze and Zend's absorb are classified. -/
theorem frontCls_pos : frontCls 16 .squeeze = true ∧ frontCls 67 (.absorb 48) = true := by
  unfold frontCls ptCls rndCls absPts sqPts rndPh phOf fsRnd
  rw [fsStarts_eq, fsRanges_eq]; decide

end FR.Snd
