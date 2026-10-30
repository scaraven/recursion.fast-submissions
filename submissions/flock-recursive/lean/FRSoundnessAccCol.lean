-- New for `flock-recursive` (BLUEPRINT §3, A.3, A.9, §5.1; stage S-G4, `hFin` step 2b).
import FRSoundnessAccPf
import FRXMsg

/-!
# `hFin`, step 2b: P2.i's opened columns on the log (`FinLog.cols`)

* **`capDig_eq`**: on the run's chain, level `i`'s cap entry `c` read off the log (`capDig`, the
  C phase's absorbed message) is π's 32 bytes at `absOff fCaps (capOff i) + 32c`, where the
  verifier compares its Merkle paths (`posT`). The positions are `capPos_eq`, the messages
  `capOffL_fsMsgs` and `fsMsgs_ctl` (S-H2's certificates).
* **`ys_facts`**: per level, the fold registers `ysOf fi i` hold `y_q = Σ_r eq(sᵢ, r)·col_q[r]`,
  the index registers below them hold `qPos κ es i q`, and each column has a path to its cap
  entry on the log.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

/-! ## Offsets inside π -/

theorem sum_take_le (l : List ℕ) (n : ℕ) : (l.take n).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop n l]
  rw [List.sum_append]; omega

theorem phaseOff_add_le {n : ℕ} (hn : n < phases.length) (f : ℕ) :
    phaseOff n f + phases[n].shape.bytesTo f ≤ fieldSize f := by
  have h := sum_take_le (phases.map fun p => p.shape.bytesTo f) (n + 1)
  rw [List.map_take.symm, List.take_add_one, List.map_append, List.sum_append] at h
  simpa [phaseOff, fieldSize, List.getElem?_eq_getElem hn] using h

theorem fieldOff_add_le {f : ℕ} (hf : f < nFields) : fieldOff f + fieldSize f ≤ piSize := by
  have h := sum_take_le fieldSizes (f + 1)
  rw [List.take_add_one, List.sum_append] at h
  have hg : fieldSizes[f]? = some (fieldSize f) := by
    simp [fieldSizes, List.getElem?_map, List.getElem?_range hf]
  simpa [fieldOff, piSize, hg] using h

/-- The verifier's cap offsets are the C phases' (and `cap0`'s) messages. -/
theorem capOff_abs {i : ℕ} (hi : i < 5) : absOff fCaps (capOff i) = X.capOffL i := by
  interval_cases i <;> decide

theorem capPos_lit {i : ℕ} (hi : i < 5) :
    capPos i = [2, 330, 369, 396, 420].getD i 0 := by
  have := capPos_eq
  interval_cases i <;> simp_all [List.range_succ]

theorem capMsg {i : ℕ} (hi : i < 5) :
    X.fsMsgs.getD (capPos i) none = some (X.capOffL i, 32 * 2 ^ X.capLogL i) := by
  rw [capPos_lit hi]
  obtain ⟨h1, h2, h3, h4⟩ := X.capOffL_fsMsgs
  have h0 := X.fsMsgs_ctl.2.1
  interval_cases i
  · simpa [X.capOffL, X.capLogL] using h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- **Level `i`'s cap entry on the log is π's** at the verifier's offset. -/
theorem capDig_eq {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {i : ℕ} (hi : i < 5) {e : ℕ} (he : e < 2 ^ X.capLogL i) :
    capDig es i e = bytesAt π (absOff fCaps (capOff i) + 32 * e) 32 := by
  have hp : capPos i < 468 ∧ 0 < capPos i := by
    rw [capPos_lit hi]; interval_cases i <;> decide
  rw [capDig, msgAt_fsQ hq hp.1 hp.2 (capMsg hi),
    bytesAt_extract_of_le π (by have := Nat.mul_le_mul_left 32 he; omega), capOff_abs hi]

theorem cap_eq {i : ℕ} (hi : i < 5) : (lvlStar i).cap = X.capLogL i := by
  interval_cases i <;> decide

theorem phStart_succ {n : ℕ} (hn : n + 1 < phases.length) :
    phStart (n + 1) = phStart n + (phases[n].shape.items.filter Item.isFS).length := by
  rw [phStart_eq_sum hn, phStart_eq_sum (by omega), List.take_add_one, List.map_append,
    List.sum_append, List.getElem?_eq_getElem (by omega)]
  simp

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- **Q.i's folds on the log** (`FinLog.cols`, register side): the fold registers hold
`Σ_r eq(sᵢ, r)·col_q[r]`, the index registers below them `qPos`, and each column `col_q` has a
path on `L` to its cap entry. -/
theorem ys_facts (h : SkRun impl κ inp tr y) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) (hπ : inp.π.size = piSize) {fi : FinIn}
    (hfi : fi.outs = skeleton.2.outs) {i : ℕ} (hi : i < 5) :
    (ysOf fi i).length = (lvl κ i).t ∧
      (∀ x ∈ ysOf fi i, x < (#[] ++ y.1.toArray).size) ∧
      ∀ q < (lvl κ i).t,
        rd (#[] ++ y.1.toArray) ((ysOf fi i).getD q 0 - 3) = .n (qPos κ (fsOf tr items) i q) ∧
        ∃ col : ByteArray, ∃ ss : List Digest, ss.length = (lvl κ i).sib ∧
          (openPath (frEnc i) col (qPos κ (fsOf tr items) i q) ss).runLog L =
            some (capDig (fsOf tr items) i (qPos κ (fsOf tr items) i q / 2 ^ (lvl κ i).sib)) ∧
          rd (#[] ++ y.1.toArray) ((ysOf fi i).getD q 0) =
            .k (∑ r : Fin (lvl κ i).rows, eqBits (sAt (fsOf tr items) i) (lvl κ i).ell r *
              algebraMap F K (readF col (16 * r))) := by
  obtain ⟨hT, hsib, hcap, hcapN, hper, hper0, hcol, -, hsq0⟩ := lvl_facts κ hi
  obtain ⟨b1, -, hfold1, hsv, -, -, -, -⟩ := p1_facts h hfi hi
  have hnC : 26 + 5 * i + 1 < phases.length := by rw [phases_length]; omega
  have hnP : 26 + 5 * i + 2 < phases.length := by rw [phases_length]; omega
  have hnQ : 26 + 5 * i + 3 < phases.length := by rw [phases_length]; omega
  have hshC : phases[26 + 5 * i + 1].shape = .absorb (capField i) (capBytes i) := by
    rw [phase_lvl_shape hi (by norm_num)]; rfl
  have hshP : phases[26 + 5 * i + 2].shape = .squeezes (lvlStar i).sq (.pos i) := by
    rw [phase_lvl_shape hi (by norm_num)]; rfl
  have hshQ : phases[26 + 5 * i + 3].shape = .queries i := by
    rw [phase_lvl_shape hi (by norm_num)]; rfl
  obtain ⟨b2, -, hpos, hfold2, -, hans⟩ := pos_view h hnP hshP hsq0
  obtain ⟨bQ, houtQ, -, hQ⟩ := queries_view h hL hin hnQ hshQ hsib
  have hcF : (cAt (26 + 5 * i + 3)).foldR = (List.range (hEll i)).map (fun j => b1 + 13 * j + 6) := by
    rw [show 26 + 5 * i + 3 = 26 + 5 * i + 2 + 1 from rfl, hfold2,
      show 26 + 5 * i + 2 = 26 + 5 * i + 1 + 1 from rfl, cAt_succ hnC, genPhase_absorb _ hshC,
      show 26 + 5 * i + 1 = 27 + 5 * i by ring, hfold1]
  have hcP : (cAt (26 + 5 * i + 3)).posAns = (List.range (lvlStar i).sq).map (b2 + ·) := hpos
  have hys : ysOf fi i = (List.range (lvlStar i).t).map (fun p => bQ + 2 + posW i * p + 3) := by
    rw [ysOf, lvOuts_eq hfi, houtQ]
  refine ⟨by rw [hys]; simp [hT], fun x hx => skeleton_out_lt h.ref _ x (by
    rw [ysOf, lvOuts_eq hfi] at hx; exact hx), fun q hq => ?_⟩
  have hq' : q < (lvlStar i).t := hT ▸ hq
  obtain ⟨hidx, hy, ss, hss, hpath⟩ := hQ q hq'
  have hgy : (ysOf fi i).getD q 0 = bQ + 2 + posW i * q + 3 := by
    rw [hys, List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range]
  -- P1.i's challenges, P2.i's answers
  have hfr : ((cAt (26 + 5 * i + 3)).foldR.map fun x => (rd (#[] ++ y.1.toArray) x).toK) =
      (List.range (hEll i)).map (sAt (fsOf tr items) i) := by
    rw [hcF, List.map_map]
    exact List.map_congr_left fun j hj => by
      simp only [Function.comp_apply]; rw [hsv j (List.mem_range.1 hj)]; rfl
  have hqp : q / (lvl κ i).per < (lvlStar i).sq :=
    lt_of_le_of_lt (Nat.div_le_div_right (by omega)) hper
  have hj : idxOf (lvl κ i).logN ((rd (#[] ++ y.1.toArray)
      ((cAt (26 + 5 * i + 3)).posAns.getD (q / (lvl κ i).per) 0)).toD) (q % (lvl κ i).per) =
      qPos κ (fsOf tr items) i q := by
    rw [hcP, List.getD_eq_getElem _ _ (by simpa using hqp), List.getElem_map, List.getElem_range,
      hans _ hqp, qPos, posAt, show 26 + 5 * i + 2 = 26 + 5 * i + 1 + 1 from rfl,
      phStart_succ (by rw [phases_length]; omega), hshC,
      show phStart (27 + 5 * i) = phStart (26 + 5 * i + 1) from congrArg phStart (by ring)]
    rfl
  simp only [hj, hfr] at hidx hy hpath
  have hlt := idx_lt (lvl κ i).logN (ansAt (fsOf tr items) (phStart (27 + 5 * i) + 1 +
    q / (lvl κ i).per)) (q % (lvl κ i).per)
  refine ⟨by rw [hgy, show bQ + 2 + posW i * q + 3 - 3 = bQ + 2 + posW i * q by omega, hidx],
    inp.π.extract (absOff fCols (phaseOff (26 + 5 * i + 3) fCols + q * colBytes i))
      (absOff fCols (phaseOff (26 + 5 * i + 3) fCols + q * colBytes i) + colBytes i),
    ss, hss, ?_, ?_⟩
  · rw [hpath, Nat.shiftRight_eq_div_pow, capDig_eq h.hq hi]
    rw [← cap_eq hi, ← hcap, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    have : (lvl κ i).cap + (lvl κ i).sib = (lvl κ i).logN := by unfold Level.sib; omega
    rw [this]; exact hlt
  · have hsz : (inp.π.extract (absOff fCols (phaseOff (26 + 5 * i + 3) fCols + q * colBytes i))
        (absOff fCols (phaseOff (26 + 5 * i + 3) fCols + q * colBytes i) + colBytes i)).size =
        colBytes i := by
      have h1 := phaseOff_add_le hnQ fCols
      have h2 := fieldOff_add_le (f := fCols) (by decide)
      rw [hshQ] at h1
      simp [Shape.bytesTo] at h1
      rw [ByteArray.size_extract, absOff_eq (by decide)]
      have : q * colBytes i + colBytes i ≤ (lvlStar i).t * colBytes i := by
        have := Nat.mul_le_mul_right (colBytes i) (show q + 1 ≤ (lvlStar i).t by omega)
        rwa [Nat.add_mul, one_mul] at this
      rw [hπ]; omega
    generalize hcol' : inp.π.extract (absOff fCols (phaseOff (26 + 5 * i + 3) fCols + q * colBytes i))
      (absOff fCols (phaseOff (26 + 5 * i + 3) fCols + q * colBytes i) + colBytes i) = col at hsz hy ⊢
    have hs : ((List.range (hEll i)).map (sAt (fsOf tr items) i)).toArray.size = hEll i := by simp
    have e1 := dotKF_eq_sum ((List.range (hEll i)).map (sAt (fsOf tr items) i)).toArray col
      (by rw [hs, hsz]; exact hcol)
    rw [hs] at e1
    have e2 : (∑ r : Fin (lvl κ i).rows, eqBits (sAt (fsOf tr items) i) (lvl κ i).ell r *
        algebraMap F K (readF col (16 * r))) = ∑ r ∈ range (2 ^ hEll i),
          eqBits (fun v => ((List.range (hEll i)).map (sAt (fsOf tr items) i)).toArray.getD v 0)
            (hEll i) r * algebraMap F K (readF col (16 * r)) := by
      rw [Fin.sum_univ_eq_sum_range (fun r => eqBits (sAt (fsOf tr items) i) (lvl κ i).ell r *
        algebraMap F K (readF col (16 * r))), Level.rows, lvl_ell κ hi]
      refine sum_congr rfl fun r _ => ?_
      rw [eqBits_congr (r' := fun v => ((List.range (hEll i)).map (sAt (fsOf tr items) i)).toArray.getD
        v 0) (fun v hv => by simp [Array.getD_eq_getD_getElem?, hv])]
    rw [hgy, hy, e1, ← e2]

end FR.Snd
