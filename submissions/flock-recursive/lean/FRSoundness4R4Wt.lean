-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`'s level steps; track R4i). The 3.x
-- templates are `FRSoundnessAccW` (`tail_vals`, `lvStepV_eq`, `wV_eq`).
import FRSoundness4R4Full

/-!
# `finPf`'s level steps at revision 4.1: `wV4` from `w0V4`

* **The kind's points** (`slot_tl4`, `slot_p04`): slot `s` of `gPfPts` (`slotIx`) is the tail
  `gTailRegs seq4 fi m (s + 1)` (`s < 4`) or `gP0Regs seq4 fi m` (`s = 4`) at the family's `m`
  (`pfFamM`), which `FinTabs4.pad` makes the chain kind's.
* **`tail_vals4`**: the tail registers hold `T4.ptL es k (v + 1)`, `v < T4.mLog κ (k − 1)`
  (`tailList4_eq`: T4's `ptL` recursion; 3.x's `tail_vals`).
* **`lvStepV_eq4`**: with `tensorW` at the spec, `lvStepV … (k + 1) W` is `T4.wHatL`'s step.
* **`wV_eq4`**: `wV4 = T4.wHatL W₀ L es 4` once `w0V4 = T4.wHatL W₀ L es 0`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## The kind's points in `gPfPts` -/

theorem getD_flatMap4 {α : Type} (f : ℕ → List α) (hf : ∀ m, (f m).length = 4) (d : α) :
    ∀ (l : List ℕ) (i s : ℕ), i < l.length → s < 4 →
      (l.flatMap f).getD (4 * i + s) d = (f (l.getD i 0)).getD s d
  | [], _, _, hi, _ => absurd hi (by simp)
  | m :: l, 0, s, _, hs => by
    rw [List.flatMap_cons, List.getD_append _ _ _ _ (by rw [hf]; omega)]; simp
  | m :: l, i + 1, s, hi, hs => by
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [hf]; omega), hf,
      show 4 * (i + 1) + s - 4 = 4 * i + s by omega]
    exact getD_flatMap4 f hf d l i s (by simpa using hi) hs

/-- The family's `m` of kind `κ`'s points (`m*` if `selA`). -/
def pfFamM (P : FinP) (κ : Kind) : ℕ := if P.kv.selA κ then P.S.mStar else P.fams.getD (famI P κ) 0

section Slots
variable (P : FinP) (fi : FinIn)

/-- The tails of family `m`. -/
private def tlF (m : ℕ) : List (List PtSrc) := (List.range 4).map fun k => (gTailRegs P.S fi m (k + 1)).map .k

/-- The claims' part of `gPfPts`. -/
private def clF : List (List PtSrc) :=
  [zSrc fi P.S.mStar] ++ P.fams.map (zSrc fi) ++ [gLcSrc P.S fi P.S.mStar] ++ P.fams.map (gLcSrc P.S fi) ++
    [gShSrc P.S fi P.S.mStar] ++ P.fams.map (gShSrc P.S fi) ++ P.e4s.map (fun e => (chals fi "E4" e).map .f)

private theorem clF_length : (clF P fi).length = 3 + 3 * P.fams.length + P.e4s.length := by
  simp [clF]; ring

private theorem gPfPts_split : gPfPts P fi = clF P fi ++ (tlF P fi P.S.mStar ++ (P.fams.flatMap (tlF P fi) ++
    ((gP0Regs P.S fi P.S.mStar).map .k :: P.fams.map (fun m => (gP0Regs P.S fi m).map .k)))) := by
  simp only [gPfPts, clF, tlF, List.append_assoc, List.singleton_append]
  rfl

private theorem tlF_length (m : ℕ) : (tlF P fi m).length = 4 := by simp [tlF]

private theorem tlF_getD (m : ℕ) {s : ℕ} (hs : s < 4) :
    (tlF P fi m).getD s [] = (gTailRegs P.S fi m (s + 1)).map .k := by
  rw [tlF, List.getD_eq_getElem _ _ (by simpa using hs)]; simp

theorem slotA_tl4 {s : ℕ} (hs : s < 4) :
    (gPfPts P fi).getD (candAIx P s) [] = (gTailRegs P.S fi P.S.mStar (s + 1)).map .k := by
  rw [gPfPts_split, candAIx, if_pos hs, List.getD_append_right _ _ _ _ (by rw [clF_length]; omega),
    clF_length, show 3 + 3 * P.fams.length + P.e4s.length + s - (3 + 3 * P.fams.length + P.e4s.length) = s by omega,
    List.getD_append _ _ _ _ (by rw [tlF_length]; omega), tlF_getD P fi _ hs]

theorem slotA_p04 : (gPfPts P fi).getD (candAIx P 4) [] = (gP0Regs P.S fi P.S.mStar).map .k := by
  rw [gPfPts_split, candAIx, if_neg (by omega), List.getD_append_right _ _ _ _ (by rw [clF_length]; omega),
    clF_length, List.getD_append_right _ _ _ _ (by rw [tlF_length]; omega), tlF_length,
    List.getD_append_right _ _ _ _ (by rw [List.length_flatMap]; simp [tlF_length]; omega)]
  rw [List.length_flatMap]
  simp only [tlF_length, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [show 7 + 7 * P.fams.length + P.e4s.length - (3 + 3 * P.fams.length + P.e4s.length) - 4 -
    P.fams.length * 4 = 0 by omega]
  rfl

theorem slotI_tl4 {i : ℕ} (hi : i < P.fams.length) {s : ℕ} (hs : s < 4) :
    (gPfPts P fi).getD (candIx P i s) [] = (gTailRegs P.S fi (P.fams.getD i 0) (s + 1)).map .k := by
  rw [gPfPts_split, candIx, if_pos hs, List.getD_append_right _ _ _ _ (by rw [clF_length]; omega),
    clF_length, List.getD_append_right _ _ _ _ (by rw [tlF_length]; omega), tlF_length,
    List.getD_append _ _ _ _ (by rw [List.length_flatMap]; simp [tlF_length]; omega),
    show 7 + 3 * P.fams.length + P.e4s.length + 4 * i + s - (3 + 3 * P.fams.length + P.e4s.length) - 4 =
      4 * i + s by omega, getD_flatMap4 _ (tlF_length P fi) _ _ i s hi hs, tlF_getD P fi _ hs]

theorem slotI_p04 {i : ℕ} (hi : i < P.fams.length) :
    (gPfPts P fi).getD (candIx P i 4) [] = (gP0Regs P.S fi (P.fams.getD i 0)).map .k := by
  rw [gPfPts_split, candIx, if_neg (by omega), List.getD_append_right _ _ _ _ (by rw [clF_length]; omega),
    clF_length, List.getD_append_right _ _ _ _ (by rw [tlF_length]; omega), tlF_length,
    List.getD_append_right _ _ _ _ (by rw [List.length_flatMap]; simp [tlF_length]; omega)]
  rw [List.length_flatMap]
  simp only [tlF_length, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [show 8 + 7 * P.fams.length + P.e4s.length + i - (3 + 3 * P.fams.length + P.e4s.length) - 4 -
    P.fams.length * 4 = i + 1 by omega, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- **Slot `s < 4` of kind `κ` is the tail `Pₛ₊₁[1..]` at the family's `m`.** -/
theorem slot_tl4 (κ : Kind) (hnf : 0 < P.fams.length) {s : ℕ} (hs : s < 4) :
    (gPfPts P fi).getD (slotIx P κ s) [] = (gTailRegs P.S fi (pfFamM P κ) (s + 1)).map .k := by
  unfold slotIx pfFamM; split_ifs
  · exact slotA_tl4 P fi hs
  · exact slotI_tl4 P fi (famI_lt P κ hnf) hs

/-- **Slot `4` of kind `κ` is `P₀` at the family's `m`.** -/
theorem slot_p04 (κ : Kind) (hnf : 0 < P.fams.length) :
    (gPfPts P fi).getD (slotIx P κ 4) [] = (gP0Regs P.S fi (pfFamM P κ)).map .k := by
  unfold slotIx pfFamM; split_ifs
  · exact slotA_p04 P fi
  · exact slotI_p04 P fi (famI_lt P κ hnf)

end Slots

/-- **The tables' family is the chain kind's** (`FinTabs4.pad`). -/
theorem pfFamM_eq {P : FinP} {κ : Kind} {κc : CKind} (hT : FinTabs4 P κ κc) : pfFamM P κ = κc.m := by
  unfold pfFamM
  rcases hT.pad with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, hT.S, h2, seq4_eq]
  · rw [if_neg (by simp [h1]), h2]

/-! ## The tail points (3.x's `tailList`, at T4's reads) -/

/-- `Pₖ[1..]`'s values: `sⱼ[1..]` for `j = k … 4`, then Pf's first `m − 25` challenges. -/
def tailList4 (es : Log) (m k : ℕ) : List K :=
  (List.range' k (5 - k)).flatMap (fun j => (List.range (hEll j - 1)).map fun t => T4.sAt es j (t + 1)) ++
    (List.range (m - 25)).map (T4.pfP es)

theorem tailList4_four_eq (es : Log) (m : ℕ) :
    tailList4 es m 4 = (List.range (tLen m 4)).map (fun v => T4.ptL es 4 (v + 1)) := by
  have h4 : hEll 4 = 4 := by simp [hEll, lvlStar, lvl, ladder, ladder32]
  have hl : tailList4 es m 4 = (List.range 3).map (fun t => T4.sAt es 4 (t + 1)) ++
      (List.range (m - 25)).map (T4.pfP es) := by
    simp [tailList4, h4]
  have h3 : tLen m 4 = 3 + (m - 25) := by simp [tLen, hEll, lvlStar, lvl, ladder, ladder32]
  rw [hl, h3, map_range_append]
  refine List.map_congr_left fun v _ => ?_
  unfold T4.ptL T4.ptD
  simp only [show 4 - 4 = 0 from rfl, h4]
  split_ifs with h1 h2 h2 <;> first | omega | exact congrArg _ (by omega)

theorem tailList4_step (es : Log) (m : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 4)
    (ih : tailList4 es m (k + 1) = (List.range (tLen m (k + 1))).map (fun v => T4.ptL es (k + 1) (v + 1))) :
    tailList4 es m k = (List.range (tLen m k)).map (fun v => T4.ptL es k (v + 1)) := by
  have hr : List.range' k (5 - k) = k :: List.range' (k + 1) (5 - (k + 1)) := by
    rw [show 5 - k = (5 - (k + 1)) + 1 by omega, List.range'_succ]
  have hl : tailList4 es m k = (List.range (hEll k - 1)).map (fun t => T4.sAt es k (t + 1)) ++
      tailList4 es m (k + 1) := by
    rw [tailList4, tailList4, hr, List.flatMap_cons, List.append_assoc]
  have hlen : tLen m k = (hEll k - 1) + tLen m (k + 1) := by
    simp only [tLen, hr, List.map_cons, List.sum_cons]; omega
  rw [hl, ih, map_range_append, hlen]
  refine List.map_congr_left fun v _ => ?_
  have he := hEll_pos (i := k) (by omega)
  rw [T4.ptL_lt (k := k) hk]
  beta_reduce
  by_cases h1 : v < hEll k - 1
  · simp only [h1, show v + 1 < hEll k by omega, ite_true]
  · rw [show v - (hEll k - 1) + 1 = v + 1 - hEll k + 1 by omega]
    simp only [h1, show ¬ v + 1 < hEll k by omega, ite_false]

theorem tailList4_eq (es : Log) (m : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    tailList4 es m k = (List.range (tLen m k)).map (fun v => T4.ptL es k (v + 1)) := by
  have h4 := tailList4_four_eq es m
  have h3 := tailList4_step es m (k := 3) (by norm_num) (by norm_num) h4
  have h2 := tailList4_step es m (k := 2) (by norm_num) (by norm_num) h3
  have h1 := tailList4_step es m (k := 1) (by norm_num) (by norm_num) h2
  obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  exacts [h1, h2, h3, h4]

/-- The tails' lengths are T4's `mLog` (every chain kind). -/
theorem tail_len4 (κ : CKind) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) : tLen κ.m k = T4.mLog κ (k - 1) := by
  rcases κ with σ | ν <;> [cases σ; cases ν] <;> interval_cases k <;> decide

theorem T4_ptL_zero {es : Log} {k : ℕ} (hk : k ≤ 4) : T4.ptL es k 0 = T4.sAt es k 0 := by
  rcases Nat.lt_or_ge k 4 with h | h
  · rw [T4.ptL_lt h]; simp [hEll_pos (i := k) (by omega)]
  · obtain rfl : k = 4 := by omega
    exact T4.ptL_four_lt es (hEll_pos (by norm_num))

section Run
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  (h : SkRun4 impl p inp tr y) {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
  {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

/-- **`sᵢ`'s registers** (`gSRegs seq4`, 3.x's `sRegs`) hold T4's `sAt`. -/
theorem gSRegs_view4 {i : ℕ} (hi : i < 5) :
    ∃ b, gSRegs seq4 fi i = (List.range (hEll i)).map (fun j => b + 13 * j + 6) ∧
      sRegs fi i = gSRegs seq4 fi i ∧
      (∀ j < hEll i, rd R (b + 13 * j + 6) = .k (T4.sAt (fsOf tr (itemsOf seq4)) i j)) ∧
      ∀ x ∈ gSRegs seq4 fi i, x < (#[] ++ y.1.toArray).size := by
  obtain ⟨b, hout, hsv, -, -, hlt, -⟩ := p1_view4 h hfi hi
  have hs : gSRegs seq4 fi i = (List.range (hEll i)).map (fun j => b + 13 * j + 6) := by
    rw [gSRegs, hout, seq4_ell hi, List.cons_append, List.drop_one, List.tail_cons,
      List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  have hlt' : ∀ x ∈ gSRegs seq4 fi i, x < (#[] ++ y.1.toArray).size := fun x hx =>
    hlt x (by rw [gSRegs] at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx))
  refine ⟨b, hs, by rw [sRegs, gSRegs, seq4_ell hi]; rfl, fun j hj => ?_, hlt'⟩
  rw [hR.rd (hlt' _ (by rw [hs]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)), hsv j hj]

/-- **The tail registers hold `T4.ptL`** (`k = 1 … 4`; 3.x's `tail_vals`). -/
theorem tail_vals4 (κ : CKind) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (gTailRegs seq4 fi κ.m k).map (fun x => (rd R x).toK) =
        (List.range (T4.mLog κ (k - 1))).map (fun v => T4.ptL (fsOf tr (itemsOf seq4)) k (v + 1)) ∧
      ∀ x ∈ gTailRegs seq4 fi κ.m k, x < (#[] ++ y.1.toArray).size := by
  obtain ⟨hpv, hpl, -, -, hpo, -⟩ := pf_view4 h hfi
  have hm : κ.m - 25 ≤ 7 := by have := CKind.m_mem κ; omega
  have hS : ∀ j < 5, ((gSRegs seq4 fi j).drop 1).map (fun x => (rd R x).toK) =
      (List.range (hEll j - 1)).map (fun t => T4.sAt (fsOf tr (itemsOf seq4)) j (t + 1)) ∧
      ∀ x ∈ (gSRegs seq4 fi j).drop 1, x < (#[] ++ y.1.toArray).size := fun j hj => by
    obtain ⟨b, hs, -, hsv, hlt⟩ := gSRegs_view4 h hfi hR hj
    refine ⟨?_, fun x hx => hlt x (List.mem_of_mem_drop hx)⟩
    rw [hs, drop_one_map_range, List.map_map]
    refine List.map_congr_left fun t ht => ?_
    have ht' := List.mem_range.1 ht
    simp only [Function.comp_apply]
    rw [hsv _ (by omega)]
    rfl
  have hch : ∀ x ∈ chals fi "Pf" 7, x ∈ outsOf fi "Pf" := fun x hx => by
    unfold chals at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
  have hP : ((chals fi "Pf" seq4.pf).take (κ.m - 25)).map (fun x => (rd R x).toK) =
      (List.range (κ.m - 25)).map (T4.pfP (fsOf tr (itemsOf seq4))) := by
    rw [seq4_pf]
    refine List.ext_getElem (by simp [hpl]; omega) fun v h1 h2 => ?_
    simp only [List.length_map, List.length_take, hpl] at h1
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    have hv : v < 7 := by omega
    have hmem : (chals fi "Pf" 7)[v] ∈ outsOf fi "Pf" := hch _ (List.getElem_mem _)
    rw [hR.rd (hpo _ hmem), ← List.getD_eq_getElem _ 0, hpv v hv]; rfl
  refine ⟨?_, fun x hx => ?_⟩
  · rw [gTailRegs, List.map_append, List.map_flatMap, hP, ← tail_len4 κ hk1 hk4,
      ← tailList4_eq _ _ hk1 hk4, tailList4,
      List.flatMap_congr fun j hj => (hS j (by have := List.mem_range'.1 hj; omega)).1]
  · rw [gTailRegs, List.mem_append, List.mem_flatMap] at hx
    rcases hx with ⟨j, hj, hx⟩ | hx
    · exact (hS j (by have := List.mem_range'.1 hj; omega)).2 x hx
    · rw [seq4_pf] at hx
      exact hpo x (hch x (List.mem_of_mem_take hx))

/-- **Q.k's position registers and count**: `ysOf fi k` has the kind's `t` registers; query `q`'s
position register holds `qPos`. -/
theorem ys_view4 {L : Log} (hL : (L.map Prod.fst).Nodup) (hin : ∀ e ∈ tr, e ∈ L)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {k : ℕ} (hk : k < 5) :
    (ysOf fi k).length = (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t ∧
      ∀ q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t,
        (ysOf fi k).getD q 0 - 3 < (#[] ++ y.1.toArray).size ∧
        rd R ((ysOf fi k).getD q 0 - 3) =
          .n (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) k q) := by
  have hys : ysOf fi k = (skeleton4 seq4 p).2.outs.getD (29 + 5 * k) [] := by
    rw [ysOf, lvOuts, hfi, phaseIx_P1, show 26 + 5 * k + 3 = 29 + 5 * k by ring]
  obtain ⟨hnQ, eQ⟩ := ph4 (phases4_lvl (i := k) hk).2.2
  have hT := (lv_facts4 (CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))) (i := k) hk).1
  have hysE : (ysOf fi k).length = (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t := by
    rw [hys, skeleton4_outs seq4 p hnQ, eQ, genPhase4_queries_outs, List.length_map, List.length_range, ← hT]; rfl
  refine ⟨hysE, fun q hq => ?_⟩
  have hyq : (ysOf fi k).getD q 0 = yReg4 p k q := by rw [yReg4, ← hys]
  have hmem : yReg4 p k q ∈ ysOf fi k := by
    rw [← hyq, List.getD_eq_getElem _ _ (by rw [hysE]; exact hq)]; exact List.getElem_mem _
  have hylt : yReg4 p k q < (#[] ++ y.1.toArray).size :=
    skeleton4_out_lt p h.ref _ _ (by rw [← hys]; exact hmem)
  have hlt : yReg4 p k q - 3 < (#[] ++ y.1.toArray).size := lt_of_le_of_lt (Nat.sub_le _ _) hylt
  exact ⟨by rw [hyq]; exact hlt, by rw [hyq, hR.rd hlt, posReg4 h hL hin hm hk hq]⟩

/-- **One level step of `finPf` at the spec** (`k + 1 = 1 … 4`; 3.x's `lvStepV_eq`): `lvStepV` is
`T4.wHatL`'s step, given the tail array `tl (k + 1)` of the kind's tail registers. -/
theorem lvStepV_eq4 {L : Log} (hL : (L.map Prod.fst).Nodup) (hin : ∀ e ∈ tr, e ∈ L)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) {tl : ℕ → Array K} {k : ℕ} (hk : k < 4)
    (htl : tl (k + 1) =
      ((gTailRegs seq4 fi (kindOfC (fsOf tr (itemsOf seq4))).m (k + 1)).map fun x => (rd R x).toK).toArray)
    (W : K) :
    lvStepV impl fi (rd R) tl (k + 1) W =
      uHat (T4.ptL (fsOf tr (itemsOf seq4)) (k + 1) 0) * (W +
        ∑ q ∈ range (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t,
          algebraMap F K (eqBits (T4.kcAt (fsOf tr (itemsOf seq4)) k) 9 q) *
            tensorTwin D logNMax (T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) k)
              (fun v => if v < T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) k then
                T4.ptL (fsOf tr (itemsOf seq4)) (k + 1) (v + 1) else 0)
              (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) k q)) := by
  obtain ⟨b, hs, hsr, hsv, -⟩ := gSRegs_view4 h hfi hR (i := k + 1) (by omega)
  obtain ⟨-, hkc⟩ := kc_view4 h hfi (i := k) (by omega) hR
  obtain ⟨hyl, hyv⟩ := ys_view4 h hfi hR hL hin hm (k := k) (by omega)
  obtain ⟨htv, -⟩ := tail_vals4 h hfi hR (kindOfC (fsOf tr (itemsOf seq4))) (k := k + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at htv
  have hT : (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t = (seq4.lv k).t :=
    (lv_facts4 (CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))) (i := k) (by omega)).1
  have ht9 := t_lt4 (i := k) (by omega)
  unfold lvStepV
  simp only [Nat.add_sub_cancel]
  have hE0 := hEll_pos (i := k + 1) (by omega)
  have hhead : (sRegs fi (k + 1)).headD 0 = b + 13 * 0 + 6 := by
    rw [hsr, hs]; obtain ⟨e, he⟩ : ∃ e, hEll (k + 1) = e + 1 := ⟨hEll (k + 1) - 1, by omega⟩
    rw [he, List.range_succ_eq_map]; rfl
  rw [hhead, hsv 0 hE0, Val.toK, T4_ptL_zero (by omega)]
  congr 1
  have hkc' : (kcOf fi k).map (fun x => (rd R x).toF) = (List.range 9).map (T4.kcAt (fsOf tr (itemsOf seq4)) k) :=
    hkc
  rw [hkc', accVal_eq, List.length_map, List.length_range, hyl,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  congr 1
  refine sum_congr rfl fun q hq => ?_
  have hq' := mem_range.1 hq
  rw [Nat.zero_add, eqTab_getD _ (by simp; omega), K.smulF_eq_mul, ← K.algebraMap_eq_ofF]
  simp only [List.size_toArray, List.length_map, List.length_range]
  rw [eqBits_congr (r' := T4.kcAt (fsOf tr (itemsOf seq4)) k) (fun v hv => by
    simp [Array.getD_eq_getD_getElem?, hv])]
  congr 1
  rw [List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range,
    (hyv q hq').2, Val.toN, ht, Impl.tensorWS,
    tensorTwin, tensorTwin]
  have hsz : (tl (k + 1)).size = T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) k := by
    rw [htl, List.size_toArray, htv]; simp
  rw [hsz]
  refine prod_congr rfl fun v hv => ?_
  have hv' := mem_range.1 hv
  have hg : (tl (k + 1)).getD v 0 = T4.ptL (fsOf tr (itemsOf seq4)) (k + 1) (v + 1) := by
    rw [htl, Array.getD_eq_getD_getElem?, List.getElem?_toArray, htv]; simp [hv']
  rw [hg, if_pos hv']

/-- **`finPf`'s `Ŵ₄(P₄)` at the spec is `T4.wHatL … 4`**, from `Ŵ₀(P₀)` (3.x's `wV_eq`). -/
theorem wV_eq4 {L : Log} (hL : (L.map Prod.fst).Nodup) (hin : ∀ e ∈ tr, e ∈ L)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) {tl : ℕ → Array K}
    (htl : ∀ k < 4, tl (k + 1) =
      ((gTailRegs seq4 fi (kindOfC (fsOf tr (itemsOf seq4))).m (k + 1)).map fun x => (rd R x).toK).toArray)
    (W₀ : Log → Log → ℕ → K) {w0 : K} (hw0 : w0 = T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 0) :
    lvsV impl fi (rd R) tl [1, 2, 3, 4] w0 = T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4 := by
  have key : ∀ k ≤ 4, lvsV impl fi (rd R) tl ((List.range k).map (· + 1)) w0 =
      T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) k := by
    intro k hk4
    induction k with
    | zero => exact hw0
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, lvsV_snoc, ih (by omega),
        lvStepV_eq4 h hfi hR hL hin hm ht (by omega) (htl k (by omega)), T4.wHatL]
  exact key 4 le_rfl

end Run

end FR.Snd.R4
