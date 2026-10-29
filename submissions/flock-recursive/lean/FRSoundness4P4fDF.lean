-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Lr1 … B′, §5.1–§5.2; stage P4f):
-- the front's phase dooms 13 … 25 at `seq4`, over X4's composed doom `DFX` and checks `RejFX`.
-- 3.x's `FRSoundnessFrDF` (`DF 13 … 25`) is the template, P4a's `FRSoundness4P4aDF` the form.
import FRSoundness4XFront

/-!
# The front's phases 13 … 25 at revision 4.1: the dooms `DFhi`

* **S2's pending claim on every segment** (`endS4U`, `pendS4U`): P4a's `endS4`/`pendS4_pendBad4`
  assume a segment's last block is among its blocks (`lastL < 2^nb`, `V_A`'s `n ≤ cap`, which no
  final of the segment program asserts). The assumption is not needed: past the blocks both the
  doom's weight and `finSh` (ii)'s `wSumSeg` lose their end term (`final_segU`, `wSumSegU`), so the
  pending S claim is RS0's `PendBad4` on every log. Without this, a segment log with `n > cap` and a
  false S2 claim could not be carried past RS0.
* **The backgrounds** (3.x's `bg20`, `bg12`, `bg16` at revision 4.1): `bg20X` (far, a false
  public cell, the pending Z, Lc (both kinds) and S claims), `bg12X` (and the M rows, until E1),
  `bg16X` (and Lr's pending batch, Lr3 … E end). X4's `BgA4` (far, public, L rows, M rows) is
  carried by phase 12's doom; Lr1 reduces its L rows, E1 its M rows, RS0 the pending claims.
* **`DFhi`**: phases 13 … 25 (3.x's `DF 13 … 25`): Lr1 `msD` over phase 12's doom, Lr2's outer
  rounds, Lrend's triple, Lr3's batch, E1 … E4 end, then P4b's `DRS0_4`, `msD DRS0_4 DRS1_4`,
  `DB4` at `far0X` and `PubOK4 src4 cells4`.
* **`dPend_X`**: E4 end's doom is P4b's `DPend4` at RS0 (the five pending-claim bridges).
* **`dfhi_ss`**: phase `k`'s doom reads the same off two logs whose words agree, on `X` of at least
  `phStart4 k + 1` entries (`hstab`, `chain`).
-/

namespace FR.Snd.P4f
open RecursionFast FR.Merkle FR.Rev4 Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## S2's pending claim on every segment -/

/-- **A segment's final value without the block bound** (P4a's `final_seg` with `Lb < 2^18` for
`Lb < 2^nb`): past the blocks the end term is `0` on both sides. -/
theorem final_segU {nb : ℕ} (hnb : nb ≤ 18) (τs rb bits : List F) (hτ : τs.length = nb)
    (hrb : rb.length = nb) {Lb : ℕ} (hL : Lb < 2 ^ 18)
    (hbits : Rev4.lastAt (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray 18 = Lb)
    (θ rp : Array F) (κ : F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb),
        eqAtR (ptOf nb rb) y * eqAtR (ptA 10 rp) q * P4a.wSeg (ptOf nb τs) (ptA 10 θ) κ Lb y q =
      (Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
          (rb ++ List.replicate (18 - nb) 0).toArray).1 * slotWS 0 θ rp +
        ((Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray).2.1 +
          κ * (Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray).2.2) * slotWS 1 θ rp := by
  set τP := τs ++ List.replicate (18 - nb) 0
  set rP := rb ++ List.replicate (18 - nb) 0
  have hτP : τP.length = 18 := by simp [τP, hτ]; omega
  have hrP : rP.length = 18 := by simp [rP, hrb]; omega
  have hA : ptA 18 (τP ++ bits).toArray = ptOf 18 τP := funext fun l => by
    simp only [ptA, ptOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (show l.val < τP.length by omega)]
  have hB : ptA 18 rP.toArray = ptOf 18 rP := ptA_toArray _ _
  have h1 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).1 = eqPoint τP.toArray rP.toArray := by
    rw [eqPoint_eq, List.size_toArray, hτP, ptA_toArray, ptA_toArray]
    simp only [Rev4.shiftSegS, hA, hB]
  have hmle : shiftMle 18 (ptOf 18 τP) (ptOf 18 rP) = shiftEqS τP.toArray rP.toArray := by
    rw [← shiftEq_meets _ _ (by simp [hτP, hrP]), shiftEqI, List.toList_toArray, List.toList_toArray,
      shiftPair_eq 18 τP rP hτP hrP]
  -- the only change against `final_seg`: the end term without `Lb < 2^nb`
  have hc : (if Lb + 1 < 2 ^ 18 then eqAtR (ptOf 18 τP) Lb * eqAtR (ptOf 18 rP) (Lb + 1) else 0) =
      if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0 := by
    have h18 : 2 ^ nb ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hnb
    rw [P4a.eqAtR_padN hnb τs hτ hL]
    by_cases h : Lb + 1 < 2 ^ nb
    · rw [if_pos (show Lb + 1 < 2 ^ 18 by omega), if_pos (show Lb < 2 ^ nb by omega),
        P4a.eqAtR_padN hnb rb hrb (by omega), if_pos h, if_pos h]
    · rw [if_neg h]
      by_cases h' : Lb + 1 < 2 ^ 18
      · rw [if_pos h', P4a.eqAtR_padN hnb rb hrb h', if_neg h, mul_zero]
      · rw [if_neg h']
  have h2 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).2.1 = shiftEqS τP.toArray rP.toArray +
      if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0 := by
    simp only [Rev4.shiftSegS, hA, hB, hbits, hmle]
    rw [← hc]
  have h3 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).2.2 =
      eqPoint (Array.replicate 18 0) rP.toArray := by
    rw [P4a.eqPoint_zero18 rP hrP]; simp only [Rev4.shiftSegS, hB]
  rw [h1, h2, h3]
  have hw : ∀ y q, P4a.wSeg (ptOf nb τs) (ptA 10 θ) κ Lb y q = wLeaf (ptOf nb τs) (ptA 10 θ) κ y q +
      (if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) * slotT (ptA 10 θ) 520 q := fun y q => by
    simp only [P4a.wSeg, wLeaf, P4a.shSeg_eq]; ring
  simp only [hw, mul_add, sum_add_distrib]
  rw [final_leaf hnb τs rb hτ hrb θ rp κ]
  have hlink : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y *
      eqAtR (ptA 10 rp) q * ((if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) *
        slotT (ptA 10 θ) 520 q) =
      (if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0) *
        slotWS 1 θ rp := by
    have e : ∀ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y *
        eqAtR (ptA 10 rp) q * ((if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) *
          slotT (ptA 10 θ) 520 q) =
        (if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0) *
          (eqAtR (ptA 10 rp) q * slotT (ptA 10 θ) 520 q) := fun q _ => by
      simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_range]
      split_ifs <;> ring
    rw [sum_congr rfl e, ← mul_sum, sum_slot_eqAtR _ _ (by norm_num), slotWS_eq]
    rfl
  rw [hlink]
  ring

/-- **A segment's weight value is the extension of `wS`** (P4a's `wSumSeg_eq` on every segment). -/
theorem wSumSegU (wN : CKind → Log → ℕ → ℕ → F) {es : Log} (hn : (kindOfC es).isNode = false) :
    P4a.wSumSeg (kindOfC es) es = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ P4a.nbC (kindOfC es)),
      eqAtR (ptOf (P4a.nbC (kindOfC es)) (P4a.rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (P4a.rpL (kindOfC es) es)) q * P4a.wS wN (kindOfC es) es y q := by
  generalize hκ : kindOfC es = κ at hn
  have hθ : ptA 10 (thL es).toArray = ptOf 10 (thL es) := ptA_toArray _ _
  have hr : ptA 10 (P4a.rpL κ es).toArray = ptOf 10 (P4a.rpL κ es) := ptA_toArray _ _
  have hτ : (P4a.tauL κ es).length = P4a.nbC κ := by simp [P4a.tauL]
  have hrb : (P4a.rbL κ es).length = P4a.nbC κ := by simp [P4a.rbL]
  have e := final_segU (P4a.nbC_le κ) (P4a.tauL κ es) (P4a.rbL κ es) (P4a.lastBits es) hτ hrb
    (P4a.lastL_lt es) (P4a.lastAt_tauLL κ es) (thL es).toArray (P4a.rpL κ es).toArray (ksL es)
  rw [hθ, hr] at e
  simp only [P4a.wS, hn, Bool.false_eq_true, if_false]
  rw [e]
  rfl

/-- **At S2's end its doom is the Sh binding failing at `ẑ`** (P4a's `endS4` on every segment). -/
theorem endS4U {wN : CKind → Log → ℕ → ℕ → F} {zw : P4a.Wit} {wNS : CKind → Log → F} {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ P4a.nbC (kindOfC es)),
        eqAtR (ptOf (P4a.nbC (kindOfC es)) (P4a.rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (P4a.rpL (kindOfC es) es)) q * wN (kindOfC es) es y q)
    (h : P4a.D2S wN zw L es) (hl : 170 ≤ es.length) :
    ¬ P4a.oSh4 wNS (kindOfC es) es (P4a.zS2 zw L es) := by
  obtain ⟨-, hw⟩ := h
  have ha : T4.ans3 114 P4a.nrS es = P4a.nrS (kindOfC es) := by
    have := P4a.nrS_le4 (kindOfC es); unfold T4.ans3; simp; omega
  rw [ha] at hw
  unfold T4.Wrong2 at hw
  rw [Nat.sub_self, trueSum_bindAll' _ _ _ (by simp [rchs2]) (P4a.TS_size4 L es), innerExpr_eval2,
    P4a.TS, arrGetD_pair0, arrGetD_pair1, P4a.nrS, mle_tab, mle_tab,
    (P4a.rchsS_pts4 _ es).1, (P4a.rchsS_pts4 _ es).2] at hw
  intro hok
  apply hw
  have hW : P4a.wSumL4 wNS (kindOfC es) es = ∑ q ∈ range (2 ^ 10),
      ∑ y ∈ range (2 ^ P4a.nbC (kindOfC es)),
      eqAtR (ptOf (P4a.nbC (kindOfC es)) (P4a.rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (P4a.rpL (kindOfC es) es)) q * P4a.wS wN (kindOfC es) es y q := by
    unfold P4a.wSumL4
    cases hn : (kindOfC es).isNode
    · simp only [Bool.false_eq_true, if_false]; exact wSumSegU wN hn
    · simp only [if_true]; rw [hNS hn]
      simp only [P4a.wS, hn, if_true]
  rw [P4a.oSh4, P4a.claimSL4, hW, P4a.zS2] at hok
  rw [show clR2 114 16 readF (fun d => chF d 0) P4a.c0SL L es (P4a.nbC (kindOfC es) + 10) =
    P4a.claimSL4 (kindOfC es) es from clR2_same rfl (fun _ _ => rfl), P4a.claimSL4]
  exact hok

/-- **S2's doom at its end is RS0's `PendBad4` at claim 3** on every log (P4a's `pendS4_pendBad4`
without its segment bound). -/
theorem pendS4U (R : P4b.FSrc) (kf : NodeKind → F → ℕ → F)
    {oZ oLc : CKind → Log → F → Prop} {wN : CKind → Log → ℕ → ℕ → F} {zw : P4a.Wit}
    {wNS : CKind → Log → F} (hzw : P4a.WitOf R zw) {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ P4a.nbC (kindOfC es)),
        eqAtR (ptOf (P4a.nbC (kindOfC es)) (P4a.rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (P4a.rpL (kindOfC es) es)) q * wN (kindOfC es) es y q)
    (h : P4a.D2S wN zw L es) (hl : 170 ≤ es.length) :
    P4b.PendBad4 R kf (P4b.okRS4 oZ oLc (P4a.oSh4 wNS)) L es := by
  refine ⟨2, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => endS4U hNS h hl ?_⟩
  have ho' : P4a.oSh4 wNS (kindOfC es) es (P4b.trueL4 R kf (kindOfC es) L es 2) := ho
  rwa [P4a.trueL4_two R kf hzw] at ho'

/-! ## The background parts and the dooms -/

/-- The level-0 word is far (`BgA4`'s first part). -/
def far0X (L es : Log) : Prop := T4.farL (kindOfC es) L es 0

/-- The node's public cells hold (`BgA4`'s second part, S-E's `cells4`). -/
def PubX : Log → Log → Prop := P4b.PubOK4 X4.src4 N4c.cells4

/-- **From E3 on**: far, a false public cell, the pending Z, Lc (both kinds) and S claims (3.x's
`bg20`). -/
def bg20X (L es : Log) : Prop :=
  far0X L es ∨ ¬ PubX L es ∨ P4a.PendZ X4.P4X.zw L es ∨ P4a.PendLc X4.P4X.M X4.P4X.zw L es ∨
    P4a.PendLcN X4.P4X.M X4.P4X.zw L es ∨ P4a.D2S X4.P4X.wN X4.P4X.zw L es

/-- **S2 … Lr end**: and the M rows (E1 reduces them; 3.x's `bg12`). -/
def bg12X (L es : Log) : Prop := bg20X L es ∨ P4b.nE4 X4.src4 NI4F.srcE4 L es

/-- **Lr3 … E end**: and Lr's pending batch (E3 reduces it; 3.x's `bg16`). -/
def bg16X (L es : Log) : Prop := bg20X L es ∨ P4b.BatBadLr4 X4.src4 NI4F.srcL4 L es

/-- **Lr3's doom** (E1's entry; 3.x's `D16F`; revision 4.4.2, RSV2 §2.6: or a false child claim,
which E1's `η·D` term reduces). -/
def D16X (L es : Log) : Prop :=
  bg16X L es ∨ P4b.nE4 X4.src4 NI4F.srcE4 L es ∨ P4b.ChildBad4 NI4F.srcE4 L es

/-- RS0's, RS1's and B′'s dooms at `far0X`, `PubX` and S-E's kind factor and cells. -/
noncomputable def DRS0X : Log → Log → Prop := P4b.DRS0_4 X4.src4 N4c.kf4 far0X PubX
noncomputable def DRS1X : Log → Log → Prop := P4b.DRS1_4 X4.src4 N4c.kf4 far0X PubX
noncomputable def DBX : Log → Log → Prop := P4b.DB4 X4.src4 N4c.kf4 N4c.cells4 far0X

/-- **The front's phase dooms 13 … 25** (3.x's `DF 13 … 25`): Lr1 is `msD` over phase 12's doom
(P4a's `DF4a P4X 12`, which carries `BgA4`). -/
noncomputable def DFhi : ℕ → Log → Log → Prop
  | 13 => msD (P4a.DF4a X4.P4X 12)
      (fun L es => bg12X L es ∨ P4b.ZCwLr4 X4.src4 NI4F.srcL4 L es) 169 9
  | 14 => fun L es => bg12X L es ∨ P4b.D3Lr4 X4.src4 NI4F.srcL4 L es
  | 15 => fun L es => bg12X L es ∨ P4b.EndBadLr4 X4.src4 NI4F.srcL4 L es
  | 16 => D16X
  | 17 => msD D16X (fun L es => bg16X L es ∨ P4b.ZCwE4 X4.src4 NI4F.srcE4 L es) 214 12
  | 18 => fun L es => bg16X L es ∨ P4b.D3E4 X4.src4 NI4F.srcE4 L es
  | 19 => fun L es => bg16X L es ∨ P4b.EndBadE4 X4.src4 NI4F.srcE4 L es
  | 20 => fun L es => bg20X L es ∨ P4b.BatBadE4 X4.src4 NI4F.srcE4 NI4F.srcL4 L es
  | 21 => fun L es => bg20X L es ∨ P4b.D4E4 X4.src4 NI4F.srcE4 NI4F.srcL4 L es
  | 22 => fun L es => bg20X L es ∨ P4b.PendE4 X4.src4 L es
  | 23 => DRS0X
  | 24 => msD DRS0X DRS1X 326 4
  | 25 => DBX
  | _ => fun _ _ => False

/-! ## Reads -/

theorem rd_far0X : T4.Reads 3 far0X := fun L es L' es' _ _ hS => by
  unfold far0X; rw [hS.kind (by norm_num)]
  exact T4.farL_same hS (i := 0) (by norm_num) _ (by rw [P4a.capPos_zero4]; omega)

theorem rd_PubX : T4.Reads 3 PubX := P4b.pubOK4_reads X4.src4 N4c.cells4

theorem rd_bg20X : T4.Reads 170 bg20X :=
  (rd_far0X.mono (by norm_num)).or ((rd_PubX.not.mono (by norm_num)).or
    (((P4a.pendZ_reads4 P4a.zwSame_zW).mono (by norm_num)).or
    (((P4a.pendLc_reads4 P4a.zwSame_zW).mono (by norm_num)).or
    (((P4a.pendLcN_reads4 P4a.zwSame_zW).mono (by norm_num)).or
      (P4a.D2S_reads4 P4a.wNLocal4 P4a.zwSame_zW)))))

theorem rd_nE4X : T4.Reads 3 (P4b.nE4 X4.src4 NI4F.srcE4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num)
    (fun κ => P4b.rowsBadG_reads X4.src4 (NI4F.srcE4 κ) (P4b.e2R κ) (P4b.ncR κ))

theorem rd_bg12X : T4.Reads 170 bg12X := rd_bg20X.or (rd_nE4X.mono (by norm_num))

theorem rd_batLr : T4.Reads 215 (P4b.BatBadLr4 X4.src4 NI4F.srcL4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ =>
    P4b.batBadG_reads X4.src4 (NI4F.srcL4 κ) (P4b.lrR κ) (P4b.ncR κ) 179 17 (by norm_num)
      (P4b.dims_le' κ).1

theorem rd_bg16X : T4.Reads 215 bg16X := (rd_bg20X.mono (by norm_num)).or rd_batLr

/-- A false child claim reads Lrend's message (213). -/
theorem rd_childX : T4.Reads 214 (P4b.ChildBad4 NI4F.srcE4) := fun L es L' es' h1 h2 hS => by
  have hA : Agree es es' 214 := hS.1
  obtain ⟨hx, hy, hs, hX⟩ := P4b.child_agree hA le_rfl
  simp only [P4b.ChildBad4, P4b.OnNode, P4b.truthChild4, hx, hy, hs, hX,
    kindOfC_congr (hA.mono (by norm_num))]
  exact ⟨fun ⟨κ, hk, _, h⟩ => ⟨κ, hk, h2, h⟩, fun ⟨κ, hk, _, h⟩ => ⟨κ, hk, h1, h⟩⟩

theorem rd_D16X : T4.Reads 215 D16X :=
  rd_bg16X.or ((rd_nE4X.mono (by norm_num)).or (rd_childX.mono (by norm_num)))

/-! ## E4 end's doom is RS0's `DPend4` -/

/-- **E4 end's doom is `DPend4` at RS0** (3.x's `dPend_of`): far and the public cells carry over;
the pending Z, Lc (both kinds), S and E claims fail their bindings (`okX`) at their true values. -/
theorem dPend_X {L es : Log} (hl : 170 ≤ es.length) (h : DFhi 22 L es) :
    P4b.DPend4 X4.src4 N4c.kf4 X4.okX far0X PubX L es := by
  simp only [DFhi, bg20X] at h
  rcases h with (h | h | h | h | h | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (P4a.pendZ4_pendBad4 X4.src4 N4c.kf4 X4.witOf_src4 h))
  · exact .inr (.inr (P4a.pendLc4_pendBad4 X4.src4 N4c.kf4 (P4a.segInd_zlm4 _ _) X4.witOf_src4 h))
  · exact .inr (.inr (P4a.pendLcN4_pendBad4 X4.src4 P4a.kfInd4 X4.witOf_src4 h))
  · exact .inr (.inr (pendS4U X4.src4 N4c.kf4 X4.witOf_src4 P4a.hNS4 h hl))
  · exact .inr (.inr (P4b.pendE4_pendBad4 h))

/-! ## `hstab`: the dooms read `L` only through the words -/

/-- The phase starts 12 … 26. -/
theorem phStart_hi : phStart4 12 = 114 ∧ phStart4 13 = 170 ∧ phStart4 14 = 179 ∧
    phStart4 15 = 213 ∧ phStart4 16 = 214 ∧ phStart4 17 = 215 ∧ phStart4 18 = 227 ∧
    phStart4 19 = 273 ∧ phStart4 20 = 274 ∧ phStart4 21 = 275 ∧ phStart4 22 = 325 ∧
    phStart4 23 = 326 ∧ phStart4 24 = 327 ∧ phStart4 25 = 331 ∧ phStart4 26 = 332 := by
  obtain ⟨-, -, -, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26⟩ :=
    P4b.p4b_pos
  exact ⟨P4a.phStart_vals4a.2.2.2.2.2.2.2.2.2.2, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26⟩

section SS
variable {L L' X : Log}

theorem ss_D3Lr4 : P4a.SameStab4 180 (P4b.D3Lr4 X4.src4 NI4F.srcL4) := fun L L' X hx hS =>
  P4b.onNode_congr rfl fun κ _ => P4b.D3G_same X4.src4 (NI4F.srcL4 κ) (P4b.lrR κ) (P4b.ncR κ) 169
    179 hS (by omega) (by have := (P4b.dims_le' κ).1; omega)

theorem ss_D3E4 : P4a.SameStab4 228 (P4b.D3E4 X4.src4 NI4F.srcE4) := fun L L' X hx hS =>
  P4b.onNode_congr rfl fun κ _ => P4b.D3E4_same X4.src4 NI4F.srcE4 κ hS (by omega)

theorem ss_batE4 : P4a.SameStab4 275 (P4b.BatBadE4 X4.src4 NI4F.srcE4 NI4F.srcL4) :=
  fun L L' X hx hS => P4b.onNode_congr rfl fun κ _ => by
    simp only [P4b.c4E4_agree (L := L) (L' := L') (fun _ _ => rfl : Agree X X 275) le_rfl,
      P4b.TEb4_same X4.src4 NI4F.srcE4 NI4F.srcL4 κ hS (by omega)]

theorem ss_D4E4 : P4a.SameStab4 276 (P4b.D4E4 X4.src4 NI4F.srcE4 NI4F.srcL4) :=
  fun L L' X hx hS => P4b.onNode_congr rfl fun κ _ =>
    D2_congrL (P4b.TEb4_same X4.src4 NI4F.srcE4 NI4F.srcL4 κ hS (by omega))
      (P4b.c4E4_agree (fun _ _ => rfl : Agree X X 275) le_rfl)

theorem ss_pendE4 : P4a.SameStab4 326 (P4b.PendE4 X4.src4) := fun L L' X hx hS =>
  P4b.onNode_congr rfl fun κ _ => by
    simp only [P4b.zCG_same X4.src4 (P4b.ncR κ) hS (show 3 ≤ X.length by omega)]

theorem rd_zcwLr : T4.Reads 179 (P4b.ZCwLr4 X4.src4 NI4F.srcL4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ =>
    (P4b.zcwG_reads X4.src4 (NI4F.srcL4 κ) (P4b.lrR κ) (P4b.ncR κ) 169 (by omega)).mono
      (by have := (P4b.dims_le' κ).1; omega)

theorem rd_zcwE : T4.Reads 227 (P4b.ZCwE4 X4.src4 NI4F.srcE4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ => P4b.zcwE4_reads X4.src4 NI4F.srcE4 κ

theorem rd_endLr : T4.Reads 214 (P4b.EndBadLr4 X4.src4 NI4F.srcL4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ =>
    P4b.endBadG_reads X4.src4 (NI4F.srcL4 κ) (P4b.lrR κ) (P4b.ncR κ) 179 17 (by norm_num)
      (P4b.dims_le' κ).1

theorem rd_endE : T4.Reads 274 (P4b.EndBadE4 X4.src4 NI4F.srcE4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ => P4b.endBadE4_reads X4.src4 NI4F.srcE4 κ

theorem rd_DRS0X : T4.Reads 327 DRS0X := P4b.dRS0_4_reads (R := X4.src4) rd_far0X rd_PubX
theorem rd_DRS1X : T4.Reads 331 DRS1X := P4b.dRS1_4_reads (R := X4.src4) rd_far0X rd_PubX
theorem rd_DBX : T4.Reads 332 DBX := P4b.dB4_reads (R := X4.src4) rd_far0X

theorem ss_df12 : P4a.SameStab4 170 (P4a.DF4a X4.P4X 12) := by
  have h := P4a.df_ss4a X4.P4X_ok (P4a.sNode4 P4a.zwSame_zW) 12 le_rfl
  rw [phStart_hi.1] at h
  exact h.up 170

/-- **Phase `k`'s doom reads the same off two logs whose words agree**, on `X` of at least
`phStart4 k + 1` entries (`13 ≤ k ≤ 25`). -/
theorem dfhi_ss : ∀ k, 12 < k → k ≤ 25 → P4a.SameStab4 (phStart4 k + 1) (DFhi k) := by
  obtain ⟨-, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, -⟩ := phStart_hi
  have b20 := P4a.ss_reads4 rd_bg20X
  have b12 := P4a.ss_reads4 rd_bg12X
  have b16 := P4a.ss_reads4 rd_bg16X
  have d16 := P4a.ss_reads4 rd_D16X
  intro k hk1 hk2
  interval_cases k
  · rw [h13]
    exact (P4a.ss_msD4 ss_df12 ((b12.up 179).or (P4a.ss_reads4 rd_zcwLr)) (by norm_num)).up _
  · rw [h14]; exact (b12.up 180).or ss_D3Lr4
  · rw [h15]; exact (b12.up 214).or (P4a.ss_reads4 rd_endLr)
  · rw [h16]; exact d16
  · rw [h17]
    exact (P4a.ss_msD4 d16 ((b16.up 227).or (P4a.ss_reads4 rd_zcwE)) (by norm_num)).up _
  · rw [h18]; exact (b16.up 228).or ss_D3E4
  · rw [h19]; exact (b16.up 274).or (P4a.ss_reads4 rd_endE)
  · rw [h20]; exact (b20.up 275).or ss_batE4
  · rw [h21]; exact (b20.up 276).or ss_D4E4
  · rw [h22]; exact (b20.up 326).or ss_pendE4
  · rw [h23]; exact P4a.ss_reads4 rd_DRS0X
  · rw [h24]
    exact (P4a.ss_msD4 (P4a.ss_reads4 rd_DRS0X) (P4a.ss_reads4 rd_DRS1X) (by norm_num)).up _
  · rw [h25]; exact P4a.ss_reads4 rd_DBX

end SS

end FR.Snd.P4f
