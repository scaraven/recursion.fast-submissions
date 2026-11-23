-- New for lvm2 MP-B cap pruning (CAP-X4, 2026-11-17): the node output's semantics at S2GB (`outIRB`), proof-help of
-- `EXB_node` (`outIRS_run`'s twin with the size word and the π tail).
import LvmS2GBExtNodeTail
import LvmXSOut

/-!
# The node output at S2GB

* `outWordsB π w`: the output words (`outWordsS stB20` with the child's size `|reassembleB …|` and the π tail);
* **`decodeWit_outWordsB`**: they denote `XwitB π w`;
* **`outIRB_run`**: from a state whose heap holds the decoded message `w` at `mB`, on the tape of an `S` proof in the
  size range, `outIRB mB` appends `outWordsB π w`.
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.Replay

/-- The sent cap's bits of `C_main`'s level `i` at S2GB: `1` at level 0, the root (`0`) at levels 1, 2. -/
def capBB (i : ℕ) : ℕ := if i = 0 then 1 else 0

/-- **`C_main`'s level-`i` sent cap from π** (`2^c` digests at `capOffS stB20 i`). -/
def capSB (π : Proof) (i : ℕ) : List Digest :=
  (List.range (2 ^ capBB i)).map fun e => hdD π (capOffS stB20 i / 8 + 4 * e)

/-- **The node witness at S2GB** of an `S` proof (`b = 1`) whose decoded stream is `w` (`XwitS stB20` with the
left child `childWB stB20 w`). -/
def XwitB (π : Proof) (w : ℕ → Word) : Wit :=
  .node (hdD π 6) (leafStmt (hdD π 15) (pw π 14).toNat) (childWB stB20 w)
    ⟨WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat), [], sigRS stB20 π w⟩

/-! ## The size range on the tape -/

theorem szB_lt {π : Proof} (hs : SzB π) : π.size < 2 ^ 64 := by
  have h := sizes_P20B.1
  have e1 := h.1
  have e2 := h.2.2.2.2.2.2
  rw [SzB, e1, e2] at hs
  (clear * - hs; omega)

theorem szB_lo {π : Proof} (hs : SzB π) : 269336 ≤ π.size := by
  have e1 := sizes_P20B.1.1
  rw [SzB, e1] at hs
  exact hs.1

/-- π's packed words on the tape of a proof in the size range (`tape_pwN`). -/
theorem tape_pwB (c : Digest) (π : Proof) (L : Log) (hs : SzB π) {j : ℕ} (hj : j < 33667) :
    (extractorInput c π L).toArray.getD (5 + j) 0 = pw π j := by
  have := szB_lo hs
  rw [getD_toArray, tape_getD_proof c π L (by (clear * - j π hj this; omega)), pw, List.getD_eq_getElem]

theorem wsAt_tapeB (c : Digest) (π : Proof) (L : Log) (hs : SzB π) {a n : ℕ} (h : a + n ≤ 33667) :
    (List.range n).map (fun j => (extractorInput c π L).toArray.getD (5 + a + j) 0) = wsAt (pw π) a n :=
  List.map_congr_left fun j hj => by
    rw [Nat.add_assoc, tape_pwB c π L hs (by simp at hj; (clear * - a j n h hj; omega))]

/-! ## The child's words -/

theorem packBytes_wordsBytes_append (a : List Word) (b : List UInt8) :
    packBytes (wordsBytes a ++ b) = a ++ packBytes b := by
  induction a with
  | nil => rfl
  | cons w ws ih =>
    rw [Lvm.QLink.wordsBytes_cons, List.append_assoc, packBytes_append8 _ (wordBytes_length w), ih, ofLE_wordBytes,
      toWord_toNat', List.cons_append]

theorem reassembleB_data (W : ℕ → Word) :
    (reassembleB P20B (readTraceLS stB20 W)).data.toList =
      wordsBytes (pWordsS stB20 W) ++ tailB P20B (readTraceLS stB20 W) := by
  rw [← reassembleS_data stB20 outOK_stB20.planOk outOK_stB20.blkOk W]
  simp [reassembleB, reassembleS, reassemble]
  rfl

/-- **The node output's words** at S2GB. -/
def outWordsB (π : Proof) (w : ℕ → Word) : List Word :=
  toWord 1 :: wsAt (pw π) 6 4 ++ packBytes (leafStmt (hdD π 15) (pw π 14).toNat).toList ++
    (toWord (reassembleB P20B (readTraceLS stB20 (laneOf w))).size ::
      (pWordsS stB20 (laneOf w) ++ packBytes (tailB P20B (readTraceLS stB20 (laneOf w))))) ++
    trWordsS stB20 (laneOf w) ++ wsAt (sigCol w) 0 597 ++
    (toWord 48 :: toWord 0 :: wsAt (pw π) 10 4 ++ [pw π 14]) ++ [toWord 0] ++ sigWords (sigRS stB20 π w)

theorem size_reassembleB (W R : ℕ → Word) (hR : ∀ u < nCp, R (sgB + u) = W u) :
    (reassembleB P20B (readTraceLS stB20 W)).size = piStatic P20B + 32 * uncW R tlvB20 := by
  have h1 := size_reassembleS stB20 outOK_stB20.planOk outOK_stB20.blkOk W
  have h2 := reassembleS_data stB20 outOK_stB20.planOk outOK_stB20.blkOk W
  rw [outOK_stB20.pz] at h1
  have h5 : 8 * (pWordsS stB20 W).length = stB20.pz := by
    rw [← h1, ByteArray.size, ← Array.length_toList, h2, wordsBytes_length]
  rw [ByteArray.size, ← Array.length_toList, reassembleB_data, List.length_append, tailB_B20 W R hR,
    wordsBytes_length, wordsBytes_length, length_tailWs, h5, show stB20.pz = piStatic P20B from rfl]
  ring

theorem signed_leftB (w : ℕ → Word) :
    signedWords (childWB stB20 w) =
      (toWord (reassembleB P20B (readTraceLS stB20 (laneOf w))).size ::
        (pWordsS stB20 (laneOf w) ++ packBytes (tailB P20B (readTraceLS stB20 (laneOf w))))) ++
      trWordsS stB20 (laneOf w) ++ wsAt (sigCol w) 0 597 := by
  rw [signedWords, bytesWords, Array.length_toList]
  simp only [childWB]
  rw [show stB20.p = P20B from rfl, reassembleB_data, packBytes_wordsBytes_append,
    logWords_readTraceLS stB20 outOK_stB20.blkOk, sigWords_sigOfF]
  rfl

/-- The list reassociation of `witWords_XwitB`, over variables (an in-context `simp` costs ~24 M kernel hb). -/
private theorem witWords_assocB (p s2 : Word) (s1 s3 s4 s5 s6 s7 s8 s9 : List Word) :
    toWord 1 :: s3 ++ s1 ++ (s2 :: (s8 ++ s9) ++ s7 ++ s5) ++
        (toWord 48 :: toWord 0 :: s4 ++ [p] ++ [toWord 0] ++ s6) =
      toWord 1 :: s3 ++ s1 ++ s2 :: (s8 ++ s9) ++ s7 ++ s5 ++ (toWord 48 :: toWord 0 :: s4 ++ [p]) ++
        [toWord 0] ++ s6 := by
  simp only [List.cons_append, List.append_assoc]

theorem witWords_XwitB (π : Proof) (w : ℕ → Word) : witWords (XwitB π w) = outWordsB π w := by
  rw [XwitB, witWords, signed_leftB, signed_rightS, hdD, packBytes_digW (length_wsAt _ _ _), outWordsB]
  exact witWords_assocB ..

theorem fits_XwitB (π : Proof) (w : ℕ → Word) : (XwitB π w).Fits := by
  have hN : nCp = 278528 := rfl
  have hL := outOK_stB20.lanes
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show (reassembleB P20B (readTraceLS stB20 (laneOf w))).size < 2 ^ 64
    rw [size_reassembleB (laneOf w) (fun a => laneOf w (a - sgB)) (fun u _ => by rw [Nat.add_sub_cancel_left])]
    have e1 := sizes_P20B.1.1
    have hu := uncW_le (fun a => laneOf w (a - sgB)) tlvB20 wB2M
    have hb := tlvLay_B20.2.2
    rw [e1]; simp only [wB2M] at hu hb; omega
  · show (readTraceLS stB20 (laneOf w)).length < _
    rw [length_readTraceLS]; exact outOK_stB20.qs
  · intro e he
    simp only [childWB, readTraceLS, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨x, hx, rfl⟩
    · simp [q0Ent, wordBytes_length]
    · obtain ⟨-, h2⟩ := walk_lt 6 (lensLS stB20) x hx
      have h3 : lanesOf (lensLS stB20) = ((blocksS stB20).map Blk.lanes).sum := lanesOf_flatMapB _
      simp only [entAt, bArr_size, wordsBytes_length, length_wsAt]
      (clear * - x hN hL h2 h3; omega)
  · exact (sigCol w 0).isLt
  · simp [childWB, sigOfF]
  · simp [childWB, sigOfF]
  · rw [WitnessSending.size_encode_leaf]; norm_num
  · simp
  · simp
  · unfold sigRS; split
    · exact BitVec.isLt _
    · exact (pw π 19).isLt
  · unfold sigRS; split <;> simp [sigOfF, Lvm.CT.sigOfP]
  · unfold sigRS; split <;> simp [sigOfF, Lvm.CT.sigOfP]

/-- **The node output's words denote the node witness** at S2GB. -/
theorem decodeWit_outWordsB (π : Proof) (w : ℕ → Word) : decodeWit (outWordsB π w) = some (XwitB π w) := by
  rw [← witWords_XwitB, decodeWit_witWords _ (fits_XwitB π w)]


/-! ## The bitmaps' layout -/

theorem bm_mem : ∀ (ls : List TLv) (b : ℕ), BmChain b ls → ∀ l ∈ ls, b ≤ l.bm ∧ l.bm + 2 ^ l.m ≤ bmEnd b ls
  | [], _, _, _, h => by simp at h
  | l :: ls, b, ⟨h1, h2⟩, l', hl' => by
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact ⟨h1.ge, by rw [h1]; exact le_bmEnd ls _⟩
    · have := bm_mem ls _ h2 l' hl'
      exact ⟨le_trans (Nat.le_add_right _ _) this.1, this.2⟩

/-! ## The run -/

set_option maxRecDepth 20000 in
/-- **The node output's run at S2GB** (`outIRS_run`'s twin): from a state whose heap holds the decoded message `w`
at `mB`, on the tape of an `S` proof in the size range, `outIRB mB` appends `outWordsB π w`. -/
theorem outIRB_run (c : Digest) (π : Proof) (L : Log) (hs : SzB π)
    (s : St) (hM : Inv s.M) {mB : ℕ} (hmB : wB2M + 512 ≤ mB) (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size)
    (w : ℕ → Word) (hw : ∀ i < 2 ^ 19, Lvm.X.rd s.M (mB + i) = w i) :
    (semXIR (extractorInput c π L).toArray (outIRB mB) s).o.toList = s.o.toList ++ outWordsB π w := by
  set I := (extractorInput c π L).toArray with hI
  have hs0 := hM.1
  have hTB : ∀ R : ℕ → Word, (∀ u < nCp, R (sgB + u) = laneOf w u) →
      tailB P20B (readTraceLS stB20 (laneOf w)) = wordsBytes (tailWs R tlvB20) := fun R hR => tailB_B20 _ R hR
  have hSZ : ∀ R : ℕ → Word, (∀ u < nCp, R (sgB + u) = laneOf w u) →
      (reassembleB P20B (readTraceLS stB20 (laneOf w))).size = piStatic P20B + 32 * uncW R tlvB20 :=
    fun R hR => size_reassembleB _ R hR
  have hL := tlvLay_B20
  have hwB : wB2M = 2097152 := rfl
  have hsgB : sgB = 16842752 := rfl
  have hnCp : nCp = 278528 := rfl
  have hregs : regs = 256 := rfl
  -- 1. the tag
  obtain ⟨o1, f1⟩ := emitIR_sem I s hM (toWord 1)
  have hM1 := inv_sem I (wf_emitIR (toWord 1)) hM
  have z1 := size_sem I (emitIR (toWord 1)) s
  rw [outIRB]
  generalize tlvB20 = ls at hTB hSZ hL ⊢
  obtain ⟨hlv, hch, hend⟩ := hL
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 1)) s = s1 at o1 f1 hM1 z1
  -- 2. `c_L`
  obtain ⟨o2, f2, hM2, z2⟩ := tcpIR_sem I s1 hM1 (a := 11) (n := 4) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (tcpIR 11 4) s1 = s2 at o2 f2 hM2 z2
  -- 3. `leafStmt h n`
  obtain ⟨o3, f3⟩ := leafStmtIR_sem I s2 hM2 (hW := 20) (nW := 19) (hdD π 15) (pw π 14).toNat
    (fun i hi => by
      rw [hdD, packBytes_digW (length_wsAt _ _ _), wsAt, List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map, List.getElem_range, show 20 + i = 5 + (15 + i) by omega,
        tape_pwB c π L hs (by omega)])
    (by rw [show 19 = 5 + 14 from rfl, tape_pwB c π L hs (by omega), toWord_toNat'])
    (pw π 14).isLt (by norm_num) (by norm_num)
  have hM3 := inv_sem I (wf_leafStmtIR 20 19) hM2
  have z3 := size_sem I (leafStmtIR 20 19) s2
  rw [semXIR_seq]
  generalize semXIR I (leafStmtIR 20 19) s2 = s3 at o3 f3 hM3 z3
  -- the heap so far
  have h3 : ∀ y, regs ≤ y → Lvm.X.rd s3.M y = Lvm.X.rd s.M y := fun y hy => by
    simp only [regs] at hy
    rw [f3 y (by simp only [regs]; omega),
      f2 y (by simp only [eW]; omega) (by simp only [eP]; omega) (by simp only [eN]; omega)
        (by simp only [eC]; omega) (by simp only [cTmp]; omega), f1 y (by simp only [eW]; omega)]
  have zz3 : s3.M.size = s.M.size := by rw [z3, z2, z1]
  -- 4. the stream copy
  obtain ⟨c1, c2, hM5, z5, o5⟩ := copyIR_sem I s3 hM3 (mB := mB) (by simp only [regs] at hwB ⊢; omega) hmB2
    (by rw [zz3]; exact hsz)
  rw [semXIR_seq]
  generalize semXIR I (copyIR mB) s3 = s5 at c1 c2 hM5 z5 o5
  have hlane : ∀ u < nCp, Lvm.X.rd s5.M (sgB + u) = laneOf w u := fun u hu => by
    rw [c1 u hu, h3 _ (by simp only [regs] at hwB ⊢; omega), hw _ (crecIdx_lt hu)]; rfl
  have hsig : ∀ j < 2 ^ 19, Lvm.X.rd s5.M (mB + j) = w j := fun j hj => by
    rw [c2 _ (by simp only [regs] at hwB ⊢; omega) (.inl (by omega)), h3 _ (by simp only [regs] at hwB ⊢; omega),
      hw _ hj]
  have zz5 : s5.M.size = s.M.size := by rw [z5, zz3]
  -- 5. the bitmaps
  have hlv1 : ∀ l ∈ ls, l.m ≤ 64 ∧ ∀ p ∈ l.pos, bmEnd wB2M ls ≤ p.1 ∧ p.1 + 1 < 2 ^ 64 ∧ p.2 < 64 :=
    fun l hl => ⟨(hlv l hl).2.1, fun p hp => by
      have := (hlv l hl).2.2.1 p hp
      clear * - this hend hwB hsgB hnCp hregs
      exact ⟨by omega, by omega, this.2.2⟩⟩
  obtain ⟨b1, b2, b3, hM6, z6⟩ := bmIR_sem I ls wB2M s5 hM5 (by rw [hwB, hregs]; norm_num) hch
    (by clear * - zz5 hsz hend hwB hsgB hnCp hregs; omega) (by clear * - zz5 hsz hend hwB hsgB hnCp hregs; omega) hlv1
  rw [semXIR_seq]
  generalize semXIR I (bmIR ls) s5 = s6 at b1 b2 b3 hM6 z6
  have hbm : ∀ l ∈ ls, regs ≤ l.bm ∧ l.bm + 2 ^ l.m < 2 ^ 64 := fun l hl => by
    have := bm_mem _ _ hch l hl
    clear * - this hend hwB hsgB hnCp hregs
    exact ⟨by omega, by omega⟩
  -- 6. the size word
  have hcnt : (ls.map fun l => cntZ (Lvm.X.rd s6.M) l.bm (2 ^ l.m)).sum = uncW (Lvm.X.rd s5.M) ls := by
    rw [uncW]
    exact congrArg List.sum (List.map_congr_left fun l hl => cntZ_bitmap _ _ l (b3 l hl))
  have hu := uncW_le (Lvm.X.rd s5.M) ls wB2M
  obtain ⟨d1, d2, hM7, z7⟩ := sizeWIR_sem I (piStatic P20B) ls s6 hM6 hbm (by
    rw [hcnt, sizes_P20B.1.1]; clear * - hu hend hwB hsgB hnCp hregs; omega)
  rw [hcnt] at d1
  rw [semXIR_seq]
  generalize semXIR I (sizeWIR (piStatic P20B) ls) s6 = s7 at d1 d2 hM7 z7
  -- the heap above the bitmaps is the copy's
  have h7 : ∀ y, wB2M + 512 ≤ y → Lvm.X.rd s7.M y = Lvm.X.rd s5.M y := fun y hy => by
    clear * - d2 b2 hy hend hwB hsgB hnCp hregs
    rw [d2 y (not_tscr (by omega)) (by simp only [tN]; omega), b2 y (not_tscr (by omega)) (.inr (by omega))]
  have h7b : ∀ l ∈ ls, ∀ x < 2 ^ l.m, Lvm.X.rd s7.M (l.bm + x) = if covW (Lvm.X.rd s5.M) l x then 1 else 0 :=
    fun l hl x hx => by
      have := bm_mem _ _ hch l hl
      rw [d2 _ (not_tscr (by clear * - this hx hend hwB hsgB hnCp hregs; omega)) (by simp only [tN]; clear * - this hx hend hwB hsgB hnCp hregs; omega),
        b3 l hl x hx]
  -- 7. the proof's segment
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := setR_sem I s7 hM7 sgB
  rw [semXIR_seq]
  generalize semXIR I (setR sgB) s7 = s8 at r1 r2 r3 r4 r5 r6 r7
  have hc8 : Ctx s7.M sgB false s8 := ⟨r1, r2, r3, r4, by rw [r5]; simp⟩
  have hA := hA_apC (R := sgB) (by simp only [regs, sgB]; norm_num) (by simp only [sgB]; norm_num)
  obtain ⟨g1, g2, g3⟩ := seg_step I hA (pSegS stB20) outOK_stB20.segs.2.2.1 outOK_stB20.segs.2.2.2 s8 hc8 r6
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 (pSegS stB20)) s8 = s9 at g1 g2 g3
  -- 8. the π tail
  have hhq : ∀ l ∈ ls, ∀ x < 2 ^ l.m, sgB ≤ l.heap.getD (x / 2) 0 ∧ l.heap.getD (x / 2) 0 + 8 ≤ sgB + nCp :=
    fun l hl x hx => by
      have h2 := hlv l hl
      have hy : x / 2 < l.heap.length := by
        rw [h2.2.2.2.1]
        have := two_pow_pred h2.1
        clear * - hx this
        omega
      exact h2.2.2.2.2 _ (by rw [List.getD_eq_getElem _ _ hy]; exact List.getElem_mem hy)
  have htl : ∀ l ∈ ls, ∀ x < 2 ^ l.m, regs ≤ l.bm + x ∧ l.bm + x < 2 ^ 64 ∧ regs ≤ l.heap.getD (x / 2) 0 ∧
      l.heap.getD (x / 2) 0 + 8 < 2 ^ 64 := fun l hl x hx => by
    have h1 := bm_mem _ _ hch l hl
    have h3 := hhq l hl x hx
    clear * - h1 h3 hx hend hwB hsgB hnCp hregs
    exact ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨t1, t2, hM10, z10⟩ := tailIR_sem I ls s9 g2.inv htl
  rw [semXIR_seq]
  have eT : (ls.flatMap fun l => (List.range (2 ^ l.m)).flatMap fun x =>
      if Lvm.X.rd s9.M (l.bm + x) = 0 then
        (List.range 4).map (fun k => Lvm.X.rd s9.M (l.heap.getD (x / 2) 0 + 4 * (x % 2) + k)) else []) =
      tailWs (Lvm.X.rd s5.M) ls := by
    refine List.flatMap_congr fun l hl => List.flatMap_congr fun x hx => ?_
    have hx' := List.mem_range.1 hx
    have hb := htl l hl x hx'
    rw [g2.heap _ hb.1, h7b l hl x hx']
    by_cases hcv : covW (Lvm.X.rd s5.M) l x
    · simp [hcv]
    · simp only [hcv, Bool.false_eq_true, if_false, if_true]
      refine List.map_congr_left fun k hk => ?_
      have hk' := List.mem_range.1 hk
      have h3 := hhq l hl x hx'
      have hx2 := Nat.mod_lt x (show 2 > 0 by norm_num)
      rw [g2.heap _ (by clear * - h3 hx2 hk' hwB hsgB hnCp hregs; omega), h7 _ (by clear * - h3 hx2 hk' hwB hsgB hnCp hregs; omega)]
  rw [eT] at t1
  generalize semXIR I (tailIR ls) s9 = s10 at t1 t2 hM10 z10
  have hc10 : Ctx s7.M sgB false s10 :=
    ⟨hM10, by rw [z10, g2.size], fun y hy => by
      rw [t2 y (by simp only [tA, regs] at hy ⊢; omega) (by simp only [tB, regs] at hy ⊢; omega), g2.heap y hy],
      by rw [t2 _ (by decide) (by decide), g2.r], by rw [t2 _ (by decide) (by decide)]; exact g2.k⟩
  have hb10 : Lvm.X.rd s10.M (oBd 0) = toWord 0 := by rw [t2 _ (by decide) (by decide), g3]
  -- 9. the trace's segment
  obtain ⟨k1, k2, k3⟩ := seg_step I hA (trSegS stB20) outOK_stB20.segs.1 outOK_stB20.segs.2.1 s10 hc10 hb10
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 (trSegS stB20)) s10 = s11 at k1 k2 k3
  -- the source is the stream below `T`
  have hT := outOK_stB20.lanes
  have hsrc : ∀ v < 6 + ((blocksS stB20).map Blk.lanes).sum, src s7.M apC sgB v = laneOf w v := fun v hv => by
    clear * - hv hT h7 hlane hwB hsgB hnCp hregs
    rw [src_apC _ (by simp only [sgB, nCp] at hT ⊢; omega), h7 _ (by omega), hlane v (by omega)]
  have eP : segOut (src s7.M apC sgB) false 0 (pSegS stB20) = pWordsS stB20 (laneOf w) := by
    rw [segOut_pSegS stB20 outOK_stB20.blkOk, ← packBytes_reassembleS stB20 outOK_stB20.planOk outOK_stB20.blkOk,
      readTraceLS_congr stB20 hsrc, packBytes_reassembleS stB20 outOK_stB20.planOk outOK_stB20.blkOk]
  have eTr : segOut (src s7.M apC sgB) false 0 (trSegS stB20) = trWordsS stB20 (laneOf w) := by
    rw [segOut_trSegS, ← logWords_readTraceLS stB20 outOK_stB20.blkOk, readTraceLS_congr stB20 hsrc,
      logWords_readTraceLS stB20 outOK_stB20.blkOk]
  -- 10. the signature column
  have hM11 := k2.inv
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := setR_sem I s11 hM11 (sigB mB)
  rw [semXIR_seq]
  generalize semXIR I (setR (sigB mB)) s11 = s12 at u1 u2 u3 u4 u5 u6 u7
  have hc12 : Ctx s7.M (sigB mB) false s12 :=
    ⟨u1, by rw [u2, k2.size], fun y hy => by rw [u3 y hy, k2.heap y hy], u4, by rw [u5]; simp⟩
  have hA' := hA_apC (R := sigB mB) (by simp only [regs, sigB] at hwB ⊢; omega)
    (by simp only [sigB, sgB] at hmB2 ⊢; omega)
  obtain ⟨v1, v2, v3⟩ := seg_step I hA' (.cp 0 597) (by decide) (by decide) s12 hc12 u6
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 (.cp 0 597)) s12 = s13 at v1 v2 v3
  have eS : segOut (src s7.M apC (sigB mB)) false 0 (.cp 0 597) = wsAt (sigCol w) 0 597 := by
    simp only [segOut, wsAt, Nat.zero_add]
    exact List.map_congr_left fun j hj => by
      have hj' : j < 597 := by simpa using hj
      clear * - hj' hmB hmB2 h7 hsig hwB hsgB hnCp hregs
      rw [src_apC _ (by simp only [sigB, sgB] at hmB2 ⊢; omega), h7 _ (by simp only [sigB]; omega), sigB,
        Nat.add_assoc, hsig _ (by omega)]; rfl
  -- 11–15. the right child
  have hM13 := v2.inv
  obtain ⟨p1, q1⟩ := emitIR_sem I s13 hM13 (toWord 48)
  have hM14 := inv_sem I (wf_emitIR (toWord 48)) hM13
  have z14 := size_sem I (emitIR (toWord 48)) s13
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 48)) s13 = s14 at p1 q1 hM14 z14
  obtain ⟨p2, q2⟩ := emitIR_sem I s14 hM14 (toWord 0)
  have hM15 := inv_sem I (wf_emitIR (toWord 0)) hM14
  have z15 := size_sem I (emitIR (toWord 0)) s14
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 0)) s14 = s15 at p2 q2 hM15 z15
  obtain ⟨p3, q3, hM16, z16⟩ := tcpIR_sem I s15 hM15 (a := 15) (n := 5) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (tcpIR 15 5) s15 = s16 at p3 q3 hM16 z16
  obtain ⟨p4, q4⟩ := emitIR_sem I s16 hM16 (toWord 0)
  have hM17 := inv_sem I (wf_emitIR (toWord 0)) hM16
  have z17 := size_sem I (emitIR (toWord 0)) s16
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 0)) s16 = s17 at p4 q4 hM17 z17
  -- the right leaf's signature from the window (`leafOut`)
  have hli : stB20.p.leafOut = true := rfl
  have hR : (semXIR I (rsigIR stB20 mB) s17).o.toList = s17.o.toList ++ sigWords (sigRS stB20 π w) := by
    rw [rsigIR, if_pos hli, sigRS_li hli, semXIR_seq]
    have hh17 : ∀ y, regs ≤ y → Lvm.X.rd s17.M y = Lvm.X.rd s7.M y := fun y hy => by
      simp only [regs] at hy
      rw [q4 y (by simp only [eW]; omega), q3 y (by simp only [eW]; omega)
        (by simp only [Lvm.X.eP]; omega) (by simp only [eN]; omega)
        (by simp only [eC]; omega) (by simp only [cTmp]; omega),
        q2 y (by simp only [eW]; omega), q1 y (by simp only [eW]; omega),
        v2.heap y (by simp only [regs]; omega)]
    have zz17 : s17.M.size = s7.M.size := by rw [z17, z16, z15, z14, v2.size]
    obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := setR_sem I s17 hM17 (sigB mB + 1024)
    generalize semXIR I (setR (sigB mB + 1024)) s17 = s18 at w1 w2 w3 w4 w5 w6 w7
    have hc18 : Ctx s7.M (sigB mB + 1024) false s18 :=
      ⟨w1, by rw [w2, zz17], fun y hy => by rw [w3 y hy, hh17 y hy], w4, by rw [w5]; simp⟩
    have hA2 := hA_apC (R := sigB mB + 1024) (by simp only [regs, sigB] at hwB ⊢; omega)
      (by simp only [sigB, sgB] at hmB2 ⊢; omega)
    obtain ⟨x1, -, -⟩ := seg_step I hA2 slSegC okSeg_slSegC (by rw [depthSeg_slSegC]; decide) s18 hc18 w6
    rw [x1, w7, segOut_slSegC _ (fun j => w (17 * 2 ^ 14 + 1024 + j)) (fun v hv => ?_)]
    clear * - hv hmB hmB2 h7 hsig hwB hsgB hnCp hregs
    rw [src_apC _ (by simp only [sigB, sgB] at hmB2 ⊢; omega), h7 _ (by simp only [sigB]; omega), sigB,
      show mB + 17 * 2 ^ 14 + 1024 + v = mB + (17 * 2 ^ 14 + 1024 + v) by omega, hsig _ (by omega)]
  -- the words
  have hsize : toWord (piStatic P20B + 32 * uncW (Lvm.X.rd s5.M) ls) =
      toWord (reassembleB P20B (readTraceLS stB20 (laneOf w))).size := by
    rw [hSZ (Lvm.X.rd s5.M) hlane]
  have htail : tailWs (Lvm.X.rd s5.M) ls = packBytes (tailB P20B (readTraceLS stB20 (laneOf w))) := by
    rw [hTB (Lvm.X.rd s5.M) hlane, packBytes_wordsBytes]
  rw [hR, p4, p3, p2, p1, v1, u7, k1, t1, g1, r7, d1, b1, o5, o3, o2, o1, eP, eTr, eS, hsize, htail]
  have t1' := wsAt_tapeB c π L hs (a := 6) (n := 4) (by norm_num)
  have t2' := wsAt_tapeB c π L hs (a := 10) (n := 5) (by norm_num)
  simp only [show (5 + 6 : ℕ) = 11 from rfl, show (5 + 10 : ℕ) = 15 from rfl] at t1' t2'
  rw [t1', t2', outWordsB, show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
  simp [wsAt, List.append_assoc]

/-- **The node output's semantics at S2GB**: the output is the node witness's words. -/
theorem outIRB_sem (c : Digest) (π : Proof) (L : Log) (hs : SzB π)
    (s : St) (hM : Inv s.M) {mB : ℕ} (hmB : wB2M + 512 ≤ mB) (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size)
    (w : ℕ → Word) (hw : ∀ i < 2 ^ 19, Lvm.X.rd s.M (mB + i) = w i) :
    ∃ ws, (semXIR (extractorInput c π L).toArray (outIRB mB) s).o.toList = s.o.toList ++ ws ∧
      decodeWit ws = some (XwitB π w) :=
  ⟨_, outIRB_run c π L hs s hM hmB hmB2 hsz w hw, decodeWit_outWordsB π w⟩

end Lvm.XB
