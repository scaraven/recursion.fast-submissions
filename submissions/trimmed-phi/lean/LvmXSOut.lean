-- New for lvm2 E2F (E2F-L, 2026-11-13): the node output's facts at a stage (owner: E2F-L's helper H1). Ports of
-- `LvmXOut`/`LvmXOutSeg`/`LvmXReasm`/`LvmXNodeIR`/`LvmXNode`/`LvmXTop`'s output facts with the stage's blocks in place
-- of `blocks pX` (the words: `LvmXSOutW`). The frozen interface statements (`-- E2F-L frozen`) are consumed by
-- `LvmXSComputes`, `LvmXSNodeSem` and `LvmXSExtEq`; `OutOK` (the stage's decided static facts) is the helper's.
import LvmXSOutW

-- (GOLF2: 2 declarations that `certified` does not use moved verbatim to `LvmXSComputesOff`, outside its import closure.)

/-!
# The node output at a stage: facts

* **`OutOK st`**: the stage's static facts the output needs (decided at `stF20`: `outOK_stF20`, one kernel
  evaluation).
* `XwitS st π w` (the node witness with the left child `childWS st w`), `outWordsS st π w` (the output's words),
  `witWords_XwitS`, `decodeWit_outWordsS`;
* the program facts **`wf_outIRS`**, `noLoopT_outIRS`, **`cost_outIRS`**, **`outs_outIRS`**, `sizeIR_outIRS`;
* the semantics **`outIRS_sem`**.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-- **The stage's static facts for the node output** (blocks reassemblable, lengths, lanes, `|π|`, the plan's
flag, the segments' measures; decided per stage). The measures' bounds are what the frozen program bounds leave
after the output's fixed parts. -/
structure OutOK (st : XStage) : Prop where
  /-- The plan's walk meets its static conditions (`PlanOkS`'s flag). -/
  planOk : (Replay.planItems st.p Replay.w0 st.items).2.ok = true
  /-- Every block is a seed or FS query or an opening, lane-aligned, its segments' counts in range. -/
  blks : (blocksS st).all (fun b => blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b)) = true
  /-- The reassembled proof has `|π|` bytes. -/
  pz : 8 + 8 * ((blocksS st).map blkPOutsL).sum = st.pz
  /-- `|π|` holds the header's packed words `0 … 615`. -/
  pzLo : 4928 ≤ st.pz
  /-- `|π|` fits a word. -/
  pzHi : st.pz < 2 ^ 64
  /-- The child's stream fits the copied lanes. -/
  lanes : 6 + ((blocksS st).map Blk.lanes).sum ≤ nCp
  /-- The trace's entry count fits a word. -/
  qs : qSS st < 2 ^ 64
  /-- The segments' cost. -/
  cost : ((blocksS st).map blkPCostL).sum + ((blocksS st).map blkTCostL).sum ≤ 7128485
  /-- The segments' outputs. -/
  outs : ((blocksS st).map blkPOutsL).sum + ((blocksS st).map blkTOutsL).sum ≤ 163533
  /-- The segments' sizes. -/
  size : ((blocksS st).map blkPSizeL).sum + ((blocksS st).map blkTSizeL).sum ≤ 250000

theorem OutOK.blkOk {st : XStage} (hst : OutOK st) : (blocksS st).all blkOkS = true :=
  List.all_eq_true.mpr fun b hb => by
    have := List.all_eq_true.mp hst.blks b hb
    simp only [Bool.and_eq_true] at this
    exact this.1.1

theorem OutOK.segs {st : XStage} (hst : OutOK st) :
    okSeg (trSegS st) = true ∧ depthSeg (trSegS st) ≤ 2 ∧ okSeg (pSegS st) = true ∧ depthSeg (pSegS st) ≤ 2 :=
  segsS_ok st (List.all_eq_true.mpr fun b hb => by
    have := List.all_eq_true.mp hst.blks b hb
    simp only [Bool.and_eq_true] at this ⊢
    exact ⟨this.1.2, this.2⟩)

/-! ## The node witness and its words -/

/-- **The node witness** of an `S` proof (`b = 1`) whose decoded stream is `w`, at a stage (`Xwit`). -/
def XwitS (st : XStage) (π : Proof) (w : ℕ → Word) : Wit :=
  .node (hdD π 6) (leafStmt (hdD π 15) (pw π 14).toNat) (childWS st w)
    ⟨WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat), [], sigOfF fun j => pw π (19 + j)⟩

/-- **The node output's words** at a stage (`outWords`). -/
def outWordsS (st : XStage) (π : Proof) (w : ℕ → Word) : List Word :=
  toWord 1 :: wsAt (pw π) 6 4 ++ packBytes (leafStmt (hdD π 15) (pw π 14).toNat).toList ++
    (toWord st.pz :: pWordsS st (laneOf w)) ++ trWordsS st (laneOf w) ++ wsAt (sigCol w) 0 597 ++
    (toWord 48 :: toWord 0 :: wsAt (pw π) 10 4 ++ [pw π 14]) ++ [toWord 0] ++
    wsAt (fun j => pw π (19 + j)) 0 597

theorem size_childWS (st : XStage) (hst : OutOK st) (w : ℕ → Word) : (childWS st w).π.size = st.pz :=
  (size_reassembleS st hst.planOk hst.blkOk _).trans hst.pz

theorem signed_leftS (st : XStage) (hst : OutOK st) (w : ℕ → Word) :
    signedWords (childWS st w) =
      (toWord st.pz :: pWordsS st (laneOf w)) ++ trWordsS st (laneOf w) ++ wsAt (sigCol w) 0 597 := by
  have hl : (childWS st w).π.data.toList.length = st.pz := by
    rw [Array.length_toList]; exact size_childWS st hst w
  rw [signedWords, bytesWords, hl]
  simp only [childWS]
  rw [packBytes_reassembleS st hst.planOk hst.blkOk, logWords_readTraceLS st hst.blkOk, sigWords_sigOfF]

theorem witWords_XwitS (st : XStage) (hst : OutOK st) (π : Proof) (w : ℕ → Word) :
    witWords (XwitS st π w) = outWordsS st π w := by
  rw [XwitS, witWords, signed_leftS st hst, signed_right, hdD, packBytes_digW (length_wsAt _ _ _), outWordsS]
  simp only [List.cons_append, List.append_assoc]

theorem fits_XwitS (st : XStage) (hst : OutOK st) (π : Proof) (w : ℕ → Word) : (XwitS st π w).Fits := by
  have hN : nCp = 278528 := rfl
  have hL := hst.lanes
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [size_childWS st hst]; exact hst.pzHi
  · show (readTraceLS st (laneOf w)).length < _
    rw [length_readTraceLS]; exact hst.qs
  · intro e he
    simp only [childWS, readTraceLS, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨x, hx, rfl⟩
    · simp [q0Ent, wordBytes_length]
    · obtain ⟨-, h2⟩ := walk_lt 6 (lensLS st) x hx
      have h3 : lanesOf (lensLS st) = ((blocksS st).map Blk.lanes).sum := lanesOf_flatMapB _
      simp only [entAt, bArr_size, wordsBytes_length, length_wsAt]
      (clear * - x st hN hL h2 h3; omega)
  · exact (sigCol w 0).isLt
  · simp [childWS, sigOfF]
  · simp [childWS, sigOfF]
  · rw [WitnessSending.size_encode_leaf]; norm_num
  · simp
  · simp
  · exact (pw π 19).isLt
  · simp [sigOfF]
  · simp [sigOfF]

/-- **The node output's words denote the node witness.** -/
theorem decodeWit_outWordsS (st : XStage) (hst : OutOK st) (π : Proof) (w : ℕ → Word) :
    decodeWit (outWordsS st π w) = some (XwitS st π w) := by
  rw [← witWords_XwitS st hst, decodeWit_witWords _ (fits_XwitS st hst π w)]

/-! ## The program: well formed, no `loopT`, cost, outputs, size -/

theorem wf_outIRS (st : XStage) (hst : OutOK st) (m : ℕ) : WF (outIRS st m) := by
  have hs := hst.segs
  simp only [outIRS, WF]
  refine ⟨wf_emitIR _, wf_tcpIR _ _, wf_leafStmtIR _ _, wf_emitIR _, wf_copyIR _, ?_, wf_segIR _ _ _ (by
    have := hs.2.2.2; (clear * - st hs; omega)), wf_segIR _ _ _ (by have := hs.2.1; (clear * - st hs; omega)), ?_,
    wf_segIR _ _ _ (by decide), wf_emitIR _, wf_emitIR _, wf_tcpIR _ _, wf_emitIR _, wf_tcpIR _ _⟩ <;>
  simp +decide [setR, WF, Prim.dst, oR, oKF, oBd]

theorem noLoopT_outIRS (st : XStage) (m : ℕ) : NoLoopT (outIRS st m) :=
  ⟨noLoopT_emitIR _, noLoopT_tcpIR _ _, noLoopT_leafStmtIR _ _, noLoopT_emitIR _, noLoopT_copyIR _,
    noLoopT_setR _, noLoopT_segIR _ _ _, noLoopT_segIR _ _ _, noLoopT_setR _, noLoopT_segIR _ _ _,
    noLoopT_emitIR _, noLoopT_emitIR _, noLoopT_tcpIR _ _, noLoopT_emitIR _, noLoopT_tcpIR _ _⟩

/-! The segments' measures, block by block (`LvmXTop`'s `segPCs` …, private there). -/

theorem segPCsS : ∀ (u : ℕ) (bs : List Blk), segCost (blkPSegs u bs) = (bs.map blkPCostL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    have : segCost (blkPSeg u b) + 1 = blkPCostL b := by
      rcases b with ⟨c, len⟩ | ⟨t, row, path⟩
      · cases c <;> rfl
      · rfl
    rw [blkPSegs, segCost, segPCsS _ bs, List.map_cons, List.sum_cons, ← this]; (clear * - u b bs; omega)

theorem segPOsS : ∀ (u : ℕ) (bs : List Blk), segOuts (blkPSegs u bs) = (bs.map blkPOutsL).sum
  | _, [] => rfl
  | u, b :: bs => by
    have : segOuts (blkPSeg u b) = blkPOutsL b := by
      rcases b with ⟨c, len⟩ | ⟨t, row, path⟩
      · cases c <;> rfl
      · rfl
    rw [blkPSegs, segOuts, segPOsS _ bs, List.map_cons, List.sum_cons, this]

theorem segPSsS : ∀ (u : ℕ) (bs : List Blk), segSize (blkPSegs u bs) = (bs.map blkPSizeL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    have : segSize (blkPSeg u b) + 1 = blkPSizeL b := by
      rcases b with ⟨c, len⟩ | ⟨t, row, path⟩
      · cases c <;> rfl
      · rfl
    rw [blkPSegs, segSize, segPSsS _ bs, List.map_cons, List.sum_cons, ← this]; (clear * - u b bs; omega)

theorem segTCsS : ∀ (u : ℕ) (bs : List Blk), segCost (blkTSegs u bs) = (bs.map blkTCostL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    have : segCost (blkTSeg u b) + 1 = blkTCostL b := by cases b <;> rfl
    rw [blkTSegs, segCost, segTCsS _ bs, List.map_cons, List.sum_cons, ← this]; (clear * - u b bs; omega)

theorem segTOsS : ∀ (u : ℕ) (bs : List Blk), segOuts (blkTSegs u bs) = (bs.map blkTOutsL).sum
  | _, [] => rfl
  | u, b :: bs => by
    have : segOuts (blkTSeg u b) = blkTOutsL b := by cases b <;> rfl
    rw [blkTSegs, segOuts, segTOsS _ bs, List.map_cons, List.sum_cons, this]

theorem segTSsS : ∀ (u : ℕ) (bs : List Blk), segSize (blkTSegs u bs) = (bs.map blkTSizeL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    have : segSize (blkTSeg u b) + 1 = blkTSizeL b := by cases b <;> rfl
    rw [blkTSegs, segSize, segTSsS _ bs, List.map_cons, List.sum_cons, ← this]; (clear * - u b bs; omega)

theorem segCost_pSegS (st : XStage) : segCost (pSegS st) = ((blocksS st).map blkPCostL).sum + 5 := by
  simp only [pSegS, segCost, segPCsS]; (clear * - st; omega)

theorem segCost_trSegS (st : XStage) : segCost (trSegS st) = ((blocksS st).map blkTCostL).sum + 208 := by
  simp only [trSegS, segCost, segTCsS]; (clear * - st; omega)

theorem segOuts_pSegS (st : XStage) : segOuts (pSegS st) = ((blocksS st).map blkPOutsL).sum + 1 := by
  simp only [pSegS, segOuts, segPOsS]; (clear * - st; omega)

theorem segOuts_trSegS (st : XStage) : segOuts (trSegS st) = ((blocksS st).map blkTOutsL).sum + 7 := by
  simp only [trSegS, segOuts, segTOsS]; (clear * - st; omega)

theorem cost_outIRS (st : XStage) (hst : OutOK st) (m t : ℕ) : cost (outIRS st m) t ≤ 15800000 := by
  have h1 := cost_segIR apC (pSegS st) 0 t
  have h2 := cost_segIR apC (trSegS st) 0 t
  have h3 := cost_segIR apC (.cp 0 597) 0 t
  have h4 := hst.cost
  rw [segCost_pSegS] at h1; rw [segCost_trSegS] at h2; rw [show segCost (.cp 0 597) = 21506 from rfl] at h3
  simp only [outIRS, cost, emitIR, setR, blkSteps, List.length_cons, List.length_nil,
    cost_tcpIR _ _ t (show 4 < 2 ^ 64 by norm_num), cost_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num),
    cost_tcpIR _ _ t (show 597 < 2 ^ 64 by norm_num), cost_leafStmtIR, cost_copyIR, nCp]
  norm_num
  (clear * - st t h1 h2 h3 h4; omega)

theorem outs_outIRS (st : XStage) (hst : OutOK st) (m t : ℕ) : outs (outIRS st m) t ≤ 164753 := by
  have h1 := outs_segIR apC (pSegS st) 0 t
  have h2 := outs_segIR apC (trSegS st) 0 t
  have h3 := outs_segIR apC (.cp 0 597) 0 t
  have h4 := hst.outs
  rw [segOuts_pSegS] at h1; rw [segOuts_trSegS] at h2; rw [show segOuts (.cp 0 597) = 597 from rfl] at h3
  simp only [outIRS, outs, emitIR, setR, outs_tcpIR _ _ t (show 4 < 2 ^ 64 by norm_num),
    outs_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), outs_tcpIR _ _ t (show 597 < 2 ^ 64 by norm_num),
    outs_leafStmtIR, copyIR, copyBody, Nat.zero_add, Nat.add_zero]
  simp at h1 h2 h3 ⊢
  (clear * - st t h1 h2 h3 h4; omega)

theorem sizeIR_outIRS (st : XStage) (hst : OutOK st) (m : ℕ) : sizeIR (outIRS st m) ≤ 2 ^ 18 - 2 ^ 10 := by
  have h4 := hst.size
  simp only [outIRS, sizeIR, sizeIR_segIR, pSegS, trSegS, segSize, segPSsS, segTSsS, sizeIR_leafStmtIR]
  simp [emitIR, setR, tcpIR, tcpBody, copyIR, copyBody, cpAddrPs, sizeIR, blkSteps]
  (clear * - st h4; omega)


/-! ## The semantics -/

/-- π's packed words on the tape (`tape_pw`). -/
theorem tape_pwS (st : XStage) (hst : OutOK st) (c : Digest) (π : Proof) (L : Log) (hs : π.size = st.pz) {j : ℕ}
    (hj : j < 616) : (extractorInput c π L).toArray.getD (5 + j) 0 = pw π j := by
  have := hst.pzLo
  rw [getD_toArray, tape_getD_proof c π L (by rw [hs]; (clear * - j st π hj this; omega)), pw, List.getD_eq_getElem]

theorem wsAt_tapeS (st : XStage) (hst : OutOK st) (c : Digest) (π : Proof) (L : Log) (hs : π.size = st.pz) {a n : ℕ}
    (h : a + n ≤ 616) :
    (List.range n).map (fun j => (extractorInput c π L).toArray.getD (5 + a + j) 0) = wsAt (pw π) a n :=
  List.map_congr_left fun j hj => by
    rw [Nat.add_assoc, tape_pwS st hst c π L hs (by simp at hj; (clear * - a j st π n h hj; omega))]

/-- **The node output's run** (`outIR_sem`): from a state whose heap holds the decoded message `w` at `mB`, on the
tape of an `S` proof, `outIRS st mB` appends `outWordsS st π w`. -/
theorem outIRS_run (st : XStage) (hst : OutOK st) (c : Digest) (π : Proof) (L : Log) (hs : π.size = st.pz)
    (s : St) (hM : Inv s.M) {mB : ℕ} (hmB : regs ≤ mB) (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size)
    (w : ℕ → Word) (hw : ∀ i < 2 ^ 19, Lvm.X.rd s.M (mB + i) = w i) :
    (semXIR (extractorInput c π L).toArray (outIRS st mB) s).o.toList = s.o.toList ++ outWordsS st π w := by
  set I := (extractorInput c π L).toArray with hI
  have hs0 := hM.1
  simp only [regs] at hs0 hmB
  -- 1. the tag
  have hwf1 := wf_emitIR (toWord 1)
  obtain ⟨o1, f1⟩ := emitIR_sem I s hM (toWord 1)
  have hM1 := inv_sem I hwf1 hM
  have z1 := size_sem I (emitIR (toWord 1)) s
  rw [outIRS, semXIR_seq]
  generalize semXIR I (emitIR (toWord 1)) s = s1 at o1 f1 hM1 z1
  -- 2. `c_L`
  obtain ⟨o2, f2, hM2, z2⟩ := tcpIR_sem I s1 hM1 (a := 11) (n := 4) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (tcpIR 11 4) s1 = s2 at o2 f2 hM2 z2
  -- 3. `leafStmt h n`
  obtain ⟨o3, f3⟩ := leafStmtIR_sem I s2 hM2 (hW := 20) (nW := 19) (hdD π 15) (pw π 14).toNat
    (fun i hi => by
      rw [hdD, packBytes_digW (length_wsAt _ _ _), wsAt, List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map, List.getElem_range, show 20 + i = 5 + (15 + i) by (clear * - i st π s mB s1 s2; omega),
        tape_pwS st hst c π L hs (by (clear * - i st π s mB s1 s2 hi; omega))])
    (by rw [show 19 = 5 + 14 from rfl, tape_pwS st hst c π L hs (by (clear * - st π s mB s1 s2; omega)), toWord_toNat'])
    (pw π 14).isLt (by norm_num) (by norm_num)
  have hM3 := inv_sem I (wf_leafStmtIR 20 19) hM2
  have z3 := size_sem I (leafStmtIR 20 19) s2
  rw [semXIR_seq]
  generalize semXIR I (leafStmtIR 20 19) s2 = s3 at o3 f3 hM3 z3
  -- 4. `|π'|`
  obtain ⟨o4, f4⟩ := emitIR_sem I s3 hM3 (toWord st.pz)
  have hM4 := inv_sem I (wf_emitIR (toWord st.pz)) hM3
  have z4 := size_sem I (emitIR (toWord st.pz)) s3
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord st.pz)) s3 = s4 at o4 f4 hM4 z4
  -- the heap so far
  have h4 : ∀ y, regs ≤ y → Lvm.X.rd s4.M y = Lvm.X.rd s.M y := fun y hy => by
    simp only [regs] at hy
    rw [f4 y (by simp only [eW]; (clear * - y st π s mB s1 s2 s3 s4 hy; omega)), f3 y (by simp only [regs]; (clear * - hy; omega)),
      f2 y (by simp only [eW]; (clear * - y st π s mB s1 s2 s3 s4 hy; omega)) (by simp only [eP]; (clear * - y st π s mB s1 s2 s3 s4 hy; omega)) (by simp only [eN]; (clear * - y st π s mB s1 s2 s3 s4 hy; omega))
        (by simp only [eC]; (clear * - y st π s mB s1 s2 s3 s4 hy; omega)) (by simp only [cTmp]; (clear * - y st π s mB s1 s2 s3 s4 hy; omega)), f1 y (by simp only [eW]; (clear * - y st π s mB s1 s2 s3 s4 hy; omega))]
  have zz4 : s4.M.size = s.M.size := by rw [z4, z3, z2, z1]
  -- 5. the stream copy
  obtain ⟨c1, c2, hM5, z5, o5⟩ := copyIR_sem I s4 hM4 (mB := mB) (by simp only [regs]; (clear * - hmB; omega)) hmB2
    (by rw [zz4]; exact hsz)
  rw [semXIR_seq]
  generalize semXIR I (copyIR mB) s4 = s5 at c1 c2 hM5 z5 o5
  -- the stream's lanes and the signature column in the heap
  have hlane : ∀ u < nCp, Lvm.X.rd s5.M (sgB + u) = laneOf w u := fun u hu => by
    rw [c1 u hu, h4 _ (by simp only [regs]; (clear * - mB u st π s hmB s1 s2 s3 s4 s5; omega)), hw _ (crecIdx_lt hu)]; rfl
  have hsig : ∀ j < 597, Lvm.X.rd s5.M (sigB mB + j) = sigCol w j := fun j hj => by
    rw [c2 _ (by simp only [regs, sigB]; (clear * - mB j st π s hmB s1 s2 s3 s4 s5 hj; omega)) (.inl (by simp only [sigB]; (clear * - mB j st π s hmB2 s1 s2 s3 s4 s5 hj; omega))), sigB,
      Nat.add_assoc, h4 _ (by simp only [regs]; (clear * - mB j st π s hmB s1 s2 s3 s4 s5 hj; omega)), hw _ (by (clear * - j st π s mB s1 s2 s3 s4 s5 hj; omega))]; rfl
  -- 6–8. the proof's and the trace's segments
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := setR_sem I s5 hM5 sgB
  rw [semXIR_seq]
  generalize semXIR I (setR sgB) s5 = s6 at r1 r2 r3 r4 r5 r6 r7
  have hc6 : Ctx s5.M sgB false s6 := ⟨r1, r2, r3, r4, by rw [r5]; simp⟩
  have hA := hA_apC (R := sgB) (by simp only [regs, sgB]; norm_num) (by simp only [sgB]; norm_num)
  obtain ⟨g1, g2, g3⟩ := seg_step I hA (pSegS st) hst.segs.2.2.1 hst.segs.2.2.2 s6 hc6 r6
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 (pSegS st)) s6 = s7 at g1 g2 g3
  obtain ⟨k1, k2, k3⟩ := seg_step I hA (trSegS st) hst.segs.1 hst.segs.2.1 s7 g2 g3
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 (trSegS st)) s7 = s8 at k1 k2 k3
  -- the source is the stream below `T`
  have hT := hst.lanes
  have hsrc : ∀ v < 6 + ((blocksS st).map Blk.lanes).sum, src s5.M apC sgB v = laneOf w v := fun v hv => by
    rw [src_apC _ (by simp only [sgB, nCp] at hT ⊢; (clear * - v st π s mB s1 s2 s3 s4 s5 s6 hT hv; omega)), hlane v (by (clear * - v st π s mB s1 s2 s3 s4 s5 s6 hT hv; omega))]
  have eP : segOut (src s5.M apC sgB) false 0 (pSegS st) = pWordsS st (laneOf w) := by
    rw [segOut_pSegS st hst.blkOk, ← packBytes_reassembleS st hst.planOk hst.blkOk, readTraceLS_congr st hsrc,
      packBytes_reassembleS st hst.planOk hst.blkOk]
  have eT : segOut (src s5.M apC sgB) false 0 (trSegS st) = trWordsS st (laneOf w) := by
    rw [segOut_trSegS, ← logWords_readTraceLS st hst.blkOk, readTraceLS_congr st hsrc,
      logWords_readTraceLS st hst.blkOk]
  -- 9–10. the signature column
  have hM8 := k2.inv
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := setR_sem I s8 hM8 (sigB mB)
  rw [semXIR_seq]
  generalize semXIR I (setR (sigB mB)) s8 = s9 at u1 u2 u3 u4 u5 u6 u7
  have hc9 : Ctx s5.M (sigB mB) false s9 :=
    ⟨u1, by rw [u2, k2.size], fun y hy => by rw [u3 y hy, k2.heap y hy], u4, by rw [u5]; simp⟩
  have hA' := hA_apC (R := sigB mB) (by simp only [regs, sigB]; (clear * - mB st π s hmB s1 s2 s3 s4 s5 s6 s8 s9; omega)) (by simp only [sigB, sgB] at hmB2 ⊢; (clear * - mB st π s hmB hmB2 s1 s2 s3 s4 s5 s6 s8 s9; omega))
  obtain ⟨v1, v2, v3⟩ := seg_step I hA' (.cp 0 597) (by decide) (by decide) s9 hc9 u6
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 (.cp 0 597)) s9 = s10 at v1 v2 v3
  have eS : segOut (src s5.M apC (sigB mB)) false 0 (.cp 0 597) = wsAt (sigCol w) 0 597 := by
    simp only [segOut, wsAt, Nat.zero_add]
    exact List.map_congr_left fun j hj => by
      rw [src_apC _ (by simp only [sigB, sgB] at hmB2 ⊢; simp at hj; (clear * - mB j st π s hmB hmB2 s1 s2 s3 s4 s5 s6 s8 s9 hj; omega)), hsig j (by simpa using hj)]
  -- 11–15. the right child
  have hM10 := v2.inv
  obtain ⟨p1, -⟩ := emitIR_sem I s10 hM10 (toWord 48)
  have hM11 := inv_sem I (wf_emitIR (toWord 48)) hM10
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 48)) s10 = s11 at p1 hM11
  obtain ⟨p2, -⟩ := emitIR_sem I s11 hM11 (toWord 0)
  have hM12 := inv_sem I (wf_emitIR (toWord 0)) hM11
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 0)) s11 = s12 at p2 hM12
  obtain ⟨p3, -, hM13, -⟩ := tcpIR_sem I s12 hM12 (a := 15) (n := 5) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (tcpIR 15 5) s12 = s13 at p3 hM13
  obtain ⟨p4, -⟩ := emitIR_sem I s13 hM13 (toWord 0)
  have hM14 := inv_sem I (wf_emitIR (toWord 0)) hM13
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 0)) s13 = s14 at p4 hM14
  obtain ⟨p5, -, -, -⟩ := tcpIR_sem I s14 hM14 (a := 24) (n := 597) (by norm_num)
  -- the words
  rw [p5, p4, p3, p2, p1, v1, u7, k1, g1, r7, o5, o4, o3, o2, o1, eP, eT, eS]
  have t1 := wsAt_tapeS st hst c π L hs (a := 6) (n := 4) (by norm_num)
  have t2 := wsAt_tapeS st hst c π L hs (a := 10) (n := 5) (by norm_num)
  have t3 := wsAt_tapeS st hst c π L hs (a := 19) (n := 597) (by norm_num)
  simp only [show (5 + 6 : ℕ) = 11 from rfl, show (5 + 10 : ℕ) = 15 from rfl,
    show (5 + 19 : ℕ) = 24 from rfl] at t1 t2 t3
  rw [t1, t2, t3, outWordsS, show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
  have e19 : wsAt (pw π) 19 597 = wsAt (fun j => pw π (19 + j)) 0 597 := by
    simp only [wsAt, Nat.zero_add]
  rw [e19]
  simp [wsAt, List.append_assoc]


/-- **The node output's semantics** (`outIR_sem`): the output is the node witness's words. -/
theorem outIRS_sem (st : XStage) (hst : OutOK st) (c : Digest) (π : Proof) (L : Log) (hs : π.size = st.pz)
    (s : St) (hM : Inv s.M) {mB : ℕ} (hmB : regs ≤ mB) (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size)
    (w : ℕ → Word) (hw : ∀ i < 2 ^ 19, Lvm.X.rd s.M (mB + i) = w i) :
    ∃ ws, (semXIR (extractorInput c π L).toArray (outIRS st mB) s).o.toList = s.o.toList ++ ws ∧
      decodeWit ws = some (XwitS st π w) := by
  exact ⟨_, outIRS_run st hst c π L hs s hM hmB hmB2 hsz w hw, decodeWit_outWordsS st hst π w⟩

end Lvm.XS
