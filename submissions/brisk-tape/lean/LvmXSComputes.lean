-- New for lvm2 E2F (E2F-L, 2026-11-13): the extractor program's facts at a stage (owner: E2F-L's helper H2). Ports of
-- `LvmMPXTop`'s WF/NoLoopT/safe/outs/cost/size and `LvmMPXComputes` with the stage's offsets. The statements are frozen
-- (`-- E2F-L frozen`); `ProgOK` holds the stage's static facts (decided once at `stF20`, `progFacts_stF20`).
import LvmXSTop
import LvmXSOut

/-!
# The extractor program at a stage: `Computes`

* **`ProgOK st`**: the stage's static facts the program needs (layout, chain table, offsets; `progOK_stF20`);
* **`computesXS`**: `Computes (extXS st) (EXS st A) fuel`; `extXS_size`; **`EXS_W`**.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-- A chain message: lane-aligned, inside a proof of `pz` bytes, its query within `queryCap`. -/
def msgOkP (pz : ℕ) (m : ℕ × ℕ) : Bool :=
  m.1 % 8 == 0 && m.2 % 8 == 0 && m.1 + m.2 ≤ pz && 32 + m.2 ≤ queryCap

/-- A chain message at a stage (`msgOkP` at `|π|`). -/
def msgOkS (st : XStage) (m : ℕ × ℕ) : Bool := msgOkP st.pz m

/-- **The stage's static facts for the program** (decided per stage). `occ0 ≤ 64`: level 0's rows are read at
stride `(64 − occ0) + occ0 = 64`, as the decoder reads them. -/
structure ProgOK (st : XStage) : Prop where
  /-- The node output's facts. -/
  out : OutOK st
  /-- `C_main`'s root rows fit a row of 64 words. -/
  occ0 : st.occ0 ≤ 64
  /-- `|π|` bound. -/
  pz_lt : st.pz < 2 ^ 32
  /-- The chain's targets fit the scan (`2^11`). -/
  nCh_lt : nChainS st < 2 ^ 11
  /-- The chain's messages exist. -/
  nCh_le : nChainS st ≤ (fsMsgsS st).length
  /-- Every chain message through position `nChainS st` is aligned, inside π, within `queryCap`. -/
  msgs : ((fsMsgsS st).take (nChainS st)).all (msgOkS st) = true
  /-- Every message's query is within `queryCap`. -/
  qcap : (fsMsgsS st).all (fun m => 32 + m.2 ≤ queryCap) = true
  /-- The 14 fold challenges are chain targets. -/
  fold : ∀ k < 14, foldPosKS st k < nChainS st
  /-- The caps inside π. -/
  cap0 : capOffS st 0 / 8 + 4 * 2 ^ 8 ≤ st.pz / 8
  cap1 : capOffS st 1 / 8 + 4 * 2 ^ 7 ≤ st.pz / 8
  cap2 : capOffS st 2 / 8 + 4 * 2 ^ 7 ≤ st.pz / 8
  /-- The residual inside π. -/
  res : resOffS st / 8 + 3 * 2 ^ 9 ≤ st.pz / 8
  /-- The tape words of the caps, the residual and the log (for the node's address bounds). -/
  capW0 : capWS st 0 + 4 * 2 ^ 8 < 2 ^ 62
  capW1 : capWS st 1 + 4 * 2 ^ 7 < 2 ^ 62
  capW2 : capWS st 2 + 4 * 2 ^ 7 < 2 ^ 62
  resW : resWS st + 3 * 2 ^ 9 < 2 ^ 63
  pL : pLS st ≤ 2 ^ 60
  /-- The header's words are inside π. -/
  pz15 : 15 ≤ st.pz / 8

/-- S2GF's static facts (one `decide +kernel`; `|π|` enters as its value `checks_P20F` proved, so the kernel does
not evaluate the schedule's tally again). -/
theorem progFacts_stF20 : stF20.occ0 ≤ 64 ∧ 306992 < 2 ^ 32 ∧ nChainS stF20 < 2 ^ 11 ∧
    nChainS stF20 ≤ (fsMsgsS stF20).length ∧
    ((fsMsgsS stF20).take (nChainS stF20)).all (msgOkP 306992) = true ∧
    (fsMsgsS stF20).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    (∀ k < 14, foldPosKS stF20 k < nChainS stF20) ∧
    capOffS stF20 0 / 8 + 4 * 2 ^ 8 ≤ 306992 / 8 ∧ capOffS stF20 1 / 8 + 4 * 2 ^ 7 ≤ 306992 / 8 ∧
    capOffS stF20 2 / 8 + 4 * 2 ^ 7 ≤ 306992 / 8 ∧ resOffS stF20 / 8 + 3 * 2 ^ 9 ≤ 306992 / 8 ∧
    capWS stF20 0 + 4 * 2 ^ 8 < 2 ^ 62 ∧ capWS stF20 1 + 4 * 2 ^ 7 < 2 ^ 62 ∧ capWS stF20 2 + 4 * 2 ^ 7 < 2 ^ 62 ∧
    resWS stF20 + 3 * 2 ^ 9 < 2 ^ 63 ∧ posL 306992 ≤ 2 ^ 60 ∧ 15 ≤ 306992 / 8 := by
  decide +kernel

/-- S2GF's `|π|`. -/
theorem stF20_pz : stF20.pz = 306992 := checks_P20F.1.1

/-- S2GF's program facts. -/
theorem progOK_stF20 : ProgOK stF20 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := progFacts_stF20
  have e : msgOkS stF20 = msgOkP 306992 := by funext m; rw [msgOkS, stF20_pz]
  exact ⟨outOK_stF20, h1, stF20_pz ▸ h2, h3, h4, e ▸ h5, h6, h7, stF20_pz ▸ h8, stF20_pz ▸ h9, stF20_pz ▸ h10,
    stF20_pz ▸ h11, h12, h13, h14, h15, by show posL stF20.pz ≤ 2 ^ 60; rw [stF20_pz]; exact h16, stF20_pz ▸ h17⟩

/-! ## The chain's table -/

theorem tabEntS_length (st : XStage) (p : ℕ) : (tabEntS st p).length = 4 := by unfold tabEntS; split <;> rfl

theorem chTabS_length (st : XStage) : (chTabS st).length = 4 * (nChainS st + 1) := by
  have h : ∀ n : ℕ, ((List.range n).flatMap (tabEntS st)).length = 4 * n := fun n => by
    rw [List.length_flatMap]
    simp only [tabEntS_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    ring
  rw [chTabS]
  exact h _

/-! ## S2GU's level-0 decoder and stream block (D-WIN (B)) -/

theorem wf_dec0S (st : XStage) : WF (dec0S st) := by
  unfold dec0S
  split
  · refine ⟨?_, ?_, wf_decMP0IR .., wf_decMP0IR ..⟩
    · simp +decide [readAt, WF, Prim.dst, rA, eW]
    · simp +decide [WF, Prim.dst, eA, eW]
  · exact wf_decMP0IR ..

theorem wf_streamS (st : XStage) : WF (streamS st) := by
  unfold streamS
  split
  · refine ⟨?_, ?_, wf_mcpIR .., wf_mcpIR ..⟩
    · simp +decide [readAt, WF, Prim.dst, rA, eW]
    · simp +decide [WF, Prim.dst, eA, eW]
  · exact wf_streamM

theorem noLoopT_dec0S (st : XStage) : NoLoopT (dec0S st) := by
  unfold dec0S
  split
  · exact ⟨by simp [readAt, NoLoopT], trivial, noLoopT_decMP0IR .., noLoopT_decMP0IR ..⟩
  · exact noLoopT_decMP0IR ..

theorem noLoopT_streamS (st : XStage) : NoLoopT (streamS st) := by
  unfold streamS
  split
  · exact ⟨by simp [readAt, NoLoopT], trivial, noLoopT_mcpIR .., noLoopT_mcpIR ..⟩
  · exact noLoopT_streamM

theorem outs_dec0S (st : XStage) (t : ℕ) : outs (dec0S st) t = 0 := by
  unfold dec0S
  split
  · simp only [dec0U, decMP0IRW, readAt, outs, outs_decMP0IR]; simp
  · exact outs_decMP0IR ..

theorem outs_streamS (st : XStage) (t : ℕ) : outs (streamS st) t = 0 := by
  unfold streamS
  split
  · simp only [streamU, readAt, outs, outs_mcpIR]; simp
  · simp only [streamM, readAt, outs, outs_mcpIR]; simp

/-- Both level-0 decoders cost `c0Model 19 19 17 8` (the window's first lane does not enter the cost). -/
theorem cost_dec0S (st : XStage) (t : ℕ) : cost (dec0S st) t ≤ 25267547498264 + 16 := by
  have h32 := cost_decMP0IR 19 19 17 32 8 dB0M wB0M aB0M fB0M t (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h40 := cost_decMP0IRW dB0M wB0M aB0M fB0M t
  rw [c0Model] at h32
  norm_num at h32
  unfold dec0S
  split
  · simp only [dec0U, readAt, cost, blkSteps, List.length_cons, List.length_nil, h32, h40, Nat.max_def]
    split_ifs <;> omega
  · omega

theorem cost_streamS (st : XStage) (t : ℕ) : cost (streamS st) t ≤ 6815800 := by
  unfold streamS
  split
  · simp only [streamU, readAt, cost, blkSteps, List.length_cons, List.length_nil,
      cost_mcpIR _ _ _ _ t (show 2 ^ 19 < 2 ^ 64 by norm_num)]
    norm_num
  · exact cost_streamM t

/-! ## Well formed, no tape loop -/

theorem wf_acpS (st : XStage) : WF (acpS st) := ⟨wf_acp3IR _ _ _, wf_acp3IR _ _ _, wf_acp3IR _ _ _⟩

theorem wf_okL0S (st : XStage) (ho : OutOK st) : WF (okL0S st) :=
  ⟨by simp +decide [WF], show 4 ≤ eW by decide, ⟨wf_streamS st, wf_outIRS st ho _⟩, by simp [WF]⟩

theorem wf_okL1S (st : XStage) (ho : OutOK st) : WF (okL1S st) :=
  ⟨by simp +decide [WF], show 4 ≤ eW by decide, ⟨wf_dec0S st, wf_okL0S st ho⟩, by simp [WF]⟩

theorem wf_okL2S (st : XStage) (ho : OutOK st) : WF (okL2S st) :=
  ⟨by simp +decide [WF], show 4 ≤ eW by decide, ⟨wf_dec1MPIR .., wf_okL1S st ho⟩, by simp [WF]⟩

theorem wf_nodeS (st : XStage) (ho : OutOK st) : WF (nodeS st) :=
  ⟨wf_idxIR4 _ _, wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide)),
    wf_readGIR .., wf_readGIR .., wf_readGIR .., wf_acpS st, wf_thcpIR _ _ _, wf_dec1MPIR .., wf_okL2S st ho⟩

theorem wf_decXS (st : XStage) (ho : OutOK st) : WF (decXS st) := by
  refine ⟨?_, wf_nodeS st ho, wf_leafIR⟩
  simp +decide [readAt, WF, rA, rBb]

theorem noLoopT_acpS (st : XStage) : NoLoopT (acpS st) :=
  ⟨noLoopT_acp3IR .., noLoopT_acp3IR .., noLoopT_acp3IR ..⟩

theorem noLoopT_okL0S (st : XStage) : NoLoopT (okL0S st) :=
  ⟨trivial, trivial, ⟨noLoopT_streamS st, noLoopT_outIRS st _⟩, trivial⟩
theorem noLoopT_okL1S (st : XStage) : NoLoopT (okL1S st) :=
  ⟨trivial, trivial, ⟨noLoopT_dec0S st, noLoopT_okL0S st⟩, trivial⟩
theorem noLoopT_okL2S (st : XStage) : NoLoopT (okL2S st) :=
  ⟨trivial, trivial, ⟨noLoopT_dec1MPIR .., noLoopT_okL1S st⟩, trivial⟩

/-- **The SNARK branch's loop bounds** at a stage, on every domain tape of an `S` proof. -/
theorem safe_decXS (st : XStage) (c : Digest) (π : Proof) (L : Log) (hs : π.size = st.pz)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length (decXS st) := by
  refine .seq (safe_of_noLoopT (by simp [readAt, NoLoopT])) (.ite ?_ (safe_of_noLoopT
    ⟨noLoopT_emitIR _, noLoopT_tcpIR _ _⟩))
  refine .seq (safe_idxIR4 _ _ (by have := hs_posL hs; rw [pLS, ← this]; have := ht; have := tape_length c π L; omega)
    (tape_count_le4 c π L (hs_posL hs) ht))
    (.seq ?_ (.seq (safe_of_noLoopT (noLoopT_readGIR ..)) (.seq (safe_of_noLoopT (noLoopT_readGIR ..))
      (.seq (safe_of_noLoopT (noLoopT_readGIR ..)) (.seq (safe_of_noLoopT (noLoopT_acpS st))
        (.seq (safe_of_noLoopT (noLoopT_thcpIR ..)) (.seq (safe_of_noLoopT (noLoopT_dec1MPIR ..))
          (safe_of_noLoopT (noLoopT_okL2S st)))))))))
  exact safe_chainIR c π L (hs_posL hs) hq ht _ _ noLoopT_sdL wf_sdL
    (nw_sdL _ (by decide) (by decide) (by decide))

/-! ## Output -/

theorem outs_acpS (st : XStage) (t : ℕ) : outs (acpS st) t = 0 := by
  simp only [acpS, outs, outs_acp3IR]

theorem outs_decXS (st : XStage) (ho : OutOK st) (t : ℕ) : outs (decXS st) t ≤ outCap := by
  have h := outs_outIRS st ho mBM t
  have h0 : outs (dec0S st) t = 0 := outs_dec0S st t
  have hs : outs (streamS st) t = 0 := outs_streamS st t
  have h1 : outs (decMP1IR dB1M wB1M aB1M fB1M fB0M) t = 0 := outs_dec1MPIR ..
  have h2 : outs (decMP2IR dB2M wB2M aB2M fB2M fB1M) t = 0 := outs_dec1MPIR ..
  simp only [decXS, nodeS, okL2S, okL1S, okL0S, hs, leafIR, readAt, outs, outs_idxIR4, outs_readGIR,
    read0S, read1M, read2M, outs_acpS, h0, h1, h2, emitIR, outs_mcpIR, outs_thcpIRM,
    outs_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), chainLS,
    outs_chainIR (pLS st) (nChainS st) t (chTabS st) (show outs sdL t = 0 by simp [sdL, outs])]
  simp at *
  rw [outCap]; omega

/-! ## Cost -/

theorem cost_acpS (st : XStage) (t : ℕ) : cost (acpS st) t = 789 := by
  simp only [acpS, cost, cost_acp3IR]

theorem cost_read0S (st : XStage) (hp : ProgOK st) (t : ℕ) : cost (read0S st) t ≤ 41955622926 := by
  have h := hp.occ0
  rw [read0S, cost_readGIR _ _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by omega) (by omega)]
  omega

/-- After level 0: the stream block and the node output. -/
theorem cost_okL0S (st : XStage) (ho : OutOK st) (t : ℕ) : cost (okL0S st) t ≤ 22700000 := by
  have hO := cost_outIRS st ho mBM t
  have hS := cost_streamS st t
  simp only [okL0S, cost, blkSteps, List.length_cons, List.length_nil, Nat.max_def]
  split_ifs <;> omega

/-- **The SNARK branch's cost** at a stage. -/
theorem cost_decXS (st : XStage) (hp : ProgOK st) (t : ℕ) :
    cost (decXS st) t ≤ 2 ^ 45 + t / 5 * 11895 + t * 168 := by
  have hC := cost_chainIR (pLS st) (nChainS st) t (chTabS st) sdL
  rw [chTabS_length, cost_sdL] at hC
  have hN := hp.nCh_lt
  have hD2 := cost_decMP2IR dB2M wB2M aB2M fB2M fB1M t
  have hD1 := cost_decMP1IR dB1M wB1M aB1M fB1M fB0M t
  have hD0 := cost_dec0S st t
  have h0 := cost_okL0S st hp.out t
  have hR0 := cost_read0S st hp t
  have hR1 := cost_read1M memM (pLS st) (capWS st 1) wB1M t
  have hR2 := cost_read2M memM (pLS st) (capWS st 2) wB2M t
  simp only [decXS, nodeS, okL2S, okL1S, leafIR, readAt, cost, blkSteps, List.length_cons,
    List.length_nil, cost_idxIR4, chainLS, hC, hR1, hR2, cost_acpS, cost_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num),
    emitIR, cost_thcpIR _ _ _ t (show 3 * 2 ^ 9 < 2 ^ 64 by norm_num), Nat.max_def]
  split_ifs <;> omega

/-! ## Size -/

private theorem szBlkS (ps : List Prim) : sizeIR (.blk ps) = blkSteps ps.length := by rw [sizeIR]
private theorem szLoadS (d a : ℕ) : sizeIR (.load d a) = 1 := by rw [sizeIR]
private theorem szInputS (d a : ℕ) : sizeIR (.input d a) = 1 := by rw [sizeIR]
private theorem szSeqS (p q : XIR) : sizeIR (.seq p q) = sizeIR p + sizeIR q + 1 := by rw [sizeIR]
private theorem szIteS (c : ℕ) (p q : XIR) : sizeIR (.ite c p q) = sizeIR p + sizeIR q + 1 := by
  rw [sizeIR]

theorem sizeIR_idxS (pL : ℕ) : sizeIR (idxIR4 memM pL) = 294 := by
  simp only [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, sizeIR, blkSteps,
    List.length_cons, List.length_nil, List.length_append]
  norm_num

theorem sizeIR_streamM : sizeIR streamM ≤ 2 ^ 10 := by decide +kernel

theorem sizeIR_streamS (st : XStage) : sizeIR (streamS st) ≤ 2 ^ 10 := by
  unfold streamS
  split
  · decide +kernel
  · exact sizeIR_streamM

theorem sizeIR_dec0S (st : XStage) : sizeIR (dec0S st) ≤ 2 ^ 16 + 2 ^ 10 := by
  unfold dec0S
  split
  · decide +kernel
  · exact le_trans sizeIR_dec0M (by norm_num)

theorem sizeIR_decXS (st : XStage) (hp : ProgOK st) : sizeIR (decXS st) ≤ 2 ^ 19 := by
  have h2 := sizeIR_dec2M
  have h1 := sizeIR_dec1M
  have h0 := sizeIR_dec0S st
  have hO := sizeIR_outIRS st hp.out mBM
  have hS := sizeIR_streamS st
  have hN := hp.nCh_lt
  have hA := sizeIR_acp3IR (ansB + 4 * foldPosS st 0 0) aB0M 6
  have hB := sizeIR_acp3IR (ansB + 4 * foldPosS st 1 0) aB1M 4
  have hC := sizeIR_acp3IR (ansB + 4 * foldPosS st 2 0) aB2M 4
  simp only [decXS, nodeS, okL2S, okL1S, okL0S, leafIR, readAt, emitIR, acpS, szBlkS, szLoadS, szInputS,
    szSeqS, szIteS, blkSteps, List.length_cons, List.length_nil, sizeIR_idxS, chainLS, sizeIR_chainIR,
    chTabS_length, read0S, read1M, read2M, sizeIR_readGIR, hA, hB, hC]
  simp only [tcpIR, tcpBody, thcpIR, thcpBody, sdL, sizeIR, blkSteps, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  omega

/-! ## `Computes` -/

/-- **The SNARK branch meets `DecOkM`** at a stage. -/
theorem decOk_decXS (st : XStage) (hp : ProgOK st) : DecOkM st.pz (decXS st) where
  pz_lt := by have := hp.pz_lt; omega
  wf := wf_decXS st hp.out
  safe := fun c π L hs hq ht => safe_decXS st c π L hs hq ht
  cost := fun t => by
    have := cost_decXS st hp t
    simp only [decBudgetM, fuelBase, fuelPerWord]
    omega
  outs := outs_decXS st hp.out
  size := sizeIR_decXS st hp

/-! ## The `W` kind -/

theorem run_W_tapeS (st : XStage) (hp : ProgOK st) (hpz : st.pz ≠ 0) (inp : List Word) (a : ℕ)
    (ha : a < 2 ^ 64) (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hk : a ≠ 0 → ¬ (inp.toArray.getD 5 0 &&& 0xFF = kindS)) :
    (extXS st).run inp (fuel inp.length) =
      some ((List.range ((a + 7) / 8)).map fun j => inp.toArray.getD (5 + j) 0) := by
  have hd := decOk_decXS st hp
  have hpz2 := hd.pz_lt
  have hwf := wf_extIRWith (pz := st.pz) hd.wf
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0 : Inv (initSt (memM + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memM + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Inv (semXIR I (parseIR st.pz) s0).M := inv_sem I hwf.1 h0
  have hz0 : a = 0 → Lvm.X.rd (semXIR I (parseIR st.pz) s0).M rIsSz = 0 := by
    intro h
    rw [parse_regs _ I s0 h0, h4, h, if_neg]
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_toWord (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpz2] at this
    omega
  have hk' : a ≠ 0 → Lvm.X.rd (semXIR I (parseIR st.pz) s0).M rIsK = 0 := fun h => by
    rw [parse_isK _ I s0 h0, if_neg (hk h)]
  have hpo : (semXIR I (parseIR st.pz) s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 ha]
  generalize hs1 : semXIR I (parseIR st.pz) s0 = s1 at h1 hz0 hk' hpo
  have hB : BoundsOk I inp.length (extIRWith st.pz (decXS st)) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk1 : Lvm.X.rd s1.M rIsK = 0
    · rw [if_pos hk1]
      exact boundsOk_of_safe (safe_wIR ha h4 (by omega)) hwf.2.2 _ h1
    · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
      rw [if_neg hk1, boundsOk_ite, if_pos (hz0 ha0)]; trivial
  have hrun := run_toProg (P := extIRWith st.pz (decXS st)) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_coversM hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  by_cases hk1 : Lvm.X.rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith st.pz (decXS st)) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk1]
    rw [congrArg (fun s' : St => s'.o.toList) e, wIR_sem I _ h1 (by omega), hpo, hw]
    rfl
  · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
    have e : semXIR I (extIRWith st.pz (decXS st)) s0 = semXIR I (.blk []) s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos (hz0 ha0)]
    rw [congrArg (fun s' : St => s'.o.toList) e, ha0]
    simp [semXIR, hpo]

/-- **`Computes (extXS st) (EXS st A) fuel`** with the declared fuel. -/
theorem computesXS (st : XStage) (hp : ProgOK st) (ho : OutOK st) (A : Digest → Digest → Signed → Bool) :
    Computes (extXS st) (EXS st A) fuel :=
  fun c π L h1 h2 h3 => by
    obtain ⟨o, ho', hl, hd⟩ := computesWithM (decOk_decXS st hp) c π L h1 h2 h3
    exact ⟨o, ho', hl, hd.trans (if_pos ⟨h1, h2, h3⟩).symm⟩

/-- The program within `progCap`. -/
theorem extXS_size (st : XStage) (hp : ProgOK st) (ho : OutOK st) : (extXS st).body.size ≤ progCap :=
  size_extWithM (decOk_decXS st hp).size

/-- Witness-sending proofs decode. -/
theorem EXS_W (st : XStage) (hp : ProgOK st) (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof)
    (L : Log) (hW : π.data[0]? ≠ some 0x53) : EXS st A c π L = WitnessSending.decode π := by
  by_cases hD : InDomE c π L
  · rw [EXS, if_pos hD, EdXS]
    have hπ : π.size < 2 ^ 64 := by have := hD.1; rw [outCap] at this; omega
    have hpz : st.pz ≠ 0 := by have := hp.cap0; omega
    have hrun := run_W_tapeS st hp hpz (extractorInput c π L) π.size hπ (by rw [getD_toArray, tape_getD4])
      (tape_length c π L) (fun hne he => by
        obtain ⟨b, hb⟩ : ∃ b, π.data[0]? = some b := by
          rcases h : π.data[0]? with _ | b
          · rw [Array.getElem?_eq_none_iff] at h; exact (hne (Nat.le_zero.mp h)).elim
          · exact ⟨b, rfl⟩
        have h1 := tape_byte0 c π L hb
        have h2 := congrArg BitVec.toNat he
        rw [lowByte, getD_toArray, h1] at h2
        exact hW (by rw [hb]; congr 1; exact UInt8.toNat_inj.mp h2))
    rw [Eden, ← den_of_run (by simp only [regs, memM]; norm_num) (wf_extIRWith (decOk_decXS st hp).wf) hrun,
      WitnessSending.decode]
    congr 1
    refine List.ext_getElem (by
      simp only [List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · rw [EXS, if_neg hD, EoutXS, if_neg hW]

end Lvm.XS
