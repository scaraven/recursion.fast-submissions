-- New for lvm2 roll 11 (M′, R11-X, part 2(b)): M′'s extractor program `decXM`/`extXM` at `S2GM`. Adapted from
-- `LvmXTop.lean` (`acpIR`, `acp3IR`, `okXIR`, `ok1XIR`, `nodeIR`, `decX`, their WF/NoLoopT/outs/cost/size/safe):
-- `C_main`'s three column reads (`LvmMPXRead`), the chain through `C_main`'s 14 fold challenges (`chainLM`), the
-- residual, the three decoders (`decMP2IR`, `decMP1IR`, `decMP0IRW`), the stream block's `2^19` words copied out of
-- the decoded window at the statement's shape, then the shipped node output (`outIR`).
import LvmMPXRead
import LvmMPXCost
import LvmXTop

/-!
# M′'s extractor program

The SNARK branch `decXM` reads the flag `b` (tape word 6): `b = 0` the leaf output (`leafIR`, shipped); else `nodeM`:

1. the log index at `memM = 2^26` (`idxIR4`), the chain scan through position `nChainM pX − 1 = 1318` (`chainLM`);
2. the column reads of `C_main`'s words: level 0 at `wB0M` (rows of 64), levels 1, 2 at `wB1M`, `wB2M` (48 words);
3. the fold challenges (chain answers at `foldPosM`, three words each) to `aB0M`, `aB1M`, `aB2M`; the residual
   (`3·2^9` tape words from `resOffM`) to `fB2M`;
4. `decMP2IR` (level 2; its message, level 1's `f`, to `fB1M`); if it succeeded `decMP1IR` (level 0's `f` to
   `fB0M`); if that succeeded `decMP0IRW` (the window, lanes 40–47, at `mM 19 17 8 dB0M`); if that succeeded
5. the stream block: `2^19` words from the window, at stride 2 from the window's start if the statement is small
   (`n ≤ 2^18`, tape word 19), else at stride 1 from window word `2^19` (`sIdx`: big `sOff20 + i`, small
   `2 (sOff20s + i)`, less `40·2^17`), to `mBM`; and `outIR mBM` (the shipped node output, the stream at `mBM`).

Heap (all below `memM`): level-0 word `[2^25 − 64, 2^26 − 64)`, its decoder `[2^23, 2^23 + 4.99 M)`; level-1 word
`[2^24 + 2^18, …)`, decoder `[2^22, …)`; level-2 word `[2^21, …)`, decoder `[2^21 + 2^19, …)`; `α` at `2^19`; `f₀`,
`f₁`, the residual at `2^20`, `2^20 + 2^19`, `2^20 + 2^19 + 2^15`; the stream block at `2^22 + 2^20`. The chain and
the output buffers are the shipped ones (`2^24 … 2^24 + 344,064`); the output's copy overlaps the start of
level 1's word, which is dead by then.

**`cost_decXM`**: `≤ 2^45 + t/5 · 11,895 + 168 t`; `sizeIR_decXM ≤ 2^19`; `outs_decXM ≤ outCap`; `safe_decXM`.
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## Layout -/

/-- **M′'s static memory** (`2^26` words: the level-0 word alone is `2^25`). -/
def memM : ℕ := 2 ^ 26

/-- The tape word of `C_main`'s level-`i` cap. -/ def capWM (i : ℕ) : ℕ := 5 + capOffM pX i / 8
/-- The tape word of the residual. -/ def resWM : ℕ := 5 + resOffM pX / 8
/-- Level 0's word (rows of 64). -/ def wB0M : ℕ := 2 ^ 25 - 64
/-- Level 1's word. -/ def wB1M : ℕ := 2 ^ 24 + 2 ^ 18
/-- Level 2's word. -/ def wB2M : ℕ := 2 ^ 21
/-- Level 0's workspace. -/ def dB0M : ℕ := 2 ^ 23
/-- Level 1's workspace. -/ def dB1M : ℕ := 2 ^ 22
/-- Level 2's workspace. -/ def dB2M : ℕ := 2 ^ 21 + 2 ^ 19
/-- Level 0's `α` (6 `E`). -/ def aB0M : ℕ := 2 ^ 19
/-- Level 1's `α` (4 `E`). -/ def aB1M : ℕ := 2 ^ 19 + 32
/-- Level 2's `α` (4 `E`). -/ def aB2M : ℕ := 2 ^ 19 + 64
/-- Level 0's `f` (`2^17` `E`, level 1's output). -/ def fB0M : ℕ := 2 ^ 20
/-- Level 1's `f` (`2^13` `E`, level 2's output). -/ def fB1M : ℕ := 2 ^ 20 + 2 ^ 19
/-- Level 2's `f`: the residual (`2^9` `E`). -/ def fB2M : ℕ := 2 ^ 20 + 2 ^ 19 + 2 ^ 15
/-- The stream block (`2^19` words) for the node output. -/ def mBM : ℕ := 2 ^ 22 + 2 ^ 20
/-- The decoded window. -/ abbrev winM : ℕ := mM 19 17 8 dB0M

theorem layoutXM : capWM 0 = 753 ∧ capWM 1 = 17737 ∧ capWM 2 = 28756 ∧ resWM = 35778 ∧
    capOffM pX 0 % 8 = 0 ∧ capOffM pX 1 % 8 = 0 ∧ capOffM pX 2 % 8 = 0 ∧ resOffM pX % 8 = 0 ∧
    foldPosM pX 0 0 = 1244 ∧ foldPosM pX 1 0 = 1285 ∧ foldPosM pX 2 0 = 1315 := by
  decide +kernel

/-! ## The program -/

/-- The fold challenges: level `i`'s `α_{i,j}` (chain answer `foldPosM pX i j`, consecutive in `j`) to `aBiM + 3j`. -/
def acpM : XIR :=
  .seq (acp3IR (ansB + 4 * foldPosM pX 0 0) aB0M 6) (.seq (acp3IR (ansB + 4 * foldPosM pX 1 0) aB1M 4)
    (acp3IR (ansB + 4 * foldPosM pX 2 0) aB2M 4))

/-- **The stream block** from the decoded window at the statement's shape: `eW := [n ≤ 2^18]` (`n` tape word 19); small:
window words `2i`, big: window words `2^19 + i`, `i < 2^19`, to `mBM`. -/
def streamM : XIR :=
  .seq (readAt eW 19) (.seq (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA])
    (.ite eW (mcpIR (2 ^ 19) winM 2 mBM) (mcpIR (2 ^ 19) (winM + 2 ^ 19) 1 mBM)))

/-- After level 0's decoder: if it succeeded, the stream block and the node output. -/
def okL0 : XIR :=
  .seq (.blk [.const eA (toWord (okM dB0M))]) (.seq (.load eW eA) (.ite eW (.seq streamM (outIR mBM)) (.blk [])))

/-- After level 1's decoder: if it succeeded, level 0's decoder and `okL0`. -/
def okL1 : XIR :=
  .seq (.blk [.const eA (toWord (ok1M dB1M))]) (.seq (.load eW eA)
    (.ite eW (.seq (decMP0IRW dB0M wB0M aB0M fB0M) okL0) (.blk [])))

/-- After level 2's decoder: if it succeeded, level 1's decoder and `okL1`. -/
def okL2 : XIR :=
  .seq (.blk [.const eA (toWord (ok1M dB2M))]) (.seq (.load eW eA)
    (.ite eW (.seq (decMP1IR dB1M wB1M aB1M fB1M fB0M) okL1) (.blk [])))

/-- **The node branch at M′.** -/
def nodeM : XIR :=
  .seq (idxIR4 memM pLX) (.seq chainLM (.seq (read0M memM pLX (capWM 0) wB0M)
    (.seq (read1M memM pLX (capWM 1) wB1M) (.seq (read2M memM pLX (capWM 2) wB2M) (.seq acpM
      (.seq (thcpIR resWM fB2M (3 * 2 ^ 9)) (.seq (decMP2IR dB2M wB2M aB2M fB2M fB1M) okL2)))))))

/-- **M′'s SNARK branch**: by the flag `b` (tape word 6). -/
def decXM : XIR := .seq (readAt rBb 6) (.ite rBb nodeM leafIR)

/-! ## Well formed -/

theorem wf_acpM : WF acpM := ⟨wf_acp3IR _ _ _, wf_acp3IR _ _ _, wf_acp3IR _ _ _⟩

theorem wf_streamM : WF streamM := by
  refine ⟨?_, ?_, wf_mcpIR .., wf_mcpIR ..⟩
  · simp +decide [readAt, WF, Prim.dst, rA, eW]
  · simp +decide [WF, Prim.dst, eA, eW]

theorem wf_okL0 : WF okL0 :=
  ⟨by simp +decide [WF, Prim.dst, eA], show 4 ≤ eW by decide, ⟨wf_streamM, wf_outIR _⟩, by simp [WF]⟩

theorem wf_okL1 : WF okL1 :=
  ⟨by simp +decide [WF, Prim.dst, eA], show 4 ≤ eW by decide, ⟨wf_decMP0IR .., wf_okL0⟩, by simp [WF]⟩

theorem wf_okL2 : WF okL2 :=
  ⟨by simp +decide [WF, Prim.dst, eA], show 4 ≤ eW by decide, ⟨wf_dec1MPIR .., wf_okL1⟩, by simp [WF]⟩

theorem wf_nodeM : WF nodeM :=
  ⟨wf_idxIR4 _ _, wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide)),
    wf_readGIR .., wf_readGIR .., wf_readGIR .., wf_acpM, wf_thcpIR _ _ _, wf_dec1MPIR .., wf_okL2⟩

theorem wf_decXM : WF decXM := by
  refine ⟨?_, wf_nodeM, wf_leafIR⟩
  simp +decide [readAt, WF, Prim.dst, rA, rBb]

/-! ## No tape loop but the index's and the chain's; loop bounds -/

theorem noLoopT_acpM : NoLoopT acpM := ⟨noLoopT_acp3IR .., noLoopT_acp3IR .., noLoopT_acp3IR ..⟩

theorem noLoopT_streamM : NoLoopT streamM :=
  ⟨by simp [readAt, NoLoopT], trivial, noLoopT_mcpIR .., noLoopT_mcpIR ..⟩

theorem noLoopT_okL0 : NoLoopT okL0 := ⟨trivial, trivial, ⟨noLoopT_streamM, noLoopT_outIR _⟩, trivial⟩
theorem noLoopT_okL1 : NoLoopT okL1 := ⟨trivial, trivial, ⟨noLoopT_decMP0IR .., noLoopT_okL0⟩, trivial⟩
theorem noLoopT_okL2 : NoLoopT okL2 := ⟨trivial, trivial, ⟨noLoopT_dec1MPIR .., noLoopT_okL1⟩, trivial⟩

/-- **M′'s SNARK branch's loop bounds** on every domain tape of an `S` proof. -/
theorem safe_decXM (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length decXM := by
  refine .seq (safe_of_noLoopT (by simp [readAt, NoLoopT])) (.ite ?_ (safe_of_noLoopT
    ⟨noLoopT_emitIR _, noLoopT_tcpIR _ _⟩))
  refine .seq (safe_idxIR4 _ _ (by have := hs_posL hs; rw [pLX, ← this]; have := ht; have := tape_length c π L; omega) (tape_count_le4 c π L (hs_posL hs) ht))
    (.seq ?_ (.seq (safe_of_noLoopT (noLoopT_readGIR ..)) (.seq (safe_of_noLoopT (noLoopT_readGIR ..))
      (.seq (safe_of_noLoopT (noLoopT_readGIR ..)) (.seq (safe_of_noLoopT noLoopT_acpM)
        (.seq (safe_of_noLoopT (noLoopT_thcpIR ..)) (.seq (safe_of_noLoopT (noLoopT_dec1MPIR ..))
          (safe_of_noLoopT noLoopT_okL2))))))))
  exact safe_chainIR c π L (hs_posL hs) hq ht _ _ noLoopT_sdL wf_sdL
    (nw_sdL _ (by decide) (by decide) (by decide))

/-! ## Output -/

theorem outs_thcpIRM (a d n t : ℕ) : outs (thcpIR a d n) t = 0 := by
  simp [thcpIR, thcpBody, outs]

theorem outs_acpM (t : ℕ) : outs acpM t = 0 := by
  simp only [acpM, outs, outs_acp3IR]

theorem outs_decXM (t : ℕ) : outs decXM t ≤ outCap := by
  have h := outs_outIR mBM t
  have h0 : outs (decMP0IRW dB0M wB0M aB0M fB0M) t = 0 := outs_decMP0IR ..
  have h1 : outs (decMP1IR dB1M wB1M aB1M fB1M fB0M) t = 0 := outs_dec1MPIR ..
  have h2 : outs (decMP2IR dB2M wB2M aB2M fB2M fB1M) t = 0 := outs_dec1MPIR ..
  simp only [decXM, nodeM, okL2, okL1, okL0, streamM, leafIR, readAt, outs, outs_idxIR4, outs_readGIR,
    read0M, read1M, read2M, outs_acpM, h0, h1, h2, emitIR, outs_mcpIR, outs_thcpIRM,
    outs_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), chainLM,
    outs_chainIR (posL (piSize pX)) (nChainM pX) t chTabM (show outs sdL t = 0 by simp [sdL, outs])]
  simp [outs] at *
  rw [outCap]; omega

/-! ## Cost -/

theorem cost_acpM (t : ℕ) : cost acpM t = 789 := by
  simp only [acpM, cost, cost_acp3IR]

theorem cost_streamM (t : ℕ) : cost streamM t ≤ 6815800 := by
  simp only [streamM, readAt, cost, blkSteps, List.length_cons, List.length_nil,
    cost_mcpIR _ _ _ _ t (show 2 ^ 19 < 2 ^ 64 by norm_num)]
  norm_num

/-- After level 0: the stream block and the node output. -/
theorem cost_okL0 (t : ℕ) : cost okL0 t ≤ 22700000 := by
  have hO := cost_outIR mBM t
  have hS := cost_streamM t
  simp only [okL0, cost, blkSteps, List.length_cons, List.length_nil, Nat.max_def]
  split_ifs <;> omega

/-- **M′'s SNARK branch's cost**: the decoders (`2^44.53`), the reads (`2^35.44`), the chain and the index per word. -/
theorem cost_decXM (t : ℕ) : cost decXM t ≤ 2 ^ 45 + t / 5 * 11895 + t * 168 := by
  have hC := cost_chainIR (posL (piSize pX)) (nChainM pX) t chTabM sdL
  rw [chTabM_len, cost_sdL] at hC
  have hD2 := cost_decMP2IR dB2M wB2M aB2M fB2M fB1M t
  have hD1 := cost_decMP1IR dB1M wB1M aB1M fB1M fB0M t
  have hD0 := cost_decMP0IRW dB0M wB0M aB0M fB0M t
  have h0 := cost_okL0 t
  have hR0 := cost_read0M memM pLX (capWM 0) wB0M t
  have hR1 := cost_read1M memM pLX (capWM 1) wB1M t
  have hR2 := cost_read2M memM pLX (capWM 2) wB2M t
  simp only [decXM, nodeM, okL2, okL1, leafIR, readAt, cost, blkSteps, List.length_cons,
    List.length_nil, cost_idxIR4, show chainLM = chainIR (posL (piSize pX)) (nChainM pX) chTabM sdL from rfl,
    hC, hR0, hR1, hR2, cost_acpM, cost_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), emitIR,
    cost_thcpIR _ _ _ t (show 3 * 2 ^ 9 < 2 ^ 64 by norm_num), Nat.max_def]
  split_ifs <;> omega

/-! ## Size -/

private theorem szBlkM (ps : List Prim) : sizeIR (.blk ps) = blkSteps ps.length := by rw [sizeIR]
private theorem szLoadM (d a : ℕ) : sizeIR (.load d a) = 1 := by rw [sizeIR]
private theorem szInputM (d a : ℕ) : sizeIR (.input d a) = 1 := by rw [sizeIR]
private theorem szSeqM (p q : XIR) : sizeIR (.seq p q) = sizeIR p + sizeIR q + 1 := by rw [sizeIR]
private theorem szIteM (c : ℕ) (p q : XIR) : sizeIR (.ite c p q) = sizeIR p + sizeIR q + 1 := by
  rw [sizeIR]

theorem sizeIR_idxM : sizeIR (idxIR4 memM pLX) = 294 := by decide +kernel

theorem sizeIR_dec2M : sizeIR (decMP2IR dB2M wB2M aB2M fB2M fB1M) ≤ 2 ^ 15 := by decide +kernel
theorem sizeIR_dec1M : sizeIR (decMP1IR dB1M wB1M aB1M fB1M fB0M) ≤ 2 ^ 15 := by decide +kernel
theorem sizeIR_dec0M : sizeIR (decMP0IRW dB0M wB0M aB0M fB0M) ≤ 2 ^ 15 := by decide +kernel
theorem sizeIR_outM : sizeIR (.seq streamM (outIR mBM)) ≤ 2 ^ 18 := by decide +kernel

theorem sizeIR_decXM : sizeIR decXM ≤ 2 ^ 19 := by
  have h2 := sizeIR_dec2M
  have h1 := sizeIR_dec1M
  have h0 := sizeIR_dec0M
  have hO := sizeIR_outM
  have hA := sizeIR_acp3IR (ansB + 4 * foldPosM pX 0 0) aB0M 6
  have hB := sizeIR_acp3IR (ansB + 4 * foldPosM pX 1 0) aB1M 4
  have hC := sizeIR_acp3IR (ansB + 4 * foldPosM pX 2 0) aB2M 4
  rw [szSeqM] at hO
  simp only [decXM, nodeM, okL2, okL1, okL0, leafIR, readAt, emitIR, acpM, szBlkM, szLoadM, szInputM,
    szSeqM, szIteM, blkSteps, List.length_cons, List.length_nil, sizeIR_idxM,
    show chainLM = chainIR (posL (piSize pX)) (nChainM pX) chTabM sdL from rfl, sizeIR_chainIR, chTabM_len,
    read0M, read1M, read2M, sizeIR_readGIR, hA, hB, hC]
  simp [tcpIR, tcpBody, thcpIR, thcpBody, sdL, sizeIR, blkSteps]
  omega

end Lvm.X
