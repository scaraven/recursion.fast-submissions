-- New for lvm2 roll 11 (M′, R11-X, part 2(b)): `Computes` for M′'s extractor with the static memory `memM = 2^26`.
-- Adapted from `LvmXComputes.lean` (`DecOk`, `extWith`, `fuel_covers`, `halts_of_tape`, `halts_with`,
-- `computesWith`), `LvmXTop.lean` (`decOk_decX`, `EdX`, `EX`, `computesX`, `extX_caps`) and `LvmXSpec.lean`
-- (`run_W_tape`, `EX_W`): the memory `memX = 2^25` becomes `memM`, the SNARK branch's budget `decBudget` becomes
-- `decBudgetM` (`2^27` held back, for the memory); the declared fuel `fuel t = 2^46 + 2^13 t` is unchanged.
import LvmXSpec
import LvmMPXRead
import LvmMPXCost
import LvmXTop

-- ===== merged from `LvmMPXTop` (GOLF module merge: `LvmMPXTop.lean` is now a stub importing `LvmMPXComputes`) =====
section
-- New for lvm2 roll 11 (M′, R11-X, part 2(b)): M′'s extractor program `decXM`/`extXM` at `S2GM`. Adapted from
-- `LvmXTop.lean` (`acpIR`, `acp3IR`, `okXIR`, `ok1XIR`, `nodeIR`, `decX`, their WF/NoLoopT/outs/cost/size/safe):
-- `C_main`'s three column reads (`LvmMPXRead`), the chain through `C_main`'s 14 fold challenges (`chainLM`), the
-- residual, the three decoders (`decMP2IR`, `decMP1IR`, `decMP0IRW`), the stream block's `2^19` words copied out of
-- the decoded window at the statement's shape, then the shipped node output (`outIR`).

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
  -- the offsets from `layoutM_P20` (one kernel evaluation of the FS messages left, `resWM`'s)
  obtain ⟨-, f0, f1, f2, -, c0, c1, c2, r, -⟩ := layoutM_P20
  refine ⟨by rw [capWM, c0], by rw [capWM, c1], by rw [capWM, c2], by decide +kernel, by rw [c0], by rw [c1],
    by rw [c2], by rw [r], f0, f1, f2⟩

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
  rw [outCap]; (clear * - t h; omega)

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
theorem sizeIR_outM : sizeIR (.seq streamM (outIR mBM)) ≤ 2 ^ 18 := by
  rw [szSeqM, outIR]
  simp only [szSeqM, sizeIR_leafStmtIR, sizeIR_segIR, segSizes.1, segSizes.2.1, segSizes.2.2]
  decide +kernel

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
  simp only [tcpIR, tcpBody, thcpIR, thcpBody, sdL, sizeIR, blkSteps, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  (clear * - h2 h1 h0 hO; omega)

end Lvm.X
end
-- ===== end of `LvmMPXTop` =====

/-!
# `Computes extXM (EXM A) fuel`

* `decBudgetM t = 2^46 − 2^27 + (2^13 − 16) t`; `DecOkM pz dec`: `DecOk` with that budget.
* `extWithM pz dec = toProg memM mpwX (extIRWith pz dec)`: the shipped parse and `W` copy, M′'s memory.
* **`decOk_decXM`**: M′'s SNARK branch meets it (`cost_decXM ≤ 2^45 + …`).
* `EdXM`, **`EXM A`** (the specification: the denotation on the domain, the shipped `EoutX A` outside),
  **`computesXM`**, `extXM_caps`, **`EXM_W`** (witness-sending proofs decode).
-/

namespace Lvm.X

open RecursionFast

/-- What M′'s SNARK branch may cost: the fuel less the memory (`2^26` and the margin), the parse and the `W`
branch. -/
def decBudgetM (t : ℕ) : ℕ := fuelBase - 2 ^ 27 + (fuelPerWord - 16) * t

/-- **The obligations on M′'s SNARK branch** (as `DecOk`, budget `decBudgetM`). -/
structure DecOkM (pz : ℕ) (dec : XIR) : Prop where
  pz_lt : pz < 2 ^ 64
  wf : WF dec
  safe : ∀ c (π : Proof) (L : Log), π.size = pz → (∀ e ∈ L, e.1.size < 2 ^ 64) →
    (extractorInput c π L).length ≤ 2 ^ 64 →
    Safe (extractorInput c π L).toArray (extractorInput c π L).length dec
  cost : ∀ t, cost dec t ≤ decBudgetM t
  outs : ∀ t, outs dec t ≤ outCap
  size : sizeIR dec ≤ 2 ^ 19

/-- The program at M′'s memory. -/
def extWithM (pz : ℕ) (dec : XIR) : XProg := toProg memM mpwX (extIRWith pz dec)

theorem fuel_coversM {pz : ℕ} {dec : XIR} (h : ∀ t, cost dec t ≤ decBudgetM t) (t : ℕ) :
    memM + mpwX * t + cost (extIRWith pz dec) t + 8 ≤ fuel t := by
  have := h t
  rw [cost_extIRWith]
  simp only [memM, mpwX, fuel, fuelBase, fuelPerWord, decBudgetM] at *
  (clear * - this; omega)

theorem size_extWithM {pz : ℕ} {dec : XIR} (h : sizeIR dec ≤ 2 ^ 19) :
    (extWithM pz dec).body.size ≤ progCap := by
  simp only [extWithM, toProg, size_compile, sizeIR, sizeIR_extIRWith, initPs, blkSteps,
    List.length_cons, List.length_nil, progCap]
  norm_num; (clear * - dec h; omega)

theorem halts_of_tapeM {pz : ℕ} {dec : XIR} (hd : DecOkM pz dec) (inp : List Word) (a : ℕ)
    (ha : a ≤ 8 * outCap)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hsafe : a = pz → Safe inp.toArray inp.length dec) :
    ∃ o, (extWithM pz dec).run inp (fuel inp.length) = some o ∧ o.length ≤ outCap := by
  rw [outCap] at ha
  have hwf := wf_extIRWith (pz := pz) hd.wf
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0 : Inv (initSt (memM + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memM + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hsafe
  have h1 : Inv (semXIR I (parseIR pz) s0).M := inv_sem I hwf.1 h0
  have hpi : rd (semXIR I (parseIR pz) s0).M rIsSz ≠ 0 → a = pz := by
    intro h
    rw [parse_regs pz I s0 h0, h4] at h
    by_contra hne
    refine h (if_neg fun he => hne ?_)
    have := congrArg BitVec.toNat he
    rwa [toNat_toWord (by (clear * - ha; omega)), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hd.pz_lt] at this
  have hpo : (semXIR I (parseIR pz) s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  generalize hs1 : semXIR I (parseIR pz) s0 = s1 at h1 hpi hpo
  have hB : BoundsOk I inp.length (extIRWith pz dec) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR pz _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk : rd s1.M rIsK = 0
    · rw [if_pos hk]
      exact boundsOk_of_safe (safe_wIR (by (clear * - ha; omega)) h4 (by (clear * - hlen; omega))) hwf.2.2 _ h1
    · rw [if_neg hk, boundsOk_ite]
      by_cases hz : rd s1.M rIsSz = 0
      · rw [if_pos hz]; trivial
      · rw [if_neg hz]
        exact boundsOk_of_safe (hsafe (hpi hz)) hd.wf _ h1
  have hrun := run_toProg (P := extIRWith pz dec) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_coversM hd.cost _)
  rw [hs0, hI] at hrun
  refine ⟨_, hrun, ?_⟩
  by_cases hk : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith pz dec) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk]
    have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 (by (clear * - ha; omega))]
    have := congrArg List.length ((congrArg (fun s' : St => s'.o.toList) e).trans
      (wIR_sem I _ h1 (by (clear * - ha hw; omega))))
    simp only [hpo, hw, Array.toList_empty, List.nil_append, List.length_map,
      List.length_range] at this
    rw [this, outCap]
    (clear * - ha hw this; omega)
  · by_cases hz : rd s1.M rIsSz = 0
    · have e : semXIR I (extIRWith pz dec) s0 = semXIR I (.blk []) s1 := by
        rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_pos hz]
      have hl : (semXIR I (extIRWith pz dec) s0).o.toList.length = 0 := by
        rw [e]; simp [semXIR, hpo]
      rw [hl]; exact Nat.zero_le _
    · have e : semXIR I (extIRWith pz dec) s0 = semXIR I dec s1 := by
        rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]
      have := outs_le (I := I) inp.length dec _ hd.wf h1
        (boundsOk_of_safe (hsafe (hpi hz)) hd.wf _ h1)
      rw [hpo, ← e] at this
      have h2 := hd.outs inp.length
      simp only [Array.size_empty, Nat.zero_add] at this
      rw [Array.length_toList]; exact this.trans h2

theorem computesWithM {pz : ℕ} {dec : XIR} (hd : DecOkM pz dec) :
    Computes (extWithM pz dec) (Eden memM mpwX (extIRWith pz dec)) fuel :=
  computes_Eof fuel (by simp only [regs, memM]; norm_num) (wf_extIRWith (pz := pz) hd.wf)
    fun c π L h1 h2 h3 => halts_of_tapeM hd _ π.size h1 (by rw [getD_toArray, tape_getD4])
      (tape_length c π L) fun h => hd.safe c π L h h2 h3

/-! ## M′'s extractor -/

/-- **M′'s SNARK branch meets `DecOkM`.** -/
theorem decOk_decXM : DecOkM (piSize pX) decXM where
  pz_lt := by rw [piSize_eq]; norm_num
  wf := wf_decXM
  safe := fun c π L hs hq ht => safe_decXM c π L hs hq ht
  cost := fun t => by
    have := cost_decXM t
    simp only [decBudgetM, fuelBase, fuelPerWord]
    omega
  outs := outs_decXM
  size := sizeIR_decXM

/-- **M′'s extractor program.** -/
def extXM : XProg := extWithM (piSize pX) decXM

/-- The in-domain extractor: the program's decoded denotation. -/
def EdXM : Digest → Proof → Log → Option Wit := Eden memM mpwX (extIRWith (piSize pX) decXM)

/-- **M′'s extractor specification**: `EdXM` on the domain, the shipped `EoutX A` outside (`A`: the certificate's
`S.acc`). -/
def EXM (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if InDomE c π L then EdXM c π L else EoutX A c π L

/-- **`Computes extXM (EXM A) fuel`** with the declared fuel `2^46 + 2^13 t`. -/
theorem computesXM (A : Digest → Digest → Signed → Bool) : Computes extXM (EXM A) fuel :=
  fun c π L h1 h2 h3 => by
    obtain ⟨o, ho, hl, hd⟩ := computesWithM decOk_decXM c π L h1 h2 h3
    exact ⟨o, ho, hl, hd.trans (if_pos ⟨h1, h2, h3⟩).symm⟩

/-- The certificate's caps on M′'s extractor: the fuel within `B`, the program within `progCap`. -/
theorem extXM_caps : (∀ t, fuel t ≤ extractorBudget t) ∧ extXM.body.size ≤ progCap :=
  ⟨fuel_le_budget, size_extWithM decOk_decXM.size⟩

/-! ## The `W` kind -/

theorem run_W_tapeM (inp : List Word) (a : ℕ) (ha : a < 2 ^ 64)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hk : a ≠ 0 → ¬ (inp.toArray.getD 5 0 &&& 0xFF = kindS)) :
    extXM.run inp (fuel inp.length) =
      some ((List.range ((a + 7) / 8)).map fun j => inp.toArray.getD (5 + j) 0) := by
  have hd := decOk_decXM
  have hwf := wf_extIRWith (pz := piSize pX) hd.wf
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0 : Inv (initSt (memM + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memM + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Inv (semXIR I (parseIR (piSize pX)) s0).M := inv_sem I hwf.1 h0
  have hz0 : a = 0 → rd (semXIR I (parseIR (piSize pX)) s0).M rIsSz = 0 := by
    intro h
    rw [parse_regs _ I s0 h0, h4, h, if_neg]
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_toWord (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [piSize_eq]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)),
      piSize_eq] at this
    (clear * - this; omega)
  have hk' : a ≠ 0 → rd (semXIR I (parseIR (piSize pX)) s0).M rIsK = 0 := fun h => by
    rw [parse_isK _ I s0 h0, if_neg (hk h)]
  have hpo : (semXIR I (parseIR (piSize pX)) s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 ha]
  generalize hs1 : semXIR I (parseIR (piSize pX)) s0 = s1 at h1 hz0 hk' hpo
  have hB : BoundsOk I inp.length (extIRWith (piSize pX) decXM) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk1 : rd s1.M rIsK = 0
    · rw [if_pos hk1]
      exact boundsOk_of_safe (safe_wIR ha h4 (by (clear * - hlen hw; omega))) hwf.2.2 _ h1
    · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
      rw [if_neg hk1, boundsOk_ite, if_pos (hz0 ha0)]; trivial
  have hrun := run_toProg (P := extIRWith (piSize pX) decXM) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_coversM hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  by_cases hk1 : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith (piSize pX) decXM) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk1]
    rw [congrArg (fun s' : St => s'.o.toList) e, wIR_sem I _ h1 (by (clear * - ha hw; omega)), hpo, hw]
    rfl
  · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
    have e : semXIR I (extIRWith (piSize pX) decXM) s0 = semXIR I (.blk []) s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos (hz0 ha0)]
    rw [congrArg (fun s' : St => s'.o.toList) e, ha0]
    simp [semXIR, hpo]

/-- **`EXM` on a `W` proof** (first byte not `'S'`), on every log: `WitnessSending.decode π`. -/
theorem EXM_W (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hW : π.data[0]? ≠ some 0x53) : EXM A c π L = WitnessSending.decode π := by
  by_cases hD : InDomE c π L
  · rw [EXM, if_pos hD, EdXM]
    have hπ : π.size < 2 ^ 64 := by have := hD.1; rw [outCap] at this; (clear * - this; omega)
    have hrun := run_W_tapeM (extractorInput c π L) π.size hπ (by rw [getD_toArray, tape_getD4])
      (tape_length c π L) (fun hne he => by
        obtain ⟨b, hb⟩ : ∃ b, π.data[0]? = some b := by
          rcases h : π.data[0]? with _ | b
          · rw [Array.getElem?_eq_none_iff] at h; exact (hne (Nat.le_zero.mp h)).elim
          · exact ⟨b, rfl⟩
        have h1 := tape_byte0 c π L hb
        have h2 := congrArg BitVec.toNat he
        rw [lowByte, getD_toArray, h1] at h2
        exact hW (by rw [hb]; congr 1; exact UInt8.toNat_inj.mp h2))
    rw [Eden, ← den_of_run (by simp only [regs, memM]; norm_num) (wf_extIRWith decOk_decXM.wf) hrun,
      WitnessSending.decode]
    congr 1
    refine List.ext_getElem (by
      simp only [List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · rw [EXM, if_neg hD, EoutX, if_neg hW]

end Lvm.X
