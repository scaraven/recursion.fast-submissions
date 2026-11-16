-- New for lvm2 roll 11 (M′, R11-X, part 2(b)): the column reads of `C_main`'s three words, generic in the tree.
-- Adapted from `LvmXReadDefs.lean` (`crCapPs`, `crZero`, `crCopy`, `crPos`, `readIR`, their WF/cost) and
-- `LvmXRead1Defs.lean` (`cr1CapPs`, `cr1Copy`, `cr1Pos`, `read1IR`): the shipped reads at `(2^15, 8, 29, 35)` and
-- `(2^12, 5, 0, 48)` become `readGIR … nPos D z occ`; the walk's pieces (`crLd4`, `crNode`, `crLeaf`, `crCopyBody`,
-- `crZeroBody`, `lookIR4`) are reused unchanged.
import LvmXRead1Defs
import LvmMPXLayout

/-!
# The column reads of `C_main` (`S2GM`)

`readGIR bX pL capW wB nPos D z occ`: for every position `p < nPos`, from the cap node `p >> D` (tape word
`capW + 4 (p >> D)`), `D` first-preimage steps down, the leaf; its row of `z + occ` words at `wB + (z + occ) p`:
`z` zero words, then the leaf's first `occ` words (missing bytes as zero; an erasure is the zero row).

* `readGIR_rec`, `read1GIR_rec`: the shipped `readIR`, `read1IR` are the instances `(2^15, 8, 29, 35)`, `(2^12, 5,
  0, 48)` (`rfl`).
* `C_main`'s words at `P20` (`layoutM_P20`): level 0 `(2^19, 11, 17, 47)` (rows of 64 words, the root leaf of 47
  words; row word `t` is lane `63 − t`), level 1 `(2^16, 9, 0, 48)`, level 2 `(2^13, 6, 0, 48)`.
* Exact cost: `14 + nPos (6572 + 6532 D + 9 z + 25 occ)`; at `C_main`'s words `2^35.28`, `2^32.02`, `2^28.52`.
-/

namespace Lvm.X

open RecursionFast

/-! ## The program -/

/-- The cap node of position `p`: `crTA := capW + 4 (p >> D)`. -/
def crCapGPs (capW D : ℕ) : List Prim :=
  [.const crK (toWord D), .op .shr crB crP crK, .const crK 2, .op .shl crB crB crK,
   .const crK (toWord capW), .op .add crTA crB crK]

/-- The row's zero prefix: `z` zero words from `crWA`. -/
def crZeroG (z : ℕ) : XIR :=
  .seq (.blk [.const crV 0, .const crNw (toWord z)]) (.loopK crCw crNw (toWord z) crZeroBody)

/-- The row: the zero prefix, then the leaf's first `occ` words from tape word `X + 1`. -/
def crCopyG (z occ : ℕ) : XIR :=
  .seq (crZeroG z)
    (.seq (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
      (.loopK crCw crNw (toWord occ) crCopyBody))

/-- **One position**: the cap node, `D` steps down, the leaf, its row, `p += 1`. -/
def crPosG (bX pL capW D z occ : ℕ) : XIR :=
  .seq (.seq (.blk (crCapGPs capW D)) crLd4) (.seq (.blk [.const crOk 1, .const crNH (toWord D)])
    (.seq (.loopK crHc crNH (toWord D) (crNode bX pL)) (.seq (crLeaf bX pL) (.seq (crCopyG z occ)
      (.blk [.op .add crP crP cOne])))))

/-- **The column reads**: positions `0 … nPos − 1`, row word `t` of position `p` at `wB + (z + occ) p + t`. -/
def readGIR (bX pL capW wB nPos D z occ : ℕ) : XIR :=
  .seq (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord nPos)])
    (.loopK crCp crNp (toWord nPos) (crPosG bX pL capW D z occ))

/-! ## The shipped reads are instances -/

theorem readGIR_rec (bX pL capW wB : ℕ) : readGIR bX pL capW wB (2 ^ 15) 8 (64 - crOcc) crOcc =
    readIR bX pL capW wB := rfl

/-! ## Well formed, no tape loop, no output, size -/

theorem wf_readGIR (bX pL capW wB nPos D z occ : ℕ) : WF (readGIR bX pL capW wB nPos D z occ) := by
  have h1 := cr_wf_look bX pL
  have h2 : ¬ Writes (lookIR4 bX pL) 130 := cr_look_nw bX pL (by omega)
  have h3 : ¬ Writes (lookIR4 bX pL) 119 := cr_look_nw bX pL (by omega)
  simp +decide [readGIR, crPosG, crLd4, crCapGPs, crGet, crChkPs, crChildPs, crNode, crLeaf,
    crCopyBody, crCopyG, crZeroG, crZeroBody, WF, Writes, Prim.dst, crP, crOk, crHc, crNH, crX, crQn,
    crB, crTA, crWA, cr8, crMk, crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3,
    cTmp, regs, h1, h2, h3]

/-- **The registers the read writes**: the compiler's scratch, `rA`, `75 … 135`. -/
theorem readGIR_nw (bX pL capW wB nPos D z occ : ℕ) {r : ℕ}
    (h : 136 ≤ r ∨ (5 ≤ r ∧ r < 64) ∨ (65 ≤ r ∧ r < 75)) :
    ¬ Writes (readGIR bX pL capW wB nPos D z occ) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r := cr_look_nw bX pL (by omega)
  simp [readGIR, crPosG, crLd4, crCapGPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    crCopyG, crZeroG, crZeroBody, Writes, Prim.dst, hl, crP, crOk, crHc, crNH, crX, crQn, crB, crTA,
    crWA, cr8, crMk, crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3, cTmp]
  omega

theorem noLoopT_readGIR (bX pL capW wB nPos D z occ : ℕ) : NoLoopT (readGIR bX pL capW wB nPos D z occ) := by
  simp [readGIR, crPosG, crLd4, crGet, crNode, crLeaf, crCopyBody, crCopyG, crZeroG, crZeroBody,
    lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, readAt, NoLoopT]

theorem outs_readGIR (bX pL capW wB nPos D z occ t : ℕ) : outs (readGIR bX pL capW wB nPos D z occ) t = 0 := by
  simp [readGIR, crPosG, crLd4, crGet, crNode, crLeaf, crCopyBody, crCopyG, crZeroG, crZeroBody,
    lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, readAt, outs]

theorem sizeIR_readGIR (bX pL capW wB nPos D z occ : ℕ) : sizeIR (readGIR bX pL capW wB nPos D z occ) = 563 := by
  simp only [readGIR, crPosG, crLd4, crCapGPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    crCopyG, crZeroG, crZeroBody, lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR,
    ceil8Ps, readAt, sizeIR, blkSteps, List.length_cons, List.length_nil, List.length_append]
  norm_num

/-! ## Cost -/

/-- **One position's cost**: `D` node steps of `6,532`, the leaf, the row (`27 + 9 z + 25 occ`), the rest. -/
theorem cost_crPosG (bX pL capW D z occ t : ℕ) (hD : D < 2 ^ 64) (hz : z < 2 ^ 64) (ho : occ < 2 ^ 64) :
    cost (crPosG bX pL capW D z occ) t = 6569 + 6532 * D + 9 * z + 25 * occ := by
  simp only [crPosG, crCapGPs, crLd4, crNode, crGet, crChkPs, crChildPs, crLeaf, crCopyG, crZeroG,
    crZeroBody, crCopyBody, cost, cr_cost_look, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord hD, toNat_toWord hz, toNat_toWord ho]
  norm_num; ring

/-- **The read's cost** on every tape. -/
theorem cost_readGIR (bX pL capW wB nPos D z occ t : ℕ) (hn : nPos < 2 ^ 64) (hD : D < 2 ^ 64)
    (hz : z < 2 ^ 64) (ho : occ < 2 ^ 64) :
    cost (readGIR bX pL capW wB nPos D z occ) t = 14 + nPos * (6572 + 6532 * D + 9 * z + 25 * occ) := by
  simp only [readGIR, cost, cost_crPosG bX pL capW D z occ t hD hz ho, blkSteps, List.length_cons,
    List.length_nil, toNat_toWord hn]
  norm_num; ring

/-! ## `C_main`'s three words -/

/-- **Level 0's word** (`2^19` positions, 11 steps below the cap of `2^8`, rows of 64: 17 zero words, the 47-word
leaf). -/
def read0M (bX pL capW wB : ℕ) : XIR := readGIR bX pL capW wB (2 ^ 19) 11 17 47
/-- **Level 1's word** (`2^16` positions, 9 steps, 48-word leaves). -/
def read1M (bX pL capW wB : ℕ) : XIR := readGIR bX pL capW wB (2 ^ 16) 9 0 48
/-- **Level 2's word** (`2^13` positions, 6 steps, 48-word leaves). -/
def read2M (bX pL capW wB : ℕ) : XIR := readGIR bX pL capW wB (2 ^ 13) 6 0 48

theorem cost_read0M (bX pL capW wB t : ℕ) : cost (read0M bX pL capW wB) t = 41813016590 := by
  rw [read0M, cost_readGIR _ _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
theorem cost_read1M (bX pL capW wB t : ℕ) : cost (read1M bX pL capW wB) t = 4362076174 := by
  rw [read1M, cost_readGIR _ _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
theorem cost_read2M (bX pL capW wB t : ℕ) : cost (read2M bX pL capW wB) t = 384729102 := by
  rw [read2M, cost_readGIR _ _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The shape check: the read depths and occupancy are `layoutM_P20`'s (`19 − 8`, `16 − 7`, `13 − 7`; the root leaf
of `376 = 8 · 47` bytes, the others `384 = 8 · 48`). -/
theorem readM_shape : readDepthM pX 0 = 11 ∧ readDepthM pX 1 = 9 ∧ readDepthM pX 2 = 6 ∧
    (mainL pX 0).row = 8 * 47 ∧ (mainL pX 1).row = 8 * 48 ∧ (mainL pX 2).row = 8 * 48 := by
  decide +kernel

end Lvm.X
