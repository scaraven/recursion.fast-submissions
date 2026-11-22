-- New for lvm2 roll 11 (M′, R11-X): the advice decoders' programs generic in the shape, for M′'s decoders
-- `decodeMP0/1/2` (`LvmMPDec`). Adapted from `LvmXAgree.lean` (`testIR`, `posBody`, `agreeIR`),
-- `LvmXDec1Agree.lean` (`test1IR`, `pos1Body`, `agree1IR`), `LvmXDecIR.lean` (`encC`, `bflyRow`, `bflyAll`,
-- `okIR`, `decTail`), `LvmXDecIR3.lean` (`decIR`), `LvmXCopy.lean` (`msgRow`, `rowsIR`), `LvmXDec1IR.lean`
-- (`enc1C`, `bfly1Row`, `bfly1All`, `ok1IR`, `tr1Row`, `tr1IR`, `dec1Tail`) and `LvmXDec1IR2.lean` (`dec1IR`):
-- the literals (`2^15`/`2^12` positions, `2^13`/`2^9` coefficients, 64 decoded rows, table dimension 15, the
-- workspace offsets) become parameters.
import LvmMPXNtt
import LvmXDecCost
import LvmXDec1Cost

/-!
# M′'s decoder programs, generic in the shape

**Level 0** (`decMP0IR N nL kL lo C dB wB aB fB`, `decodeG0 N nL kL lo C`): the word's `2^nL` positions of 64
leaf words at `wB + 64 q + t`, `α` (6 `E`) at `aB`, the residual (`2^kL` `E`) at `fB`; it decodes the `C` rows
`lo … lo + C − 1` only. **Workspace** `[dB, dB + 2^13 + 2^(kL+1) + 5·2^nL + 2C·2^kL)`:

| cells | content |
|---|---|
| `tbM = dB` | basis table, `N²` words (`N ≤ 64`) |
| `qM = dB + 2^12` | `eq(α, ·)`, 192 words |
| `okM = dB + 2^12 + 256` | the flag |
| `wbM = dB + 2^13`, `ebM = wbM + 2^kL` | interpolation weights and `E` row, `2^kL` each |
| `agM = dB + 2^13 + 2^(kL+1)` | the agreement list, `2^nL` |
| `encM = agM + 2^nL` | `Enc(f)`'s three coordinates, `3·2^nL` (slot `4·2^nL`) |
| `oM = encM + 4·2^nL` | the interpolated rows, `C·2^kL` (row `lo + C − 1 − c` at `oM + c·2^kL`) |
| `mM = oM + C·2^kL` | **the decoded window**, `C·2^kL` words in `decodeG0`'s order |

The interpolation reads the window's leaf words `64 − lo − C … 63 − lo` (`cb = wB + 64 − lo − C`, stride 64);
`rowsMIR` puts row `lo + r` at `mM + r·2^kL`.

**Levels ≥ 1** (`dec1MPIR N nL kL dB wB aB fB oB`, `decode1G N nL kL`): `2^nL` positions of 48 leaf words at
`wB + 48 q + t`, `α` (4 `E`) at `aB`, `f` (`2^kL` `E`) at `fB`; output `2^(kL+4)` `E` entries at `oB` (entry
`u + 16 v` at `oB + 3(u + 16 v)`, the next level's `fB`). Workspace `[dB, dB + 2^13 + 2^(kL+1) + 5·2^nL + 48·2^kL)`
with the same offsets (`q1M`, `ok1M`, `wb1M`, `eb1M`, `ag1M`, `enc1M`, `ob1M`).

M′'s instances: `decMP2IR = dec1MPIR 19 13 9`, `decMP1IR = dec1MPIR 19 16 13`, `decMP0IR' = decMP0IR 19 19 17 40 8`.
The shipped scans are instances (`agreeNIR_15`, `agree1NIR_12`), and so are the shipped reorders (`rowsMIR_64`,
`tr1MIR_9`) and NTT loops (`bflyAllM_lvm`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

/-! ## The agreement scans at `n` positions -/

/-- **The comparison** with `Enc(f)[q]`'s coordinates at `eB + c·n + q` (`testIR` at `n`). -/
def testNIR (n eB : ℕ) : XIR :=
  .seq (.blk [.const gK (toWord eB), .op .add gX gQ gK]) (.seq (.load gE gX)
    (.seq (.blk [.op .eq gZ gE gA0, .const gK (toWord n), .op .add gX gX gK])
      (.seq (.load gE gX) (.seq (.blk [.op .eq gZ2 gE gA1, .op .and gZ gZ gZ2, .op .add gX gX gK])
        (.seq (.load gE gX) (.blk [.op .eq gZ2 gE gA2, .op .and gZ gZ gZ2]))))))

/-- One position of the level-0 scan. -/
def posNBody (n wB qB eB agB : ℕ) : XIR :=
  .seq (foldIR wB qB) (.seq (testNIR n eB) (.seq (.ite gZ (appendIR agB) (.blk []))
    (.blk [.op .add gQ gQ cOne])))

/-- **The level-0 agreement scan** over `q < n` (64 `K` lanes). -/
def agreeNIR (n wB qB eB agB : ℕ) : XIR :=
  .seq (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord n)])
    (.loopK gC1 gN1 (toWord n) (posNBody n wB qB eB agB))

/-- The level-≥1 comparison at stride `n` (`test1IR` at `n`). -/
def test1NIR (n eB : ℕ) : XIR :=
  .seq (.blk [.const gK (toWord eB), .op .add gX gQ gK]) (.seq (.load gE gX)
    (.seq (.blk [.op .eq gZ gE h1A, .const gK (toWord n), .op .add gX gX gK])
      (.seq (.load gE gX) (.seq (.blk [.op .eq gZ2 gE (h1A + 1), .op .and gZ gZ gZ2,
        .op .add gX gX gK])
        (.seq (.load gE gX) (.blk [.op .eq gZ2 gE (h1A + 2), .op .and gZ gZ gZ2]))))))

/-- One position of the level-≥1 scan. -/
def pos1NBody (n wB qB eB agB : ℕ) : XIR :=
  .seq (fold1IR wB qB) (.seq (test1NIR n eB) (.seq (.ite gZ (appendIR agB) (.blk []))
    (.blk [.op .add gQ gQ cOne])))

/-- **The level-≥1 agreement scan** over `q < n` (16 `E` lanes). -/
def agree1NIR (n wB qB eB agB : ℕ) : XIR :=
  .seq (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord n)])
    (.loopK gC1 gN1 (toWord n) (pos1NBody n wB qB eB agB))

theorem agreeNIR_15 (wB qB eB agB : ℕ) : agreeNIR (2 ^ 15) wB qB eB agB = agreeIR wB qB eB agB := rfl
theorem agree1NIR_12 (wB qB eB agB : ℕ) : agree1NIR (2 ^ 12) wB qB eB agB = agree1IR wB qB eB agB := rfl

/-! ## Level 0: layout -/

/-- The basis table. -/ def tbM (dB : ℕ) : ℕ := dB
/-- The `eq(α, ·)` table. -/ def qM (dB : ℕ) : ℕ := dB + 2 ^ 12
/-- The success flag. -/ def okM (dB : ℕ) : ℕ := dB + 2 ^ 12 + 256
/-- The interpolation weights. -/ def wbM (dB : ℕ) : ℕ := dB + 2 ^ 13
/-- The interpolation's `E` row. -/ def ebM (kL dB : ℕ) : ℕ := dB + 2 ^ 13 + 2 ^ kL
/-- The agreement list. -/ def agM (kL dB : ℕ) : ℕ := dB + 2 ^ 13 + 2 ^ (kL + 1)
/-- `Enc(f)`'s coordinates. -/ def encM (nL kL dB : ℕ) : ℕ := agM kL dB + 2 ^ nL
/-- The interpolated rows. -/ def oM (nL kL dB : ℕ) : ℕ := encM nL kL dB + 4 * 2 ^ nL
/-- **The decoded window.** -/ def mM (nL kL C dB : ℕ) : ℕ := oM nL kL dB + C * 2 ^ kL
/-- The workspace's size. -/ def wsM (nL kL C : ℕ) : ℕ := 2 ^ 13 + 2 ^ (kL + 1) + 5 * 2 ^ nL + 2 * C * 2 ^ kL

/-! ## Level 0: the programs -/

/-- **`Enc(f)`'s coordinate `c`** at `encM + c·2^nL`: copy, zero padding, forward NTT at `nL`. -/
def encMC (N nL kL dB fB c : ℕ) : XIR :=
  .seq (mcpIR (2 ^ kL) (fB + c) 3 (encM nL kL dB + c * 2 ^ nL))
    (.seq (zeroIR (2 ^ nL - 2 ^ kL) (encM nL kL dB + c * 2 ^ nL + 2 ^ kL))
      (.seq (.blk [.const rA0 (toWord (encM nL kL dB + c * 2 ^ nL))]) (fwdNIR N nL (tbM dB))))

/-- The three coordinates. -/
def encMIR (N nL kL dB fB : ℕ) : XIR :=
  .seq (encMC N nL kL dB fB 0) (.seq (encMC N nL kL dB fB 1) (encMC N nL kL dB fB 2))

/-- One row `t` of `2^kL` coefficients at `ob`: the inverse NTT at table dimension `N`, `t += 1`. -/
def bflyRowM (N kL tb ob : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ kL)), .op .mul rA0 zT zK, .const zK (toWord ob),
      .op .add rA0 rA0 zK]) (.seq (bflyNIR N kL tb) (.blk [.op .add zT zT cOne]))

/-- **The inverse NTT of `R` rows** of `2^kL` coefficients at `ob`. -/
def bflyAllM (N kL R tb ob : ℕ) : XIR :=
  .seq (.blk [.const zT 0, .const zN (toWord R)]) (.loopK zC zN (toWord R) (bflyRowM N kL tb ob))

/-- **The flag** `rOk := [2^kL ≤ cnt]`, stored at `ok`. -/
def okMIR (kL ok : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ kL)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord ok)]) (.store zK rOk)

/-- One window row `r` (`yL`): source row `C − 1 − r` at `oB`, `2^kL` words to `mB + r·2^kL`; `r += 1`. -/
def msgRowM (kL C oB mB : ℕ) : XIR :=
  .seq (.blk [.const yK (toWord (C - 1)), .op .sub ySr yK yL, .const yK (toWord (2 ^ kL)),
      .op .mul ySr ySr yK, .const yK (toWord oB), .op .add ySr ySr yK, .const yK (toWord (2 ^ kL)),
      .op .mul yDs yL yK, .const yK (toWord mB), .op .add yDs yDs yK, .const yStr 1])
    (.seq (mcpLoop (2 ^ kL)) (.blk [.op .add yL yL cOne]))

/-- **The reorder** of the `C` interpolated rows into the window's order. -/
def rowsMIR (kL C oB mB : ℕ) : XIR :=
  .seq (.blk [.const yL 0, .const yN2 (toWord C)]) (.loopK yC2 yN2 (toWord C) (msgRowM kL C oB mB))

/-- **The decoding proper** (on success): interpolation of the window's `C` rows on the first `2^kL` listed
positions, the inverse NTT per row, the reorder. -/
def decMP0Tail (N nL kL lo C dB wB : ℕ) : XIR :=
  .seq (baryIR (2 ^ kL) C (agM kL dB) (wbM dB) (ebM kL dB) (wB + (64 - lo - C)) 64 (oM nL kL dB))
    (.seq (bflyAllM N kL C (tbM dB) (oM nL kL dB)) (rowsMIR kL C (oM nL kL dB) (mM nL kL C dB)))

/-- **The level-0 decoder program** (`decodeG0 N nL kL lo C`). -/
def decMP0IR (N nL kL lo C dB wB aB fB : ℕ) : XIR :=
  .seq (wtabNIR N (tbM dB)) (.seq (eqtIR 6 aB (qM dB)) (.seq (encMIR N nL kL dB fB)
    (.seq (agreeNIR (2 ^ nL) wB (qM dB) (encM nL kL dB) (agM kL dB)) (.seq (okMIR kL (okM dB))
      (.ite rOk (decMP0Tail N nL kL lo C dB wB) (.blk []))))))

theorem rowsMIR_64 (oB mB : ℕ) : rowsMIR 13 64 oB mB = rowsIR oB mB := rfl
theorem bflyAllM_lvm (dB : ℕ) : bflyAllM 15 13 64 (tbB dB) (oB dB) = bflyAll dB := rfl

/-! ## Levels ≥ 1: layout and programs -/

/-- The `eq(α, ·)` table. -/ def q1M (dB : ℕ) : ℕ := dB + 2 ^ 12
/-- The success flag. -/ def ok1M (dB : ℕ) : ℕ := dB + 2 ^ 12 + 256
/-- The interpolation weights. -/ def wb1M (dB : ℕ) : ℕ := dB + 2 ^ 13
/-- The interpolation's `E` row. -/ def eb1M (kL dB : ℕ) : ℕ := dB + 2 ^ 13 + 2 ^ kL
/-- The agreement list. -/ def ag1M (kL dB : ℕ) : ℕ := dB + 2 ^ 13 + 2 ^ (kL + 1)
/-- `Enc(f)`'s coordinates. -/ def enc1M (nL kL dB : ℕ) : ℕ := ag1M kL dB + 2 ^ nL
/-- The interpolated lanes (`2^kL` each). -/ def ob1M (nL kL dB : ℕ) : ℕ := enc1M nL kL dB + 4 * 2 ^ nL
/-- The workspace's size. -/ def ws1M (nL kL : ℕ) : ℕ := 2 ^ 13 + 2 ^ (kL + 1) + 5 * 2 ^ nL + 48 * 2 ^ kL

/-- **`Enc(f)`'s coordinate `c`** at `enc1M + c·2^nL`. -/
def enc1MC (N nL kL dB fB c : ℕ) : XIR :=
  .seq (mcpIR (2 ^ kL) (fB + c) 3 (enc1M nL kL dB + c * 2 ^ nL))
    (.seq (zeroIR (2 ^ nL - 2 ^ kL) (enc1M nL kL dB + c * 2 ^ nL + 2 ^ kL))
      (.seq (.blk [.const rA0 (toWord (enc1M nL kL dB + c * 2 ^ nL))]) (fwdNIR N nL dB)))

/-- The three coordinates. -/
def enc1MIR (N nL kL dB fB : ℕ) : XIR :=
  .seq (enc1MC N nL kL dB fB 0) (.seq (enc1MC N nL kL dB fB 1) (enc1MC N nL kL dB fB 2))

/-- One transposed row `v` (`tr1Row` at `2^kL`). -/
def tr1RowM (kL ob oB : ℕ) : XIR :=
  .seq (.blk [.const yK (toWord ob), .op .add ySr yL yK, .const yK 48, .op .mul yDs yL yK,
      .const yK (toWord oB), .op .add yDs yDs yK, .const yStr (toWord (2 ^ kL))])
    (.seq (mcpLoop 48) (.blk [.op .add yL yL cOne]))

/-- **The transpose** of the `48 × 2^kL` lanes at `ob` into `2^kL` rows of 48 words at `oB`. -/
def tr1MIR (kL ob oB : ℕ) : XIR :=
  .seq (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) (.loopK yC2 yN2 (toWord (2 ^ kL)) (tr1RowM kL ob oB))

/-- **The decoding proper** (on success): interpolation of the 48 lanes, the inverse NTTs, the transpose. -/
def dec1MTail (N nL kL dB wB oB : ℕ) : XIR :=
  .seq (baryIR (2 ^ kL) 48 (ag1M kL dB) (wb1M dB) (eb1M kL dB) wB 48 (ob1M nL kL dB))
    (.seq (bflyAllM N kL 48 dB (ob1M nL kL dB)) (tr1MIR kL (ob1M nL kL dB) oB))

/-- **The level-≥1 decoder program** (`decode1G N nL kL`). -/
def dec1MPIR (N nL kL dB wB aB fB oB : ℕ) : XIR :=
  .seq (wtabNIR N dB) (.seq (eqtIR 4 aB (q1M dB)) (.seq (enc1MIR N nL kL dB fB)
    (.seq (agree1NIR (2 ^ nL) wB (q1M dB) (enc1M nL kL dB) (ag1M kL dB)) (.seq (okMIR kL (ok1M dB))
      (.ite rOk (dec1MTail N nL kL dB wB oB) (.blk []))))))

theorem tr1MIR_9 (ob oB : ℕ) : tr1MIR 9 ob oB = tr1IR ob oB := rfl
theorem bflyAllM_lvm1 (dB : ℕ) : bflyAllM 15 9 48 (tbB dB) (ob1B dB) = bfly1All dB := rfl

/-! ## M′'s instances -/

/-- M′ level 2 (`decodeMP2 = decode1G 19 13 9`). -/
def decMP2IR (dB wB aB fB oB : ℕ) : XIR := dec1MPIR 19 13 9 dB wB aB fB oB
/-- M′ level 1 (`decodeMP1 = decode1G 19 16 13`). -/
def decMP1IR (dB wB aB fB oB : ℕ) : XIR := dec1MPIR 19 16 13 dB wB aB fB oB
/-- M′ level 0, lanes `40 … 47` (`decodeMP0 = decodeG0 19 19 17 40 8`). -/
def decMP0IRW (dB wB aB fB : ℕ) : XIR := decMP0IR 19 19 17 40 8 dB wB aB fB

/-! ## Well formed, no tape loop, no output -/

theorem wf_agreeNIR (n wB qB eB agB : ℕ) : WF (agreeNIR n wB qB eB agB) := by
  simp +decide [agreeNIR, posNBody, foldIR, laneBody, macC, testNIR, appendIR, mulKC, redC, WF,
    Writes, Prim.dst, gQ, gPw, gPe, gA0, gA1, gA2, gV, gE, gT, gX, gZ, gZ2, gCnt, gK, gC1, gN1,
    gC2, gN2, cTmp, regs]

theorem noLoopT_agreeNIR (n wB qB eB agB : ℕ) : NoLoopT (agreeNIR n wB qB eB agB) := by
  simp [agreeNIR, posNBody, foldIR, laneBody, macC, testNIR, appendIR, NoLoopT]

theorem outs_agreeNIR (n wB qB eB agB t : ℕ) : outs (agreeNIR n wB qB eB agB) t = 0 := by
  simp [agreeNIR, posNBody, foldIR, laneBody, macC, testNIR, appendIR, outs]

theorem noLoopT_agree1NIR (n wB qB eB agB : ℕ) : NoLoopT (agree1NIR n wB qB eB agB) := by
  simp [agree1NIR, pos1NBody, fold1IR, lane1Body, eqtLdE, eqtLd1, test1NIR, appendIR, mulE, NoLoopT]

theorem outs_agree1NIR (n wB qB eB agB t : ℕ) : outs (agree1NIR n wB qB eB agB) t = 0 := by
  simp [agree1NIR, pos1NBody, fold1IR, lane1Body, eqtLdE, eqtLd1, test1NIR, appendIR, mulE, outs]

theorem noLoopT_decMP0IR (N nL kL lo C dB wB aB fB : ℕ) : NoLoopT (decMP0IR N nL kL lo C dB wB aB fB) := by
  simp only [decMP0IR, encMIR, encMC, okMIR, decMP0Tail, bflyAllM, bflyRowM, rowsMIR, msgRowM, NoLoopT,
    noLoopT_wtabNIR, noLoopT_eqtIR, noLoopT_mcpIR, noLoopT_zeroIR, noLoopT_fwdNIR, noLoopT_agreeNIR,
    noLoopT_baryIR, noLoopT_bflyNIR, and_self]
  simp [mcpLoop, mcpBody, NoLoopT]

theorem outs_decMP0IR (N nL kL lo C dB wB aB fB t : ℕ) : outs (decMP0IR N nL kL lo C dB wB aB fB) t = 0 := by
  simp only [decMP0IR, encMIR, encMC, okMIR, decMP0Tail, bflyAllM, bflyRowM, rowsMIR, msgRowM, outs,
    outs_wtabNIR, outs_eqtIR, outs_mcpIR, outs_zeroIR, outs_fwdNIR, outs_agreeNIR, outs_baryIR,
    outs_bflyNIR]
  simp [mcpLoop, mcpBody, outs]

theorem noLoopT_dec1MPIR (N nL kL dB wB aB fB oB : ℕ) : NoLoopT (dec1MPIR N nL kL dB wB aB fB oB) := by
  simp only [dec1MPIR, enc1MIR, enc1MC, okMIR, dec1MTail, bflyAllM, bflyRowM, tr1MIR, tr1RowM, NoLoopT,
    noLoopT_wtabNIR, noLoopT_eqtIR, noLoopT_mcpIR, noLoopT_zeroIR, noLoopT_fwdNIR, noLoopT_agree1NIR,
    noLoopT_baryIR, noLoopT_bflyNIR, and_self]
  simp [mcpLoop, mcpBody, NoLoopT]

theorem outs_dec1MPIR (N nL kL dB wB aB fB oB t : ℕ) : outs (dec1MPIR N nL kL dB wB aB fB oB) t = 0 := by
  simp only [dec1MPIR, enc1MIR, enc1MC, okMIR, dec1MTail, bflyAllM, bflyRowM, tr1MIR, tr1RowM, outs,
    outs_wtabNIR, outs_eqtIR, outs_mcpIR, outs_zeroIR, outs_fwdNIR, outs_agree1NIR, outs_baryIR,
    outs_bflyNIR]
  simp [mcpLoop, mcpBody, outs]

theorem wf_agree1NIR (n wB qB eB agB : ℕ) : WF (agree1NIR n wB qB eB agB) := by
  simp +decide [agree1NIR, pos1NBody, fold1IR, lane1Body, eqtLdE, eqtLd1, mulE, mulEC, redC, test1NIR,
    appendIR, WF, Writes, Prim.dst, gQ, gPw, gPe, h1A, h1S, h1W, h1T, gE, gX, gZ, gZ2, gCnt, gK,
    gC1, gN1, gC2, gN2, cOne]

theorem bflyNIR_nw_hi (N ℓ tb : ℕ) {r : ℕ} (hr : 187 ≤ r) : ¬ Writes (bflyNIR N ℓ tb) r := by
  intro hw
  simp only [bflyNIR, lvlNStep, levelNIR, pairNBody, pairPs, alphaNIR, alphaBody, arithIR, addK, mulK,
    mulKC, redC, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, List.cons_append,
    List.nil_append, exists_eq_or_imp, exists_eq_left, or_false, false_or] at hw
  simp only [rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI,
    rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp] at hw
  omega

theorem wf_rowsMIR (kL C oB mB : ℕ) : WF (rowsMIR kL C oB mB) := by
  simp +decide [rowsMIR, msgRowM, mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yStr, yV, yC,
    yN, yL, yK, yC2, yN2, cTmp, regs]

theorem wf_tr1MIR (kL ob oB : ℕ) : WF (tr1MIR kL ob oB) := by
  simp +decide [tr1MIR, tr1RowM, mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yStr, yV, yC,
    yN, yL, yK, yC2, yN2, cTmp, regs]

/-- **The level-0 decoder is well formed.** -/
theorem wf_decMP0IR (N nL kL lo C dB wB aB fB : ℕ) : WF (decMP0IR N nL kL lo C dB wB aB fB) := by
  have h1 := wf_wtabNIR N (tbM dB)
  have h2 := wf_eqtIR 6 aB (qM dB)
  have h3 := fun c => wf_mcpIR (2 ^ kL) (fB + c) 3 (encM nL kL dB + c * 2 ^ nL)
  have h4 := fun c => wf_zeroIR (2 ^ nL - 2 ^ kL) (encM nL kL dB + c * 2 ^ nL + 2 ^ kL)
  have h5 := wf_fwdNIR N nL (tbM dB)
  have h6 := wf_agreeNIR (2 ^ nL) wB (qM dB) (encM nL kL dB) (agM kL dB)
  have h7 := wf_baryIR (2 ^ kL) C (agM kL dB) (wbM dB) (ebM kL dB) (wB + (64 - lo - C)) 64 (oM nL kL dB)
  have h8 := wf_bflyNIR N kL (tbM dB)
  have h9 := wf_rowsMIR kL C (oM nL kL dB) (mM nL kL C dB)
  have n8 := bflyNIR_nw_hi N kL (tbM dB) (r := zC) (by decide)
  simp only [decMP0IR, encMIR, encMC, okMIR, decMP0Tail, bflyAllM, bflyRowM, WF, Writes, Prim.dst, h1, h2,
    h3, h4, h5, h6, h7, h8, h9, n8, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    exists_eq_or_imp, exists_eq_left, or_false, false_or, true_and, and_true]
  simp +decide [rA0, zK, rOk, zT, zN, zC, cTmp, regs]

/-- **The level-≥1 decoder is well formed.** -/
theorem wf_dec1MPIR (N nL kL dB wB aB fB oB : ℕ) : WF (dec1MPIR N nL kL dB wB aB fB oB) := by
  have h1 := wf_wtabNIR N dB
  have h2 := wf_eqtIR 4 aB (q1M dB)
  have h3 := fun c => wf_mcpIR (2 ^ kL) (fB + c) 3 (enc1M nL kL dB + c * 2 ^ nL)
  have h4 := fun c => wf_zeroIR (2 ^ nL - 2 ^ kL) (enc1M nL kL dB + c * 2 ^ nL + 2 ^ kL)
  have h5 := wf_fwdNIR N nL dB
  have h6 := wf_agree1NIR (2 ^ nL) wB (q1M dB) (enc1M nL kL dB) (ag1M kL dB)
  have h7 := wf_baryIR (2 ^ kL) 48 (ag1M kL dB) (wb1M dB) (eb1M kL dB) wB 48 (ob1M nL kL dB)
  have h8 := wf_bflyNIR N kL dB
  have h9 := wf_tr1MIR kL (ob1M nL kL dB) oB
  have n8 := bflyNIR_nw_hi N kL dB (r := zC) (by decide)
  simp only [dec1MPIR, enc1MIR, enc1MC, okMIR, dec1MTail, bflyAllM, bflyRowM, WF, Writes, Prim.dst, h1,
    h2, h3, h4, h5, h6, h7, h8, h9, n8, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    exists_eq_or_imp, exists_eq_left, or_false, false_or, true_and, and_true]
  simp +decide [rA0, zK, rOk, zT, zN, zC, cTmp, regs]

end Lvm.X
