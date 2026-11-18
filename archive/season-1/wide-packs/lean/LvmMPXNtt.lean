-- New for lvm2 roll 11 (M′, R11-X): the additive NTT programs of `LvmXNtt` generic in the basis table's
-- dimension `N` (the shipped ones are `N = nLog = 15`: `alphaNIR_15`, `bflyNIR_15`, `fwdNIR_15`, `wtabNIR_15`,
-- all `rfl`). Programs and costs adapted from `LvmXNtt.lean` (`alphaIR`, `pairBody`, `levelIR`, `lvlStep`,
-- `bflyIR`, `row0IR`, `rowBody`, `rowIR`, `wtabIR`, `fpairBody`, `flevelIR`, `fPre`, `fStep`, `fwdIR`,
-- `cost_*`, `wf_*`), with the literal `15` (bits of `wAt`, table row stride, rows `1 … 14`) replaced by `N`.
import LvmXNtt

/-!
# The additive NTTs at any table dimension `N`

M′ decodes `C_main` with `coeffsAt ptK 19` (`nLogMP`): level 0's codeword has `2^19` positions, so the forward
NTT runs at `ℓ = 19` and needs the basis table `wRow ptK 19 v`, `v < 19` (`19²` words). The programs are
`LvmXNtt`'s with the table's dimension a parameter:

* `wtabNIR N tb`: rows `0 … N − 1` of `N` entries at `tb + N v + i`;
* `alphaNIR N`: `wAt ptK N l base` over the bits `i < N`;
* `bflyNIR N ℓ tb`, `fwdNIR N ℓ tb`: the inverse and forward NTTs, table row stride `N`.

Costs (exact): `alphaNIR` `16 + 20 N`; a butterfly `64 + 20 N`; `bflyNIR N ℓ` `14 + ℓ ((67 + 20 N) 2^(ℓ−1) +
23)`; `fwdNIR N ℓ` `14 + ℓ ((67 + 20 N) 2^(ℓ−1) + 27)`; `wtabNIR N` `29 + 13 N + (N − 1)(1077 + 45 N)`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

/-! ## The programs -/

/-- **`α`** over the `N` bits of the block at `rBs`, from the table row at `rTr` (`alphaIR` at `N`). -/
def alphaNIR (N : ℕ) : XIR :=
  .seq (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)])
    (.loopK rC2 rN2 (toWord N) alphaBody)

/-- **One butterfly** (`pairBody` at `N`). -/
def pairNBody (N : ℕ) : XIR :=
  .seq (.blk pairPs) (.seq (alphaNIR N) (.seq arithIR (.seq (.store rAL fN)
    (.seq (.store rAH fH) (.blk [.op .add rQ rQ cOne])))))

/-- **A level** (`levelIR` at `N`). -/
def levelNIR (N ℓ : ℕ) : XIR :=
  .seq (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))])
    (.loopK rC1 rN1 (toWord (2 ^ (ℓ - 1))) (pairNBody N))

/-- A level, then the next level and table row (stride `N`). -/
def lvlNStep (N ℓ : ℕ) : XIR :=
  .seq (levelNIR N ℓ) (.blk [.op .add rLv rLv cOne, .const uT1 (toWord N), .op .add rTr rTr uT1])

/-- **The inverse NTT** at table dimension `N`: levels `0 … ℓ − 1` on the row at `rA0`. -/
def bflyNIR (N ℓ tb : ℕ) : XIR :=
  .seq (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
    (.loopK rC3 rN3 (toWord ℓ) (lvlNStep N ℓ))

/-- Row `0` of the table (`N` entries). -/
def row0NIR (N : ℕ) : XIR :=
  .seq (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) (.loopK rC2 rN2 (toWord N) row0Body)

/-- Row `v + 1`, one entry (stored `N` cells on). -/
def rowNBody (N : ℕ) : XIR :=
  .seq (.load fU rTa) (.seq (.blk [.op .xor fW fU cOne])
    (.seq (mulK fH fU fW) (.seq (mulK fN fH fAl) (.seq (.blk [.const uT1 (toWord N), .op .add rAH rTa uT1])
      (.seq (.store rAH fN) (.blk [.op .add rTa rTa cOne]))))))

/-- Row `v + 1` from row `v` (`rowIR` at `N`). -/
def rowNIR (N : ℕ) : XIR :=
  .seq (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1])
    (.seq (.load fU rTa) (.seq (.blk [.op .xor fW fU cOne])
      (.seq (mulK fH fU fW) (.seq (invK fAl fH) (.seq (.blk [.op .or rTa rTr rTr, .const rN2 (toWord N)])
        (.seq (.loopK rC2 rN2 (toWord N) (rowNBody N))
          (.blk [.op .add rLv rLv cOne, .const uT1 (toWord N), .op .add rTr rTr uT1])))))))

/-- **The basis table** of dimension `N` at `tb`: row `0`, then rows `1 … N − 1`. -/
def wtabNIR (N tb : ℕ) : XIR :=
  .seq (.blk [.const rTr (toWord tb)]) (.seq (row0NIR N) (.seq (.blk [.const rLv 0, .const rN3 (toWord (N - 1))])
    (.loopK rC3 rN3 (toWord (N - 1)) (rowNIR N))))

/-- **One forward butterfly** (`fpairBody` at `N`). -/
def fpairNBody (N : ℕ) : XIR :=
  .seq (.blk pairPs) (.seq (alphaNIR N) (.seq farithIR (.seq (.store rAL fN)
    (.seq (.store rAH fH) (.blk [.op .add rQ rQ cOne])))))

/-- **A forward level** (`flevelIR` at `N`). -/
def flevelNIR (N ℓ : ℕ) : XIR :=
  .seq (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))])
    (.loopK rC1 rN1 (toWord (2 ^ (ℓ - 1))) (fpairNBody N))

/-- The level's registers: `rLv := rKf − 1`, `rTr := tb + N rLv`. -/
def fPreN (N : ℕ) : List Prim :=
  [.op .sub rLv rKf cOne, .const uT1 (toWord N), .op .mul rTr rLv uT1, .op .add rTr rTr rTbf]

/-- One forward step. -/
def fStepN (N ℓ : ℕ) : XIR := .seq (.blk (fPreN N)) (.seq (flevelNIR N ℓ) (.blk [.op .sub rKf rKf cOne]))

/-- **The forward NTT** at table dimension `N`: levels `ℓ − 1 … 0` on the row at `rA0`. -/
def fwdNIR (N ℓ tb : ℕ) : XIR :=
  .seq (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)])
    (.loopK rC3 rN3 (toWord ℓ) (fStepN N ℓ))

/-! ## The shipped programs are the instances at `N = 15` -/

theorem alphaNIR_15 : alphaNIR 15 = alphaIR := rfl
theorem bflyNIR_15 (ℓ tb : ℕ) : bflyNIR 15 ℓ tb = bflyIR ℓ tb := rfl
theorem fwdNIR_15 (ℓ tb : ℕ) : fwdNIR 15 ℓ tb = fwdIR ℓ tb := rfl
theorem wtabNIR_15 (tb : ℕ) : wtabNIR 15 tb = wtabIR tb := rfl

/-! ## Costs -/

theorem cost_alphaNIR (N t : ℕ) (hN : N < 2 ^ 64) : cost (alphaNIR N) t = 16 + 20 * N := by
  simp only [alphaNIR, alphaBody, cost, blkSteps, List.length_cons, List.length_nil, toNat_toWord hN]
  norm_num; ring

theorem cost_pairNBody (N t : ℕ) (hN : N < 2 ^ 64) : cost (pairNBody N) t = 64 + 20 * N := by
  simp only [pairNBody, pairPs, arithIR, cost, cost_alphaNIR N t hN, cost_addK, cost_mulK, blkSteps,
    List.length_cons, List.length_nil]
  norm_num; ring

theorem cost_fpairNBody (N t : ℕ) (hN : N < 2 ^ 64) : cost (fpairNBody N) t = 64 + 20 * N := by
  simp only [fpairNBody, pairPs, farithIR, cost, cost_alphaNIR N t hN, cost_addK, cost_mulK, blkSteps,
    List.length_cons, List.length_nil]
  norm_num; ring

/-- **The inverse NTT's cost** at table dimension `N`. -/
theorem cost_bflyNIR (N ℓ tb t : ℕ) (hN : N < 2 ^ 64) (hℓ : 2 ^ (ℓ - 1) < 2 ^ 64) (hℓ' : ℓ < 2 ^ 64) :
    cost (bflyNIR N ℓ tb) t = 14 + ℓ * ((67 + 20 * N) * 2 ^ (ℓ - 1) + 23) := by
  simp only [bflyNIR, lvlNStep, levelNIR, cost, cost_pairNBody N t hN, blkSteps, List.length_cons,
    List.length_nil, toNat_toWord hℓ, toNat_toWord hℓ']
  norm_num; ring

/-- **The forward NTT's cost** at table dimension `N`. -/
theorem cost_fwdNIR (N ℓ tb t : ℕ) (hN : N < 2 ^ 64) (hℓ : 2 ^ (ℓ - 1) < 2 ^ 64) (hℓ' : ℓ < 2 ^ 64) :
    cost (fwdNIR N ℓ tb) t = 14 + ℓ * ((67 + 20 * N) * 2 ^ (ℓ - 1) + 27) := by
  simp only [fwdNIR, fStepN, fPreN, flevelNIR, cost, cost_fpairNBody N t hN, blkSteps, List.length_cons,
    List.length_nil, toNat_toWord hℓ, toNat_toWord hℓ']
  norm_num; ring

/-- **The basis table's cost** at dimension `N`. -/
theorem cost_wtabNIR (N tb t : ℕ) (hN : N < 2 ^ 64) :
    cost (wtabNIR N tb) t = 29 + 13 * N + (N - 1) * (1077 + 45 * N) := by
  have h1 : N - 1 < 2 ^ 64 := lt_of_le_of_lt (Nat.sub_le N 1) hN
  simp only [wtabNIR, row0NIR, row0Body, rowNIR, rowNBody, cost, cost_mulK, cost_invK, blkSteps,
    List.length_cons, List.length_nil, toNat_toWord hN, toNat_toWord h1]
  norm_num; ring

theorem cost_wtabNIR_19 (tb t : ℕ) : cost (wtabNIR 19 tb) t = 35052 := by
  rw [cost_wtabNIR 19 tb t (by norm_num)]

/-! ## Well formed, no tape loop, no output -/

theorem wf_alphaNIR (N : ℕ) : WF (alphaNIR N) := by
  simp +decide [alphaNIR, alphaBody, WF, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rN2, rC2, cTmp]

theorem wf_bflyNIR (N ℓ tb : ℕ) : WF (bflyNIR N ℓ tb) := by
  simp +decide only [bflyNIR, lvlNStep, levelNIR, pairNBody, pairPs, arithIR, alphaNIR, alphaBody,
    addK, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAH, rTa, rBit, uI, rTr, rC1,
    rN1, rC2, rN2, rC3, rN3, fAl, fU, fW, fH, fT, fN, fG, cTmp, regs, mulK_wf_iff,
    mulK_writes_iff, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp,
    forall_eq, exists_eq_left, or_false, and_true]

theorem wf_fwdNIR (N ℓ tb : ℕ) : WF (fwdNIR N ℓ tb) := by
  simp +decide only [fwdNIR, fStepN, fPreN, flevelNIR, fpairNBody, pairPs, farithIR, alphaNIR, alphaBody,
    addK, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAH, rTa, rBit, uI, rTr, rC1,
    rN1, rC2, rN2, rC3, rN3, fAl, fU, fW, fH, fT, fN, fG, rKf, rTbf, cTmp, regs, mulK_wf_iff,
    mulK_writes_iff, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp,
    forall_eq, exists_eq_left, or_false, and_true]

theorem wf_rowNIR (N : ℕ) : WF (rowNIR N) := by
  have m3 := wf_invK fAl fH (by decide)
  have n1 : ¬ Writes (mulK fH fU fW) rC2 := by rw [mulK_writes_iff (by decide) (by decide)]; simp
  have n2 : ¬ Writes (mulK fN fH fAl) rC2 := by rw [mulK_writes_iff (by decide) (by decide)]; simp
  simp only [rowNIR, rowNBody, WF, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, m3, n1, n2,
    mulK_wf_iff (show 4 ≤ fH by decide), mulK_wf_iff (show 4 ≤ fN by decide)]
  simp [rLv, uT1, rAH, rTa, rTr, rC2, rN2, fU, fW, cTmp, regs]

theorem wf_wtabNIR (N tb : ℕ) : WF (wtabNIR N tb) := by
  have n3 : ¬ Writes (mulK fH fU fW) rC3 := by rw [mulK_writes_iff (by decide) (by decide)]; simp
  have n4 : ¬ Writes (invK fAl fH) rC3 := by rw [invK_writes_iff (by decide) (by decide)]; simp
  have n5 : ¬ Writes (mulK fN fH fAl) rC3 := by rw [mulK_writes_iff (by decide) (by decide)]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, wf_rowNIR N⟩
  · simp [WF, Prim.dst, rTr]
  · simp +decide only [row0NIR, row0Body, WF, Writes, Prim.dst, uI, rTa, rN2, rC2, fG, cTmp, regs,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq,
      exists_eq_left, or_false, and_true]
  · simp [WF, Prim.dst, rLv, rN3]
  · decide
  · decide
  · simp only [rowNIR, rowNBody, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, n3, n4, n5]
    simp [rLv, uT1, rAH, rTa, rTr, rC2, rN2, rC3, fU, fW, cTmp]

theorem noLoopT_bflyNIR (N ℓ tb : ℕ) : NoLoopT (bflyNIR N ℓ tb) := by
  simp [bflyNIR, lvlNStep, levelNIR, pairNBody, arithIR, alphaNIR, alphaBody, addK, mulK, NoLoopT]

theorem noLoopT_fwdNIR (N ℓ tb : ℕ) : NoLoopT (fwdNIR N ℓ tb) := by
  simp [fwdNIR, fStepN, flevelNIR, fpairNBody, farithIR, alphaNIR, alphaBody, addK, mulK, NoLoopT]

theorem noLoopT_wtabNIR (N tb : ℕ) : NoLoopT (wtabNIR N tb) := by
  simp [wtabNIR, row0NIR, row0Body, rowNIR, rowNBody, mulK, invK, NoLoopT]

theorem outs_bflyNIR (N ℓ tb t : ℕ) : outs (bflyNIR N ℓ tb) t = 0 := by
  simp [bflyNIR, lvlNStep, levelNIR, pairNBody, arithIR, alphaNIR, alphaBody, addK, mulK, outs]

theorem outs_fwdNIR (N ℓ tb t : ℕ) : outs (fwdNIR N ℓ tb) t = 0 := by
  simp [fwdNIR, fStepN, flevelNIR, fpairNBody, farithIR, alphaNIR, alphaBody, addK, mulK, outs]

theorem outs_wtabNIR (N tb t : ℕ) : outs (wtabNIR N tb) t = 0 := by
  simp [wtabNIR, row0NIR, row0Body, rowNIR, rowNBody, mulK, invK, outs]

end Lvm.X
