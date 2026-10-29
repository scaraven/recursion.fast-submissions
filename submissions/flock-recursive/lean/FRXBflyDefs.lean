-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, §6.5 `coeffs_spec`; stage S-H2, track L-ext).
import FRXRead
import FRXDecodeB

/-!
# The butterflies on the machine: the programs

BLUEPRINT §6.2 step 4 ("novel coefficients"), in the iterative form of `FRXDecodeB.bflyRun`.
An `F` element sits in two consecutive heap cells (`rdF`, `c₀` first); a row of `2^ℓ` elements
from cell `A` holds element `i` at `A + 2i`.

* **The basis table** (`wtabIR tb`): the rows `wRow D 20 v`, `v < 20`, at `tb + 40 v + 2 i`.
  Row `0` is `D(2^i)`, the words `(2^i, 0)`; row `v + 1` maps each entry `a` of row `v` to
  `a (a + 1) · (b (b + 1))⁻¹`, `b` entry `v + 1` of row `v` (LCH, `FRRSEval.wRow`): one `invF`
  per row.
* **`α`** (`alphaIR`): `wAt D 20 l base`, the sum over the set bits `i < 20` of `base` of the
  table entry `(l, i)`, branch-free (`mask = 0 − bit`).
* **One butterfly** (`pairBody`): pair `q < 2^(ℓ−1)` of level `l` (`P = 2^l`) has the positions
  `lo = ⌊q/P⌋·2P + q mod P` and `hi = lo + P`; with `u, w` their values,
  `lo := u + α (w + u)`, `hi := w + u` (characteristic 2: `bflyLevel`'s `u − α (w − u)`, `w − u`).
* **A level** (`levelIR ℓ`): the `2^(ℓ−1)` pairs; **the butterflies** (`bflyIR ℓ tb`): levels
  `0 … ℓ − 1` on the row at `rA0`.

Registers `140 … 177`.
-/

namespace FR.X

open RecursionFast

/-! ## Registers -/

/-- The pair index `q`. -/ def rQ : ℕ := 140
/-- The level `l`. -/ def rLv : ℕ := 141
/-- `2^l`. -/ def rP2 : ℕ := 142
/-- The block's base position. -/ def rBs : ℕ := 143
/-- `q mod 2^l`. -/ def uX : ℕ := 144
/-- Scratch. -/ def uT1 : ℕ := 145
/-- Scratch. -/ def uT2 : ℕ := 146
/-- The address of `lo`. -/ def rAL : ℕ := 147
/-- Its second word. -/ def rAL1 : ℕ := 148
/-- The address of `hi`. -/ def rAH : ℕ := 149
/-- Its second word. -/ def rAH1 : ℕ := 150
/-- A table address. -/ def rTa : ℕ := 151
/-- Its second word. -/ def rTa1 : ℕ := 152
/-- The bit mask. -/ def rBit : ℕ := 153
/-- The bit index. -/ def uI : ℕ := 154
/-- The row's first cell `A`. -/ def rA0 : ℕ := 155
/-- The table row's first cell. -/ def rTr : ℕ := 156
/-- Counter of the pair loop. -/ def rC1 : ℕ := 157
/-- Count of the pair loop. -/ def rN1 : ℕ := 158
/-- Counter of the bit loops. -/ def rC2 : ℕ := 159
/-- Count of the bit loops. -/ def rN2 : ℕ := 160
/-- Counter of the level loops. -/ def rC3 : ℕ := 161
/-- Count of the level loops. -/ def rN3 : ℕ := 162
/-- `α` (an `F` pair). -/ def fAl : ℕ := 164
/-- `u`. -/ def fU : ℕ := 166
/-- `w`. -/ def fW : ℕ := 168
/-- `w + u`. -/ def fH : ℕ := 170
/-- `α (w + u)`. -/ def fT : ℕ := 172
/-- The new `lo`. -/ def fN : ℕ := 174
/-- A table entry. -/ def fG : ℕ := 176

/-! ## Heap `F` elements -/

/-- `d, d + 1 :=` the heap element at `M[p]` (`p1 := p + 1`). -/
def ldF (d p p1 : ℕ) : XIR := .seq (.load d p) (.seq (.blk [.op .add p1 p cOne]) (.load (d + 1) p1))

/-- The heap element at `M[p]` `:=` registers `v, v + 1` (`p1 := p + 1`). -/
def stF (p p1 v : ℕ) : XIR := .seq (.blk [.op .add p1 p cOne]) (.seq (.store p v) (.store p1 (v + 1)))

/-! ## `α = wAt D 20 l base` -/

/-- One bit `i`: `α += [bit_i(base)] · T[l][i]`; `rTa += 2`, `i += 1`. -/
def alphaBody : XIR :=
  .seq (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0, .op .sub rBit uT1 rBit])
    (.seq (ldF fG rTa rTa1)
      (.blk [.op .and fG fG rBit, .op .and (fG + 1) (fG + 1) rBit, .op .xor fAl fAl fG,
        .op .xor (fAl + 1) (fAl + 1) (fG + 1), .const uT1 2, .op .add rTa rTa uT1,
        .op .add uI uI cOne]))

/-- **`α`** for the block at `rBs`, from the table row at `rTr`. -/
def alphaIR : XIR :=
  .seq (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 20])
    (.loopK rC2 rN2 20 alphaBody)

/-! ## One butterfly, a level, the iteration -/

/-- The pair's addresses: `rBs := ⌊q/P⌋ · 2P`, `rAL := A + 2 lo`, `rAH := A + 2 hi`. -/
def pairPs : List Prim :=
  [.op .divu uT1 rQ rP2, .op .remu uX rQ rP2, .op .add uT2 rP2 rP2, .op .mul rBs uT1 uT2,
   .op .add uT1 rBs uX, .op .add uT1 uT1 uT1, .op .add rAL rA0 uT1, .op .add rAH rAL uT2]

/-- The butterfly's arithmetic: `u, w` from the heap, `fH := w + u`, `fN := u + α fH`. -/
def arithIR : XIR :=
  .seq (ldF fU rAL rAL1) (.seq (ldF fW rAH rAH1) (.seq (addF fH fW fU) (.seq (mulF fT fAl fH)
    (addF fN fU fT))))

/-- **One butterfly**: pair `q` of the level in `rLv`. -/
def pairBody : XIR :=
  .seq (.blk pairPs) (.seq alphaIR (.seq arithIR (.seq (stF rAL rAL1 fN)
    (.seq (stF rAH rAH1 fH) (.blk [.op .add rQ rQ cOne])))))

/-- **A level**: the `2^(ℓ−1)` pairs, `P = 2^l`. -/
def levelIR (ℓ : ℕ) : XIR :=
  .seq (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))])
    (.loopK rC1 rN1 (toWord (2 ^ (ℓ - 1))) pairBody)

/-- A level, then the next level and table row. -/
def lvlStep (ℓ : ℕ) : XIR :=
  .seq (levelIR ℓ) (.blk [.op .add rLv rLv cOne, .const uT1 40, .op .add rTr rTr uT1])

/-- **The butterflies**: levels `0 … ℓ − 1` on the row at `rA0`, the table at `tb`. -/
def bflyIR (ℓ tb : ℕ) : XIR :=
  .seq (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
    (.loopK rC3 rN3 (toWord ℓ) (lvlStep ℓ))

/-! ## The basis table -/

/-- Row `0`, entry `i`: the words `(2^i, 0)` (`D(2^i)`). -/
def row0Body : XIR :=
  .seq (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) (.seq (stF rTa rTa1 fG)
    (.blk [.const uT1 2, .op .add rTa rTa uT1, .op .add uI uI cOne]))

/-- Row `0` at `rTr`. -/
def row0IR : XIR :=
  .seq (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) (.loopK rC2 rN2 20 row0Body)

/-- Row `v + 1`, entry at `rTa` (row `v`): `a (a + 1) · fAl`, stored 40 cells on. -/
def rowBody : XIR :=
  .seq (ldF fU rTa rTa1) (.seq (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)])
    (.seq (mulF fH fU fW) (.seq (mulF fN fH fAl) (.seq (.blk [.const uT1 40, .op .add rAH rTa uT1])
      (.seq (stF rAH rAH1 fN) (.blk [.const uT1 2, .op .add rTa rTa uT1]))))))

/-- Row `v + 1` from row `v` (at `rTr`, `v` in `rLv`): `fAl := (b (b + 1))⁻¹`, `b` entry `v + 1`;
then the 20 entries; `rLv += 1`, `rTr += 40`. -/
def rowIR : XIR :=
  .seq (.blk [.op .add uT1 rLv cOne, .op .add uT1 uT1 uT1, .op .add rTa rTr uT1])
    (.seq (ldF fU rTa rTa1) (.seq (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)])
      (.seq (mulF fH fU fW) (.seq (invF fAl fH) (.seq (.blk [.op .or rTa rTr rTr, .const rN2 20])
        (.seq (.loopK rC2 rN2 20 rowBody)
          (.blk [.op .add rLv rLv cOne, .const uT1 40, .op .add rTr rTr uT1])))))))

/-- **The basis table** at `tb`: row `0`, then rows `1 … 19`. -/
def wtabIR (tb : ℕ) : XIR :=
  .seq (.blk [.const rTr (toWord tb)]) (.seq row0IR (.seq (.blk [.const rLv 0, .const rN3 19])
    (.loopK rC3 rN3 19 rowIR)))

/-! ## Well formed, no tape loop, no output, cost -/

theorem wf_alphaIR : WF alphaIR := by
  simp +decide only [alphaIR, alphaBody, ldF, WF, Writes, Prim.dst, rBit, uT1, rTa, rTa1, fG, fAl,
    uI, rN2, rC2, cTmp, regs, or_false, and_true]

theorem nw_mulF {d a b c : ℕ} (hc : 15 ≤ c) (h0 : c ≠ d) (h1 : c ≠ d + 1) :
    ¬ Writes (mulF d a b) c := fun ⟨p, hp, he⟩ => by
  rcases mulFC_dst' d a b p hp with h | h | h <;> omega

theorem nw_invF {d a c : ℕ} (hc : 19 ≤ c) (h0 : c ≠ d) (h1 : c ≠ d + 1) :
    ¬ Writes (invF d a) c := fun ⟨p, hp, he⟩ => by
  rcases invFC_dst' d a p hp with h | h | h <;> omega

/-- `simp` forms of `wf_mulF` and `nw_mulF`: the `WF`/`Writes` side conditions never unfold
`mulF`'s primitives (G2: elaboration time). -/
theorem mulF_wf_iff {d a b : ℕ} (hd : 4 ≤ d) : WF (mulF d a b) ↔ True :=
  iff_true_intro (wf_mulF d a b hd)

theorem mulF_writes_iff {d a b c : ℕ} (hc : 15 ≤ c) (h0 : c ≠ d) (h1 : c ≠ d + 1) :
    Writes (mulF d a b) c ↔ False := ⟨nw_mulF hc h0 h1, False.elim⟩

theorem wf_bflyIR (ℓ tb : ℕ) : WF (bflyIR ℓ tb) := by
  simp +decide only [bflyIR, lvlStep, levelIR, pairBody, pairPs, arithIR, alphaIR, alphaBody, ldF,
    stF, addF, addFC, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAL1, rAH, rAH1,
    rTa, rTa1, rBit, uI, rTr, rC1, rN1, rC2, rN2, rC3, rN3, fAl, fU, fW, fH, fT, fN, fG, cTmp, regs,
    mulF_wf_iff, mulF_writes_iff, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true]

theorem wf_wtabIR (tb : ℕ) : WF (wtabIR tb) := by
  have m1 := wf_mulF fH fU fW (by decide)
  have m2 := wf_mulF fN fH fAl (by decide)
  have m3 := wf_invF fAl fH (by decide)
  have n1 : ¬ Writes (mulF fH fU fW) rC2 := nw_mulF (by decide) (by decide) (by decide)
  have n2 : ¬ Writes (mulF fN fH fAl) rC2 := nw_mulF (by decide) (by decide) (by decide)
  have n3 : ¬ Writes (mulF fH fU fW) rC3 := nw_mulF (by decide) (by decide) (by decide)
  have n4 : ¬ Writes (invF fAl fH) rC3 := nw_invF (by decide) (by decide) (by decide)
  have n5 : ¬ Writes (mulF fN fH fAl) rC3 := nw_mulF (by decide) (by decide) (by decide)
  simp only [wtabIR, row0IR, row0Body, rowIR, rowBody, ldF, stF, WF, Writes, Prim.dst,
    List.mem_cons, List.mem_nil_iff, m1, m2, m3, n1, n2, n3, n4, n5]
  simp [rLv, uT1, rAH, rAH1, rTa, rTa1, uI, rTr, rC2, rN2, rC3, rN3, fU, fW, fG, cTmp,
    regs]

theorem noLoopT_bflyIR (ℓ tb : ℕ) : NoLoopT (bflyIR ℓ tb) := by
  simp [bflyIR, lvlStep, levelIR, pairBody, arithIR, alphaIR, alphaBody, ldF, stF, addF, mulF,
    NoLoopT]

theorem noLoopT_wtabIR (tb : ℕ) : NoLoopT (wtabIR tb) := by
  simp [wtabIR, row0IR, row0Body, rowIR, rowBody, ldF, stF, mulF, invF, NoLoopT]

theorem outs_bflyIR (ℓ tb t : ℕ) : outs (bflyIR ℓ tb) t = 0 := by
  simp [bflyIR, lvlStep, levelIR, pairBody, arithIR, alphaIR, alphaBody, ldF, stF, addF, mulF,
    outs]

theorem outs_wtabIR (tb t : ℕ) : outs (wtabIR tb) t = 0 := by
  simp [wtabIR, row0IR, row0Body, rowIR, rowBody, ldF, stF, mulF, invF, outs]

theorem cost_alphaIR (t : ℕ) : cost alphaIR t = 618 := by
  simp only [alphaIR, alphaBody, ldF, cost, blkSteps, List.length_cons, List.length_nil]
  norm_num

theorem cost_pairBody (t : ℕ) : cost pairBody t = 738 := by
  simp only [pairBody, pairPs, arithIR, ldF, stF, cost, cost_alphaIR, addF, mulF, blkSteps, len_addFC,
    len_mulFC, List.length_cons, List.length_nil]
  norm_num

/-- **The butterflies' cost**: `ℓ` levels of `2^(ℓ−1)` pairs. -/
theorem cost_bflyIR (ℓ tb t : ℕ) (hℓ : 2 ^ (ℓ - 1) < 2 ^ 64) (hℓ' : ℓ < 2 ^ 64) :
    cost (bflyIR ℓ tb) t = 14 + ℓ * (741 * 2 ^ (ℓ - 1) + 23) := by
  have a1 : (toWord (2 ^ (ℓ - 1))).toNat = 2 ^ (ℓ - 1) := toNat_toWord hℓ
  have a2 : (toWord ℓ).toNat = ℓ := toNat_toWord hℓ'
  simp only [bflyIR, lvlStep, levelIR, cost, cost_pairBody, blkSteps, List.length_cons,
    List.length_nil, a1, a2]
  norm_num
  ring

theorem cost_wtabIR (tb t : ℕ) : cost (wtabIR tb) t = 79606 := by
  have a : (19 : Word).toNat = 19 := rfl
  simp only [wtabIR, row0IR, row0Body, rowIR, rowBody, ldF, stF, mulF, invF, cost, blkSteps,
    len_mulFC, len_invFC, List.length_cons, List.length_nil, a]
  norm_num

end FR.X
