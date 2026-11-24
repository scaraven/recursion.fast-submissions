-- lvm6 X7b (X6b §4 item 1): the descent's agreement-set builder. Per round: encode the previous round's
-- decoded coefficients (every `K`-lane `q` of the folded word, column `colB + str·q`) at the `2^ℓ` points with the
-- forward NTT, compare with the folded word (a round table gives its base and row stride, as for the loaders),
-- and list the first `d + 3` agreeing positions at `sA B`. New.
import Lvm6XDescFold

/-!
# The agreement-set builder

* **`sbIR N ℓ B colB str d tS K`**: the round `r` (register 248) names, at `tS + 2r`, the folded word's base and
  row stride `occ` (= its `K`-lane count, `≤ K`); the builder builds the basis table, clears a flag row, and per
  lane `q < occ` copies column `q`'s first `d + 1` coefficients into a zero-padded row, runs `fwdNIR` and ORs
  `row[j] ⊕ word(q, j)` into flag `j`; then it lists the positions `j < 2^ℓ` with flag `0`, at most `d + 3` of them,
  at `sA B`. Scratch: the FD1 workspace `[yA, fdEnd)` (flags, row, table), which `lamIR`/`laneIR` overwrite.
* **F-X7b-1**: X6b's `SbOk` lets the builder write `S` only: no heap scratch, so no encoder (an NTT needs a row).
  **`SbOkW`** also lets it write `[sA + |S|, fdEnd B ℓ)`; **`roundX_semW`** is X6b's `roundX_semB` with `SbOkW`
  (same conclusion: the round reads `S` and the heap below `B` only).
* **`sbSpec`**: the list the builder writes (the first `d + 3` positions where every lane's encoding agrees with
  the word), `sbSpec_eq_agreeS`-ready form; structure (`wf`, `noLoopT`, `outs`, `AllBelow 248`), exact cost
  `cost_sbIR`, size `sizeIR_sbIR`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

attribute [local irreducible] entryK storeM

/-! ## The weak builder specification and the round with it -/

/-- **The agreement-set builder, with scratch**: from a state satisfying `Pre` (heap of `fdEnd B ℓ` words), it writes
`S` at `sA B`, may change `[sA B + |S|, fdEnd B ℓ)`, and keeps every other heap word, `Inv` and the output. -/
def SbOkW (I : Array Word) (sb : XIR) (B ℓ : ℕ) (S : List ℕ) (Pre : St → Prop) : Prop :=
  ∀ s : St, Pre s → Inv s.M → fdEnd B ℓ ≤ s.M.size →
    (∀ i < S.length, rd (semXIR I sb s).M (sA B + i) = toWord (S.getD i 0)) ∧
    Inv (semXIR I sb s).M ∧ (semXIR I sb s).o = s.o ∧
    ∀ x, regs ≤ x → (x < sA B ∨ fdEnd B ℓ ≤ x) → rd (semXIR I sb s).M x = rd s.M x

theorem SbOk.sbOkW {I : Array Word} {sb : XIR} {B ℓ : ℕ} {S : List ℕ} {Pre : St → Prop}
    (h : SbOk I sb B S Pre) (hS : S.length ≤ 2 ^ ℓ) : SbOkW I sb B ℓ S Pre := by
  intro s hP hM _
  obtain ⟨a1, a2, a3, a4⟩ := h s hP hM
  have eS : sA B = B + 4096 := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  exact ⟨a1, a2, a3, fun x hx hx' ↦ a4 x hx (by omega)⟩

/-- **A round of `descX6` on the machine** with a builder that uses the FD1 workspace (`SbOkW`). -/
theorem roundX_semW (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B colB str : ℕ} {r : RoundX} {S : List ℕ}
    {Pre : St → Prop} (hP : Pre s) (hsb : SbOkW I r.sb B ℓ S Pre) (hmS : S.length = r.m) (M₀ : Mem)
    (ys : ℕ → ℕ → BF64) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hm : S.length ≤ 2 ^ ℓ)
    (hSn : ∀ j ∈ S, j < 2 ^ ℓ) (hcol : fdEnd B ℓ ≤ colB) (hstr : 2 ^ ℓ ≤ str) (h64 : colB + str * r.n < 2 ^ 64)
    (hsz : colB + str * r.n ≤ s.M.size) (h0 : ∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x)
    (hld : ∀ q < r.n, LoadOkB I (r.ld q) ℓ B M₀ (ys q)) :
    (∀ q < r.n, ∀ x < 2 ^ ℓ, rdK (semXIR I (roundX N ℓ B colB str r) s).M (colB + str * q + x) =
        fd1 N ℓ S (ys q) x) ∧
      Inv (semXIR I (roundX N ℓ B colB str r) s).M ∧ (semXIR I (roundX N ℓ B colB str r) s).o = s.o ∧
      ∀ x, regs ≤ x → (x < B ∨ (fdEnd B ℓ ≤ x ∧ x < colB) ∨ colB + str * r.n ≤ x) →
        rd (semXIR I (roundX N ℓ B colB str r) s).M x = rd s.M x := by
  have eS : sA B = B + 4096 := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  obtain ⟨a1, a2, a3, a4⟩ := hsb s hP hM (by omega)
  have z1 := size_sem I r.sb s
  have h01 : ∀ x, regs ≤ x → x < B → rd (semXIR I r.sb s).M x = rd M₀ x := fun x hx hxB ↦ by
    rw [a4 x hx (Or.inl (by omega)), h0 x hx hxB]
  rw [roundX, semXIR_seq, ← hmS]
  generalize semXIR I r.sb s = s1 at a1 a2 a3 a4 z1 h01
  obtain ⟨b1, b2, b3, b4⟩ := roundIR_semB I s1 a2 r.ld M₀ ys hN hN64 hB hm hSn a1 hcol hstr h64
    (by rw [z1]; exact hsz) h01 hld
  refine ⟨b1, b2, b3.trans a3, fun x hx hx' ↦ ?_⟩
  rw [b4 x hx (by omega), a4 x hx (by omega)]

/-! ## The program -/

/-- A builder register. -/ def bT : ℕ := 190
/-- A builder register. -/ def bU : ℕ := 191
/-- The folded word's base. -/ def bBase : ℕ := 192
/-- Its row stride (= its `K`-lane count). -/ def bOcc : ℕ := 193
/-- The lane `q`. -/ def bQ : ℕ := 194
/-- The word pointer. -/ def bP : ℕ := 195
/-- The row pointer. -/ def bR : ℕ := 196
/-- The flag pointer. -/ def bF : ℕ := 197
/-- A word. -/ def bv : ℕ := 198
/-- An encoded value. -/ def be : ℕ := 199
/-- A flag. -/ def bf : ℕ := 200
/-- The listing test. -/ def bz : ℕ := 201
/-- The count test. -/ def bl : ℕ := 202
/-- The list pointer. -/ def bS : ℕ := 203
/-- The position `j`. -/ def bJ : ℕ := 204
/-- The count of listed positions. -/ def bCnt : ℕ := 205
/-- The list's length bound `d + 3`. -/ def bDm : ℕ := 206
/-- Zero. -/ def bZ0 : ℕ := 207
/-- The lane loop's counter. -/ def bC1 : ℕ := 241
/-- The inner loops' counter. -/ def bC2 : ℕ := 242
/-- The inner loops' count. -/ def bN2 : ℕ := 243

/-- The flags (`2^ℓ` words). -/ def flA (B ℓ : ℕ) : ℕ := yA B ℓ
/-- The encoded row (`2^ℓ` words). -/ def rwA (B ℓ : ℕ) : ℕ := yA B ℓ + 2 ^ ℓ
/-- The basis table (`N²` words). -/ def tbA' (B ℓ : ℕ) : ℕ := yA B ℓ + 2 * 2 ^ ℓ

/-- One position of a lane: `flag[j] |= row[j] ⊕ word(q, j)`. -/
def cmpBody : XIR :=
  .seq (sIR [.ld bv bP, .ld be bR, .op .xor bv bv be, .ld bf bF, .op .or bf bf bv])
    (.seq (.store bF bf) (sIR [.op .add bP bP bOcc, .op .add bR bR cOne, .op .add bF bF cOne]))

/-- **One lane `q`**: column `q`'s first `d + 1` coefficients, zero-padded, encoded (`fwdNIR`), compared. -/
def laneB (N ℓ B colB str d : ℕ) : XIR :=
  .seq (sIR [.cst bU (toWord str), .op .mul bT bQ bU, .cst bU (toWord colB), .op .add ySr bT bU,
      .cst yStr (toWord 1), .cst yDs (toWord (rwA B ℓ))])
    (.seq (mcpLoop (d + 1))
    (.seq (zeroIR (2 ^ ℓ - (d + 1)) (rwA B ℓ + (d + 1)))
    (.seq (.blk [.const rA0 (toWord (rwA B ℓ))])
    (.seq (fwdNIR N ℓ (tbA' B ℓ))
    (.seq (sIR [.op .add bP bBase bQ, .cst bF (toWord (flA B ℓ)), .cst bR (toWord (rwA B ℓ)),
        .cst bN2 (toWord (2 ^ ℓ))])
    (.seq (.loopK bC2 bN2 (toWord (2 ^ ℓ)) cmpBody)
      (sIR [.op .add bQ bQ cOne])))))))

/-- One position of the listing: if `flag[j] = 0` and fewer than `d + 3` are listed, `M[sA + cnt] := j`. -/
def scanBody : XIR :=
  .seq (sIR [.ld bf bF, .op .eq bz bf bZ0, .op .ltu bl bCnt bDm, .op .and bz bz bl])
    (.seq (.ite bz (.seq (.store bS bJ) (sIR [.op .add bS bS cOne, .op .add bCnt bCnt cOne])) (.blk []))
      (sIR [.op .add bF bF cOne, .op .add bJ bJ cOne]))

/-- The listing of the agreeing positions. -/
def scanIR (ℓ B d : ℕ) : XIR :=
  .seq (sIR [.cst bF (toWord (flA B ℓ)), .cst bJ (toWord 0), .cst bCnt (toWord 0), .cst bS (toWord (sA B)),
      .cst bDm (toWord (d + 3)), .cst bZ0 (toWord 0), .cst bN2 (toWord (2 ^ ℓ))])
    (.loopK bC2 bN2 (toWord (2 ^ ℓ)) scanBody)

/-- The builder's prologue: round `r`'s word (`tS + 2r`: base, row stride), `q := 0`. -/
def sbPro (tS : ℕ) : List SOp :=
  [.op .add bT xR xR, .cst bU (toWord tS), .op .add bT bT bU, .ld bBase bT, .op .add bT bT cOne, .ld bOcc bT,
    .cst bQ (toWord 0)]

/-- **The agreement-set builder** (lanes `q < occ ≤ K`). -/
def sbIR (N ℓ B colB str d tS K : ℕ) : XIR :=
  .seq (sIR (sbPro tS)) (.seq (wtabNIR N (tbA' B ℓ)) (.seq (zeroIR (2 ^ ℓ) (flA B ℓ))
    (.seq (.loopK bC1 bOcc (toWord K) (laneB N ℓ B colB str d)) (scanIR ℓ B d))))

/-! ## Structure, cost, size -/

theorem allBelow_mcpLoop (n : ℕ) : AllBelow 80 (mcpLoop n) := by
  simp +decide [mcpLoop, mcpBody, AllBelow, Prim.dst, ySr, yDs, yV, yC, yN, cTmp]

theorem allBelow_zeroIR (n dst : ℕ) : AllBelow 80 (zeroIR n dst) := by
  simp +decide [zeroIR, zeroBody, AllBelow, Prim.dst, yDs, yV, yC, yN, cTmp]

theorem allBelow_sbIR (N ℓ B colB str d tS K : ℕ) : AllBelow 248 (sbIR N ℓ B colB str d tS K) := by
  have w := allBelow_mono (show 187 ≤ 248 by decide) (allBelow_wtabNIR N (tbA' B ℓ))
  have f := allBelow_mono (show 187 ≤ 248 by decide) (allBelow_fwdNIR N ℓ (tbA' B ℓ))
  refine ⟨allBelow_sIR (by norm_num) _ (by simp +decide [sbPro, SOp.dst, bT, bU, bBase, bOcc, bQ]), w,
    allBelow_mono (by decide) (allBelow_zeroIR _ _), ⟨by decide, by decide, ?_⟩, ?_⟩
  · refine ⟨allBelow_sIR (by norm_num) _ (by simp +decide [SOp.dst, bU, bT, ySr, yStr, yDs]),
      allBelow_mono (by decide) (allBelow_mcpLoop _), allBelow_mono (by decide) (allBelow_zeroIR _ _),
      by simp +decide [AllBelow, Prim.dst, rA0], f,
      allBelow_sIR (by norm_num) _ (by simp +decide [SOp.dst, bP, bF, bR, bN2]), ⟨by decide, by decide, ?_⟩,
      allBelow_sIR (by norm_num) _ (by simp +decide [SOp.dst, bQ])⟩
    exact ⟨allBelow_sIR (by norm_num) _ (by simp +decide [SOp.dst, bv, be, bf]), by simp [AllBelow, cTmp],
      allBelow_sIR (by norm_num) _ (by simp +decide [SOp.dst, bP, bR, bF])⟩
  · refine ⟨allBelow_sIR (by norm_num) _ (by simp +decide [SOp.dst, bF, bJ, bCnt, bS, bDm, bZ0, bN2]),
      by decide, by decide, ?_⟩
    exact ⟨allBelow_sIR (by norm_num) _ (by simp +decide [SOp.dst, bf, bz, bl]),
      ⟨⟨by simp [AllBelow, cTmp], allBelow_sIR (by norm_num) _ (by simp +decide [SOp.dst, bS, bCnt])⟩,
        by simp [AllBelow]⟩, allBelow_sIR (by norm_num) _ (by simp +decide [SOp.dst, bF, bJ])⟩

theorem noLoopT_sbIR (N ℓ B colB str d tS K : ℕ) : NoLoopT (sbIR N ℓ B colB str d tS K) := by
  simp [sbIR, laneB, scanIR, scanBody, cmpBody, NoLoopT, noLoopT_sIR, mcpLoop, mcpBody, zeroIR, zeroBody,
    noLoopT_wtabNIR, noLoopT_fwdNIR]

theorem outs_sbIR (N ℓ B colB str d tS K t : ℕ) : outs (sbIR N ℓ B colB str d tS K) t = 0 := by
  simp [sbIR, laneB, scanIR, scanBody, cmpBody, outs, outs_sIR, mcpLoop, mcpBody, zeroIR, zeroBody,
    outs_wtabNIR, outs_fwdNIR]

theorem wf_sbIR (N ℓ B colB str d tS K : ℕ) : WF (sbIR N ℓ B colB str d tS K) := by
  have nf1 : ¬ Writes (fwdNIR N ℓ (tbA' B ℓ)) bC1 := nw_of_allBelow (by decide) (allBelow_fwdNIR ..)
  have nm : ∀ n, ¬ Writes (mcpLoop n) bC1 := fun n ↦ nw_of_allBelow (by decide) (allBelow_mcpLoop n)
  have nz : ∀ n a, ¬ Writes (zeroIR n a) bC1 := fun n a ↦ nw_of_allBelow (by decide) (allBelow_zeroIR n a)
  refine ⟨wf_sIR _ (by simp +decide [sbPro, SOp.Ok, Trk, regs, bT, bU, bBase, bOcc, bQ, xR, cOne]),
    wf_wtabNIR .., wf_zeroIR .., ⟨⟨by decide, by decide, by decide⟩, by decide, ?_, ?_⟩, ?_⟩
  · simp only [laneB, Writes, writes_sIR_iff, not_or]
    refine ⟨by simp +decide [SOp.Wr, SOp.dst, SOp.isMul, bU, bT, ySr, yStr, yDs, bC1], nm _, nz _ _,
      by simp +decide [Prim.dst, rA0, bC1], nf1, by simp +decide [SOp.Wr, SOp.dst, SOp.isMul, bP, bF, bR, bN2, bC1],
      ⟨by decide, by decide, ?_⟩, by simp +decide [SOp.Wr, SOp.dst, SOp.isMul, bQ, bC1]⟩
    simp only [cmpBody, Writes, writes_sIR_iff, not_or]
    refine ⟨by simp +decide [SOp.Wr, SOp.dst, SOp.isMul, bv, be, bf, bC1], by decide,
      by simp +decide [SOp.Wr, SOp.dst, SOp.isMul, bP, bR, bF, bC1]⟩
  · refine ⟨wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, bU, bT, bQ, ySr, yStr, yDs]), wf_mcpLoop _,
      wf_zeroIR .., by simp +decide [WF, Prim.dst, rA0], wf_fwdNIR .., wf_sIR _ (by
        simp +decide [SOp.Ok, Trk, regs, bP, bBase, bQ, bF, bR, bN2]), ⟨⟨by decide, by decide, by decide⟩,
        by decide, ?_, ?_⟩, wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, bQ, cOne])⟩
    · simp only [cmpBody, Writes, writes_sIR_iff, not_or]
      refine ⟨by simp +decide [SOp.Wr, SOp.dst, SOp.isMul, bv, be, bf, bC2], by decide,
        by simp +decide [SOp.Wr, SOp.dst, SOp.isMul, bP, bR, bF, bC2]⟩
    · exact ⟨wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, bv, be, bf, bP, bR, bF]), by simp only [WF]; decide,
        wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, bP, bR, bF, bOcc, cOne])⟩
  · refine ⟨wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, bF, bJ, bCnt, bS, bDm, bZ0, bN2]),
      ⟨by decide, by decide, by decide⟩, by decide, ?_, ?_⟩
    · simp +decide [scanBody, Writes, writes_sIR_iff, SOp.Wr, SOp.dst, SOp.isMul, bf, bz, bl, bS, bCnt, bF, bJ,
        bC2, cTmp]
    · exact ⟨wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, bf, bF, bz, bZ0, bl, bCnt, bDm]),
        ⟨⟨by simp only [WF]; decide, wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, bS, bCnt, cOne])⟩,
          by simp [WF]⟩, wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, bF, bJ, cOne])⟩

/-- The cost of one lane. -/
def laneBCost (N ℓ d : ℕ) : ℕ :=
  13 + (10 + 13 * (d + 1)) + (14 + 9 * (2 ^ ℓ - (d + 1))) + 1 +
    (14 + ℓ * ((67 + 20 * N) * 2 ^ (ℓ - 1) + 27)) + 9 + (8 + 2 ^ ℓ * 27) + 3 + 7

/-- **The builder's cost** (exact): the table, the flag clear, `K` lanes, the listing. -/
def sbCost (N ℓ d K : ℕ) : ℕ :=
  15 + (29 + 13 * N + (N - 1) * (1077 + 45 * N)) + (14 + 9 * 2 ^ ℓ) + (8 + K * (laneBCost N ℓ d + 3)) +
    (15 + (8 + 2 ^ ℓ * 30)) + 5

theorem cost_sbIR (N ℓ B colB str d tS K t : ℕ) (hN : N < 2 ^ 64) (hℓ : 2 ^ ℓ < 2 ^ 64) (hd : d + 1 < 2 ^ 64)
    (hK : K < 2 ^ 64) :
    cost (sbIR N ℓ B colB str d tS K) t = sbCost N ℓ d K := by
  have h1 : 2 ^ (ℓ - 1) < 2 ^ 64 := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le ℓ 1)) hℓ
  have hℓ' : ℓ < 2 ^ 64 := lt_of_lt_of_le (Nat.lt_two_pow_self) hℓ.le
  have h2 : 2 ^ ℓ - (d + 1) < 2 ^ 64 := lt_of_le_of_lt (Nat.sub_le _ _) hℓ
  simp only [sbIR, laneB, scanIR, scanBody, cmpBody, sbPro, cost, cost_sIR, sCost, cost_wtabNIR N _ t hN,
    cost_zeroIR _ _ t hℓ, cost_zeroIR _ _ t h2, cost_fwdNIR N ℓ _ t hN h1 hℓ', mcpLoop, mcpBody, blkSteps,
    List.length_cons, List.length_nil, toNat_toWord hℓ, toNat_toWord hd, toNat_toWord hK, sbCost, laneBCost]
  norm_num
  ring

/-- **The builder's size**: evaluated: `1,523` statements (the table `wtabNIR` and `fwdNIR` included); the lanes and
positions are loops, so the size does not grow with them. -/
theorem sizeIR_sbIR_le (N ℓ B colB str d tS K : ℕ) :
    sizeIR (sbIR N ℓ B colB str d tS K) ≤ 400 + sizeIR (wtabNIR N (tbA' B ℓ)) +
      sizeIR (fwdNIR N ℓ (tbA' B ℓ)) := by
  simp [sbIR, laneB, scanIR, scanBody, cmpBody, sbPro, sizeIR, sizeIR_sIR, sSize, zeroIR, zeroBody,
    mcpLoop, mcpBody, blkSteps]
  omega

/-! ## What the builder lists -/

/-- Lane `q`'s encoding: the forward NTT of column `q`'s first `d + 1` words, zero-padded. -/
noncomputable def encRow (M : Mem) (N ℓ colB str d q : ℕ) : ℕ → BF64 :=
  fwdRun ptK N ℓ (fun x ↦ if x < d + 1 then rdK M (colB + str * q + x) else 0)

/-- Position `j` agrees: every lane's encoding equals word `q` of row `j` of round `r`'s folded word. -/
def GoodB (M : Mem) (N ℓ colB str d tS r j : ℕ) : Prop :=
  ∀ q < tbOcc M tS r, encRow M N ℓ colB str d q j = rdK M (tbBase M tS r + q + tbOcc M tS r * j)

/-- **The list the builder writes**: the first `d + 3` agreeing positions below `2^ℓ`. -/
noncomputable def sbSpec (M : Mem) (N ℓ colB str d tS r : ℕ) : List ℕ := by
  classical
  exact ((List.range (2 ^ ℓ)).filter fun j ↦ decide (GoodB M N ℓ colB str d tS r j)).take (d + 3)

end Lvm6.X
