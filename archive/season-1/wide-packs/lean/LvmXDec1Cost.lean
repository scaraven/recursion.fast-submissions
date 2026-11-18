-- lvm2 X-REC2 (helper DEC): the level-1 decoder's well-formedness, cost, a concrete layout and the
-- non-vacuity checks. Adapted from this entry's `LvmXDecCost.lean`.
import LvmXRead1Defs
import LvmXDecCost
import LvmXDec1Agree
import LvmXDecIR4

-- (GOLF2: 12 declarations that `certified` does not use moved verbatim to `LvmXTopOff`, outside its import closure.)

-- ===== merged from `LvmXDec1IR` (GOLF module merge: `LvmXDec1IR.lean` is now a stub importing `LvmXDec1Cost`) =====
section
-- lvm2 X-REC2 (helper DEC): the phases of `C_rec`'s level-1 decoder on the machine. Adapted from this
-- entry's `LvmXDecIR.lean`/`LvmXDecIR2.lean` (v1's `encC`, `bflyAll`, `okIR` and their semantics) at
-- `ℓ = 12`/`9` and 48 lanes, and `LvmXCopy.lean` (`msgRow`/`rowsIR`, as the transpose `tr1Row`/`tr1IR`).

/-!
# The level-1 decoder's phases

**Workspace** `[d1B, d1B + 2^16)`: basis table `tbB d1B = d1B` (225 words, v1's), `eq` table
`q1B = d1B + 256` (48), the flag `ok1B = d1B + 512`, the weights `wb1B = d1B + 2^10` and the `E`
row `eb1B = d1B + 2^11` (`2^9` each), the agreement list `ag1B = d1B + 2^12` (`2^12`), `Enc₁(f₂)`'s
coordinates `enc1B = d1B + 2^13` (`3·2^12`), the interpolated lanes `ob1B = d1B + 2^15`
(`48·2^9`). The inputs (word `w1B`, `α` at `a1B`, `f₂` at `f2B`) and the output `oB` lie outside.

* `enc1C c`: `f₂`'s coordinate `c` (`f2B + 3v + c`, `v < 2^9`) zero-padded to `2^12`, then the
  forward NTT (`fwdIR 12`): `enc1C_sem`, `Enc` over `K` of the coordinate at every position.
* `bfly1All`: the inverse NTT (`bflyIR 9`) on each of the 48 lanes at `ob1B` (`bfly1All_sem`).
* `ok1IR`: the flag `[2^9 ≤ |A|]` in `rOk` and at `ok1B`.
* `tr1IR ob oB`: the transpose `M[oB + 48 v + t] := M[ob + 2^9 t + v]` (`v < 2^9`, `t < 48`), so
  that `rdE (oB + 3 (u + 16 v))` is row `u`'s coefficient `v`.

Registers: v1's `rA0`, `rOk`, `zT`, `zK`, `zC`, `zN`, the copy's `64 … 73`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

/-! ## Layout -/

/-- The `eq(α₁, ·)` table. -/ def q1B (dB : ℕ) : ℕ := dB + 256
/-- The success flag. -/ def ok1B (dB : ℕ) : ℕ := dB + 512
/-- The interpolation weights. -/ def wb1B (dB : ℕ) : ℕ := dB + 2 ^ 10
/-- The interpolation's `E` row. -/ def eb1B (dB : ℕ) : ℕ := dB + 2 ^ 11
/-- The agreement list. -/ def ag1B (dB : ℕ) : ℕ := dB + 2 ^ 12
/-- `Enc₁(f₂)`'s coordinates. -/ def enc1B (dB : ℕ) : ℕ := dB + 2 ^ 13
/-- The interpolated lanes (`2^9` each). -/ def ob1B (dB : ℕ) : ℕ := dB + 2 ^ 15

/-! ## The programs -/

/-- **`Enc₁(f₂)`'s coordinate `c`** at `enc1B + c·2^12`: copy, zero padding, forward NTT. -/
def enc1C (dB fB c : ℕ) : XIR :=
  .seq (mcpIR (2 ^ 9) (fB + c) 3 (enc1B dB + c * 2 ^ 12))
    (.seq (zeroIR (2 ^ 12 - 2 ^ 9) (enc1B dB + c * 2 ^ 12 + 2 ^ 9))
      (.seq (.blk [.const rA0 (toWord (enc1B dB + c * 2 ^ 12))]) (fwdIR 12 (tbB dB))))

/-- The three coordinates. -/
def enc1IR (dB fB : ℕ) : XIR := .seq (enc1C dB fB 0) (.seq (enc1C dB fB 1) (enc1C dB fB 2))

/-- One lane `t`: `rA0 := ob1B + t·2^9`, the inverse NTT, `t += 1`. -/
def bfly1Row (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK, .const zK (toWord (ob1B dB)),
      .op .add rA0 rA0 zK]) (.seq (bflyIR 9 (tbB dB)) (.blk [.op .add zT zT cOne]))

/-- **The inverse NTT of the 48 lanes.** -/
def bfly1All (dB : ℕ) : XIR :=
  .seq (.blk [.const zT 0, .const zN 48]) (.loopK zC zN 48 (bfly1Row dB))

/-- **The flag** `rOk := [2^9 ≤ cnt]`, stored at `ok1B`. -/
def ok1IR (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 9)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (ok1B dB))]) (.store zK rOk)

/-- One transposed row `v` (`yL`): `M[oB + 48 v + t] := M[ob + v + 2^9 t]`, `t < 48`; `v += 1`. -/
def tr1Row (ob oB : ℕ) : XIR :=
  .seq (.blk [.const yK (toWord ob), .op .add ySr yL yK, .const yK 48, .op .mul yDs yL yK,
      .const yK (toWord oB), .op .add yDs yDs yK, .const yStr (toWord (2 ^ 9))])
    (.seq (mcpLoop 48) (.blk [.op .add yL yL cOne]))

/-- **The transpose** of the `48 × 2^9` lanes at `ob` into `2^9` rows of 48 words at `oB`. -/
def tr1IR (ob oB : ℕ) : XIR :=
  .seq (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) (.loopK yC2 yN2 (toWord (2 ^ 9)) (tr1Row ob oB))

/-- **The decoding proper** (on success): interpolation of the 48 lanes on the first `2^9`
listed positions, the inverse NTT per lane, the transpose into the output. -/
def dec1Tail (dB wB oB : ℕ) : XIR :=
  .seq (baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB))
    (.seq (bfly1All dB) (tr1IR (ob1B dB) oB))

/-! ## Semantics of the phases -/

/-- `mcpBody_sem` with only the read address below `2^64` (the source pointer may wrap after it). -/
theorem tr1Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {a d k : ℕ} (ha : a < 2 ^ 64)
    (hd : regs ≤ d) (hd2 : d + 1 < 2 ^ 64) (hds : d < s.M.size)
    (hS : rd s.M ySr = toWord a) (hD : rd s.M yDs = toWord d) (hK : rd s.M yStr = toWord k) :
    rd (semXIR I mcpBody s).M d = rd s.M a ∧
    rd (semXIR I mcpBody s).M ySr = toWord (a + k) ∧
    rd (semXIR I mcpBody s).M yDs = toWord (d + 1) ∧
    (∀ r, r ≠ yV → r ≠ ySr → r ≠ yDs → r ≠ cTmp → r ≠ d → rd (semXIR I mcpBody s).M r = rd s.M r) ∧
    Inv (semXIR I mcpBody s).M := by
  have hs := hM.1
  simp only [regs] at hs hd
  rw [mcpBody, semXIR_seq]
  obtain ⟨l1, l2, hM1⟩ := load_sem I s hM (d := yV) (p := ySr) (by decide) (by decide) hS ha
  have z1 := size_sem I (.load yV ySr) s
  generalize semXIR I (.load yV ySr) s = s1 at l1 l2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := yDs) (v := yV) (x := d) (by decide) (by decide)
    (by rw [l2 _ (by decide), hD]) (by simp only [regs]; (clear * - hd; omega)) (by (clear * - d s a hd hd2 s1; omega)) (by (clear * - d s1 s a hds z1; omega))
  have z2 := size_sem I (.store yDs yV) s1
  generalize semXIR I (.store yDs yV) s1 = s2 at c1 c2 hM2 z2
  have hdr : ∀ r, r < regs → r ≠ d := fun r hr => by simp only [regs] at hr; (clear * - r d s a hd hd2 s1 s2 hr; omega)
  have e2 : ∀ r, r ≠ yV → r ≠ cTmp → r ≠ d → rd s2.M r = rd s.M r := fun r h1 h2 h3 =>
    (c2 r h3 h2).trans (l2 r h1)
  have h1 : rd s2.M cOne = 1 := hM2.2 0 (by decide)
  refine ⟨?_, ?_, ?_, fun r r1 r2 r3 r4 r5 => ?_, inv_sem I (P := .blk [.op .add ySr ySr yStr,
    .op .add yDs yDs cOne]) (by simp +decide [WF, Prim.dst, ySr, yDs]) hM2⟩
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, ySr, yDs]; (clear * - d s a hd hd2 s1 s2; omega)), c1, l1]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [ySr]; (clear * - s2 s a d hs s1 z1 z2; omega)),
      e2 _ (by decide) (by decide) (hdr _ (by decide)), e2 _ (by decide) (by decide)
        (hdr _ (by decide)), hS, hK, add_toWord]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, yDs]; (clear * - s2 s a d hs s1 z1 z2; omega)), rd_set_ne (by decide),
      rd_set_ne (by decide), e2 _ (by decide) (by decide) (hdr _ (by decide)), hD, h1,
      add_one_toWord]
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact ⟨Ne.symm r2, Ne.symm r3⟩),
      e2 r r1 r4 r5]

/-- `mcpLoop_sem` with only the read addresses below `2^64`. -/
theorem tr1Loop_sem (I : Array Word) (s : St) (hM : Inv s.M) {n src str dst : ℕ}
    (hn : n < 2 ^ 64) (hsrc2 : ∀ i < n, src + str * i < 2 ^ 64) (hdst : regs ≤ dst)
    (hdst2 : dst + n < 2 ^ 64) (hdsts : dst + n ≤ s.M.size)
    (hdisj : ∀ i < n, src + str * i < dst ∨ dst + n ≤ src + str * i)
    (hsrcR : ∀ i < n, regs ≤ src + str * i)
    (hS : rd s.M ySr = toWord src) (hD : rd s.M yDs = toWord dst) (hK : rd s.M yStr = toWord str) :
    (∀ i < n, rd (semXIR I (mcpLoop n) s).M (dst + i) = rd s.M (src + str * i)) ∧
    (∀ r, KeepC r → (r < dst ∨ dst + n ≤ r) → rd (semXIR I (mcpLoop n) s).M r = rd s.M r) ∧
    Inv (semXIR I (mcpLoop n) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdst
  rw [mcpLoop, semXIR_seq]
  have hM0 := inv_sem I (P := .blk [.const yN (toWord n)]) (by simp +decide [WF, Prim.dst, yN]) hM
  have n0 : rd (semXIR I (.blk [.const yN (toWord n)]) s).M yN = toWord n := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [yN]; (clear * - s n dst hs; omega))]
  have k0 : ∀ r, r ≠ yN → rd (semXIR I (.blk [.const yN (toWord n)]) s).M r = rd s.M r :=
    fun r hr => rd_blk_of_not_dst I _ s (by simp [Prim.dst]; exact Ne.symm hr)
  have z0 := size_sem I (.blk [.const yN (toWord n)]) s
  generalize semXIR I (.blk [.const yN (toWord n)]) s = s0 at hM0 n0 k0 z0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M ySr = toWord (src + str * j) ∧ rd s'.M yDs = toWord (dst + j) ∧
    rd s'.M yStr = toWord str ∧ (∀ i < j, rd s'.M (dst + i) = rd s.M (src + str * i)) ∧
    (∀ r, KeepC r → (r < dst ∨ dst + j ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC → i ≠ cTmp → rd (entryK yC yN (toWord n) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC yN (toWord n) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_, ?_,
      fun i hi => absurd hi (by (clear * - i s n dst s0 hi; omega)), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hS, Nat.mul_zero, Nat.add_zero]
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hD, Nat.add_zero]
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hK]
    · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
      rw [hE _ r4 r6, k0 _ r5]
  have hstep : ∀ j s', j < n → P j s' → P (j + 1) (decS yC (semXIR I mcpBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨b1, b2, b3, b4, hM'⟩ := tr1Body_sem I s' i1 (a := src + str * j) (d := dst + j)
      (k := str) (hsrc2 j hj) (by simp only [regs]; (clear * - dst j s n hdst s0 s'; omega)) (by (clear * - dst j s n hdst2 s0 s' hj; omega)) (by (clear * - dst j s' s n src str hdsts s0 z0 h0 hj i2; omega)) i3 i4 i5
    have hd : ∀ x, x ≠ yC → rd (decS yC (semXIR I mcpBody s')).M x =
        rd (semXIR I mcpBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], ?_, ?_, ?_,
      fun i hi => ?_, fun r hr hr2 => ?_⟩
    · rw [hd _ (by decide), b2, Nat.mul_succ, Nat.add_assoc]
    · rw [hd _ (by decide), b3, Nat.add_assoc]
    · rw [hd _ (by decide), b4 _ (by decide) (by decide) (by decide) (by decide)
        (by simp only [yStr, regs] at *; (clear * - dst j s n hdst s0 s'; omega)), i5]
    · have hdx : ∀ x, regs ≤ x → x ≠ yC := fun x hx => by simp only [yC, regs] at *; (clear * - x s n dst s0 j s' i hx; omega)
      rw [hd _ (hdx _ (by simp only [regs]; (clear * - dst i s n hdst s0 j s'; omega)))]
      by_cases hij : i = j
      · subst hij
        rw [b1, i7 _ (keepC_of_regs (hsrcR i (by (clear * - hj; omega))))
          ((hdisj i hj).imp_right (fun h => by (clear * - dst i src str s n s0 s' hj h; omega)))]
      · have hk := keepC_of_regs (show regs ≤ dst + i by simp only [regs]; (clear * - dst i s n hdst s0 j s'; omega))
        rw [b4 _ hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.2.2 (by (clear * - dst i j s n s0 s' hij; omega)), i6 i (by (clear * - i j s n dst s0 s' hi hij; omega))]
    · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
      rw [hd _ r4, b4 r r1 r2 r3 r6 (by (clear * - r dst j s n hn s0 s' hj hr2 r1 r2 r3 r4 r5 r6; omega)), i7 r ⟨r1, r2, r3, r4, r5, r6⟩ (by (clear * - r dst j s n s0 s' hr2 r1 r2 r3 r4 r5 r6; omega))]
  have hfin := loopK_run I mcpBody P s0 hM0 (c := yC) (n := yN) (K := n) (by decide) (by decide)
    (by decide) n0 hn h0 hstep
  exact ⟨hfin.2.2.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2.2.2 r hr hr2, hfin.1⟩

end Lvm.X
end
-- ===== end of `LvmXDec1IR` =====

-- ===== merged from `LvmXDec1IR2` (GOLF module merge: `LvmXDec1IR2.lean` is now a stub importing `LvmXDec1Cost`) =====
section
-- lvm2 X-REC2 (helper DEC): the level-1 decoder program `dec1IR` and its semantics. Adapted from this
-- entry's `LvmXDecIR3.lean`/`LvmXDecIR4.lean` (v1's `decTail_sem`, `decIR`, `decIR_sem`).

/-!
# The level-1 decoder of `C_rec` on the machine

`dec1IR dB wB aB fB oB`: the basis table (`wtabIR`); `eq(α₁, ·)` (`eqtIR 4`); `Enc₁(f₂)`
(`enc1IR`); the agreement scan (`agree1IR`); the flag (`ok1IR`); on success the interpolation
of the 48 lanes, their inverse NTTs and the transpose into the output (`dec1Tail`).

**`dec1IR_sem`**: on a memory holding the level-1 word `wd` at `wB + 48q + t` (`q < 2^12`,
`t < 48`), `α_i` at `aB + 3i` (`i < 4`) and `f₂(v)` at `fB + 3v` (`v < 2^9`, `rdE`), with the
layout `Dec1Lay`:
* the cell `ok1B dB` holds `[2^9 ≤ |agree1L wd α f₂|]`, i.e. `decodeRec1 wd α f₂ ≠ none`;
* if `decodeRec1 wd α f₂ = some f₁`, then `rdE (oB + 3v) = f₁ v` for every `v < 2^13`: the
  layout v1's `decIR` reads its `f₁` from (`fB := oB`);
* the heap outside the workspace `[dB, dB + 2^16)` and the output `[oB, oB + 3·2^13)` is kept.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The level-1 decoder program.** -/
def dec1IR (dB wB aB fB oB : ℕ) : XIR :=
  .seq (wtabIR (tbB dB)) (.seq (eqtIR 4 aB (q1B dB)) (.seq (enc1IR dB fB)
    (.seq (agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)) (.seq (ok1IR dB)
      (.ite rOk (dec1Tail dB wB oB) (.blk []))))))

theorem eqA1_congr {α α' : ℕ → Ext3} (h : ∀ i < 4, α i = α' i) (u : ℕ) : eqA1 α u = eqA1 α' u := by
  simp only [eqA1, eqBits, bitSel]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i (mem_range.1 hi)]

end Lvm.X
end
-- ===== end of `LvmXDec1IR2` =====

/-!
# The level-1 decoder's cost and layout

* `wf_dec1IR`, `noLoopT_dec1IR`, `outs_dec1IR`, `dec1IR_o` (no output statement).
* **`cost_dec1IR_le`**: the level-1 decoder is below `2^31` steps; with the level-1 reads
  (`cost_read1IR_le`) the level adds below `2^32` to v1's `2^37.95`.
* **`dec1Lay_example`**: `w1B = 2^23`, `d1B = 2^23 + 2^21`, `f2B = 2^23 + 2^22`,
  `a1B = 2^19 + 24`, `oB = 2^19 + 64` (v1's `fB`): everything below `2^24` (`memX = 2^25` is
  untouched), disjoint from v1's `decLay_example` (`dB = 2^22` workspace `[2^22, 3·2^21)`, word
  `[2^20, 3·2^20)`, `α₀` `[2^19, 2^19 + 18)`) except the output, which is v1's `f₁` input.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

theorem wf_dec1IR (dB wB aB fB oB : ℕ) : WF (dec1IR dB wB aB fB oB) := by
  have h1 := wf_wtabIR (tbB dB)
  have h2 := wf_eqtIR 4 aB (q1B dB)
  have h3 := fun c => wf_mcpIR (2 ^ 9) (fB + c) 3 (enc1B dB + c * 2 ^ 12)
  have h4 := fun c => wf_zeroIR (2 ^ 12 - 2 ^ 9) (enc1B dB + c * 2 ^ 12 + 2 ^ 9)
  have h5 := wf_fwdIR 12 (tbB dB)
  have h6 := wf_agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)
  have h7 := wf_baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB)
  have h8 := wf_bflyIR 9 (tbB dB)
  have n8 := bflyIR_nw_hi 9 (tbB dB) (r := zC) (by decide)
  simp only [dec1IR, enc1IR, enc1C, ok1IR, dec1Tail, bfly1All, bfly1Row, tr1IR, tr1Row, WF, Writes,
    Prim.dst, h1, h2, h3, h4, h5, h6, h7, h8, n8, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, exists_eq_or_imp, exists_eq_left, or_false, false_or, true_and, and_true]
  simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, rA0, zK, rOk, zT, zN, zC, cTmp, regs, ySr,
    yDs, yStr, yV, yC, yN, yL, yK, yC2, yN2]

theorem noLoopT_dec1IR (dB wB aB fB oB : ℕ) : NoLoopT (dec1IR dB wB aB fB oB) := by
  simp only [dec1IR, enc1IR, enc1C, ok1IR, dec1Tail, bfly1All, bfly1Row, tr1IR, tr1Row, mcpLoop,
    mcpBody, NoLoopT, noLoopT_wtabIR, noLoopT_eqtIR, noLoopT_mcpIR, noLoopT_zeroIR, noLoopT_fwdIR,
    noLoopT_agree1IR, noLoopT_baryIR, noLoopT_bflyIR, and_self]

theorem outs_dec1IR (dB wB aB fB oB t : ℕ) : outs (dec1IR dB wB aB fB oB) t = 0 := by
  simp only [dec1IR, enc1IR, enc1C, ok1IR, dec1Tail, bfly1All, bfly1Row, tr1IR, tr1Row, mcpLoop,
    mcpBody, outs, outs_wtabIR, outs_eqtIR, outs_mcpIR, outs_zeroIR, outs_fwdIR, outs_agree1IR,
    outs_baryIR, outs_bflyIR]
  norm_num

/-! ## Costs -/

theorem cost_enc1C (dB fB c t : ℕ) : cost (enc1C dB fB c) t = 9058676 := by
  simp only [enc1C, cost, cost_mcpIR _ _ _ _ _ (show 2 ^ 9 < 2 ^ 64 by norm_num),
    cost_zeroIR _ _ _ (show 2 ^ 12 - 2 ^ 9 < 2 ^ 64 by norm_num),
    cost_fwdIR 12 _ _ (by norm_num) (by norm_num), blkSteps, List.length_cons, List.length_nil]
  norm_num

theorem cost_bfly1All (dB t : ℕ) : cost (bfly1All dB) t = 40598508 := by
  simp only [bfly1All, bfly1Row, cost, cost_bflyIR 9 _ _ (by norm_num) (by norm_num), blkSteps,
    List.length_cons, List.length_nil]
  norm_num

theorem cost_tr1IR (ob oB t : ℕ) : cost (tr1IR ob oB) t = 334348 := by
  simp only [tr1IR, tr1Row, mcpLoop, mcpBody, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (show 2 ^ 9 < 2 ^ 64 by norm_num), toNat_toWord (show 48 < 2 ^ 64 by norm_num)]
  norm_num

/-- **The level-1 decoder's cost**: `925,440,493` steps (`≈ 2^29.79`; interpolation
`848,495,641`, inverse NTTs `40,598,508`, `Enc₁` `27,176,030`, agreement `8,802,318`). -/
theorem cost_dec1IR (dB wB aB fB oB t : ℕ) : cost (dec1IR dB wB aB fB oB) t = 925440493 := by
  simp only [dec1IR, enc1IR, ok1IR, dec1Tail, cost, cost_wtabIR, cost_eqtIR 4 _ _ _ (by norm_num),
    cost_enc1C, cost_agree1IR, cost_baryIR (2 ^ 9) 48 _ _ _ _ _ _ _ (by norm_num) (by norm_num),
    cost_bfly1All, cost_tr1IR, blkSteps, List.length_cons, List.length_nil]
  norm_num

/-- **The level-1 decoder is below `2^31`** (in fact `2^29.79`). -/
theorem cost_dec1IR_le (dB wB aB fB oB t : ℕ) : cost (dec1IR dB wB aB fB oB) t ≤ 2 ^ 31 := by
  rw [cost_dec1IR]; norm_num

/-- **The level-1 reads and decoder together are below `2^32`.** -/
theorem dec1_fixed_le (bX pL capW wB dB aB fB oB t : ℕ) :
    cost (read1IR bX pL capW wB) t + cost (dec1IR dB wB aB fB oB) t ≤ 2 ^ 32 := by
  have h1 := cost_read1IR_le bX pL capW wB t
  have h2 := cost_dec1IR_le dB wB aB fB oB t
  (clear * - bX pL capW wB t dB aB fB oB h1 h2; omega)

end Lvm.X
