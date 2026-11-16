-- WP-13b: heap copies of the decoder (new; the loop-by-invariant proofs follow LvmXAgree's, i.e.
-- rf-k/submissions/flock-recursive/lean/FRXAgree.lean@8bff272b `scanIR_sem`, and FRXRead.lean `copyLoop`).
import LvmXAgree

-- (GOLF2: 2 declarations that `certified` does not use moved verbatim to `LvmXCopyOff`, outside its import closure.)

/-!
# Strided copies, zero fills, the message reorder

* `mcpLoop n`: `n` words `M[dst + i] := M[src + str·i]` from the pointers `ySr`, `yDs` and the
  stride `yStr`; `mcpIR n src str dst` sets them (`mcpIR_sem`). The decoder copies `f₁`'s
  coordinate `c` (`str = 3`) before the forward NTT, and the rows into message order.
* `zeroIR n dst`: `n` zero words (`zeroIR_sem`), the forward NTT's zero padding.
* `rowsIR oB mB`: row `l` of the message (`mB + l·2^13 + v`) from row `63 − l` of the decoded leaf
  words (`oB + (63 − l)·2^13 + v`) (`rowsIR_sem`).

Registers `64 … 74`.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-- Source pointer. -/ def ySr : ℕ := 64
/-- Destination pointer. -/ def yDs : ℕ := 65
/-- Stride. -/ def yStr : ℕ := 66
/-- A word. -/ def yV : ℕ := 67
/-- The inner counter. -/ def yC : ℕ := 68
/-- Its count. -/ def yN : ℕ := 69
/-- The row `l`. -/ def yL : ℕ := 70
/-- Scratch. -/ def yK : ℕ := 71
/-- The outer counter. -/ def yC2 : ℕ := 72
/-- Its count. -/ def yN2 : ℕ := 73

/-! ## The programs -/

/-- One word: `M[yDs] := M[ySr]`, `ySr += yStr`, `yDs += 1`. -/
def mcpBody : XIR :=
  .seq (.load yV ySr) (.seq (.store yDs yV) (.blk [.op .add ySr ySr yStr, .op .add yDs yDs cOne]))

/-- `n` words from the pointers in `ySr`, `yDs`, `yStr`. -/
def mcpLoop (n : ℕ) : XIR := .seq (.blk [.const yN (toWord n)]) (.loopK yC yN (toWord n) mcpBody)

/-- **The strided copy** `M[dst + i] := M[src + str·i]`, `i < n`. -/
def mcpIR (n src str dst : ℕ) : XIR :=
  .seq (.blk [.const ySr (toWord src), .const yStr (toWord str), .const yDs (toWord dst)])
    (mcpLoop n)

/-- One zero word: `M[yDs] := 0`, `yDs += 1` (`yV` holds `0`). -/
def zeroBody : XIR := .seq (.store yDs yV) (.blk [.op .add yDs yDs cOne])

/-- **The zero fill** of `[dst, dst + n)`. -/
def zeroIR (n dst : ℕ) : XIR :=
  .seq (.blk [.const yV 0, .const yDs (toWord dst), .const yN (toWord n)])
    (.loopK yC yN (toWord n) zeroBody)

/-- One message row `l`: source row `63 − l`, then the copy of `2^13` words; `l += 1`. -/
def msgRow (oB mB : ℕ) : XIR :=
  .seq (.blk [.const yK 63, .op .sub ySr yK yL, .const yK (toWord (2 ^ 13)), .op .mul ySr ySr yK,
      .const yK (toWord oB), .op .add ySr ySr yK, .const yK (toWord (2 ^ 13)), .op .mul yDs yL yK,
      .const yK (toWord mB), .op .add yDs yDs yK, .const yStr 1])
    (.seq (mcpLoop (2 ^ 13)) (.blk [.op .add yL yL cOne]))

/-- **The reorder**: message row `l` at `mB + l·2^13` from leaf-word row `63 − l` at `oB`. -/
def rowsIR (oB mB : ℕ) : XIR :=
  .seq (.blk [.const yL 0, .const yN2 64]) (.loopK yC2 yN2 64 (msgRow oB mB))

/-! ## Well formed, no tape loop, no output, cost -/

theorem wf_mcpIR (n src str dst : ℕ) : WF (mcpIR n src str dst) := by
  simp +decide [mcpIR, mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yStr, yV, yC, yN, cTmp,
    regs]

theorem wf_zeroIR (n dst : ℕ) : WF (zeroIR n dst) := by
  simp +decide [zeroIR, zeroBody, WF, Writes, Prim.dst, yDs, yV, yC, yN, cTmp, regs]

theorem wf_rowsIR (oB mB : ℕ) : WF (rowsIR oB mB) := by
  simp +decide [rowsIR, msgRow, mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yStr, yV, yC,
    yN, yL, yK, yC2, yN2, cTmp, regs]

theorem noLoopT_mcpIR (n src str dst : ℕ) : NoLoopT (mcpIR n src str dst) := by
  simp [mcpIR, mcpLoop, mcpBody, NoLoopT]

theorem noLoopT_zeroIR (n dst : ℕ) : NoLoopT (zeroIR n dst) := by
  simp [zeroIR, zeroBody, NoLoopT]

theorem noLoopT_rowsIR (oB mB : ℕ) : NoLoopT (rowsIR oB mB) := by
  simp [rowsIR, msgRow, mcpLoop, mcpBody, NoLoopT]

theorem outs_mcpIR (n src str dst t : ℕ) : outs (mcpIR n src str dst) t = 0 := by
  simp [mcpIR, mcpLoop, mcpBody, outs]

theorem outs_zeroIR (n dst t : ℕ) : outs (zeroIR n dst) t = 0 := by
  simp [zeroIR, zeroBody, outs]

theorem outs_rowsIR (oB mB t : ℕ) : outs (rowsIR oB mB) t = 0 := by
  simp [rowsIR, msgRow, mcpLoop, mcpBody, outs]

theorem cost_mcpIR (n src str dst t : ℕ) (hn : n < 2 ^ 64) :
    cost (mcpIR n src str dst) t = 16 + 13 * n := by
  simp only [mcpIR, mcpLoop, mcpBody, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord hn]
  norm_num; ring

theorem cost_zeroIR (n dst t : ℕ) (hn : n < 2 ^ 64) : cost (zeroIR n dst) t = 14 + 9 * n := by
  simp only [zeroIR, zeroBody, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord hn]
  norm_num; ring

/-- **The reorder's cost**: `64` rows of `2^13` words (`≈ 2^22.7`). -/
theorem cost_rowsIR (oB mB t : ℕ) : cost (rowsIR oB mB) t = 6818124 := by
  simp only [rowsIR, msgRow, mcpLoop, mcpBody, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (show 2 ^ 13 < 2 ^ 64 by norm_num)]
  norm_num

/-! ## Semantics -/

/-- **One copied word**: `M[d] := M[a]`, `ySr := a + k`, `yDs := d + 1`. -/
theorem mcpBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {a d k : ℕ} (ha2 : a + k < 2 ^ 64)
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
  obtain ⟨l1, l2, hM1⟩ := load_sem I s hM (d := yV) (p := ySr) (by decide) (by decide) hS
    (by (clear * - ha2; omega))
  have z1 := size_sem I (.load yV ySr) s
  generalize semXIR I (.load yV ySr) s = s1 at l1 l2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := yDs) (v := yV) (x := d) (by decide) (by decide)
    (by rw [l2 _ (by decide), hD]) (by simp only [regs]; (clear * - hd; omega)) (by (clear * - hd hd2; omega)) (by (clear * - hds z1; omega))
  have z2 := size_sem I (.store yDs yV) s1
  generalize semXIR I (.store yDs yV) s1 = s2 at c1 c2 hM2 z2
  have hdr : ∀ r, r < regs → r ≠ d := fun r hr => by simp only [regs] at hr; (clear * - hd hd2 hr; omega)
  have e2 : ∀ r, r ≠ yV → r ≠ cTmp → r ≠ d → rd s2.M r = rd s.M r := fun r h1 h2 h3 =>
    (c2 r h3 h2).trans (l2 r h1)
  have h1 : rd s2.M cOne = 1 := hM2.2 0 (by decide)
  refine ⟨?_, ?_, ?_, fun r r1 r2 r3 r4 r5 => ?_, inv_sem I (P := .blk [.op .add ySr ySr yStr,
    .op .add yDs yDs cOne]) (by simp +decide [WF, Prim.dst, ySr, yDs]) hM2⟩
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, ySr, yDs]; (clear * - hd hd2; omega)), c1, l1]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [ySr]; (clear * - hs z1 z2; omega)),
      e2 _ (by decide) (by decide) (hdr _ (by decide)), e2 _ (by decide) (by decide)
        (hdr _ (by decide)), hS, hK, add_toWord]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, yDs]; (clear * - hs z1 z2; omega)), rd_set_ne (by decide),
      rd_set_ne (by decide), e2 _ (by decide) (by decide) (hdr _ (by decide)), hD, h1,
      add_one_toWord]
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact ⟨Ne.symm r2, Ne.symm r3⟩),
      e2 r r1 r4 r5]

/-- The cells and registers the copy loop keeps. -/
def KeepC (r : ℕ) : Prop := r ≠ yV ∧ r ≠ ySr ∧ r ≠ yDs ∧ r ≠ yC ∧ r ≠ yN ∧ r ≠ cTmp

theorem keepC_of_regs {r : ℕ} (h : regs ≤ r) : KeepC r := by
  simp only [KeepC, regs, yV, ySr, yDs, yC, yN, cTmp] at *; (clear * - r h; omega)

/-- **The copy loop**: from `ySr = src`, `yDs = dst`, `yStr = str`, `n` words
`M[dst + i] := M[src + str·i]`; the heap outside `[dst, dst + n)` and the registers outside the
loop's are kept. The source cells must lie outside the destination. -/
theorem mcpLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {n src str dst : ℕ}
    (hn : n < 2 ^ 64) (hsrc2 : src + str * n < 2 ^ 64) (hdst : regs ≤ dst)
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
    rw [rd_set_self (by simp only [yN]; (clear * - hs; omega))]
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
      fun i hi => absurd hi (by (clear * - hi; omega)), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hS, Nat.mul_zero, Nat.add_zero]
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hD, Nat.add_zero]
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hK]
    · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
      rw [hE _ r4 r6, k0 _ r5]
  have hstep : ∀ j s', j < n → P j s' → P (j + 1) (decS yC (semXIR I mcpBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hsj : src + str * j + str ≤ src + str * n := by
      have := Nat.mul_le_mul_left str (show j + 1 ≤ n by (clear * - hj; omega)); rw [Nat.mul_succ] at this; (clear * - this; omega)
    obtain ⟨b1, b2, b3, b4, hM'⟩ := mcpBody_sem I s' i1 (a := src + str * j) (d := dst + j)
      (k := str) (by (clear * - hsrc2 hsj; omega)) (by simp only [regs]; (clear * - hdst; omega)) (by (clear * - hdst2 hj; omega)) (by (clear * - hdsts z0 h0 hj i2; omega)) i3 i4 i5
    have hd : ∀ x, x ≠ yC → rd (decS yC (semXIR I mcpBody s')).M x =
        rd (semXIR I mcpBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], ?_, ?_, ?_,
      fun i hi => ?_, fun r hr hr2 => ?_⟩
    · rw [hd _ (by decide), b2, Nat.mul_succ, Nat.add_assoc]
    · rw [hd _ (by decide), b3, Nat.add_assoc]
    · rw [hd _ (by decide), b4 _ (by decide) (by decide) (by decide) (by decide)
        (by simp only [yStr, regs] at *; (clear * - hdst; omega)), i5]
    · have hdx : ∀ x, regs ≤ x → x ≠ yC := fun x hx => by simp only [yC, regs] at *; (clear * - hx; omega)
      rw [hd _ (hdx _ (by simp only [regs]; (clear * - hdst; omega)))]
      by_cases hij : i = j
      · subst hij
        rw [b1, i7 _ (keepC_of_regs (hsrcR i (by (clear * - hj; omega))))
          ((hdisj i hj).imp_right (fun h => by (clear * - hj h; omega)))]
      · have hk := keepC_of_regs (show regs ≤ dst + i by simp only [regs]; (clear * - hdst; omega))
        rw [b4 _ hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.2.2 (by (clear * - hij; omega)), i6 i (by (clear * - hi hij; omega))]
    · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
      rw [hd _ r4, b4 r r1 r2 r3 r6 (by (clear * - hn hj hr2 r1 r2 r3 r4 r5 r6; omega)), i7 r ⟨r1, r2, r3, r4, r5, r6⟩ (by (clear * - hr2 r1 r2 r3 r4 r5 r6; omega))]
  have hfin := loopK_run I mcpBody P s0 hM0 (c := yC) (n := yN) (K := n) (by decide) (by decide)
    (by decide) n0 hn h0 hstep
  exact ⟨hfin.2.2.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2.2.2 r hr hr2, hfin.1⟩

/-- **The strided copy** (`mcpLoop` with its pointers set). -/
theorem mcpIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n src str dst : ℕ}
    (hn : n < 2 ^ 64) (hsrc2 : src + str * n < 2 ^ 64) (hstr : str < 2 ^ 64) (hdst : regs ≤ dst)
    (hdst2 : dst + n < 2 ^ 64) (hdsts : dst + n ≤ s.M.size)
    (hdisj : ∀ i < n, src + str * i < dst ∨ dst + n ≤ src + str * i)
    (hsrcR : ∀ i < n, regs ≤ src + str * i) :
    (∀ i < n, rd (semXIR I (mcpIR n src str dst) s).M (dst + i) = rd s.M (src + str * i)) ∧
    (∀ r, regs ≤ r → (r < dst ∨ dst + n ≤ r) → rd (semXIR I (mcpIR n src str dst) s).M r = rd s.M r) ∧
    Inv (semXIR I (mcpIR n src str dst) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdst
  rw [mcpIR, semXIR_seq]
  have w0 : WF (.blk [.const ySr (toWord src), .const yStr (toWord str), .const yDs (toWord dst)]) :=
    by simp +decide [WF, Prim.dst, ySr, yStr, yDs]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const ySr (toWord src), .const yStr (toWord str),
    .const yDs (toWord dst)]) s
  have r0 : rd (semXIR I (.blk [.const ySr (toWord src), .const yStr (toWord str),
        .const yDs (toWord dst)]) s).M ySr = toWord src ∧
      rd (semXIR I (.blk [.const ySr (toWord src), .const yStr (toWord str),
        .const yDs (toWord dst)]) s).M yDs = toWord dst ∧
      rd (semXIR I (.blk [.const ySr (toWord src), .const yStr (toWord str),
        .const yDs (toWord dst)]) s).M yStr = toWord str := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, ySr, yStr, yDs]; (clear * - s I n src str dst hs z0; omega))) only [rd_set_self, rd_set_ne]
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk [.const ySr (toWord src), .const yStr (toWord str),
      .const yDs (toWord dst)]) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, ySr, yStr, yDs] <;> (clear * - hr; omega)
  generalize semXIR I (.blk [.const ySr (toWord src), .const yStr (toWord str),
    .const yDs (toWord dst)]) s = s0 at hM0 z0 r0 k0
  obtain ⟨a1, a2, a3⟩ := mcpLoop_sem I s0 hM0 hn hsrc2 (by simp only [regs]; (clear * - hdst; omega)) hdst2 (by (clear * - hdsts z0; omega))
    hdisj hsrcR r0.1 r0.2.1 r0.2.2
  refine ⟨fun i hi => ?_, fun r hr hr2 => ?_, a3⟩
  · rw [a1 i hi, k0 _ (hsrcR i hi)]
  · rw [a2 r (keepC_of_regs hr) hr2, k0 r hr]

/-- **The zero fill** of `[dst, dst + n)`. -/
theorem zeroIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n dst : ℕ} (hn : n < 2 ^ 64)
    (hdst : regs ≤ dst) (hdst2 : dst + n < 2 ^ 64) (hdsts : dst + n ≤ s.M.size) :
    (∀ i < n, rd (semXIR I (zeroIR n dst) s).M (dst + i) = 0) ∧
    (∀ r, regs ≤ r → (r < dst ∨ dst + n ≤ r) → rd (semXIR I (zeroIR n dst) s).M r = rd s.M r) ∧
    Inv (semXIR I (zeroIR n dst) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdst
  rw [zeroIR, semXIR_seq]
  have w0 : WF (.blk [.const yV 0, .const yDs (toWord dst), .const yN (toWord n)]) := by
    simp +decide [WF, Prim.dst, yV, yDs, yN]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const yV 0, .const yDs (toWord dst), .const yN (toWord n)]) s
  have r0 : rd (semXIR I (.blk [.const yV 0, .const yDs (toWord dst), .const yN (toWord n)]) s).M
        yV = 0 ∧
      rd (semXIR I (.blk [.const yV 0, .const yDs (toWord dst), .const yN (toWord n)]) s).M yDs =
        toWord dst ∧
      rd (semXIR I (.blk [.const yV 0, .const yDs (toWord dst), .const yN (toWord n)]) s).M yN =
        toWord n := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yV, yDs, yN]; (clear * - s I n dst hs z0; omega))) only [rd_set_self, rd_set_ne]
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk [.const yV 0, .const yDs (toWord dst),
      .const yN (toWord n)]) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, yV, yDs, yN] <;> (clear * - hr; omega)
  generalize semXIR I (.blk [.const yV 0, .const yDs (toWord dst), .const yN (toWord n)]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨v0, d0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M yV = 0 ∧ rd s'.M yDs = toWord (dst + j) ∧ (∀ i < j, rd s'.M (dst + i) = 0) ∧
    (∀ r, regs ≤ r → (r < dst ∨ dst + j ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC → i ≠ cTmp → rd (entryK yC yN (toWord n) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC yN (toWord n) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun i hi => absurd hi (by (clear * - hi; omega)), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), v0]
    · rw [hE _ (by decide) (by decide), d0, Nat.add_zero]
    · simp only [regs] at hr
      rw [hE _ (by simp only [yC]; (clear * - hr; omega)) (by simp only [cTmp]; (clear * - hr; omega)), k0 r (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < n → P j s' → P (j + 1) (decS yC (semXIR I zeroBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    rw [zeroBody, semXIR_seq]
    obtain ⟨c1, c2, hM1⟩ := store_sem I s' i1 (p := yDs) (v := yV) (x := dst + j) (by decide)
      (by decide) i4 (by simp only [regs]; (clear * - hdst; omega)) (by (clear * - hdst2 hj; omega)) (by (clear * - hdsts z0 h0 hj i2; omega))
    have z1 := size_sem I (.store yDs yV) s'
    generalize semXIR I (.store yDs yV) s' = s1 at c1 c2 hM1 z1
    have hs1 := hM1.1
    simp only [regs] at hs1
    have hdr : ∀ r, r < regs → r ≠ dst + j := fun r hr => by simp only [regs] at hr; (clear * - hn hdst hdst2 hj hr; omega)
    have b2 : ∀ r, r ≠ yDs → rd (semXIR I (.blk [.op .add yDs yDs cOne]) s1).M r = rd s1.M r :=
      fun r hr => rd_blk_of_not_dst I _ s1 (by simp [Prim.dst]; exact Ne.symm hr)
    have hM2 := inv_sem I (P := .blk [.op .add yDs yDs cOne]) (by simp +decide [WF, Prim.dst, yDs]) hM1
    have hd : ∀ x, x ≠ yC → rd (decS yC (semXIR I (.blk [.op .add yDs yDs cOne]) s1)).M x =
        rd (semXIR I (.blk [.op .add yDs yDs cOne]) s1).M x := fun x hx => rd_decS (Ne.symm hx) _
    have hx : ∀ x, regs ≤ x → x ≠ yC ∧ x ≠ yDs ∧ x ≠ cTmp := fun x hx => by
      simp only [regs, yC, yDs, cTmp] at *; (clear * - hx; omega)
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, z1, i2], ?_, ?_,
      fun i hi => ?_, fun r hr hr2 => ?_⟩
    · rw [hd _ (by decide), b2 _ (by decide), c2 _ (hdr _ (by decide)) (by decide), i3]
    · rw [hd _ (by decide), sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [yDs]; (clear * - hs z0 h0 i2 z1; omega)), c2 _ (hdr _ (by decide)) (by decide), i4,
        c2 _ (hdr _ (by decide)) (by decide), show rd s'.M cOne = 1 from i1.2 0 (by decide),
        add_one_toWord, Nat.add_assoc]
    · obtain ⟨x1, x2, x3⟩ := hx (dst + i) (by simp only [regs]; (clear * - hdst; omega))
      rw [hd _ x1, b2 _ x2]
      by_cases hij : i = j
      · subst hij; rw [c1, i3]
      · rw [c2 _ (by (clear * - hij; omega)) x3, i5 i (by (clear * - hi hij; omega))]
    · obtain ⟨x1, x2, x3⟩ := hx r hr
      rw [hd _ x1, b2 _ x2, c2 _ (by (clear * - hn hj hr2 x1 x2 x3; omega)) x3, i6 r hr (by (clear * - hr2 x1 x2 x3; omega))]
  have hfin := loopK_run I zeroBody P s0 hM0 (c := yC) (n := yN) (K := n) (by decide) (by decide)
    (by decide) n0 hn h0 hstep
  exact ⟨hfin.2.2.2.2.1, hfin.2.2.2.2.2, hfin.1⟩

end Lvm.X
