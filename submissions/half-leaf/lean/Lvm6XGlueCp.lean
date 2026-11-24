-- lvm6 EXG (DP6 §2 item 2): the scatter copy `scpIR n src str dst` (`M[dst + str·i] := M[src + i]`, `i < n`), the
-- mirror of season 1's `mcpIR` (LvmXCopy: `M[dst + i] := M[src + str·i]`) with the stride on the destination; the
-- level glue interleaves a decoded tuple's lanes with it. Proofs follow `mcpBody_sem`/`mcpLoop_sem`/`mcpIR_sem`. New.
import Lvm6XDescProg

/-!
# The scatter copy

* `scpBody`: `M[yDs] := M[ySr]`, `ySr += 1`, `yDs += yStr`; `scpLoop n`, `scpIR n src str dst` (the pointers set).
* **`scpIR_sem`**: `n` words `M[dst + str·i] := M[src + i]`; every other heap cell kept; `Inv`.
* `cost_scpIR` (`16 + 13 n`), `sizeIR_scpIR` (`30`), `wf_scpIR`, `noLoopT_scpIR`, `outs_scpIR`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X

attribute [local irreducible] entryK storeM

/-- One word: `M[yDs] := M[ySr]`, `ySr += 1`, `yDs += yStr`. -/
def scpBody : XIR :=
  .seq (.load yV ySr) (.seq (.store yDs yV) (.blk [.op .add ySr ySr cOne, .op .add yDs yDs yStr]))

/-- `n` words from the pointers in `ySr`, `yDs`, `yStr`. -/
def scpLoop (n : ℕ) : XIR := .seq (.blk [.const yN (toWord n)]) (.loopK yC yN (toWord n) scpBody)

/-- **The scatter copy** `M[dst + str·i] := M[src + i]`, `i < n`. -/
def scpIR (n src str dst : ℕ) : XIR :=
  .seq (.blk [.const ySr (toWord src), .const yStr (toWord str), .const yDs (toWord dst)]) (scpLoop n)

theorem wf_scpIR (n src str dst : ℕ) : WF (scpIR n src str dst) := by
  simp +decide [scpIR, scpLoop, scpBody, WF, Writes, Prim.dst, ySr, yDs, yStr, yV, yC, yN, cTmp]

theorem noLoopT_scpIR (n src str dst : ℕ) : NoLoopT (scpIR n src str dst) := by
  simp [scpIR, scpLoop, scpBody, NoLoopT]

theorem outs_scpIR (n src str dst t : ℕ) : outs (scpIR n src str dst) t = 0 := by
  simp [scpIR, scpLoop, scpBody, outs]

theorem cost_scpIR (n src str dst t : ℕ) (hn : n < 2 ^ 64) : cost (scpIR n src str dst) t = 16 + 13 * n := by
  simp only [scpIR, scpLoop, scpBody, cost, blkSteps, List.length_cons, List.length_nil, toNat_toWord hn]
  norm_num; ring

theorem sizeIR_scpIR (n src str dst : ℕ) : sizeIR (scpIR n src str dst) = 30 := rfl

/-- **One scattered word**: `M[d] := M[a]`, `ySr := a + 1`, `yDs := d + k`. -/
theorem scpBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {a d k : ℕ} (ha2 : a + 1 < 2 ^ 64)
    (hd : regs ≤ d) (hd2 : d + k < 2 ^ 64) (hds : d < s.M.size)
    (hS : rd s.M ySr = toWord a) (hD : rd s.M yDs = toWord d) (hK : rd s.M yStr = toWord k) :
    rd (semXIR I scpBody s).M d = rd s.M a ∧
    rd (semXIR I scpBody s).M ySr = toWord (a + 1) ∧
    rd (semXIR I scpBody s).M yDs = toWord (d + k) ∧
    (∀ r, r ≠ yV → r ≠ ySr → r ≠ yDs → r ≠ cTmp → r ≠ d → rd (semXIR I scpBody s).M r = rd s.M r) ∧
    Inv (semXIR I scpBody s).M := by
  have hs := hM.1
  simp only [regs] at hs hd
  rw [scpBody, semXIR_seq]
  obtain ⟨l1, l2, hM1⟩ := load_sem I s hM (d := yV) (p := ySr) (by decide) (by decide) hS
    (by (clear * - ha2; omega))
  have z1 := size_sem I (.load yV ySr) s
  generalize semXIR I (.load yV ySr) s = s1 at l1 l2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := yDs) (v := yV) (x := d) (by decide) (by decide)
    (by rw [l2 _ (by decide), hD]) (by simp only [regs]; (clear * - hd; omega)) (by (clear * - hd hd2; omega))
    (by (clear * - hds z1; omega))
  have z2 := size_sem I (.store yDs yV) s1
  generalize semXIR I (.store yDs yV) s1 = s2 at c1 c2 hM2 z2
  have hdr : ∀ r, r < regs → r ≠ d := fun r hr => by simp only [regs] at hr; (clear * - hd hd2 hr; omega)
  have e2 : ∀ r, r ≠ yV → r ≠ cTmp → r ≠ d → rd s2.M r = rd s.M r := fun r h1 h2 h3 =>
    (c2 r h3 h2).trans (l2 r h1)
  have h1 : rd s2.M cOne = 1 := hM2.2 0 (by decide)
  refine ⟨?_, ?_, ?_, fun r r1 r2 r3 r4 r5 => ?_, inv_sem I (P := .blk [.op .add ySr ySr cOne,
    .op .add yDs yDs yStr]) (by simp +decide [WF]) hM2⟩
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, ySr, yDs]; (clear * - hd hd2; omega)), c1, l1]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [ySr]; (clear * - hs z1 z2; omega)),
      e2 _ (by decide) (by decide) (hdr _ (by decide)), h1, hS, add_one_toWord]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, yDs]; (clear * - hs z1 z2; omega)), rd_set_ne (by decide),
      rd_set_ne (by decide), e2 _ (by decide) (by decide) (hdr _ (by decide)),
      e2 _ (by decide) (by decide) (hdr _ (by decide)), hD, hK, add_toWord]
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact ⟨Ne.symm r2, Ne.symm r3⟩), e2 r r1 r4 r5]

/-- **The scatter loop**: from `ySr = src`, `yDs = dst`, `yStr = str`, `n` words `M[dst + str·i] := M[src + i]`. -/
theorem scpLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {n src str dst : ℕ} (hs1 : 0 < str)
    (hn : n < 2 ^ 64) (hsrc2 : src + n < 2 ^ 64) (hdst : regs ≤ dst) (hdst2 : dst + str * n < 2 ^ 64)
    (hdsts : ∀ i < n, dst + str * i < s.M.size) (hdisj : ∀ i < n, ∀ i' < n, src + i ≠ dst + str * i')
    (hsrcR : regs ≤ src)
    (hS : rd s.M ySr = toWord src) (hD : rd s.M yDs = toWord dst) (hK : rd s.M yStr = toWord str) :
    (∀ i < n, rd (semXIR I (scpLoop n) s).M (dst + str * i) = rd s.M (src + i)) ∧
    (∀ r, KeepC r → (∀ i < n, r ≠ dst + str * i) → rd (semXIR I (scpLoop n) s).M r = rd s.M r) ∧
    Inv (semXIR I (scpLoop n) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdst hsrcR
  rw [scpLoop, semXIR_seq]
  have hM0 := inv_sem I (P := .blk [.const yN (toWord n)]) (by simp +decide [WF, Prim.dst, yN]) hM
  have n0 : rd (semXIR I (.blk [.const yN (toWord n)]) s).M yN = toWord n := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [yN]; (clear * - hs; omega))]
  have k0 : ∀ r, r ≠ yN → rd (semXIR I (.blk [.const yN (toWord n)]) s).M r = rd s.M r :=
    fun r hr => rd_blk_of_not_dst I _ s (by simp [Prim.dst]; exact Ne.symm hr)
  have z0 := size_sem I (.blk [.const yN (toWord n)]) s
  generalize semXIR I (.blk [.const yN (toWord n)]) s = s0 at hM0 n0 k0 z0
  have hmono : ∀ i j, i < j → str * i < str * j := fun i j h => Nat.mul_lt_mul_of_pos_left h hs1
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M ySr = toWord (src + j) ∧ rd s'.M yDs = toWord (dst + str * j) ∧
    rd s'.M yStr = toWord str ∧ (∀ i < j, rd s'.M (dst + str * i) = rd s.M (src + i)) ∧
    (∀ r, KeepC r → (∀ i < j, r ≠ dst + str * i) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC → i ≠ cTmp → rd (entryK yC yN (toWord n) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC yN (toWord n) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_, ?_,
      fun i hi => absurd hi (by (clear * - hi; omega)), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hS, Nat.add_zero]
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hD, Nat.mul_zero, Nat.add_zero]
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hK]
    · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
      rw [hE _ r4 r6, k0 _ r5]
  have hstep : ∀ j s', j < n → P j s' → P (j + 1) (decS yC (semXIR I scpBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hsj : dst + str * j + str ≤ dst + str * n := by
      have := Nat.mul_le_mul_left str (show j + 1 ≤ n by (clear * - hj; omega))
      rw [Nat.mul_succ] at this; (clear * - this; omega)
    have hdj := hdsts j hj
    obtain ⟨b1, b2, b3, b4, hM'⟩ := scpBody_sem I s' i1 (a := src + j) (d := dst + str * j)
      (k := str) (by (clear * - hsrc2 hj; omega)) (by simp only [regs]; (clear * - hdst; omega))
      (by (clear * - hdst2 hsj; omega)) (by (clear * - hdj i2; omega)) i3 i4 i5
    have hd : ∀ x, x ≠ yC → rd (decS yC (semXIR I scpBody s')).M x =
        rd (semXIR I scpBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], ?_, ?_, ?_,
      fun i hi => ?_, fun r hr hr2 => ?_⟩
    · rw [hd _ (by decide), b2, Nat.add_assoc]
    · rw [hd _ (by decide), b3, Nat.mul_succ, Nat.add_assoc]
    · rw [hd _ (by decide), b4 _ (by decide) (by decide) (by decide) (by decide)
        (by simp only [yStr] at *; (clear * - hdst; omega)), i5]
    · have hdx : ∀ x, regs ≤ x → x ≠ yC := fun x hx => by simp only [yC, regs] at *; (clear * - hx; omega)
      rw [hd _ (hdx _ (by simp only [regs]; (clear * - hdst; omega)))]
      by_cases hij : i = j
      · subst hij
        rw [b1, i7 _ (keepC_of_regs (show regs ≤ src + i by simp only [regs]; (clear * - hsrcR; omega)))
          (fun i' hi' => hdisj i hj i' (by (clear * - hi' hj; omega)))]
      · have hk := keepC_of_regs (show regs ≤ dst + str * i by simp only [regs]; (clear * - hdst; omega))
        have hne : dst + str * i ≠ dst + str * j := by
          rcases Nat.lt_or_gt_of_ne hij with h | h
          · have := hmono i j h; (clear * - this; omega)
          · have := hmono j i h; (clear * - this; omega)
        rw [b4 _ hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.2.2 hne, i6 i (by (clear * - hi hij; omega))]
    · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
      rw [hd _ r4, b4 r r1 r2 r3 r6 (hr2 j (by (clear * - hj; omega))),
        i7 r ⟨r1, r2, r3, r4, r5, r6⟩ (fun i hi => hr2 i (by (clear * - hi; omega)))]
  have hfin := loopK_run I scpBody P s0 hM0 (c := yC) (n := yN) (K := n) (by decide) (by decide)
    (by decide) n0 hn h0 hstep
  exact ⟨hfin.2.2.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2.2.2 r hr hr2, hfin.1⟩

/-- **The scatter copy**: `n` words `M[dst + str·i] := M[src + i]`; every other heap cell kept. -/
theorem scpIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n src str dst : ℕ} (hs1 : 0 < str)
    (hn : n < 2 ^ 64) (hsrc2 : src + n < 2 ^ 64) (hsrcR : regs ≤ src) (hdst : regs ≤ dst)
    (hdst2 : dst + str * n < 2 ^ 64) (hdsts : ∀ i < n, dst + str * i < s.M.size)
    (hdisj : ∀ i < n, ∀ i' < n, src + i ≠ dst + str * i') :
    (∀ i < n, rd (semXIR I (scpIR n src str dst) s).M (dst + str * i) = rd s.M (src + i)) ∧
    (∀ r, regs ≤ r → (∀ i < n, r ≠ dst + str * i) → rd (semXIR I (scpIR n src str dst) s).M r = rd s.M r) ∧
    Inv (semXIR I (scpIR n src str dst) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdst hsrcR
  rw [scpIR, semXIR_seq]
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
  obtain ⟨a1, a2, a3⟩ := scpLoop_sem I s0 hM0 hs1 hn hsrc2 (by simp only [regs]; (clear * - hdst; omega)) hdst2
    (fun i hi => by rw [z0]; exact hdsts i hi) hdisj (by simp only [regs]; (clear * - hsrcR; omega))
    r0.1 r0.2.1 r0.2.2
  refine ⟨fun i hi => ?_, fun r hr hr2 => ?_, a3⟩
  · rw [a1 i hi, k0 _ (by simp only [regs]; (clear * - hsrcR; omega))]
  · rw [a2 r (keepC_of_regs hr) hr2, k0 r hr]

end Lvm6.X
