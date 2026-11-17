-- adapted from rf-k/submissions/flock-recursive/lean/FRXFwd.lean@8bff272b (section G6_FRXBfly:
-- alphaBody_sem … bflyIR_sem).
-- New for lvm (WP-13b); namespace `FR.X` → `Lvm.X`. Re-targeted from FR's two-word `F` to lvm's
-- one-word `K = BF64` (`ldF_sem`/`stF_sem` → `load_sem`/`store_sem`, `rdF_eq` → `rdK_eq`, element
-- stride 2 → 1, table row stride 40 → 15, 20 bits → 15).
import LvmXNtt

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmXSComputesOff`, outside its import closure.)

/-!
# The inverse additive NTT on the machine: the semantics

* **`alphaIR_sem`**: `α = Σ_{i<15} [bit_i(base)] T(i)`, i.e. `wAt ptK 15 l base` on the table row
  of level `l` (`alphaIR_wAt`).
* `arith_sem`, `pairPs_sem`, **`pairBody_sem`**: one butterfly; **`levelIR_sem`**: one level
  (`bflyLevel`).
* **`bflyIR_sem`**: from the row `Y` of `2^ℓ` elements at `A` and the basis table at `tb`, the
  program leaves `bflyRun ptK 15 0 ℓ Y` in the row and keeps the heap outside it;
  `bflyIR_coeffs`: that is `coeffsAt ptK 15 ℓ 0 Y`, the novel-basis coefficients of the values.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

/-! ## One-word helpers -/

theorem rdK_eq {M M' : Mem} {a b : ℕ} (h : rd M a = rd M' b) : rdK M a = rdK M' b := by
  rw [rdK, rdK, h]

theorem rdK_decS {c a : ℕ} (s : St) (h0 : c ≠ a) : rdK (decS c s).M a = rdK s.M a :=
  rdK_eq (rd_decS h0 s)

theorem addK_frame (I : Array Word) (s : St) {d a b i : ℕ} (h : i ≠ d) :
    rd (semXIR I (addK d a b) s).M i = rd s.M i := xorC_frame d a b h s.M

theorem mulK_frame (I : Array Word) (s : St) {d a b i : ℕ} (h0 : 9 ≤ i) (h1 : i ≠ d) :
    rd (semXIR I (mulK d a b) s).M i = rd s.M i := by
  rw [mulK, sem_blk]; exact mulKC_frame _ _ _ (.inr h0) h1 _

/-- Masked accumulation of a `K` element. -/
theorem wK_acc (a g : Word) (p : Prop) [Decidable p] :
    wK (a ^^^ (if p then g else 0)) = wK a + if p then wK g else 0 := by
  by_cases h : p
  · simp only [if_pos h]; rfl
  · simp only [if_neg h, add_zero, xor_zero']

/-! ## `α` -/

/-! ## One butterfly on the machine -/

theorem lo_arithIR : Lo arithIR := by
  simp +decide only [arithIR, addK, Lo, Prim.dst, fU, fW, fH, fT, fN, mulK_lo_iff,
    List.mem_cons, List.mem_nil_iff, forall_eq, or_false, and_true]

/-- **The arithmetic**: `fN := U + α (W + U)`, `fH := W + U` for the heap elements `U` at `a`
and `W` at `b`, `α` in `fAl`. -/
theorem arith_sem (I : Array Word) (s : St) (hM : Inv s.M) {a b : ℕ}
    (ha2 : a < 2 ^ 64) (hb : regs ≤ b) (hb2 : b < 2 ^ 64)
    (hAL : rd s.M rAL = toWord a) (hAH : rd s.M rAH = toWord b) :
    rdK (semXIR I arithIR s).M fN = rdK s.M a + rdK s.M fAl * (rdK s.M b + rdK s.M a) ∧
    rdK (semXIR I arithIR s).M fH = rdK s.M b + rdK s.M a := by
  have hs := hM.1
  simp only [regs] at hs hb
  rw [arithIR, semXIR_seq]
  obtain ⟨u1, u3, hM1⟩ := load_sem I s hM (d := fU) (p := rAL) (by decide) (by decide) hAL ha2
  generalize semXIR I (.load fU rAL) s = s1 at u1 u3 hM1
  have hAH1 : rd s1.M rAH = toWord b := (u3 _ (by decide)).trans hAH
  have hal1 : rdK s1.M fAl = rdK s.M fAl := rdK_eq (u3 _ (by decide))
  have hb1 : rdK s1.M b = rdK s.M b := rdK_eq (u3 _ (by simp only [fU]; omega))
  rw [semXIR_seq]
  obtain ⟨w1, w3, hM2⟩ := load_sem I s1 hM1 (d := fW) (p := rAH) (by decide) (by decide) hAH1 hb2
  generalize semXIR I (.load fW rAH) s1 = s2 at w1 w3 hM2
  have hu2 : rdK s2.M fU = rdK s.M a := (rdK_eq (w3 _ (by decide))).trans (rdK_eq u1)
  have hal2 : rdK s2.M fAl = rdK s.M fAl := (rdK_eq (w3 _ (by decide))).trans hal1
  have hw2 : rdK s2.M fW = rdK s.M b := (rdK_eq w1).trans hb1
  rw [semXIR_seq]
  have h3 := addK_sem (I := I) (s := s2) hM2 (d := fH) (a := fW) (b := fU) (by decide)
  have f3 : ∀ i, i ≠ fH → rd (semXIR I (addK fH fW fU) s2).M i = rd s2.M i :=
    fun i h => addK_frame I s2 h
  have hM3 := inv_sem I (wf_addK fH fW fU (by decide)) hM2
  generalize semXIR I (addK fH fW fU) s2 = s3 at h3 f3 hM3
  rw [semXIR_seq]
  have h4 := mulK_sem (I := I) (s := s3) hM3 (d := fT) (a := fAl) (b := fH) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 9 ≤ i → i ≠ fT → rd (semXIR I (mulK fT fAl fH) s3).M i = rd s3.M i :=
    fun i h0 h1 => mulK_frame I s3 h0 h1
  have hM4 := inv_sem I (wf_mulK fT fAl fH (by decide)) hM3
  have hu3 : rdK s3.M fU = rdK s.M a := (rdK_eq (f3 _ (by decide))).trans hu2
  have hal3 : rdK s3.M fAl = rdK s.M fAl := (rdK_eq (f3 _ (by decide))).trans hal2
  generalize semXIR I (mulK fT fAl fH) s3 = s4 at h4 f4 hM4
  have h5 := addK_sem (I := I) (s := s4) hM4 (d := fN) (a := fU) (b := fT) (by decide)
  have hu4 : rdK s4.M fU = rdK s.M a := (rdK_eq (f4 _ (by decide) (by decide))).trans hu3
  have hh4 : rdK s4.M fH = rdK s.M b + rdK s.M a := by
    rw [rdK_eq (f4 _ (by decide) (by decide)), h3, hw2, hu2]
  refine ⟨?_, ?_⟩
  · rw [h5, h4, hu4, hal3, h3, hw2, hu2]
  · rw [← hh4]; exact rdK_eq (addK_frame I s4 (by decide))

/-- **The pair's addresses.** -/
theorem pairPs_sem (I : Array Word) (s : St) (hM : Inv s.M) {A l q : ℕ} (hq : q < 2 ^ 64)
    (hP : 2 ^ l < 2 ^ 64) (hQ : rd s.M rQ = toWord q) (hP2 : rd s.M rP2 = toWord (2 ^ l))
    (hA0 : rd s.M rA0 = toWord A) :
    rd (semXIR I (.blk pairPs) s).M rBs = toWord (baseP l q) ∧
    rd (semXIR I (.blk pairPs) s).M rAL = toWord (A + loP l q) ∧
    rd (semXIR I (.blk pairPs) s).M rAH = toWord (A + hiP l q) := by
  have hs := hM.1
  simp only [regs] at hs
  have e : q / 2 ^ l * (2 ^ l + 2 ^ l) = baseP l q := by rw [baseP, two_pow_succ_eq]
  simp only [semXIR, runPrims, pairPs, List.foldl, Prim.run]
  refine ⟨?_, ?_, ?_⟩ <;>
  simp (disch := first | decide | (simp only [size_set, uT1, uX, uT2, rBs, rAL, rAH]; omega)) only
    [rd_set_self, rd_set_ne] <;>
  simp only [hQ, hP2, hA0, divu_toWord hq hP, remu_toWord hq hP, add_toWord, mul_toWord, e]
  all_goals first | rfl | (congr 1; simp only [hiP, loP]; ring)

/-! ## A level, and the iteration -/

end Lvm.X
