-- adapted from rf-k/submissions/flock-recursive/lean/FRXFwd.lean@8bff272b (section G6_FRXFwd:
-- farith_sem … fwdIR_enc).
-- New for lvm (WP-13b); namespace `FR.X` → `Lvm.X`. Re-targeted from FR's two-word `F` and
-- domain `D` to lvm's one-word `K = BF64` and domain `ptK` (`ldF_sem`/`stF_sem` →
-- `load_sem`/`store_sem`, element stride 2 → 1, table row stride 40 → 15).
import LvmXNtt2

-- (GOLF2: 7 declarations that `certified` does not use moved verbatim to `LvmXTopOff`, outside its import closure.)

/-!
# The forward additive NTT on the machine (`Enc` of a message)

The program `fwdIR ℓ tb` runs the levels `ℓ − 1, …, 0` of `Lvm.Nb.fwdRun` in place on a row of
`2^ℓ` `K` elements at `rA0`. It reuses the inverse NTT's pair addresses (`pairPs`), `α`
(`alphaIR`) and the basis table (`wtabIR`). Two things differ:
- the arithmetic `farithIR`: `lo := u + α w`, `hi := u + α w + w`;
- the level order: `rLv := rKf − 1` with `rKf = ℓ − j` counting down, and `rTr := tb + 15·rLv`.

* `fpairBody_sem`, `flevelIR_sem`: one forward butterfly, one level (`fwdLevel`).
* **`fwdIR_sem`**: the row ends holding `fwdRun ptK 15 ℓ Y`; the heap outside it is kept.
* **`fwdIR_enc`**: on a message of `2^m` coefficients zero-padded to `2^ℓ`, the row ends holding
  `encN ptK c` (`Lvm.Nb.fwdRun_enc`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM runPrims

theorem lo_farithIR : Lo farithIR := by
  simp +decide only [farithIR, addK, Lo, Prim.dst, fU, fW, fH, fT, fN, mulK_lo_iff,
    List.mem_cons, List.mem_nil_iff, forall_eq, or_false, and_true]

/-- **The forward arithmetic**: `fN := U + α W`, `fH := U + α W + W` for the heap elements `U`
at `a` and `W` at `b`, `α` in `fAl`. -/
theorem farith_sem (I : Array Word) (s : St) (hM : Inv s.M) {a b : ℕ}
    (ha2 : a < 2 ^ 64) (hb : regs ≤ b) (hb2 : b < 2 ^ 64)
    (hAL : rd s.M rAL = toWord a) (hAH : rd s.M rAH = toWord b) :
    rdK (semXIR I farithIR s).M fN = rdK s.M a + rdK s.M fAl * rdK s.M b ∧
    rdK (semXIR I farithIR s).M fH = rdK s.M a + rdK s.M fAl * rdK s.M b + rdK s.M b := by
  have hs := hM.1
  simp only [regs] at hs hb
  rw [farithIR, semXIR_seq]
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
  have h3 := mulK_sem (I := I) (s := s2) hM2 (d := fT) (a := fAl) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f3 : ∀ i, 9 ≤ i → i ≠ fT → rd (semXIR I (mulK fT fAl fW) s2).M i = rd s2.M i :=
    fun i h0 h1 => mulK_frame I s2 h0 h1
  have hM3 := inv_sem I (wf_mulK fT fAl fW (by decide)) hM2
  generalize semXIR I (mulK fT fAl fW) s2 = s3 at h3 f3 hM3
  have hu3 : rdK s3.M fU = rdK s.M a := (rdK_eq (f3 _ (by decide) (by decide))).trans hu2
  have hw3 : rdK s3.M fW = rdK s.M b := (rdK_eq (f3 _ (by decide) (by decide))).trans hw2
  rw [semXIR_seq]
  have h4 := addK_sem (I := I) (s := s3) hM3 (d := fN) (a := fU) (b := fT) (by decide)
  have f4 : ∀ i, i ≠ fN → rd (semXIR I (addK fN fU fT) s3).M i = rd s3.M i :=
    fun i h => addK_frame I s3 h
  have hM4 := inv_sem I (wf_addK fN fU fT (by decide)) hM3
  generalize semXIR I (addK fN fU fT) s3 = s4 at h4 f4 hM4
  have hw4 : rdK s4.M fW = rdK s.M b := (rdK_eq (f4 _ (by decide))).trans hw3
  have hn4 : rdK s4.M fN = rdK s.M a + rdK s.M fAl * rdK s.M b := by rw [h4, hu3, h3, hal2, hw2]
  have h5 := addK_sem (I := I) (s := s4) hM4 (d := fH) (a := fN) (b := fW) (by decide)
  refine ⟨?_, ?_⟩
  · rw [← hn4]; exact rdK_eq (addK_frame I s4 (by decide))
  · rw [h5, hn4, hw4]

/-! ## The forward NTT -/

end Lvm.X
