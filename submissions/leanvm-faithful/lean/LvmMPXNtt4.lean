-- New for lvm2 roll 11 (M′, R11-X): the forward NTT's semantics at any table dimension `N`. Adapted from
-- `LvmXNtt4.lean` (`fpairBody_nw`, `fpairBody_sem`, `flevelIR_sem`, `flevelIR_nw`, `fPre_sem`, `fwdIR_sem`,
-- `fwdIR_enc`) with the literal `15` replaced by `N`; `lo_farithIR`, `farith_sem` are reused.
import LvmXNtt4
import LvmMPXNtt
import LvmXNtt2
import LvmXNtt3

-- ===== merged from `LvmMPXNtt2` (GOLF module merge: `LvmMPXNtt2.lean` is now a stub importing `LvmMPXNtt4`) =====
section
-- New for lvm2 roll 11 (M′, R11-X): the inverse NTT's semantics at any table dimension `N`. Adapted from
-- `LvmXNtt2.lean` (`loK_alphaIR`, `alphaBody_sem`, `alphaIR_sem`, `alphaIR_wAt`, `pairBody_nw`, `pairBody_sem`,
-- `levelIR_sem`, `levelIR_nw`, `bflyIR_sem`, `bflyIR_coeffs`) with the literal `15` (bits, row stride,
-- `nLog`) replaced by `N`; the shape-free helpers (`rdK_eq`, `arith_sem`, `pairPs_sem`, …) are reused.

/-!
# The inverse additive NTT at table dimension `N`: the semantics

* `alphaNIR_sem`, `alphaNIR_wAt`: `α = wAt ptK N l base` from the table row of level `l`;
* `pairNBody_sem`, `levelNIR_sem`: one butterfly, one level (`bflyLevel ptK N`);
* **`bflyNIR_sem`**, **`bflyNIR_coeffs`**: `(bflyNIR N ℓ tb)` (`ℓ ≤ N`) leaves `coeffsAt ptK N ℓ 0 Y` in the row,
  from the basis table (`wRow ptK N v` at `tb + N v + i`).
-/

namespace Lvm.X

variable {N : ℕ}

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

/-- Proof help: `rd_runPrims_of_not_writes` stated on `semXIR … (.blk ps)`, so that a concrete `ps` is matched
syntactically instead of by unfolding `runPrims` over it (elaboration: `fPreN_sem` 16 s of defeq). -/
theorem rd_blkN_of_not_writes (I : Array Word) (ps : List Prim) (s : St) {i : ℕ}
    (h : ∀ p ∈ ps, p.dst ≠ i) : rd (semXIR I (.blk ps) s).M i = rd s.M i :=
  rd_runPrims_of_not_writes h s.M

theorem wf_pairNBody (N : ℕ) : WF (pairNBody N) := by
  simp +decide [pairNBody, pairPs, arithIR, alphaNIR, alphaBody, addK, WF, Writes, Prim.dst, rQ,
    uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, regs,
    mulK_wf_iff, mulK_writes_iff]

/-! ## `α` -/

theorem loK_alphaNIR : LoK (alphaNIR N) := by
  simp +decide [alphaNIR, alphaBody, LoK, Prim.dst, regs, rBit, uT1, rTa, fG, fAl, uI, rN2,
    rC2, and_true]

/-- **One bit of `α`.** -/
theorem alphaBody_semN (I : Array Word) (s : St) (hM : Inv s.M) {base ta j : ℕ} {T : ℕ → BF64}
    (hb : base < 2 ^ 64) (hj : j < N) (hj64 : j < 64) (hta : regs ≤ ta) (hta2 : ta + N < 2 ^ 64)
    (hBs : rd s.M rBs = toWord base) (hI : rd s.M uI = toWord j)
    (hTa : rd s.M rTa = toWord (ta + j)) (hT : rdK s.M (ta + j) = T j) :
    rdK (semXIR I alphaBody s).M fAl = rdK s.M fAl + (if base.testBit j then T j else 0) ∧
    rd (semXIR I alphaBody s).M uI = toWord (j + 1) ∧
    rd (semXIR I alphaBody s).M rTa = toWord (ta + (j + 1)) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hta
  have w1 : WF (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
      .op .sub rBit uT1 rBit]) := by simp +decide [WF, Prim.dst, rBit, uT1]
  have hM1 := inv_sem I w1 hM
  have hH1 := hframe I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
      .op .sub rBit uT1 rBit]) s (by simp +decide [Lo, Prim.dst, regs, rBit, uT1])
  have r1 : rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M rBit =
        XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord base) (toWord j)) 1) ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M rTa = toWord (ta + j) ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M uI = toWord j ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M fAl = rd s.M fAl ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M cOne = 1 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rBit, uT1]; (clear * - s N base ta j hs; omega))) only
      [rd_set_self, rd_set_ne]
    · rw [hBs, hI, h1]
    · exact hTa
    · exact hI
    · exact h1
  rw [alphaBody, semXIR_seq]
  generalize semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
    .op .sub rBit uT1 rBit]) s = s1 at hM1 hH1 r1
  obtain ⟨b1, a1, i1, f1, o1⟩ := r1
  obtain ⟨l1, l2, hM2⟩ := load_sem I s1 hM1 (d := fG) (p := rTa) (x := ta + j) (by decide)
    (by decide) a1 (by (clear * - hj hta2; omega))
  rw [semXIR_seq]
  generalize semXIR I (.load fG rTa) s1 = s2 at l1 l2 hM2
  have hs2 := hM2.1
  simp only [regs] at hs2
  have g2 : wK (rd s2.M fG) = T j := by
    rw [← hT]; exact rdK_eq (l1.trans (hH1 _ (by simp only [regs]; (clear * - hj64 hta hta2; omega))))
  have k1 : rd s2.M rBit = XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord base) (toWord j)) 1) :=
    (l2 _ (by decide)).trans b1
  have k2 : rd s2.M fAl = rd s.M fAl := (l2 _ (by decide)).trans f1
  have k4 : rd s2.M rTa = toWord (ta + j) := (l2 _ (by decide)).trans a1
  have k5 : rd s2.M uI = toWord j := (l2 _ (by decide)).trans i1
  have k6 : rd s2.M cOne = 1 := (l2 _ (by decide)).trans o1
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_, ?_⟩
  · simp only [rdK]
    simp (disch := first | decide | (simp only [size_set, fG, fAl, rTa, uI]; (clear * - s2 N s base ta j hs2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [k1, k2, eval_xor, mask_bit _ hb (by (clear * - hj64; omega)), wK_acc, g2]
  · simp (disch := first | decide | (simp only [size_set, fG, fAl, rTa, uI]; (clear * - s2 N s base ta j hs2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [k5, k6, add_one_toWord]
  · simp (disch := first | decide | (simp only [size_set, fG, fAl, rTa, uI]; (clear * - s2 N s base ta j hs2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [k4, k6, add_one_toWord]
    rfl

/-- **`α`**: the sum over the bits `i < N` of `base` of the table entries `T i` at `ta + i`
(the row at `rTr`). -/
theorem alphaNIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {base ta : ℕ} {T : ℕ → BF64}
    (hb : base < 2 ^ 64) (hta : regs ≤ ta) (hta2 : ta + N < 2 ^ 64)
    (hBs : rd s.M rBs = toWord base) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < N, rdK s.M (ta + i) = T i) :
    rdK (semXIR I (alphaNIR N) s).M fAl = ∑ i ∈ range N, if base.testBit i then T i else 0 := by
  have hs := hM.1
  simp only [regs] at hs hta
  have w0 : WF (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) := by
    simp +decide [WF, Prim.dst, fAl, uI, rTa, rN2]
  have hM0 := inv_sem I w0 hM
  have hH0 := hframe I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s
    (by simp +decide [Lo, Prim.dst, regs, fAl, uI, rTa, rN2])
  have r0 : rdK (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 (toWord N)]) s).M fAl = 0 ∧
      rd (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 (toWord N)]) s).M uI = toWord 0 ∧
      rd (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 (toWord N)]) s).M rTa = toWord (ta + 0) ∧
      rd (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 (toWord N)]) s).M rBs = toWord base ∧
      rd (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 (toWord N)]) s).M rN2 = toWord N := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, rdK]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, fAl, uI, rTa, rN2]; (clear * - s N base ta hs; omega))) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rfl
    · rw [hTr, or_self_eval]; rfl
    · exact hBs
  rw [alphaNIR, semXIR_seq]
  generalize semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s
    = s0 at hM0 hH0 r0
  obtain ⟨z0, i0, t0, b0, n0⟩ := r0
  rw [loopK_eq I alphaBody s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord (show N < 2 ^ 64 by (clear * - hN; omega))]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 (toWord N) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := toWord N) hM0 (by decide)
  have wb : WF alphaBody := (wf_alphaNIR N).2.2.2.2
  have lb : LoK alphaBody := (loK_alphaNIR (N := N)).2.2
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ rd s'.M uI = toWord j ∧
    rd s'.M rTa = toWord (ta + j) ∧ rd s'.M rBs = toWord base ∧
    (∀ x, regs ≤ x → rd s'.M x = rd s.M x) ∧
    rdK s'.M fAl = ∑ i ∈ range j, if base.testBit i then T i else 0
  have step : ∀ j s', j < N → P j s' → P (j + 1) (decS rC2 (semXIR I alphaBody s')) := by
    rintro j s' hj ⟨q1, q2, q3, q4, q5, q6⟩
    have hTj : rdK s'.M (ta + j) = T j := by
      rw [← hT j hj]
      exact rdK_eq (q5 (ta + j) (by simp only [regs]; (clear * - hta; omega)))
    obtain ⟨e1, e2, e3⟩ := alphaBody_semN I s' q1 (T := T) hb hj (by (clear * - hN hj; omega)) (by simp only [regs]; omega) hta2
      q4 q2 q3 hTj
    refine ⟨by (try dsimp only); exact inv_decS (inv_sem I wb q1) (by decide), ?_, ?_, ?_, fun x hx => ?_, ?_⟩
    · rw [rd_decS (by decide), e2]
    · rw [rd_decS (by decide), e3]
    · rw [rd_decS (by decide), frame I _ s' wb q1 _ (by decide) (by
        simp +decide [alphaBody, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rBs,
          or_false]), q4]
    · rw [rd_decS (by simp only [rC2, regs] at *; (clear * - hx; omega)), hframeK I _ s' lb x hx, q5 x hx]
    · rw [rdK_decS _ (by decide), e1, q6, sum_range_succ]
  have hP0 : P 0 ⟨entryK rC2 rN2 (toWord N) s0.M, s0.o⟩ := by
    refine ⟨by dsimp only; exact hME, ?_, ?_, ?_, fun x hx => ?_, ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), i0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), b0]
    · dsimp only
      rw [hE _ (by simp only [rC2, regs] at *; (clear * - hx; omega)) (by simp only [cTmp, regs] at *; (clear * - hx; omega)),
        hH0 x hx]
    · dsimp only
      rw [rdK_eq (hE _ (by decide) (by decide)), z0]; rfl
  have := iterL_ind (f := semXIR I alphaBody) (c := rC2) (m := N) P step N 0 _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - N; omega))) hP0
  rw [Nat.zero_add] at this
  exact this.2.2.2.2.2

/-- `α` on a table row is `wAt ptK N l base`. -/
theorem alphaNIR_wAt (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {base ta l : ℕ}
    (hb : base < 2 ^ 64) (hta : regs ≤ ta) (hta2 : ta + N < 2 ^ 64)
    (hBs : rd s.M rBs = toWord base) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < N, rdK s.M (ta + i) = (wRow ptK N l).getD i 0) :
    rdK (semXIR I (alphaNIR N) s).M fAl = wAt ptK N l base :=
  alphaNIR_sem I s hM hN hb hta hta2 hBs hTr hT

/-! ## One butterfly on the machine -/

/-- Proof help for `pairNBody_nw` (kept separate so that `pairNBody_nw` itself has no `_simp_` auxiliaries). -/
private theorem pairNBody_nw_of {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3) : ¬ Writes (pairNBody N) r := by
  have h9 : 9 ≤ r ∧ r ≠ fT := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  simp only [pairNBody, pairPs, arithIR, alphaNIR, alphaBody, addK, Writes, Prim.dst,
    mulK_writes_iff h9.1 h9.2, List.mem_cons, exists_eq_or_imp, exists_eq_left, List.mem_nil_iff, or_false]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rQ, uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, rA0,
      rP2, rTr, rLv, rC1, rN1, rC3, rN3] <;> decide

theorem pairNBody_nw {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3) : ¬ Writes (pairNBody N) r :=
  pairNBody_nw_of hr

/-- **One butterfly**: the pair's low and high elements become `u + α (w + u)` and `w + u`,
`α = Σ_{i<N} [bit_i(base)] T(i)`; nothing else on the heap changes; `q += 1`. -/
theorem pairNBody_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {A ta l q : ℕ} {T : ℕ → BF64}
    (hl : l < 64) (hA : regs ≤ A) (hq : q < 2 ^ 64) (hhi : A + hiP l q < 2 ^ 64)
    (hsz : A + hiP l q < s.M.size) (hta : regs ≤ ta) (hta2 : ta + N < 2 ^ 64)
    (hQ : rd s.M rQ = toWord q) (hP2 : rd s.M rP2 = toWord (2 ^ l)) (hA0 : rd s.M rA0 = toWord A)
    (hTr : rd s.M rTr = toWord ta) (hT : ∀ i < N, rdK s.M (ta + i) = T i) :
    rdK (semXIR I (pairNBody N) s).M (A + loP l q) = rdK s.M (A + loP l q) +
      (∑ i ∈ range N, if (baseP l q).testBit i then T i else 0) *
        (rdK s.M (A + hiP l q) + rdK s.M (A + loP l q)) ∧
    rdK (semXIR I (pairNBody N) s).M (A + hiP l q) =
      rdK s.M (A + hiP l q) + rdK s.M (A + loP l q) ∧
    (∀ x, regs ≤ x → x ≠ A + loP l q → x ≠ A + hiP l q →
      rd (semXIR I (pairNBody N) s).M x = rd s.M x) ∧
    rd (semXIR I (pairNBody N) s).M rQ = toWord (q + 1) := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hlh := loP_lt_hiP l q
  have hP : 2 ^ l < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hl
  have hbase : baseP l q < 2 ^ 64 := by
    have : baseP l q ≤ loP l q := by simp [loP]
    (clear * - hA hhi hlh this; omega)
  -- the addresses
  have w1 : WF (.blk pairPs) := by
    simp +decide [pairPs, WF, Prim.dst, uT1, uX, uT2, rBs, rAL, rAH]
  obtain ⟨p1, p2, p3⟩ := pairPs_sem I s hM (A := A) hq hP hQ hP2 hA0
  have hM1 := inv_sem I w1 hM
  have z1 := size_sem I (.blk pairPs) s
  have hH1 := hframe I (.blk pairPs) s (by simp +decide [pairPs, Lo, Prim.dst, regs, uT1, uX,
    uT2, rBs, rAL, rAH])
  have q1 : rd (semXIR I (.blk pairPs) s).M rQ = toWord q := by
    rw [frame I _ s w1 hM _ (by decide) (by simp +decide [pairPs, Writes, Prim.dst, uT1, uX,
      uT2, rBs, rAL, rAH, rQ]), hQ]
  have t1 : rd (semXIR I (.blk pairPs) s).M rTr = toWord ta := by
    rw [frame I _ s w1 hM _ (by decide) (by simp +decide [pairPs, Writes, Prim.dst, uT1, uX,
      uT2, rBs, rAL, rAH, rTr]), hTr]
  rw [pairNBody, semXIR_seq]
  generalize semXIR I (.blk pairPs) s = s1 at p1 p2 p3 hM1 hH1 q1 t1 z1
  have hT1 : ∀ i < N, rdK s1.M (ta + i) = T i := fun i hi => by
    rw [← hT i hi]; exact rdK_eq (hH1 _ (by simp only [regs]; (clear * - hta; omega)))
  -- `α`
  have a2 := alphaNIR_sem I s1 hM1 hN hbase (by simp only [regs]; (clear * - hta; omega)) hta2 p1 t1 hT1
  have hM2 := inv_sem I (wf_alphaNIR N) hM1
  have z2 := size_sem I (alphaNIR N) s1
  have hH2 := hframeK I (alphaNIR N) s1 (loK_alphaNIR (N := N))
  have nwA : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I (alphaNIR N) s1).M r = rd s1.M r :=
    fun r hr => frame I _ s1 (wf_alphaNIR N) hM1 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide [alphaNIR, alphaBody, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rN2,
        rC2, cTmp, rAL, rAH, rQ, or_false])
  rw [semXIR_seq]
  generalize semXIR I (alphaNIR N) s1 = s2 at a2 hM2 hH2 nwA z2
  have l2 : rd s2.M rAL = toWord (A + loP l q) := (nwA _ (.inl rfl)).trans p2
  have h2 : rd s2.M rAH = toWord (A + hiP l q) := (nwA _ (.inr (.inl rfl))).trans p3
  have q2 : rd s2.M rQ = toWord q := (nwA _ (.inr (.inr rfl))).trans q1
  have hY : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => (hH2 x hx).trans (hH1 x hx)
  -- the arithmetic
  obtain ⟨b1, b2⟩ := arith_sem I s2 hM2 (a := A + loP l q) (b := A + hiP l q)
    (by (clear * - hhi hlh; omega)) (by simp only [regs]; (clear * - hA; omega)) (by omega) l2 h2
  have hM3 := inv_sem I wf_arithIR hM2
  have z3 := size_sem I arithIR s2
  have hH3 := hframe I arithIR s2 lo_arithIR
  have nwB : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I arithIR s2).M r = rd s2.M r :=
    fun r hr => frame I _ s2 wf_arithIR hM2 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide [arithIR, addK, Writes, Prim.dst, fU, fW, fH, fT, fN, rAL, rAH, rQ,
        mulK_writes_iff, or_false])
  have eU : rdK s2.M (A + loP l q) = rdK s.M (A + loP l q) :=
    rdK_eq (hY _ (by simp only [regs]; (clear * - hA; omega)))
  have eW : rdK s2.M (A + hiP l q) = rdK s.M (A + hiP l q) :=
    rdK_eq (hY _ (by simp only [regs]; (clear * - hA; omega)))
  rw [eU, eW, a2] at b1
  rw [eU, eW] at b2
  rw [semXIR_seq]
  generalize semXIR I arithIR s2 = s3 at b1 b2 hM3 hH3 nwB z3
  have l3 : rd s3.M rAL = toWord (A + loP l q) := (nwB _ (.inl rfl)).trans l2
  have h3 : rd s3.M rAH = toWord (A + hiP l q) := (nwB _ (.inr (.inl rfl))).trans h2
  have q3 : rd s3.M rQ = toWord q := (nwB _ (.inr (.inr rfl))).trans q2
  -- the stores
  obtain ⟨c1, c2, hM4⟩ := store_sem I s3 hM3 (p := rAL) (v := fN) (x := A + loP l q)
    (by decide) (by decide) l3 (by simp only [regs]; (clear * - hA; omega)) (by (clear * - hhi hlh; omega)) (by (clear * - hsz hlh z1 z2 z3; omega))
  have z4 := size_sem I (.store rAL fN) s3
  rw [semXIR_seq]
  generalize semXIR I (.store rAL fN) s3 = s4 at c1 c2 hM4 z4
  have hT4 : cTmp = 4 := rfl
  have hr4 : ∀ r, r < 256 → r ≠ cTmp → rd s4.M r = rd s3.M r := fun r hr h2 =>
    c2 r (by (clear * - hA hhi hr; omega)) h2
  have h4 : rd s4.M rAH = toWord (A + hiP l q) := (hr4 _ (by decide) (by decide)).trans h3
  have q4 : rd s4.M rQ = toWord q := (hr4 _ (by decide) (by decide)).trans q3
  have f4 : rdK s4.M fH = rdK s3.M fH := rdK_eq (hr4 _ (by decide) (by decide))
  obtain ⟨d1, d2, hM5⟩ := store_sem I s4 hM4 (p := rAH) (v := fH) (x := A + hiP l q)
    (by decide) (by decide) h4 (by simp only [regs]; (clear * - hA; omega)) (by omega) (by (clear * - hsz z1 z2 z3 z4; omega))
  rw [semXIR_seq]
  generalize semXIR I (.store rAH fH) s4 = s5 at d1 d2 hM5
  have hr5 : ∀ r, r < 256 → r ≠ cTmp → rd s5.M r = rd s4.M r := fun r hr h2 =>
    d2 r (by (clear * - hA hr; omega)) h2
  -- `q += 1`
  have e6 : ∀ x, x ≠ rQ → rd (semXIR I (.blk [.op .add rQ rQ cOne]) s5).M x = rd s5.M x :=
    fun x hx => rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact fun h => hx h.symm)
  refine ⟨?_, ?_, fun x hx x1 x2 => ?_, ?_⟩
  · rw [rdK_eq (e6 _ (by simp only [rQ]; (clear * - hA; omega))), rdK_eq (d2 _ (by (clear * - hlh; omega)) (by (clear * - hA hhi hT4; omega))),
      rdK_eq c1, b1]
  · rw [rdK_eq (e6 _ (by simp only [rQ]; (clear * - hA; omega))), rdK_eq d1, f4, b2]
  · simp only [regs] at hx
    rw [e6 _ (by simp only [rQ]; (clear * - hx; omega)), d2 _ x2 (by (clear * - hT4 hx; omega)), c2 _ x1 (by (clear * - hT4 hx; omega)),
      hH3 x (by simp only [regs]; (clear * - hx; omega)), hY x (by simp only [regs]; (clear * - hx; omega))]
  · have hs5 := hM5.1
    simp only [regs] at hs5
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rQ]; (clear * - hs5; omega)), hr5 _ (by decide) (by decide), q4,
      hr5 _ (by decide) (by decide), show rd s4.M cOne = 1 from hM4.2 0 (by decide)]
    exact add_one_toWord q

/-! ## A level, and the iteration -/

/-- **A level** `l < ℓ` on the row of `2^ℓ` elements at `A`, with the table row `wRow ptK N l`
at `ta`: every element becomes `bflyLevel`'s; the heap outside the row is kept. -/
theorem levelNIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {A ta ℓ l : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ N) (hl : l < ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (hta : regs ≤ ta) (hta2 : ta + N < 2 ^ 64)
    (hdisj : ta + N ≤ A ∨ A + 2 ^ ℓ ≤ ta)
    (hLv : rd s.M rLv = toWord l) (hA0 : rd s.M rA0 = toWord A) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < N, rdK s.M (ta + i) = (wRow ptK N l).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    (∀ i < 2 ^ ℓ, rdK (semXIR I ((levelNIR N ℓ)) s).M (A + i) = bflyLevel ptK N 0 l Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd (semXIR I ((levelNIR N ℓ)) s).M x = rd s.M x) ∧
    (semXIR I ((levelNIR N ℓ)) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hP1 : 2 ^ (ℓ - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by (clear * - hN hℓ hl; omega))
  have hPl : l * 1 < 64 := by (clear * - hN hℓ hl; omega)
  have w0 : WF (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))]) := by
    simp +decide [WF, Prim.dst, rQ, rP2, rN1, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s
  have hH0 := hframe I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s (by simp +decide [Lo, Prim.dst, regs, rQ, rP2, rN1,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  have r0 : rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rQ = toWord 0 ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rP2 = toWord (2 ^ l) ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rN1 = toWord (2 ^ (ℓ - 1)) ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rA0 = toWord A ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rTr = toWord ta := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rQ, rP2, rN1]; (clear * - s N I A ta ℓ l hs z0; omega))) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hLv, show rd s.M cOne = toWord 1 from hM.2 0 (by decide), shl_toWord (by (clear * - hPl; omega))
        (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by (clear * - hPl; omega))), Nat.one_mul]
    · exact hA0
    · exact hTr
  rw [levelNIR, semXIR_seq]
  generalize semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s = s0 at hM0 z0 hH0 r0
  obtain ⟨q0, p0, n0, a0, t0⟩ := r0
  rw [loopK_eq I (pairNBody N) s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hP1]
  have hE : ∀ i, i ≠ rC1 → i ≠ cTmp → rd (entryK rC1 rN1 (toWord (2 ^ (ℓ - 1))) s0.M) i =
      rd s0.M i := fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC1) (n := rN1) (K := toWord (2 ^ (ℓ - 1))) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rQ = toWord j ∧ rd s'.M rP2 = toWord (2 ^ l) ∧ rd s'.M rA0 = toWord A ∧
    rd s'.M rTr = toWord ta ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdK s'.M (A + i) =
      if pairOf l i < j then bflyLevel ptK N 0 l Y i else Y i
  have nwP : ∀ r, (r = rA0 ∨ r = rP2 ∨ r = rTr) → ∀ s', Inv s'.M →
      rd (decS rC1 (semXIR I (pairNBody N) s')).M r = rd s'.M r := fun r hr s' hs' => by
    rw [rd_decS (by rcases hr with rfl | rfl | rfl <;> decide)]
    exact frame I _ s' (wf_pairNBody N) hs' _ (by rcases hr with rfl | rfl | rfl <;> decide)
      (pairNBody_nw (by rcases hr with rfl | rfl | rfl <;> simp))
  have step : ∀ j s', j < 2 ^ (ℓ - 1) → P j s' → P (j + 1) (decS rC1 (semXIR I (pairNBody N) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    have hhi := hiP_lt hl hj
    have hlh := loP_lt_hiP l j
    have hT' : ∀ i < N, rdK s'.M (ta + i) = (wRow ptK N l).getD i 0 := fun i hi => by
      rw [← hT i hi]
      exact rdK_eq (i7 _ (by simp only [regs]; (clear * - hta; omega)) (by (clear * - hdisj hi; omega)))
    obtain ⟨e1, e2, e3, e4⟩ := pairNBody_sem I s' i1 hN (A := A)
      (T := fun i => (wRow ptK N l).getD i 0)
      (by (clear * - hPl; omega)) (by simp only [regs]; omega) (by (clear * - hP1 hj; omega)) (by (clear * - hA2 hhi; omega)) (by (clear * - hsz z0 i2 hhi; omega))
      (by simp only [regs]; (clear * - hta; omega)) hta2 i3 i4 i5 i6 hT'
    have hd : ∀ x, x ≠ rC1 → rd (decS rC1 (semXIR I (pairNBody N) s')).M x =
        rd (semXIR I (pairNBody N) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hlo' := i8 _ (by (clear * - hhi hlh; omega) : loP l j < 2 ^ ℓ)
    have hhi' := i8 _ hhi
    rw [pairOf_loP, if_neg (lt_irrefl j)] at hlo'
    rw [pairOf_hiP, if_neg (lt_irrefl j)] at hhi'
    refine ⟨by (try dsimp only); exact inv_decS (inv_sem I (wf_pairNBody N) i1) (by decide), by rw [size_decS, size_sem, i2], ?_,
      (nwP _ (.inr (.inl rfl)) s' i1).trans i4, (nwP _ (.inl rfl) s' i1).trans i5,
      (nwP _ (.inr (.inr rfl)) s' i1).trans i6, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide), e4]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC1]; (clear * - hx; omega)), e3 x (by simp only [regs]; omega) (by (clear * - hhi hlh hx2; omega))
        (by (clear * - hhi hx2; omega)), i7 x (by simp only [regs]; omega) hx2]
    · rw [rdK_eq (hd _ (by simp only [rC1, regs] at *; (clear * - hA; omega)))]
      by_cases hq : pairOf l i = j
      · rw [if_pos (by (clear * - hq; omega))]
        rcases pair_cases hq with rfl | rfl
        · rw [e1, hlo', hhi', bflyLevel_lo]; rfl
        · rw [e2, hlo', hhi', bflyLevel_hi]
      · have hil : i ≠ loP l j := fun h => hq (by rw [h, pairOf_loP])
        have hih : i ≠ hiP l j := fun h => hq (by rw [h, pairOf_hiP])
        rw [rdK_eq (e3 _ (by simp only [regs]; (clear * - hA; omega)) (by (clear * - hlh hil hih; omega)) (by (clear * - hih; omega))), i8 i hi]
        by_cases hlt : pairOf l i < j
        · rw [if_pos hlt, if_pos (by (clear * - hlt; omega))]
        · rw [if_neg hlt, if_neg (by (clear * - hlh hq hil hih hlt; omega))]
  have hP0 : P 0 ⟨entryK rC1 rN1 (toWord (2 ^ (ℓ - 1))) s0.M, s0.o⟩ := by
    refine ⟨by dsimp only; exact hME, by simp only [size_entryK, z0], ?_, ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), q0]
    · dsimp only; rw [hE _ (by decide) (by decide), p0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only
      rw [hE _ (by simp only [rC1, regs] at *; (clear * - hx; omega)) (by simp only [cTmp, regs] at *; (clear * - hx; omega)),
        hH0 x hx]
    · dsimp only
      rw [if_neg (Nat.not_lt_zero _), ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC1]; (clear * - hA; omega)) (by simp only [cTmp]; (clear * - hA; omega))).trans
        (hH0 _ (by simp only [regs]; (clear * - hA; omega))))
  have := iterL_ind (f := semXIR I (pairNBody N)) (c := rC1) (m := 2 ^ (ℓ - 1)) P step (2 ^ (ℓ - 1)) 0
    _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - ℓ; omega))) hP0
  rw [Nat.zero_add] at this
  obtain ⟨-, z, -, -, -, -, f7, f8⟩ := this
  refine ⟨fun i hi => ?_, f7, z⟩
  rw [f8 i hi, if_pos (pairOf_lt hl hi)]

theorem levelNIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rLv ∨ r = rTr ∨ r = rC3 ∨ r = rN3) (ℓ : ℕ) :
    ¬ Writes ((levelNIR N ℓ)) r := by
  intro h
  simp only [levelNIR, Writes] at h
  rcases h with ⟨p, hp, he⟩ | h | h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, rQ, rP2, rN1, rA0, rLv, rTr, rC3, rN3] at he
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [rC1, rA0, rLv, rTr, rC3, rN3] at h
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cTmp, rA0, rLv, rTr, rC3, rN3] at h
  · exact pairNBody_nw (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) h

/-- **The inverse NTT** (`bflyRun`) on the machine: from the row `Y` of `2^ℓ` elements at `A`
(`rA0 = A`) and the basis table at `tb` (row `v` at `tb + N v`), `(bflyNIR N ℓ tb)` leaves
`bflyRun ptK N 0 ℓ Y` in the row and keeps the heap outside it. -/
theorem bflyNIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ N) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64)
    (hdisj : tb + N * N ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < N, ∀ i < N, rdK s.M (tb + N * v + i) = (wRow ptK N v).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    (∀ i < 2 ^ ℓ, rdK (semXIR I ((bflyNIR N ℓ tb)) s).M (A + i) = bflyRun ptK N 0 ℓ Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd (semXIR I ((bflyNIR N ℓ tb)) s).M x = rd s.M x) ∧
    Inv (semXIR I ((bflyNIR N ℓ tb)) s).M := by
  have hs := hM.1
  simp only [regs] at hs hA htb
  have hℓ64 : ℓ < 2 ^ 64 := by (clear * - hN hℓ; omega)
  have w0 : WF (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) := by
    simp +decide [WF, Prim.dst, rLv, rTr, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) s
  have hH0 := hframe I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) s
    (by simp +decide [Lo, Prim.dst, regs, rLv, rTr, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have r0 : rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rLv = toWord 0 ∧
      rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rTr = toWord (tb + N * 0) ∧
      rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rN3 = toWord ℓ ∧
      rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rA0 = toWord A := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLv, rTr, rN3]; (clear * - s N I A tb ℓ hs z0; omega))) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rfl
    · exact hA0
  rw [bflyNIR, semXIR_seq]
  generalize semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) s = s0
    at hM0 z0 hH0 r0
  obtain ⟨l0, t0, n0, a0⟩ := r0
  rw [loopK_eq I ((lvlNStep N ℓ)) s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hℓ64]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 (toWord ℓ) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := toWord ℓ) hM0 (by decide)
  have wl : WF ((levelNIR N ℓ)) := (wf_bflyNIR N ℓ tb).2.2.2.2.1
  have wlb : WF (.blk [.op .add rLv rLv cOne, .const uT1 (toWord N), .op .add rTr rTr uT1]) := by
    simp +decide [WF, Prim.dst, rLv, uT1, rTr]
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rLv = toWord j ∧ rd s'.M rTr = toWord (tb + N * j) ∧ rd s'.M rA0 = toWord A ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdK s'.M (A + i) = bflyRun ptK N 0 j Y i
  have step : ∀ j s', j < ℓ → P j s' → P (j + 1) (decS rC3 (semXIR I ((lvlNStep N ℓ)) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hjN : N * j + N ≤ N * N := by
      rw [show N * j + N = N * (j + 1) by ring]; exact Nat.mul_le_mul_left N (by (clear * - hℓ hj; omega))
    have hT : ∀ i < N, rdK s'.M (tb + N * j + i) = (wRow ptK N j).getD i 0 :=
      fun i hi => by
        rw [← hW j (by (clear * - hℓ hj; omega)) i (by omega)]
        exact rdK_eq (i6 _ (by simp only [regs]; (clear * - htb; omega)) (by (clear * - hA hA2 htb2 hdisj hjN hi; omega)))
    obtain ⟨e1, e2, e3⟩ := levelNIR_sem I s' i1 hN (Y := bflyRun ptK N 0 j Y) (by (clear * - hℓ; omega)) hj
      (by simp only [regs]; (clear * - hA; omega)) hA2 (by (clear * - hsz z0 i2; omega)) (by simp only [regs]; (clear * - htb; omega)) (by (clear * - htb2 hjN; omega))
      (by (clear * - hdisj hjN; omega)) i3 i5 i4 hT i7
    have hM1 := inv_sem I wl i1
    have nw : ∀ r, (r = rA0 ∨ r = rLv ∨ r = rTr) → rd (semXIR I ((levelNIR N ℓ)) s').M r = rd s'.M r :=
      fun r hr => frame I _ s' wl i1 _ (by rcases hr with rfl | rfl | rfl <;> decide)
        (levelNIR_nw (by rcases hr with rfl | rfl | rfl <;> simp) ℓ)
    rw [lvlNStep]
    simp only [semXIR_seq]
    generalize hs1 : semXIR I ((levelNIR N ℓ)) s' = s1 at e1 e2 e3 hM1 nw
    have hs1' := hM1.1
    simp only [regs] at hs1'
    have hd : ∀ x, x ≠ rC3 → rd (decS rC3 (semXIR I (.blk [.op .add rLv rLv cOne, .const uT1 (toWord N),
        .op .add rTr rTr uT1]) s1)).M x = rd (semXIR I (.blk [.op .add rLv rLv cOne,
        .const uT1 (toWord N), .op .add rTr rTr uT1]) s1).M x := fun x hx => rd_decS (Ne.symm hx) _
    have hb : ∀ x, x ≠ rLv → x ≠ uT1 → x ≠ rTr → rd (semXIR I (.blk [.op .add rLv rLv cOne,
        .const uT1 (toWord N), .op .add rTr rTr uT1]) s1).M x = rd s1.M x := fun x h1 h2 h3 =>
      rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩)
    refine ⟨by (try dsimp only); exact inv_decS (inv_sem I wlb hM1) (by decide), by rw [size_decS, size_sem, e3, i2], ?_, ?_,
      ?_, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; (clear * - s1 N s A tb ℓ hs s0 z0 j s' i2 e3; omega))) only
        [rd_set_self, rd_set_ne]
      rw [nw _ (.inr (.inl rfl)), i3, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
        add_one_toWord]
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; (clear * - s1 N s A tb ℓ hs s0 z0 j s' i2 e3; omega))) only
        [rd_set_self, rd_set_ne]
      rw [nw _ (.inr (.inr rfl)), i4, add_toWord]
      congr 1; ring
    · rw [hd _ (by decide), hb _ (by decide) (by decide) (by decide), nw _ (.inl rfl), i5]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC3]; (clear * - hx; omega)), hb _ (by simp only [rLv]; (clear * - hx; omega))
        (by simp only [uT1]; (clear * - hx; omega)) (by simp only [rTr]; (clear * - hx; omega)), e2 x (by simp only [regs]; omega)
        hx2, i6 x (by simp only [regs]; (clear * - hx; omega)) hx2]
    · rw [rdK_eq ((hd _ (by simp only [rC3]; (clear * - hA; omega))).trans (hb _ (by simp only [rLv]; (clear * - hA; omega))
        (by simp only [uT1]; (clear * - hA; omega)) (by simp only [rTr]; (clear * - hA; omega)))), e1 i hi]
      rfl
  have hP0 : P 0 ⟨entryK rC3 rN3 (toWord ℓ) s0.M, s0.o⟩ := by
    refine ⟨by dsimp only; exact hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), l0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only
      rw [hE _ (by simp only [rC3, regs] at *; (clear * - hx; omega)) (by simp only [cTmp, regs] at *; (clear * - hx; omega)),
        hH0 x hx]
    · dsimp only
      rw [show bflyRun ptK N 0 0 Y i = Y i from rfl, ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC3]; (clear * - hA; omega)) (by simp only [cTmp]; (clear * - hA; omega))).trans
        (hH0 _ (by simp only [regs]; (clear * - hA; omega))))
  have := iterL_ind (f := semXIR I ((lvlNStep N ℓ))) (c := rC3) (m := ℓ) P step ℓ 0 _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - ℓ; omega))) hP0
  rw [Nat.zero_add] at this
  exact ⟨this.2.2.2.2.2.2, this.2.2.2.2.2.1, this.1⟩

/-- **The inverse NTT computes the novel-basis coefficients** (`bflyRun_eq`): `coeffsAt` of the
values on `ptK [0, 2^ℓ)`. -/
theorem bflyNIR_coeffs (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ N) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64)
    (hdisj : tb + N * N ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < N, ∀ i < N, rdK s.M (tb + N * v + i) = (wRow ptK N v).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    ∀ i < 2 ^ ℓ, rdK (semXIR I ((bflyNIR N ℓ tb)) s).M (A + i) = coeffsAt ptK N ℓ 0 Y i :=
  fun i hi => ((bflyNIR_sem I s hM hN hℓ hA hA2 hsz htb htb2 hdisj hA0 hW hY).1 i hi).trans
    (bflyRun_eq ptK N 0 ℓ Y hi)

end Lvm.X
end
-- ===== end of `LvmMPXNtt2` =====

-- ===== merged from `LvmMPXNtt3` (GOLF module merge: `LvmMPXNtt3.lean` is now a stub importing `LvmMPXNtt4`) =====
section
-- New for lvm2 roll 11 (M′, R11-X): the basis table's semantics at any dimension `N`. Adapted from
-- `LvmXNtt3.lean` (`wRow_zero_getD`, `wRow_succ_getD`, `row0Body_sem`, `row0IR_sem`, `rowBody_sem`, `rowIR_sem`,
-- `wtabIR_sem`, `wtabIR_normW`) with the literal `15` (`14` rows after row `0`, row stride, `225` words) replaced
-- by `N` (`N − 1`, `N`, `N²`); `wK_add_one`, `plusOne_sem`, `wf_plusOne`, `wf_row0Body` are reused.

/-!
# The basis table at dimension `N`

**`wtabNIR_sem`**: `wtabNIR N tb` (`1 ≤ N ≤ 64`) writes the rows `wRow ptK N v`, `v < N`, at `tb + N v + i` and
keeps the heap outside `[tb, tb + N²)`; `wtabNIR_normW`: entry `(v, i)` is `Ŵ_v(ptK 2^i)`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

variable {N : ℕ}

attribute [local irreducible] entryK storeM

theorem wf_rowNBody (N : ℕ) : WF (rowNBody N) := by
  simp only [rowNBody, WF, Prim.dst, List.mem_cons, List.mem_nil_iff,
    mulK_wf_iff (show 4 ≤ fH by decide), mulK_wf_iff (show 4 ≤ fN by decide)]
  simp [fU, fW, fH, fN, uT1, rAH, rTa, cTmp]

theorem wRow_zero_getDN {i : ℕ} (hi : i < N) : (wRow ptK N 0).getD i 0 = ptK (2 ^ i) := by
  simp [wRow, hi, List.getD_eq_getElem?_getD, ptK_zero, show ptK 1 = 1 from rfl]

theorem wRow_succ_getDN (v : ℕ) {i : ℕ} (hi : i < N) : (wRow ptK N (v + 1)).getD i 0 =
    (wRow ptK N v).getD i 0 * ((wRow ptK N v).getD i 0 + 1) *
      ((wRow ptK N v).getD (v + 1) 0 * ((wRow ptK N v).getD (v + 1) 0 + 1))⁻¹ := by
  rw [wRow]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, wRow_length]; exact hi), List.getElem_map,
    ← List.getD_eq_getElem _ 0]
  rfl

/-- One entry of row `0`: `ptK (2^i)` at `tb + i`. -/
theorem row0Body_semN (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {tb i : ℕ} (hi : i < N)
    (htb : regs ≤ tb) (htb2 : tb + N < 2 ^ 64) (hsz : tb + N ≤ s.M.size)
    (hI : rd s.M uI = toWord i) (hTa : rd s.M rTa = toWord (tb + i)) :
    rdK (semXIR I row0Body s).M (tb + i) = ptK (2 ^ i) ∧
    (∀ x, regs ≤ x → x ≠ tb + i → rd (semXIR I row0Body s).M x = rd s.M x) ∧
    rd (semXIR I row0Body s).M uI = toWord (i + 1) ∧
    rd (semXIR I row0Body s).M rTa = toWord (tb + (i + 1)) ∧
    rd (semXIR I row0Body s).M rTr = rd s.M rTr := by
  have hs := hM.1
  simp only [regs] at hs htb
  have w1 : WF (.blk [.op .shl fG cOne uI]) := by simp +decide [WF, Prim.dst, fG]
  have hM1 := inv_sem I w1 hM
  have hH1 := hframe I (.blk [.op .shl fG cOne uI]) s (by simp +decide [Lo, Prim.dst, regs, fG])
  have r1 : rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M fG = toWord (2 ^ i) ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M rTa = toWord (tb + i) ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M uI = toWord i ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M rTr = rd s.M rTr := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, fG]; (clear * - s N tb i hs; omega))) only [rd_set_self, rd_set_ne]
    · rw [hI, show rd s.M cOne = toWord 1 from hM.2 0 (by decide), shl_toWord (by (clear * - hN hi; omega))
        (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by (clear * - hN hi; omega))), Nat.one_mul]
    · exact hTa
    · exact hI
  rw [row0Body, semXIR_seq]
  have z1 := size_sem I (.blk [.op .shl fG cOne uI]) s
  generalize semXIR I (.blk [.op .shl fG cOne uI]) s = s1 at hM1 hH1 r1 z1
  obtain ⟨g1, a1, i1, t1⟩ := r1
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := rTa) (v := fG) (x := tb + i) (by decide)
    (by decide) a1 (by simp only [regs]; (clear * - htb; omega)) (by (clear * - hi htb2; omega)) (by (clear * - hi hsz z1; omega))
  rw [semXIR_seq]
  generalize semXIR I (.store rTa fG) s1 = s2 at c1 c2 hM2
  have hT4 : cTmp = 4 := rfl
  have hr2 : ∀ r, r < 256 → r ≠ cTmp → rd s2.M r = rd s1.M r := fun r hr h2 =>
    c2 r (by (clear * - hN hi htb htb2 hr; omega)) h2
  have hb : ∀ x, x ≠ rTa → x ≠ uI → rd (semXIR I (.blk [.op .add rTa rTa cOne,
      .op .add uI uI cOne]) s2).M x = rd s2.M x := fun x h1 h2 =>
    rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩)
  have hs2 := hM2.1
  simp only [regs] at hs2
  refine ⟨?_, fun x hx x1 => ?_, ?_, ?_, ?_⟩
  · rw [rdK_eq (hb _ (by simp only [rTa]; (clear * - htb; omega)) (by simp only [uI]; (clear * - htb; omega))), rdK_eq c1, rdK, g1]
    rfl
  · simp only [regs] at hx
    rw [hb _ (by simp only [rTa]; (clear * - hx; omega)) (by simp only [uI]; (clear * - hx; omega)), c2 _ x1 (by (clear * - hT4 hx; omega)),
      hH1 x (by simp only [regs]; (clear * - hx; omega))]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rTa, uI]; (clear * - s2 N s tb i s1 hs2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [hr2 _ (by decide) (by decide), i1, hr2 _ (by decide) (by decide),
      show rd s1.M cOne = 1 from hM1.2 0 (by decide), add_one_toWord]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rTa, uI]; (clear * - s2 N s tb i s1 hs2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [hr2 _ (by decide) (by decide), a1, hr2 _ (by decide) (by decide),
      show rd s1.M cOne = 1 from hM1.2 0 (by decide), add_one_toWord]
    rfl
  · rw [hb _ (by decide) (by decide), hr2 _ (by decide) (by decide), t1]

/-- **Row `0`** at `rTr = tb`: `ptK (2^i)` at `tb + i`, `i < N`. -/
theorem row0NIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + N < 2 ^ 64) (hsz : tb + N ≤ s.M.size) (hTr : rd s.M rTr = toWord tb) :
    (∀ i < N, rdK (semXIR I (row0NIR N) s).M (tb + i) = ptK (2 ^ i)) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + N ≤ x) → rd (semXIR I (row0NIR N) s).M x = rd s.M x) ∧
    rd (semXIR I (row0NIR N) s).M rTr = toWord tb ∧ Inv (semXIR I (row0NIR N) s).M ∧
    (semXIR I (row0NIR N) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs htb
  have w0 : WF (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) := by
    simp +decide [WF, Prim.dst, uI, rTa, rN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s
  have hH0 := hframe I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s
    (by simp +decide [Lo, Prim.dst, regs, uI, rTa, rN2])
  have r0 : rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s).M uI =
        toWord 0 ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s).M rTa =
        toWord (tb + 0) ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s).M rN2 = toWord N ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s).M rTr =
        toWord tb := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, uI, rTa, rN2]; (clear * - s N I tb hs z0; omega))) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hTr, or_self_eval]; rfl
    · exact hTr
  rw [row0NIR, semXIR_seq]
  generalize semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s = s0
    at hM0 z0 hH0 r0
  obtain ⟨i0, a0, n0, t0⟩ := r0
  rw [loopK_eq I row0Body s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord (show N < 2 ^ 64 by (clear * - hN; omega))]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 (toWord N) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := toWord N) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M uI = toWord j ∧ rd s'.M rTa = toWord (tb + j) ∧ rd s'.M rTr = toWord tb ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + j ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < j, rdK s'.M (tb + i) = ptK (2 ^ i)
  have step : ∀ j s', j < N → P j s' → P (j + 1) (decS rC2 (semXIR I row0Body s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := row0Body_semN (hN := hN) I s' i1 hj (by simp only [regs]; (clear * - htb; omega)) htb2
      (by (clear * - hsz z0 i2; omega)) i3 i4
    have hd : ∀ x, x ≠ rC2 → rd (decS rC2 (semXIR I row0Body s')).M x =
        rd (semXIR I row0Body s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨by (try dsimp only); exact inv_decS (inv_sem I wf_row0Body i1) (by decide), by rw [size_decS, size_sem, i2],
      by rw [hd _ (by decide), e3], by rw [hd _ (by decide), e4], by rw [hd _ (by decide), e5, i5],
      fun x hx hx2 => ?_, fun i hi => ?_⟩
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC2]; (clear * - hx; omega)), e2 x (by simp only [regs]; omega) (by (clear * - hx2; omega)),
        i6 x (by simp only [regs]; (clear * - hx; omega)) (by (clear * - hx2; omega))]
    · rw [rdK_eq (hd _ (by simp only [rC2]; (clear * - htb; omega)))]
      by_cases h : i = j
      · subst h; exact e1
      · rw [rdK_eq (e2 _ (by simp only [regs]; (clear * - htb; omega)) (by (clear * - h; omega))), i7 i (by (clear * - hi h; omega))]
  have hP0 : P 0 ⟨entryK rC2 rN2 (toWord N) s0.M, s0.o⟩ := by
    refine ⟨by dsimp only; exact hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · dsimp only; rw [hE _ (by decide) (by decide), i0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only
      rw [hE _ (by simp only [rC2, regs] at *; (clear * - hx; omega)) (by simp only [cTmp, regs] at *; (clear * - hx; omega)),
        hH0 x hx]
  have := iterL_ind (f := semXIR I row0Body) (c := rC2) (m := N) P step N 0 _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - N; omega))) hP0
  rw [Nat.zero_add] at this
  obtain ⟨f1, f2, -, -, f5, f6, f7⟩ := this
  exact ⟨f7, fun x hx hx2 => f6 x hx (by (clear * - hx2; omega)), f5, f1, f2⟩

/-- **One entry of row `j + 1`**: `a (a + 1) c` at `ta + N + k`, `a` the entry at `ta + k`,
`c` in `fAl`. -/
theorem rowNBody_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {ta k : ℕ} (hk : k < N)
    (hta : regs ≤ ta) (hta2 : ta + 2 * N < 2 ^ 64) (hsz : ta + 2 * N ≤ s.M.size)
    (hTa : rd s.M rTa = toWord (ta + k)) :
    rdK (semXIR I (rowNBody N) s).M (ta + N + k) =
      rdK s.M (ta + k) * (rdK s.M (ta + k) + 1) * rdK s.M fAl ∧
    (∀ x, regs ≤ x → x ≠ ta + N + k → rd (semXIR I (rowNBody N) s).M x = rd s.M x) ∧
    rd (semXIR I (rowNBody N) s).M rTa = toWord (ta + (k + 1)) ∧
    rdK (semXIR I (rowNBody N) s).M fAl = rdK s.M fAl ∧
    rd (semXIR I (rowNBody N) s).M rTr = rd s.M rTr ∧ rd (semXIR I (rowNBody N) s).M rLv = rd s.M rLv := by
  have hs := hM.1
  simp only [regs] at hs hta
  have hT4 : cTmp = 4 := rfl
  -- load `a`
  obtain ⟨u1, u3, hM1⟩ := load_sem I s hM (d := fU) (p := rTa) (by decide) (by decide) hTa
    (by (clear * - hk hta2; omega))
  have y1 := size_sem I (.load fU rTa) s
  rw [rowNBody, semXIR_seq]
  generalize semXIR I (.load fU rTa) s = s1 at u1 u3 hM1 y1
  -- `a + 1`
  obtain ⟨v1, v2⟩ := plusOne_sem I s1 hM1
  have hM2 := inv_sem I wf_plusOne hM1
  have y2 := size_sem I (.blk [.op .xor fW fU cOne]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .xor fW fU cOne]) s1 = s2 at v1 v2 hM2 y2
  -- the products
  have m3 := mulK_sem (I := I) (s := s2) hM2 (d := fH) (a := fU) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f3 : ∀ i, 9 ≤ i → i ≠ fH → rd (semXIR I (mulK fH fU fW) s2).M i = rd s2.M i :=
    fun i h0 h1 => mulK_frame I s2 h0 h1
  have hM3 := inv_sem I (wf_mulK fH fU fW (by decide)) hM2
  have y3 := size_sem I (mulK fH fU fW) s2
  rw [semXIR_seq]
  generalize semXIR I (mulK fH fU fW) s2 = s3 at m3 f3 hM3 y3
  have m4 := mulK_sem (I := I) (s := s3) hM3 (d := fN) (a := fH) (b := fAl) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 9 ≤ i → i ≠ fN → rd (semXIR I (mulK fN fH fAl) s3).M i = rd s3.M i :=
    fun i h0 h1 => mulK_frame I s3 h0 h1
  have hM4 := inv_sem I (wf_mulK fN fH fAl (by decide)) hM3
  have y4 := size_sem I (mulK fN fH fAl) s3
  rw [semXIR_seq]
  generalize semXIR I (mulK fN fH fAl) s3 = s4 at m4 f4 hM4 y4
  -- facts on `s4`
  have k4 : ∀ x, 256 ≤ x → rd s4.M x = rd s.M x := fun x hx => by
    rw [f4 x (by (clear * - hx; omega)) (by simp only [fN]; (clear * - hx; omega)), f3 x (by (clear * - hx; omega)) (by simp only [fH]; (clear * - hx; omega)),
      v2 x (by simp only [fW]; (clear * - hx; omega)), u3 x (by simp only [fU]; (clear * - hx; omega))]
  have r4 : ∀ r, (r = rTa ∨ r = rTr ∨ r = rLv ∨ r = fAl) → rd s4.M r = rd s.M r :=
    fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
      rw [f4 _ (by decide) (by decide), f3 _ (by decide) (by decide), v2 _ (by decide),
        u3 _ (by decide)]
  have n4 : rdK s4.M fN = rdK s.M (ta + k) * (rdK s.M (ta + k) + 1) * rdK s.M fAl := by
    have al2 : rdK s2.M fAl = rdK s.M fAl :=
      rdK_eq ((v2 _ (by decide)).trans (u3 _ (by decide)))
    have al3 : rdK s3.M fAl = rdK s.M fAl := (rdK_eq (f3 _ (by decide) (by decide))).trans al2
    have fu2 : rdK s2.M fU = rdK s.M (ta + k) := (rdK_eq (v2 _ (by decide))).trans (rdK_eq u1)
    rw [m4, m3, v1, al3, fu2, rdK_eq u1]
  -- the address
  have hs4 := hM4.1
  simp only [regs] at hs4
  have a5 : rd (semXIR I (.blk [.const uT1 (toWord N), .op .add rAH rTa uT1]) s4).M rAH =
      toWord (ta + N + k) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rAH]; (clear * - s4 N s ta k hs s1 y1 s2 y2 s3 y3 y4; omega))) only
      [rd_set_self, rd_set_ne]
    rw [r4 _ (.inl rfl), hTa, add_toWord]
    congr 1; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
  have b5 : ∀ x, x ≠ uT1 → x ≠ rAH → rd (semXIR I (.blk [.const uT1 (toWord N), .op .add rAH rTa uT1])
      s4).M x = rd s4.M x := fun x h1 h2 =>
    rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩)
  have hM5 := inv_sem I (P := .blk [.const uT1 (toWord N), .op .add rAH rTa uT1])
    (by simp +decide [WF, Prim.dst, uT1, rAH]) hM4
  have z5 := size_sem I (.blk [.const uT1 (toWord N), .op .add rAH rTa uT1]) s4
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const uT1 (toWord N), .op .add rAH rTa uT1]) s4 = s5 at a5 b5 hM5 z5
  -- the store
  obtain ⟨c1, c2, hM6⟩ := store_sem I s5 hM5 (p := rAH) (v := fN) (x := ta + N + k)
    (by decide) (by decide) a5 (by simp only [regs]; (clear * - hk hta; omega)) (by (clear * - hk hta2; omega)) (by (clear * - hk hsz y1 y2 y3 y4 z5; omega))
  rw [semXIR_seq]
  generalize semXIR I (.store rAH fN) s5 = s6 at c1 c2 hM6
  have hr6 : ∀ r, r < 256 → r ≠ cTmp → rd s6.M r = rd s5.M r := fun r hr h2 =>
    c2 r (by (clear * - hN hta hta2 hr; omega)) h2
  have hb : ∀ x, x ≠ rTa → rd (semXIR I (.blk [.op .add rTa rTa cOne]) s6).M x = rd s6.M x :=
    fun x h1 => rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact Ne.symm h1)
  have hs6 := hM6.1
  simp only [regs] at hs6
  refine ⟨?_, fun x hx x1 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [rdK_eq (hb _ (by simp only [rTa]; (clear * - hN hk hta hta2; omega))), rdK_eq c1,
      rdK_eq (b5 _ (by decide) (by decide)), n4]
  · simp only [regs] at hx
    rw [hb _ (by simp only [rTa]; (clear * - hx; omega)), c2 _ x1 (by (clear * - hT4 hx; omega)), b5 _ (by simp only [uT1]; (clear * - hx; omega))
      (by simp only [rAH]; (clear * - hx; omega)), k4 x hx]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rTa]; (clear * - s6 N s ta k s1 s2 s3 s4 s5 hs6; omega))) only
      [rd_set_self, rd_set_ne]
    rw [hr6 _ (by decide) (by decide), b5 _ (by decide) (by decide), r4 _ (.inl rfl), hTa,
      hr6 _ (by decide) (by decide), show rd s5.M cOne = 1 from hM5.2 0 (by decide),
      add_one_toWord]
    rfl
  · exact rdK_eq ((hb _ (by decide)).trans ((hr6 _ (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inr (.inr rfl)))))))
  · exact (hb _ (by decide)).trans ((hr6 _ (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inl rfl)))))
  · exact (hb _ (by decide)).trans ((hr6 _ (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inr (.inl rfl))))))

set_option maxRecDepth 8000 in
/-- **Row `j + 1`** from row `j` (`R`, at `ta = rTr`; `rLv = j`, `j + 1 < N`):
`R i (R i + 1) (b (b + 1))⁻¹` at `ta + N + i`, `b = R (j + 1)`. -/
theorem rowNIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {ta j : ℕ} {R : ℕ → BF64}
    (hj : j + 1 < N) (hta : regs ≤ ta) (hta2 : ta + 2 * N < 2 ^ 64) (hsz : ta + 2 * N ≤ s.M.size)
    (hLv : rd s.M rLv = toWord j) (hTr : rd s.M rTr = toWord ta)
    (hR : ∀ i < N, rdK s.M (ta + i) = R i) :
    (∀ i < N, rdK (semXIR I (rowNIR N) s).M (ta + N + i) =
      R i * (R i + 1) * (R (j + 1) * (R (j + 1) + 1))⁻¹) ∧
    (∀ x, regs ≤ x → (x < ta + N ∨ ta + 2 * N ≤ x) → rd (semXIR I (rowNIR N) s).M x = rd s.M x) ∧
    rd (semXIR I (rowNIR N) s).M rLv = toWord (j + 1) ∧ rd (semXIR I (rowNIR N) s).M rTr = toWord (ta + N) ∧
    Inv (semXIR I (rowNIR N) s).M ∧ (semXIR I (rowNIR N) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hta
  have hT4 : cTmp = 4 := rfl
  -- `rTa := ta + (j + 1)`
  have r1 : rd (semXIR I (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1]) s).M rTa =
      toWord (ta + (j + 1)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rTa]; (clear * - s N ta j hs; omega))) only
      [rd_set_self, rd_set_ne]
    rw [hLv, hTr, show rd s.M cOne = 1 from hM.2 0 (by decide), add_one_toWord, add_toWord]
  have b1 : ∀ x, x ≠ uT1 → x ≠ rTa → rd (semXIR I (.blk [.op .add uT1 rLv cOne,
      .op .add rTa rTr uT1]) s).M x = rd s.M x := fun x h1 h2 =>
    rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩)
  have hM1 := inv_sem I (P := .blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1])
    (by simp +decide [WF, Prim.dst, uT1, rTa]) hM
  have y1 := size_sem I (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1]) s
  rw [rowNIR, semXIR_seq]
  generalize semXIR I (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1]) s = s1 at r1 b1 hM1 y1
  -- `b`
  obtain ⟨u1, u3, hM2⟩ := load_sem I s1 hM1 (d := fU) (p := rTa) (by decide) (by decide) r1
    (by (clear * - hj hta2; omega))
  have y2 := size_sem I (.load fU rTa) s1
  rw [semXIR_seq]
  generalize semXIR I (.load fU rTa) s1 = s2 at u1 u3 hM2 y2
  have hb2 : rdK s2.M fU = R (j + 1) := by
    rw [rdK_eq u1, ← hR (j + 1) hj]
    exact rdK_eq (b1 _ (by simp only [uT1]; (clear * - hta; omega)) (by simp only [rTa]; (clear * - hta; omega)))
  obtain ⟨v1, v2⟩ := plusOne_sem I s2 hM2
  have hM3 := inv_sem I wf_plusOne hM2
  have y3 := size_sem I (.blk [.op .xor fW fU cOne]) s2
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .xor fW fU cOne]) s2 = s3 at v1 v2 hM3 y3
  have m4 := mulK_sem (I := I) (s := s3) hM3 (d := fH) (a := fU) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 9 ≤ i → i ≠ fH → rd (semXIR I (mulK fH fU fW) s3).M i = rd s3.M i :=
    fun i h0 h1 => mulK_frame I s3 h0 h1
  have hM4 := inv_sem I (wf_mulK fH fU fW (by decide)) hM3
  have y4 := size_sem I (mulK fH fU fW) s3
  rw [semXIR_seq]
  generalize semXIR I (mulK fH fU fW) s3 = s4 at m4 f4 hM4 y4
  have i5 := invK_sem (I := I) (s := s4) hM4 (d := fAl) (a := fH) (by decide) (by decide)
  have f5 : ∀ i, 12 ≤ i → i ≠ fAl → rd (semXIR I (invK fAl fH) s4).M i = rd s4.M i :=
    fun i h0 h1 => by rw [invK, sem_blk]; exact invKC_frame _ _ (.inr h0) h1 _
  have hM5 := inv_sem I (wf_invK fAl fH (by decide)) hM4
  have y5 := size_sem I (invK fAl fH) s4
  rw [semXIR_seq]
  generalize semXIR I (invK fAl fH) s4 = s5 at i5 f5 hM5 y5
  have c5 : rdK s5.M fAl = (R (j + 1) * (R (j + 1) + 1))⁻¹ := by
    rw [i5, m4, v1, rdK_eq (v2 _ (by decide)), hb2]
  have k5 : ∀ x, 256 ≤ x → rd s5.M x = rd s.M x := fun x hx => by
    rw [f5 x (by (clear * - hx; omega)) (by simp only [fAl]; (clear * - hx; omega)), f4 x (by (clear * - hx; omega)) (by simp only [fH]; (clear * - hx; omega)),
      v2 x (by simp only [fW]; (clear * - hx; omega)), u3 x (by simp only [fU]; (clear * - hx; omega)),
      b1 x (by simp only [uT1]; (clear * - hx; omega)) (by simp only [rTa]; (clear * - hx; omega))]
  have r5 : ∀ r, (r = rTr ∨ r = rLv) → rd s5.M r = rd s.M r := fun r hr => by
    rcases hr with rfl | rfl <;>
    rw [f5 _ (by decide) (by decide), f4 _ (by decide) (by decide), v2 _ (by decide),
      u3 _ (by decide), b1 _ (by decide) (by decide)]
  -- the entries
  have hs5 := hM5.1
  simp only [regs] at hs5
  have r6 : rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 (toWord N)]) s5).M rTa = toWord (ta + 0) ∧
      rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 (toWord N)]) s5).M rN2 = toWord N := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rTa, rN2]; (clear * - s5 N s ta j hs s1 y1 s2 y2 s3 y3 s4 y4 y5; omega))) only
      [rd_set_self, rd_set_ne]
    rw [r5 _ (.inl rfl), hTr, or_self_eval]; rfl
  have b6 : ∀ x, x ≠ rTa → x ≠ rN2 → rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 (toWord N)])
      s5).M x = rd s5.M x := fun x h1 h2 =>
    rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩)
  have hM6 := inv_sem I (P := .blk [.op .or rTa rTr rTr, .const rN2 (toWord N)])
    (by simp +decide [WF, Prim.dst, rTa, rN2]) hM5
  have y6 := size_sem I (.blk [.op .or rTa rTr rTr, .const rN2 (toWord N)]) s5
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 (toWord N)]) s5 = s6 at r6 b6 hM6 y6
  obtain ⟨a6, n6⟩ := r6
  rw [semXIR_seq, loopK_eq I (rowNBody N) s6 hM6 (by decide) (by decide) (by decide) n6]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 (toWord N) s6.M) i = rd s6.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := toWord N) hM6 (by decide)
  let c := (R (j + 1) * (R (j + 1) + 1))⁻¹
  let P : ℕ → St → Prop := fun k s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rTa = toWord (ta + k) ∧ rdK s'.M fAl = c ∧ rd s'.M rTr = toWord ta ∧
    rd s'.M rLv = toWord j ∧
    (∀ x, regs ≤ x → (x < ta + N ∨ ta + N + k ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < k, rdK s'.M (ta + N + i) = R i * (R i + 1) * c
  have step : ∀ k s', k < N → P k s' → P (k + 1) (decS rC2 (semXIR I (rowNBody N) s')) := by
    rintro k s' hk ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rowNBody_sem (hN := hN) I s' i1 hk (by simp only [regs]; (clear * - hta; omega)) hta2
      (by (clear * - hsz y1 y2 y3 y4 y5 y6 i2; omega)) i3
    have hd : ∀ x, x ≠ rC2 → rd (decS rC2 (semXIR I (rowNBody N) s')).M x =
        rd (semXIR I (rowNBody N) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hRk : rdK s'.M (ta + k) = R k := by
      rw [← hR k hk]
      exact rdK_eq (i7 _ (by simp only [regs]; (clear * - hta; omega)) (by (clear * - hk; omega)))
    refine ⟨by (try dsimp only); exact inv_decS (inv_sem I (wf_rowNBody N) i1) (by decide), by rw [size_decS, size_sem, i2],
      by rw [hd _ (by decide), e3], by rw [rdK_decS _ (by decide), e4, i4],
      by rw [hd _ (by decide), e5, i5], by rw [hd _ (by decide), e6, i6],
      fun x hx hx2 => ?_, fun i hi => ?_⟩
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC2]; (clear * - hx; omega)), e2 x (by simp only [regs]; omega) (by (clear * - hx2; omega)),
        i7 x (by simp only [regs]; (clear * - hx; omega)) (by (clear * - hx2; omega))]
    · rw [rdK_eq (hd _ (by simp only [rC2]; (clear * - hN hj hta; omega)))]
      by_cases h : i = k
      · subst h; rw [e1, hRk, i4]
      · rw [rdK_eq (e2 _ (by simp only [regs]; (clear * - hta hk hi; omega)) (by (clear * - h; omega))), i8 i (by (clear * - hi h; omega))]
  have hP0 : P 0 ⟨entryK rC2 rN2 (toWord N) s6.M, s6.o⟩ := by
    refine ⟨by dsimp only; exact hME, by simp only [size_entryK, y6, y5, y4, y3, y2, y1], ?_, ?_, ?_, ?_,
      fun x hx _ => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · dsimp only; rw [hE _ (by decide) (by decide), a6]
    · dsimp only
      rw [rdK_eq ((hE _ (by decide) (by decide)).trans (b6 _ (by decide) (by decide))), c5]
    · dsimp only
      rw [hE _ (by decide) (by decide), b6 _ (by decide) (by decide), r5 _ (.inl rfl), hTr]
    · dsimp only
      rw [hE _ (by decide) (by decide), b6 _ (by decide) (by decide), r5 _ (.inr rfl), hLv]
    · dsimp only
      simp only [regs] at hx
      rw [hE _ (by simp only [rC2]; (clear * - hx; omega)) (by (clear * - hT4 hx; omega)), b6 _ (by simp only [rTa]; (clear * - hx; omega))
        (by simp only [rN2]; (clear * - hx; omega)), k5 x hx]
  have := iterL_ind (f := semXIR I (rowNBody N)) (c := rC2) (m := N) P step N 0 _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - N; omega))) hP0
  rw [Nat.zero_add] at this
  rw [toNat_toWord (show N < 2 ^ 64 by (clear * - hN; omega))]
  generalize iterL (semXIR I (rowNBody N)) rC2 N ⟨entryK rC2 rN2 (toWord N) s6.M, s6.o⟩ = s7 at this ⊢
  obtain ⟨g1, g2, -, -, g5, g6, g7, g8⟩ := this
  have hs7 := g1.1
  simp only [regs] at hs7
  have hb : ∀ x, x ≠ rLv → x ≠ uT1 → x ≠ rTr → rd (semXIR I (.blk [.op .add rLv rLv cOne,
      .const uT1 (toWord N), .op .add rTr rTr uT1]) s7).M x = rd s7.M x := fun x h1 h2 h3 =>
    rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩)
  have wfin : WF (.blk [.op .add rLv rLv cOne, .const uT1 (toWord N), .op .add rTr rTr uT1]) := by
    simp +decide [WF, Prim.dst, rLv, uT1, rTr]
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, ?_, ?_, inv_sem I wfin g1, ?_⟩
  rotate_left 4
  · rw [size_sem, g2]
  · rw [rdK_eq (hb _ (by simp only [rLv]; (clear * - hN hj hta; omega)) (by simp only [uT1]; (clear * - hN hj hta; omega))
      (by simp only [rTr]; (clear * - hN hj hta; omega))), g8 i hi]
  · simp only [regs] at hx
    rw [hb _ (by simp only [rLv]; (clear * - hx; omega)) (by simp only [uT1]; (clear * - hx; omega)) (by simp only [rTr]; (clear * - hx; omega)),
      g7 x (by simp only [regs]; (clear * - hx; omega)) (by (clear * - hx2; omega))]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; (clear * - s7 N s ta j R hs s1 y1 s2 y2 s3 y3 s4 y4 s5 y5 s6 y6 hP0 g2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [g6, show rd s7.M cOne = 1 from g1.2 0 (by decide), add_one_toWord]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; (clear * - s7 N s ta j R hs s1 y1 s2 y2 s3 y3 s4 y4 s5 y5 s6 y6 hP0 g2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [g5, add_toWord]

/-- **The basis table** (`(wtabNIR N tb)`): the rows `wRow ptK N v`, `v < N`, at `tb + N v + i`;
the heap outside `[tb, tb + N * N)` is kept. -/
theorem wtabNIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) (hN1 : 1 ≤ N) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + N * N < 2 ^ 64) (hsz : tb + N * N ≤ s.M.size) :
    (∀ v < N, ∀ i < N, rdK (semXIR I ((wtabNIR N tb)) s).M (tb + N * v + i) =
      (wRow ptK N v).getD i 0) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + N * N ≤ x) → rd (semXIR I ((wtabNIR N tb)) s).M x = rd s.M x) ∧
    Inv (semXIR I ((wtabNIR N tb)) s).M ∧ (semXIR I ((wtabNIR N tb)) s).M.size = s.M.size := by
  have hNN : N ≤ N * N := Nat.le_mul_self N
  have hs := hM.1
  simp only [regs] at hs htb
  have hT4 : cTmp = 4 := rfl
  have w0 : WF (.blk [.const rTr (toWord tb)]) := by simp +decide [WF, Prim.dst, rTr,
    List.mem_cons, List.mem_nil_iff, forall_eq, or_false]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rTr (toWord tb)]) s
  have hH0 := hframe I (.blk [.const rTr (toWord tb)]) s (by simp +decide [Lo, Prim.dst, regs,
    rTr, List.mem_cons, List.mem_nil_iff, forall_eq, or_false])
  have t0 : rd (semXIR I (.blk [.const rTr (toWord tb)]) s).M rTr = toWord tb := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rTr]; (clear * - hs z0; omega))
  rw [wtabNIR, semXIR_seq]
  generalize semXIR I (.blk [.const rTr (toWord tb)]) s = s0 at hM0 z0 hH0 t0
  obtain ⟨o1, o2, o3, hM1, z1⟩ := row0NIR_sem (hN := hN) I s0 hM0 (by simp only [regs]; (clear * - htb; omega)) (by (clear * - htb2 hNN; omega))
    (by (clear * - hsz hNN z0; omega)) t0
  rw [semXIR_seq]
  generalize semXIR I (row0NIR N) s0 = s1 at o1 o2 o3 hM1 z1
  have r2 : rd (semXIR I (.blk [.const rLv 0, .const rN3 (toWord (N - 1))]) s1).M rLv = toWord 0 ∧
      rd (semXIR I (.blk [.const rLv 0, .const rN3 (toWord (N - 1))]) s1).M rN3 = toWord (N - 1) := by
    have := hM1.1; simp only [regs] at this
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLv, rN3]; (clear * - s1 N s tb hs s0 z0 z1; omega))) only
      [rd_set_self, rd_set_ne] <;> rfl
  have b2 : ∀ x, x ≠ rLv → x ≠ rN3 → rd (semXIR I (.blk [.const rLv 0, .const rN3 (toWord (N - 1))]) s1).M x =
      rd s1.M x := fun x h1 h2 =>
    rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩)
  have hM2 := inv_sem I (P := .blk [.const rLv 0, .const rN3 (toWord (N - 1))]) (by simp +decide [WF,
    Prim.dst, rLv, rN3]) hM1
  have z2 := size_sem I (.blk [.const rLv 0, .const rN3 (toWord (N - 1))]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rLv 0, .const rN3 (toWord (N - 1))]) s1 = s2 at r2 b2 hM2 z2
  obtain ⟨l2, n2⟩ := r2
  rw [loopK_eq I (rowNIR N) s2 hM2 (by decide) (by decide) (by decide) n2,
    toNat_toWord (show N - 1 < 2 ^ 64 by (clear * - hN hN1; omega))]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 (toWord (N - 1)) s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := toWord (N - 1)) hM2 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rLv = toWord j ∧ rd s'.M rTr = toWord (tb + N * j) ∧
    (∀ v ≤ j, ∀ i < N, rdK s'.M (tb + N * v + i) = (wRow ptK N v).getD i 0) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + N * (j + 1) ≤ x) → rd s'.M x = rd s.M x)
  have step : ∀ j s', j < N - 1 → P j s' → P (j + 1) (decS rC3 (semXIR I (rowNIR N) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hjN : N * j + 2 * N ≤ N * N := by
      rw [show N * j + 2 * N = N * (j + 2) by ring]; exact Nat.mul_le_mul_left N (by (clear * - hN hN1 hj; omega))
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rowNIR_sem (hN := hN) I s' i1 (ta := tb + N * j)
      (R := fun i => (wRow ptK N j).getD i 0) (by (clear * - hN hN1 hj; omega)) (by simp only [regs]; (clear * - htb; omega))
      (by (clear * - htb2 hjN; omega)) (by (clear * - hsz z0 z1 z2 i2 hjN; omega)) i3 i4 (fun i hi => i5 j le_rfl i hi)
    have hd : ∀ x, x ≠ rC3 → rd (decS rC3 (semXIR I (rowNIR N) s')).M x =
        rd (semXIR I (rowNIR N) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨by (try dsimp only); exact inv_decS e5 (by decide), by rw [size_decS, e6, i2], by rw [hd _ (by decide), e3],
      by rw [hd _ (by decide), e4, show tb + N * j + N = tb + N * (j + 1) by ring],
      fun v hv i hi => ?_, fun x hx hx2 => ?_⟩
    · rw [rdK_eq (hd _ (by simp only [rC3]; (clear * - htb; omega)))]
      by_cases h : v = j + 1
      · subst h
        rw [show tb + N * (j + 1) + i = tb + N * j + N + i by ring, e1 i hi,
          wRow_succ_getDN j hi]
      · have hvj := Nat.mul_le_mul_left N (show v ≤ j by (clear * - hv h; omega))
        rw [rdK_eq (e2 _ (by simp only [regs]; (clear * - htb; omega)) (by (clear * - hi hvj; omega))), i5 v (by (clear * - hv h; omega)) i hi]
    · simp only [regs] at hx
      rw [show N * (j + 1 + 1) = N * j + 2 * N by ring] at hx2
      have hj1 : N * (j + 1) = N * j + N := by ring
      rw [hd _ (by simp only [rC3]; (clear * - hx; omega)), e2 x (by simp only [regs]; omega) (by (clear * - hx2 hj1; omega)),
        i6 x (by simp only [regs]; (clear * - hx; omega)) (by (clear * - hN hN1 hx2 hj1; omega))]
  have hP0 : P 0 ⟨entryK rC3 rN3 (toWord (N - 1)) s2.M, s2.o⟩ := by
    refine ⟨by dsimp only; exact hME, by simp only [size_entryK, z2, z1, z0], ?_, ?_, fun v hv i hi => ?_,
      fun x hx hx2 => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), l2]
    · dsimp only
      rw [hE _ (by decide) (by decide), b2 _ (by decide) (by decide), o3]; rfl
    · obtain rfl : v = 0 := by (clear * - hv; omega)
      dsimp only
      rw [rdK_eq ((hE _ (by simp only [rC3]; (clear * - htb; omega)) (by (clear * - htb hT4; omega))).trans
          (b2 _ (by simp only [rLv]; (clear * - htb; omega)) (by simp only [rN3]; (clear * - htb; omega)))),
        Nat.mul_zero, Nat.add_zero, o1 i hi, wRow_zero_getDN hi]
    · dsimp only
      simp only [regs] at hx
      rw [hE _ (by simp only [rC3]; (clear * - hx; omega)) (by (clear * - hT4 hx; omega)), b2 _ (by simp only [rLv]; (clear * - hx; omega))
        (by simp only [rN3]; (clear * - hx; omega)), o2 x (by simp only [regs]; omega) (by (clear * - hx2; omega)),
        hH0 x (by simp only [regs]; (clear * - hx; omega))]
  have := iterL_ind (f := semXIR I (rowNIR N)) (c := rC3) (m := N - 1) P step (N - 1) 0 _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - N; omega))) hP0
  rw [Nat.zero_add] at this
  obtain ⟨f1, f2, -, -, f5, f6⟩ := this
  have eN : N * (N - 1 + 1) = N * N := by rw [Nat.sub_add_cancel hN1]
  exact ⟨fun v hv i hi => f5 v (by (clear * - hN hN1 hv; omega)) i (by omega), fun x hx hx2 => f6 x hx (by (clear * - eN hx2; omega)), f1, f2⟩

/-- **The table holds `Ŵ_v(ptK 2^i)`** (`Lvm.Nb.wRow_spec`). -/
theorem wtabNIR_normW (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) (hN1 : 1 ≤ N) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + N * N < 2 ^ 64) (hsz : tb + N * N ≤ s.M.size) :
    ∀ v < N, ∀ i < N, rdK (semXIR I ((wtabNIR N tb)) s).M (tb + N * v + i) =
      (Lvm.Nb.normW ptK v).eval (ptK (2 ^ i)) := fun v hv i hi => by
  rw [(wtabNIR_sem (hN := hN) (hN1 := hN1) I s hM htb htb2 hsz).1 v hv i hi, wRow_spec ptK_xor (ptK_injOn hN) v hv i hi]

end Lvm.X
end
-- ===== end of `LvmMPXNtt3` =====

/-!
# The forward additive NTT at table dimension `N`: the semantics

* `fpairNBody_sem`, `flevelNIR_sem`: one forward butterfly, one level (`fwdLevel ptK N`);
* **`fwdNIR_sem`**: the row ends holding `fwdRun ptK N ℓ Y` (`ℓ ≤ N ≤ 64`);
* **`fwdNIR_enc`**: on a message of `2^m` coefficients zero-padded to `2^ℓ`, the row ends holding `encN ptK c`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

variable {N : ℕ}

attribute [local irreducible] entryK storeM

/-- The forward NTT's first `j` levels (`fwdTop` at `N`). -/
def fwdTopN (N ℓ : ℕ) : ℕ → (ℕ → BF64) → ℕ → BF64
  | 0, Y => Y
  | j + 1, Y => fwdLevel ptK N (ℓ - 1 - j) (fwdTopN N ℓ j Y)

theorem fwdRun_topN (N ℓ : ℕ) (Y : ℕ → BF64) :
    ∀ j ≤ ℓ, fwdRun ptK N ℓ Y = fwdRun ptK N (ℓ - j) (fwdTopN N ℓ j Y)
  | 0, _ => rfl
  | j + 1, hj => by
    rw [fwdRun_topN N ℓ Y j (by (clear * - j ℓ hj; omega)), show ℓ - j = (ℓ - (j + 1)) + 1 by (clear * - ℓ j hj; omega), fwdRun, fwdTopN,
      show ℓ - (j + 1) = ℓ - 1 - j by (clear * - ℓ j hj; omega)]

theorem wf_fpairNBody (N : ℕ) : WF (fpairNBody N) := by
  simp +decide [fpairNBody, pairPs, farithIR, alphaNIR, alphaBody, addK, WF, Writes, Prim.dst,
    rQ, uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp,
    regs, mulK_wf_iff, mulK_writes_iff]

/-- Proof help for `fpairNBody_nw` (kept separate so that `fpairNBody_nw` itself has no `_simp_` auxiliaries). -/
private theorem fpairNBody_nw_of {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3 ∨ r = rKf ∨ r = rTbf) : ¬ Writes (fpairNBody N) r := by
  have h9 : 9 ≤ r ∧ r ≠ fT := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  simp only [fpairNBody, pairPs, farithIR, alphaNIR, alphaBody, addK, Writes, Prim.dst,
    mulK_writes_iff h9.1 h9.2, List.mem_cons, exists_eq_or_imp, exists_eq_left, List.mem_nil_iff, or_false]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rQ, uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, rA0,
      rP2, rTr, rLv, rC1, rN1, rC3, rN3, rKf, rTbf] <;> decide

theorem fpairNBody_nw {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3 ∨ r = rKf ∨ r = rTbf) : ¬ Writes (fpairNBody N) r :=
  fpairNBody_nw_of hr

/-- **One forward butterfly**: the pair's low and high elements become `u + α w` and
`u + α w + w`, `α = Σ_{i<N} [bit_i(base)] T(i)`; nothing else on the heap changes; `q += 1`. -/
theorem fpairNBody_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {A ta l q : ℕ} {T : ℕ → BF64}
    (hl : l < 64) (hA : regs ≤ A) (hq : q < 2 ^ 64) (hhi : A + hiP l q < 2 ^ 64)
    (hsz : A + hiP l q < s.M.size) (hta : regs ≤ ta) (hta2 : ta + N < 2 ^ 64)
    (hQ : rd s.M rQ = toWord q) (hP2 : rd s.M rP2 = toWord (2 ^ l)) (hA0 : rd s.M rA0 = toWord A)
    (hTr : rd s.M rTr = toWord ta) (hT : ∀ i < N, rdK s.M (ta + i) = T i) :
    rdK (semXIR I (fpairNBody N) s).M (A + loP l q) = rdK s.M (A + loP l q) +
      (∑ i ∈ range N, if (baseP l q).testBit i then T i else 0) * rdK s.M (A + hiP l q) ∧
    rdK (semXIR I (fpairNBody N) s).M (A + hiP l q) = rdK s.M (A + loP l q) +
      (∑ i ∈ range N, if (baseP l q).testBit i then T i else 0) * rdK s.M (A + hiP l q) +
        rdK s.M (A + hiP l q) ∧
    (∀ x, regs ≤ x → x ≠ A + loP l q → x ≠ A + hiP l q →
      rd (semXIR I (fpairNBody N) s).M x = rd s.M x) ∧
    rd (semXIR I (fpairNBody N) s).M rQ = toWord (q + 1) := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hlh := loP_lt_hiP l q
  have hP : 2 ^ l < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hl
  have hbase : baseP l q < 2 ^ 64 := by
    have : baseP l q ≤ loP l q := by simp [loP]
    (clear * - hA hhi hlh this; omega)
  -- the addresses
  have w1 : WF (.blk pairPs) := by
    simp +decide [pairPs, WF, Prim.dst, uT1, uX, uT2, rBs, rAL, rAH]
  obtain ⟨p1, p2, p3⟩ := pairPs_sem I s hM (A := A) hq hP hQ hP2 hA0
  have hM1 := inv_sem I w1 hM
  have z1 := size_sem I (.blk pairPs) s
  have hH1 := hframe I (.blk pairPs) s (by simp +decide [pairPs, Lo, Prim.dst, regs, uT1, uX,
    uT2, rBs, rAL, rAH])
  have q1 : rd (semXIR I (.blk pairPs) s).M rQ = toWord q := by
    rw [frame I _ s w1 hM _ (by decide) (by simp +decide [pairPs, Writes, Prim.dst, uT1, uX,
      uT2, rBs, rAL, rAH, rQ]), hQ]
  have t1 : rd (semXIR I (.blk pairPs) s).M rTr = toWord ta := by
    rw [frame I _ s w1 hM _ (by decide) (by simp +decide [pairPs, Writes, Prim.dst, uT1, uX,
      uT2, rBs, rAL, rAH, rTr]), hTr]
  rw [fpairNBody, semXIR_seq]
  generalize semXIR I (.blk pairPs) s = s1 at p1 p2 p3 hM1 hH1 q1 t1 z1
  have hT1 : ∀ i < N, rdK s1.M (ta + i) = T i := fun i hi => by
    rw [← hT i hi]; exact rdK_eq (hH1 _ (by simp only [regs]; (clear * - hta; omega)))
  -- `α`
  have a2 := alphaNIR_sem I s1 hM1 hN hbase (by simp only [regs]; (clear * - hta; omega)) hta2 p1 t1 hT1
  have hM2 := inv_sem I (wf_alphaNIR N) hM1
  have z2 := size_sem I (alphaNIR N) s1
  have hH2 := hframeK I (alphaNIR N) s1 (loK_alphaNIR (N := N))
  have nwA : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I (alphaNIR N) s1).M r = rd s1.M r :=
    fun r hr => frame I _ s1 (wf_alphaNIR N) hM1 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide [alphaNIR, alphaBody, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rN2,
        rC2, cTmp, rAL, rAH, rQ, or_false])
  rw [semXIR_seq]
  generalize semXIR I (alphaNIR N) s1 = s2 at a2 hM2 hH2 nwA z2
  have l2 : rd s2.M rAL = toWord (A + loP l q) := (nwA _ (.inl rfl)).trans p2
  have h2 : rd s2.M rAH = toWord (A + hiP l q) := (nwA _ (.inr (.inl rfl))).trans p3
  have q2 : rd s2.M rQ = toWord q := (nwA _ (.inr (.inr rfl))).trans q1
  have hY : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => (hH2 x hx).trans (hH1 x hx)
  -- the arithmetic
  obtain ⟨b1, b2⟩ := farith_sem I s2 hM2 (a := A + loP l q) (b := A + hiP l q)
    (by (clear * - hhi hlh; omega)) (by simp only [regs]; (clear * - hA; omega)) (by omega) l2 h2
  have hM3 := inv_sem I wf_farithIR hM2
  have z3 := size_sem I farithIR s2
  have hH3 := hframe I farithIR s2 lo_farithIR
  have nwB : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I farithIR s2).M r = rd s2.M r :=
    fun r hr => frame I _ s2 wf_farithIR hM2 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide [farithIR, addK, Writes, Prim.dst, fU, fW, fH, fT, fN, rAL, rAH, rQ,
        mulK_writes_iff, or_false])
  have eU : rdK s2.M (A + loP l q) = rdK s.M (A + loP l q) :=
    rdK_eq (hY _ (by simp only [regs]; (clear * - hA; omega)))
  have eW : rdK s2.M (A + hiP l q) = rdK s.M (A + hiP l q) :=
    rdK_eq (hY _ (by simp only [regs]; (clear * - hA; omega)))
  rw [eU, eW, a2] at b1
  rw [eU, eW, a2] at b2
  rw [semXIR_seq]
  generalize semXIR I farithIR s2 = s3 at b1 b2 hM3 hH3 nwB z3
  have l3 : rd s3.M rAL = toWord (A + loP l q) := (nwB _ (.inl rfl)).trans l2
  have h3 : rd s3.M rAH = toWord (A + hiP l q) := (nwB _ (.inr (.inl rfl))).trans h2
  have q3 : rd s3.M rQ = toWord q := (nwB _ (.inr (.inr rfl))).trans q2
  -- the stores
  obtain ⟨c1, c2, hM4⟩ := store_sem I s3 hM3 (p := rAL) (v := fN) (x := A + loP l q)
    (by decide) (by decide) l3 (by simp only [regs]; (clear * - hA; omega)) (by (clear * - hhi hlh; omega)) (by (clear * - hsz hlh z1 z2 z3; omega))
  have z4 := size_sem I (.store rAL fN) s3
  rw [semXIR_seq]
  generalize semXIR I (.store rAL fN) s3 = s4 at c1 c2 hM4 z4
  have hT4 : cTmp = 4 := rfl
  have hr4 : ∀ r, r < 256 → r ≠ cTmp → rd s4.M r = rd s3.M r := fun r hr h2 =>
    c2 r (by (clear * - hA hhi hr; omega)) h2
  have h4 : rd s4.M rAH = toWord (A + hiP l q) := (hr4 _ (by decide) (by decide)).trans h3
  have q4 : rd s4.M rQ = toWord q := (hr4 _ (by decide) (by decide)).trans q3
  have f4 : rdK s4.M fH = rdK s3.M fH := rdK_eq (hr4 _ (by decide) (by decide))
  obtain ⟨d1, d2, hM5⟩ := store_sem I s4 hM4 (p := rAH) (v := fH) (x := A + hiP l q)
    (by decide) (by decide) h4 (by simp only [regs]; (clear * - hA; omega)) (by omega) (by (clear * - hsz z1 z2 z3 z4; omega))
  rw [semXIR_seq]
  generalize semXIR I (.store rAH fH) s4 = s5 at d1 d2 hM5
  have hr5 : ∀ r, r < 256 → r ≠ cTmp → rd s5.M r = rd s4.M r := fun r hr h2 =>
    d2 r (by (clear * - hA hr; omega)) h2
  -- `q += 1`
  have e6 : ∀ x, x ≠ rQ → rd (semXIR I (.blk [.op .add rQ rQ cOne]) s5).M x = rd s5.M x :=
    fun x hx => rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact fun h => hx h.symm)
  refine ⟨?_, ?_, fun x hx x1 x2 => ?_, ?_⟩
  · rw [rdK_eq (e6 _ (by simp only [rQ]; (clear * - hA; omega))), rdK_eq (d2 _ (by (clear * - hlh; omega)) (by (clear * - hA hhi hT4; omega))),
      rdK_eq c1, b1]
  · rw [rdK_eq (e6 _ (by simp only [rQ]; (clear * - hA; omega))), rdK_eq d1, f4, b2]
  · simp only [regs] at hx
    rw [e6 _ (by simp only [rQ]; (clear * - hx; omega)), d2 _ x2 (by (clear * - hT4 hx; omega)), c2 _ x1 (by (clear * - hT4 hx; omega)),
      hH3 x (by simp only [regs]; (clear * - hx; omega)), hY x (by simp only [regs]; (clear * - hx; omega))]
  · have hs5 := hM5.1
    simp only [regs] at hs5
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rQ]; (clear * - hs5; omega)), hr5 _ (by decide) (by decide), q4,
      hr5 _ (by decide) (by decide), show rd s4.M cOne = 1 from hM4.2 0 (by decide)]
    exact add_one_toWord q

/-- **A forward level** `l < ℓ` on the row of `2^ℓ` elements at `A`, with the table row
`wRow ptK N l` at `ta`: every element becomes `fwdLevel`'s; the heap outside the row is kept. -/
theorem flevelNIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {A ta ℓ l : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ N) (hl : l < ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (hta : regs ≤ ta) (hta2 : ta + N < 2 ^ 64)
    (hdisj : ta + N ≤ A ∨ A + 2 ^ ℓ ≤ ta)
    (hLv : rd s.M rLv = toWord l) (hA0 : rd s.M rA0 = toWord A) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < N, rdK s.M (ta + i) = (wRow ptK N l).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    (∀ i < 2 ^ ℓ, rdK (semXIR I ((flevelNIR N ℓ)) s).M (A + i) = fwdLevel ptK N l Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd (semXIR I ((flevelNIR N ℓ)) s).M x = rd s.M x) ∧
    (semXIR I ((flevelNIR N ℓ)) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hP1 : 2 ^ (ℓ - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by (clear * - hN hℓ hl; omega))
  have hPl : l * 1 < 64 := by (clear * - hN hℓ hl; omega)
  have w0 : WF (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))]) := by
    simp +decide [WF, Prim.dst, rQ, rP2, rN1, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s
  have hH0 := hframe I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s (by simp +decide [Lo, Prim.dst, regs, rQ, rP2, rN1,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  have r0 : rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rQ = toWord 0 ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rP2 = toWord (2 ^ l) ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rN1 = toWord (2 ^ (ℓ - 1)) ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rA0 = toWord A ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rTr = toWord ta := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rQ, rP2, rN1]; (clear * - s N I A ta ℓ l hs z0; omega))) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hLv, show rd s.M cOne = toWord 1 from hM.2 0 (by decide), shl_toWord (by (clear * - hPl; omega))
        (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by (clear * - hPl; omega))), Nat.one_mul]
    · exact hA0
    · exact hTr
  rw [flevelNIR, semXIR_seq]
  generalize semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s = s0 at hM0 z0 hH0 r0
  obtain ⟨q0, p0, n0, a0, t0⟩ := r0
  rw [loopK_eq I (fpairNBody N) s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hP1]
  have hE : ∀ i, i ≠ rC1 → i ≠ cTmp → rd (entryK rC1 rN1 (toWord (2 ^ (ℓ - 1))) s0.M) i =
      rd s0.M i := fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC1) (n := rN1) (K := toWord (2 ^ (ℓ - 1))) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rQ = toWord j ∧ rd s'.M rP2 = toWord (2 ^ l) ∧ rd s'.M rA0 = toWord A ∧
    rd s'.M rTr = toWord ta ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdK s'.M (A + i) = if pairOf l i < j then fwdLevel ptK N l Y i else Y i
  have nwP : ∀ r, (r = rA0 ∨ r = rP2 ∨ r = rTr) → ∀ s', Inv s'.M →
      rd (decS rC1 (semXIR I (fpairNBody N) s')).M r = rd s'.M r := fun r hr s' hs' => by
    rw [rd_decS (by rcases hr with rfl | rfl | rfl <;> decide)]
    exact frame I _ s' (wf_fpairNBody N) hs' _ (by rcases hr with rfl | rfl | rfl <;> decide)
      (fpairNBody_nw (by rcases hr with rfl | rfl | rfl <;> simp))
  have step : ∀ j s', j < 2 ^ (ℓ - 1) → P j s' →
      P (j + 1) (decS rC1 (semXIR I (fpairNBody N) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    have hhi := hiP_lt hl hj
    have hlh := loP_lt_hiP l j
    have hT' : ∀ i < N, rdK s'.M (ta + i) = (wRow ptK N l).getD i 0 := fun i hi => by
      rw [← hT i hi]
      exact rdK_eq (i7 _ (by simp only [regs]; (clear * - hta; omega)) (by (clear * - hdisj hi; omega)))
    obtain ⟨e1, e2, e3, e4⟩ := fpairNBody_sem (hN := hN) I s' i1 (A := A)
      (T := fun i => (wRow ptK N l).getD i 0)
      (by (clear * - hPl; omega)) (by simp only [regs]; omega) (by (clear * - hP1 hj; omega)) (by (clear * - hA2 hhi; omega)) (by (clear * - hsz z0 i2 hhi; omega))
      (by simp only [regs]; (clear * - hta; omega)) hta2 i3 i4 i5 i6 hT'
    have hd : ∀ x, x ≠ rC1 → rd (decS rC1 (semXIR I (fpairNBody N) s')).M x =
        rd (semXIR I (fpairNBody N) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hlo' := i8 _ (by (clear * - hhi hlh; omega) : loP l j < 2 ^ ℓ)
    have hhi' := i8 _ hhi
    rw [pairOf_loP, if_neg (lt_irrefl j)] at hlo'
    rw [pairOf_hiP, if_neg (lt_irrefl j)] at hhi'
    refine ⟨by (try dsimp only); exact inv_decS (inv_sem I (wf_fpairNBody N) i1) (by decide), by rw [size_decS, size_sem, i2], ?_,
      (nwP _ (.inr (.inl rfl)) s' i1).trans i4, (nwP _ (.inl rfl) s' i1).trans i5,
      (nwP _ (.inr (.inr rfl)) s' i1).trans i6, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide), e4]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC1]; (clear * - hx; omega)), e3 x (by simp only [regs]; omega) (by (clear * - hhi hlh hx2; omega))
        (by (clear * - hhi hx2; omega)), i7 x (by simp only [regs]; omega) hx2]
    · rw [rdK_eq (hd _ (by simp only [rC1, regs] at *; (clear * - hA; omega)))]
      by_cases hq : pairOf l i = j
      · rw [if_pos (by (clear * - hq; omega))]
        rcases pair_cases hq with rfl | rfl
        · rw [e1, hlo', hhi', fwdLevel_lo]; rfl
        · rw [e2, hlo', hhi', fwdLevel_hi]; rfl
      · have hil : i ≠ loP l j := fun h => hq (by rw [h, pairOf_loP])
        have hih : i ≠ hiP l j := fun h => hq (by rw [h, pairOf_hiP])
        rw [rdK_eq (e3 _ (by simp only [regs]; (clear * - hA; omega)) (by (clear * - hlh hil hih; omega)) (by (clear * - hih; omega))), i8 i hi]
        by_cases hlt : pairOf l i < j
        · rw [if_pos hlt, if_pos (by (clear * - hlt; omega))]
        · rw [if_neg hlt, if_neg (by (clear * - hlh hq hil hih hlt; omega))]
  have hP0 : P 0 ⟨entryK rC1 rN1 (toWord (2 ^ (ℓ - 1))) s0.M, s0.o⟩ := by
    refine ⟨by dsimp only; exact hME, by simp only [size_entryK, z0], ?_, ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), q0]
    · dsimp only; rw [hE _ (by decide) (by decide), p0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only
      rw [hE _ (by simp only [rC1, regs] at *; (clear * - hx; omega)) (by simp only [cTmp, regs] at *; (clear * - hx; omega)),
        hH0 x hx]
    · dsimp only
      rw [if_neg (Nat.not_lt_zero _), ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC1]; (clear * - hA; omega)) (by simp only [cTmp]; (clear * - hA; omega))).trans
        (hH0 _ (by simp only [regs]; (clear * - hA; omega))))
  have := iterL_ind (f := semXIR I (fpairNBody N)) (c := rC1) (m := 2 ^ (ℓ - 1)) P step (2 ^ (ℓ - 1))
    0 _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - ℓ; omega))) hP0
  rw [Nat.zero_add] at this
  obtain ⟨-, z, -, -, -, -, f7, f8⟩ := this
  refine ⟨fun i hi => ?_, f7, z⟩
  rw [f8 i hi, if_pos (pairOf_lt hl hi)]

theorem flevelNIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rKf ∨ r = rTbf ∨ r = rC3 ∨ r = rN3) (ℓ : ℕ) :
    ¬ Writes ((flevelNIR N ℓ)) r := by
  intro h
  simp only [flevelNIR, Writes] at h
  rcases h with ⟨p, hp, he⟩ | h | h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, rQ, rP2, rN1, rA0, rKf, rTbf, rC3, rN3] at he
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [rC1, rA0, rKf, rTbf, rC3, rN3] at h
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cTmp, rA0, rKf, rTbf, rC3, rN3] at h
  · exact fpairNBody_nw (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) h

/-! ## The forward NTT -/

theorem fPreN_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {ℓ j tb : ℕ} (hj : j < ℓ)
    (hℓ : ℓ < 2 ^ 64) (hK : rd s.M rKf = toWord (ℓ - j)) (hTb : rd s.M rTbf = toWord tb) :
    rd (semXIR I (.blk (fPreN N)) s).M rLv = toWord (ℓ - 1 - j) ∧
    rd (semXIR I (.blk (fPreN N)) s).M rTr = toWord (tb + N * (ℓ - 1 - j)) ∧
    ∀ x, x ≠ rLv → x ≠ uT1 → x ≠ rTr → rd (semXIR I (.blk (fPreN N)) s).M x = rd s.M x := by
  have hs := hM.1
  simp only [regs] at hs
  have e1 : rd s.M cOne = toWord 1 := hM.2 0 (by decide)
  refine ⟨?_, ?_, fun x h1 h2 h3 => rd_blkN_of_not_writes I _ s (by
    simp [fPreN, Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩)⟩
  · simp only [semXIR, runPrims, fPreN, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; (clear * - s N ℓ j hs; omega))) only
      [rd_set_self, rd_set_ne]
    rw [hK, e1, sub_toWord (by (clear * - hj hℓ; omega)) (by (clear * - hj; omega))]
    congr 1; (clear * - hj; omega)
  · simp only [semXIR, runPrims, fPreN, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; (clear * - s N ℓ j hs; omega))) only
      [rd_set_self, rd_set_ne]
    rw [hK, e1, sub_toWord (by (clear * - hj hℓ; omega)) (by (clear * - hj; omega)), hTb, 
      mul_toWord, add_toWord]
    congr 1; rw [show ℓ - j - 1 = ℓ - 1 - j by (clear * - hj; omega)]; ring

/-- **The forward NTT** (`fwdRun`) on the machine: from the row `Y` of `2^ℓ` elements at `A`
(`rA0 = A`) and the basis table at `tb` (row `v` at `tb + N v`), `(fwdNIR N ℓ tb)` leaves
`fwdRun ptK N ℓ Y` in the row and keeps the heap outside it. -/
theorem fwdNIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ N) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64)
    (hdisj : tb + N * N ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < N, ∀ i < N, rdK s.M (tb + N * v + i) = (wRow ptK N v).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    (∀ i < 2 ^ ℓ, rdK (semXIR I ((fwdNIR N ℓ tb)) s).M (A + i) = fwdRun ptK N ℓ Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd (semXIR I ((fwdNIR N ℓ tb)) s).M x = rd s.M x) ∧
    Inv (semXIR I ((fwdNIR N ℓ tb)) s).M := by
  have hs := hM.1
  simp only [regs] at hs hA htb
  have hℓ64 : ℓ < 2 ^ 64 := by (clear * - hN hℓ; omega)
  have w0 : WF (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)]) := by
    simp +decide [WF, Prim.dst, rKf, rTbf, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
    .const rN3 (toWord ℓ)]) s
  have hH0 := hframe I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
    .const rN3 (toWord ℓ)]) s
    (by simp +decide [Lo, Prim.dst, regs, rKf, rTbf, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have r0 : rd (semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
        .const rN3 (toWord ℓ)]) s).M rKf = toWord (ℓ - 0) ∧
      rd (semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
        .const rN3 (toWord ℓ)]) s).M rTbf = toWord tb ∧
      rd (semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
        .const rN3 (toWord ℓ)]) s).M rN3 = toWord ℓ ∧
      rd (semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
        .const rN3 (toWord ℓ)]) s).M rA0 = toWord A := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rKf, rTbf, rN3]; (clear * - s N I A tb ℓ hs z0; omega))) only
      [rd_set_self, rd_set_ne]
    · rfl
    · exact hA0
  rw [fwdNIR, semXIR_seq]
  generalize semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
    .const rN3 (toWord ℓ)]) s = s0 at hM0 z0 hH0 r0
  obtain ⟨k0, t0, n0, a0⟩ := r0
  rw [loopK_eq I ((fStepN N ℓ)) s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hℓ64]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 (toWord ℓ) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := toWord ℓ) hM0 (by decide)
  have wpre : WF (.blk (fPreN N)) := by simp +decide [fPreN, WF, Prim.dst, rLv, uT1, rTr]
  have wl : WF ((flevelNIR N ℓ)) := (wf_fwdNIR N ℓ tb).2.2.2.2.2.1
  have wlb : WF (.blk [.op .sub rKf rKf cOne]) := by simp +decide [WF, Prim.dst, rKf]
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rKf = toWord (ℓ - j) ∧ rd s'.M rTbf = toWord tb ∧ rd s'.M rA0 = toWord A ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdK s'.M (A + i) = fwdTopN N ℓ j Y i
  have step : ∀ j s', j < ℓ → P j s' → P (j + 1) (decS rC3 (semXIR I ((fStepN N ℓ)) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨p1, p2, p3⟩ := fPreN_sem (hN := hN) I s' i1 hj hℓ64 (tb := tb) i3 i4
    have hM1 := inv_sem I wpre i1
    have hH1 := hframe I (.blk (fPreN N)) s' (by simp +decide [fPreN, Lo, Prim.dst, regs, rLv, uT1,
      rTr])
    have z1 := size_sem I (.blk (fPreN N)) s'
    rw [fStepN, semXIR_seq, semXIR_seq]
    generalize semXIR I (.blk (fPreN N)) s' = s1 at p1 p2 p3 hM1 hH1 z1
    have hjN : N * (ℓ - 1 - j) + N ≤ N * N := by
      rw [show N * (ℓ - 1 - j) + N = N * (ℓ - 1 - j + 1) by ring]
      exact Nat.mul_le_mul_left N (by (clear * - hℓ hj; omega))
    have hT : ∀ i < N, rdK s1.M (tb + N * (ℓ - 1 - j) + i) =
        (wRow ptK N (ℓ - 1 - j)).getD i 0 := fun i hi => by
      rw [← hW (ℓ - 1 - j) (by (clear * - hℓ hj; omega)) i (by omega)]
      exact rdK_eq ((hH1 _ (by simp only [regs]; (clear * - htb; omega))).trans
          (i6 _ (by simp only [regs]; (clear * - htb; omega)) (by (clear * - hA hA2 htb2 hdisj hjN hi; omega))))
    have hY1 : ∀ i < 2 ^ ℓ, rdK s1.M (A + i) = fwdTopN N ℓ j Y i := fun i hi => by
      rw [← i7 i hi]
      exact rdK_eq (hH1 _ (by simp only [regs]; (clear * - hA; omega)))
    have a1 : rd s1.M rA0 = toWord A := (p3 _ (by decide) (by decide) (by decide)).trans i5
    obtain ⟨e1, e2, e3⟩ := flevelNIR_sem (hN := hN) I s1 hM1 (Y := fwdTopN N ℓ j Y) (l := ℓ - 1 - j) (by (clear * - hℓ; omega))
      (by (clear * - hj; omega)) (by simp only [regs]; omega) hA2 (by (clear * - hsz z0 i2 z1; omega)) (by simp only [regs]; (clear * - htb; omega))
      (by (clear * - htb2 hjN; omega)) (by (clear * - hdisj hjN; omega)) p1 a1 p2 hT hY1
    have hM2 := inv_sem I wl hM1
    have nw : ∀ r, (r = rA0 ∨ r = rKf ∨ r = rTbf) →
        rd (semXIR I ((flevelNIR N ℓ)) s1).M r = rd s1.M r :=
      fun r hr => frame I _ s1 wl hM1 _ (by rcases hr with rfl | rfl | rfl <;> decide)
        (flevelNIR_nw (by rcases hr with rfl | rfl | rfl <;> simp) ℓ)
    generalize semXIR I ((flevelNIR N ℓ)) s1 = s2 at e1 e2 e3 hM2 nw
    have hs2 := hM2.1
    simp only [regs] at hs2
    have hd : ∀ x, x ≠ rC3 → rd (decS rC3 (semXIR I (.blk [.op .sub rKf rKf cOne]) s2)).M x =
        rd (semXIR I (.blk [.op .sub rKf rKf cOne]) s2).M x := fun x hx => rd_decS (Ne.symm hx) _
    have hb : ∀ x, x ≠ rKf → rd (semXIR I (.blk [.op .sub rKf rKf cOne]) s2).M x = rd s2.M x :=
      fun x h1 => rd_blkN_of_not_writes I _ _ (by simp [Prim.dst]; exact Ne.symm h1)
    refine ⟨by (try dsimp only); exact inv_decS (inv_sem I wlb hM2) (by decide), by rw [size_decS, size_sem, e3, z1, i2], ?_,
      ?_, ?_, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rKf]; (clear * - s2 N s A tb ℓ hs s0 z0 j s' i2 s1 z1 e3; omega))) only
        [rd_set_self]
      rw [nw _ (.inr (.inl rfl)), p3 _ (by decide) (by decide) (by decide), i3,
        show rd s2.M cOne = toWord 1 from hM2.2 0 (by decide), sub_toWord (by (clear * - hN hℓ htb htb2 hℓ64 hj hjN; omega)) (by (clear * - hj; omega)),
        show ℓ - j - 1 = ℓ - (j + 1) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - ℓ j; omega))]
    · rw [hd _ (by decide), hb _ (by decide), nw _ (.inr (.inr rfl)),
        p3 _ (by decide) (by decide) (by decide), i4]
    · rw [hd _ (by decide), hb _ (by decide), nw _ (.inl rfl), a1]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC3]; (clear * - hx; omega)), hb _ (by simp only [rKf]; (clear * - hx; omega)),
        e2 x (by simp only [regs]; (clear * - hx; omega)) hx2, hH1 x (by simp only [regs]; (clear * - hx; omega)),
        i6 x (by simp only [regs]; (clear * - hx; omega)) hx2]
    · rw [rdK_eq ((hd _ (by simp only [rC3]; (clear * - hA; omega))).trans (hb _ (by simp only [rKf]; (clear * - hA; omega)))),
        e1 i hi]
      rfl
  have hP0 : P 0 ⟨entryK rC3 rN3 (toWord ℓ) s0.M, s0.o⟩ := by
    refine ⟨by dsimp only; exact hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), k0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only
      rw [hE _ (by simp only [rC3, regs] at *; (clear * - hx; omega)) (by simp only [cTmp, regs] at *; (clear * - hx; omega)),
        hH0 x hx]
    · dsimp only
      rw [show fwdTopN N ℓ 0 Y i = Y i from rfl, ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC3]; (clear * - hA; omega)) (by simp only [cTmp]; (clear * - hA; omega))).trans
        (hH0 _ (by simp only [regs]; (clear * - hA; omega))))
  have := iterL_ind (f := semXIR I ((fStepN N ℓ))) (c := rC3) (m := ℓ) P step ℓ 0 _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - ℓ; omega))) hP0
  rw [Nat.zero_add] at this
  refine ⟨fun i hi => ?_, this.2.2.2.2.2.1, this.1⟩
  rw [this.2.2.2.2.2.2 i hi, fwdRun_topN N ℓ Y ℓ le_rfl, Nat.sub_self]
  rfl

/-- **`Enc` on the machine**: on a message `c` of `2^m` coefficients zero-padded to the row of
`2^ℓ` elements (`m ≤ ℓ ≤ N`), `(fwdNIR N ℓ tb)` leaves `Enc(c)` at `ptK j`, i.e. `encN ptK c j`, at
every position `j < 2^ℓ`. -/
theorem fwdNIR_enc (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) {A tb ℓ m : ℕ}
    (hℓ : ℓ ≤ N) (hmℓ : m ≤ ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64)
    (hdisj : tb + N * N ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < N, ∀ i < N, rdK s.M (tb + N * v + i) = (wRow ptK N v).getD i 0)
    (c : Fin (2 ^ m) → BF64)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = if h : i < 2 ^ m then c ⟨i, h⟩ else 0) :
    ∀ j < 2 ^ ℓ, rdK (semXIR I ((fwdNIR N ℓ tb)) s).M (A + j) = encN ptK c j := by
  intro j hj
  rw [(fwdNIR_sem (hN := hN) I s hM hℓ hA hA2 hsz htb htb2 hdisj hA0 hW
    (Y := fun i => if h : i < 2 ^ m then c ⟨i, h⟩ else 0) hY).1 j hj]
  exact fwdRun_enc ptK_xor (ptK_injOn hN) hmℓ hℓ c _ (fun _ => rfl) hj

end Lvm.X
