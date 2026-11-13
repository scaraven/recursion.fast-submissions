-- New for lvm2 roll 11 (M′, R11-X): the inverse NTT's semantics at any table dimension `N`. Adapted from
-- `LvmXNtt2.lean` (`loK_alphaIR`, `alphaBody_sem`, `alphaIR_sem`, `alphaIR_wAt`, `pairBody_nw`, `pairBody_sem`,
-- `levelIR_sem`, `levelIR_nw`, `bflyIR_sem`, `bflyIR_coeffs`) with the literal `15` (bits, row stride,
-- `nLog`) replaced by `N`; the shape-free helpers (`rdK_eq`, `arith_sem`, `pairPs_sem`, …) are reused.
import LvmMPXNtt
import LvmXNtt2

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
    simp (disch := first | decide | (simp only [size_set, rBit, uT1]; omega)) only
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
    (by decide) a1 (by omega)
  rw [semXIR_seq]
  generalize semXIR I (.load fG rTa) s1 = s2 at l1 l2 hM2
  have hs2 := hM2.1
  simp only [regs] at hs2
  have g2 : wK (rd s2.M fG) = T j := by
    rw [← hT]; exact rdK_eq (l1.trans (hH1 _ (by simp only [regs]; omega)))
  have k1 : rd s2.M rBit = XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord base) (toWord j)) 1) :=
    (l2 _ (by decide)).trans b1
  have k2 : rd s2.M fAl = rd s.M fAl := (l2 _ (by decide)).trans f1
  have k4 : rd s2.M rTa = toWord (ta + j) := (l2 _ (by decide)).trans a1
  have k5 : rd s2.M uI = toWord j := (l2 _ (by decide)).trans i1
  have k6 : rd s2.M cOne = 1 := (l2 _ (by decide)).trans o1
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_, ?_⟩
  · simp only [rdK]
    simp (disch := first | decide | (simp only [size_set, fG, fAl, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [k1, k2, eval_xor, mask_bit _ hb (by omega), wK_acc, g2]
  · simp (disch := first | decide | (simp only [size_set, fG, fAl, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [k5, k6, add_one_toWord]
  · simp (disch := first | decide | (simp only [size_set, fG, fAl, rTa, uI]; omega)) only
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
    simp (disch := first | decide | (simp only [size_set, fAl, uI, rTa, rN2]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rfl
    · rw [hTr, or_self_eval]; rfl
    · exact hBs
  rw [alphaNIR, semXIR_seq]
  generalize semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 (toWord N)]) s
    = s0 at hM0 hH0 r0
  obtain ⟨z0, i0, t0, b0, n0⟩ := r0
  rw [loopK_eq I alphaBody s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord (show N < 2 ^ 64 by omega)]
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
      exact rdK_eq (q5 (ta + j) (by simp only [regs]; omega))
    obtain ⟨e1, e2, e3⟩ := alphaBody_semN I s' q1 (T := T) hb hj (by omega) (by simp only [regs]; omega) hta2
      q4 q2 q3 hTj
    refine ⟨inv_decS (inv_sem I wb q1) (by decide), ?_, ?_, ?_, fun x hx => ?_, ?_⟩
    · rw [rd_decS (by decide), e2]
    · rw [rd_decS (by decide), e3]
    · rw [rd_decS (by decide), frame I _ s' wb q1 _ (by decide) (by
        simp +decide [alphaBody, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rBs,
          or_false]), q4]
    · rw [rd_decS (by simp only [rC2, regs] at *; omega), hframeK I _ s' lb x hx, q5 x hx]
    · rw [rdK_decS _ (by decide), e1, q6, sum_range_succ]
  have hP0 : P 0 ⟨entryK rC2 rN2 (toWord N) s0.M, s0.o⟩ := by
    refine ⟨hME, ?_, ?_, ?_, fun x hx => ?_, ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), i0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), b0]
    · dsimp only
      rw [hE _ (by simp only [rC2, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
    · dsimp only
      rw [rdK_eq (hE _ (by decide) (by decide)), z0]; rfl
  have := iterL_ind (f := semXIR I alphaBody) (c := rC2) (m := N) P step N 0 _ (by omega) hP0
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

theorem pairNBody_nw {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3) : ¬ Writes (pairNBody N) r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide [pairNBody, pairPs, arithIR, alphaNIR, alphaBody, addK, Writes, Prim.dst, rQ,
    uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, rA0,
    rP2, rTr, rLv, rC1, rN1, rC3, rN3, mulK_writes_iff, or_false]

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
    omega
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
    rw [← hT i hi]; exact rdK_eq (hH1 _ (by simp only [regs]; omega))
  -- `α`
  have a2 := alphaNIR_sem I s1 hM1 hN hbase (by simp only [regs]; omega) hta2 p1 t1 hT1
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
    (by omega) (by simp only [regs]; omega) (by omega) l2 h2
  have hM3 := inv_sem I wf_arithIR hM2
  have z3 := size_sem I arithIR s2
  have hH3 := hframe I arithIR s2 lo_arithIR
  have nwB : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I arithIR s2).M r = rd s2.M r :=
    fun r hr => frame I _ s2 wf_arithIR hM2 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide [arithIR, addK, Writes, Prim.dst, fU, fW, fH, fT, fN, rAL, rAH, rQ,
        mulK_writes_iff, or_false])
  have eU : rdK s2.M (A + loP l q) = rdK s.M (A + loP l q) :=
    rdK_eq (hY _ (by simp only [regs]; omega))
  have eW : rdK s2.M (A + hiP l q) = rdK s.M (A + hiP l q) :=
    rdK_eq (hY _ (by simp only [regs]; omega))
  rw [eU, eW, a2] at b1
  rw [eU, eW] at b2
  rw [semXIR_seq]
  generalize semXIR I arithIR s2 = s3 at b1 b2 hM3 hH3 nwB z3
  have l3 : rd s3.M rAL = toWord (A + loP l q) := (nwB _ (.inl rfl)).trans l2
  have h3 : rd s3.M rAH = toWord (A + hiP l q) := (nwB _ (.inr (.inl rfl))).trans h2
  have q3 : rd s3.M rQ = toWord q := (nwB _ (.inr (.inr rfl))).trans q2
  -- the stores
  obtain ⟨c1, c2, hM4⟩ := store_sem I s3 hM3 (p := rAL) (v := fN) (x := A + loP l q)
    (by decide) (by decide) l3 (by simp only [regs]; omega) (by omega) (by omega)
  have z4 := size_sem I (.store rAL fN) s3
  rw [semXIR_seq]
  generalize semXIR I (.store rAL fN) s3 = s4 at c1 c2 hM4 z4
  have hT4 : cTmp = 4 := rfl
  have hr4 : ∀ r, r < 256 → r ≠ cTmp → rd s4.M r = rd s3.M r := fun r hr h2 =>
    c2 r (by omega) h2
  have h4 : rd s4.M rAH = toWord (A + hiP l q) := (hr4 _ (by decide) (by decide)).trans h3
  have q4 : rd s4.M rQ = toWord q := (hr4 _ (by decide) (by decide)).trans q3
  have f4 : rdK s4.M fH = rdK s3.M fH := rdK_eq (hr4 _ (by decide) (by decide))
  obtain ⟨d1, d2, hM5⟩ := store_sem I s4 hM4 (p := rAH) (v := fH) (x := A + hiP l q)
    (by decide) (by decide) h4 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (.store rAH fH) s4 = s5 at d1 d2 hM5
  have hr5 : ∀ r, r < 256 → r ≠ cTmp → rd s5.M r = rd s4.M r := fun r hr h2 =>
    d2 r (by omega) h2
  -- `q += 1`
  have e6 : ∀ x, x ≠ rQ → rd (semXIR I (.blk [.op .add rQ rQ cOne]) s5).M x = rd s5.M x :=
    fun x hx => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact fun h => hx h.symm) _
  refine ⟨?_, ?_, fun x hx x1 x2 => ?_, ?_⟩
  · rw [rdK_eq (e6 _ (by simp only [rQ]; omega)), rdK_eq (d2 _ (by omega) (by omega)),
      rdK_eq c1, b1]
  · rw [rdK_eq (e6 _ (by simp only [rQ]; omega)), rdK_eq d1, f4, b2]
  · simp only [regs] at hx
    rw [e6 _ (by simp only [rQ]; omega), d2 _ x2 (by omega), c2 _ x1 (by omega),
      hH3 x (by simp only [regs]; omega), hY x (by simp only [regs]; omega)]
  · have hs5 := hM5.1
    simp only [regs] at hs5
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rQ]; omega), hr5 _ (by decide) (by decide), q4,
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
  have hP1 : 2 ^ (ℓ - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hPl : l * 1 < 64 := by omega
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
    simp (disch := first | decide | (simp only [size_set, rQ, rP2, rN1]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hLv, show rd s.M cOne = toWord 1 from hM.2 0 (by decide), shl_toWord (by omega)
        (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)), Nat.one_mul]
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
      exact rdK_eq (i7 _ (by simp only [regs]; omega) (by omega))
    obtain ⟨e1, e2, e3, e4⟩ := pairNBody_sem I s' i1 hN (A := A)
      (T := fun i => (wRow ptK N l).getD i 0)
      (by omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
      (by simp only [regs]; omega) hta2 i3 i4 i5 i6 hT'
    have hd : ∀ x, x ≠ rC1 → rd (decS rC1 (semXIR I (pairNBody N) s')).M x =
        rd (semXIR I (pairNBody N) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hlo' := i8 _ (by omega : loP l j < 2 ^ ℓ)
    have hhi' := i8 _ hhi
    rw [pairOf_loP, if_neg (lt_irrefl j)] at hlo'
    rw [pairOf_hiP, if_neg (lt_irrefl j)] at hhi'
    refine ⟨inv_decS (inv_sem I (wf_pairNBody N) i1) (by decide), by rw [size_decS, size_sem, i2], ?_,
      (nwP _ (.inr (.inl rfl)) s' i1).trans i4, (nwP _ (.inl rfl) s' i1).trans i5,
      (nwP _ (.inr (.inr rfl)) s' i1).trans i6, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide), e4]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC1]; omega), e3 x (by simp only [regs]; omega) (by omega)
        (by omega), i7 x (by simp only [regs]; omega) hx2]
    · rw [rdK_eq (hd _ (by simp only [rC1, regs] at *; omega))]
      by_cases hq : pairOf l i = j
      · rw [if_pos (by omega)]
        rcases pair_cases hq with rfl | rfl
        · rw [e1, hlo', hhi', bflyLevel_lo]; rfl
        · rw [e2, hlo', hhi', bflyLevel_hi]
      · have hil : i ≠ loP l j := fun h => hq (by rw [h, pairOf_loP])
        have hih : i ≠ hiP l j := fun h => hq (by rw [h, pairOf_hiP])
        rw [rdK_eq (e3 _ (by simp only [regs]; omega) (by omega) (by omega)), i8 i hi]
        by_cases hlt : pairOf l i < j
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt, if_neg (by omega)]
  have hP0 : P 0 ⟨entryK rC1 rN1 (toWord (2 ^ (ℓ - 1))) s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), q0]
    · dsimp only; rw [hE _ (by decide) (by decide), p0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only
      rw [hE _ (by simp only [rC1, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
    · dsimp only
      rw [if_neg (Nat.not_lt_zero _), ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC1]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
  have := iterL_ind (f := semXIR I (pairNBody N)) (c := rC1) (m := 2 ^ (ℓ - 1)) P step (2 ^ (ℓ - 1)) 0
    _ (by omega) hP0
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
  have hℓ64 : ℓ < 2 ^ 64 := by omega
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
    simp (disch := first | decide | (simp only [size_set, rLv, rTr, rN3]; omega)) only
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
      rw [show N * j + N = N * (j + 1) by ring]; exact Nat.mul_le_mul_left N (by omega)
    have hT : ∀ i < N, rdK s'.M (tb + N * j + i) = (wRow ptK N j).getD i 0 :=
      fun i hi => by
        rw [← hW j (by omega) i (by omega)]
        exact rdK_eq (i6 _ (by simp only [regs]; omega) (by omega))
    obtain ⟨e1, e2, e3⟩ := levelNIR_sem I s' i1 hN (Y := bflyRun ptK N 0 j Y) (by omega) hj
      (by simp only [regs]; omega) hA2 (by omega) (by simp only [regs]; omega) (by omega)
      (by omega) i3 i5 i4 hT i7
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
      rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩) _
    refine ⟨inv_decS (inv_sem I wlb hM1) (by decide), by rw [size_decS, size_sem, e3, i2], ?_, ?_,
      ?_, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
        [rd_set_self, rd_set_ne]
      rw [nw _ (.inr (.inl rfl)), i3, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
        add_one_toWord]
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
        [rd_set_self, rd_set_ne]
      rw [nw _ (.inr (.inr rfl)), i4, add_toWord]
      congr 1; ring
    · rw [hd _ (by decide), hb _ (by decide) (by decide) (by decide), nw _ (.inl rfl), i5]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC3]; omega), hb _ (by simp only [rLv]; omega)
        (by simp only [uT1]; omega) (by simp only [rTr]; omega), e2 x (by simp only [regs]; omega)
        hx2, i6 x (by simp only [regs]; omega) hx2]
    · rw [rdK_eq ((hd _ (by simp only [rC3]; omega)).trans (hb _ (by simp only [rLv]; omega)
        (by simp only [uT1]; omega) (by simp only [rTr]; omega))), e1 i hi]
      rfl
  have hP0 : P 0 ⟨entryK rC3 rN3 (toWord ℓ) s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), l0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only
      rw [hE _ (by simp only [rC3, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
    · dsimp only
      rw [show bflyRun ptK N 0 0 Y i = Y i from rfl, ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC3]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
  have := iterL_ind (f := semXIR I ((lvlNStep N ℓ))) (c := rC3) (m := ℓ) P step ℓ 0 _ (by omega) hP0
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
