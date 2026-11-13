-- New for lvm2 roll 11 (M′, R11-X): the level-0 agreement scan's semantics at `st` positions. Adapted from
-- `LvmXAgree.lean` (`foldIR_sem`, `testIR_sem`, `AgreeP`, `agreeM`, `posBody_sem`, `agreeM_succ`,
-- `length_agreeM_le`, `ReadsOut`, `agreeP_congr`, `agreeIR_sem`) and `LvmXDecBr.lean` (`agreeP_iff`): the
-- `2^15` positions (and coordinate stride) become `st`; `macC_sem`, `laneBody_sem`, `appendIR_sem` are reused.
import LvmMPXDecIR
import LvmMPDec

/-!
# The level-0 agreement scan at `st` positions

* `foldIR_semN`: the fold at a position `q < st` (64 lanes, the word at `wB + 64 q + t`).
* `testNIR_sem`, `posNBody_sem`, **`agreeNIR_sem`**: the scan over `q < st` lists the positions where the fold's
  three coordinates equal `Enc(f)[q]`'s at `eB + c·st + q` (`agreeNM`).
* **`agreeNM_eq_agreeG`**: with the word, the `eq(α, ·)` table and `Enc(f)`'s coordinates in memory, `agreeNM` at
  `st = 2^nL` is `LvmMPDec.agreeG nL kL`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

theorem lo_testNIR (st eB : ℕ) : LoK (testNIR st eB) := by
  simp +decide [testNIR, LoK, Prim.dst, gK, gX, gE, gZ, gZ2, regs]

/-- **The fold at the position `q`** (`gQ = q`): the three accumulators hold `foldPM … 64`;
the heap and the registers outside the fold's are kept. -/
theorem foldIR_semN (I : Array Word) (s : St) (hM : Inv s.M) {wB qB q : ℕ} (hwB : regs ≤ wB)
    {st : ℕ} (hq : q < st) (hwB2 : wB + 64 * st < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 192 < 2 ^ 64)
    (hQ : rd s.M gQ = toWord q) :
    (∀ c < 3, rdK (semXIR I (foldIR wB qB) s).M (gA0 + c) = foldPM s.M wB qB q c 64) ∧
    (∀ r, KeepF r → rd (semXIR I (foldIR wB qB) s).M r = rd s.M r) ∧
    Inv (semXIR I (foldIR wB qB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB
  have hpw : wB + 64 * q + 63 < 2 ^ 64 := by omega
  have w0 : WF (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64, .op .mul gPw gQ gK,
      .const gK (toWord (wB + 63)), .op .add gPw gPw gK, .const gPe (toWord qB),
      .const gN2 64]) := by
    simp +decide [WF, Prim.dst, gA0, gA1, gA2, gK, gPw, gPe, gN2]
  have hM0 := inv_sem I w0 hM
  rw [foldIR, semXIR_seq]
  have r0 : rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gPw = toWord (wB + 64 * q + 63) ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gPe = toWord qB ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gN2 = toWord 64 ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gA0 = 0 ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gA1 = 0 ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gA2 = 0 := by
    rw [sem_blk']
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, gA0, gA1, gA2, gK, gPw, gPe, gN2]; omega))
      only [rd_set_self, rd_set_ne]
    · rw [hQ, show (64 : Word) = toWord 64 from rfl, mul_toWord, add_toWord]
      congr 1; ring
    · rfl
  have k0 : ∀ r, KeepF r → rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0,
      .const gK 64, .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
      .const gPe (toWord qB), .const gN2 64]) s).M r = rd s.M r := fun r hr => by
    simp only [KeepF, gA0, gA1, gA2, gPe, gPw, gV, gE, gT, gK, gC2, gN2, cTmp] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, gA0, gA1, gA2, gPe, gPw, gK, gN2] <;> omega
  generalize semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
    .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
    .const gPe (toWord qB), .const gN2 64]) s = s0 at hM0 r0 k0
  obtain ⟨p0, e0, n0, a0, a1, a2⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧
    rd s'.M gPw = toWord (wB + 64 * q + 63 - j) ∧ rd s'.M gPe = toWord (qB + 3 * j) ∧
    rdK s'.M gA0 = foldPM s.M wB qB q 0 j ∧ rdK s'.M gA1 = foldPM s.M wB qB q 1 j ∧
    rdK s'.M gA2 = foldPM s.M wB qB q 2 j ∧ (∀ r, KeepF r → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ gC2 → i ≠ cTmp → rd (entryK gC2 gN2 (toWord 64) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC2 gN2 (toWord 64) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), p0, Nat.sub_zero]
    · rw [hE _ (by decide) (by decide), e0, Nat.mul_zero, Nat.add_zero]
    · rw [rdK, hE _ (by decide) (by decide), a0]; rfl
    · rw [rdK, hE _ (by decide) (by decide), a1]; rfl
    · rw [rdK, hE _ (by decide) (by decide), a2]; rfl
    · rw [hE _ hr.2.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.2.1, k0 r hr]
  have hstep : ∀ j s', j < 64 → P j s' → P (j + 1) (decS gC2 (semXIR I laneBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hK : ∀ x, regs ≤ x → rdK s'.M x = rdK s.M x := fun x hx => by
      simp only [rdK]; rw [i7 x (keepF_of_regs hx)]
    obtain ⟨l1, l2, l3, l4, l5, l6, hM'⟩ := laneBody_sem I s' i1 (pw := wB + 64 * q + 63 - j)
      (pe := qB + 3 * j) (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega)
      (by omega) i2 i3
    have hd : ∀ x, x ≠ gC2 → rd (decS gC2 (semXIR I laneBody s')).M x =
        rd (semXIR I laneBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hpw : wB + 64 * q + 63 - j = wB + 64 * q + (63 - j) := by omega
    refine ⟨inv_decS hM' (by decide), ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · rw [hd _ (by decide), l4, show wB + 64 * q + 63 - j - 1 = wB + 64 * q + 63 - (j + 1) by omega]
    · rw [hd _ (by decide), l5, show qB + 3 * j + 3 = qB + 3 * (j + 1) by ring]
    · rw [show rdK (decS gC2 (semXIR I laneBody s')).M gA0 = rdK (semXIR I laneBody s').M gA0 by
        simp only [rdK]; rw [hd _ (by decide)], l1, i4, foldPM, foldPM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; omega), hK _ (by simp only [regs]; omega), hpw, Nat.add_zero]
    · rw [show rdK (decS gC2 (semXIR I laneBody s')).M gA1 = rdK (semXIR I laneBody s').M gA1 by
        simp only [rdK]; rw [hd _ (by decide)], l2, i5, foldPM, foldPM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; omega), hK _ (by simp only [regs]; omega), hpw]
    · rw [show rdK (decS gC2 (semXIR I laneBody s')).M gA2 = rdK (semXIR I laneBody s').M gA2 by
        simp only [rdK]; rw [hd _ (by decide)], l3, i6, foldPM, foldPM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; omega), hK _ (by simp only [regs]; omega), hpw]
    · have hr' := hr
      obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -, r9, -, -, r12⟩ := hr'
      rw [hd _ r9, l6 r r0 r1 r2 r3 r4 r5 r6 r7 r12, i7 r hr]
  have hfin := loopK_run I laneBody P s0 hM0 (c := gC2) (n := gN2) (K := 64) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  obtain ⟨f1, -, -, f4, f5, f6, f7⟩ := hfin
  refine ⟨fun c hc => ?_, f7, f1⟩
  interval_cases c
  · exact f4
  · exact f5
  · exact f6

/-- **The comparison**: `gZ` is `1` iff the three accumulators equal the three words of
`Enc₀(f₁)[q]`'s coordinates (`eB + c·st + q`); only `gK, gX, gE, gZ, gZ2` change. -/
theorem testNIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {st eB q : ℕ} (heB : regs ≤ eB)
    (hq : q < st) (hst : st < 2 ^ 64) (heB2 : eB + 3 * st < 2 ^ 64) (hQ : rd s.M gQ = toWord q) :
    rd (semXIR I (testNIR st eB) s).M gZ =
      bW (decide (rd s.M (eB + q) = rd s.M gA0) && decide (rd s.M (eB + st + q) = rd s.M gA1) &&
        decide (rd s.M (eB + 2 * st + q) = rd s.M gA2)) ∧
    (∀ r, r ≠ gK → r ≠ gX → r ≠ gE → r ≠ gZ → r ≠ gZ2 → rd (semXIR I (testNIR st eB) s).M r = rd s.M r) ∧
    Inv (semXIR I (testNIR st eB) s).M := by
  have hs := hM.1
  simp only [regs] at hs heB
  have hw : WF (testNIR st eB) := by simp +decide [testNIR, WF, Prim.dst, gK, gX, gE, gZ, gZ2]
  refine ⟨?_, fun r r1 r2 r3 r4 r5 => ?_, inv_sem I hw hM⟩
  · simp only [testNIR, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, gA0, gA1, gA2]; omega)) only [rd_set_self, rd_set_ne]
    rw [hQ, add_toWord, toNat_toWord (by omega), add_toWord, toNat_toWord (by omega), add_toWord,
      toNat_toWord (by omega)]
    simp (disch := first | decide | (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, gA0, gA1, gA2]; omega)) only [rd_set_self, rd_set_ne]
    rw [eq_bW, eq_bW, eq_bW, bW_and, bW_and]
    congr 3 <;> ring_nf
  · by_cases hr : r < regs
    · refine frame I (testNIR st eB) s hw hM r hr ?_
      simp only [testNIR, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left]
      omega
    · exact hframeK I (testNIR st eB) s (lo_testNIR st eB) r (by omega)

/-- The fold and `Enc₀(f₁)`'s three coordinates agree at `q` (memory `M`, the machine's test). -/
abbrev AgreeNP (M : Mem) (st wB qB eB q : ℕ) : Prop :=
  wK (rd M (eB + q)) = foldPM M wB qB q 0 64 ∧ wK (rd M (eB + st + q)) = foldPM M wB qB q 1 64 ∧
    wK (rd M (eB + 2 * st + q)) = foldPM M wB qB q 2 64

/-- **The machine's agreement list** below `n`. -/
def agreeNM (M : Mem) (st wB qB eB n : ℕ) : List ℕ :=
  (List.range n).filter fun q => decide (AgreeNP M st wB qB eB q)



/-- **One position**: `q` is listed at `agB + c` iff the fold agrees with `Enc₀(f₁)` at `q`;
`gQ := q + 1`; the heap outside the listed cell is kept. -/
theorem posNBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {st wB qB eB agB q c : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 64 * st < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 192 < 2 ^ 64)
    (heB : regs ≤ eB) (heB2 : eB + 3 * st < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + st < 2 ^ 64) (hags : agB + st ≤ s.M.size)
    (hq : q < st) (hcq : c ≤ q) (hQ : rd s.M gQ = toWord q) (hC : rd s.M gCnt = toWord c) :
    rd (semXIR I (posNBody st wB qB eB agB) s).M gQ = toWord (q + 1) ∧
    (if AgreeNP s.M st wB qB eB q then
      rd (semXIR I (posNBody st wB qB eB agB) s).M gCnt = toWord (c + 1) ∧
        rd (semXIR I (posNBody st wB qB eB agB) s).M (agB + c) = toWord q ∧
        ∀ x, regs ≤ x → x ≠ agB + c → rd (semXIR I (posNBody st wB qB eB agB) s).M x = rd s.M x
    else
      rd (semXIR I (posNBody st wB qB eB agB) s).M gCnt = toWord c ∧
        ∀ x, regs ≤ x → rd (semXIR I (posNBody st wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (posNBody st wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  rw [posNBody, semXIR_seq]
  obtain ⟨f1, f2, hM1⟩ := foldIR_semN I s hM (wB := wB) (qB := qB) (by simp only [regs]; omega) hq
    hwB2 (by simp only [regs]; omega) hqB2 hQ
  have z1 := size_sem I (foldIR wB qB) s
  generalize semXIR I (foldIR wB qB) s = s1 at f1 f2 hM1 z1
  have q1 : rd s1.M gQ = toWord q := (f2 gQ keepF_gQ).trans hQ
  have c1 : rd s1.M gCnt = toWord c := (f2 gCnt keepF_gCnt).trans hC
  have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s.M x := fun x hx => f2 x (keepF_of_regs hx)
  rw [semXIR_seq]
  obtain ⟨t1, t2, hM2⟩ := testNIR_sem I s1 hM1 (eB := eB) (by simp only [regs]; omega) hq (by omega) heB2 q1
  have z2 := size_sem I (testNIR st eB) s1
  generalize semXIR I (testNIR st eB) s1 = s2 at t1 t2 hM2 z2
  -- the flag is the test
  have f10 : wK (rd s1.M gA0) = foldPM s.M wB qB q 0 64 := f1 0 (by norm_num)
  have f11 : wK (rd s1.M gA1) = foldPM s.M wB qB q 1 64 := f1 1 (by norm_num)
  have f12 : wK (rd s1.M gA2) = foldPM s.M wB qB q 2 64 := f1 2 (by norm_num)
  have e : ∀ a b, regs ≤ a → wK (rd s1.M b) = foldPM s.M wB qB q (b - gA0) 64 →
      (rd s1.M a = rd s1.M b ↔ wK (rd s.M a) = foldPM s.M wB qB q (b - gA0) 64) := by
    intro a b ha hb
    rw [← wK_inj, h1 a ha, hb]
  have hZ : rd s2.M gZ = bW (decide (AgreeNP s.M st wB qB eB q)) := by
    rw [t1]
    congr 1
    simp only [AgreeNP, Bool.decide_and]
    rw [decide_eq_decide.2 (e _ gA0 (by simp only [regs]; omega) f10),
      decide_eq_decide.2 (e _ gA1 (by simp only [regs]; omega) f11),
      decide_eq_decide.2 (e _ gA2 (by simp only [regs]; omega) f12), Bool.and_assoc]
    rfl
  have q2 : rd s2.M gQ = toWord q := (t2 gQ (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans q1
  have c2 : rd s2.M gCnt = toWord c := (t2 gCnt (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans c1
  have h2 : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    rw [t2 x (by simp only [gK]; omega) (by simp only [gX]; omega) (by simp only [gE]; omega)
      (by simp only [gZ]; omega) (by simp only [gZ2]; omega), h1 x (by simp only [regs]; omega)]
  -- `q += 1`
  have fin : ∀ s3 : St, Inv s3.M → rd s3.M gQ = toWord q →
      rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M gQ = toWord (q + 1) ∧
      (∀ x, x ≠ gQ → rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M x = rd s3.M x) ∧
      Inv (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M := fun s3 h3 hq3 => by
    have := h3.1; simp only [regs] at this
    refine ⟨?_, fun x hx => rd_blk_of_not_dst I _ s3 (by simp [Prim.dst]; exact Ne.symm hx),
      inv_sem I (P := .blk [.op .add gQ gQ cOne]) (by simp +decide [WF, Prim.dst, gQ]) h3⟩
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [gQ]; omega), hq3, show rd s3.M cOne = 1 from h3.2 0 (by decide),
      add_one_toWord]
  rw [semXIR_seq, semXIR_ite, hZ]
  by_cases hb : AgreeNP s.M st wB qB eB q
  · rw [decide_eq_true hb, if_neg bW_true_ne, if_pos hb]
    obtain ⟨a1, a2, a3, hM3⟩ := appendIR_sem I s2 hM2 (agB := agB) (c := c)
      (by simp only [regs]; omega) (by omega) (by omega) (by omega) c2
    generalize semXIR I (appendIR agB) s2 = s3 at a1 a2 a3 hM3
    have hagc : ∀ r, r < regs → r ≠ agB + c := fun r hr => by simp only [regs] at hr; omega
    obtain ⟨g1, g2, hM4⟩ := fin s3 hM3 (by
      rw [a3 gQ (by decide) (by decide) (by decide) (by decide) (hagc _ (by decide)), q2])
    refine ⟨g1, ⟨?_, ?_, fun x hx hx2 => ?_⟩, hM4⟩
    · rw [g2 _ (by decide), a2]
    · rw [g2 _ (Ne.symm (hagc _ (by decide))), a1, q2]
    · simp only [regs] at hx
      rw [g2 x (by simp only [gQ]; omega), a3 x (by simp only [gK]; omega) (by simp only [gX]; omega)
        (by simp only [gCnt]; omega) (by simp only [cTmp]; omega) hx2, h2 x (by simp only [regs]; omega)]
  · rw [decide_eq_false hb, bW_false_eq, if_pos rfl, if_neg hb]
    have e3 : semXIR I (.blk []) s2 = s2 := by cases s2; rfl
    rw [e3]
    obtain ⟨g1, g2, hM4⟩ := fin s2 hM2 q2
    refine ⟨g1, ⟨by rw [g2 _ (by decide), c2], fun x hx => ?_⟩, hM4⟩
    simp only [regs] at hx
    rw [g2 x (by simp only [gQ]; omega), h2 x (by simp only [regs]; omega)]

theorem agreeNM_succ (M : Mem) (st wB qB eB n : ℕ) : agreeNM M st wB qB eB (n + 1) =
    agreeNM M st wB qB eB n ++ if AgreeNP M st wB qB eB n then [n] else [] := by
  rw [agreeNM, agreeNM, List.range_succ, List.filter_append]
  congr 1
  by_cases h : AgreeNP M st wB qB eB n
  · rw [if_pos h]; simp only [List.filter_cons, List.filter_nil, decide_eq_true h, ite_true]
  · rw [if_neg h]; simp only [List.filter_cons, List.filter_nil, decide_eq_false h]; rfl

theorem length_agreeNM_le (M : Mem) (st wB qB eB n : ℕ) : (agreeNM M st wB qB eB n).length ≤ n :=
  (List.length_filter_le _ _).trans (by simp)

/-- The cells the test reads, outside the list's region. -/
def ReadsNOut (st wB qB eB agB : ℕ) : Prop :=
  (agB + st ≤ wB ∨ wB + 64 * st ≤ agB) ∧ (agB + st ≤ qB ∨ qB + 192 ≤ agB) ∧
    (agB + st ≤ eB ∨ eB + 3 * st ≤ agB)

theorem agreeNP_congr {M M' : Mem} {st wB qB eB agB q : ℕ} (hq : q < st) (hwB : regs ≤ wB)
    (hqB : regs ≤ qB) (heB : regs ≤ eB) (hR : ReadsNOut st wB qB eB agB)
    (h : ∀ x, regs ≤ x → (x < agB ∨ agB + st ≤ x) → rd M' x = rd M x) :
    AgreeNP M' st wB qB eB q ↔ AgreeNP M st wB qB eB q := by
  obtain ⟨r1, r2, r3⟩ := hR
  simp only [regs] at hwB hqB heB
  have hF : ∀ c < 3, foldPM M' wB qB q c 64 = foldPM M wB qB q c 64 := fun c hc =>
    Finset.sum_congr rfl fun l hl => by
      have hl' := mem_range.1 hl
      simp only [rdK]
      rw [h (qB + 3 * l + c) (by simp only [regs]; omega) (by omega),
        h (wB + 64 * q + (63 - l)) (by simp only [regs]; omega) (by omega)]
  simp only [AgreeNP]
  rw [hF 0 (by norm_num), hF 1 (by norm_num), hF 2 (by norm_num),
    h (eB + q) (by simp only [regs]; omega) (by omega),
    h (eB + st + q) (by simp only [regs]; omega) (by omega),
    h (eB + 2 * st + q) (by simp only [regs]; omega) (by omega)]

/-- **The agreement scan**: the count is `|agreeNM|` and `agB + t` holds the `t`-th agreeing
position (`agreeNM s.M st wB qB eB st`, the positions in increasing order); the heap outside
`[agB, agB + st)` is kept. -/
theorem agreeNIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {st wB qB eB agB : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 64 * st < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 192 < 2 ^ 64)
    (heB : regs ≤ eB) (heB2 : eB + 3 * st < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + st < 2 ^ 64) (hags : agB + st ≤ s.M.size)
    (hR : ReadsNOut st wB qB eB agB) :
    rd (semXIR I (agreeNIR st wB qB eB agB) s).M gCnt =
      toWord (agreeNM s.M st wB qB eB (st)).length ∧
    (∀ t < (agreeNM s.M st wB qB eB (st)).length,
      rd (semXIR I (agreeNIR st wB qB eB agB) s).M (agB + t) =
        toWord ((agreeNM s.M st wB qB eB (st)).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + st ≤ x) →
      rd (semXIR I (agreeNIR st wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (agreeNIR st wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  have w0 : WF (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) := by
    simp +decide [WF, Prim.dst, gQ, gCnt, gN1]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s
  have r0 : rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s).M gQ =
        toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s).M gCnt =
        toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s).M gN1 =
        toWord (st) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, gQ, gCnt, gN1]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const gQ 0, .const gCnt 0,
      .const gN1 (toWord (st))]) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, gQ, gCnt, gN1] <;> omega
  rw [agreeNIR, semXIR_seq]
  generalize semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨q0, c0, n0⟩ := r0
  set L := fun j => agreeNM s.M st wB qB eB j with hL
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M gQ = toWord j ∧ rd s'.M gCnt = toWord (L j).length ∧
    (∀ t < (L j).length, rd s'.M (agB + t) = toWord ((L j).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + st ≤ x) → rd s'.M x = rd s.M x)
  have hE : ∀ i, i ≠ gC1 → i ≠ cTmp → rd (entryK gC1 gN1 (toWord (st)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC1 gN1 (toWord (st)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun t ht => absurd ht (by simp [hL, agreeNM]), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), q0]
    · rw [hE _ (by decide) (by decide), c0]; simp [hL, agreeNM]
    · simp only [regs] at hx
      rw [hE _ (by simp only [gC1]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < st → P j s' →
      P (j + 1) (decS gC1 (semXIR I (posNBody st wB qB eB agB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hlen := length_agreeNM_le s.M st wB qB eB j
    have hlenL : (L j).length ≤ j := hlen
    obtain ⟨e1, e2, e3⟩ := posNBody_sem I s' i1 (wB := wB) (qB := qB) (eB := eB) (agB := agB)
      (c := (L j).length) (by simp only [regs]; omega) hwB2 (by simp only [regs]; omega) hqB2
      (by simp only [regs]; omega) heB2 (by simp only [regs]; omega) hag2 (by omega) hj hlen i3 i4
    have hd : ∀ x, x ≠ gC1 → rd (decS gC1 (semXIR I (posNBody st wB qB eB agB) s')).M x =
        rd (semXIR I (posNBody st wB qB eB agB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hM' := inv_decS e3 (show 4 ≤ gC1 by decide)
    have hz' : (decS gC1 (semXIR I (posNBody st wB qB eB agB) s')).M.size = s.M.size := by
      rw [size_decS, size_sem, i2]
    have hA : AgreeNP s'.M st wB qB eB j ↔ AgreeNP s.M st wB qB eB j :=
      agreeNP_congr hj (by simp only [regs]; omega) (by simp only [regs]; omega)
        (by simp only [regs]; omega) hR i6
    dsimp only [P]
    rw [hL]
    dsimp only
    rw [agreeNM_succ]
    by_cases hb : AgreeNP s.M st wB qB eB j
    · rw [if_pos (hA.2 hb)] at e2
      obtain ⟨g1, g2, g3⟩ := e2
      rw [if_pos hb]
      have hlen1 : (agreeNM s.M st wB qB eB j ++ [j]).length = (L j).length + 1 := by
        rw [List.length_append, List.length_singleton]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1, hlen1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; omega)]
        rw [hlen1] at ht
        by_cases htc : t = (L j).length
        · subst htc
          rw [g2, List.getD_append_right _ _ _ _ (by simp [hL])]
          simp [hL]
        · rw [g3 _ (by simp only [regs]; omega) (by omega), i5 t (by omega),
            List.getD_append _ _ _ _ (by simp only [hL] at *; omega)]
      · rw [hd _ (by simp only [gC1, regs] at *; omega), g3 x hx (by omega), i6 x hx hx2]
    · rw [if_neg (fun h => hb (hA.1 h))] at e2
      obtain ⟨g1, g2⟩ := e2
      rw [if_neg hb, List.append_nil]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; omega), g2 _ (by simp only [regs]; omega), i5 t ht]
      · rw [hd _ (by simp only [gC1, regs] at *; omega), g2 x hx, i6 x hx hx2]
  have := loopK_run I (posNBody st wB qB eB agB) P s0 hM0 (c := gC1) (n := gN1) (K := st)
    (by decide) (by decide) (by decide) n0 (by omega) h0 hstep
  exact ⟨this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2, this.1⟩

/-! ## The link to `LvmMPDec.agreeG` -/

/-- **`Enc` in coordinates** (`enc0_coords` at `2^kL` coefficients): `encG kL f` from `f`'s three limbs. -/
theorem encG_coords (kL : ℕ) (f : ℕ → Ext3) (g : ℕ → ℕ → BF64)
    (hg : ∀ v < 2 ^ kL, f v = mkE (g 0 v) (g 1 v) (g 2 v)) (q : ℕ) :
    encG kL f q = mkE (encN ptK (fun x : Fin (2 ^ kL) => g 0 x) q)
      (encN ptK (fun x : Fin (2 ^ kL) => g 1 x) q) (encN ptK (fun x : Fin (2 ^ kL) => g 2 x) q) := by
  have e : ∀ c, encN ptK (fun x : Fin (2 ^ kL) => g c x) q = ∑ v ∈ range (2 ^ kL), g c v * nbAt v q :=
    fun c => by
      rw [encN, ← Fin.sum_univ_eq_sum_range (fun v => g c v * nbAt v q)]; rfl
  rw [e, e, e, ← mkE_sum, encG]
  exact sum_congr rfl fun v hv => by rw [hg v (mem_range.1 hv), mkE_mul_ofK]

/-- The test at one position is the generic decoder's (`agreeP_iff` at `st` positions, `encG kL`). -/
theorem agreeNP_iff {M : Mem} {st kL wB qB eB q : ℕ} (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hq : q < st)
    (hW : ∀ q < st, ∀ t < 64, rdK M (wB + 64 * q + t) = wd q t)
    (hQ : ∀ l < 64, rdE M (qB + 3 * l) = eqA α l)
    (hE : ∀ q < st, encG kL f q =
      mkE (rdK M (eB + q)) (rdK M (eB + st + q)) (rdK M (eB + 2 * st + q))) :
    AgreeNP M st wB qB eB q ↔ foldAt α wd q = encG kL f q := by
  have hF : foldAt α wd q = mkE (foldPM M wB qB q 0 64) (foldPM M wB qB q 1 64)
      (foldPM M wB qB q 2 64) := by
    rw [foldAt_coords α wd q (fun c l => rdK M (qB + 3 * l + c))
      (fun l hl => by rw [← hQ l hl]; rfl)]
    have e : ∀ c, ∑ l ∈ range 64, rdK M (qB + 3 * l + c) * rowW wd l q = foldPM M wB qB q c 64 :=
      fun c => sum_congr rfl fun l hl => by
        rw [rowW, hW q hq (63 - l) (by have := mem_range.1 hl; omega)]
    rw [e 0, e 1, e 2]
  rw [hF, hE q hq]
  constructor
  · rintro ⟨h0, h1, h2⟩
    show mkE _ _ _ = mkE _ _ _
    rw [← h0, ← h1, ← h2]; rfl
  · intro h
    obtain ⟨h0, h1, h2⟩ := mkE_inj h
    exact ⟨h0.symm, h1.symm, h2.symm⟩

/-- **The machine's agreement list is the generic decoder's** (`agreeM_eq_agreeL` at `2^nL` positions). -/
theorem agreeNM_eq_agreeG {M : Mem} {nL kL wB qB eB : ℕ} (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ nL, ∀ t < 64, rdK M (wB + 64 * q + t) = wd q t)
    (hQ : ∀ l < 64, rdE M (qB + 3 * l) = eqA α l)
    (hE : ∀ q < 2 ^ nL, encG kL f q =
      mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ nL + q)) (rdK M (eB + 2 * 2 ^ nL + q))) :
    agreeNM M (2 ^ nL) wB qB eB (2 ^ nL) = agreeG nL kL wd α f := by
  unfold agreeNM agreeG
  refine List.filter_congr fun q hq => ?_
  exact decide_eq_decide.2 (agreeNP_iff wd α f (List.mem_range.1 hq) hW hQ hE)

end Lvm.X
