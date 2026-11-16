-- New for lvm2 roll 11 (M′, R11-X): the level-≥1 decoder program `dec1MPIR N nL kL` computes `decode1G N nL kL`.
-- Adapted from `LvmXDec1IR.lean` (`Dec1Lay`, `enc1C_sem`, `enc1IR_sem`) and `LvmXDec1IR2.lean` (`dec1Tail_sem`,
-- `dec1IR_sem`) at a generic shape: `2^nL` positions, `2^kL` coefficients, table dimension `N`, the workspace of
-- `LvmMPXDecIR` (`q1M`, `ok1M`, `wb1M`, `eb1M`, `ag1M`, `enc1M`, `ob1M`).
import LvmMPXInterp
import LvmMPXDecIR
import LvmMPDec
import LvmMPXNtt4
import LvmMPXCost

-- ===== merged from `LvmMPXAgree` (GOLF module merge: `LvmMPXAgree.lean` is now a stub importing `LvmMPXDec1Sem`) =====
section
-- New for lvm2 roll 11 (M′, R11-X): the level-0 agreement scan's semantics at `st` positions. Adapted from
-- `LvmXAgree.lean` (`foldIR_sem`, `testIR_sem`, `AgreeP`, `agreeM`, `posBody_sem`, `agreeM_succ`,
-- `length_agreeM_le`, `ReadsOut`, `agreeP_congr`, `agreeIR_sem`) and `LvmXDecBr.lean` (`agreeP_iff`): the
-- `2^15` positions (and coordinate stride) become `st`; `macC_sem`, `laneBody_sem`, `appendIR_sem` are reused.

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
  have hpw : wB + 64 * q + 63 < 2 ^ 64 := by (clear * - hq hwB2; omega)
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
      simp only [Prim.dst, gA0, gA1, gA2, gPe, gPw, gK, gN2] <;> (clear * - hr; omega)
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
      (pe := qB + 3 * j) (by simp only [regs]; (clear * - hwB hwB2 hj; omega)) (by (clear * - hq hwB2 hj; omega)) (by simp only [regs]; (clear * - hqB hqB2 hj; omega))
      (by (clear * - hqB hqB2 hj; omega)) i2 i3
    have hd : ∀ x, x ≠ gC2 → rd (decS gC2 (semXIR I laneBody s')).M x =
        rd (semXIR I laneBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hpw : wB + 64 * q + 63 - j = wB + 64 * q + (63 - j) := by (clear * - hwB hj; omega)
    refine ⟨inv_decS hM' (by decide), ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · rw [hd _ (by decide), l4, show wB + 64 * q + 63 - j - 1 = wB + 64 * q + 63 - (j + 1) by (clear * -; omega)]
    · rw [hd _ (by decide), l5, show qB + 3 * j + 3 = qB + 3 * (j + 1) by ring]
    · rw [show rdK (decS gC2 (semXIR I laneBody s')).M gA0 = rdK (semXIR I laneBody s').M gA0 by
        simp only [rdK]; rw [hd _ (by decide)], l1, i4, foldPM, foldPM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; (clear * - hqB hqB2 hj; omega)), hK _ (by simp only [regs]; (clear * - hwB hwB2 hpw; omega)), hpw, Nat.add_zero]
    · rw [show rdK (decS gC2 (semXIR I laneBody s')).M gA1 = rdK (semXIR I laneBody s').M gA1 by
        simp only [rdK]; rw [hd _ (by decide)], l2, i5, foldPM, foldPM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; (clear * - hqB hqB2 hj; omega)), hK _ (by simp only [regs]; (clear * - hwB hwB2 hpw; omega)), hpw]
    · rw [show rdK (decS gC2 (semXIR I laneBody s')).M gA2 = rdK (semXIR I laneBody s').M gA2 by
        simp only [rdK]; rw [hd _ (by decide)], l3, i6, foldPM, foldPM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; (clear * - hqB hqB2 hj; omega)), hK _ (by simp only [regs]; (clear * - hwB hwB2 hpw; omega)), hpw]
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
    rw [hQ, add_toWord, toNat_toWord (by (clear * - hq heB2; omega)), add_toWord, toNat_toWord (by (clear * - hq heB2; omega)), add_toWord,
      toNat_toWord (by (clear * - hq heB2; omega))]
    simp (disch := first | decide | (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, gA0, gA1, gA2]; omega)) only [rd_set_self, rd_set_ne]
    rw [eq_bW, eq_bW, eq_bW, bW_and, bW_and]
    congr 3 <;> ring_nf
  · by_cases hr : r < regs
    · refine frame I (testNIR st eB) s hw hM r hr ?_
      simp only [testNIR, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left]
      (clear * - r1 r2 r3 r4 r5; omega)
    · exact hframeK I (testNIR st eB) s (lo_testNIR st eB) r (by (clear * - hr; omega))

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
  obtain ⟨t1, t2, hM2⟩ := testNIR_sem I s1 hM1 (eB := eB) (by simp only [regs]; omega) hq (by (clear * - hwB hwB2; omega)) heB2 q1
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
    rw [decide_eq_decide.2 (e _ gA0 (by simp only [regs]; (clear * - heB; omega)) f10),
      decide_eq_decide.2 (e _ gA1 (by simp only [regs]; (clear * - heB hq hcq; omega)) f11),
      decide_eq_decide.2 (e _ gA2 (by simp only [regs]; (clear * - heB hq hcq; omega)) f12), Bool.and_assoc]
    rfl
  have q2 : rd s2.M gQ = toWord q := (t2 gQ (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans q1
  have c2 : rd s2.M gCnt = toWord c := (t2 gCnt (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans c1
  have h2 : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    rw [t2 x (by simp only [gK]; (clear * - hx; omega)) (by simp only [gX]; (clear * - hx; omega)) (by simp only [gE]; (clear * - hx; omega))
      (by simp only [gZ]; (clear * - hx; omega)) (by simp only [gZ2]; (clear * - hx; omega)), h1 x (by simp only [regs]; omega)]
  -- `q += 1`
  have fin : ∀ s3 : St, Inv s3.M → rd s3.M gQ = toWord q →
      rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M gQ = toWord (q + 1) ∧
      (∀ x, x ≠ gQ → rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M x = rd s3.M x) ∧
      Inv (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M := fun s3 h3 hq3 => by
    have := h3.1; simp only [regs] at this
    refine ⟨?_, fun x hx => rd_blk_of_not_dst I _ s3 (by simp [Prim.dst]; exact Ne.symm hx),
      inv_sem I (P := .blk [.op .add gQ gQ cOne]) (by simp +decide [WF, Prim.dst, gQ]) h3⟩
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [gQ]; (clear * - this; omega)), hq3, show rd s3.M cOne = 1 from h3.2 0 (by decide),
      add_one_toWord]
  rw [semXIR_seq, semXIR_ite, hZ]
  by_cases hb : AgreeNP s.M st wB qB eB q
  · rw [decide_eq_true hb, if_neg bW_true_ne, if_pos hb]
    obtain ⟨a1, a2, a3, hM3⟩ := appendIR_sem I s2 hM2 (agB := agB) (c := c)
      (by simp only [regs]; omega) (by (clear * - hag2 hq hcq; omega)) (by (clear * - hags hq hcq z1 z2; omega)) (by (clear * - heB heB2 hq hcq; omega)) c2
    generalize semXIR I (appendIR agB) s2 = s3 at a1 a2 a3 hM3
    have hagc : ∀ r, r < regs → r ≠ agB + c := fun r hr => by simp only [regs] at hr; (clear * - hagB hr; omega)
    obtain ⟨g1, g2, hM4⟩ := fin s3 hM3 (by
      rw [a3 gQ (by decide) (by decide) (by decide) (by decide) (hagc _ (by decide)), q2])
    refine ⟨g1, ⟨?_, ?_, fun x hx hx2 => ?_⟩, hM4⟩
    · rw [g2 _ (by decide), a2]
    · rw [g2 _ (Ne.symm (hagc _ (by decide))), a1, q2]
    · simp only [regs] at hx
      rw [g2 x (by simp only [gQ]; (clear * - hx; omega)), a3 x (by simp only [gK]; (clear * - hx; omega)) (by simp only [gX]; (clear * - hx; omega))
        (by simp only [gCnt]; (clear * - hx; omega)) (by simp only [cTmp]; (clear * - hx; omega)) hx2, h2 x (by simp only [regs]; omega)]
  · rw [decide_eq_false hb, bW_false_eq, if_pos rfl, if_neg hb]
    have e3 : semXIR I (.blk []) s2 = s2 := by cases s2; rfl
    rw [e3]
    obtain ⟨g1, g2, hM4⟩ := fin s2 hM2 q2
    refine ⟨g1, ⟨by rw [g2 _ (by decide), c2], fun x hx => ?_⟩, hM4⟩
    simp only [regs] at hx
    rw [g2 x (by simp only [gQ]; (clear * - hx; omega)), h2 x (by simp only [regs]; omega)]

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
      rw [h (qB + 3 * l + c) (by simp only [regs]; (clear * - hqB hc hl'; omega)) (by (clear * - r2 r3 hc hl'; omega)),
        h (wB + 64 * q + (63 - l)) (by simp only [regs]; (clear * - hwB; omega)) (by (clear * - hq r1 r2 r3 hl'; omega))]
  simp only [AgreeNP]
  rw [hF 0 (by norm_num), hF 1 (by norm_num), hF 2 (by norm_num),
    h (eB + q) (by simp only [regs]; (clear * - heB; omega)) (by (clear * - hq r3; omega)),
    h (eB + st + q) (by simp only [regs]; (clear * - heB; omega)) (by (clear * - hq r3; omega)),
    h (eB + 2 * st + q) (by simp only [regs]; (clear * - heB; omega)) (by (clear * - hq r3; omega))]

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
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, gQ, gCnt, gN1] <;> (clear * - hx; omega)
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
      rw [hE _ (by simp only [gC1]; (clear * - hx; omega)) (by simp only [cTmp]; (clear * - hx; omega)), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < st → P j s' →
      P (j + 1) (decS gC1 (semXIR I (posNBody st wB qB eB agB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hlen := length_agreeNM_le s.M st wB qB eB j
    have hlenL : (L j).length ≤ j := hlen
    obtain ⟨e1, e2, e3⟩ := posNBody_sem I s' i1 (wB := wB) (qB := qB) (eB := eB) (agB := agB)
      (c := (L j).length) (by simp only [regs]; omega) hwB2 (by simp only [regs]; omega) hqB2
      (by simp only [regs]; omega) heB2 (by simp only [regs]; omega) hag2 (by (clear * - hags z0 h0 i2; omega)) hj hlen i3 i4
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
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hagB; omega))]
        rw [hlen1] at ht
        by_cases htc : t = (L j).length
        · subst htc
          rw [g2, List.getD_append_right _ _ _ _ (by simp [hL])]
          simp [hL]
        · rw [g3 _ (by simp only [regs]; (clear * - hagB; omega)) (by (clear * - hlen1 htc; omega)), i5 t (by (clear * - hlen1 ht htc; omega)),
            List.getD_append _ _ _ _ (by simp only [hL] at *; (clear * - hlen1 ht htc; omega))]
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hx; omega)), g3 x hx (by (clear * - hj hlenL hlen1 hx2; omega)), i6 x hx hx2]
    · rw [if_neg (fun h => hb (hA.1 h))] at e2
      obtain ⟨g1, g2⟩ := e2
      rw [if_neg hb, List.append_nil]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hagB; omega)), g2 _ (by simp only [regs]; (clear * - hagB; omega)), i5 t ht]
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hx; omega)), g2 x hx, i6 x hx hx2]
  have := loopK_run I (posNBody st wB qB eB agB) P s0 hM0 (c := gC1) (n := gN1) (K := st)
    (by decide) (by decide) (by decide) n0 (by (clear * - hwB hwB2; omega)) h0 hstep
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
        rw [rowW, hW q hq (63 - l) (by have := mem_range.1 hl; (clear * - this; omega))]
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
end
-- ===== end of `LvmMPXAgree` =====

-- ===== merged from `LvmMPXAgree1` (GOLF module merge: `LvmMPXAgree1.lean` is now a stub importing `LvmMPXDec1Sem`) =====
section
-- New for lvm2 roll 11 (M′, R11-X): the level-≥1 agreement scan's semantics at `st` positions. Adapted from
-- `LvmXDec1Agree.lean` (`fold1IR_sem`, `test1IR_sem`, `Agree1P`, `agree1M`, `Reads1Out`, `pos1Body_sem`,
-- `agree1M_succ`, `length_agree1M_le`, `agree1P_congr`, `agree1IR_sem`, `agree1P_iff`, `agree1M_eq_agree1L`): the
-- `2^12` positions (and coordinate stride) become `st`; `lane1Body_sem`, `acc1_sem`, `appendIR_sem` are reused.

/-!
# The level-≥1 agreement scan at `st` positions

* `fold1IR_semN`, `test1NIR_sem`, `pos1NBody_sem`, **`agree1NIR_sem`** (16 `E` lanes, the word at `wB + 48 q + t`);
* **`agree1NM_eq_agree1G`**: at `st = 2^nL` the machine's list is `LvmMPDec.agree1G nL kL`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

theorem lo_test1NIR (st eB : ℕ) : LoK (test1NIR st eB) := by
  simp +decide [test1NIR, LoK, Prim.dst, gK, gX, gE, gZ, gZ2, h1A, regs]

/-- **The fold at the position `q`** (`gQ = q`): the accumulator holds `fold1PM … 16`; the heap
and the registers outside the fold's are kept. -/
theorem fold1IR_semN (I : Array Word) (s : St) (hM : Inv s.M) {wB qB q : ℕ} (hwB : regs ≤ wB)
    {st : ℕ} (hq : q < st) (hwB2 : wB + 48 * st < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 48 < 2 ^ 64)
    (hQ : rd s.M gQ = toWord q) :
    rdE (semXIR I (fold1IR wB qB) s).M h1A = fold1PM s.M wB qB q 16 ∧
    (∀ r, Keep1F r → rd (semXIR I (fold1IR wB qB) s).M r = rd s.M r) ∧
    Inv (semXIR I (fold1IR wB qB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB
  have w0 : WF (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
      .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
      .const gN2 16]) := by
    simp +decide [WF, Prim.dst, h1A, gK, gPw, gPe, gN2]
  have hM0 := inv_sem I w0 hM
  rw [fold1IR, semXIR_seq]
  have r0 : rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M gPw = toWord (wB + 48 * q + 3 * 0) ∧
      rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M gPe = toWord (qB + 3 * 0) ∧
      rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M gN2 = toWord 16 ∧
      rdE (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M h1A = 0 := by
    rw [sem_blk']
    simp only [rdE, rdK, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, h1A, gK, gPw, gPe, gN2]; omega))
      only [rd_set_self, rd_set_ne]
    · rw [hQ, show (48 : Word) = toWord 48 from rfl, mul_toWord, add_toWord]
      congr 1; ring
    · rfl
    · rfl
    · rw [eqt_wK_zero, mkE_zero]
  have k0 : ∀ r, Keep1F r → rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0,
      .const (h1A + 2) 0, .const gK 48, .op .mul gPw gQ gK, .const gK (toWord wB),
      .op .add gPw gPw gK, .const gPe (toWord qB), .const gN2 16]) s).M r = rd s.M r :=
    fun r hr => by
    simp only [Keep1F, gPe, gPw, gK, gC2, gN2, cTmp] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, h1A, gPe, gPw, gK, gN2] <;> (clear * - hr; omega)
  generalize semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
    .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
    .const gN2 16]) s = s0 at hM0 r0 k0
  obtain ⟨p0, e0, n0, a0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧
    rd s'.M gPw = toWord (wB + 48 * q + 3 * j) ∧ rd s'.M gPe = toWord (qB + 3 * j) ∧
    rdE s'.M h1A = fold1PM s.M wB qB q j ∧ (∀ r, Keep1F r → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ gC2 → i ≠ cTmp → rd (entryK gC2 gN2 (toWord 16) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC2 gN2 (toWord 16) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), ?_, ?_, ?_, fun r hr => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), p0]
    · rw [hE _ (by decide) (by decide), e0]
    · rw [eqt_rdE_eq (hE _ (by decide) (by decide)) (hE _ (by decide) (by decide))
        (hE _ (by decide) (by decide)), a0, fold1PM, Finset.sum_range_zero]
    · rw [hE _ hr.2.2.2.2.1 hr.2.2.2.2.2.2, k0 r hr]
  have hstep : ∀ j s', j < 16 → P j s' → P (j + 1) (decS gC2 (semXIR I lane1Body s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    have hK : ∀ x, regs ≤ x → rdE s'.M x = rdE s.M x := fun x hx => eqt_rdE_eq
      (i5 x (keep1F_of_regs hx)) (i5 _ (keep1F_of_regs (by (clear * - hx; omega))))
      (i5 _ (keep1F_of_regs (by (clear * - hx; omega))))
    obtain ⟨l1, l2, l3, l4, hM'⟩ := lane1Body_sem I s' i1 (pw := wB + 48 * q + 3 * j)
      (pe := qB + 3 * j) (by simp only [regs]; (clear * - hwB hq hwB2 hj; omega)) (by (clear * - hq hwB2 hj; omega)) (by simp only [regs]; (clear * - hqB hqB2 hj; omega))
      (by (clear * - hqB hqB2 hj; omega)) i2 i3
    have hd : ∀ x, x ≠ gC2 → rd (decS gC2 (semXIR I lane1Body s')).M x =
        rd (semXIR I lane1Body s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS hM' (by decide), ?_, ?_, ?_, fun r hr => ?_⟩
    · rw [hd _ (by decide), l2, show wB + 48 * q + 3 * j + 3 = wB + 48 * q + 3 * (j + 1) by ring]
    · rw [hd _ (by decide), l3, show qB + 3 * j + 3 = qB + 3 * (j + 1) by ring]
    · rw [eqt_rdE_decS _ (.inr (by decide)), l1, i4, fold1PM, fold1PM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; (clear * - hqB hqB2 hj; omega)), hK _ (by simp only [regs]; (clear * - hwB hq hwB2 hj; omega))]
    · have hr' := hr
      obtain ⟨r0, r1, r2, -, r4, -, -⟩ := hr'
      rw [hd _ r4, l4 r r0 r1 r2, i5 r hr]
  have hfin := loopK_run I lane1Body P s0 hM0 (c := gC2) (n := gN2) (K := 16) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, hfin.2.2.2.2, hfin.1⟩

/-! ## The comparison -/

-- adapted from LvmXAgree.lean (`lo_testIR`, `testIR_sem`)
/-- **The comparison**: `gZ` is `1` iff the accumulator's three words equal the three words of
`Enc₁(f₂)[q]`'s coordinates (`eB + c·2^12 + q`); only `gK, gX, gE, gZ, gZ2` change. -/
theorem test1NIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {st eB q : ℕ} (heB : regs ≤ eB)
    (hq : q < st) (hst : st < 2 ^ 64) (heB2 : eB + 3 * st < 2 ^ 64) (hQ : rd s.M gQ = toWord q) :
    rd (semXIR I (test1NIR st eB) s).M gZ =
      bW (decide (rd s.M (eB + q) = rd s.M h1A) &&
        decide (rd s.M (eB + st + q) = rd s.M (h1A + 1)) &&
        decide (rd s.M (eB + 2 * st + q) = rd s.M (h1A + 2))) ∧
    (∀ r, r ≠ gK → r ≠ gX → r ≠ gE → r ≠ gZ → r ≠ gZ2 →
      rd (semXIR I (test1NIR st eB) s).M r = rd s.M r) ∧
    Inv (semXIR I (test1NIR st eB) s).M := by
  have hs := hM.1
  simp only [regs] at hs heB
  have hw : WF (test1NIR st eB) := by simp +decide [test1NIR, WF, Prim.dst, gK, gX, gE, gZ, gZ2]
  refine ⟨?_, fun r r1 r2 r3 r4 r5 => ?_, inv_sem I hw hM⟩
  · simp only [test1NIR, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide |
      (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, h1A]; omega)) only [rd_set_self, rd_set_ne]
    rw [hQ, add_toWord, toNat_toWord (by (clear * - hq heB2; omega)), add_toWord, toNat_toWord (by (clear * - hq heB2; omega)), add_toWord,
      toNat_toWord (by (clear * - hq heB2; omega))]
    simp (disch := first | decide |
      (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, h1A]; omega)) only [rd_set_ne]
    rw [eq_bW, eq_bW, eq_bW, bW_and, bW_and]
    congr 3 <;> ring_nf
  · by_cases hr : r < regs
    · refine frame I (test1NIR st eB) s hw hM r hr ?_
      simp only [test1NIR, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left]
      (clear * - r1 r2 r3 r4 r5; omega)
    · exact hframeK I (test1NIR st eB) s (lo_test1NIR st eB) r (by (clear * - hr; omega))

/-! ## One position and the scan -/

/-- The fold and `Enc(f)`'s coordinates agree at `q` (stride `st`). -/
abbrev Agree1NP (M : Mem) (st wB qB eB q : ℕ) : Prop :=
  mkE (rdK M (eB + q)) (rdK M (eB + st + q)) (rdK M (eB + 2 * st + q)) =
    fold1PM M wB qB q 16

/-- **The machine's level-≥1 agreement list** below `n` (stride `st`). -/
def agree1NM (M : Mem) (st wB qB eB n : ℕ) : List ℕ :=
  (List.range n).filter fun q => decide (Agree1NP M st wB qB eB q)

/-- The cells the test reads, outside the list's region. -/
def Reads1NOut (st wB qB eB agB : ℕ) : Prop :=
  (agB + st ≤ wB ∨ wB + 48 * st ≤ agB) ∧ (agB + st ≤ qB ∨ qB + 48 ≤ agB) ∧
    (agB + st ≤ eB ∨ eB + 3 * st ≤ agB)

/-- **One position**: `q` is listed at `agB + c` iff the fold agrees with `Enc₁(f₂)` at `q`;
`gQ := q + 1`; the heap outside the listed cell is kept. -/
theorem pos1NBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {st wB qB eB agB q c : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * st < 2 ^ 64) (hqB : regs ≤ qB)
    (hqB2 : qB + 48 < 2 ^ 64) (heB : regs ≤ eB) (heB2 : eB + 3 * st < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + st < 2 ^ 64) (hags : agB + st ≤ s.M.size)
    (hq : q < st) (hcq : c ≤ q) (hQ : rd s.M gQ = toWord q) (hC : rd s.M gCnt = toWord c) :
    rd (semXIR I (pos1NBody st wB qB eB agB) s).M gQ = toWord (q + 1) ∧
    (if Agree1NP s.M st wB qB eB q then
      rd (semXIR I (pos1NBody st wB qB eB agB) s).M gCnt = toWord (c + 1) ∧
        rd (semXIR I (pos1NBody st wB qB eB agB) s).M (agB + c) = toWord q ∧
        ∀ x, regs ≤ x → x ≠ agB + c → rd (semXIR I (pos1NBody st wB qB eB agB) s).M x = rd s.M x
    else
      rd (semXIR I (pos1NBody st wB qB eB agB) s).M gCnt = toWord c ∧
        ∀ x, regs ≤ x → rd (semXIR I (pos1NBody st wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (pos1NBody st wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  rw [pos1NBody, semXIR_seq]
  obtain ⟨f1, f2, hM1⟩ := fold1IR_semN I s hM (wB := wB) (qB := qB) (by simp only [regs]; omega)
    hq hwB2 (by simp only [regs]; omega) hqB2 hQ
  have z1 := size_sem I (fold1IR wB qB) s
  generalize semXIR I (fold1IR wB qB) s = s1 at f1 f2 hM1 z1
  have q1 : rd s1.M gQ = toWord q := (f2 gQ keep1F_gQ).trans hQ
  have c1 : rd s1.M gCnt = toWord c := (f2 gCnt keep1F_gCnt).trans hC
  have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s.M x := fun x hx => f2 x (keep1F_of_regs hx)
  rw [semXIR_seq]
  obtain ⟨t1, t2, hM2⟩ := test1NIR_sem I s1 hM1 (eB := eB) (by simp only [regs]; omega) hq (by (clear * - hwB hwB2; omega)) heB2 q1
  have z2 := size_sem I (test1NIR st eB) s1
  generalize semXIR I (test1NIR st eB) s1 = s2 at t1 t2 hM2 z2
  -- the flag is the test
  have e : ∀ a b, regs ≤ a → (rd s1.M a = rd s1.M b ↔ rdK s.M a = rdK s1.M b) := fun a b ha => by
    rw [rdK, rdK, wK_inj, h1 a ha]
  have hiff : Agree1NP s.M st wB qB eB q ↔ (rd s1.M (eB + q) = rd s1.M h1A ∧
      rd s1.M (eB + st + q) = rd s1.M (h1A + 1) ∧
      rd s1.M (eB + 2 * st + q) = rd s1.M (h1A + 2)) := by
    simp only [Agree1NP]
    rw [← f1, rdE, mkE_eq_iff, e _ _ (by simp only [regs]; (clear * - heB; omega)),
      e _ _ (by simp only [regs]; (clear * - heB hq hcq; omega)), e _ _ (by simp only [regs]; (clear * - heB hq hcq; omega))]
  have hZ : rd s2.M gZ = bW (decide (Agree1NP s.M st wB qB eB q)) := by
    rw [t1]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    exact hiff.symm
  have q2 : rd s2.M gQ = toWord q := (t2 gQ (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans q1
  have c2 : rd s2.M gCnt = toWord c := (t2 gCnt (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans c1
  have h2 : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    rw [t2 x (by simp only [gK]; (clear * - hx; omega)) (by simp only [gX]; (clear * - hx; omega)) (by simp only [gE]; (clear * - hx; omega))
      (by simp only [gZ]; (clear * - hx; omega)) (by simp only [gZ2]; (clear * - hx; omega)), h1 x (by simp only [regs]; omega)]
  -- `q += 1`
  have fin : ∀ s3 : St, Inv s3.M → rd s3.M gQ = toWord q →
      rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M gQ = toWord (q + 1) ∧
      (∀ x, x ≠ gQ → rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M x = rd s3.M x) ∧
      Inv (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M := fun s3 h3 hq3 => by
    have := h3.1; simp only [regs] at this
    refine ⟨?_, fun x hx => rd_blk_of_not_dst I _ s3 (by simp [Prim.dst]; exact Ne.symm hx),
      inv_sem I (P := .blk [.op .add gQ gQ cOne]) (by simp +decide [WF]) h3⟩
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [gQ]; (clear * - this; omega)), hq3, show rd s3.M cOne = 1 from h3.2 0 (by decide),
      add_one_toWord]
  rw [semXIR_seq, semXIR_ite, hZ]
  by_cases hb : Agree1NP s.M st wB qB eB q
  · rw [decide_eq_true hb, if_neg bW_true_ne, if_pos hb]
    obtain ⟨a1, a2, a3, hM3⟩ := appendIR_sem I s2 hM2 (agB := agB) (c := c)
      (by simp only [regs]; omega) (by (clear * - hag2 hq hcq; omega)) (by (clear * - hags hq hcq z1 z2; omega)) (by (clear * - heB heB2 hq hcq; omega)) c2
    generalize semXIR I (appendIR agB) s2 = s3 at a1 a2 a3 hM3
    have hagc : ∀ r, r < regs → r ≠ agB + c := fun r hr => by simp only [regs] at hr; (clear * - hagB hr; omega)
    obtain ⟨g1, g2, hM4⟩ := fin s3 hM3 (by
      rw [a3 gQ (by decide) (by decide) (by decide) (by decide) (hagc _ (by decide)), q2])
    refine ⟨g1, ⟨?_, ?_, fun x hx hx2 => ?_⟩, hM4⟩
    · rw [g2 _ (by decide), a2]
    · rw [g2 _ (Ne.symm (hagc _ (by decide))), a1, q2]
    · simp only [regs] at hx
      rw [g2 x (by simp only [gQ]; (clear * - hx; omega)), a3 x (by simp only [gK]; (clear * - hx; omega))
        (by simp only [gX]; (clear * - hx; omega)) (by simp only [gCnt]; (clear * - hx; omega)) (by simp only [cTmp]; (clear * - hx; omega)) hx2,
        h2 x (by simp only [regs]; omega)]
  · rw [decide_eq_false hb, bW_false_eq, if_pos rfl, if_neg hb]
    have e3 : semXIR I (.blk []) s2 = s2 := by cases s2; rfl
    rw [e3]
    obtain ⟨g1, g2, hM4⟩ := fin s2 hM2 q2
    refine ⟨g1, ⟨by rw [g2 _ (by decide), c2], fun x hx => ?_⟩, hM4⟩
    simp only [regs] at hx
    rw [g2 x (by simp only [gQ]; (clear * - hx; omega)), h2 x (by simp only [regs]; omega)]

-- adapted from LvmXAgree.lean (`agreeM_succ`, `length_agreeM_le`, `agreeP_congr`)
theorem agree1NM_succ (M : Mem) (st wB qB eB n : ℕ) : agree1NM M st wB qB eB (n + 1) =
    agree1NM M st wB qB eB n ++ if Agree1NP M st wB qB eB n then [n] else [] := by
  rw [agree1NM, agree1NM, List.range_succ, List.filter_append]
  congr 1
  by_cases h : Agree1NP M st wB qB eB n
  · rw [if_pos h]; simp only [List.filter_cons, List.filter_nil, decide_eq_true h, ite_true]
  · rw [if_neg h]; simp only [List.filter_cons, List.filter_nil, decide_eq_false h]; rfl

theorem length_agree1NM_le (M : Mem) (st wB qB eB n : ℕ) : (agree1NM M st wB qB eB n).length ≤ n :=
  (List.length_filter_le _ _).trans (by simp)

theorem agree1NP_congr {M M' : Mem} {st wB qB eB agB q : ℕ} (hq : q < st) (hwB : regs ≤ wB)
    (hqB : regs ≤ qB) (heB : regs ≤ eB) (hR : Reads1NOut st wB qB eB agB)
    (h : ∀ x, regs ≤ x → (x < agB ∨ agB + st ≤ x) → rd M' x = rd M x) :
    Agree1NP M' st wB qB eB q ↔ Agree1NP M st wB qB eB q := by
  obtain ⟨r1, r2, r3⟩ := hR
  simp only [regs] at hwB hqB heB
  have hF : fold1PM M' wB qB q 16 = fold1PM M wB qB q 16 :=
    Finset.sum_congr rfl fun u hu => by
      have hu' := mem_range.1 hu
      have hq' : q + 1 ≤ st := hq
      have hq48 : 48 * q + 48 ≤ 48 * st := by (clear * - hq; omega)
      rw [eqt_rdE_eq (h (qB + 3 * u) (by simp only [regs]; (clear * - hqB hu'; omega)) (by (clear * - r2 r3 hu'; omega)))
          (h (qB + 3 * u + 1) (by simp only [regs]; (clear * - hqB hu'; omega)) (by (clear * - r2 r3 hu'; omega)))
          (h (qB + 3 * u + 2) (by simp only [regs]; (clear * - hqB hu'; omega)) (by (clear * - r2 r3 hu'; omega))),
        eqt_rdE_eq (h (wB + 48 * q + 3 * u) (by simp only [regs]; (clear * - hwB hu'; omega)) (by (clear * - hq r1 r2 r3 hu'; omega)))
          (h (wB + 48 * q + 3 * u + 1) (by simp only [regs]; (clear * - hwB hu'; omega)) (by (clear * - hq r1 r2 r3 hu'; omega)))
          (h (wB + 48 * q + 3 * u + 2) (by simp only [regs]; (clear * - hwB hu'; omega)) (by (clear * - hq r1 r2 r3 hu'; omega)))]
  simp only [Agree1NP, hF, rdK]
  rw [h (eB + q) (by simp only [regs]; (clear * - heB; omega)) (by (clear * - hq r3; omega)),
    h (eB + st + q) (by simp only [regs]; (clear * - heB; omega)) (by (clear * - hq r3; omega)),
    h (eB + 2 * st + q) (by simp only [regs]; (clear * - heB; omega)) (by (clear * - hq r3; omega))]

/-! ## Semantics -/

-- adapted from LvmXAgree.lean (`agreeIR_sem`)
/-- **The level-1 agreement scan**: the count is `|agree1NM|` and `agB + t` holds the `t`-th
agreeing position (`agree1NM s.M st wB qB eB (2^12)`, increasing); the heap outside
`[agB, agB + 2^12)` is kept. -/
theorem agree1NIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {st wB qB eB agB : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * st < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 48 < 2 ^ 64)
    (heB : regs ≤ eB) (heB2 : eB + 3 * st < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + st < 2 ^ 64) (hags : agB + st ≤ s.M.size)
    (hR : Reads1NOut st wB qB eB agB) :
    rd (semXIR I (agree1NIR st wB qB eB agB) s).M gCnt =
      toWord (agree1NM s.M st wB qB eB (st)).length ∧
    (∀ t < (agree1NM s.M st wB qB eB (st)).length,
      rd (semXIR I (agree1NIR st wB qB eB agB) s).M (agB + t) =
        toWord ((agree1NM s.M st wB qB eB (st)).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + st ≤ x) →
      rd (semXIR I (agree1NIR st wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (agree1NIR st wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  have w0 : WF (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) := by
    simp +decide [WF, Prim.dst, gQ, gCnt, gN1]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s
  have r0 : rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s).M
        gQ = toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s).M gCnt =
        toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s).M gN1 =
        toWord (st) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, gQ, gCnt, gN1]; omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const gQ 0, .const gCnt 0,
      .const gN1 (toWord (st))]) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, gQ, gCnt, gN1] <;> (clear * - hx; omega)
  rw [agree1NIR, semXIR_seq]
  generalize semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (st))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨q0, c0, n0⟩ := r0
  set L := fun j => agree1NM s.M st wB qB eB j with hL
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M gQ = toWord j ∧ rd s'.M gCnt = toWord (L j).length ∧
    (∀ t < (L j).length, rd s'.M (agB + t) = toWord ((L j).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + st ≤ x) → rd s'.M x = rd s.M x)
  have hE : ∀ i, i ≠ gC1 → i ≠ cTmp →
      rd (entryK gC1 gN1 (toWord (st)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC1 gN1 (toWord (st)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun t ht => absurd ht (by simp [hL, agree1NM]), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), q0]
    · rw [hE _ (by decide) (by decide), c0]; simp [hL, agree1NM]
    · simp only [regs] at hx
      rw [hE _ (by simp only [gC1]; (clear * - hx; omega)) (by simp only [cTmp]; (clear * - hx; omega)),
        k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < st → P j s' →
      P (j + 1) (decS gC1 (semXIR I (pos1NBody st wB qB eB agB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hlen := length_agree1NM_le s.M st wB qB eB j
    have hlenL : (L j).length ≤ j := hlen
    obtain ⟨e1, e2, e3⟩ := pos1NBody_sem I s' i1 (wB := wB) (qB := qB) (eB := eB) (agB := agB)
      (c := (L j).length) (by simp only [regs]; omega) hwB2 (by simp only [regs]; omega) hqB2
      (by simp only [regs]; omega) heB2 (by simp only [regs]; omega) hag2 (by (clear * - hags z0 h0 i2; omega)) hj hlen i3 i4
    have hd : ∀ x, x ≠ gC1 → rd (decS gC1 (semXIR I (pos1NBody st wB qB eB agB) s')).M x =
        rd (semXIR I (pos1NBody st wB qB eB agB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hM' := inv_decS e3 (show 4 ≤ gC1 by decide)
    have hz' : (decS gC1 (semXIR I (pos1NBody st wB qB eB agB) s')).M.size = s.M.size := by
      rw [size_decS, size_sem, i2]
    have hA : Agree1NP s'.M st wB qB eB j ↔ Agree1NP s.M st wB qB eB j :=
      agree1NP_congr hj (by simp only [regs]; omega) (by simp only [regs]; omega)
        (by simp only [regs]; omega) hR i6
    dsimp only [P]
    rw [hL]
    dsimp only
    rw [agree1NM_succ]
    by_cases hb : Agree1NP s.M st wB qB eB j
    · rw [if_pos (hA.2 hb)] at e2
      obtain ⟨g1, g2, g3⟩ := e2
      rw [if_pos hb]
      have hlen1 : (agree1NM s.M st wB qB eB j ++ [j]).length = (L j).length + 1 := by
        rw [List.length_append, List.length_singleton]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1, hlen1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hagB; omega))]
        rw [hlen1] at ht
        by_cases htc : t = (L j).length
        · subst htc
          rw [g2, List.getD_append_right _ _ _ _ (by simp [hL])]
          simp [hL]
        · rw [g3 _ (by simp only [regs]; (clear * - hagB; omega)) (by (clear * - hlen1 htc; omega)), i5 t (by (clear * - hlen1 ht htc; omega)),
            List.getD_append _ _ _ _ (by simp only [hL] at *; (clear * - hlen1 ht htc; omega))]
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hx; omega)), g3 x hx (by (clear * - hj hlenL hlen1 hx2; omega)), i6 x hx hx2]
    · rw [if_neg (fun h => hb (hA.1 h))] at e2
      obtain ⟨g1, g2⟩ := e2
      rw [if_neg hb, List.append_nil]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hagB; omega)), g2 _ (by simp only [regs]; (clear * - hagB; omega)),
          i5 t ht]
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hx; omega)), g2 x hx, i6 x hx hx2]
  have := loopK_run I (pos1NBody st wB qB eB agB) P s0 hM0 (c := gC1) (n := gN1) (K := st)
    (by decide) (by decide) (by decide) n0 (by (clear * - hwB hwB2; omega)) h0 hstep
  exact ⟨this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2, this.1⟩


/-- The test at one position is the generic decoder's. -/
theorem agree1NP_iff {M : Mem} {st kL wB qB eB q : ℕ} (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hq : q < st)
    (hW : ∀ q < st, ∀ t < 48, rdK M (wB + 48 * q + t) = wd q t)
    (hQ : ∀ u < 16, rdE M (qB + 3 * u) = eqA1 α u)
    (hE : ∀ q < st, encG kL f q =
      mkE (rdK M (eB + q)) (rdK M (eB + st + q)) (rdK M (eB + 2 * st + q))) :
    Agree1NP M st wB qB eB q ↔ fold1At α wd q = encG kL f q := by
  have hF : fold1At α wd q = fold1PM M wB qB q 16 := by
    rw [fold1At, fold1PM]
    refine sum_congr rfl fun u hu => ?_
    have hu' := mem_range.1 hu
    rw [hQ u hu', row1, rdE, ← hW q hq (3 * u) (by (clear * - hu'; omega)), ← hW q hq (3 * u + 1) (by (clear * - hu'; omega)),
      ← hW q hq (3 * u + 2) (by (clear * - hu'; omega))]
    rfl
  simp only [Agree1NP]
  rw [← hF, ← hE q hq]
  exact eq_comm

/-- **The machine's level-≥1 list is the generic decoder's** (`agree1M_eq_agree1L` at `2^nL` positions). -/
theorem agree1NM_eq_agree1G {M : Mem} {nL kL wB qB eB : ℕ} (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ nL, ∀ t < 48, rdK M (wB + 48 * q + t) = wd q t)
    (hQ : ∀ u < 16, rdE M (qB + 3 * u) = eqA1 α u)
    (hE : ∀ q < 2 ^ nL, encG kL f q =
      mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ nL + q)) (rdK M (eB + 2 * 2 ^ nL + q))) :
    agree1NM M (2 ^ nL) wB qB eB (2 ^ nL) = agree1G nL kL wd α f := by
  unfold agree1NM agree1G
  refine List.filter_congr fun q hq => ?_
  exact decide_eq_decide.2 (agree1NP_iff wd α f (List.mem_range.1 hq) hW hQ hE)

end Lvm.X
end
-- ===== end of `LvmMPXAgree1` =====

-- ===== merged from `LvmMPXNtt5` (GOLF module merge: `LvmMPXNtt5.lean` is now a stub importing `LvmMPXDec1Sem`) =====
section
-- New for lvm2 roll 11 (M′, R11-X): the NTT programs composed with the basis table, at any dimension `N`.
-- Adapted from `LvmXNtt5.lean` (`wtabIR_nw`, `wtab_bflyIR_coeffs`, `wtab_fwdIR_enc`) at `N` for `15`.

/-!
# The NTT programs at dimension `N` composed with the basis table

* `wtabNIR_nw`: the table program does not touch the row pointer `rA0` or the forward NTT's registers.
* **`wtab_bflyNIR_coeffs`**, **`wtab_fwdNIR_enc`**: `wtabNIR N tb` then `bflyNIR N ℓ tb` (resp. `fwdNIR N ℓ tb`)
  from any state with the row pointer set; the table hypothesis is discharged by `wtabNIR_sem`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

variable {N : ℕ}

/-- The table program writes neither the row pointer nor the forward NTT's registers. -/
theorem wtabNIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rKf ∨ r = rTbf) (N tb : ℕ) :
    ¬ Writes (wtabNIR N tb) r := by
  have hr12 : 12 ≤ r ∧ r ≠ fH ∧ r ≠ fN ∧ r ≠ fAl := by
    rcases hr with rfl | rfl | rfl <;> decide
  have n1 : ¬ Writes (mulK fH fU fW) r := (mulK_writes_iff (by have := hr12.1; omega) hr12.2.1).1
  have n2 : ¬ Writes (mulK fN fH fAl) r :=
    (mulK_writes_iff (by have := hr12.1; omega) hr12.2.2.1).1
  have n3 : ¬ Writes (invK fAl fH) r := (invK_writes_iff hr12.1 hr12.2.2.2).1
  simp only [wtabNIR, row0NIR, row0Body, rowNIR, rowNBody, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, n1, n2, n3]
  rcases hr with rfl | rfl | rfl <;>
  simp [rA0, rKf, rTbf, rTr, uI, rTa, rN2, rC2, fG, rLv, rN3, rC3, uT1, fU, fW, rAH, cTmp]

/-- **The table, then the inverse NTT**: the row ends holding the novel-basis coefficients of its values. -/
theorem wtab_bflyNIR_coeffs (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) (hN1 : 1 ≤ N)
    {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ N) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64) (hsz : A + 2 ^ ℓ ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64) (hszt : tb + N * N ≤ s.M.size)
    (hdisj : tb + N * N ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    ∀ i < 2 ^ ℓ, rdK (semXIR I (.seq (wtabNIR N tb) (bflyNIR N ℓ tb)) s).M (A + i) =
      coeffsAt ptK N ℓ 0 Y i := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabNIR_sem I s hM hN hN1 htb htb2 hszt
  rw [semXIR_seq]
  refine bflyNIR_coeffs I _ t3 hN hℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 ?_
  · rw [frame I _ s (wf_wtabNIR N tb) hM _ (by decide) (wtabNIR_nw (.inl rfl) N tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

/-- **The table, then the forward NTT**: on a zero-padded message the row ends holding `Enc`. -/
theorem wtab_fwdNIR_enc (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) (hN1 : 1 ≤ N)
    {A tb ℓ m : ℕ}
    (hℓ : ℓ ≤ N) (hmℓ : m ≤ ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64)
    (hszt : tb + N * N ≤ s.M.size) (hdisj : tb + N * N ≤ A ∨ A + 2 ^ ℓ ≤ tb)
    (hA0 : rd s.M rA0 = toWord A) (c : Fin (2 ^ m) → BF64)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = if h : i < 2 ^ m then c ⟨i, h⟩ else 0) :
    ∀ j < 2 ^ ℓ, rdK (semXIR I (.seq (wtabNIR N tb) (fwdNIR N ℓ tb)) s).M (A + j) = encN ptK c j := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabNIR_sem I s hM hN hN1 htb htb2 hszt
  rw [semXIR_seq]
  refine fwdNIR_enc I _ t3 hN hℓ hmℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 c ?_
  · rw [frame I _ s (wf_wtabNIR N tb) hM _ (by decide) (wtabNIR_nw (.inl rfl) N tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

end Lvm.X
end
-- ===== end of `LvmMPXNtt5` =====

-- ===== merged from `LvmMPXDecSem` (GOLF module merge: `LvmMPXDecSem.lean` is now a stub importing `LvmMPXDec1Sem`) =====
section
-- New for lvm2 roll 11 (M′, R11-X): the semantics of the decoders' shape-generic phases. Adapted from
-- `LvmXDec1IR.lean` (`ok1IR_sem`, `bfly1All_sem`, `tr1Row_sem`, `tr1IR_sem`) and `LvmXDecIR2.lean` (`TabOk`,
-- `tabOk_congr`): the flag at `2^kL`, the inverse NTTs of `R` rows of `2^kL` at table dimension `N`, the
-- transpose of `48 × 2^kL`; `tr1Body_sem`, `tr1Loop_sem` are reused.

/-!
# The generic phases' semantics

* `TabOkN N M tb`: the basis table of dimension `N` at `tb` (`wtabNIR_sem`'s output).
* `okMIR_sem`: the flag `[2^kL ≤ cnt]`.
* **`bflyAllM_sem`**: `R` rows of `2^kL` at `ob` become their novel-basis coefficients (`coeffsAt ptK N kL 0`).
* **`tr1MIR_sem`**: the transpose `M[oB + 48 v + t] = M[ob + 2^kL t + v]`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

/-- The transpose's address bound. -/
theorem trB {k v i : ℕ} (hv : v < k) (hi : i < 48) : v + k * i < 48 * k := by
  have h := Nat.mul_le_mul_left k (show i + 1 ≤ 48 by (clear * - hi; omega))
  rw [Nat.mul_succ, Nat.mul_comm k 48] at h; (clear * - hv h; omega)

/-- The table hypothesis of the NTTs at dimension `N`. -/
def TabOkN (N : ℕ) (M : Mem) (tb : ℕ) : Prop :=
  ∀ v < N, ∀ i < N, rdK M (tb + N * v + i) = (wRow ptK N v).getD i 0

theorem tabOkN_congr {N : ℕ} {M M' : Mem} {tb : ℕ} (h : TabOkN N M tb)
    (hf : ∀ x, tb ≤ x → x < tb + N * N → rd M' x = rd M x) : TabOkN N M' tb := fun v hv i hi => by
  have : N * v + i < N * N := by
    have := Nat.mul_le_mul_left N (show v + 1 ≤ N by (clear * - hv; omega)); rw [Nat.mul_succ] at this; (clear * - hi this; omega)
  simp only [rdK]; rw [hf _ (by (clear * -; omega)) (by (clear * - this; omega))]; exact h v hv i hi

/-- **The flag**: `rOk` and `ok1B`'s cell `= [2^9 ≤ cnt]`. -/
theorem okMIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL ok n : ℕ} (hk : kL < 64) (hdB : regs ≤ ok)
    (hdB2 : ok < 2 ^ 64) (hdBs : ok < s.M.size) (hn : n < 2 ^ 64)
    (hC : rd s.M gCnt = toWord n) :
    rd (semXIR I (okMIR kL ok) s).M rOk = bW (decide (2 ^ kL ≤ n)) ∧
    rd (semXIR I (okMIR kL ok) s).M (ok) = bW (decide (2 ^ kL ≤ n)) ∧
    (∀ x, regs ≤ x → x ≠ ok → rd (semXIR I (okMIR kL ok) s).M x = rd s.M x) ∧
    Inv (semXIR I (okMIR kL ok) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdB
  rw [okMIR, semXIR_seq]
  set ps : List Prim := [.const zK (toWord (2 ^ kL)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (ok))] with hps
  have hM1 := inv_sem I (P := .blk ps) (by simp +decide [hps, WF, Prim.dst, zK, rOk]) hM
  have v1 : rd (semXIR I (.blk ps) s).M rOk = bW (decide (2 ^ kL ≤ n)) ∧
      rd (semXIR I (.blk ps) s).M zK = toWord (ok) := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zK, rOk]; omega)) only [rd_set_self, rd_set_ne]
    rw [hC, ltW_toWord hn (pow_lt64 hk), show rd s.M cOne = 1 from hM.2 0 (by decide), eval_xor,
      bW_xor_one]
    congr 1
    rw [← decide_not]
    simp only [Nat.not_lt]
  have k1 : ∀ x, regs ≤ x → rd (semXIR I (.blk ps) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, zK, rOk] <;> (clear * - hx; omega)
  have z1 := size_sem I (.blk ps) s
  generalize semXIR I (.blk ps) s = s1 at hM1 v1 k1 z1
  obtain ⟨st1, st2, hM2⟩ := store_sem I s1 hM1 (p := zK) (v := rOk) (x := ok) (by decide)
    (by decide) v1.2 (by simp only [regs, ok1B]; omega) hdB2 (by (clear * - hdBs z1; omega))
  refine ⟨?_, by rw [st1, v1.1], fun x hx hx2 => by
    rw [st2 x hx2 (by simp only [regs, cTmp] at *; (clear * - hx; omega)), k1 x hx], hM2⟩
  rw [st2 _ (by simp only [rOk, ok1B]; (clear * - hdB hdB2; omega)) (by decide), v1.1]


/-- **One transposed row** `v < 2^9`: `oB + 48 v + t := ob + v + 2^9 t` (`t < 48`), `yL := v + 1`. -/
theorem tr1RowM_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL ob oB v : ℕ} (hk : kL < 64) (hv : v < 2 ^ kL)
    (hob : regs ≤ ob) (hob2 : ob + 48 * 2 ^ kL < 2 ^ 64) (hoB : regs ≤ oB)
    (hoB2 : oB + 48 * 2 ^ kL < 2 ^ 64) (hoBs : oB + 48 * 2 ^ kL ≤ s.M.size)
    (hdisj : ob + 48 * 2 ^ kL ≤ oB ∨ oB + 48 * 2 ^ kL ≤ ob) (hL : rd s.M yL = toWord v) :
    (∀ t < 48, rd (semXIR I (tr1RowM kL ob oB) s).M (oB + 48 * v + t) = rd s.M (ob + v + 2 ^ kL * t)) ∧
    rd (semXIR I (tr1RowM kL ob oB) s).M yL = toWord (v + 1) ∧
    (∀ r, regs ≤ r → (r < oB + 48 * v ∨ oB + 48 * v + 48 ≤ r) →
      rd (semXIR I (tr1RowM kL ob oB) s).M r = rd s.M r) ∧
    Inv (semXIR I (tr1RowM kL ob oB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hob hoB
  rw [tr1RowM, semXIR_seq]
  set ps : List Prim := [.const yK (toWord ob), .op .add ySr yL yK, .const yK 48, .op .mul yDs yL yK,
      .const yK (toWord oB), .op .add yDs yDs yK, .const yStr (toWord (2 ^ kL))] with hps
  have w0 : WF (.blk ps) := by simp +decide [hps, WF, Prim.dst, yK, ySr, yDs, yStr]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk ps) s
  have r0 : rd (semXIR I (.blk ps) s).M ySr = toWord (ob + v) ∧
      rd (semXIR I (.blk ps) s).M yDs = toWord (oB + 48 * v) ∧
      rd (semXIR I (.blk ps) s).M yStr = toWord (2 ^ kL) ∧ rd (semXIR I (.blk ps) s).M yL = toWord v := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yK, ySr, yDs, yStr, yL]; omega)) only [rd_set_self, rd_set_ne]
    · rw [hL, add_toWord, Nat.add_comm]
    · rw [hL, show (48 : Word) = toWord 48 from rfl, mul_toWord, add_toWord, Nat.add_comm,
        Nat.mul_comm]
    · exact hL
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk ps) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, yK, ySr, yDs, yStr] <;> (clear * - hr; omega)
  generalize semXIR I (.blk ps) s = s0 at hM0 z0 r0 k0
  obtain ⟨p1, p2, p3, p4⟩ := r0
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := tr1Loop_sem I s0 hM0 (n := 48) (src := ob + v) (str := 2 ^ kL)
    (dst := oB + 48 * v) (by norm_num) (fun i hi => by have := trB hv hi; (clear * - hob2 this; omega)) (by simp only [regs]; (clear * - hoB; omega))
    (by (clear * - hv hoB2; omega)) (by (clear * - hv hoBs z0; omega)) (fun i hi => by have := trB hv hi; (clear * - hv hdisj this; omega)) (fun i hi => by simp only [regs]; (clear * - hob; omega)) p1 p2 p3
  have z1 := size_sem I (mcpLoop 48) s0
  have l1 : rd (semXIR I (mcpLoop 48) s0).M yL = toWord v := by
    rw [frame I _ s0 (by simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yV, yN,
      yC, cTmp, regs]) hM0 yL (by decide) (by simp +decide [mcpLoop, mcpBody, Writes, Prim.dst,
        ySr, yDs, yV, yN, yC, yL, cTmp]), p4]
  generalize semXIR I (mcpLoop 48) s0 = s1 at m1 m2 hM1 z1 l1
  have b2 : ∀ r, r ≠ yL → rd (semXIR I (.blk [.op .add yL yL cOne]) s1).M r = rd s1.M r :=
    fun r hr => rd_blk_of_not_dst I _ s1 (by simp [Prim.dst]; exact Ne.symm hr)
  have hx : ∀ x, regs ≤ x → x ≠ yL := fun x hx => by simp only [regs, yL] at *; (clear * - hx; omega)
  refine ⟨fun t ht => ?_, ?_, fun r hr hr2 => ?_, inv_sem I (P := .blk [.op .add yL yL cOne])
    (by simp +decide [WF, Prim.dst, yL]) hM1⟩
  · rw [b2 _ (hx _ (by simp only [regs]; (clear * - hoB ht; omega))), m1 t ht, k0 _ (by simp only [regs]; (clear * - hob; omega))]
  · have hs1 := hM1.1
    simp only [regs] at hs1
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [yL]; (clear * - hs z0 z1; omega)), l1, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
      add_one_toWord]
  · rw [b2 _ (hx r hr), m2 r (keepC_of_regs hr) hr2, k0 r hr]

/-- **The transpose**: `M[oB + 48 v + t] = M[ob + 2^9 t + v]`; the heap outside
`[oB, oB + 48·2^9)` is kept. -/
theorem tr1MIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL ob oB : ℕ} (hk : kL < 64)
    (hob : regs ≤ ob) (hob2 : ob + 48 * 2 ^ kL < 2 ^ 64) (hoB : regs ≤ oB)
    (hoB2 : oB + 48 * 2 ^ kL < 2 ^ 64) (hoBs : oB + 48 * 2 ^ kL ≤ s.M.size)
    (hd : ob + 48 * 2 ^ kL ≤ oB ∨ oB + 48 * 2 ^ kL ≤ ob) :
    (∀ v < 2 ^ kL, ∀ t < 48, rd (semXIR I (tr1MIR kL ob oB) s).M (oB + 48 * v + t) =
      rd s.M (ob + 2 ^ kL * t + v)) ∧
    (∀ x, regs ≤ x → (x < oB ∨ oB + 48 * 2 ^ kL ≤ x) → rd (semXIR I (tr1MIR kL ob oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (tr1MIR kL ob oB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hob hoB
  rw [tr1MIR, semXIR_seq]
  have w0 : WF (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) := by
    simp +decide [WF, Prim.dst, yL, yN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s
  have r0 : rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s).M yL = toWord 0 ∧
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s).M yN2 = toWord (2 ^ kL) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yL, yN2]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r →
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [regs] at hr
      refine rd_blk_of_not_dst I _ s ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, yL, yN2] <;> (clear * - hr; omega)
  generalize semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s = s0 at hM0 z0 r0 k0
  obtain ⟨l0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M yL = toWord j ∧
    (∀ v < j, ∀ t < 48, rd s'.M (oB + 48 * v + t) = rd s.M (ob + 2 ^ kL * t + v)) ∧
    (∀ r, regs ≤ r → (r < oB ∨ oB + 48 * j ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC2 → i ≠ cTmp → rd (entryK yC2 yN2 (toWord (2 ^ kL)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC2 yN2 (toWord (2 ^ kL)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun v hv => absurd hv (by (clear * - hv; omega)), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), l0]
    · simp only [regs] at hr
      rw [hE _ (by simp only [yC2]; (clear * - hr; omega)) (by simp only [cTmp]; (clear * - hr; omega)), k0 r (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 2 ^ kL → P j s' → P (j + 1) (decS yC2 (semXIR I (tr1RowM kL ob oB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    obtain ⟨b1, b2, b3, hM'⟩ := tr1RowM_sem I s' i1 (ob := ob) (oB := oB) hk hj
      (by simp only [regs]; omega) hob2 (by simp only [regs]; omega) hoB2 (by (clear * - hoBs z0 h0 i2; omega)) hd i3
    have hd' : ∀ x, x ≠ yC2 → rd (decS yC2 (semXIR I (tr1RowM kL ob oB) s')).M x =
        rd (semXIR I (tr1RowM kL ob oB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hx : ∀ x, regs ≤ x → x ≠ yC2 := fun x hx => by simp only [regs, yC2] at *; (clear * - hx; omega)
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], by rw [hd' _ (by decide), b2],
      fun v hv t ht => ?_, fun r hr hr2 => ?_⟩
    · rw [hd' _ (hx _ (by simp only [regs]; (clear * - hoB ht; omega)))]
      by_cases hvj : v = j
      · subst hvj
        have := trB hj ht
        rw [b1 t ht, i5 _ (by simp only [regs]; (clear * - hob; omega)) (by (clear * - hd hj this; omega)), Nat.add_right_comm]
      · rw [b3 _ (by simp only [regs]; (clear * - hoB ht; omega)) (by (clear * - hv ht hvj; omega)), i4 v (by (clear * - hv hvj; omega)) t ht]
    · rw [hd' _ (hx r hr), b3 r hr (by (clear * - hob hob2 hoB hoB2 hj hr2; omega)), i5 r hr (by (clear * - hr2; omega))]
  have hfin := loopK_run I (tr1RowM kL ob oB) P s0 hM0 (c := yC2) (n := yN2) (K := 2 ^ kL) (by decide)
    (by decide) (by decide) n0 (pow_lt64 hk) h0 hstep
  exact ⟨hfin.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2 r hr (by omega), hfin.1⟩


/-- **The inverse NTT of `R` rows** of `2^kL` coefficients at `ob` (table dimension `N`). -/
theorem bflyAllM_sem (I : Array Word) (s : St) (hM : Inv s.M) {N kL R tb ob : ℕ} (hN : N ≤ 64)
    (hkN : kL ≤ N) (hR : R < 2 ^ 64) (hob : regs ≤ ob) (hob2 : ob + R * 2 ^ kL < 2 ^ 64)
    (hsz : ob + R * 2 ^ kL ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64)
    (hdisj : tb + N * N ≤ ob ∨ ob + R * 2 ^ kL ≤ tb) (hT : TabOkN N s.M tb) (Y : ℕ → ℕ → BF64)
    (hY : ∀ t < R, ∀ i < 2 ^ kL, rdK s.M (ob + t * 2 ^ kL + i) = Y t i) :
    (∀ t < R, ∀ i < 2 ^ kL, rdK (semXIR I (bflyAllM N kL R tb ob) s).M (ob + t * 2 ^ kL + i) =
      coeffsAt ptK N kL 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < ob ∨ ob + R * 2 ^ kL ≤ x) →
      rd (semXIR I (bflyAllM N kL R tb ob) s).M x = rd s.M x) ∧
    Inv (semXIR I (bflyAllM N kL R tb ob) s).M := by
  have hs := hM.1
  have hK0 : 0 < 2 ^ kL := by positivity
  simp only [regs] at hob hs htb
  rw [bflyAllM, semXIR_seq]
  have w0 : WF (.blk [.const zT 0, .const zN (toWord R)]) := by simp +decide [WF, Prim.dst, zT, zN]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const zT 0, .const zN (toWord R)]) s
  have r0 : rd (semXIR I (.blk [.const zT 0, .const zN (toWord R)]) s).M zT = toWord 0 ∧
      rd (semXIR I (.blk [.const zT 0, .const zN (toWord R)]) s).M zN = toWord R := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zT, zN]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const zT 0, .const zN (toWord R)]) s).M x = rd s.M x :=
    fun x hx => rd_blk_of_not_dst I _ s (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, zT, zN] <;> simp only [regs] at hx <;> (clear * - hx; omega))
  generalize semXIR I (.blk [.const zT 0, .const zN (toWord R)]) s = s0 at hM0 z0 r0 k0
  obtain ⟨t0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M zT = toWord j ∧
    (∀ t < j, ∀ i < 2 ^ kL, rdK s'.M (ob + t * 2 ^ kL + i) = coeffsAt ptK N kL 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < ob ∨ ob + j * 2 ^ kL ≤ x) → rd s'.M x = rd s.M x)
  have hE : ∀ i, i ≠ zC → i ≠ cTmp → rd (entryK zC zN (toWord R) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK zC zN (toWord R) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun t ht => absurd ht (by (clear * - ht; omega)), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), t0]
    · simp only [regs] at hx
      rw [hE _ (by simp only [zC]; (clear * - hx; omega)) (by simp only [cTmp]; (clear * - hx; omega)), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < R → P j s' → P (j + 1) (decS zC (semXIR I (bflyRowM N kL tb ob) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    rw [bflyRowM, semXIR_seq]
    set A := ob + j * 2 ^ kL with hA
    have hjR : j * 2 ^ kL + 2 ^ kL ≤ R * 2 ^ kL := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    have hs' := i1.1
    simp only [regs] at hs'
    have a1 : rd (semXIR I (.blk [.const zK (toWord (2 ^ kL)), .op .mul rA0 zT zK,
        .const zK (toWord ob), .op .add rA0 rA0 zK]) s').M rA0 = toWord A := by
      rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, zK, rA0, zT]; omega)) only [rd_set_self, rd_set_ne]
      rw [i3, mul_toWord, add_toWord, hA, Nat.add_comm]
    have a2 : ∀ x, x ≠ zK → x ≠ rA0 → rd (semXIR I (.blk [.const zK (toWord (2 ^ kL)),
        .op .mul rA0 zT zK, .const zK (toWord ob), .op .add rA0 rA0 zK]) s').M x = rd s'.M x :=
      fun x h1 h2 => rd_blk_of_not_dst I _ s' (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Prim.dst]
        exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h1, Ne.symm h2⟩)
    have hM1 := inv_sem I (P := .blk [.const zK (toWord (2 ^ kL)), .op .mul rA0 zT zK,
      .const zK (toWord ob), .op .add rA0 rA0 zK]) (by simp +decide [WF, Prim.dst, zK, rA0]) i1
    have z1 := size_sem I (.blk [.const zK (toWord (2 ^ kL)), .op .mul rA0 zT zK,
      .const zK (toWord ob), .op .add rA0 rA0 zK]) s'
    generalize semXIR I (.blk [.const zK (toWord (2 ^ kL)), .op .mul rA0 zT zK,
      .const zK (toWord ob), .op .add rA0 rA0 zK]) s' = s1 at a1 a2 hM1 z1
    rw [semXIR_seq]
    have hx1 : ∀ x, regs ≤ x → x ≠ zK ∧ x ≠ rA0 := fun x hx => by
      simp only [regs, zK, rA0] at *; (clear * - hx; omega)
    have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s'.M x := fun x hx => a2 x (hx1 x hx).1 (hx1 x hx).2
    have hT1 : TabOkN N s1.M tb := tabOkN_congr hT fun x hx1' hx2' => by
      rw [h1 x (by simp only [regs]; (clear * - htb hx1'; omega))]
      exact i5 x (by simp only [regs]; (clear * - htb hx1'; omega)) (by (clear * - hdisj hK0 hjR hx1' hx2'; omega))
    have hY1 : ∀ i < 2 ^ kL, rdK s1.M (A + i) = Y j i := fun i hi => by
      simp only [rdK]
      rw [h1 _ (by simp only [regs]; (clear * - hob hob2 hK0 hjR; omega)), hA, i5 _ (by simp only [regs]; (clear * - hob hob2 hK0 hjR; omega)) (Or.inr (by (clear * -; omega)))]
      exact hY j hj i hi
    obtain ⟨-, b2, hM2⟩ := bflyNIR_sem I s1 hM1 hN (A := A) (tb := tb) (ℓ := kL) (Y := Y j) hkN
      (by simp only [regs]; (clear * - hob; omega)) (by (clear * - hob2 hjR; omega)) (by (clear * - hsz z0 h0 i2 hjR z1; omega)) (by simp only [regs]; omega) htb2
      (by (clear * - hdisj hjR; omega)) a1 hT1 hY1
    have b1 := bflyNIR_coeffs I s1 hM1 hN (A := A) (tb := tb) (ℓ := kL) (Y := Y j) hkN
      (by simp only [regs]; (clear * - hob; omega)) (by (clear * - hob2 hjR; omega)) (by (clear * - hsz z0 h0 i2 hjR z1; omega)) (by simp only [regs]; omega) htb2
      (by (clear * - hdisj hjR; omega)) a1 hT1 hY1
    have q2 : rd (semXIR I (bflyNIR N kL tb) s1).M zT = toWord j := by
      rw [frame I _ s1 (wf_bflyNIR N kL tb) hM1 zT (by decide) (bflyNIR_nw_hi N kL tb (by decide)),
        a2 _ (by decide) (by decide), i3]
    have z2 := size_sem I (bflyNIR N kL tb) s1
    generalize semXIR I (bflyNIR N kL tb) s1 = s2 at b1 b2 hM2 q2 z2
    have hd : ∀ x, x ≠ zC → rd (decS zC (semXIR I (.blk [.op .add zT zT cOne]) s2)).M x =
        rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x := fun x hx => rd_decS (Ne.symm hx) _
    have c2 : ∀ x, x ≠ zT → rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x = rd s2.M x :=
      fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact Ne.symm hx)
    have hM3 := inv_sem I (P := .blk [.op .add zT zT cOne]) (by simp +decide [WF, Prim.dst, zT]) hM2
    have hx3 : ∀ x, regs ≤ x → x ≠ zC ∧ x ≠ zT := fun x hx => by
      simp only [regs, zC, zT] at *; (clear * - hx; omega)
    refine ⟨inv_decS hM3 (by decide), by rw [size_decS, size_sem, z2, z1, i2], ?_,
      fun t ht i hi => ?_, fun x hx hx2 => ?_⟩
    · have hs2 := hM2.1
      simp only [regs] at hs2
      rw [hd _ (by decide), sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [zT]; (clear * - hs z0 h0 i2 z1 z2; omega)), q2, show rd s2.M cOne = 1 from hM2.2 0 (by decide),
        add_one_toWord]
    · have hxr : regs ≤ ob + t * 2 ^ kL + i := by simp only [regs] at *; (clear * - hob hob2 hjR hi; omega)
      simp only [rdK]
      rw [hd _ (hx3 _ hxr).1, c2 _ (hx3 _ hxr).2]
      by_cases htj : t = j
      · subst htj; exact b1 i hi
      · have ht' : t < j := by (clear * - ht htj; omega)
        have : t * 2 ^ kL + 2 ^ kL ≤ j * 2 ^ kL := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht'
        rw [b2 _ hxr (by left; (clear * - hi this; omega)), h1 _ hxr]
        exact i4 t ht' i hi
    · have e : (j + 1) * 2 ^ kL = j * 2 ^ kL + 2 ^ kL := by ring
      rw [e] at hx2
      have hx4 : x < A ∨ A + 2 ^ kL ≤ x := by (clear * - hx2 e; omega)
      have hx5 : x < ob ∨ ob + j * 2 ^ kL ≤ x := by (clear * - hK0 hx2 e hx4; omega)
      rw [hd _ (hx3 x hx).1, c2 _ (hx3 x hx).2, b2 x hx hx4, h1 x hx, i5 x hx hx5]
  have hfin := loopK_run I (bflyRowM N kL tb ob) P s0 hM0 (c := zC) (n := zN) (K := R) (by decide)
    (by decide) (by decide) n0 hR h0 hstep
  exact ⟨hfin.2.2.2.1, fun x hx hx2 => hfin.2.2.2.2 x hx hx2, hfin.1⟩

end Lvm.X
end
-- ===== end of `LvmMPXDecSem` =====

/-!
# The level-≥1 decoder on the machine, generic in the shape

**`dec1MPIR_sem`**: on a memory holding the word `wd` at `wB + 48 q + t` (`q < 2^nL`), `α_i` at `aB + 3i` and
`f(v)` at `fB + 3v` (`rdE`), with the layout `Dec1MLay`:

* the cell `ok1M dB` holds `[2^kL ≤ |agree1G nL kL wd α f|]`, i.e. `decode1G N nL kL wd α f ≠ none`;
* if `decode1G N nL kL wd α f = some g`, then `rdE (oB + 3v) = g v` for `v < 2^(kL+4)`;
* the heap outside the workspace and the output is kept.

`decMP2IR_sem`, `decMP1IR_sem`: M′'s levels 2 and 1 (`decodeMP2`, `decodeMP1`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The level-≥1 decoder's memory layout** at the shape `(N, nL, kL)`: the workspace
`[dB, dB + ws1M nL kL)`; the word (`wB`, `48·2^nL` words), `α` (`aB`, 12 words) and `f` (`fB`, `3·2^kL`) outside
it; the output (`oB`, `3·2^(kL+4)`) inside the memory and outside the workspace; addresses below `2^60`. -/
structure Dec1MLay (N nL kL dB wB aB fB oB sz : ℕ) : Prop where
  hN : N ≤ 64
  hN1 : 1 ≤ N
  hkn : kL ≤ nL
  hnN : nL ≤ N
  r : regs ≤ dB
  t : dB + ws1M nL kL < 2 ^ 60
  z : dB + ws1M nL kL ≤ sz
  rW : regs ≤ wB
  tW : wB + 48 * 2 ^ nL < 2 ^ 60
  dW : wB + 48 * 2 ^ nL ≤ dB ∨ dB + ws1M nL kL ≤ wB
  rA : regs ≤ aB
  tA : aB + 12 < 2 ^ 60
  dA : aB + 12 ≤ dB ∨ dB + ws1M nL kL ≤ aB
  rF : regs ≤ fB
  tF : fB + 3 * 2 ^ kL < 2 ^ 60
  dF : fB + 3 * 2 ^ kL ≤ dB ∨ dB + ws1M nL kL ≤ fB
  rO : regs ≤ oB
  tO : oB + 3 * 2 ^ (kL + 4) < 2 ^ 60
  zO : oB + 3 * 2 ^ (kL + 4) ≤ sz
  dO : oB + 3 * 2 ^ (kL + 4) ≤ dB ∨ dB + ws1M nL kL ≤ oB

/-- The arithmetic facts of the layout, as linear facts on the atoms `2^kL`, `2^nL`. -/
theorem Dec1MLay.facts {N nL kL dB wB aB fB oB sz : ℕ} (hL : Dec1MLay N nL kL dB wB aB fB oB sz) :
    0 < 2 ^ kL ∧ 2 ^ kL ≤ 2 ^ nL ∧ 2 ^ (kL + 1) = 2 * 2 ^ kL ∧ 2 ^ (kL + 4) = 16 * 2 ^ kL ∧
      N * N ≤ 2 ^ 12 ∧ kL < 61 ∧ nL < 61 ∧ ws1M nL kL = 2 ^ 13 + 2 * 2 ^ kL + 5 * 2 ^ nL + 48 * 2 ^ kL := by
  have h1 := hL.hN
  have hkn := hL.hkn
  have hk := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hL.hkn
  have hNN : N * N ≤ 64 * 64 := Nat.mul_le_mul h1 h1
  have hn : nL < 61 := by
    have := hL.tW
    by_contra h
    have : 2 ^ 61 ≤ 2 ^ nL := Nat.pow_le_pow_right (by norm_num) (by (clear * - h; omega))
    omega
  refine ⟨by positivity, hk, by ring, by ring, by omega, by (clear * - hkn hn; omega), hn, ?_⟩
  rw [ws1M, pow_succ]; ring

/-! ## `Enc(f)` -/

/-- **One coordinate of `Enc(f)`** at `enc1M + c·2^nL`. -/
theorem enc1MC_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL dB wB aB fB oB c : ℕ}
    (hL : Dec1MLay N nL kL dB wB aB fB oB s.M.size) (hc : c < 3) (hT : TabOkN N s.M dB) :
    (∀ j < 2 ^ nL, rdK (semXIR I (enc1MC N nL kL dB fB c) s).M (enc1M nL kL dB + c * 2 ^ nL + j) =
      encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < enc1M nL kL dB + c * 2 ^ nL ∨ enc1M nL kL dB + c * 2 ^ nL + 2 ^ nL ≤ x) →
      rd (semXIR I (enc1MC N nL kL dB fB c) s).M x = rd s.M x) ∧
    Inv (semXIR I (enc1MC N nL kL dB fB c) s).M := by
  obtain ⟨k0, hkn', e1, e4, hNN, hk61, hn61, hws⟩ := hL.facts
  obtain ⟨hN, hN1, hkn, hnN, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  have hc2 : c * 2 ^ nL + 2 ^ nL ≤ 3 * 2 ^ nL := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by (clear * - hc; omega))
  set A := enc1M nL kL dB + c * 2 ^ nL with hA
  have hAd : dB + 2 ^ 12 ≤ A ∧ A + 2 ^ nL ≤ dB + ws1M nL kL := by
    simp only [hA, enc1M, ag1M]; constructor <;> (clear * - hws e4 hc2; omega)
  rw [enc1MC, semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpIR_sem I s hM (n := 2 ^ kL) (src := fB + c) (str := 3) (dst := A)
    (pow_lt64 (by (clear * - hk61; omega))) (by (clear * - hc tF; omega)) (by norm_num) (by simp only [regs]; (clear * - r hAd; omega)) (by (clear * - hkn' hws t hAd; omega)) (by (clear * - hkn' hws z hAd; omega))
    (fun i hi => by (clear * - hc hkn' hws dF dO hAd hi; omega)) (fun i hi => by simp only [regs]; (clear * - hc rF; omega))
  have z1 := size_sem I (mcpIR (2 ^ kL) (fB + c) 3 A) s
  generalize semXIR I (mcpIR (2 ^ kL) (fB + c) 3 A) s = s1 at m1 m2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨n1, n2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 ^ nL - 2 ^ kL) (dst := A + 2 ^ kL)
    (by (clear * - k0 hkn' e4 hws r t rF tF rO tO; omega)) (by simp only [regs]; (clear * - e4 hws r t rW tW hAd; omega)) (by (clear * - hkn' hws t hAd; omega)) (by (clear * - hkn' hws z hAd z1; omega))
  have z2 := size_sem I (zeroIR (2 ^ nL - 2 ^ kL) (A + 2 ^ kL)) s1
  generalize semXIR I (zeroIR (2 ^ nL - 2 ^ kL) (A + 2 ^ kL)) s1 = s2 at n1 n2 hM2 z2
  rw [semXIR_seq]
  have a3 : rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M rA0 = toWord A := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rA0]; (clear * - hs z1 z2; omega))]
  have k3 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M x = rd s2.M x :=
    fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, rA0]; simp only [regs] at hx; (clear * - hx; omega))
  have hM3 := inv_sem I (P := .blk [.const rA0 (toWord A)]) (by simp +decide [WF, Prim.dst, rA0]) hM2
  have z3 := size_sem I (.blk [.const rA0 (toWord A)]) s2
  generalize semXIR I (.blk [.const rA0 (toWord A)]) s2 = s3 at a3 k3 hM3 z3
  have h3 : ∀ x, regs ≤ x → (x < A ∨ A + 2 ^ nL ≤ x) → rd s3.M x = rd s.M x := fun x hx hx2 => by
    rw [k3 x hx, n2 x hx (by (clear * - k0 hkn' e4 rF tF tO hx2; omega)), m2 x hx (by (clear * - hkn' hx2; omega))]
  have hT3 : TabOkN N s3.M dB := tabOkN_congr hT fun x h1 h2 => h3 x (by simp only [regs] at *; (clear * - hNN r h1 h2; omega))
    (by (clear * - hNN hAd h1 h2; omega))
  have hY : ∀ i < 2 ^ nL, rdK s3.M (A + i) =
      if h : i < 2 ^ kL then (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) ⟨i, h⟩ else 0 := by
    intro i hi
    simp only [rdK]
    rw [k3 _ (by simp only [regs]; (clear * - r hAd; omega))]
    by_cases h : i < 2 ^ kL
    · rw [dif_pos h, n2 _ (by simp only [regs]; (clear * - r hAd; omega)) (by (clear * - h; omega)), m1 i h]
      congr 2; ring
    · rw [dif_neg h, show A + i = A + 2 ^ kL + (i - 2 ^ kL) by (clear * - h; omega), n1 _ (by (clear * - hkn' hi h; omega))]; rfl
  have hfe := fwdNIR_enc I s3 hM3 hN (A := A) (tb := dB) (ℓ := nL) (m := kL) hnN hkn
    (by simp only [regs]; (clear * - r hAd; omega)) (by (clear * - hws t hAd; omega)) (by (clear * - hws z hAd z1 z2 z3; omega)) (by simp only [regs]; omega)
    (by (clear * - hNN hws t; omega)) (by (clear * - hNN hAd; omega)) a3 hT3 (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) hY
  obtain ⟨-, f2, f3⟩ := fwdNIR_sem I s3 hM3 hN (A := A) (tb := dB) (ℓ := nL)
    (Y := fun i => rdK s3.M (A + i)) hnN (by simp only [regs]; (clear * - r hAd; omega)) (by (clear * - hws t hAd; omega)) (by (clear * - hws z hAd z1 z2 z3; omega))
    (by simp only [regs]; omega) (by (clear * - hNN hws t; omega)) (by (clear * - hNN hAd; omega)) a3 hT3 (fun i _ => rfl)
  exact ⟨hfe, fun x hx hx2 => (f2 x hx hx2).trans (h3 x hx hx2), f3⟩

/-- **`Enc(f)`'s three coordinates** at `enc1M + c·2^nL + j`. -/
theorem enc1MIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL dB wB aB fB oB : ℕ}
    (hL : Dec1MLay N nL kL dB wB aB fB oB s.M.size) (hT : TabOkN N s.M dB) :
    (∀ c < 3, ∀ j < 2 ^ nL, rdK (semXIR I (enc1MIR N nL kL dB fB) s).M (enc1M nL kL dB + c * 2 ^ nL + j) =
      encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < enc1M nL kL dB ∨ enc1M nL kL dB + 3 * 2 ^ nL ≤ x) →
      rd (semXIR I (enc1MIR N nL kL dB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (enc1MIR N nL kL dB fB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, e4, hNN, hk61, hn61, hws⟩ := hL.facts
  obtain ⟨hN, hN1, hkn, hnN, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  simp only [regs] at r rF
  rw [enc1MIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := enc1MC_sem I s hM hL (c := 0) (by norm_num) hT
  have z1 := size_sem I (enc1MC N nL kL dB fB 0) s
  generalize semXIR I (enc1MC N nL kL dB fB 0) s = s1 at a1 a2 hM1 z1
  have hL1 : Dec1MLay N nL kL dB wB aB fB oB s1.M.size := by rw [z1]; exact hL
  have hF1 : ∀ x, regs ≤ x → (x < enc1M nL kL dB ∨ enc1M nL kL dB + 2 ^ nL ≤ x) → rd s1.M x = rd s.M x :=
    fun x hx hx2 => a2 x hx (by simpa using hx2)
  have hT1 : TabOkN N s1.M dB := tabOkN_congr hT fun x h1 h2 =>
    hF1 x (by simp only [regs] at *; (clear * - hNN r h1 h2; omega)) (by simp only [enc1M, ag1M] at *; (clear * - hNN hws tW h1 h2; omega))
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := enc1MC_sem I s1 hM1 hL1 (c := 1) (by norm_num) hT1
  have z2 := size_sem I (enc1MC N nL kL dB fB 1) s1
  generalize semXIR I (enc1MC N nL kL dB fB 1) s1 = s2 at b1 b2 hM2 z2
  have hL2 : Dec1MLay N nL kL dB wB aB fB oB s2.M.size := by rw [z2]; exact hL1
  have hT2 : TabOkN N s2.M dB := tabOkN_congr hT1 fun x h1 h2 =>
    b2 x (by simp only [regs] at *; (clear * - hNN r h1 h2; omega)) (by simp only [enc1M, ag1M] at *; (clear * - hNN hws tW h1 h2; omega))
  obtain ⟨c1, c2, hM3⟩ := enc1MC_sem I s2 hM2 hL2 (c := 2) (by norm_num) hT2
  have hfB : ∀ x c, x < 2 ^ kL → c < 3 → regs ≤ fB + 3 * x + c ∧
      (fB + 3 * x + c < enc1M nL kL dB ∨ enc1M nL kL dB + 3 * 2 ^ nL ≤ fB + 3 * x + c) := fun x c hx hc => by
    simp only [regs, enc1M, ag1M] at *; (clear * - hkn' e4 hws r rF tF dF rO tO dO hx hc; omega)
  have ee1 : ∀ x : Fin (2 ^ kL), ∀ c < 3, rdK s1.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [a2 _ h1 (by (clear * - h2; omega))]
  have ee2 : ∀ x : Fin (2 ^ kL), ∀ c < 3, rdK s2.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [b2 _ h1 (by (clear * - h2; omega))]; exact ee1 x c hc
  refine ⟨fun c hc j hj => ?_, fun x hx hx2 => ?_, hM3⟩
  · interval_cases c
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, enc1M, ag1M] at *; (clear * - hws r; omega)) (by simp only [enc1M, ag1M] at *; (clear * - hj; omega)),
        b2 _ (by simp only [regs, enc1M, ag1M] at *; (clear * - hws r; omega)) (by simp only [enc1M, ag1M] at *; (clear * - hj; omega))]
      exact a1 j hj
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, enc1M, ag1M] at *; (clear * - hws r; omega)) (by simp only [enc1M, ag1M] at *; (clear * - hj; omega))]
      rw [show wK (rd s2.M (enc1M nL kL dB + 1 * 2 ^ nL + j)) = rdK s2.M (enc1M nL kL dB + 1 * 2 ^ nL + j)
        from rfl, b1 j hj]
      congr 1; funext x; exact ee1 x 1 (by norm_num)
    · rw [c1 j hj]
      congr 1; funext x; exact ee2 x 2 (by norm_num)
  · rw [c2 x hx (by (clear * - hx2; omega)), b2 x hx (by (clear * - hx2; omega)), a2 x hx (by (clear * - hx2; omega))]

/-! ## The decoding proper -/

theorem coef1G_getD_take {L : List ℕ} {n t : ℕ} (ht : t < n) : (L.take n).getD t 0 = L.getD t 0 :=
  getD_take_lt ht

/-- **The decoding proper**: on a list of `≥ 2^kL` agreeing positions at `ag1M`, the decoded message at `oB`. -/
theorem dec1MTail_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL dB wB aB fB oB : ℕ}
    (hL : Dec1MLay N nL kL dB wB aB fB oB s.M.size) (hT : TabOkN N s.M dB) (wd : ℕ → ℕ → BF64)
    (α f : ℕ → Ext3) (hW : ∀ q < 2 ^ nL, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hlen : 2 ^ kL ≤ (agree1G nL kL wd α f).length)
    (hJ : ∀ t < 2 ^ kL, rd s.M (ag1M kL dB + t) = toWord ((agree1G nL kL wd α f).getD t 0)) :
    (∀ v < 2 ^ (kL + 4), rdE (semXIR I (dec1MTail N nL kL dB wB oB) s).M (oB + 3 * v) =
      dec1G N nL kL wd α f v) ∧
    (∀ x, regs ≤ x → (x < wb1M dB ∨ dB + ws1M nL kL ≤ x) → (x < oB ∨ oB + 3 * 2 ^ (kL + 4) ≤ x) →
      rd (semXIR I (dec1MTail N nL kL dB wB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1MTail N nL kL dB wB oB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, e4, hNN, hk61, hn61, hws⟩ := hL.facts
  have n0 : 0 < 2 ^ nL := by positivity
  obtain ⟨hN, hN1, hkn, hnN, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  simp only [regs] at r rW rO
  set Jl := (agree1G nL kL wd α f).take (2 ^ kL) with hJl
  have hJlen : Jl.length = 2 ^ kL := by
    rw [hJl, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_filter_range _ _).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ nL := fun j hj => by
    have := List.mem_of_mem_take hj
    rw [agree1G, List.mem_filter, List.mem_range] at this
    exact this.1
  have hBL : BaryLayP (2 ^ nL) (2 ^ kL) 48 (ag1M kL dB) (wb1M dB) (eb1M kL dB) wB 48 (ob1M nL kL dB)
      s.M.size := by
    refine ⟨by (clear * - rW tW; omega), by norm_num, hkn', le_rfl, ?_, ?_, ?_, ?_, rW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [regs, ag1M, wb1M, eb1M, ob1M, enc1M]) <;> (clear * - k0 e4 r rO tO hJlen n0 hws t tW z tF zO hkn' dW tA dA dF dO rW; omega)
  have hget : ∀ t < 2 ^ kL, Jl.getD t 0 < 2 ^ nL := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by (clear * - hJlen ht; omega))]
    exact hJlt _ (List.getElem_mem (l := Jl) (n := t) (by (clear * - hJlen ht; omega)))
  rw [dec1MTail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_semP I s hM (Jl := Jl) hBL hget (fun t ht => by
    rw [hJ t ht, hJl, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ kL) 48 (ag1M kL dB) (wb1M dB) (eb1M kL dB) wB 48 (ob1M nL kL dB)) s
  generalize semXIR I (baryIR (2 ^ kL) 48 (ag1M kL dB) (wb1M dB) (eb1M kL dB) wB 48 (ob1M nL kL dB)) s
    = s1 at b1 b2 hM1 z1
  have hT1 : TabOkN N s1.M dB := tabOkN_congr hT fun x h1 h2 => by
    exact b2 x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [wb1M]; (clear * - hNN h2; omega))
      (by simp only [eb1M]; (clear * - hNN hJlen h1 h2; omega)) (by simp only [ob1M, enc1M, ag1M]; (clear * - hNN hws n0 t hJlen h1 h2; omega))
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bflyAllM_sem I s1 hM1 hN (kL := kL) (R := 48) (tb := dB) (ob := ob1M nL kL dB)
    (by (clear * - hkn hnN; omega)) (by norm_num) (by simp only [regs, ob1M, enc1M, ag1M]; (clear * - k0 e4 n0 r rO tO hJlen; omega))
    (by simp only [ob1M, enc1M, ag1M]; (clear * - hws t hJlen; omega)) (by rw [z1]; simp only [ob1M, enc1M, ag1M]; (clear * - hws z hJlen z1; omega))
    (by simp only [regs]; omega) (by (clear * - hNN hws t hJlen; omega)) (by simp only [ob1M, enc1M, ag1M]; (clear * - k0 e4 hNN n0 rO tO hJlen; omega)) hT1
    (fun t i => rdK s1.M (ob1M nL kL dB + t * 2 ^ kL + i)) (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bflyAllM N kL 48 dB (ob1M nL kL dB)) s1
  generalize semXIR I (bflyAllM N kL 48 dB (ob1M nL kL dB)) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := tr1MIR_sem I s2 hM2 (kL := kL) (ob := ob1M nL kL dB) (oB := oB) (by (clear * - hk61; omega))
    (by simp only [regs, ob1M, enc1M, ag1M]; (clear * - k0 e4 n0 r rO tO hJlen; omega)) (by simp only [ob1M, enc1M, ag1M]; (clear * - hws t hJlen; omega))
    (by simp only [regs]; omega) (by (clear * - e4 tO hJlen; omega)) (by rw [z2, z1]; (clear * - e4 zO hJlen z1 z2; omega))
    (by simp only [ob1M, enc1M, ag1M]; (clear * - k0 e4 hws n0 t tF rO tO dO hJlen; omega))
  generalize semXIR I (tr1MIR kL (ob1M nL kL dB) oB) s2 = s3 at d1 d2 hM3
  refine ⟨fun v hv => ?_, fun x hx hx2 hx3 => ?_, hM3⟩
  · -- the decoded entry `v = u + 16 v'`
    have hval : ∀ c < 3, rdK s3.M (oB + 3 * v + c) = coef1G N nL kL wd α f (3 * (v % 16) + c) (v / 16) := by
      intro c hc
      have hu : v % 16 < 16 := Nat.mod_lt _ (by norm_num)
      have hv' : v / 16 < 2 ^ kL := by (clear * - e4 hJlen hv hu; omega)
      have e : oB + 3 * v + c = oB + 48 * (v / 16) + (3 * (v % 16) + c) := by (clear * -; omega)
      simp only [rdK]
      rw [e, d1 (v / 16) hv' (3 * (v % 16) + c) (by (clear * - hc hu; omega)),
        show ob1M nL kL dB + 2 ^ kL * (3 * (v % 16) + c) + v / 16 =
          ob1M nL kL dB + (3 * (v % 16) + c) * 2 ^ kL + v / 16 by ring,
        show wK (rd s2.M (ob1M nL kL dB + (3 * (v % 16) + c) * 2 ^ kL + v / 16)) =
          rdK s2.M (ob1M nL kL dB + (3 * (v % 16) + c) * 2 ^ kL + v / 16) from rfl,
        c1 (3 * (v % 16) + c) (by (clear * - hc hu; omega)) (v / 16) hv', coef1G, ← hJl]
      refine coeffsAt_congr ptK N kL 0 _ _ (fun j hj => ?_) (v / 16) hv'
      rw [show ob1M nL kL dB + (3 * (v % 16) + c) * 2 ^ kL + j =
          ob1M nL kL dB + 2 ^ kL * (3 * (v % 16) + c) + j by ring,
        b1 j hj _ (by (clear * - hc hu; omega)), show (2 : ℕ) ^ kL = Jl.length from hJlen.symm,
        baryValK_eqP (P := 2 ^ nL) (by (clear * - rW tW; omega)) hJnd hJlt (by (clear * - hkn' hJlen hj; omega))]
      refine interpF_congr ptK _ (fun q hq => ?_) j
      have hq' := hJlt q (List.mem_toFinset.1 hq)
      rw [hW q hq' _ (by (clear * - hc hu; omega)), lane1]
    have h0 := hval 0 (by norm_num)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [rdE, h0, hval 1 (by norm_num), hval 2 (by norm_num), dec1G]
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by (clear * - e4 hJlen hx3; omega)),
      c2 x (by simp only [regs]; omega) (by simp only [ob1M, enc1M, ag1M, wb1M] at *; (clear * - e4 hws n0 t rO tO hJlen hx hx2 hx3; omega)),
      b2 x (by simp only [regs]; omega) (by simp only [wb1M] at *; (clear * - e4 hws n0 r t rO tO hJlen hx2 hx3; omega))
        (by simp only [eb1M, wb1M] at *; (clear * - e4 hws n0 r tO hJlen hx2 hx3; omega)) (by simp only [ob1M, enc1M, ag1M, wb1M] at *; (clear * - e4 hws n0 t rO tO hJlen hx hx2 hx3; omega))]

/-! ## The whole program -/

/-- **The level-≥1 decoder program computes `decode1G N nL kL`.** -/
theorem dec1MPIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL dB wB aB fB oB : ℕ}
    (hL : Dec1MLay N nL kL dB wB aB fB oB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ nL, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hA : ∀ i < 4, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ kL, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (dec1MPIR N nL kL dB wB aB fB oB) s).M (ok1M dB) =
      bW (decide (2 ^ kL ≤ (agree1G nL kL wd α f).length)) ∧
    (∀ g, decode1G N nL kL wd α f = some g →
      ∀ v < 2 ^ (kL + 4), rdE (semXIR I (dec1MPIR N nL kL dB wB aB fB oB) s).M (oB + 3 * v) = g v) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + ws1M nL kL ≤ x) → (x < oB ∨ oB + 3 * 2 ^ (kL + 4) ≤ x) →
      rd (semXIR I (dec1MPIR N nL kL dB wB aB fB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1MPIR N nL kL dB wB aB fB oB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, e4, hNN, hk61, hn61, hws⟩ := hL.facts
  have n0 : 0 < 2 ^ nL := by positivity
  obtain ⟨hN, hN1, hkn, hnN, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF rO hs
  -- 1. the basis table
  rw [dec1MPIR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabNIR_sem I s hM hN hN1 (tb := dB) (by simp only [regs]; omega)
    (by (clear * - hNN hws t; omega)) (by (clear * - e4 hNN hws n0 z; omega))
  generalize semXIR I (wtabNIR N dB) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOkN N s1.M dB := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_sem I s1 hM1 (ℓ := 4) (aB := aB) (qB := q1M dB) (by norm_num)
    (by simp only [regs]; omega) (by (clear * - rA tA; omega)) (by simp only [regs, q1M]; (clear * - r; omega))
    (by simp only [q1M]; (clear * - hws t; omega)) (by rw [z1]; simp only [q1M]; (clear * - e4 hws n0 z z1; omega)) (by simp only [q1M]; (clear * - e4 hws n0 dA dF dO; omega))
  have z2 := size_sem I (eqtIR 4 aB (q1M dB)) s1
  generalize semXIR I (eqtIR 4 aB (q1M dB)) s1 = s2 at q1 q2 hM2 z2
  have q2' : ∀ x, regs ≤ x → (x < q1M dB ∨ q1M dB + 48 ≤ x) → rd s2.M x = rd s1.M x :=
    fun x hx hx2 => q2 x (.inr (lt_of_lt_of_le (by decide) hx)) (by omega)
  have hT2 : TabOkN N s2.M dB := tabOkN_congr hT1 fun x h1 h2 => by
    exact q2' x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [q1M]; (clear * - hNN h2; omega))
  have hQ2 : ∀ u < 16, rdE s2.M (q1M dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [q1 u hu]
    refine eqA1_congr (fun i hi => ?_) u
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; (clear * - rA tA hi hk; omega)) (by (clear * - k0 e4 hNN hws n0 r t rA tA dA tF dF tO dO hi hk; omega))
  have hL2 : Dec1MLay N nL kL dB wB aB fB oB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc(f)`
  rw [semXIR_seq]
  obtain ⟨ee1, ee2, hM3⟩ := enc1MIR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (enc1MIR N nL kL dB fB) s2
  generalize semXIR I (enc1MIR N nL kL dB fB) s2 = s3 at ee1 ee2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + ws1M nL kL ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2' x hx (by simp only [q1M]; (clear * - e4 hws n0 hx2; omega)), w2 x hx (by (clear * - e4 hNN hws n0 hx2; omega))]
  have hfB : ∀ v < 2 ^ kL, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; (clear * - rF hc; omega)) (by (clear * - hws dF dO hv hc; omega))]
  have hW3 : ∀ q < 2 ^ nL, ∀ t < 48, rdK s3.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
    have : 48 * q + t < 48 * 2 ^ nL := by (clear * - hq ht; omega)
    rw [← hW q hq t ht]; simp only [rdK]
    rw [ee2 _ (by simp only [regs]; (clear * - rW ht; omega)) (by simp only [enc1M, ag1M]; omega),
      hout _ (by simp only [regs]; (clear * - rW ht; omega)) (by (clear * - hws dW dA dF dO ht this; omega))]
  have hQ3 : ∀ u < 16, rdE s3.M (q1M dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [← hQ2 u hu]
    exact rdE_congr fun k hk => ee2 _ (by simp only [regs, q1M]; (clear * - r hu hk; omega))
      (by simp only [q1M, enc1M, ag1M]; (clear * - hws rW tW hu hk; omega))
  have hE3 : ∀ q < 2 ^ nL, encG kL f q = mkE (rdK s3.M (enc1M nL kL dB + q))
      (rdK s3.M (enc1M nL kL dB + 2 ^ nL + q)) (rdK s3.M (enc1M nL kL dB + 2 * 2 ^ nL + q)) := by
    intro q hq
    rw [encG_coords kL f (fun c v => rdK s.M (fB + 3 * v + c)) (fun v hv => by rw [← hF v hv]; rfl) q]
    have hc : ∀ c < 3, encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) q =
        rdK s3.M (enc1M nL kL dB + c * 2 ^ nL + q) := fun c hc => by
      rw [ee1 c hc q hq]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), Nat.zero_mul, Nat.add_zero,
      Nat.one_mul]
  have hAg : agree1NM s3.M (2 ^ nL) wB (q1M dB) (enc1M nL kL dB) (2 ^ nL) = agree1G nL kL wd α f :=
    agree1NM_eq_agree1G wd α f hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agree1NIR_sem I s3 hM3 (st := 2 ^ nL) (wB := wB) (qB := q1M dB)
    (eB := enc1M nL kL dB) (agB := ag1M kL dB) (by simp only [regs]; omega) (by (clear * - tW; omega))
    (by simp only [regs, q1M]; (clear * - r; omega)) (by simp only [q1M]; (clear * - hws t; omega))
    (by simp only [regs, enc1M, ag1M]; (clear * - hws n0 r; omega)) (by simp only [enc1M, ag1M]; (clear * - e4 hws t; omega))
    (by simp only [regs, ag1M]; (clear * - e4 r; omega)) (by simp only [ag1M]; (clear * - e4 hws t; omega))
    (by rw [z3, z2, z1]; simp only [ag1M]; (clear * - e4 hws n0 z z1 z2 z3; omega))
    ⟨by simp only [ag1M]; (clear * - e4 hws n0 rW tW dW dA dF dO; omega), by simp only [ag1M, q1M]; (clear * - e4; omega), by simp only [ag1M, enc1M]; (clear * -; omega)⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agree1NIR (2 ^ nL) wB (q1M dB) (enc1M nL kL dB) (ag1M kL dB)) s3
  generalize semXIR I (agree1NIR (2 ^ nL) wB (q1M dB) (enc1M nL kL dB) (ag1M kL dB)) s3 = s4
    at g1 g2 g3 hM4 z4
  have hlenL : (agree1G nL kL wd α f).length ≤ 2 ^ nL := by
    rw [agree1G]; exact (List.length_filter_le _ _).trans (by simp)
  have hlen64 : (agree1G nL kL wd α f).length < 2 ^ 64 := by (clear * - rW tW hlenL; omega)
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := okMIR_sem I s4 hM4 (kL := kL) (ok := ok1M dB)
    (n := (agree1G nL kL wd α f).length) (by (clear * - hk61; omega)) (by simp only [regs, ok1M]; (clear * - r; omega))
    (by simp only [ok1M]; (clear * - hws t; omega)) (by rw [z4, z3, z2, z1]; simp only [ok1M]; (clear * - e4 hws z z1 z2 z3 z4 hlenL hlen64; omega)) hlen64 g1
  have z5 := size_sem I (okMIR kL (ok1M dB)) s4
  generalize semXIR I (okMIR kL (ok1M dB)) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOkN N s5.M dB := tabOkN_congr hT2 fun x h1 h2 => by
    rw [o3 x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [ok1M]; (clear * - hNN h2; omega)),
      g3 x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [ag1M]; (clear * - e4 hNN rW tW h1 h2; omega)),
      ee2 x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [enc1M, ag1M]; (clear * - hNN hws hlenL hlen64 h1 h2; omega))]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + ws1M nL kL ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [ok1M]; (clear * - e4 hws hlenL hlen64 hx2; omega)), g3 x hx (by simp only [ag1M]; (clear * - e4 hws hlenL hlen64 hx2; omega)),
      ee2 x hx (by simp only [enc1M, ag1M]; (clear * - e4 hws hlenL hlen64 hx2; omega)), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ kL ≤ (agree1G nL kL wd α f).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : Dec1MLay N nL kL dB wB aB fB oB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ nL, ∀ t < 48, rdK s5.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
      have : 48 * q + t < 48 * 2 ^ nL := by (clear * - hq ht; omega)
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; (clear * - rW ht; omega)) (by (clear * - hws dW dA dF dO ht this; omega))]
    have hJ5 : ∀ t < 2 ^ kL, rd s5.M (ag1M kL dB + t) = toWord ((agree1G nL kL wd α f).getD t 0) :=
      fun t ht => by
        rw [o3 _ (by simp only [regs, ag1M]; (clear * - r ht; omega)) (by simp only [ag1M, ok1M]; (clear * - ht; omega)), g2 t (by (clear * - hk ht; omega))]
    obtain ⟨d1, d2, hM6⟩ := dec1MTail_sem I s5 hM5 hL5 hT5 wd α f hW5 hk hJ5
    refine ⟨?_, fun g hout' v hv => ?_, fun x hx hx2 hx3 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, ok1M]; (clear * - r; omega)) (by simp only [ok1M, wb1M]; (clear * -; omega))
        (by simp only [ok1M]; (clear * - e4 hws n0 r rO tO dO; omega)), o2, decide_eq_true hk]
    · rw [decode1G, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 v hv]
      exact (if_pos hv).symm
    · rw [d2 x hx (by simp only [wb1M]; (clear * - hws hx2 hx3; omega)) hx3, h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun g hout' => ?_, fun x hx hx2 _ => h5 x hx hx2, hM5⟩
    rw [decode1G, if_neg hk] at hout'
    exact absurd hout' (by simp)

/-! ## M′'s levels 2 and 1 -/

/-- **M′'s level-2 decoder program computes `decodeMP2`** (`2^13` positions, `k = 2^9`). -/
theorem decMP2IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1MLay 19 13 9 dB wB aB fB oB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 13, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hA : ∀ i < 4, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 9, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (decMP2IR dB wB aB fB oB) s).M (ok1M dB) =
      bW (decide (2 ^ 9 ≤ (agree1G 13 9 wd α f).length)) ∧
    (∀ g, decodeMP2 wd α f = some g →
      ∀ v < 2 ^ 13, rdE (semXIR I (decMP2IR dB wB aB fB oB) s).M (oB + 3 * v) = g v) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + ws1M 13 9 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 13 ≤ x) →
      rd (semXIR I (decMP2IR dB wB aB fB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP2IR dB wB aB fB oB) s).M :=
  dec1MPIR_sem I s hM hL wd α f hW hA hF

/-- **M′'s level-1 decoder program computes `decodeMP1`** (`2^16` positions, `k = 2^13`). -/
theorem decMP1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1MLay 19 16 13 dB wB aB fB oB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 16, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hA : ∀ i < 4, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 13, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (decMP1IR dB wB aB fB oB) s).M (ok1M dB) =
      bW (decide (2 ^ 13 ≤ (agree1G 16 13 wd α f).length)) ∧
    (∀ g, decodeMP1 wd α f = some g →
      ∀ v < 2 ^ 17, rdE (semXIR I (decMP1IR dB wB aB fB oB) s).M (oB + 3 * v) = g v) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + ws1M 16 13 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 17 ≤ x) →
      rd (semXIR I (decMP1IR dB wB aB fB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP1IR dB wB aB fB oB) s).M :=
  dec1MPIR_sem I s hM hL wd α f hW hA hF

/-- **A level-2 layout exists** (non-vacuity): workspace at `2^22`, word at `2^23`, `α` at `2^20`, `f` at
`2^20 + 64`, output at `2^21`. -/
theorem decMP2Lay_example (sz : ℕ) (hsz : 2 ^ 24 ≤ sz) :
    Dec1MLay 19 13 9 (2 ^ 22) (2 ^ 23) (2 ^ 20) (2 ^ 20 + 64) (2 ^ 21) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs, ws1M]) <;> norm_num <;> omega

/-- **A level-1 layout exists** (non-vacuity), same placement. -/
theorem decMP1Lay_example (sz : ℕ) (hsz : 2 ^ 24 ≤ sz) :
    Dec1MLay 19 16 13 (2 ^ 22) (2 ^ 23) (2 ^ 20) (2 ^ 20 + 64) (2 ^ 21) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs, ws1M]) <;> norm_num <;> omega

end Lvm.X
